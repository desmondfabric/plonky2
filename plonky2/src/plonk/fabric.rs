
use std::fs::File;
use std::io::Write;

use alloc::collections::BTreeMap;
use fabric_runtime::value::Value;
use hashbrown::HashMap;
use plonky2_field::{extension::Extendable, types::PrimeField64, fft::FftRootTable};

use crate::{hash::hash_types::RichField, iop::{witness::PartialWitness, target::Target, generator::{WitnessGenerator, WitnessGeneratorRef}}, gates::{lookup_table::LookupTable, lookup::{Lookup}}, fri::{FriConfig, reduction_strategies::FriReductionStrategy, FriParams, oracle::PolynomialBatch}};

use crate::hash::merkle_tree::MerkleTree;
use super::{config::{GenericConfig, GenericHashOut, Hasher}, circuit_data::{CircuitData, self}, circuit_builder::LookupWire};

pub struct InputValue;
pub const PATH_TO_FABRIC: &str = "/home/desmond/fabric/Fabric/fabric/workloads/plonky2/tests/data/example.txt";

impl InputValue{
    pub fn prover_test_data<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
        partial_witness: &PartialWitness<F>,
        data: &CircuitData<F, C, D>
    ) ->  std::io::Result<()> {
        let mut res: Vec<(&str, Value)> = Vec::new();

        // common test data
        let common   = &data.common;

        res.push(("input::common::luts", inner_vec_to_value(&common.luts, lookuptable_to_value)));
        res.push(("input::common::quotient_degree", prim_to_value(&common.quotient_degree())));
        res.push(("input::common::degree", prim_to_value(&common.degree())));
        res.push(("input::common::num_partial_products", prim_to_value(&common.num_partial_products)));
        res.push(("input::common::k_is", f_vec_to_value(&common.k_is)));
        res.push(("input::common::fri_params", friparam_to_value(&common.fri_params)));

        let config = &common.config;

        res.push(("input::common::config::num_routed_wires", prim_to_value(&config.num_routed_wires)));
        res.push(("input::common::config::friconfig", friconfig_to_value(&config.fri_config)));
        res.push(("input::common::config::num_challenges", prim_to_value(&config.num_challenges)));
        res.push(("input::common::config::num_wires", prim_to_value(&config.num_wires)));
        res.push(("input::common::config::zero_knowledge", bool_to_value(&config.zero_knowledge)));


        // prover test data
        let prover = &data.prover_only;

        res.push(("input::prover::generators", generators_to_value(&prover.generators)));
        res.push(("input::prover::generator_indices_by_watches", map_to_value(&prover.generator_indices_by_watches)));
        res.push(("input::prover::representative_map", prim_vec_to_value(&prover.representative_map)));
        res.push(("input::prover::lut_to_lookups", inner_vec_to_value(&prover.lut_to_lookups,lookup_to_value)));
        if prover.fft_root_table.is_some(){
            res.push(("input::prover::fft_root_table", inner_vec_to_value(&prover.fft_root_table.as_ref().unwrap(),f_vec_to_value)));
        }
        res.push(("input::prover::circuit_digest", f_vec_to_value(&prover.circuit_digest.to_vec())));
        res.push(("input::prover::subgroup", f_vec_to_value(&prover.subgroup)));
        res.push(("input::prover::sigmas", inner_vec_to_value(&prover.sigmas,f_vec_to_value)));
        res.push(("input::prover::constants_sigmas_commitment", polynomial_batch_to_value(&prover.constants_sigmas_commitment)));
        res.push(("input::prover::public_inputs", target_vec_to_value(&prover.public_inputs)));
        res.push(("input::prover::lookup_rows", inner_vec_to_value(&prover.lookup_rows, lookup_wire_to_value)));
        
        // witness test data
        res.push(("input::parital_witness::target_values", target_values_to_value(&partial_witness.target_values)));
        
        save_res_to_file(&res, PATH_TO_FABRIC)
    }
}


fn save_res_to_file(vals: &[(&str, Value)], file_path: &str) -> std::io::Result<()> {
    let mut file = File::create(file_path)?;

    writeln!(file, "[")?;
    for (name, val) in vals.iter() {
        writeln!(file, "  (\"{}\", {}),", name, val.to_immediate())?;
    }
    writeln!(file, "]")?;

    Ok(())
}

pub fn target_values_to_value<F: RichField>(input: &HashMap<Target, F>) -> Value{
    let mut targets: Vec<Value> = Vec::new();
    for (key, val) in input{
        targets.push(Value::Vector(vec![target_to_value(&key),prim_to_value(&val.to_canonical_u64())]));
    }
    Value::Vector(targets)
}

pub fn lookup_wire_to_value(input: &LookupWire) -> Value{
    let mut wire_vec: Vec<Value> = Vec::new();
    wire_vec.push(prim_to_value(&input.last_lu_gate));
    wire_vec.push(prim_to_value(&input.last_lut_gate));
    wire_vec.push(prim_to_value(&input.first_lut_gate));
    Value::Vector(wire_vec)
}
pub fn polynomial_batch_to_value<F: RichField + Extendable<D>, 
    C: GenericConfig<D, F = F>, const D: usize>(input: &PolynomialBatch<F, C, D>) -> Value{
    let mut poly_vec: Vec<Value> = Vec::new();
    let poly_coeffs: &Vec<Vec<F>> = &input.polynomials.iter()
        .map(|x| x.coeffs.clone()).collect();
    poly_vec.push(inner_vec_to_value(&poly_coeffs, f_vec_to_value));
    poly_vec.push(merkle_tree_to_value(&input.merkle_tree));
    poly_vec.push(prim_to_value(&input.degree_log));
    poly_vec.push(prim_to_value(&input.rate_bits));
    poly_vec.push(bool_to_value(&input.blinding));
    Value::Vector(poly_vec)
}

pub fn merkle_tree_to_value<F: RichField + Extendable<D>, H: Hasher<F>, const D:usize>(input: &MerkleTree<F, H>) -> Value{
    let mut merkle_vec: Vec<Value> = Vec::new();
    merkle_vec.push(inner_vec_to_value(&input.leaves, f_vec_to_value));
    let digest_vec: &Vec<Vec<F>>  = &input.digests.iter().map(|x| x.to_vec()).collect();
    merkle_vec.push(inner_vec_to_value(digest_vec, f_vec_to_value));
    let cap_vec: &Vec<Vec<F>> = &input.cap.0.iter().map(|x| x.to_vec()).collect();
    merkle_vec.push(inner_vec_to_value(&cap_vec, f_vec_to_value));
    Value::Vector(merkle_vec)
}

pub fn inner_vec_to_value<T, K>(input: &Vec<T>, converter: K) -> Value
where
    K: Fn(&T) -> Value,
{
    Value::Vector(input.iter().map(converter).collect())
}

pub fn lookup_to_value(input: &Lookup) -> Value {
    let pair_vec: Vec<Vec<Target>> = input.iter()
        .map(|&(x, y)| vec![x, y]).collect();
    inner_vec_to_value(&pair_vec, target_vec_to_value)
}

pub fn f_vec_to_value<F: RichField>(input: &Vec<F>) -> Value{
    let canonical_vec: Vec<u64> = input.iter()
        .map(PrimeField64::to_canonical_u64).collect();
    prim_vec_to_value(&canonical_vec)
}

pub fn friparam_to_value(input: &FriParams) -> Value {
    let mut fri_vec: Vec<Value> = Vec::new();
    fri_vec.push(friconfig_to_value(&input.config));
    fri_vec.push(bool_to_value(&input.hiding));
    fri_vec.push(prim_to_value(&input.degree_bits));
    fri_vec.push(prim_vec_to_value(&input.reduction_arity_bits));
    Value::Vector(fri_vec)
}
pub fn friconfig_to_value(input: &FriConfig) -> Value{
    let mut fri_vec: Vec<Value> = Vec::new();
    fri_vec.push(prim_to_value(&input.rate_bits));
    fri_vec.push(prim_to_value(&input.cap_height));
    fri_vec.push(prim_to_value(&input.proof_of_work_bits));
    fri_vec.push(fri_reduction_to_value(&input.reduction_strategy));
    fri_vec.push(prim_to_value(&input.num_query_rounds));
    Value::Vector(fri_vec)

}

pub fn fri_reduction_to_value(input: &FriReductionStrategy) 
    -> Value {
    // check first element to see which type of enum
    let mut acc: Vec<usize> = Vec::new();
    match input{
        FriReductionStrategy::Fixed(vec) => {
            acc.push(0);
            acc.extend(vec);
        },
        FriReductionStrategy::ConstantArityBits(a, b) => {
            acc.push(1);
            acc.push(*a);
            acc.push(*b);
        },
        FriReductionStrategy::MinSize(min) => {
            acc.push(2);
            if min.is_some(){
                acc.push(min.unwrap())
            }
        },
    }
    prim_vec_to_value(&acc)
}

pub fn bool_to_value(input: &bool) -> Value {
    let mut val = 0;
    if *input{
        val += 1;
    }
    prim_to_value(&val)
}

pub fn prim_to_value<T: ToString>(input: &T) -> Value {
    Value::scalar_from_str(&input.to_string())
}

pub fn prim_vec_to_value<T: ToString>(input: &Vec<T>) -> Value{
    inner_vec_to_value(&input, prim_to_value)
}

pub fn lookuptable_to_value(input: &LookupTable) -> Value {
    let inner_vec: &Vec<(u16, u16)> = &input;
    let pair_vec: Vec<Vec<u16>> = inner_vec.iter().map(|&(x, y)| vec![x, y]).collect();
    inner_vec_to_value(&pair_vec, prim_vec_to_value)
}

pub fn generators_to_value<F: RichField + Extendable<D>, const D: usize>(input: &Vec<WitnessGeneratorRef<F,D>>) -> Value{
    let watch_lists: &Vec<Vec<Target>> = &input
        .iter().map(|gen_ref| gen_ref.0.watch_list()).collect();
    inner_vec_to_value(&watch_lists, target_vec_to_value)
}

pub fn map_to_value(input: &BTreeMap<usize, Vec<usize>>) -> Value{
    let mut acc: Vec<Value> = Vec::new();
    for (key, val) in input{
        acc.push(Value::Vector(vec![prim_to_value(&key),prim_vec_to_value(&val)]));
    }
    Value::Vector(acc)
}

pub fn target_vec_to_value(input: &Vec<Target>) -> Value{
    let mut wires: Vec<usize> = Vec::new();
    let mut virtual_targets: Vec<usize> = Vec::new();
    for target in input{
        match target {
            Target::Wire(wire) => wires.extend(vec![wire.row, wire.column]),
            Target::VirtualTarget { index } => virtual_targets.push(*index),
        }
    }
    Value::Vector(vec![prim_vec_to_value(&wires), prim_vec_to_value(&virtual_targets)])
}

pub fn target_to_value(input: &Target) -> Value{
    match input {
        Target::Wire(wire) => prim_vec_to_value(&vec![wire.row, wire.column]),
        Target::VirtualTarget { index } => prim_to_value(index)
    }
}
