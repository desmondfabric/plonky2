
use core::any::Any;
use std::fs::File;
use std::io::Write;

use alloc::collections::BTreeMap;
use fabric_runtime::value::ToBigInt;
use fabric_runtime::{value::Value, protos::Message};
use fabric_runtime::protos::Edges;
use hashbrown::HashMap;
use plonky2_field::{extension::Extendable, types::PrimeField64};

use crate::gates::arithmetic_base::ArithmeticBaseGenerator;
use crate::iop::generator::{self, SimpleGenerator, SimpleGeneratorAdapter, ConstantGenerator, RandomValueGenerator};
use crate::util::serialization::{Buffer, Read};
use crate::{hash::hash_types::RichField, iop::{witness::PartialWitness, target::Target, generator::WitnessGeneratorRef}, gates::{lookup_table::LookupTable, lookup::{Lookup}}, fri::{FriConfig, reduction_strategies::FriReductionStrategy, FriParams, oracle::PolynomialBatch}};

use crate::hash::merkle_tree::MerkleTree;
use super::circuit_data::CommonCircuitData;
use super::{config::{GenericConfig, GenericHashOut, Hasher}, circuit_data::CircuitData, circuit_builder::LookupWire};

pub struct InputValue;
pub const PATH_TO_FABRIC: &str = "/home/desmond/fabric/Fabric/fabric/workloads/plonky2/tests/data/";

impl InputValue{
    pub fn prover_test_data<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>(
        partial_witness: &PartialWitness<F>,
        data: &CircuitData<F, C, D>,
        name: &str
    ) -> std::io::Result<()>{
        let mut res: Vec<(&'static str, usize)> = Vec::new();
        let mut edges = Edges::default();

        // common test data
        let common   = &data.common;
        //print!("{}", D);

        /*
        1. convert to edgevalue
        2. convert to edges
        3. create list of names
        let mut edges = protos::Edges::default();
         */
        edges.edges.push(Value::Scalar(F::order().to_bigint().unwrap()).to_edge_value());
        //edges.edges.push(Value::prime_from_str(F::order().to_str_radix(10).as_str()).to_edge_value());
        edges.edges.push(prim_to_value(&D).to_edge_value());
        //edges.edges.push(inner_vec_to_value(&common.luts, lookuptable_to_value).to_edge_value());
        edges.edges.push(prim_to_value(&common.quotient_degree()).to_edge_value());
        edges.edges.push(prim_to_value(&common.degree()).to_edge_value());
        edges.edges.push(prim_to_value(&common.num_partial_products).to_edge_value());
        edges.edges.push(f_vec_to_value(&common.k_is).to_edge_value());
        edges.edges.push(friparam_to_value(&common.fri_params).to_edge_value());

        res.push(("order", 1));
        res.push(("D", 1));
        //res.push(("luts", 1));
        res.push(("quotient_degree", 1));
        res.push(("degree", 1));
        res.push(("num_partial_products", 1));
        res.push(("k_is", 1));
        res.push(("fri_params", 1));

        let config = &common.config;
        edges.edges.push(prim_to_value(&config.num_routed_wires).to_edge_value());
        edges.edges.push(friconfig_to_value(&config.fri_config).to_edge_value());
        edges.edges.push(prim_to_value(&config.num_challenges).to_edge_value());
        edges.edges.push(prim_to_value(&config.num_wires).to_edge_value());
        edges.edges.push(bool_to_value(&config.zero_knowledge).to_edge_value());

        res.push(("num_routed_wires", 1));
        res.push(("friconfig", 1));
        res.push(("num_challenges", 1));
        res.push(("num_wires", 1));
        res.push(("zero_knowledge", 1));

        let prover = &data.prover_only;

        // currently:
        // list of watch_lists

        // need:
        // generator_targets: [watch_lists] -> [[targets]]
        // generator_targets_types: [[watch_lists types]]
        // let generator  = generators_to_value(&prover.generators);
        // edges.edges.push(generator.to_edge_value());
        // res.push(("generators_targets", 1));
        // generator_params: [[witness id, witness param]]
        let generators = generator_to_params(&prover.generators, common);
        res.push(("generators", generators.len()));
        edges.edges.push(Value::Vector(generators).to_edge_value());

        let generator_indices_by_watches = map_to_value(&prover.generator_indices_by_watches);
        res.push(("generator_indices_by_watches_keys", generator_indices_by_watches.0.len()));
        res.push(("generator_indices_by_watches_values", generator_indices_by_watches.1.len()));
        edges.edges.push(Value::Vector(generator_indices_by_watches.0).to_edge_value());
        edges.edges.push(prim_vec_to_value(&generator_indices_by_watches.1).to_edge_value());

        edges.edges.push(prim_vec_to_value(&prover.representative_map).to_edge_value());
        //edges.edges.push(inner_vec_to_value(&prover.lut_to_lookups, lookup_to_value).to_edge_value());
        edges.edges.push(f_vec_to_value(&prover.circuit_digest.to_vec()).to_edge_value());
        edges.edges.push(f_vec_to_value(&prover.subgroup).to_edge_value());
        edges.edges.push(inner_vec_to_value(&prover.sigmas, f_vec_to_value).to_edge_value());
        edges.edges.push(polynomial_batch_to_value(&prover.constants_sigmas_commitment).to_edge_value());
        edges.edges.push(target_vec_to_value(&prover.public_inputs).to_edge_value());
        //edges.edges.push(inner_vec_to_value(&prover.lookup_rows, lookup_wire_to_value).to_edge_value());

        res.push(("representative_map", 1));
        //res.push(("lut_to_lookups", 1));
        res.push(("circuit_digest", 1));
        res.push(("subgroup", 1));
        res.push(("sigmas", 1));
        res.push(("constants_sigmas_commitment", 1));
        res.push(("public_inputs", 1));
        //res.push(("lookup_rows", 1));

        if prover.fft_root_table.is_some() {
            edges.edges.push(inner_vec_to_value(prover.fft_root_table.as_ref().unwrap(), f_vec_to_value).to_edge_value());
            res.push(("fft_root_table", 1));
        }
        // target_keys: [[target_type,r/i,c/0]]
        let target_keys = target_vec_to_value_2(&partial_witness.target_values.keys().cloned().collect());
        res.push(("target_keys", target_keys.len()));
        edges.edges.push(Value::Vector(target_keys).to_edge_value());
        //target_values: [val]
        let target_values: &Vec<u64> = &partial_witness.target_values.values().map(|val| val.to_canonical_u64()).collect();
        res.push(("target_values", target_values.len()));
        edges.edges.push(prim_vec_to_value(&target_values).to_edge_value());

        save_res_to_file(res, format!("{}{}_names.txt", PATH_TO_FABRIC, name))?;
        edges_to_bin(edges, format!("{}{}_edges.bin", PATH_TO_FABRIC, name))?;

        Ok(())
    }
}

fn edges_to_bin(edges: Edges, file_path: String) -> std::io::Result<()> {
    
    let serialized_data = edges.encode_to_vec();

    // Write the binary data to the file
    let mut file = File::create(&file_path)?;
    file.write_all(&serialized_data)?;

    println!("Protobuf data written to {} successfully.", file_path);

    Ok(())
}

fn print_length<T>(input: &Vec<Vec<T>>, name: &str){
    let mut lengths: Vec<usize> = Vec::new();
    for ele in input{
        lengths.push(ele.len());
    }
    println!("{}:{:?}", name, lengths);

}

/* */


fn save_res_to_file(vals: Vec<(&'static str, usize)>, file_path: String) -> std::io::Result<()> {
    let mut file = File::create(file_path)?;

    writeln!(file, "[")?;
    for (name, length) in vals.iter() {
        writeln!(file, "  (\"{}\", {}),", name, length)?;
    }
    writeln!(file, "]")?;

    Ok(())
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

pub fn generator_to_params<F: RichField + Extendable<D>, const D: usize>
    (input: &Vec<WitnessGeneratorRef<F,D>>, common_data: &CommonCircuitData<F,D>) -> Vec<Value>{
    let mut params_list: Vec<Value> = Vec::new();
    for witness_generator_ref in input{
        // split values
        let mut params: Vec<u64> = Vec::new();
        let mut serialized_data: Vec<u8> = Vec::new();
        let generator = &witness_generator_ref.0;
        // let generator_any = &*generator as &dyn Any;
        let id = generator.id();
        let _ = generator.serialize(&mut serialized_data, common_data);
        let mut buf = Buffer::new(serialized_data.as_slice());
        if id == "ConstantGenerator" {
            params.push(0);
            params.push(buf.read_usize().unwrap().try_into().unwrap());
            params.push(buf.read_usize().unwrap().try_into().unwrap());
            params.push(buf.read_usize().unwrap().try_into().unwrap());
            params.push(buf.read_field::<F>().unwrap().to_canonical_u64());
        }
        if id == "ArithmeticBaseGenerator" {
            params.push(1);
            params.push(buf.read_usize().unwrap().try_into().unwrap());
            params.push(buf.read_field::<F>().unwrap().to_canonical_u64());
            params.push(buf.read_field::<F>().unwrap().to_canonical_u64());
            params.push(buf.read_usize().unwrap().try_into().unwrap());
        }
        if id == "RandomValueGenerator" {
            params.push(2);
            let target = buf.read_target().unwrap();
            match target {
                Target::Wire(wire) => {
                    params.push(1);
                    params.push(wire.row.try_into().unwrap());
                    params.push(wire.column.try_into().unwrap());
                }
                Target::VirtualTarget { index } => {
                    params.push(0);
                    params.push(index.try_into().unwrap());
                    params.push(0);
                }
            }
            params.push(0);
        }
        if id == "PoseidonGenerator" {
            params.push(3);
            params.push(buf.read_usize().unwrap().try_into().unwrap());
            params.push(0);
            params.push(0);
            params.push(0);
        }
        params_list.push(prim_vec_to_value(&params));
    }
    params_list
}
pub fn flat_target_vec(input: &Vec<Vec<Target>>) -> Value {
    let mut targets: Vec<Value> = Vec::new();
    for watchlist in input {
        targets.push(Value::Vector(target_vec_to_value_2(watchlist)));
    }
    Value::Vector(targets)
}

// pub fn  generators_to_value<F: RichField + Extendable<D>, const D: usize>(input: &Vec<WitnessGeneratorRef<F,D>>) -> Value{
//     let mut watch_list_types: HashMap<String,usize> = HashMap::new();
//     for watch_list in input{
//         let id = watch_list.0.id().clone();
//         let entry = watch_list_types.entry(id).or_insert(0);
//         *entry += 1;
//     }
//     let mut random_value_generators: Vec<Value> = Vec::new();
//     let mut poseidon_generators:
//     for watchlist in input {
//         targets.push(target_vec_to_value_2(watchlist));
//     }
//     Value::Vector(targets)
//     println!("{:?}", watch_list_types);
//     let watch_lists: &Vec<Vec<Target>> = &input
//         .iter().map(|gen_ref| gen_ref.0.watch_list()).collect();
//     //print_length(&watch_lists,"watchlists");
//     flat_target_vec(&watch_lists)
// }

pub fn map_to_value(input: &BTreeMap<usize, Vec<usize>>) -> (Vec<Value>, Vec<usize>){
    let mut key_list: Vec<Value> = Vec::new();
    let mut value_list: Vec<usize> = Vec::new();
    let mut map = HashMap::<usize, usize>::new();
    for val in input.values(){
        let entry = map.entry(val.len()).or_insert(0);
        *entry += 1;
        //println!("{}:{}", watch_list.0.id(), watch_list.0.watch_list().len());
    }
    println!("{:?}", map);
    for (key, val) in input{
        //println!("{}", val.len());
        key_list.push(prim_to_value(&key));
        value_list.push(val.len());
        value_list.extend(val);
    }
    (key_list, value_list)
}
// [[]]
pub fn target_vec_to_value(input: &Vec<Target>) -> Value {
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

pub fn target_vec_to_value_2(input: &Vec<Target>) -> Vec<Value> {
    let mut targets: Vec<Value> = Vec::new();
    for target in input{
        targets.push(prim_vec_to_value(&target_to_vec(target)));
    }
    targets
}

pub fn target_to_value(input: &Target) -> Value {
    match input {
        Target::Wire(wire) => prim_vec_to_value(&vec![wire.row, wire.column]),
        Target::VirtualTarget { index } => prim_to_value(index)
    }
}

pub fn target_to_vec(input: &Target) -> Vec<usize>{
    match input {
        Target::Wire(wire) => vec![1, wire.row, wire.column],
        Target::VirtualTarget { index } => vec![0, *index, 0]
    }
}