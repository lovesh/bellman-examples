use pairing::{
    Engine,
    Field,
    PrimeField,
    PrimeFieldRepr
};

use pairing::bls12_381::{Bls12, Fr, FrRepr};

use bellman::{Circuit, ConstraintSystem, SynthesisError, LinearCombination, Variable};

use bellman::groth16::{
    Proof,
    generate_random_parameters,
    prepare_verifying_key,
    create_random_proof,
    verify_proof,
};

use mimc::{mimc, MiMCDemo, MIMC_ROUNDS};
use std::collections::HashMap;
use std::ops::{Add, Sub};
use merkle_tree::utils::*;


type DBVal<E: Engine> = (E::Fr, E::Fr);

pub struct VanillaSparseMerkleTree<'a, E: Engine> {
    pub depth: usize,
    empty_tree_hashes: Vec<E::Fr>,
    db: HashMap<Vec<u8>, DBVal<E>>,
    hash_constants: &'a [E::Fr],
    pub root: E::Fr
}

impl<'a, E: Engine> VanillaSparseMerkleTree<'a, E> {
    pub fn new(hash_constants: &'a [E::Fr]) -> VanillaSparseMerkleTree<'a, E> {
        let depth = 256;
        let mut db = HashMap::new();
        let mut empty_tree_hashes: Vec<E::Fr> = vec![];
        empty_tree_hashes.push(E::Fr::zero());
        for i in 1..=depth {
            let prev = empty_tree_hashes[i-1];
            let new = mimc::<E>(prev, prev, hash_constants);
            let key = field_elem_to_bytes::<E>(&new);

            db.insert(key, (prev, prev));
            empty_tree_hashes.push(new);
        }

        let root = empty_tree_hashes[depth].clone();

        VanillaSparseMerkleTree {
            depth,
            empty_tree_hashes,
            db,
            hash_constants,
            root
        }
    }

    pub fn update(&mut self, idx: E::Fr, val: E::Fr) -> E::Fr {
        let mut sidenodes: Vec<E::Fr> = vec![];
        let depth_minus_1 = (self.depth - 1) as u32;
        let mut cur_node = self.root.clone();
        let mut cur_idx = idx.into_repr();

        for i in 0..self.depth {
            let k = field_elem_to_bytes::<E>(&cur_node);
            let v = self.db.get(&k).unwrap();
            if is_msb_zero!(cur_idx, self.depth as u32) {
                sidenodes.push(v.1);
                cur_node = v.0;
            } else {
                sidenodes.push(v.0);
                cur_node = v.1;
            }
            //cur_idx.shl(1);
            cur_idx.mul2();
        }

        let mut cur_idx = idx.into_repr();
        let mut cur_val = val.clone();

        for i in 0..self.depth {
            let side_elem = sidenodes.pop().unwrap();
            let new_val = {
                if cur_idx.is_odd() {
                    let nv =  mimc::<E>(side_elem, cur_val, self.hash_constants);
                    let key = field_elem_to_bytes::<E>(&nv);
                    self.db.insert(key, (side_elem, cur_val));
                    nv
                } else {
                    let nv =  mimc::<E>(cur_val, side_elem, self.hash_constants);
                    let key = field_elem_to_bytes::<E>(&nv);
                    self.db.insert(key, (cur_val, side_elem));
                    nv
                }
            };
            //println!("Root at level {} is {:?}", i, &cur_val);
            //cur_idx.shr(1);
            cur_idx.div2();
            cur_val = new_val;
        }

        self.root = cur_val;

        cur_val
    }

    pub fn get(&self, idx: E::Fr, proof: &mut Option<Vec<E::Fr>>) -> E::Fr {
        let depth_minus_1 = (self.depth - 1) as u32;
        let mut cur_idx = idx.into_repr();
        let mut cur_node = self.root.clone();

        let need_proof = proof.is_some();
        let mut proof_vec = Vec::<E::Fr>::new();

        for i in 0..self.depth {
            let k = field_elem_to_bytes::<E>(&cur_node);
            let v = self.db.get(&k).unwrap();
            if is_msb_zero!(cur_idx, self.depth as u32) {
                cur_node = v.0;
                if need_proof { proof_vec.push(v.1); }
            } else {
                cur_node = v.1;
                if need_proof { proof_vec.push(v.0); }
            }
            //cur_idx.shl(1);
            cur_idx.mul2();
        }

        match proof {
            Some(v) => {
                v.extend_from_slice(&proof_vec);
            }
            None => ()
        }

        cur_node
    }

    pub fn verify_proof(&self, idx: E::Fr, val: E::Fr, proof: &[E::Fr], root: Option<&E::Fr>) -> bool {
        let mut cur_idx = idx.into_repr();
        let mut cur_val = val.clone();

        for i in 0..self.depth {
            cur_val = {
                if cur_idx.is_odd() {
                    mimc::<E>(proof[self.depth-1-i], cur_val, self.hash_constants)
                } else {
                    mimc::<E>(cur_val, proof[self.depth-1-i], self.hash_constants)
                }
            };

            //cur_idx.shr(1);
            cur_idx.div2();
        }

        // Check if root is equal to cur_val
        match root {
            Some(r) => {
                are_equal_mut::<E>(cur_val, r)
            }
            None => {
                are_equal_mut::<E>(cur_val, &self.root)
            }
        }
    }
}

pub struct VSMTVerif<'a, E: Engine> {
    pub depth: usize,
    pub leaf_val: E::Fr,
    leaf_index_bits: Option<Vec<E::Fr>>,
    proof_nodes: Option<Vec<E::Fr>>,
    mimc_constants: &'a [E::Fr]
}

/// left = (1-leaf_side) * leaf + (leaf_side * proof_node)
/// right = leaf_side * leaf + ((1-leaf_side) * proof_node))
impl<'a, E: Engine> Circuit<E> for VSMTVerif<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        /*let leaf_index_bits = self.leaf_index_bits;
        let proof_nodes = self.proof_nodes;*/

        //let leaf_lc: LinearCombination<E> = vec![(self.leaf_val, CS::one())].into();
        let leaf_lc = LinearCombination::<E>::zero() + (self.leaf_val, CS::one());
        let one = E::Fr::one();
        let one_lc = LinearCombination::<E>::zero() + (one.clone(), CS::one());

        let mut last_hash: (Option<E::Fr>, Variable) = (None, CS::one());

        for i in 0..self.depth {
            let cs = &mut cs.namespace(|| format!("tree depth {}", i));

            let (mut left_val, mut left, mut right_val, mut right) = if i == 0 {
                /*let leaf_side_val = leaf_index_bits.map(|bits| {
                    bits[i]
                });*/
                let leaf_side_val = match &self.leaf_index_bits {
                    Some(bits) => Some(bits[i]),
                    None => None
                };

                /*let proof_node_val = proof_nodes.map(|nodes| {
                    nodes[i]
                });*/
                let proof_node_val = match &self.proof_nodes {
                    Some(nodes) => Some(nodes[i]),
                    None => None
                };

                // 0 for `leaf_side` indicates leaf is on the left, 1 indicates its on right
                let leaf_side = cs.alloc(|| "leaf side", || {
                    leaf_side_val.ok_or(SynthesisError::AssignmentMissing)
                })?;

                // 0 for `proof_node` indicates proof node is on the left, 1 indicates its on right
                let proof_node = cs.alloc(|| "proof node", || {
                    proof_node_val.ok_or(SynthesisError::AssignmentMissing)
                })?;

                let one_minus_leaf_side_val = leaf_side_val.map(|v| {
                    let mut l = one.clone();
                    l.sub_assign(&v);
                    l
                });
                let mut one_minus_leaf_side = cs.alloc(|| "one_minus_leaf_side", || {
                    one_minus_leaf_side_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                let mut left_1_val = one_minus_leaf_side_val.map(|v| {
                    let mut l1 = v.clone();
                    l1.mul_assign(&self.leaf_val);
                    l1
                });
                let mut left_1 = cs.alloc(|| "left_1", || {
                    left_1_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || " (1-leaf_side) * leaf",
                    |lc| lc + one_minus_leaf_side,
                    |lc| lc + (self.leaf_val, CS::one()),
                    |lc| lc + left_1
                );

                let mut left_2_val = match (leaf_side_val, proof_node_val) {
                    (Some(l), Some(p)) => {
                        let mut l2 = l.clone();
                        l2.mul_assign(&p);
                        Some(l2)
                    },
                    _ => None
                };
                let mut left_2 = cs.alloc(|| "left_2", || {
                    left_2_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || " leaf_side * proof_node",
                    |lc| lc + leaf_side,
                    |lc| lc + proof_node,
                    |lc| lc + left_2
                );

                let left_val = match (left_1_val, left_2_val) {
                    (Some(l1), Some(l2)) => {
                        let mut s = l1.clone();
                        s.add_assign(&l2);
                        Some(s)
                    },
                    _ => None
                };
                let mut left = cs.alloc(|| "left", || {
                    left_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || " left_1 + left_2 = left",
                    |lc| lc + left_1 + left_2,
                    |lc| lc + CS::one(),
                    |lc| lc + left
                );

                let mut right_1_val = leaf_side_val.map( |e| {
                    let mut r1 = e.clone();
                    r1.mul_assign(&self.leaf_val);
                    r1
                });
                let mut right_1 = cs.alloc(|| "right_1", || {
                    right_1_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || " leaf_side * leaf",
                    |lc| lc + leaf_side,
                    |lc| lc + (self.leaf_val, CS::one()),
                    |lc| lc + right_1
                );

                let mut right_2_val = match (one_minus_leaf_side_val, proof_node_val) {
                    (Some(l), Some(p)) => {
                        let mut r2 = l.clone();
                        r2.mul_assign(&p);
                        Some(r2)
                    },
                    _ => None
                };
                let mut right_2 = cs.alloc(|| "right_2", || {
                    right_2_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || " (1-leaf_side) * proof_node",
                    |lc| lc + one_minus_leaf_side,
                    |lc| lc + proof_node,
                    |lc| lc + right_2
                );

                let right_val = match (right_1_val, right_2_val) {
                    (Some(r1), Some(r2)) => {
                        let mut s = r1.clone();
                        s.add_assign(&r2);
                        Some(s)
                    },
                    _ => None
                };
                let mut right = cs.alloc(|| "right", || {
                    right_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || " right_1 + right_2 = right",
                    |lc| lc + right_1 + right_2,
                    |lc| lc + CS::one(),
                    |lc| lc + right
                );

                (left_val, left, right_val, right)
            } else {
                let (prev_hash_val, prev_hash) = last_hash;

                let leaf_side_val = match &self.leaf_index_bits {
                    Some(bits) => Some(bits[i]),
                    None => None
                };

                let proof_node_val = match &self.proof_nodes {
                    Some(nodes) => Some(nodes[i]),
                    None => None
                };

                // 0 for `leaf_side` indicates leaf is on the left, 1 indicates its on right
                let leaf_side = cs.alloc(|| "leaf side", || {
                    leaf_side_val.ok_or(SynthesisError::AssignmentMissing)
                })?;

                // 0 for `proof_node` indicates proof node is on the left, 1 indicates its on right
                let proof_node = cs.alloc(|| "proof node", || {
                    proof_node_val.ok_or(SynthesisError::AssignmentMissing)
                })?;

                let one_minus_leaf_side_val = leaf_side_val.map(|v| {
                    let mut l = one.clone();
                    l.sub_assign(&v);
                    l
                });
                let mut one_minus_leaf_side = cs.alloc(|| "one_minus_leaf_side", || {
                    one_minus_leaf_side_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                let mut left_1_val = one_minus_leaf_side_val.map(|v| {
                    let mut l1 = v.clone();
                    l1.mul_assign(&prev_hash_val.unwrap());
                    l1
                });
                let mut left_1 = cs.alloc(|| "left_1", || {
                    left_1_val.ok_or(SynthesisError::AssignmentMissing)
                })?;

                let mut left_2_val = match (leaf_side_val, proof_node_val) {
                    (Some(l), Some(p)) => {
                        let mut l2 = l.clone();
                        l2.mul_assign(&p);
                        Some(l2)
                    },
                    _ => None
                };
                let mut left_2 = cs.alloc(|| "left_2", || {
                    left_2_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || " leaf_side * proof_node",
                    |lc| lc + leaf_side,
                    |lc| lc + proof_node,
                    |lc| lc + left_2
                );

                let left_val = match (left_1_val, left_2_val) {
                    (Some(l1), Some(l2)) => {
                        let mut s = l1.clone();
                        s.add_assign(&l2);
                        Some(s)
                    },
                    _ => None
                };
                let mut left = cs.alloc(|| "left", || {
                    left_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || " left_1 + left_2 = left",
                    |lc| lc + left_1 + left_2,
                    |lc| lc + CS::one(),
                    |lc| lc + left
                );

                let mut right_1_val = leaf_side_val.map( |e| {
                    let mut r1 = e.clone();
                    r1.mul_assign(&prev_hash_val.unwrap());
                    r1
                });
                let mut right_1 = cs.alloc(|| "right_1", || {
                    right_1_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || " leaf_side * leaf",
                    |lc| lc + leaf_side,
                    |lc| lc + prev_hash,
                    |lc| lc + right_1
                );

                let mut right_2_val = match (one_minus_leaf_side_val, proof_node_val) {
                    (Some(l), Some(p)) => {
                        let mut r2 = l.clone();
                        r2.mul_assign(&p);
                        Some(r2)
                    },
                    _ => None
                };
                let mut right_2 = cs.alloc(|| "right_2", || {
                    right_2_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || " (1-leaf_side) * proof_node",
                    |lc| lc + one_minus_leaf_side,
                    |lc| lc + proof_node,
                    |lc| lc + right_2
                );

                let right_val = match (right_1_val, right_2_val) {
                    (Some(r1), Some(r2)) => {
                        let mut s = r1.clone();
                        s.add_assign(&r2);
                        Some(s)
                    },
                    _ => None
                };
                let mut right = cs.alloc(|| "right", || {
                    right_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || " right_1 + right_2 = right",
                    |lc| lc + right_1 + right_2,
                    |lc| lc + CS::one(),
                    |lc| lc + right
                );

                (left_val, left, right_val, right)
            };

            let (hash_val, hash) = hash_2(cs, left_val, left, right_val, right, i==(self.depth-1), MIMC_ROUNDS, self.mimc_constants)?;

            last_hash = (hash_val, hash);
        }

        Ok(())
    }
}

mod tests {
    use super::*;
    // For randomness (during paramgen and proof generation)
    use rand::{thread_rng, Rng};
    use mimc::MIMC_ROUNDS;
    use testing_cs::TestConstraintSystem;
    use std::time::{Duration, Instant};

    #[test]
    fn test_VSMT() {
        let rng = &mut thread_rng();

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();

        let mut tree = VanillaSparseMerkleTree::<Bls12>::new(&constants);
        let (k0, v0) = (Fr::from_str("0").unwrap(), Fr::from_str("1").unwrap());
        let (k1, v1) = (Fr::from_str("1").unwrap(), Fr::from_str("1").unwrap());
        let (k2, v2) = (Fr::from_str("2").unwrap(), Fr::from_str("2").unwrap());
        let (k8, v8) = (Fr::from_str("8").unwrap(), Fr::from_str("8").unwrap());


        tree.update(k0, v0);
        tree.update(k1, v1);
        tree.update(k2, v2);
        tree.update(k8, v8);

        assert_eq!(v0, tree.get(k0, &mut None));
        assert_eq!(v1, tree.get(k1, &mut None));
        assert_eq!(v2, tree.get(k2, &mut None));

        let mut proof_vec = Vec::<Fr>::new();
        let mut proof = Some(proof_vec);
        assert_eq!(v8, tree.get(k8, &mut proof));
        proof_vec = proof.unwrap();
        println!("proof length = {:?}", &proof_vec.len());
        assert!(tree.verify_proof(k8, v8, &proof_vec, None));
        assert!(tree.verify_proof(k8, v8, &proof_vec, Some(&tree.root)));


        // Some random key values
        let mut kvs: Vec<(Fr, Fr)> = (0..100).map(|_| (rng.gen(), rng.gen())).collect();
        for i in 0..kvs.len() {
            tree.update(kvs[0].0, kvs[0].1);
        }

        for i in 0..kvs.len() {
            let mut proof_vec = Vec::<Fr>::new();
            let mut proof = Some(proof_vec);
            assert_eq!(kvs[0].1, tree.get(kvs[0].0, &mut proof));
            proof_vec = proof.unwrap();
            assert!(tree.verify_proof(kvs[0].0, kvs[0].1, &proof_vec, None));
            assert!(tree.verify_proof(kvs[0].0, kvs[0].1, &proof_vec, Some(&tree.root)));
        }
    }

    #[test]
    fn test_VSMT_Verif_with_TestConstraintSystem() {
        let rng = &mut thread_rng();

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();
        let mut tree = VanillaSparseMerkleTree::<Bls12>::new(&constants);
        let (k0, v0) = (Fr::from_str("0").unwrap(), Fr::from_str("0").unwrap());
        let (k1, v1) = (Fr::from_str("1").unwrap(), Fr::from_str("1").unwrap());
        let (k2, v2) = (Fr::from_str("2").unwrap(), Fr::from_str("0").unwrap());
        let (k8, v8) = (Fr::from_str("8").unwrap(), Fr::from_str("0").unwrap());
        let (k9, v9) = (Fr::from_str("9").unwrap(), Fr::from_str("1").unwrap());

        tree.update(k0, v0);
        tree.update(k1, v1);
        tree.update(k2, v2);
        tree.update(k8, v8);
        tree.update(k9, v9);

        let root = tree.root.clone();
        let depth = tree.depth.clone();
        let mut merkle_proof_vec = Vec::<Fr>::new();
        let mut merkle_proof = Some(merkle_proof_vec);
        tree.get(k8, &mut merkle_proof);
        merkle_proof_vec = merkle_proof.unwrap();

        assert!(tree.verify_proof(k8, v8, &merkle_proof_vec, Some(&root)));

        println!("root={:?}", &root);
        println!("root_repr={:?}", &root.into_repr());

        // Reverse proof vector since it contains proof nodes from top to bottom of tree, i.e. root node is first item
        merkle_proof_vec.reverse();
        let mut cs = TestConstraintSystem::<Bls12>::new();
        let c = VSMTVerif::<Bls12> {
            depth,
            leaf_val: v8,
            leaf_index_bits: Some(field_elem_to_bitvec::<Bls12>(k8, 256)),
            proof_nodes: Some(merkle_proof_vec),
            mimc_constants: &constants
        };

        c.synthesize(&mut cs).unwrap();
        let satisfied = cs.is_satisfied();
        assert!(satisfied);
        println!("Num constraints {}", &cs.num_constraints());
        let mut root_from_circuit = cs.get(&format!("tree depth {}/mimc round {}/root", depth-1, MIMC_ROUNDS-1));
        println!("Root from circuit {:?}", &root_from_circuit);
        println!("Root_repr from circuit {:?}", &root_from_circuit.into_repr());

        assert!(are_equal_mut::<Bls12>(root_from_circuit, &root));
    }

    #[test]
    fn test_VSMT_Verif() {
        let rng = &mut thread_rng();

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();
        let mut tree = VanillaSparseMerkleTree::<Bls12>::new(&constants);
        let (k0, v0) = (Fr::from_str("0").unwrap(), Fr::from_str("0").unwrap());
        let (k1, v1) = (Fr::from_str("1").unwrap(), Fr::from_str("1").unwrap());
        let (k2, v2) = (Fr::from_str("2").unwrap(), Fr::from_str("0").unwrap());
        let (k8, v8) = (Fr::from_str("8").unwrap(), Fr::from_str("0").unwrap());
        let (k9, v9) = (Fr::from_str("9").unwrap(), Fr::from_str("1").unwrap());

        tree.update(k0, v0);
        tree.update(k1, v1);
        tree.update(k2, v2);
        tree.update(k8, v8);
        tree.update(k9, v9);

        let root = tree.root.clone();
        let depth = tree.depth.clone();
        let mut merkle_proof_vec = Vec::<Fr>::new();
        let mut merkle_proof = Some(merkle_proof_vec);
        tree.get(k8, &mut merkle_proof);
        merkle_proof_vec = merkle_proof.unwrap();

        assert!(tree.verify_proof(k8, v8, &merkle_proof_vec, Some(&root)));

        println!("Creating parameters...");

        // Create parameters for our circuit
        let params = {
            let c = VSMTVerif::<Bls12> {
                depth,
                leaf_val: v8,
                leaf_index_bits: None,
                proof_nodes: None,
                mimc_constants: &constants
            };

            generate_random_parameters(c, rng).unwrap()
        };

        // Prepare the verification key (for proof verification)
        let pvk = prepare_verifying_key(&params.vk);

        println!("Creating proofs...");

        // Reverse proof vector since it contains proof nodes from top to bottom of tree, i.e. root node is first item
        merkle_proof_vec.reverse();

        // Create a groth16 proof with our parameters.
        let c = VSMTVerif::<Bls12> {
            depth,
            leaf_val: v8,
            leaf_index_bits: Some(field_elem_to_bitvec::<Bls12>(k8, 256)),
            proof_nodes: Some(merkle_proof_vec),
            mimc_constants: &constants
        };
        let mut start = Instant::now();
        let proof = create_random_proof(c, &params, rng).unwrap();
        println!("Proof gen time with vanilla sparse merkle tree {:?}", start.elapsed());

        start = Instant::now();
        assert!(verify_proof(
            &pvk,
            &proof,
            &[root]
        ).unwrap());
        println!("Proof verification time with vanilla sparse merkle tree {:?}", start.elapsed());
    }
}