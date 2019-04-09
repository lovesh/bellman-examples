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


// TODO: Use enum
type DBVal<E: Engine> = (Option<bool>, E::Fr, E::Fr);



pub struct OptmzSparseMerkleTree<'a, E: Engine> {
    pub depth: usize,
    empty_tree_hashes: Vec<E::Fr>,
    db: HashMap<Vec<u8>, DBVal<E>>,
    hash_constants: &'a [E::Fr],
    pub root: E::Fr
}

impl<'a, E: Engine> OptmzSparseMerkleTree<'a, E> {
    pub fn new(hash_constants: &'a [E::Fr]) -> OptmzSparseMerkleTree<'a, E> {
        let depth = 256;
        let mut db = HashMap::new();
        let mut empty_tree_hashes: Vec<E::Fr> = vec![];
        empty_tree_hashes.push(E::Fr::zero());
        for _ in 0..depth {
            let prev = empty_tree_hashes[0];
            let new = mimc::<E>(prev, prev, hash_constants);
            empty_tree_hashes.insert(0, new);
        }

        let root = empty_tree_hashes[0].clone();

        OptmzSparseMerkleTree {
            depth,
            empty_tree_hashes,
            db,
            hash_constants,
            root
        }
    }

    pub fn update(&mut self, idx: E::Fr, val: E::Fr) -> E::Fr {
        let old_root = &self.root.clone();
        let new_root = self._update(idx.into_repr(), val, old_root, 0);
        self.root = new_root.clone();
        new_root
    }

    pub fn get(&self, idx: E::Fr, proof: &mut Option<Vec<DBVal<E>>>) -> E::Fr {
        let mut cur_idx = idx.into_repr();
        let mut cur_node = self.root.clone();

        let need_proof = proof.is_some();
        let mut proof_vec = Vec::<DBVal<E>>::new();

        for i in 0..self.depth {
            if are_equal::<E>(&cur_node, &self.empty_tree_hashes[i]) {
                println!("Root:Num bits of child node idx={}", cur_idx.num_bits());
                cur_node = E::Fr::zero();
                break
            }

            let v = self.get_from_db(&cur_node);
            if need_proof { proof_vec.push(v.clone()); }

            println!("Loop: cur_idx {:?}", &cur_idx);
            println!("Loop: cur_idx reduced {:?}", &reduce_field_repr_to_elem::<E>(cur_idx));
            println!("Loop: db key {:?}", &cur_node);
            println!("Loop: k-v {:?}", v);
            if v.0.is_some() {
                //if are_equal::<E>(&E::Fr::from_repr(cur_idx).unwrap(), &v.1) {
                println!("1Child:Num bits of child node idx={}", cur_idx.num_bits());
                println!("1Child:cur_idx={:?}", &cur_idx);
                println!("1Child:cur_idx reduced={:?}", &reduce_field_repr_to_elem::<E>(cur_idx));
                if are_equal::<E>(&reduce_field_repr_to_elem::<E>(cur_idx), &v.1) {
                    cur_node =  v.2;
                    break
                } else {
                    println!("1Child:found 0 for key val {:?}={:?}", &v.1, &v.2);
                    cur_node =  E::Fr::zero();
                    break
                }
            }

            if is_msb_zero!(cur_idx, self.depth as u32) {
                cur_node = v.1;
            } else {
                cur_node = v.2;

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

    pub fn verify_proof(&self, idx: E::Fr, val: E::Fr, proof: &[DBVal<E>], root: &E::Fr) -> bool {
        if are_equal::<E>(&root, &self.empty_tree_hashes[0]) {
            return proof.len() == 0
        }

        let mut prev_hash: E::Fr = root.clone();

        let mut path = idx.into_repr();

        for i in 0..proof.len() {
            let proof_node = proof[i];
            if proof_node.0.is_some() {
                //let rhs = E::Fr::from_repr(path).unwrap();
                let rhs = reduce_field_repr_to_elem::<E>(path);
                if are_equal::<E>(&proof_node.1, &rhs) {
                    return are_equal::<E>(&proof_node.2, &val)
                } else {
                    return val.is_zero()
                }
            } else {
                let expected_hash = mimc::<E>(proof_node.1.clone(), proof_node.2.clone(), self.hash_constants);
                if !are_equal::<E>(&expected_hash, &prev_hash) {
                    return false
                }

                if is_msb_zero!(path, self.depth as u32) {
                    prev_hash = proof_node.1.clone()
                } else {
                    prev_hash = proof_node.2.clone()
                }
            }

            path.mul2();
        }

        if proof.len() == self.depth {
            are_equal::<E>(&prev_hash, &val)
        } else {
            val.is_zero()
        }
    }

    fn _update(&mut self, path: <E::Fr as PrimeField>::Repr, val: E::Fr, root: &E::Fr, depth: usize) -> E::Fr {
        if depth == self.depth {
            return val
        }

        if are_equal::<E>(root, &self.empty_tree_hashes[depth]) {
            let new_root = self.get_subtree_with_one_val(path, &val, depth);
            self.update_db_with_key_value(&new_root,
                                          //(Some(true), E::Fr::from_repr(path).unwrap(), val));
                                          (Some(true), reduce_field_repr_to_elem::<E>(path), val));
            return new_root
        }

        //println!("_update with depth {}", &depth);
        let child = self.get_from_db(&root).clone();
        if child.0.is_some() {
            return self.update_one_val_subtree(path, val.clone(),
                                                       child.1.into_repr(), child.2.clone(), depth)
        } else {
            let mut new_path = path.clone();
            new_path.mul2();
            if is_msb_zero!(path, self.depth as u32) {
                let new_left = self._update(new_path, val, &child.1, depth+1);
                let root = mimc::<E>(new_left.clone(), child.2.clone(), self.hash_constants);
                self.update_db_with_key_value(&root, (None, new_left, child.2.clone()));
                return root
            } else {
                let new_right = self._update(new_path, val, &child.2, depth+1);
                let root = mimc::<E>(child.1.clone(), new_right.clone(), self.hash_constants);
                self.update_db_with_key_value(&root, (None, child.1.clone(), new_right));
                return root
            }
        }
    }

    fn update_one_val_subtree(&mut self, path_for_new_key: <E::Fr as PrimeField>::Repr,
                              val_for_new_key: E::Fr, path_for_old_key: <E::Fr as PrimeField>::Repr,
                              val_for_old_key: E::Fr, depth: usize) -> E::Fr {
        if depth == self.depth {
            panic!("Error in update_one_val_subtree")
        }

        let (left, right) = {
            let mut next_new_path = path_for_new_key.clone();
//            next_new_path.shl(1);
            next_new_path.mul2();
            let mut next_old_path = path_for_old_key.clone();
//            next_old_path.shl(1);
            next_old_path.mul2();
            if is_msb_zero!(path_for_new_key, self.depth as u32) {
                if is_msb_zero!(path_for_old_key, self.depth as u32) {
                    (self.update_one_val_subtree(next_new_path, val_for_new_key,
                                                 next_old_path, val_for_old_key, depth+1),
                     self.empty_tree_hashes[depth+1].clone())
                } else {
                    let left_subtree_hash = self.get_subtree_with_one_val(next_new_path, &val_for_new_key, depth+1);
                    let right_subtree_hash = self.get_subtree_with_one_val(next_old_path, &val_for_old_key, depth+1);
                    self.update_db_with_key_value(&left_subtree_hash, (Some(true), reduce_field_repr_to_elem::<E>(next_new_path), val_for_new_key));
                    self.update_db_with_key_value(&right_subtree_hash, (Some(true), reduce_field_repr_to_elem::<E>(next_old_path), val_for_old_key));
                    (left_subtree_hash, right_subtree_hash)
                }
            } else {
                if is_msb_zero!(path_for_old_key, self.depth as u32) {
                    let left_subtree_hash = self.get_subtree_with_one_val(next_old_path, &val_for_old_key, depth+1);
                    let right_subtree_hash = self.get_subtree_with_one_val(next_new_path, &val_for_new_key, depth+1);
                    self.update_db_with_key_value(&left_subtree_hash, (Some(true), reduce_field_repr_to_elem::<E>(next_old_path), val_for_old_key));
                    self.update_db_with_key_value(&right_subtree_hash, (Some(true), reduce_field_repr_to_elem::<E>(next_new_path), val_for_new_key));
                    (left_subtree_hash, right_subtree_hash)
                } else {
                    (self.empty_tree_hashes[depth+1].clone(),
                     self.update_one_val_subtree(next_new_path, val_for_new_key,
                                                 next_old_path, val_for_old_key, depth+1))
                }
            }
        };

        let root = mimc::<E>(left.clone(), right.clone(), self.hash_constants);
        self.update_db_with_key_value(&root, (None, left, right));
        root
    }

    fn get_subtree_with_one_val(&self, path: <E::Fr as PrimeField>::Repr, val: &E::Fr, depth: usize) -> E::Fr {
        if depth == self.depth {
            return val.clone()
        }

        let (l, r) = {
            let mut new_path = path.clone();
            //new_path.shl(1);
            new_path.mul2();
            if is_msb_zero!(path, self.depth as u32) {
                (self.get_subtree_with_one_val(new_path, val, depth+1),
                 self.empty_tree_hashes[depth+1].clone())
            } else {
                (self.empty_tree_hashes[depth+1].clone(),
                 self.get_subtree_with_one_val(new_path, val, depth+1))
            }
        };
        mimc::<E>(l, r, self.hash_constants)
    }

    fn update_db_with_key_value(&mut self, key: &E::Fr, val: DBVal<E>) {
        let k = field_elem_to_bytes::<E>(key);
        //println!("Adding to db={:?}", key);
        //println!("Adding to db val={:?}", &val);
        println!("Adding to db key-val {:?}={:?}", key, &val);
        if self.db.get(&k).is_some() {
            println!("Root already present: {:?}", &k);
        }
        self.db.insert(k, val);
    }

    fn get_from_db(&self, key: &E::Fr) -> &DBVal<E> {
        // TODO: Raise an error when root is not present in db
        /*println!("Getting from db={:?}", key);
        if !self.empty_tree_hashes.contains(key) {
            println!("{:?} not in empty hashes", key);
        } else {
            println!("empty hashes = {:?}", &self.empty_tree_hashes);
        }*/
        let k = field_elem_to_bytes::<E>(&key);
        self.db.get(&k).unwrap()
    }
}

mod tests {
    use super::*;
    // For randomness (during paramgen and proof generation)
    use rand::{thread_rng, Rng};
    use mimc::MIMC_ROUNDS;
    use testing_cs::TestConstraintSystem;
    use std::time::{Duration, Instant};

    /*lazy_static! {

    }*/

    #[test]
    fn test_field_elems() {
        let n = Fr::from_str("1").unwrap();
        let mut m = n.into_repr();
        let x = Fr::from_repr(FrRepr([8077060817615454808, 2216592996627606547, 624624763875441229, 6422915601121582141])).unwrap();


        for i in 0..254 {
            m.mul2();
            //println!("i={}", i);
        }
        println!("Char is {}", &Fr::char());
        println!("Num bits for m {}", &m.num_bits());
        println!("m is {}", &m);
        let mut m_1 = m.clone();
        m_1.sub_noborrow(&n.into_repr());
        println!("m_1 is {}", &m_1);
        let t = Fr::from_repr(m).unwrap();
        println!("t is {}", &t);
        println!("m is {:?}", &m);
        let t1 = reduce_field_repr_to_elem::<Bls12>(m.clone());
        println!("t1 is {:?}", &t1);
        let t11 = reduce_field_repr_to_elem::<Bls12>(t1.into_repr());
        println!("t11 is {:?}", &t11);
        m.mul2();
        let t2 = reduce_field_repr_to_elem::<Bls12>(m.clone());
        println!("t2 is {:?}", &t2);
        m.mul2();
        println!("Num bits for m {}", &m.num_bits());
        println!("m is {:?}", &m);
        let t3 = reduce_field_repr_to_elem::<Bls12>(m.clone());
        println!("t3 is {:?}", &t3);

        let mut _t4 = t2.into_repr();
        _t4.mul2();
        let t4 = reduce_field_repr_to_elem::<Bls12>(_t4);
        println!("t4 is {:?}", &t4);
    }

    #[test]
    fn test_OSMT() {
        let rng = &mut thread_rng();

        // Generate the MiMC round constants
        let constants = (0..MIMC_ROUNDS).map(|_| rng.gen()).collect::<Vec<_>>();

        let mut tree = OptmzSparseMerkleTree::<Bls12>::new(&constants);
        let (k0, v0) = (Fr::from_str("0").unwrap(), Fr::from_str("0").unwrap());
        let (k1, v1) = (Fr::from_str("1").unwrap(), Fr::from_str("1").unwrap());
        let (k2, v2) = (Fr::from_str("2").unwrap(), Fr::from_str("2").unwrap());
        let (k8, v8) = (Fr::from_str("8").unwrap(), Fr::from_str("8").unwrap());

        tree.update(k0, v0);
        println!("DB size = {:?}", &tree.db.len());
        tree.update(k1, v1);
        println!("DB size = {:?}", &tree.db.len());
        tree.update(k2, v2);
        println!("DB size = {:?}", &tree.db.len());
        tree.update(Fr::from_str("3").unwrap(), Fr::from_str("3").unwrap());
        tree.update(Fr::from_str("6").unwrap(), Fr::from_str("6").unwrap());
        tree.update(Fr::from_str("129").unwrap(), Fr::from_str("129").unwrap());
        tree.update(k8, v8);
        println!("DB size = {:?}", &tree.db.len());

        assert_eq!(v0, tree.get(k0, &mut None));
        assert_eq!(v1, tree.get(k1, &mut None));
        assert_eq!(v2, tree.get(k2, &mut None));
        assert_eq!(Fr::from_str("3").unwrap(), tree.get(Fr::from_str("3").unwrap(), &mut None));
        assert_eq!(Fr::from_str("6").unwrap(), tree.get(Fr::from_str("6").unwrap(), &mut None));
        assert_eq!(Fr::from_str("129").unwrap(), tree.get(Fr::from_str("129").unwrap(), &mut None));
        assert_eq!(v8, tree.get(k8, &mut None));

        /*for (k, v) in vec![(k0, v0), (k1, v1), (k2, v2), (k8, v8)] {
            let mut proof_vec = Vec::<DBVal<Bls12>>::new();
            let mut proof = Some(proof_vec);
            assert_eq!(v, tree.get(k, &mut proof));

            proof_vec = proof.unwrap();
            println!("proof length for {} = {:?}", &k, &proof_vec.len());
            assert!(tree.verify_proof(k, v, &proof_vec, &tree.root));
        }*/


        // Some random key values
        let kvs: Vec<(Fr, Fr)> = (0..10).map(|_| (rng.gen(), rng.gen())).collect();
        for i in 0..kvs.len() {
            println!("Setting {:?}={:?}", &kvs[i].0, &kvs[i].1);
            tree.update(kvs[i].0, kvs[i].1);
        }
        println!("DB size = {:?}", &tree.db.len());

        for i in 0..kvs.len() {
            println!("Getting {:?}", &kvs[i].0);
            assert_eq!(kvs[i].1, tree.get(kvs[i].0, &mut None));
        }
    }
}