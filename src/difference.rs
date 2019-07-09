/// Check in how many elements are 2 ordered sets different

extern crate bellman;
extern crate pairing;
extern crate rand;

// For randomness (during paramgen and proof generation)
use rand::{thread_rng, Rng, Rand};

// Bring in some tools for using pairing-friendly curves
use pairing::{
    Engine,
    Field,
    PrimeField,
    PrimeFieldRepr
};

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use pairing::bls12_381::{
    Bls12, Fr, FrRepr
};

// We'll use these interfaces to construct our circuit.
use bellman::{Variable, Circuit, ConstraintSystem, SynthesisError, LinearCombination};

// We're going to use the Groth16 proving system.
use bellman::groth16::{
    Proof,
    generate_random_parameters,
    prepare_verifying_key,
    create_random_proof,
    verify_proof,
};
use std::collections::HashSet;
use testing_cs::TestConstraintSystem;

pub struct SetDifference<E: Engine> {
    pub original: Vec<Option<E::Fr>>,
    pub new: Vec<E::Fr>,
    pub count_modified: u64
}

impl <E: Engine> Circuit<E> for SetDifference<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError> {
        assert_eq!(self.original.len(), self.new.len());

        let mut sum_val: Option<E::Fr> = None;
        let mut sum = LinearCombination::<E>::zero();

        for i in 0..self.original.len() {
            let mut cs = &mut cs.namespace(|| format!("at index: {}", i));
            let x_val = self.original[i];
            let x = cs.alloc(|| format!("x[{}]", i), || {
                x_val.ok_or(SynthesisError::AssignmentMissing)
            })?;

            // diff[i] = x[i] - new[i]
            let tmp = x_val.clone();
            let diff_val = tmp.map(| mut t | {
                t.sub_assign(&self.new[i]);
                t
            });

            let mut diff = cs.alloc(|| format!("diff[{}]", i), || {
                diff_val.ok_or(SynthesisError::AssignmentMissing)
            })?;

            // x - diff[i] = new[i]
            cs.enforce(
                || "x - diff[i] = new[i]",
                |lc| lc + x - diff,
                |lc| lc + CS::one(),
                |lc| lc + (self.new[i], CS::one())
            );

            // y = diff * (diff)^-1 = 1 or 0
            let mut diff_inv_val = diff_val.map(| t| {
                t.inverse().map_or(E::Fr::zero(), | u | u)
            });
            let mut diff_inv = cs.alloc(|| format!("diff_inv[{}]", i), || {
                diff_inv_val.ok_or(SynthesisError::AssignmentMissing)
            })?;
            let mut y_val = diff_inv_val.map(| t| {
                if t == E::Fr::zero() {
                    E::Fr::zero()
                } else {
                    E::Fr::one()
                }
            });
            let mut y = cs.alloc(|| format!("y[{}]", i), || {
                y_val.ok_or(SynthesisError::AssignmentMissing)
            })?;

            cs.enforce(
                || "diff * (diff)^-1 = y",
                |lc| lc + diff,
                |lc| lc + diff_inv,
                |lc| lc + y
            );

            cs.enforce(
                || "diff * (1-y) = 0",
                |lc| lc + diff,
                |lc| lc + (E::Fr::one(), CS::one()) - y,
                |lc| lc
            );

            sum_val = y_val.map(|t| {
                if sum_val.is_none() {
                    t
                } else {
                    let mut u = sum_val.unwrap();
                    u.add_assign(&t);
                    u
                }
            });
            sum = sum + y;
        }

        let out = cs.alloc_input(|| "sum", || {
            Ok(sum_val.unwrap())
        })?;
        cs.enforce(
            || "out = sum",
            |lc| lc + &sum,
            |lc| lc + CS::one(),
            |lc| lc + out
        );

        Ok(())
    }
}

// For benchmarking
use std::time::{Duration, Instant};

#[test]
fn test_difference() {
    let rng = &mut thread_rng();

    let data_size = 15000;
    let count_modified = 50u64;
    let original_data = (0..data_size).map(|_| rng.gen()).collect::<Vec<<Bls12 as Engine>::Fr>>();
    let mut new_data = original_data.clone();
    // For testing only. Generating random indices to modify
    let mut modify_indices = HashSet::new();
    for _ in 0..count_modified {
        modify_indices.insert(rng.gen_range(0, data_size) as usize);
    }
    if modify_indices.len() != (count_modified as usize) {
        panic!("Could not generate {} random numbers but only {}", count_modified, modify_indices.len());
    }
    for i in modify_indices {
        new_data[i] = rng.gen();
    }

    /*{
        let c = SetDifference::<Bls12> {
            original: original_data.iter().map(|t| Some(*t)).collect::<Vec<Option<<Bls12 as Engine>::Fr>>>(),
            new: new_data.clone(),
            count_modified
        };
        let mut cs = TestConstraintSystem::<Bls12>::new();
        c.synthesize(&mut cs).unwrap();
        let satisfied = cs.is_satisfied();
        //println!("{}", cs.which_is_unsatisfied().unwrap());
        assert!(satisfied);
        println!("{}", cs.find_unconstrained());
    }*/

    let params = {
        let c = SetDifference::<Bls12> {
            original: (0..data_size).map(|_| None).collect::<Vec<Option<<Bls12 as Engine>::Fr>>>(),
            new: new_data.clone(),
            count_modified
        };

        generate_random_parameters(c, rng).unwrap()
    };

    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    let mut proof_bytes = vec![];
    let start = Instant::now();
    let c = SetDifference::<Bls12> {
        original: original_data.iter().map(|t| Some(*t)).collect::<Vec<Option<<Bls12 as Engine>::Fr>>>(),
        new: new_data.clone(),
        count_modified
    };

    let proof = create_random_proof(c, &params, rng).unwrap();
    let end = start.elapsed();
    proof.write(&mut proof_bytes).unwrap();
    println!("Proof gen time with data size = {} and count_modified = {} is {:?}. Proof size is {} bytes", data_size, count_modified, end, proof_bytes.len());

    let start = Instant::now();
    assert!(verify_proof(
        &pvk,
        &proof,
        &[Fr::from_repr(FrRepr::from(count_modified)).unwrap()]
    ).unwrap());
    println!("Verification time is {:?}", start.elapsed());
}