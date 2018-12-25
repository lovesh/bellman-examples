extern crate bellman;
extern crate pairing;
extern crate rand;

// For randomness (during paramgen and proof generation)
use rand::{thread_rng, Rng};

// Bring in some tools for using pairing-friendly curves
use pairing::{
    Engine,
    Field
};

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use pairing::bls12_381::{
    Bls12
};

// We'll use these interfaces to construct our circuit.
use bellman::{
    Variable,
    Circuit,
    ConstraintSystem,
    SynthesisError
};

// We're going to use the Groth16 proving system.
use bellman::groth16::{
    Proof,
    generate_random_parameters,
    prepare_verifying_key,
    create_random_proof,
    verify_proof,
};

struct SharkMiMCParams<E: Engine> {
    pub num_branches: usize,
    pub middle_rounds: usize,
    pub total_rounds: usize,
//    pub round_constants: Vec<E::Fr>,
    pub round_keys: Vec<E::Fr>,
    // TODO: Add matrix_1
    pub matrix_2: Vec<Vec<E::Fr>>
}

impl<E: Engine> SharkMiMCParams<E> {
    fn new(num_branches: usize, middle_rounds: usize) -> SharkMiMCParams<E> {
        let total_rounds = 6 + middle_rounds;
//        let round_constants = Self::gen_round_constants(num_branches, total_rounds);
        let round_keys = Self::gen_round_keys(num_branches, total_rounds);
        let matrix_2 = Self::gen_matrix_2(num_branches);
        SharkMiMCParams {
            num_branches,
            middle_rounds,
            total_rounds,
//            round_constants,
            round_keys,
            matrix_2
        }
    }

    /*fn gen_round_constants(num_branches: usize, total_rounds: usize) -> Vec<E::Fr> {
        let cap = total_rounds * num_branches;
        let mut consts: Vec<E::Fr> = Vec::with_capacity(cap);
        for i in 0..cap {
            consts[i] = E::Fr::one();
        }
        consts
    }*/

    fn gen_round_keys(num_branches: usize, total_rounds: usize) -> Vec<E::Fr> {
        let cap = (total_rounds + 1) * num_branches;
        vec![E::Fr::one(); cap]
    }

    fn gen_matrix_2(num_branches: usize) -> Vec<Vec<E::Fr>> {
        vec![vec![E::Fr::one(); num_branches]; num_branches]
    }
}

pub trait Sbox<E: Engine> {
    fn apply(elem: &E::Fr) -> E::Fr;
}

// Circuit for proving knowledge of the preimage of a SharkMiMC hash.
struct SharkMiMC<'a, E: Engine> {
    pub input: Vec<Option<E::Fr>>,
    params: &'a SharkMiMCParams<E>
}

impl<'a, E: Engine> SharkMiMC<'a, E> {
    fn applySbox(elem: &E::Fr) -> E::Fr {
        elem.clone()
    }
}

impl<'a, E: Engine> Circuit<E> for SharkMiMC<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        let num_branches = self.params.num_branches;
        assert_eq!(self.input.len(), num_branches);
        let mut input_vals: Vec<Option<E::Fr>> = vec![None; num_branches];
        let mut input_vars: Vec<Variable> = vec![CS::one(); num_branches];

        for i in 0..num_branches {
            input_vals[i] = self.input[i];
            input_vars[i] = cs.alloc(|| format!("input {}", i), || {
                input_vals[i].ok_or(SynthesisError::AssignmentMissing)
            })?;
        }

        let mut round_keys_offset = 0;

        // ------------ First 3 rounds begin --------------------

        for k in 0..3 {
            let mut sbox_out_vals: Vec<Option<E::Fr>> = vec![None; num_branches];

            // Substitution (S-box) layer
            for i in 0..num_branches {
                let cs = &mut cs.namespace(|| format!("sbox: round-branch: {}:{}", k, i));

                let round_key = self.params.round_keys[round_keys_offset];

                let mut tmp = input_vals[i].clone();
                tmp = tmp.map(| mut t | {
                    t.add_assign(&round_key);
                    t
                });

                let mut square_val = tmp.clone().map(|mut t| {
                    t.square();
                    t
                });
                let mut square = cs.alloc(|| "square", || {
                    square_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || "square constraint",
                    |lc| lc + input_vars[i] + (round_key, CS::one()),
                    |lc| lc + input_vars[i] + (round_key, CS::one()),
                    |lc| lc + square
                );

                let mut cube_val = square_val.map(|mut t| {
                    t.mul_assign(&tmp.unwrap());
                    t
                });
                let mut cube = cs.alloc(|| "cube", || {
                    cube_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || "cube constraint",
                    |lc| lc + square,
                    |lc| lc + input_vars[i] + (round_key, CS::one()),
                    |lc| lc + cube
                );

                sbox_out_vals[i] = cube_val;

                round_keys_offset += 1;
            }

            // Linear layer

            let mut next_input_vals: Vec<Option<E::Fr>> = vec![Some(E::Fr::zero()); num_branches];
            let mut next_input_vars: Vec<Variable> = vec![CS::one(); num_branches];

            for j in 0..num_branches {
                for i in 0..num_branches {
                    let tmp = sbox_out_vals[j].clone().map( | mut t | {
                        t.mul_assign(&self.params.matrix_2[i][j]);
                        t
                    });
                    next_input_vals[i] = next_input_vals[i].map( | mut t | {
//                        t.add_assign(&tmp.unwrap());
                        tmp.map(| t_ | t.add_assign(&t_));
                        t
                    });
                }
            }

            for i in 0..num_branches {
                let cs = &mut cs.namespace(|| format!("linear: round-branch: {}:{}", k, i));
                input_vals[i] = next_input_vals[i];
                input_vars[i] = cs.alloc(|| "linear", || {
                    next_input_vals[i].ok_or(SynthesisError::AssignmentMissing)
                })?;
            }
        }

        // ------------ First 3 rounds end --------------------

        // ------------ Middle rounds begin --------------------

        for k in 3..(3+self.params.middle_rounds) {
            let mut sbox_out_vals: Vec<Option<E::Fr>> = vec![None; num_branches];

            // Substitution (S-box) layer
            for i in 0..num_branches {
                let cs = &mut cs.namespace(|| format!("sbox: round-branch: {}:{}", k, i));

                let round_key = self.params.round_keys[round_keys_offset];

                let mut tmp = input_vals[i].clone();
                tmp = tmp.map(|mut t| {
                    t.add_assign(&round_key);
                    t
                });

                if i == 0 {
                    let mut square_val = tmp.clone().map(|mut t| {
                        t.square();
                        t
                    });
                    let mut square = cs.alloc(|| "square", || {
                        square_val.ok_or(SynthesisError::AssignmentMissing)
                    })?;
                    cs.enforce(
                        || "square constraint",
                        |lc| lc + input_vars[i] + (round_key, CS::one()),
                        |lc| lc + input_vars[i] + (round_key, CS::one()),
                        |lc| lc + square
                    );

                    let mut cube_val = square_val.map(|mut t| {
                        t.mul_assign(&tmp.unwrap());
                        t
                    });
                    let mut cube = cs.alloc(|| "cube", || {
                        cube_val.ok_or(SynthesisError::AssignmentMissing)
                    })?;
                    cs.enforce(
                        || "cube constraint",
                        |lc| lc + square,
                        |lc| lc + input_vars[i] + (round_key, CS::one()),
                        |lc| lc + cube
                    );

                    sbox_out_vals[i] = cube_val;
                } else {
                    sbox_out_vals[i] = tmp;
                }

                round_keys_offset += 1;
            }

            // Linear layer

            let mut next_input_vals: Vec<Option<E::Fr>> = vec![Some(E::Fr::zero()); num_branches];
            let mut next_input_vars: Vec<Variable> = vec![CS::one(); num_branches];

            for j in 0..num_branches {
                for i in 0..num_branches {
                    let tmp = sbox_out_vals[j].clone().map( | mut t | {
                        t.mul_assign(&self.params.matrix_2[i][j]);
                        t
                    });
                    next_input_vals[i] = next_input_vals[i].map( | mut t | {
//                        t.add_assign(&tmp.unwrap());
                        tmp.map(| t_ | t.add_assign(&t_));
                        t
                    });
                }
            }

            for i in 0..num_branches {
                let cs = &mut cs.namespace(|| format!("linear: round-branch: {}:{}", k, i));
                input_vals[i] = next_input_vals[i];
                input_vars[i] = cs.alloc(|| "linear", || {
                    next_input_vals[i].ok_or(SynthesisError::AssignmentMissing)
                })?;
            }
        }

        // ------------ Middle rounds end --------------------

        // ------------ Last 2+1 rounds begin --------------------

        // 2 rounds
        for k in 3+self.params.middle_rounds..(3+self.params.middle_rounds+2) {
            let mut sbox_out_vals: Vec<Option<E::Fr>> = vec![None; num_branches];

            // Substitution (S-box) layer
            for i in 0..num_branches {
                let cs = &mut cs.namespace(|| format!("sbox: round-branch: {}:{}", k, i));

                let round_key = self.params.round_keys[round_keys_offset];

                let mut tmp = input_vals[i].clone();
                tmp = tmp.map(| mut t | {
                    t.add_assign(&round_key);
                    t
                });

                let mut square_val = tmp.clone().map(|mut t| {
                    t.square();
                    t
                });
                let mut square = cs.alloc(|| "square", || {
                    square_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || "square constraint",
                    |lc| lc + input_vars[i] + (round_key, CS::one()),
                    |lc| lc + input_vars[i] + (round_key, CS::one()),
                    |lc| lc + square
                );

                let mut cube_val = square_val.map(|mut t| {
                    t.mul_assign(&tmp.unwrap());
                    t
                });
                let mut cube = cs.alloc(|| "cube", || {
                    cube_val.ok_or(SynthesisError::AssignmentMissing)
                })?;
                cs.enforce(
                    || "cube constraint",
                    |lc| lc + square,
                    |lc| lc + input_vars[i] + (round_key, CS::one()),
                    |lc| lc + cube
                );

                sbox_out_vals[i] = cube_val;

                round_keys_offset += 1;
            }

            // Linear layer

            let mut next_input_vals: Vec<Option<E::Fr>> = vec![Some(E::Fr::zero()); num_branches];
            let mut next_input_vars: Vec<Variable> = vec![CS::one(); num_branches];

            for j in 0..num_branches {
                for i in 0..num_branches {
                    let tmp = sbox_out_vals[j].clone().map( | mut t | {
                        t.mul_assign(&self.params.matrix_2[i][j]);
                        t
                    });
                    next_input_vals[i] = next_input_vals[i].map( | mut t | {
//                        t.add_assign(&tmp.unwrap());
                        tmp.map(| t_ | t.add_assign(&t_));
                        t
                    });
                }
            }

            for i in 0..num_branches {
                let cs = &mut cs.namespace(|| format!("linear: round-branch: {}:{}", k, i));
                input_vals[i] = next_input_vals[i];
                input_vars[i] = cs.alloc(|| "linear", || {
                    next_input_vals[i].ok_or(SynthesisError::AssignmentMissing)
                })?;
            }
        }

        // Last round
        let mut output_vals: Vec<Option<E::Fr>> = vec![None; num_branches];
        let mut output_vars: Vec<Variable> = vec![CS::one(); num_branches];

        // Substitution (S-box) layer
        for i in 0..num_branches {
            let cs = &mut cs.namespace(|| format!("sbox: round-branch: {}:{}", self.params.total_rounds-1, i));

            let round_key = self.params.round_keys[round_keys_offset];

            let mut tmp = input_vals[i].clone();
            tmp = tmp.map(|mut t| {
                t.add_assign(&round_key);
                t
            });

            let mut square_val = tmp.clone().map(|mut t| {
                t.square();
                t
            });
            let mut square = cs.alloc(|| "square", || {
                square_val.ok_or(SynthesisError::AssignmentMissing)
            })?;
            cs.enforce(
                || "square constraint",
                |lc| lc + input_vars[i] + (round_key, CS::one()),
                |lc| lc + input_vars[i] + (round_key, CS::one()),
                |lc| lc + square
            );

            let mut cube_val = square_val.map(|mut t| {
                t.mul_assign(&tmp.unwrap());
                t
            });
            let mut cube = cs.alloc(|| "cube", || {
                cube_val.ok_or(SynthesisError::AssignmentMissing)
            })?;
            cs.enforce(
                || "cube constraint",
                |lc| lc + square,
                |lc| lc + input_vars[i] + (round_key, CS::one()),
                |lc| lc + cube
            );

            round_keys_offset += 1;

            let new_round_key = self.params.round_keys[round_keys_offset];

            output_vals[i] = cube_val.clone().map(|mut t| {
                t.add_assign(&new_round_key);
                t
            });
            output_vars[i] = cs.alloc_input(|| "image", || {
                output_vals[i].ok_or(SynthesisError::AssignmentMissing)
            })?;

            round_keys_offset += 1;
        }

        // ------------ Last 2+1 rounds end --------------------
        println!("synthesis done");
        Ok(())
    }
}


#[test]
fn test_SharkMiMC() {
    use pairing::bls12_381::{Bls12, Fr};
    use pairing::PrimeField;

    let rng = &mut thread_rng();

    let num_branches = 4;
    let middle_rounds = 38;
    let s_params = SharkMiMCParams::<Bls12>::new(num_branches, middle_rounds);

    let params = {
        let c = SharkMiMC::<Bls12> {
            input: vec![None; num_branches],
            params: &s_params
        };

        let x = generate_random_parameters(c, rng);
//        assert!(x.is_ok());
        x.unwrap()
    };

    let pvk = prepare_verifying_key(&params.vk);

    // Input and output generated from python implementation (sharkmimc.py)
    let circuit = SharkMiMC::<Bls12> {
        input: vec![Fr::from_str("1"), Fr::from_str("2"),
                    Fr::from_str("3"), Fr::from_str("4")],
        params: &s_params
    };

    let proof = create_random_proof(circuit, &params, rng).unwrap();

    let image: Vec<Fr> = vec![
        Fr::from_str("67467530373502753752924860171790442231048313900282686261343205429092560401206073946299845046733797859154502122857").unwrap(),
        Fr::from_str("762128189513891820312535132127527487877314215797849354999559120718946811992864139948058805671503493721069958513709").unwrap(),
        Fr::from_str("994431830302227569593741217325868538797115453206571284864030749113203138226634657912641665782834572234751139919329").unwrap(),
        Fr::from_str("3903970509687998100224236216689220321329382292912982132882363870929206722842112920590656441858573865007030514464078").unwrap()
    ];
    assert!(verify_proof(&pvk, &proof, &image).unwrap());
}