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

fn apply_cube_sbox<E: Engine>(elem: &E::Fr) -> E::Fr
{
    let mut res = E::Fr::one();
    res.mul_assign(elem);
    res.mul_assign(elem);
    res.mul_assign(elem);
    res
}

fn apply_inverse_sbox<E: Engine>(elem: &E::Fr) -> E::Fr
{
    elem.inverse().map_or(E::Fr::zero(), | t | t)
}

/*pub trait HasSbox<E: Engine> {
    fn apply_sbox(elem: &E::Fr) -> E::Fr;
}

pub trait HasCubeSbox<E: Engine>: HasSbox<E> {
    fn apply_sbox(elem: &E::Fr) -> E::Fr {
        apply_cube_sbox::<E>(elem)
    }
}

pub trait HasInverseSbox<E: Engine>: HasSbox<E> {
    fn apply_sbox(elem: &E::Fr) -> E::Fr {
        apply_inverse_sbox::<E>(elem)
    }
}*/

fn SharkMiMC<E: Engine>(
    input: Vec<E::Fr>,
    params: &SharkMiMCParams<E>,
    apply_sbox: &Fn(&E::Fr) -> E::Fr
) -> Vec<E::Fr>
{
    assert_eq!(input.len(), params.num_branches);

    let mut value_branch = input;
    let mut value_branch_temp = vec![E::Fr::zero(); params.num_branches];

    let mut round_keys_offset = 0;

    // 3 full Sbox rounds
    for _ in 0..3 {
        // Sbox layer
        for i in 0..params.num_branches {
            value_branch[i].add_assign(&params.round_keys[round_keys_offset]);
            value_branch[i] = apply_sbox(&value_branch[i]);
            round_keys_offset += 1;
        }

        // linear layer
        for j in 0..params.num_branches {
            for i in 0..params.num_branches {
                let mut temp = value_branch[j].clone();
                temp.mul_assign(&params.matrix_2[i][j]);
                value_branch_temp[i].add_assign(&temp);
            }
        }

        // Output of this round becomes input to next round
        for i in 0..params.num_branches {
            value_branch[i] = value_branch_temp[i];
            value_branch_temp[i] = E::Fr::zero();
        }
    }

    // middle partial Sbox rounds
    for _ in 3..(3+params.middle_rounds) {
        for i in 0..params.num_branches {
            value_branch[i].add_assign(&params.round_keys[round_keys_offset]);
            round_keys_offset += 1;
        }

        // partial Sbox layer
        value_branch[0] = apply_sbox(&value_branch[0]);

        // linear layer
        for j in 0..params.num_branches {
            for i in 0..params.num_branches {
                let mut temp = value_branch[j].clone();
                temp.mul_assign(&params.matrix_2[i][j]);
                value_branch_temp[i].add_assign(&temp);
            }
        }

        // Output of this round becomes input to next round
        for i in 0..params.num_branches {
            value_branch[i] = value_branch_temp[i];
            value_branch_temp[i] = E::Fr::zero();
        }
    }

    // last full Sbox rounds
    for _ in 3+params.middle_rounds..(3+params.middle_rounds+2) {
        // Sbox layer
        for i in 0..params.num_branches {
            value_branch[i].add_assign(&params.round_keys[round_keys_offset]);
            value_branch[i] = apply_sbox(&value_branch[i]);
            round_keys_offset += 1;
        }

        // linear layer
        for j in 0..params.num_branches {
            for i in 0..params.num_branches {
                let mut temp = value_branch[j].clone();
                temp.mul_assign(&params.matrix_2[i][j]);
                value_branch_temp[i].add_assign(&temp);
            }
        }

        // Output of this round becomes input to next round
        for i in 0..params.num_branches {
            value_branch[i] = value_branch_temp[i];
            value_branch_temp[i] = E::Fr::zero();
        }
    }

    for i in 0..params.num_branches {
        value_branch[i].add_assign(&params.round_keys[round_keys_offset]);
        value_branch[i] = apply_sbox(&value_branch[i]);
        round_keys_offset += 1;

        value_branch[i].add_assign(&params.round_keys[round_keys_offset]);
        round_keys_offset += 1;
    }

    value_branch
}

enum SboxType {
    Cube,
    Inverse
}

// Circuit for proving knowledge of the preimage of a SharkMiMC hash.
struct SharkMiMCCircuit<'a, E: Engine> {
    pub input: Vec<Option<E::Fr>>,
    params: &'a SharkMiMCParams<E>,
    sbox_type: SboxType
}

/*impl<'a, E: Engine> SharkMiMCCircuit<'a, E> {
    fn applySbox(elem: &E::Fr) -> E::Fr {
        elem.clone()
    }
}*/

impl<'a, E: Engine> Circuit<E> for SharkMiMCCircuit<'a, E> {
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

        fn synthesize_sbox<E: Engine, CS: ConstraintSystem<E>>(
            cs: &mut CS,
            input_val: &Option<E::Fr>,
            input_var: Variable,
            round_key: E::Fr,
            sbox_type: &SboxType
        ) -> Result<Option<E::Fr>, SynthesisError> {
            match sbox_type {
                SboxType::Cube => synthesize_cube_sbox::<E, CS>(cs, input_val, input_var, round_key),
                SboxType::Inverse => synthesize_inverse_sbox::<E, CS>(cs, input_val, input_var, round_key)
            }
        }

        fn synthesize_cube_sbox<E: Engine, CS: ConstraintSystem<E>>(
            cs: &mut CS,
            input_val: &Option<E::Fr>,
            input_var: Variable,
            round_key: E::Fr
        ) -> Result<Option<E::Fr>, SynthesisError> {
            let mut tmp = input_val.clone();
            tmp = tmp.map(| mut t | {
                t.add_assign(&round_key);
                t
            });

            let mut square_val = tmp.map(|mut t| {
                t.square();
                t
            });
            let mut square = cs.alloc(|| "square", || {
                square_val.ok_or(SynthesisError::AssignmentMissing)
            })?;
            cs.enforce(
                || "square constraint",
                |lc| lc + input_var + (round_key, CS::one()),
                |lc| lc + input_var + (round_key, CS::one()),
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
                |lc| lc + input_var + (round_key, CS::one()),
                |lc| lc + cube
            );

            Ok(cube_val)
        }

        fn synthesize_inverse_sbox<E: Engine, CS: ConstraintSystem<E>>(
            cs: &mut CS,
            input_val: &Option<E::Fr>,
            input_var: Variable,
            round_key: E::Fr
        ) -> Result<Option<E::Fr>, SynthesisError> {
            let mut tmp = input_val.map(|mut t| {
                t.add_assign(&round_key);
                t
            });;

            let mut inverse_val = tmp.map(| t| {
                apply_inverse_sbox::<E>(&t)
            });
            let mut inverse = cs.alloc(|| "inverse", || {
                inverse_val.ok_or(SynthesisError::AssignmentMissing)
            })?;
            cs.enforce(
                || "inverse constraint",
                |lc| lc + input_var + (round_key, CS::one()),
                |lc| lc + inverse,
                |lc| lc + CS::one()
            );

            Ok(inverse_val)
        }

        fn apply_linear_layer<E: Engine>(
            num_branches: usize,
            sbox_out_vals: &Vec<Option<E::Fr>>,
            next_input_vals: &mut Vec<Option<E::Fr>>,
            matrix_2: &Vec<Vec<E::Fr>>,
        ) {
            for j in 0..num_branches {
                for i in 0..num_branches {
                    let tmp = sbox_out_vals[j].clone().map( | mut t | {
                        t.mul_assign(&matrix_2[i][j]);
                        t
                    });
                    next_input_vals[i] = next_input_vals[i].map( | mut t | {
                        tmp.map(| t_ | t.add_assign(&t_));
                        t
                    });
                }
            }
        }

        // ------------ First 3 rounds begin --------------------

        for k in 0..3 {
            let mut sbox_out_vals: Vec<Option<E::Fr>> = vec![None; num_branches];

            // Substitution (S-box) layer
            for i in 0..num_branches {
                let mut cs = &mut cs.namespace(|| format!("sbox: round-branch: {}:{}", k, i));

                let round_key = self.params.round_keys[round_keys_offset];

                sbox_out_vals[i] = synthesize_sbox(&mut cs, &input_vals[i].clone(),
                                                   input_vars[i].clone(), round_key.clone(), &self.sbox_type)?;

                round_keys_offset += 1;
            }

            // Linear layer

            let mut next_input_vals: Vec<Option<E::Fr>> = vec![Some(E::Fr::zero()); num_branches];

            apply_linear_layer::<E>(num_branches, &sbox_out_vals, &mut next_input_vals, &self.params.matrix_2);

            for i in 0..num_branches {
                input_vals[i] = next_input_vals[i];

                // Only first branch of output of the last round is used for constraint for middle rounds
                if k < 2 || i == 0 {
                    let cs = &mut cs.namespace(|| format!("linear: round-branch: {}:{}", k, i));
                    input_vars[i] = cs.alloc(|| "linear", || {
                        next_input_vals[i].ok_or(SynthesisError::AssignmentMissing)
                    })?;
                }
            }
        }

        // ------------ First 3 rounds end --------------------

        // ------------ Middle rounds begin --------------------

        for k in 3..(3+self.params.middle_rounds) {
            let mut sbox_out_vals: Vec<Option<E::Fr>> = vec![None; num_branches];

            // Substitution (S-box) layer
            for i in 0..num_branches {
                let mut cs = &mut cs.namespace(|| format!("sbox: round-branch: {}:{}", k, i));

                let round_key = self.params.round_keys[round_keys_offset];

                if i == 0 {
                    sbox_out_vals[i] = synthesize_sbox(&mut cs, &input_vals[i].clone(),
                                                       input_vars[i].clone(), round_key.clone(), &self.sbox_type)?;
                } else {
                    let mut tmp = input_vals[i].clone();
                    tmp = tmp.map(|mut t| {
                        t.add_assign(&round_key);
                        t
                    });
                    sbox_out_vals[i] = tmp;
                }

                round_keys_offset += 1;
            }

            // Linear layer

            let mut next_input_vals: Vec<Option<E::Fr>> = vec![Some(E::Fr::zero()); num_branches];

            apply_linear_layer::<E>(num_branches, &sbox_out_vals, &mut next_input_vals, &self.params.matrix_2);

            for i in 0..num_branches {
                input_vals[i] = next_input_vals[i];

                // For middle rounds, only first branch is involved in constraints. Allocate variables for
                // all branches only for last middle round such that it can be used for input for next round.
                if i == 0 || k == 3+self.params.middle_rounds-1 {
                    let cs = &mut cs.namespace(|| format!("linear: round-branch: {}:{}", k, i));
                    input_vars[i] = cs.alloc(|| "linear", || {
                        next_input_vals[i].ok_or(SynthesisError::AssignmentMissing)
                    })?;
                }
            }
        }

        // ------------ Middle rounds end --------------------

        // ------------ Last 2+1 rounds begin --------------------

        // 2 rounds
        for k in 3+self.params.middle_rounds..(3+self.params.middle_rounds+2) {
            let mut sbox_out_vals: Vec<Option<E::Fr>> = vec![None; num_branches];

            // Substitution (S-box) layer
            for i in 0..num_branches {
                let mut cs = &mut cs.namespace(|| format!("sbox: round-branch: {}:{}", k, i));

                let round_key = self.params.round_keys[round_keys_offset];

                sbox_out_vals[i] = synthesize_sbox(&mut cs, &input_vals[i].clone(),
                                                   input_vars[i].clone(), round_key.clone(), &self.sbox_type)?;

                round_keys_offset += 1;
            }

            // Linear layer

            let mut next_input_vals: Vec<Option<E::Fr>> = vec![Some(E::Fr::zero()); num_branches];

            apply_linear_layer::<E>(num_branches, &sbox_out_vals, &mut next_input_vals, &self.params.matrix_2);

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
            let mut cs = &mut cs.namespace(|| format!("sbox: round-branch: {}:{}", self.params.total_rounds-1, i));

            let round_key = self.params.round_keys[round_keys_offset];

            let cube_val = synthesize_sbox(&mut cs, &input_vals[i].clone(),
                                               input_vars[i].clone(), round_key.clone(), &self.sbox_type)?;

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
fn SharkMiMC_with_TestConstraintSystem() {
    use pairing::bls12_381::{Bls12, Fr, FrRepr};
    use pairing::{PrimeField, PrimeFieldRepr};
    use testing_cs::TestConstraintSystem;

    let num_branches = 4;
    let middle_rounds = 38;
    let s_params = SharkMiMCParams::<Bls12>::new(num_branches, middle_rounds);
    let total_rounds = s_params.total_rounds;

    let input = vec![Fr::from_str("1"), Fr::from_str("2"),
                     Fr::from_str("3"), Fr::from_str("4")];
    println!("Input >>>>>>>>>");
    println!("{:?}", input[0]);
    println!("{:?}", input[1]);
    println!("{:?}", input[2]);
    println!("{:?}", input[3]);

    let mut input1 = vec![Fr::zero(); num_branches];
    for i in 0..num_branches {
        input1[i] = input[i].clone().unwrap();
    }
    let input2 = input1.clone();
    let image_from_func_cube = SharkMiMC::<Bls12>(input1, &s_params, &apply_cube_sbox::<Bls12>);
    let image_from_func_inverse = SharkMiMC::<Bls12>(input2, &s_params, &apply_inverse_sbox::<Bls12>);

    println!("Output with Sbox as cube (from function) >>>>>>>>>");
    for i in 0..num_branches {
        println!("{}", image_from_func_cube[i]);
    }

    println!("Output with Sbox as inverse (from function) >>>>>>>>>");
    for i in 0..num_branches {
        println!("{}", image_from_func_inverse[i]);
    }

    {
        println!("Checking with Sbox as cube");
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let c = SharkMiMCCircuit::<Bls12> {
            input: input.clone(),
            params: &s_params,
            sbox_type: SboxType::Cube
        };

        c.synthesize(&mut cs).unwrap();
        let satisfied = cs.is_satisfied();
        assert!(satisfied);
        println!("Is satisfied {}", satisfied);
        println!("Num constraints {}", &cs.num_constraints());
//    println!("{}", &cs.pretty_print());
        let mut image_from_circuit = vec![Fr::zero(); num_branches];

        for i in 0..num_branches {
            image_from_circuit[i] = cs.get(&format!("sbox: round-branch: {}:{}/image", total_rounds-1, i));
            println!("Output {}:{}", i, &image_from_circuit[i]);
        }

        assert_eq!(image_from_func_cube, image_from_circuit);
//    println!("{}", cs.find_unconstrained());
        println!("Successful with Sbox as cube");
    }

    {
        println!("Checking with Sbox as inverse");
        let mut cs = TestConstraintSystem::<Bls12>::new();

        let c = SharkMiMCCircuit::<Bls12> {
            input,
            params: &s_params,
            sbox_type: SboxType::Inverse
        };

        c.synthesize(&mut cs).unwrap();
        let satisfied = cs.is_satisfied();
        assert!(satisfied);
        println!("Is satisfied {}", satisfied);
        println!("Num constraints {}", &cs.num_constraints());

        let mut image_from_circuit = vec![Fr::zero(); num_branches];

        for i in 0..num_branches {
            image_from_circuit[i] = cs.get(&format!("sbox: round-branch: {}:{}/image", total_rounds-1, i));
            println!("Output {}:{}", i, &image_from_circuit[i]);
        }

        assert_eq!(image_from_func_inverse, image_from_circuit);

        println!("Successful with Sbox as inverse");
    }
}

#[test]
fn SharkMiMC_basic() {
    use pairing::bls12_381::{Bls12, Fr};
    use pairing::PrimeField;

    let rng = &mut thread_rng();

    let num_branches = 4;
    let middle_rounds = 38;
    let s_params = SharkMiMCParams::<Bls12>::new(num_branches, middle_rounds);

    {
        let params = {
            let c = SharkMiMCCircuit::<Bls12> {
                input: vec![None; num_branches],
                params: &s_params,
                sbox_type: SboxType::Cube
            };

            let x = generate_random_parameters(c, rng);
//        assert!(x.is_ok());
            x.unwrap()
        };

        let pvk = prepare_verifying_key(&params.vk);

        // Input and output generated from python implementation (sharkmimc.py)
        let circuit = SharkMiMCCircuit::<Bls12> {
            input: vec![Fr::from_str("1"), Fr::from_str("2"),
                        Fr::from_str("3"), Fr::from_str("4")],
            params: &s_params,
            sbox_type: SboxType::Cube
        };

        let proof = create_random_proof(circuit, &params, rng).unwrap();

        let image: Vec<Fr> = vec![
            Fr::from_str("7662334185782834131368228856096374400481443875468189238128380422619483242028").unwrap(),
            Fr::from_str("7662334185782834131368228856096374400481443875468189238128380422619483242028").unwrap(),
            Fr::from_str("7662334185782834131368228856096374400481443875468189238128380422619483242028").unwrap(),
            Fr::from_str("7662334185782834131368228856096374400481443875468189238128380422619483242028").unwrap()
        ];
        assert!(verify_proof(&pvk, &proof, &image).unwrap());
    }

    {
        let params = {
            let c = SharkMiMCCircuit::<Bls12> {
                input: vec![None; num_branches],
                params: &s_params,
                sbox_type: SboxType::Inverse
            };

            let x = generate_random_parameters(c, rng);
//        assert!(x.is_ok());
            x.unwrap()
        };

        let pvk = prepare_verifying_key(&params.vk);

        // Input and output generated from python implementation (sharkmimc.py)
        let circuit = SharkMiMCCircuit::<Bls12> {
            input: vec![Fr::from_str("1"), Fr::from_str("2"),
                        Fr::from_str("3"), Fr::from_str("4")],
            params: &s_params,
            sbox_type: SboxType::Inverse
        };

        let proof = create_random_proof(circuit, &params, rng).unwrap();

        let image: Vec<Fr> = vec![
            Fr::from_str("10276024393822213844666845682424323944661768026855316848735489998167350300948").unwrap(),
            Fr::from_str("10276024393822213844666845682424323944661768026855316848735489998167350300948").unwrap(),
            Fr::from_str("10276024393822213844666845682424323944661768026855316848735489998167350300948").unwrap(),
            Fr::from_str("10276024393822213844666845682424323944661768026855316848735489998167350300948").unwrap()
        ];
        assert!(verify_proof(&pvk, &proof, &image).unwrap());
    }
}