extern crate bellman;
extern crate pairing;
extern crate rand;

// For randomness (during paramgen and proof generation)
use rand::{thread_rng, Rng, Rand};

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

pub enum SboxType<E: Engine> {
    Quint(E),
    Inverse(E)
}

impl<E: Engine> SboxType<E> {
    pub fn apply(&self, elem: &E::Fr) -> E::Fr {
        match self {
            SboxType::Inverse(E) => Self::apply_inverse_sbox(elem),
            SboxType::Quint(E) => Self::apply_quintic_sbox(elem)
        }
    }

    // Allocate variables in circuit and enforce constraints for Sbox layer
    pub fn synthesize<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        input_val: &Option<E::Fr>,
        input_var: Variable,
        round_key: E::Fr
    ) -> Result<Option<E::Fr>, SynthesisError> {
        match self {
            SboxType::Quint(E) => Self::synthesize_quintic_sbox::<CS>(cs, input_val, input_var, round_key),
            SboxType::Inverse(E) => Self::synthesize_inverse_sbox::<CS>(cs, input_val, input_var, round_key)
        }
    }

    // Allocate variables in circuit and enforce constraints when Sbox as cube
    fn synthesize_quintic_sbox<CS: ConstraintSystem<E>>(
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
            || "square constraint (x * x = x^2)",
            |lc| lc + input_var + (round_key, CS::one()),
            |lc| lc + input_var + (round_key, CS::one()),
            |lc| lc + square
        );

        let mut quad_val = square_val.map(|mut t| {
            t.square();
            t
        });
        let mut quad = cs.alloc(|| "quad", || {
            quad_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        cs.enforce(
            || "quad constraint (x^2 * x^2 = x^2)",
            |lc| lc + square,
            |lc| lc + square,
            |lc| lc + quad
        );

        let mut quint_val = quad_val.map(|mut t| {
            t.mul_assign(&tmp.unwrap());
            t
        });
        let mut quint = cs.alloc(|| "quint", || {
            quint_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        cs.enforce(
            || "quint constraint (x^4 * x = x^5)",
            |lc| lc + quad,
            |lc| lc + input_var + (round_key, CS::one()),
            |lc| lc + quint
        );

        Ok(quint_val)
    }

    // Allocate variables in circuit and enforce constraints when Sbox as inverse
    fn synthesize_inverse_sbox<CS: ConstraintSystem<E>>(
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
            Self::apply_inverse_sbox(&t)
        });
        let mut inverse = cs.alloc(|| "inverse", || {
            inverse_val.ok_or(SynthesisError::AssignmentMissing)
        })?;
        cs.enforce(
            || "inverse constraint (x * x^-1 = 1)",
            |lc| lc + input_var + (round_key, CS::one()),
            |lc| lc + inverse,
            |lc| lc + CS::one()
        );

        Ok(inverse_val)
    }

    fn apply_quintic_sbox(elem: &E::Fr) -> E::Fr
    {
        let mut elem_sqr = elem.clone();
        elem_sqr.mul_assign(elem);

        let mut res = elem.clone();
        res.mul_assign(&elem_sqr);
        res.mul_assign(&elem_sqr);
        res
    }

    fn apply_inverse_sbox(elem: &E::Fr) -> E::Fr
    {
        elem.inverse().map_or(E::Fr::zero(), | t | t)
    }
}

struct PoseidonParams<E: Engine> {
    pub width: usize,
    pub full_rounds_beginning: usize,
    pub partial_rounds: usize,
    pub full_rounds_end: usize,
//    pub round_constants: Vec<E::Fr>,
    pub round_keys: Vec<E::Fr>,
    // TODO: Add matrix_1
    pub matrix_2: Vec<Vec<E::Fr>>
}

impl<E: Engine> PoseidonParams<E> {
    fn new(width: usize, full_rounds_beginning: usize, partial_rounds: usize, full_rounds_end: usize) -> PoseidonParams<E> {
        let total_rounds = full_rounds_beginning + partial_rounds + full_rounds_end;
//        let round_constants = Self::gen_round_constants(width, total_rounds);
        let round_keys = Self::gen_round_keys(width, total_rounds);
        let matrix_2 = Self::gen_matrix_2(width);
        PoseidonParams {
            width,
            full_rounds_beginning,
            partial_rounds,
            full_rounds_end,
//            round_constants,
            round_keys,
            matrix_2
        }
    }

    fn gen_round_keys(width: usize, total_rounds: usize) -> Vec<E::Fr> {
        let cap = (total_rounds + 1) * width;
        let mut rng = &mut thread_rng();
        let mut rk = vec![];
        for _ in 0..cap {
            rk.push(E::Fr::rand(&mut rng));
        }
        rk
        //vec![E::Fr::one(); cap]
    }

    fn gen_matrix_2(width: usize) -> Vec<Vec<E::Fr>> {
        let mut rng = &mut thread_rng();
        let mut matrix = vec![];
        for _ in 0..width {
            let mut row = vec![];
            for _ in 0..width {
                row.push(E::Fr::rand(&mut rng));
            }
            matrix.push(row)
        }
        matrix
        //vec![vec![E::Fr::one(); width]; width]
    }
}

// Sbox is parametrized using function `apply_sbox`
fn PoseidonPerm<E: Engine>(
    input: Vec<E::Fr>,
    params: &PoseidonParams<E>,
    sbox_type: &SboxType<E>
) -> Vec<E::Fr>
{
    assert_eq!(input.len(), params.width);

    let mut current_state = input;
    let mut current_state_temp = vec![E::Fr::zero(); params.width];

    let mut round_keys_offset = 0;

    // 3 full Sbox rounds
    for _ in 0..params.full_rounds_beginning {
        // Sbox layer
        for i in 0..params.width {
            current_state[i].add_assign(&params.round_keys[round_keys_offset]);
            current_state[i] = sbox_type.apply(&current_state[i]);
            round_keys_offset += 1;
        }

        // linear layer
        for i in 0..params.width {
            for j in 0..params.width {
                let mut temp = current_state[j].clone();
                temp.mul_assign(&params.matrix_2[j][i]);
                current_state_temp[i].add_assign(&temp);
            }
        }

        // Output of this round becomes input to next round
        for i in 0..params.width {
            current_state[i] = current_state_temp[i];
            current_state_temp[i] = E::Fr::zero();
        }
    }

    // middle partial Sbox rounds
    for _ in params.full_rounds_beginning..(params.full_rounds_beginning+params.partial_rounds) {
        for i in 0..params.width {
            current_state[i].add_assign(&params.round_keys[round_keys_offset]);
            round_keys_offset += 1;
        }

        // partial Sbox layer
        current_state[params.width-1] = sbox_type.apply(&current_state[params.width-1]);

        // linear layer
        for i in 0..params.width {
            for j in 0..params.width {
                let mut temp = current_state[j].clone();
                temp.mul_assign(&params.matrix_2[j][i]);
                current_state_temp[i].add_assign(&temp);
            }
        }

        // Output of this round becomes input to next round
        for i in 0..params.width {
            current_state[i] = current_state_temp[i];
            current_state_temp[i] = E::Fr::zero();
        }
    }

    // last full Sbox rounds
    for _ in (params.full_rounds_beginning+params.partial_rounds)..(params.full_rounds_beginning+params.partial_rounds+params.full_rounds_end) {
        // Sbox layer
        for i in 0..params.width {
            current_state[i].add_assign(&params.round_keys[round_keys_offset]);
            current_state[i] = sbox_type.apply(&current_state[i]);
            round_keys_offset += 1;
        }

        // linear layer
        for i in 0..params.width {
            for j in 0..params.width {
                let mut temp = current_state[j].clone();
                temp.mul_assign(&params.matrix_2[j][i]);
                current_state_temp[i].add_assign(&temp);
            }
        }

        // Output of this round becomes input to next round
        for i in 0..params.width {
            current_state[i] = current_state_temp[i];
            current_state_temp[i] = E::Fr::zero();
        }
    }

    current_state
}

// Circuit for proving knowledge of the preimage of a SharkMiMC hash.
struct PoseidonPermCircuit<'a, E: Engine> {
    pub input: Vec<Option<E::Fr>>,
    params: &'a PoseidonParams<E>,
    sbox_type: SboxType<E>
}

impl<'a, E: Engine> Circuit<E> for PoseidonPermCircuit<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        let width = self.params.width;
        assert_eq!(self.input.len(), width);
        let mut input_vals: Vec<Option<E::Fr>> = vec![None; width];
        let mut input_vars: Vec<Variable> = vec![CS::one(); width];

        for i in 0..width {
            input_vals[i] = self.input[i];
            input_vars[i] = cs.alloc(|| format!("input {}", i), || {
                input_vals[i].ok_or(SynthesisError::AssignmentMissing)
            })?;
        }

        let mut round_keys_offset = 0;

        fn apply_linear_layer<E: Engine>(
            width: usize,
            sbox_out_vals: &Vec<Option<E::Fr>>,
            next_input_vals: &mut Vec<Option<E::Fr>>,
            matrix_2: &Vec<Vec<E::Fr>>,
        ) {
            for i in 0..width {
                for j in 0..width {
                    let tmp = sbox_out_vals[j].clone().map( | mut t | {
                        t.mul_assign(&matrix_2[j][i]);
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

        for k in 0..self.params.full_rounds_beginning {
            let mut sbox_out_vals: Vec<Option<E::Fr>> = vec![None; width];

            // Substitution (S-box) layer
            for i in 0..width {
                let mut cs = &mut cs.namespace(|| format!("sbox: round-branch: {}:{}", k, i));

                let round_key = self.params.round_keys[round_keys_offset];

                sbox_out_vals[i] = self.sbox_type.synthesize(&mut cs, &input_vals[i].clone(),
                                                             input_vars[i].clone(), round_key.clone())?;

                round_keys_offset += 1;
            }

            // Linear layer

            let mut next_input_vals: Vec<Option<E::Fr>> = vec![Some(E::Fr::zero()); width];

            apply_linear_layer::<E>(width, &sbox_out_vals, &mut next_input_vals, &self.params.matrix_2);

            for i in 0..width {
                input_vals[i] = next_input_vals[i];

                // Only first branch of output of the last round is used for constraint for middle rounds
                if k < (self.params.full_rounds_beginning-1) || i == (width-1) {
                    let cs = &mut cs.namespace(|| format!("linear: round-branch: {}:{}", k, i));
                    input_vars[i] = cs.alloc(|| "linear", || {
                        next_input_vals[i].ok_or(SynthesisError::AssignmentMissing)
                    })?;
                }
            }
        }

        // ------------ First 3 rounds end --------------------

        // ------------ Middle rounds begin --------------------

        for k in self.params.full_rounds_beginning..(self.params.full_rounds_beginning+self.params.partial_rounds) {
            let mut sbox_out_vals: Vec<Option<E::Fr>> = vec![None; width];

            // Substitution (S-box) layer
            for i in 0..width {
                let mut cs = &mut cs.namespace(|| format!("sbox: round-branch: {}:{}", k, i));

                let round_key = self.params.round_keys[round_keys_offset];

                if i == (width-1) {
                    sbox_out_vals[i] = self.sbox_type.synthesize(&mut cs, &input_vals[i].clone(),
                                                                 input_vars[i].clone(), round_key.clone())?;
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

            let mut next_input_vals: Vec<Option<E::Fr>> = vec![Some(E::Fr::zero()); width];

            apply_linear_layer::<E>(width, &sbox_out_vals, &mut next_input_vals, &self.params.matrix_2);

            for i in 0..width {
                input_vals[i] = next_input_vals[i];

                // For middle rounds, only first branch is involved in constraints. Allocate variables for
                // all branches only for the last middle round such that it can be used for input for next round.
                if i == (width-1) || k == (self.params.full_rounds_beginning+self.params.partial_rounds -1) {
                    let cs = &mut cs.namespace(|| format!("linear: round-branch: {}:{}", k, i));
                    input_vars[i] = cs.alloc(|| "linear", || {
                        next_input_vals[i].ok_or(SynthesisError::AssignmentMissing)
                    })?;
                }
            }
        }

        // ------------ Middle rounds end --------------------

        // ------------ Last full rounds begin --------------------

        // 3 rounds
        for k in (self.params.full_rounds_beginning+self.params.partial_rounds)..(self.params.full_rounds_beginning+self.params.partial_rounds+self.params.full_rounds_end) {
            let mut sbox_out_vals: Vec<Option<E::Fr>> = vec![None; width];

            // Substitution (S-box) layer
            for i in 0..width {
                let mut cs = &mut cs.namespace(|| format!("sbox: round-branch: {}:{}", k, i));

                let round_key = self.params.round_keys[round_keys_offset];

                sbox_out_vals[i] = self.sbox_type.synthesize(&mut cs, &input_vals[i].clone(),
                                                             input_vars[i].clone(), round_key.clone())?;

                round_keys_offset += 1;
            }

            // Linear layer

            let mut next_input_vals: Vec<Option<E::Fr>> = vec![Some(E::Fr::zero()); width];

            apply_linear_layer::<E>(width, &sbox_out_vals, &mut next_input_vals, &self.params.matrix_2);

            for i in 0..width {
                let cs = &mut cs.namespace(|| format!("linear: round-branch: {}:{}", k, i));
                if k == (self.params.full_rounds_beginning+self.params.partial_rounds+self.params.full_rounds_end-1) {
                    input_vals[i] = next_input_vals[i];
                    input_vars[i] = cs.alloc_input(|| "output", || {
                        next_input_vals[i].ok_or(SynthesisError::AssignmentMissing)
                    })?;
                } else {
                    input_vals[i] = next_input_vals[i];
                    input_vars[i] = cs.alloc(|| "linear", || {
                        next_input_vals[i].ok_or(SynthesisError::AssignmentMissing)
                    })?;
                }
            }
        }

        // ------------ Last 2+1 rounds end --------------------
        println!("synthesis done");
        Ok(())
    }
}


mod test {
    use std::time::{Duration, Instant};
    use pairing::bls12_381::{Bls12, Fr, FrRepr};
    use pairing::{PrimeField, PrimeFieldRepr};
    use testing_cs::TestConstraintSystem;
    use super::*;

    #[test]
    fn PoseidonPerm_with_TestConstraintSystem() {
        let width = 6;
        let full_rounds_beginning = 4;
        let partial_rounds = 57;
        let full_rounds_end = 4;
        let s_params = PoseidonParams::<Bls12>::new(width, full_rounds_beginning, partial_rounds, full_rounds_end);
        let total_rounds = full_rounds_beginning + partial_rounds + full_rounds_end;

        let input = vec![Fr::from_str("1"), Fr::from_str("2"),
                         Fr::from_str("3"), Fr::from_str("4"), Fr::from_str("5"), Fr::from_str("6")];
        println!("Input >>>>>>>>>");
        println!("{:?}", input[0]);
        println!("{:?}", input[1]);
        println!("{:?}", input[2]);
        println!("{:?}", input[3]);

        let mut input1 = vec![Fr::zero(); width];
        for i in 0..width {
            input1[i] = input[i].clone().unwrap();
        }
        let input2 = input1.clone();
        let image_from_quintic = PoseidonPerm::<Bls12>(input1, &s_params, &SboxType::Quint(Bls12));
        let image_from_inverse = PoseidonPerm::<Bls12>(input2, &s_params, &SboxType::Inverse(Bls12));

        println!("Output with Sbox as cube (from function) >>>>>>>>>");
        for i in 0..width {
            println!("{:?}", image_from_quintic[i]);
        }

        println!("Output with Sbox as inverse (from function) >>>>>>>>>");
        for i in 0..width {
            println!("{:?}", image_from_inverse[i]);
        }

        {
            println!("Checking with Sbox as cube");
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let c = PoseidonPermCircuit::<Bls12> {
                input: input.clone(),
                params: &s_params,
                sbox_type: SboxType::Quint(Bls12)
            };

            c.synthesize(&mut cs).unwrap();
            let satisfied = cs.is_satisfied();
            assert!(satisfied);
            println!("Is satisfied {}", satisfied);
            println!("Num constraints {}", &cs.num_constraints());
//    println!("{}", &cs.pretty_print());
            let mut image_from_circuit = vec![Fr::zero(); width];

            for i in 0..width {
                image_from_circuit[i] = cs.get(&format!("linear: round-branch: {}:{}/output", total_rounds - 1, i));
                println!("Output {}:{}", i, &image_from_circuit[i]);
            }

            assert_eq!(image_from_quintic, image_from_circuit);
//    println!("{}", cs.find_unconstrained());
            println!("Successful with Sbox as cube");
        }

        {
            println!("Checking with Sbox as inverse");
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let c = PoseidonPermCircuit::<Bls12> {
                input,
                params: &s_params,
                sbox_type: SboxType::Inverse(Bls12)
            };

            c.synthesize(&mut cs).unwrap();
            let satisfied = cs.is_satisfied();
            assert!(satisfied);
            println!("Is satisfied {}", satisfied);
            println!("Num constraints {}", &cs.num_constraints());

            let mut image_from_circuit = vec![Fr::zero(); width];

            for i in 0..width {
                image_from_circuit[i] = cs.get(&format!("linear: round-branch: {}:{}/output", total_rounds - 1, i));
                println!("Output {}:{}", i, &image_from_circuit[i]);
            }

            assert_eq!(image_from_inverse, image_from_circuit);

            println!("Successful with Sbox as inverse");
        }
    }

    #[test]
    fn PoseidonPerm_basic() {
        let rng = &mut thread_rng();

        let width = 6;
        let full_rounds_beginning = 4;
        let partial_rounds = 57;
        let full_rounds_end = 4;
        let s_params = PoseidonParams::<Bls12>::new(width, full_rounds_beginning, partial_rounds, full_rounds_end);
        let total_rounds = full_rounds_beginning + partial_rounds + full_rounds_end;

        {
            let params = {
                let c = PoseidonPermCircuit::<Bls12> {
                    input: vec![None; width],
                    params: &s_params,
                    sbox_type: SboxType::Quint(Bls12)
                };

                let x = generate_random_parameters(c, rng);
                x.unwrap()
            };

            let input = vec![Fr::from_str("1"), Fr::from_str("2"),
                             Fr::from_str("3"), Fr::from_str("4"), Fr::from_str("5"), Fr::from_str("6")];
            let image: Vec<Fr> = PoseidonPerm::<Bls12>(input.iter().map(|f|f.unwrap()).collect(), &s_params, &SboxType::Quint(Bls12));

            let pvk = prepare_verifying_key(&params.vk);

            let circuit = PoseidonPermCircuit::<Bls12> {
                input,
                params: &s_params,
                sbox_type: SboxType::Quint(Bls12)
            };

            let start = Instant::now();
            let proof = create_random_proof(circuit, &params, rng).unwrap();
            println!("Proof gen time with Sbox as cube {:?}", start.elapsed());

            assert!(verify_proof(&pvk, &proof, &image).unwrap());
        }

        {
            let params = {
                let c = PoseidonPermCircuit::<Bls12> {
                    input: vec![None; width],
                    params: &s_params,
                    sbox_type: SboxType::Inverse(Bls12)
                };

                let x = generate_random_parameters(c, rng);
                x.unwrap()
            };

            let input = vec![Fr::from_str("1"), Fr::from_str("2"),
                             Fr::from_str("3"), Fr::from_str("4"), Fr::from_str("5"), Fr::from_str("6")];
            let image: Vec<Fr> = PoseidonPerm::<Bls12>(input.iter().map(|f|f.unwrap()).collect(), &s_params, &SboxType::Inverse(Bls12));

            let pvk = prepare_verifying_key(&params.vk);

            let circuit = PoseidonPermCircuit::<Bls12> {
                input,
                params: &s_params,
                sbox_type: SboxType::Inverse(Bls12)
            };

            let start = Instant::now();
            let proof = create_random_proof(circuit, &params, rng).unwrap();
            println!("Proof gen time with Sbox as inverse {:?}", start.elapsed());


            assert!(verify_proof(&pvk, &proof, &image).unwrap());
        }
    }
}