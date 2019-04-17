use pairing::{
    Engine,
    Field,
    PrimeField,
    PrimeFieldRepr
};

use bellman::{Circuit, ConstraintSystem, SynthesisError, LinearCombination, Variable};

use mimc::MIMC_ROUNDS;

pub fn are_equal<E: Engine>(a: &E::Fr, b: &E::Fr) -> bool {
    let mut a = a.clone();
    a.sub_assign(b);
    a.is_zero()
}

pub fn are_equal_mut<E: Engine>(mut a: E::Fr, b: &E::Fr) -> bool {
    a.sub_assign(b);
    a.is_zero()
}

pub fn reduce_field_repr_to_elem<E: Engine>(elem_repr: <E::Fr as PrimeField>::Repr) -> E::Fr {
    E::Fr::from_repr(reduce_field_repr::<E>(elem_repr)).unwrap()
}

pub fn reduce_field_repr<E: Engine>(elem_repr: <E::Fr as PrimeField>::Repr) -> <E::Fr as PrimeField>::Repr {
    let modulus = E::Fr::char();

    let mut r = elem_repr.clone();
    while r >= modulus {
        r.sub_noborrow(&modulus);
    }
    r
}


/// Convert field element to bit vector with LSB in beginning of vector and MSB in last
pub fn field_elem_to_bitvec<E: Engine>(elem: E::Fr, size: usize) -> Vec<E::Fr> {
    let mut bitvec = Vec::<E::Fr>::with_capacity(size);
    let mut elem = elem.into_repr();

    let zero = E::Fr::zero();
    let one = E::Fr::one();

    for i in 0..size {
        if elem.is_odd() {
            bitvec.push(one)
        } else {
            bitvec.push(zero)
        }
        //elem.shr(1);
        elem.div2();
    }
    bitvec
}

/// For a field element, check if the most signification bit is 0
/// elem_size is size of element in bits
#[macro_export]
macro_rules! is_msb_zero {
    ( $elem:expr, $elem_size:expr ) => {
        {
            let mut e = $elem.clone();
            e.shr($elem_size-1);
            e.is_zero()
        }
    };
}

pub fn field_elem_to_bytes<E: Engine>(elem: &E::Fr) -> Vec<u8> {
    let mut v: Vec<u8> = vec![];
    elem.into_repr().write_be(&mut v).unwrap();
    v
}

pub fn bytes_to_field_elem<E: Engine>(key: Vec<u8>) -> E::Fr {
    let mut z = <E::Fr as PrimeField>::Repr::default();
    z.read_be(&key[0..]).unwrap();
    E::Fr::from_repr(z).unwrap()
}

pub fn hash_2<E: Engine, CS: ConstraintSystem<E>>(cs: &mut CS,
                                              mut left_val: Option<E::Fr>,
                                              mut left: Variable,
                                              mut right_val: Option<E::Fr>,
                                              mut right: Variable,
                                              alloc_input: bool,
                                              mimc_rounds: usize,
                                              mimc_constants: &[E::Fr]) -> Result<(Option<E::Fr>, Variable), SynthesisError> {
    for j in 0..mimc_rounds {
        // xL, xR := xR + (xL + Ci)^3, xL
        let cs = &mut cs.namespace(|| format!("mimc round {}", j));

        // tmp = (xL + Ci)^2
        let mut tmp_value = left_val.map(|mut e| {
            e.add_assign(&mimc_constants[j]);
            e.square();
            e
        });
        let mut tmp = cs.alloc(|| "tmp", || {
            tmp_value.ok_or(SynthesisError::AssignmentMissing)
        })?;

        cs.enforce(
            || "tmp = (xL + Ci)^2",
            |lc| lc + left + (mimc_constants[j], CS::one()),
            |lc| lc + left + (mimc_constants[j], CS::one()),
            |lc| lc + tmp
        );

        // new_xL = xR + (xL + Ci)^3
        // new_xL = xR + tmp * (xL + Ci)
        // new_xL - xR = tmp * (xL + Ci)
        let mut new_xl_value = left_val.map(|mut e| {
            e.add_assign(&mimc_constants[j]);
            e.mul_assign(&tmp_value.unwrap());
            e.add_assign(&right_val.unwrap());
            e
        });

        let mut new_xl = if alloc_input && (j == (MIMC_ROUNDS-1)) {
            // This is the last round, xL is our image and so
            // we allocate a public input.
            cs.alloc_input(|| "root", || {
                new_xl_value.ok_or(SynthesisError::AssignmentMissing)
            })?
        } else {
            cs.alloc(|| "new_xl", || {
                new_xl_value.ok_or(SynthesisError::AssignmentMissing)
            })?
        };

        cs.enforce(
            || "new_xL = xR + (xL + Ci)^3",
            |lc| lc + tmp,
            |lc| lc + left + (mimc_constants[j], CS::one()),
            |lc| lc + new_xl - right
        );

        // xR = xL
        right = left;
        right_val = left_val;

        // xL = new_xL
        left = new_xl;
        left_val = new_xl_value;
    }
    Ok((left_val, left))
}

mod tests {
    use super::*;
    // For randomness (during paramgen and proof generation)
    use rand::{thread_rng, Rng};
    use mimc::MIMC_ROUNDS;
    use testing_cs::TestConstraintSystem;
    use std::time::{Duration, Instant};

    use pairing::bls12_381::{Bls12, Fr, FrRepr};

    #[test]
    fn test_to_and_from_key() {
        let rng = &mut thread_rng();

        let x: Fr = rng.gen();

        let key = field_elem_to_bytes::<Bls12>(&x);

        let zz = bytes_to_field_elem::<Bls12>(key.clone());

        assert!(are_equal_mut::<Bls12>(zz, &x));
    }
}