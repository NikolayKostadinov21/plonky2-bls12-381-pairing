use ark_bls12_381::{Fq, Fq2};
use ark_ff::Field;
use itertools::Itertools;
use num_bigint::BigUint;
use num_traits::Zero;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::{BoolTarget, Target},
        witness::{PartitionWitness, Witness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
    util::serialization::{Buffer, IoError},
};
use plonky2_ecdsa::gadgets::{
    biguint::{GeneratedValuesBigUint, WitnessBigUint},
    nonnative::CircuitBuilderNonNative,
};

use crate::fields::{
    fq_target::FqTarget,
    helpers::{from_biguint_to_fq, sgn0_fq2},
};

#[derive(Debug, Clone)]
pub struct Fq2Target<F: RichField + Extendable<D>, const D: usize> {
    pub coeffs: [FqTarget<F, D>; 2],
}
impl<F: RichField + Extendable<D>, const D: usize> Fq2Target<F, D> {
    pub fn empty(builder: &mut CircuitBuilder<F, D>) -> Self {
        let coeffs = [(); 2]
            .iter()
            .map(|_| FqTarget::empty(builder))
            .collect_vec()
            .try_into()
            .unwrap();
        Fq2Target { coeffs }
    }

    pub fn new(coeffs: Vec<FqTarget<F, D>>) -> Self {
        Fq2Target {
            coeffs: coeffs.try_into().unwrap(),
        }
    }

    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        for i in 0..2 {
            builder.connect_nonnative(&lhs.coeffs[i].target, &rhs.coeffs[i].target);
        }
    }

    pub fn select(
        builder: &mut CircuitBuilder<F, D>,
        lhs: &Self,
        rhs: &Self,
        flag: &BoolTarget,
    ) -> Self {
        let coeffs = lhs
            .coeffs
            .iter()
            .enumerate()
            .map(|(i, x)| FqTarget::select(builder, x, &rhs.coeffs[i], flag))
            .collect_vec()
            .try_into()
            .unwrap();
        Fq2Target { coeffs }
    }

    pub fn is_equal(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> BoolTarget {
        let flags = (0..2)
            .map(|i| self.coeffs[i].is_equal(builder, &rhs.coeffs[i]).target)
            .collect_vec();
        let is_equal = builder.mul_many(&flags);
        BoolTarget::new_unsafe(is_equal)
    }

    pub fn is_zero(&self, builder: &mut CircuitBuilder<F, D>) -> BoolTarget {
        let zero = Self::constant(builder, Fq2::ZERO);
        self.is_equal(builder, &zero)
    }

    pub fn constant(builder: &mut CircuitBuilder<F, D>, c: Fq2) -> Self {
        let coeffs = [c.c0, c.c1]
            .iter()
            .map(|x| FqTarget::constant(builder, x.clone()))
            .collect_vec()
            .try_into()
            .unwrap();
        Self { coeffs }
    }

    pub fn add(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> Self {
        let coeffs = self
            .coeffs
            .iter()
            .enumerate()
            .map(|(i, x)| x.add(builder, &rhs.coeffs[i]))
            .collect_vec()
            .try_into()
            .unwrap();
        Fq2Target { coeffs }
    }

    pub fn neg(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let coeffs = self
            .coeffs
            .iter()
            .map(|x| x.neg(builder))
            .collect_vec()
            .try_into()
            .unwrap();
        Fq2Target { coeffs }
    }

    pub fn sub(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> Self {
        let coeffs = self
            .coeffs
            .iter()
            .enumerate()
            .map(|(i, x)| x.sub(builder, &rhs.coeffs[i]))
            .collect_vec()
            .try_into()
            .unwrap();
        Fq2Target { coeffs }
    }

    pub fn mul_scalar(&self, builder: &mut CircuitBuilder<F, D>, s: &FqTarget<F, D>) -> Self {
        let coeffs = self
            .coeffs
            .iter()
            .map(|x| x.mul(builder, s))
            .collect_vec()
            .try_into()
            .unwrap();
        Fq2Target { coeffs }
    }

    pub fn mul_scalar_const(&self, builder: &mut CircuitBuilder<F, D>, c: &Fq) -> Self {
        let c = FqTarget::constant(builder, c.clone());
        self.mul_scalar(builder, &c)
    }

    pub fn mul(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> Self {
        let a0 = self.coeffs[0].clone();
        let a1 = self.coeffs[1].clone();

        let b0 = rhs.coeffs[0].clone();
        let b1 = rhs.coeffs[1].clone();

        let a0_b0 = a0.mul(builder, &b0);
        let a1_b1 = a1.mul(builder, &b1);

        let c0 = a0_b0.sub(builder, &a1_b1);

        let a0_b1 = a0.mul(builder, &b1);
        let a1_b0 = a1.mul(builder, &b0);

        let c1 = a0_b1.add(builder, &a1_b0);

        Fq2Target { coeffs: [c0, c1] }
    }

    pub fn mul_by_nonresidue(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        // Multiply a + bu by u + 1, getting
        // au + a + bu^2 + bu
        // and because u^2 = -1, we get
        // (a - b) + (a + b)u

        Self {
            coeffs: [
                self.coeffs[0].sub(builder, &self.coeffs[1]),
                self.coeffs[0].add(builder, &self.coeffs[1]),
            ],
        }
    }

    // check validity
    pub fn mul_w6<const I_0: usize>(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let a0 = self.coeffs[0].clone();
        let a1 = self.coeffs[1].clone();
        // (a0 + a1 u) * (I_0 + u) = (a0 * I_0 - a1) + (a1 * I_0 + a0) u
        let a0_i0 = a0.mul_const(builder, &Fq::from(I_0 as u64));
        let out0 = a0_i0.sub(builder, &a1);
        let a1_i0 = a1.mul_const(builder, &Fq::from(I_0 as u64));
        let out1 = a1_i0.add(builder, &a0);
        Fq2Target {
            coeffs: [out0, out1],
        }
    }

    // this method fails if self is zero
    pub fn inv(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let inv = Self::empty(builder);
        builder.add_simple_generator(Fq2InverseGenerator::<F, D> {
            x: self.clone(),
            inv: inv.clone(),
        });
        let one = Self::constant(builder, Fq2::ONE);
        let x_mul_inv = self.mul(builder, &inv);
        Self::connect(builder, &x_mul_inv, &one);
        inv
    }

    // this method returns zero if self is zero
    pub fn inv0(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let inv = Self::empty(builder);
        builder.add_simple_generator(Fq2InverseGenerator::<F, D> {
            x: self.clone(),
            inv: inv.clone(),
        });
        let is_zero = self.is_zero(builder);
        let is_not_zero = builder.not(is_zero);
        let is_not_zero_fq = FqTarget::from_bool(builder, &is_not_zero);
        let is_not_zero_fq2 = Fq2Target {
            coeffs: [is_not_zero_fq, FqTarget::constant(builder, Fq::zero())],
        };

        let out = inv.mul(builder, &is_not_zero_fq2); // out = inv*is_not_zero
        let in_out = self.mul(builder, &out);
        Self::connect(builder, &in_out, &is_not_zero_fq2); // out * in = is_not_zero

        out
    }

    pub fn div(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> Self {
        let inv = rhs.inv(builder);
        self.mul(builder, &inv)
    }

    pub fn conjugate(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let c0 = self.coeffs[0].clone();
        let c1 = self.coeffs[1].clone();
        Fq2Target {
            coeffs: [c0, c1.neg(builder)],
        }
    }

    pub fn neg_conjugate(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let c0 = self.coeffs[0].clone();
        let c1 = self.coeffs[1].clone();
        Fq2Target {
            coeffs: [c0.neg(builder), c1],
        }
    }

    pub fn sgn0(&self, builder: &mut CircuitBuilder<F, D>) -> BoolTarget {
        let sgn_x = self.coeffs[0].sgn0(builder);
        let is_zero = self.coeffs[0].is_zero(builder);
        let sgn_y = self.coeffs[1].sgn0(builder);
        let is_zero_and_sgn_y = builder.and(is_zero, sgn_y.clone());
        builder.or(sgn_x, is_zero_and_sgn_y)
    }

    pub fn is_square(&self, builder: &mut CircuitBuilder<F, D>) -> BoolTarget {
        let x = self.coeffs[0].clone();
        let y = self.coeffs[1].clone();
        let x_sq = x.mul(builder, &x);
        let y_sq = y.mul(builder, &y);
        let norm = x_sq.add(builder, &y_sq);
        norm.is_square(builder)
    }

    pub fn square(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        // Complex squaring:
        //
        // v0  = c0 * c1
        // c0' = (c0 + c1) * (c0 + \beta*c1) - v0 - \beta * v0
        // c1' = 2 * v0
        //
        // In BLS12-381's F_{p^2}, our \beta is -1 so we
        // can modify this formula:
        //
        // c0' = (c0 + c1) * (c0 - c1)
        // c1' = 2 * c0 * c1

        let c0 = self.coeffs[0].clone();
        let c1 = self.coeffs[1].clone();

        let a = c0.add(builder, &c1);
        let b = c0.sub(builder, &c1);
        let c = c0.add(builder, &c0);

        let r_c0 = a.mul(builder, &b);
        let r_c1 = c.mul(builder, &c1);
        Fq2Target {
            coeffs: [r_c0, r_c1],
        }
    }

    // if self is not square, this fails
    // the return value is ensured to be sgn0(x) = sgn0(sgn)
    pub fn sqrt_with_sgn(&self, builder: &mut CircuitBuilder<F, D>, sgn: BoolTarget) -> Self {
        let sqrt = Self::empty(builder);
        builder.add_simple_generator(Fq2SqrtGenerator::<F, D> {
            x: self.clone(),
            sgn: sgn.clone(),
            sqrt: sqrt.clone(),
        });

        // sqrt^2 = x
        let sqrt_sq = sqrt.mul(builder, &sqrt);
        Self::connect(builder, &sqrt_sq, self);

        // sgn0(sqrt) = sgn0(sgn)
        let sgn0_sqrt = sqrt.sgn0(builder);
        builder.connect(sgn0_sqrt.target, sgn.target);

        sqrt
    }
}

#[derive(Debug)]
struct Fq2InverseGenerator<F: RichField + Extendable<D>, const D: usize> {
    x: Fq2Target<F, D>,
    inv: Fq2Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F>
    for Fq2InverseGenerator<F, D>
{
    fn dependencies(&self) -> Vec<Target> {
        self.x
            .coeffs
            .iter()
            .flat_map(|coeff| coeff.target.value.limbs.iter().map(|&l| l.0))
            .collect_vec()
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let coeffs: Vec<Fq> = self
            .x
            .coeffs
            .iter()
            .map(|x| from_biguint_to_fq(witness.get_biguint_target(x.target.value.clone())))
            .collect_vec();
        let x = Fq2::new(coeffs[0], coeffs[1]);
        let inv_x: Fq2 = match x.inverse() {
            Some(inv_x) => inv_x,
            None => Fq2::zero(),
        };
        let inv_x_biguint: Vec<BigUint> = [inv_x.c0, inv_x.c1]
            .iter()
            .cloned()
            .map(|coeff| coeff.into())
            .collect_vec();

        for i in 0..2 {
            out_buffer.set_biguint_target(&self.inv.coeffs[i].target.value, &inv_x_biguint[i]);
        }
    }

    fn id(&self) -> std::string::String {
        "Fq2InverseGenerator".to_string()
    }

    fn serialize(&self, _: &mut Vec<u8>) -> Result<(), IoError> {
        unimplemented!()
    }
    fn deserialize(_: &mut Buffer) -> Result<Self, IoError> {
        unimplemented!()
    }
}

#[derive(Debug)]
struct Fq2SqrtGenerator<F: RichField + Extendable<D>, const D: usize> {
    x: Fq2Target<F, D>,
    sgn: BoolTarget,
    sqrt: Fq2Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F> for Fq2SqrtGenerator<F, D> {
    fn dependencies(&self) -> Vec<Target> {
        let mut x_vec = self
            .x
            .coeffs
            .iter()
            .flat_map(|coeff| coeff.target.value.limbs.iter().map(|&l| l.0))
            .collect_vec();
        x_vec.push(self.sgn.target);
        x_vec
    }

    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let coeffs: Vec<Fq> = self
            .x
            .coeffs
            .iter()
            .map(|x| from_biguint_to_fq(witness.get_biguint_target(x.target.value.clone())))
            .collect_vec();
        let sgn_val = witness.get_target(self.sgn.target);
        let x = Fq2::new(coeffs[0], coeffs[1]);
        let mut sqrt_x: Fq2 = x.sqrt().unwrap();
        let desired_sgn = sgn_val.to_canonical_u64() % 2 == 1;
        let sng0_x = sgn0_fq2(sqrt_x);
        if sng0_x != desired_sgn {
            sqrt_x = -sqrt_x;
        }
        assert_eq!(sgn0_fq2(sqrt_x), desired_sgn);
        let sqrt_x_biguint: Vec<BigUint> = [sqrt_x.c0, sqrt_x.c1]
            .iter()
            .cloned()
            .map(|coeff| coeff.into())
            .collect_vec();

        for i in 0..2 {
            out_buffer.set_biguint_target(&self.sqrt.coeffs[i].target.value, &sqrt_x_biguint[i]);
        }
    }

    fn id(&self) -> std::string::String {
        "Fq2SqrtGenerator".to_string()
    }

    fn serialize(&self, _: &mut Vec<u8>) -> Result<(), IoError> {
        unimplemented!()
    }
    fn deserialize(_: &mut Buffer) -> Result<Self, IoError> {
        unimplemented!()
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Fq2Target<F, D> {
    pub fn to_vec(&self) -> Vec<Target> {
        self.coeffs.iter().flat_map(|c| c.to_vec()).collect()
    }

    pub fn from_vec(builder: &mut CircuitBuilder<F, D>, input: &[Target]) -> Self {
        let num_limbs = 8;
        assert_eq!(input.len(), 2 * num_limbs);
        let coeffs = input
            .iter()
            .cloned()
            .chunks(num_limbs)
            .into_iter()
            .map(|chunk| FqTarget::from_vec(builder, &chunk.collect_vec()))
            .collect_vec();
        Fq2Target {
            coeffs: coeffs.try_into().unwrap(),
        }
    }

    pub fn set_witness<W: WitnessWrite<F>>(&self, pw: &mut W, value: &Fq2) {
        let coeffs = vec![value.c0, value.c1];
        self.coeffs
            .iter()
            .cloned()
            .zip(coeffs)
            .map(|(c_t, c)| c_t.set_witness(pw, &c))
            .for_each(drop);
    }
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{Fq, Fq2};
    use ark_ff::Field;
    use ark_std::UniformRand;
    use num_traits::{One, Zero};
    use plonky2::{
        field::{goldilocks_field::GoldilocksField, types::Field as plonky2_field},
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    use rand::Rng;

    use crate::fields::helpers::sgn0_fq2;

    use super::Fq2Target;

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_w6() {
        let rng = &mut rand::thread_rng();
        let x: Fq2 = Fq2::rand(rng);
        let x_mul_w6: Fq2 = x * Fq2::new(Fq::from(1), Fq::ONE);

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x_mul_w6_expected = Fq2Target::constant(&mut builder, x_mul_w6);
        let x_t = Fq2Target::constant(&mut builder, x);
        let x_mul_w6_t = x_t.mul_w6::<1>(&mut builder);

        Fq2Target::connect(&mut builder, &x_mul_w6_t, &x_mul_w6_expected);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    // todo! fails when true, true, true

    #[test]
    fn test_fq2_inv_circuit() {
        let rng = &mut rand::thread_rng();
        let x: Fq2 = Fq2::rand(rng);
        let inv_x_expected = x.inverse().unwrap();

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x_t = Fq2Target::constant(&mut builder, x);
        let inv_x_t = x_t.inv(&mut builder);
        let inv_x_expected_t = Fq2Target::constant(&mut builder, inv_x_expected);

        Fq2Target::connect(&mut builder, &inv_x_t, &inv_x_expected_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_is_zero() {
        let zero = Fq2::zero();
        let non_zero = Fq2::rand(&mut rand::thread_rng());
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let zero_t = Fq2Target::constant(&mut builder, zero);
        let is_zero = zero_t.is_zero(&mut builder);
        let non_zero_t = Fq2Target::constant(&mut builder, non_zero);
        let is_zero_non_zero = non_zero_t.is_zero(&mut builder);

        let not_is_zero_non_zero = builder.not(is_zero_non_zero);
        builder.connect(not_is_zero_non_zero.target, is_zero.target);

        let mut pw = PartialWitness::new();
        pw.set_target(is_zero.target, F::ONE);
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_inv0_input_nonzero_success() {
        let rng = &mut rand::thread_rng();
        let x: Fq2 = Fq2::rand(rng);
        let inv_x_expected = x.inverse().unwrap();

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x_t = Fq2Target::constant(&mut builder, x);
        let inv0_x_t = x_t.inv0(&mut builder);
        let inv0_x_expected_t = Fq2Target::constant(&mut builder, inv_x_expected);

        Fq2Target::connect(&mut builder, &inv0_x_t, &inv0_x_expected_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    #[should_panic]
    fn test_inv0_input_nonzero_fail() {
        let rng = &mut rand::thread_rng();
        let x: Fq2 = Fq2::rand(rng);
        let inv_x_expected = x.inverse().unwrap() + Fq2::ONE;

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x_t = Fq2Target::constant(&mut builder, x);
        let inv0_x_t = x_t.inv0(&mut builder);
        let inv0_x_expected_t = Fq2Target::constant(&mut builder, inv_x_expected);

        Fq2Target::connect(&mut builder, &inv0_x_t, &inv0_x_expected_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_inv0_input_zero_success() {
        let x = Fq2::zero();
        let inv_x_expected = Fq2::zero();

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x_t = Fq2Target::constant(&mut builder, x);
        let inv0_x_t = x_t.inv0(&mut builder);
        let inv0_x_expected_t = Fq2Target::constant(&mut builder, inv_x_expected);

        Fq2Target::connect(&mut builder, &inv0_x_t, &inv0_x_expected_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    #[should_panic]
    fn test_inv0_input_zero_fail() {
        let x = Fq2::zero();
        let inv_x_expected = Fq2::one();

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x_t = Fq2Target::constant(&mut builder, x);
        let inv0_x_t = x_t.inv0(&mut builder);
        let inv0_x_expected_t = Fq2Target::constant(&mut builder, inv_x_expected);

        Fq2Target::connect(&mut builder, &inv0_x_t, &inv0_x_expected_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_sgn0() {
        let rng = &mut rand::thread_rng();
        let a: Fq2 = Fq2::rand(rng);
        let expected_a_sgn0 = sgn0_fq2(a);
        dbg!(expected_a_sgn0);

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = Fq2Target::constant(&mut builder, a);
        let sgn0_a_t = a_t.sgn0(&mut builder);
        let expected_sgn0_a_t = builder.constant_bool(expected_a_sgn0);

        builder.connect(sgn0_a_t.target, expected_sgn0_a_t.target);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_sqrt_with_sgn() {
        let rng = &mut rand::thread_rng();
        let a: Fq2 = {
            // resample a until it is a square
            let mut a = Fq2::rand(rng);
            while !a.legendre().is_qr() {
                a = Fq2::rand(rng);
            }
            a
        };
        assert!(a.legendre().is_qr());
        let sgn: bool = rng.gen();
        let sqrt = a.sqrt().unwrap();
        let expected_sqrt = if sgn == sgn0_fq2(sqrt) { sqrt } else { -sqrt };
        assert_eq!(expected_sqrt * expected_sqrt, a);
        assert_eq!(sgn0_fq2(expected_sqrt), sgn);

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a_t = Fq2Target::constant(&mut builder, a);
        let sgn_t = builder.constant_bool(sgn);
        let sqrt_t = a_t.sqrt_with_sgn(&mut builder, sgn_t);
        let expected_sqrt_t = Fq2Target::constant(&mut builder, expected_sqrt);

        Fq2Target::connect(&mut builder, &sqrt_t, &expected_sqrt_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        let _proof = data.prove(pw);
    }
}
