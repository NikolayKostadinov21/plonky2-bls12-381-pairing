use core::fmt::{self, Debug, Display, Formatter};
use core::hash::{Hash, Hasher};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use ark_bls12_381::Fq;
use itertools::Itertools;
use num::bigint::BigUint;
use num::{Integer, One};
use serde::{Deserialize, Serialize};

use plonky2::field::types::{Field, PrimeField, Sample};

/// The base field of the bls12-381 elliptic curve.
///
/// Its order is
/// ```ignore
/// P = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
/// ```
#[derive(Copy, Clone, Serialize, Deserialize)]
pub struct Bls12_381Base(pub [u64; 6]);

fn biguint_from_array(arr: [u64; 6]) -> BigUint {
    BigUint::from_slice(&[
        arr[0] as u32,
        (arr[0] >> 32) as u32,
        arr[1] as u32,
        (arr[1] >> 32) as u32,
        arr[2] as u32,
        (arr[2] >> 32) as u32,
        arr[3] as u32,
        (arr[3] >> 32) as u32,
        arr[4] as u32,
        (arr[4] >> 32) as u32,
        arr[5] as u32,
        (arr[5] >> 32) as u32,
    ])
}

impl Default for Bls12_381Base {
    fn default() -> Self {
        Self::ZERO
    }
}

impl PartialEq for Bls12_381Base {
    fn eq(&self, other: &Self) -> bool {
        self.to_canonical_biguint() == other.to_canonical_biguint()
    }
}

impl Eq for Bls12_381Base {}

impl Hash for Bls12_381Base {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.to_canonical_biguint().hash(state)
    }
}

impl Display for Bls12_381Base {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.to_canonical_biguint(), f)
    }
}

impl Debug for Bls12_381Base {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.to_canonical_biguint(), f)
    }
}

impl Sample for Bls12_381Base {
    #[inline]
    fn sample<R>(rng: &mut R) -> Self
    where
        R: rand::RngCore + ?Sized,
    {
        use num::bigint::RandBigInt;
        Self::from_noncanonical_biguint(rng.gen_biguint_below(&Self::order()))
    }
}

impl Field for Bls12_381Base {
    const ZERO: Self = Self([0; 6]);
    const ONE: Self = Self([1, 0, 0, 0, 0, 0]);
    const TWO: Self = Self([2, 0, 0, 0, 0, 0]);
    const NEG_ONE: Self = Self([
        // P - 1
        0xB9FEFFFFFFFFAAAA,
        0x1EABFFFEB153FFFF,
        0x6730D2A0F6B0F624,
        0x64774B84F38512BF,
        0x4B1BA7B6434BACD7,
        0x1A0111EA397FE69A,
    ]);

    const TWO_ADICITY: usize = 1;
    const CHARACTERISTIC_TWO_ADICITY: usize = Self::TWO_ADICITY;

    // Sage: `g = GF(p).multiplicative_generator()`
    const MULTIPLICATIVE_GROUP_GENERATOR: Self = Self([3, 0, 0, 0, 0, 0]);

    // Sage: `g_2 = g^((p - 1) / 2)`
    const POWER_OF_TWO_GENERATOR: Self = Self::NEG_ONE;

    const BITS: usize = 381;

    fn order() -> BigUint {
        BigUint::from_slice(&[
            0xFFFFAAAB, 0xB9FEFFFF, 0xB153FFFF, 0x1EABFFFE, 0xF6B0F624, 0x6730D2A0, 0xF38512BF,
            0x64774B84, 0x434BACD7, 0x4B1BA7B6, 0x397FE69A, 0x1A0111EA,
        ])
    }
    fn characteristic() -> BigUint {
        Self::order()
    }

    fn try_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        // Fermat's Little Theorem
        Some(self.exp_biguint(&(Self::order() - BigUint::one() - BigUint::one())))
    }

    fn from_noncanonical_biguint(val: BigUint) -> Self {
        Self(
            val.to_u64_digits()
                .into_iter()
                .pad_using(6, |_| 0)
                .collect::<Vec<_>>()[..]
                .try_into()
                .expect("error converting to u64 array"),
        )
    }

    #[inline]
    fn from_canonical_u64(n: u64) -> Self {
        Self([n, 0, 0, 0, 0, 0])
    }

    #[inline]
    fn from_noncanonical_u128(n: u128) -> Self {
        Self([n as u64, (n >> 64) as u64, 0, 0, 0, 0])
    }

    #[inline]
    fn from_noncanonical_u96(n: (u64, u32)) -> Self {
        Self([n.0, n.1 as u64, 0, 0, 0, 0])
    }

    #[inline]
    fn from_noncanonical_u64(_: u64) -> Self {
        todo!()
    }

    #[inline]
    fn from_noncanonical_i64(_: i64) -> Self {
        todo!()
    }
}

impl PrimeField for Bls12_381Base {
    fn to_canonical_biguint(&self) -> BigUint {
        let mut result = biguint_from_array(self.0);
        if result >= Self::order() {
            result -= Self::order();
        }
        result
    }
}

impl Neg for Bls12_381Base {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        if self.is_zero() {
            Self::ZERO
        } else {
            Self::from_noncanonical_biguint(Self::order() - self.to_canonical_biguint())
        }
    }
}

impl Add for Bls12_381Base {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        let mut result = self.to_canonical_biguint() + rhs.to_canonical_biguint();
        if result >= Self::order() {
            result -= Self::order();
        }
        Self::from_noncanonical_biguint(result)
    }
}

impl AddAssign for Bls12_381Base {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sum for Bls12_381Base {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, x| acc + x)
    }
}

impl Sub for Bls12_381Base {
    type Output = Self;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, rhs: Self) -> Self {
        self + -rhs
    }
}

impl SubAssign for Bls12_381Base {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Mul for Bls12_381Base {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self::from_noncanonical_biguint(
            (self.to_canonical_biguint() * rhs.to_canonical_biguint()).mod_floor(&Self::order()),
        )
    }
}

impl MulAssign for Bls12_381Base {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Product for Bls12_381Base {
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc * x).unwrap_or(Self::ONE)
    }
}

impl Div for Bls12_381Base {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inverse()
    }
}

impl DivAssign for Bls12_381Base {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl From<Fq> for Bls12_381Base {
    fn from(value: Fq) -> Self {
        let biguint = value.into();
        Bls12_381Base::from_noncanonical_biguint(biguint)
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;
    use ark_bls12_381::Fq;
    use plonky2::{
        field::types::Sample,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
    };
    use plonky2_ecdsa::gadgets::nonnative::CircuitBuilderNonNative;

    use super::Bls12_381Base;
    #[test]
    fn test_add_base_circuit() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::pairing_config();

        let pw = PartialWitness::<F>::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        for _ in 0..100 {
            let a = Bls12_381Base::rand();
            let b = Bls12_381Base::rand();
            let x = builder.constant_nonnative(a);
            let y = builder.constant_nonnative(b);
            let z = builder.add_nonnative(&x, &y);
            let expected_z = builder.constant_nonnative(a + b);
            builder.connect_nonnative(&z, &expected_z);
        }

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)?;

        Ok(())
    }

    #[test]
    fn test_add_base_special_circuit() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::pairing_config();

        let pw = PartialWitness::<F>::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let a: Bls12_381Base = Fq::from(10).into();
        let b: Bls12_381Base = Fq::from(-10).into();
        let x = builder.constant_nonnative(a);
        let y = builder.constant_nonnative(b);
        let z = builder.add_nonnative(&x, &y);
        let expected_z = builder.constant_nonnative(a + b);
        builder.connect_nonnative(&z, &expected_z);

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)?;

        Ok(())
    }

    #[test]
    fn test_mul_base_circuit() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::pairing_config();

        let pw = PartialWitness::<F>::new();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        for _ in 0..100 {
            let a = Bls12_381Base::rand();
            let b = Bls12_381Base::rand();
            let x = builder.constant_nonnative(a);
            let y = builder.constant_nonnative(b);
            let z = builder.mul_nonnative(&x, &y);
            let x_big = builder.nonnative_to_canonical_biguint(&x);
            x_big.limbs;
            let expected_z = builder.constant_nonnative(a * b);
            builder.connect_nonnative(&z, &expected_z);
        }

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();

        data.verify(proof)?;

        Ok(())
    }
}
