use ark_bls12_381::Fq;
use num::{One, Zero};
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::target::BoolTarget,
    plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig},
};

use crate::fields::bls12_381base::Bls12_381Base;
use crate::fields::fq_target::FqTarget;

#[derive(Clone, Debug)]
pub struct G1AffineTarget<F: RichField + Extendable<D>, const D: usize> {
    pub x: FqTarget<F, D>,
    pub y: FqTarget<F, D>,
    infinity: BoolTarget,
}

impl<F: RichField + Extendable<D>, const D: usize> G1AffineTarget<F, D> {
    pub fn is_identity(&self) -> BoolTarget {
        self.infinity
    }

    /// Returns the identity of the group: the point at infinity.
    pub fn identity() -> Self {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        Self {
            x: FqTarget::constant(&mut builder, Fq::zero()),
            y: FqTarget::constant(&mut builder, Fq::one()),
            infinity: BoolTarget::new_unsafe(builder.one()),
        }
    }

    pub fn generator() -> Self {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        Self {
            x: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0x5cb3_8790_fd53_0c16,
                    0x7817_fc67_9976_fff5,
                    0x154f_95c7_143b_a1c1,
                    0xf0ae_6acd_f3d0_e747,
                    0xedce_6ecc_21db_f440,
                    0x1201_7741_9e0b_fb75,
                ]),
            ),
            y: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0xbaac_93d5_0ce7_2271,
                    0x8c22_631a_7918_fd8e,
                    0xdd59_5f13_5707_25ce,
                    0x51ac_5829_5040_5194,
                    0x0e1c_8c3f_ad00_59c0,
                    0x0bbc_3efc_5008_a26a,
                ]),
            ),
            infinity: BoolTarget::new_unsafe(builder.zero()),
        }
    }
}
