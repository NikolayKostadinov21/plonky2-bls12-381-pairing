use ark_bls12_381::Fq2;
use num::{One, Zero};
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::target::BoolTarget,
    plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig},
};

use crate::fields::{bls12_381base::Bls12_381Base, fq2_target::Fq2Target, fq_target::FqTarget};

#[derive(Clone, Debug)]
pub struct G2ProjectiveTarget<F: RichField + Extendable<D>, const D: usize> {
    pub x: Fq2Target<F, D>,
    pub y: Fq2Target<F, D>,
    pub z: Fq2Target<F, D>,
}

#[derive(Clone, Debug)]
pub struct G2AffineTarget<F: RichField + Extendable<D>, const D: usize> {
    pub x: Fq2Target<F, D>,
    pub y: Fq2Target<F, D>,
    pub infinity: BoolTarget,
}

impl<'a, F: RichField + Extendable<D>, const D: usize> From<&'a G2AffineTarget<F, D>>
    for G2ProjectiveTarget<F, D>
{
    fn from(p: &'a G2AffineTarget<F, D>) -> G2ProjectiveTarget<F, D> {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let zero = Fq2Target::constant(&mut builder, Fq2::zero());
        let one = Fq2Target::constant(&mut builder, Fq2::one());
        G2ProjectiveTarget {
            x: p.x.clone(),
            y: p.y.clone(),
            z: Fq2Target::select(&mut builder, &one, &zero, &p.infinity),
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> From<G2AffineTarget<F, D>>
    for G2ProjectiveTarget<F, D>
{
    fn from(p: G2AffineTarget<F, D>) -> G2ProjectiveTarget<F, D> {
        G2ProjectiveTarget::from(&p)
    }
}

impl<F: RichField + Extendable<D>, const D: usize> G2AffineTarget<F, D> {
    /// Returns the identity of the group: the point at infinity.
    pub fn identity() -> Self {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        Self {
            x: Fq2Target::constant(&mut builder, Fq2::zero()),
            y: Fq2Target::constant(&mut builder, Fq2::one()),
            infinity: BoolTarget::new_unsafe(builder.one()),
        }
    }

    pub fn generator() -> Self {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        Self {
            x: Fq2Target::new(vec![
                FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0xf5f2_8fa2_0294_0a10,
                        0xb3f5_fb26_87b4_961a,
                        0xa1a8_93b5_3e2a_e580,
                        0x9894_999d_1a3c_aee9,
                        0x6f67_b763_1863_366b,
                        0x0581_9192_4350_bcd7,
                    ]),
                ),
                FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0xa5a9_c075_9e23_f606,
                        0xaaa0_c59d_bccd_60c3,
                        0x3bb1_7e18_e286_7806,
                        0x1b1a_b6cc_8541_b367,
                        0xc2b6_ed0e_f215_8547,
                        0x1192_2a09_7360_edf3,
                    ]),
                ),
            ]),
            y: Fq2Target::new(vec![
                FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0x4c73_0af8_6049_4c4a,
                        0x597c_fa1f_5e36_9c5a,
                        0xe7e6_856c_aa0a_635a,
                        0xbbef_b5e9_6e0d_495f,
                        0x07d3_a975_f0ef_25a2,
                        0x0083_fd8e_7e80_dae5,
                    ]),
                ),
                FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0xadc0_fc92_df64_b05d,
                        0x18aa_270a_2b14_61dc,
                        0x86ad_ac6a_3be4_eba0,
                        0x7949_5c4e_c93d_a33a,
                        0xe717_5850_a43c_caed,
                        0x0b2b_c2a1_63de_1bf2,
                    ]),
                ),
            ]),
            infinity: BoolTarget::new_unsafe(builder.zero()),
        }
    }

    pub fn conditional_select(a: &Self, b: &Self, flag: BoolTarget) -> Self {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        Self {
            x: Fq2Target::select(&mut builder, &a.x, &b.x, &flag),
            y: Fq2Target::select(&mut builder, &a.y, &b.y, &flag),
            infinity: builder.or(a.infinity, b.infinity),
        }
    }
}
