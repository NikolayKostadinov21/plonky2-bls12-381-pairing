use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::target::BoolTarget,
    plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig},
};

use crate::fields::{bls12_381base::Bls12_381Base, fq_target::FqTarget};

use super::fq2_target_tree::Fq2Target;

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
        let zero = Fq2Target::zero(&mut builder);
        let one = Fq2Target::one(&mut builder);
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
            x: Fq2Target::zero(&mut builder),
            y: Fq2Target::one(&mut builder),
            infinity: builder._true(),
        }
    }

    pub fn generator() -> Self {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        Self {
            x: Fq2Target {
                c0: FqTarget::fp_constant(
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
                c1: FqTarget::fp_constant(
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
            },
            y: Fq2Target {
                c0: FqTarget::fp_constant(
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
                c1: FqTarget::fp_constant(
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
            },
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

    pub fn is_point_equal_to(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> BoolTarget {
        // The only cases in which two points are equal are
        // 1. infinity is set on both
        // 2. infinity is not set on both, and their coordinates are equal

        let inf_set_on_both = builder.and(self.infinity, rhs.infinity);
        let inf_not_set_on_self = builder.not(self.infinity);
        let inf_not_set_on_rhs = builder.not(rhs.infinity);
        let inf_not_set_on_both = builder.and(inf_not_set_on_self, inf_not_set_on_rhs);

        let x_eq_x = self.x.is_equal(builder, &rhs.x);
        let y_eq_y = self.y.is_equal(builder, &rhs.y);

        let x_y_are_eq = builder.and(x_eq_x, y_eq_y);
        let second_pred = builder.and(x_y_are_eq, inf_not_set_on_both);

        builder.or(inf_set_on_both, second_pred)
    }
}

#[cfg(test)]
mod tests {
    use crate::{fields::fq_target::FqTarget, fields_as_trees::fq2_target_tree::Fq2Target};

    use super::G2AffineTarget;
    use ark_bls12_381::{G2Affine, G2Projective};
    use ark_ec::{AffineRepr, Group};
    use plonky2::{
        field::{goldilocks_field::GoldilocksField, types::Field},
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };
    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_g2affine_point_equality() {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let rand_gen = G2Affine::generator();
        let _rand_iden = G2Affine::identity();

        let const_one = Fq2Target::one(&mut builder);
        let rand_gen_x = Fq2Target {
            c0: FqTarget::constant(&mut builder, rand_gen.x().unwrap().c0),
            c1: FqTarget::constant(&mut builder, rand_gen.x().unwrap().c1),
        };
        let rand_gen_x_1 = rand_gen_x.add(&mut builder, &const_one);
        let rand_gen_y = Fq2Target {
            c0: FqTarget::constant(&mut builder, rand_gen.y().unwrap().c0),
            c1: FqTarget::constant(&mut builder, rand_gen.y().unwrap().c1),
        };
        let rand_gen_y_1 = rand_gen_y.add(&mut builder, &const_one);

        let a: G2AffineTarget<F, D> = G2AffineTarget {
            x: rand_gen_x.clone(),
            y: rand_gen_y.clone(),
            infinity: builder._false(),
        };

        let b: G2AffineTarget<F, D> = G2AffineTarget {
            x: rand_gen_x,
            y: rand_gen_y.clone(),
            infinity: builder._false(),
        };
        let case_1 = a.is_point_equal_to(&mut builder, &b);

        let b: G2AffineTarget<F, D> = G2AffineTarget {
            x: rand_gen_x_1.clone(),
            y: rand_gen_y_1.clone(),
            infinity: builder._false(),
        };
        let case_2 = a.is_point_equal_to(&mut builder, &b);

        let b: G2AffineTarget<F, D> = G2AffineTarget {
            x: rand_gen_x_1.clone(),
            y: rand_gen_y_1,
            infinity: builder._true(),
        };
        let case_3 = a.is_point_equal_to(&mut builder, &b);

        let a: G2AffineTarget<F, D> = G2AffineTarget {
            x: rand_gen_x_1,
            y: rand_gen_y,
            infinity: builder._true(),
        };
        let case_4 = a.is_point_equal_to(&mut builder, &b);

        let mut pw = PartialWitness::new();
        pw.set_target(case_1.target, F::ONE);
        pw.set_target(case_2.target, F::ZERO);
        pw.set_target(case_3.target, F::ZERO);
        pw.set_target(case_4.target, F::ONE);
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_g2projective_point_equality() {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let rand_gen = G2Projective::generator();

        let const_one = Fq2Target::one(&mut builder);
        let rand_gen_x = Fq2Target {
            c0: FqTarget::constant(&mut builder, rand_gen.x.c0),
            c1: FqTarget::constant(&mut builder, rand_gen.x.c1),
        };
        let rand_gen_x_1 = rand_gen_x.add(&mut builder, &const_one);
        let rand_gen_y = Fq2Target {
            c0: FqTarget::constant(&mut builder, rand_gen.y.c0),
            c1: FqTarget::constant(&mut builder, rand_gen.y.c1),
        };
        let rand_gen_y_1 = rand_gen_y.add(&mut builder, &const_one);

        let a: G2AffineTarget<F, D> = G2AffineTarget {
            x: rand_gen_x.clone(),
            y: rand_gen_y.clone(),
            infinity: builder._false(),
        };

        let b: G2AffineTarget<F, D> = G2AffineTarget {
            x: rand_gen_x,
            y: rand_gen_y.clone(),
            infinity: builder._false(),
        };
        let case_1 = a.is_point_equal_to(&mut builder, &b);

        let b: G2AffineTarget<F, D> = G2AffineTarget {
            x: rand_gen_x_1.clone(),
            y: rand_gen_y_1.clone(),
            infinity: builder._false(),
        };
        let case_2 = a.is_point_equal_to(&mut builder, &b);

        let b: G2AffineTarget<F, D> = G2AffineTarget {
            x: rand_gen_x_1.clone(),
            y: rand_gen_y_1,
            infinity: builder._true(),
        };
        let case_3 = a.is_point_equal_to(&mut builder, &b);

        let a: G2AffineTarget<F, D> = G2AffineTarget {
            x: rand_gen_x_1,
            y: rand_gen_y,
            infinity: builder._true(),
        };
        let case_4 = a.is_point_equal_to(&mut builder, &b);

        let mut pw = PartialWitness::new();
        pw.set_target(case_1.target, F::ONE);
        pw.set_target(case_2.target, F::ZERO);
        pw.set_target(case_3.target, F::ZERO);
        pw.set_target(case_4.target, F::ONE);
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }
}
