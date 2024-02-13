use ark_bls12_381::{Fq, G1Affine};
use ark_ec::AffineRepr;
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

    pub fn experimental_generator() -> Self {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let g1_generator = G1Affine::generator();

        Self {
            x: FqTarget::constant(&mut builder, *g1_generator.x().unwrap()),
            y: FqTarget::constant(&mut builder, *g1_generator.y().unwrap()),
            infinity: builder._false(),
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
    use crate::fields::fq_target::FqTarget;

    use super::G1AffineTarget;
    use ark_bls12_381::{Fq, G1Affine};
    use ark_ec::AffineRepr;
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
    fn test_g1affine_point_equality() {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let rand_gen = G1Affine::generator();
        let _rand_iden = G1Affine::identity();

        let const_one = FqTarget::constant(&mut builder, Fq::from(1));
        let rand_gen_x = FqTarget::constant(&mut builder, *rand_gen.x().unwrap());
        let rand_gen_x_1 = rand_gen_x.add(&mut builder, &const_one);
        let rand_gen_y = FqTarget::constant(&mut builder, *rand_gen.y().unwrap());
        let rand_gen_y_1 = rand_gen_y.add(&mut builder, &const_one);

        let a: G1AffineTarget<F, D> = G1AffineTarget {
            x: rand_gen_x.clone(),
            y: rand_gen_y.clone(),
            infinity: builder._false(),
        };

        let b: G1AffineTarget<F, D> = G1AffineTarget {
            x: rand_gen_x,
            y: rand_gen_y.clone(),
            infinity: builder._false(),
        };
        let case_1 = a.is_point_equal_to(&mut builder, &b);

        let b: G1AffineTarget<F, D> = G1AffineTarget {
            x: rand_gen_x_1.clone(),
            y: rand_gen_y_1.clone(),
            infinity: builder._false(),
        };
        let case_2 = a.is_point_equal_to(&mut builder, &b);

        let b: G1AffineTarget<F, D> = G1AffineTarget {
            x: rand_gen_x_1.clone(),
            y: rand_gen_y_1,
            infinity: builder._true(),
        };
        let case_3 = a.is_point_equal_to(&mut builder, &b);

        let a: G1AffineTarget<F, D> = G1AffineTarget {
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
