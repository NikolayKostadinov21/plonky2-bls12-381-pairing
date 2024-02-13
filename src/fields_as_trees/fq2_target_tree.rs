use ark_bls12_381::Fq;
use ark_std::{One, Zero};
use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField, iop::target::BoolTarget,
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_ecdsa::gadgets::nonnative::CircuitBuilderNonNative;

use crate::fields::fq_target::FqTarget;

#[derive(Clone, Debug)]
pub struct Fq2Target<F: RichField + Extendable<D>, const D: usize> {
    pub c0: FqTarget<F, D>,
    pub c1: FqTarget<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> Fq2Target<F, D> {
    pub fn zero(builder: &mut CircuitBuilder<F, D>) -> Self {
        let zero = FqTarget::constant(builder, Fq::zero());
        Self {
            c0: zero.clone(),
            c1: zero,
        }
    }

    pub fn one(builder: &mut CircuitBuilder<F, D>) -> Self {
        let zero = FqTarget::constant(builder, Fq::zero());
        let one = FqTarget::constant(builder, Fq::one());
        Self { c0: one, c1: zero }
    }

    pub fn add(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> Self {
        Self {
            c0: self.c0.add(builder, &rhs.c0),
            c1: self.c1.add(builder, &rhs.c1),
        }
    }

    pub fn sub(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> Self {
        Self {
            c0: self.c0.sub(builder, &rhs.c0),
            c1: self.c1.sub(builder, &rhs.c1),
        }
    }

    pub fn neg(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        Self {
            c0: self.c0.neg(builder),
            c1: self.c1.neg(builder),
        }
    }

    // Derived https://github.com/onurinanc/noir-bls-signature/blob/a3d19b69b4cd8698afd8f3ad8ca2a77495c58c0e/src/bls12_381/fp2.nr#L122
    pub fn invert(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let t0 = self.c0.mul(builder, &self.c0);
        let t1 = self.c1.mul(builder, &self.c1);
        let t0 = t0.add(builder, &t1);
        let t1 = t0.inv(builder);
        let c0 = t1.mul(builder, &self.c0);
        let c1 = self.c1.mul(builder, &t1);
        let c1 = c1.neg(builder);

        Self { c0, c1 }
    }

    pub fn inv(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let c0_squared = self.c0.mul(builder, &self.c0);
        let c1_squared = self.c1.mul(builder, &self.c1);

        let inverted = &c0_squared.add(builder, &c1_squared);
        let inverted = inverted.inv(builder);
        let neg_inverted = inverted.neg(builder);

        Self {
            c0: self.c0.mul(builder, &inverted),
            c1: self.c1.mul(builder, &neg_inverted),
        }
    }

    pub fn square(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let c0 = &self.c0;
        let c1 = &self.c1;
        let a = c0.add(builder, &c1);
        let b = c0.sub(builder, &c1);
        let c = c0.add(builder, &c0);

        let c0 = a.mul(builder, &b);
        let c1 = c.mul(builder, &c1);

        Self { c0, c1 }
    }

    pub fn frobenius_map(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        self.conjugate(builder)
    }

    pub fn mul(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> Self {
        let a0 = &self.c0;
        let a1 = &self.c1;

        let b0 = &rhs.c0;
        let b1 = &rhs.c1;

        let a0_b0 = a0.mul(builder, &b0);
        let a1_b1 = a1.mul(builder, &b1);

        let c0 = a0_b0.sub(builder, &a1_b1);

        let a0_b1 = a0.mul(builder, &b1);
        let a1_b0 = a1.mul(builder, &b0);

        let c1 = a0_b1.add(builder, &a1_b0);

        Self { c0, c1 }
    }

    pub fn conjugate(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        Self {
            c0: self.c0.clone(),
            c1: self.c1.neg(builder),
        }
    }

    pub fn is_equal(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> BoolTarget {
        let self_c0 = &self.c0;
        let self_c1 = &self.c1;

        let rhs_c0 = &rhs.c0;
        let rhs_c1 = &rhs.c1;

        let r_c0 = self_c0.is_equal(builder, rhs_c0);
        let r_c1 = self_c1.is_equal(builder, rhs_c1);

        builder.and(r_c0, r_c1)
    }

    pub fn mul_by_nonresidue(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        Self {
            c0: self.c0.sub(builder, &self.c1),
            c1: self.c0.add(builder, &self.c1),
        }
    }

    pub fn select(
        builder: &mut CircuitBuilder<F, D>,
        lhs: &Self,
        rhs: &Self,
        flag: &BoolTarget,
    ) -> Self {
        let lhs_c0 = &lhs.c0;
        let lhs_c1 = &lhs.c1;
        let rhs_c0 = &rhs.c0;
        let rhs_c1 = &rhs.c1;

        Self {
            c0: FqTarget::select(builder, &lhs_c0, &rhs_c0, flag),
            c1: FqTarget::select(builder, &lhs_c1, &rhs_c1, flag),
        }
    }

    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        builder.connect_nonnative(&lhs.c0.target, &rhs.c0.target);
        builder.connect_nonnative(&lhs.c1.target, &rhs.c1.target);
    }
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::Fq2;
    use ark_ff::{Field, UniformRand};
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use crate::fields::{bls12_381base::Bls12_381Base, fq_target::FqTarget};

    use super::Fq2Target;

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_multiplication() {
        let rng = &mut rand::thread_rng();
        let a = Fq2::rand(rng);
        let b = Fq2::rand(rng);
        let c_expected = a * b;

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a = Fq2Target {
            c0: FqTarget::constant(&mut builder, a.c0),
            c1: FqTarget::constant(&mut builder, a.c1),
        };
        let b = Fq2Target {
            c0: FqTarget::constant(&mut builder, b.c0),
            c1: FqTarget::constant(&mut builder, b.c1),
        };

        let c_t = a.mul(&mut builder, &b);
        let c_expected_t = Fq2Target {
            c0: FqTarget::constant(&mut builder, c_expected.c0),
            c1: FqTarget::constant(&mut builder, c_expected.c1),
        };

        Fq2Target::connect(&mut builder, &c_expected_t, &c_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_addition() {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let a = Fq2Target {
            c0: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0xc9a2_1831_63ee_70d4,
                    0xbc37_70a7_196b_5c91,
                    0xa247_f8c1_304c_5f44,
                    0xb01f_c2a3_726c_80b5,
                    0xe1d2_93e5_bbd9_19c9,
                    0x04b7_8e80_020e_f2ca,
                ]),
            ),
            c1: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0x952e_a446_0462_618f,
                    0x238d_5edd_f025_c62f,
                    0xf6c9_4b01_2ea9_2e72,
                    0x03ce_24ea_c1c9_3808,
                    0x0559_50f9_45da_483c,
                    0x010a_768d_0df4_eabc,
                ]),
            ),
        };

        let b = Fq2Target {
            c0: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0xa1e0_9175_a4d2_c1fe,
                    0x8b33_acfc_204e_ff12,
                    0xe244_15a1_1b45_6e42,
                    0x61d9_96b1_b6ee_1936,
                    0x1164_dbe8_667c_853c,
                    0x0788_557a_cc7d_9c79,
                ]),
            ),
            c1: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0xda6a_87cc_6f48_fa36,
                    0x0fc7_b488_277c_1903,
                    0x9445_ac4a_dc44_8187,
                    0x0261_6d5b_c909_9209,
                    0xdbed_4677_2db5_8d48,
                    0x11b9_4d50_76c7_b7b1,
                ]),
            ),
        };

        let c = Fq2Target {
            c0: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0x6b82_a9a7_08c1_32d2,
                    0x476b_1da3_39ba_5ba4,
                    0x848c_0e62_4b91_cd87,
                    0x11f9_5955_295a_99ec,
                    0xf337_6fce_2255_9f06,
                    0x0c3f_e3fa_ce8c_8f43,
                ]),
            ),
            c1: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0x6f99_2c12_73ab_5bc5,
                    0x3355_1366_17a1_df33,
                    0x8b0e_f74c_0aed_aff9,
                    0x062f_9246_8ad2_ca12,
                    0xe146_9770_738f_d584,
                    0x12c3_c3dd_84bc_a26d,
                ]),
            ),
        };

        let a_plus_b = a.add(&mut builder, &b);
        Fq2Target::connect(&mut builder, &c, &a_plus_b);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_inversion() {
        let rng = &mut rand::thread_rng();
        let x: Fq2 = Fq2::rand(rng);
        let inv_x_expected = x.inverse().unwrap();

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x_t = Fq2Target {
            c0: FqTarget::constant(&mut builder, x.c0),
            c1: FqTarget::constant(&mut builder, x.c1),
        };
        let inv_x_t = x_t.inv(&mut builder);
        let inv_x_expected_t = Fq2Target {
            c0: FqTarget::constant(&mut builder, inv_x_expected.c0),
            c1: FqTarget::constant(&mut builder, inv_x_expected.c1),
        };

        Fq2Target::connect(&mut builder, &inv_x_t, &inv_x_expected_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_subtraction() {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let a = Fq2Target {
            c0: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0xc9a2_1831_63ee_70d4,
                    0xbc37_70a7_196b_5c91,
                    0xa247_f8c1_304c_5f44,
                    0xb01f_c2a3_726c_80b5,
                    0xe1d2_93e5_bbd9_19c9,
                    0x04b7_8e80_020e_f2ca,
                ]),
            ),
            c1: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0x952e_a446_0462_618f,
                    0x238d_5edd_f025_c62f,
                    0xf6c9_4b01_2ea9_2e72,
                    0x03ce_24ea_c1c9_3808,
                    0x0559_50f9_45da_483c,
                    0x010a_768d_0df4_eabc,
                ]),
            ),
        };
        let b = Fq2Target {
            c0: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0xa1e0_9175_a4d2_c1fe,
                    0x8b33_acfc_204e_ff12,
                    0xe244_15a1_1b45_6e42,
                    0x61d9_96b1_b6ee_1936,
                    0x1164_dbe8_667c_853c,
                    0x0788_557a_cc7d_9c79,
                ]),
            ),
            c1: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0xda6a_87cc_6f48_fa36,
                    0x0fc7_b488_277c_1903,
                    0x9445_ac4a_dc44_8187,
                    0x0261_6d5b_c909_9209,
                    0xdbed_4677_2db5_8d48,
                    0x11b9_4d50_76c7_b7b1,
                ]),
            ),
        };
        let c = Fq2Target {
            c0: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0xe1c0_86bb_bf1b_5981,
                    0x4faf_c3a9_aa70_5d7e,
                    0x2734_b5c1_0bb7_e726,
                    0xb2bd_7776_af03_7a3e,
                    0x1b89_5fb3_98a8_4164,
                    0x1730_4aef_6f11_3cec,
                ]),
            ),
            c1: FqTarget::fp_constant(
                &mut builder,
                Bls12_381Base([
                    0x74c3_1c79_9519_1204,
                    0x3271_aa54_79fd_ad2b,
                    0xc9b4_7157_4915_a30f,
                    0x65e4_0313_ec44_b8be,
                    0x7487_b238_5b70_67cb,
                    0x0952_3b26_d0ad_19a4,
                ]),
            ),
        };

        let a_sub_b = a.sub(&mut builder, &b);
        Fq2Target::connect(&mut builder, &c, &a_sub_b);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }
}
