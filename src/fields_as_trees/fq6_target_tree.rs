use plonky2::{
    field::extension::Extendable, hash::hash_types::RichField, iop::target::BoolTarget,
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_ecdsa::gadgets::nonnative::CircuitBuilderNonNative;

use crate::fields::{bls12_381base::Bls12_381Base, fq_target::FqTarget};

use super::fq2_target_tree::Fq2Target;

#[derive(Clone, Debug)]
pub struct Fq6Target<F: RichField + Extendable<D>, const D: usize> {
    pub c0: Fq2Target<F, D>,
    pub c1: Fq2Target<F, D>,
    pub c2: Fq2Target<F, D>,
}

impl<F: RichField + Extendable<D>, const D: usize> Fq6Target<F, D> {
    pub fn zero(builder: &mut CircuitBuilder<F, D>) -> Self {
        Self {
            c0: Fq2Target::zero(builder),
            c1: Fq2Target::zero(builder),
            c2: Fq2Target::zero(builder),
        }
    }

    pub fn one(builder: &mut CircuitBuilder<F, D>) -> Self {
        Self {
            c0: Fq2Target::one(builder),
            c1: Fq2Target::zero(builder),
            c2: Fq2Target::zero(builder),
        }
    }

    pub fn add(&self, builder: &mut CircuitBuilder<F, D>, rhs: Self) -> Self {
        Self {
            c0: self.c0.add(builder, &rhs.c0),
            c1: self.c1.add(builder, &rhs.c1),
            c2: self.c2.add(builder, &rhs.c2),
        }
    }

    pub fn sub(&self, builder: &mut CircuitBuilder<F, D>, rhs: Self) -> Self {
        Self {
            c0: self.c0.sub(builder, &rhs.c0),
            c1: self.c1.sub(builder, &rhs.c1),
            c2: self.c2.sub(builder, &rhs.c2),
        }
    }

    pub fn neg(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        Self {
            c0: self.c0.neg(builder),
            c1: self.c1.neg(builder),
            c2: self.c2.neg(builder),
        }
    }

    pub fn inv(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let c0 = self.c1.mul(builder, &self.c2);
        let c0 = c0.mul_by_nonresidue(builder);
        let temp = self.c0.square(builder);
        let c0 = temp.sub(builder, &c0);

        let c1 = self.c2.square(builder);
        let c1 = c1.mul_by_nonresidue(builder);
        let temp = self.c0.mul(builder, &self.c1);
        let c1 = c1.sub(builder, &temp);

        let c2 = self.c1.square(builder);
        let temp = self.c0.mul(builder, &self.c2);
        let c2 = c2.sub(builder, &temp);

        let temp = self.c1.mul(builder, &c2);
        let tmp = temp;
        let temp = self.c2.mul(builder, &c1);
        let tmp = tmp.add(builder, &temp);
        let tmp = tmp.mul_by_nonresidue(builder);
        let temp = self.c0.mul(builder, &c0);
        let tmp = tmp.add(builder, &temp);

        let inverted = tmp.inv(builder);

        Self {
            c0: c0.mul(builder, &inverted),
            c1: c1.mul(builder, &inverted),
            c2: c2.mul(builder, &inverted),
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
        let lhs_c2 = &lhs.c2;

        let rhs_c0 = &rhs.c0;
        let rhs_c1 = &rhs.c1;
        let rhs_c2 = &rhs.c2;

        Self {
            c0: Fq2Target::select(builder, &lhs_c0, &rhs_c0, flag),
            c1: Fq2Target::select(builder, &lhs_c1, &rhs_c1, flag),
            c2: Fq2Target::select(builder, &lhs_c2, &rhs_c2, flag),
        }
    }

    pub fn is_equal(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> BoolTarget {
        let self_c0 = &self.c0;
        let self_c1 = &self.c1;
        let self_c2 = &self.c2;

        let rhs_c0 = &rhs.c0;
        let rhs_c1 = &rhs.c1;
        let rhs_c2 = &rhs.c2;

        let r_c0 = self_c0.is_equal(builder, rhs_c0);
        let r_c1 = self_c1.is_equal(builder, rhs_c1);
        let r_c2 = self_c2.is_equal(builder, rhs_c2);

        let temp = builder.and(r_c0, r_c1);
        builder.and(temp, r_c2)
    }

    pub fn frobenius_map(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let c0 = self.c0.frobenius_map(builder);
        let c1 = self.c1.frobenius_map(builder);
        let c2 = self.c2.frobenius_map(builder);

        // c1 = c1 * (u + 1)^((p - 1) / 3)
        let temp = Fq2Target {
            c0: FqTarget::zero(builder),
            c1: FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0xcd03_c9e4_8671_f071,
                    0x5dab_2246_1fcd_a5d2,
                    0x5870_42af_d385_1b95,
                    0x8eb6_0ebe_01ba_cb9e,
                    0x03f9_7d6e_83d0_50d2,
                    0x18f0_2065_5463_8741,
                ]),
            ),
        };
        let c1 = c1.mul(builder, &temp);

        // c2 = c2 * (u + 1)^((2p - 2) / 3)
        let temp = Fq2Target {
            c0: FqTarget::fp_constant(
                builder,
                Bls12_381Base([
                    0x890d_c9e4_8675_45c3,
                    0x2af3_2253_3285_a5d5,
                    0x5088_0866_309b_7e2c,
                    0xa20d_1b8c_7e88_1024,
                    0x14e4_f04f_e2db_9068,
                    0x14e5_6d3f_1564_853a,
                ]),
            ),
            c1: FqTarget::zero(builder),
        };
        let c2 = c2.mul(builder, &temp);

        Self { c0, c1, c2 }
    }

    // Derived from https://github.com/onurinanc/noir-bls-signature/blob/a3d19b69b4cd8698afd8f3ad8ca2a77495c58c0e/src/bls12_381/fp6.nr#L53
    pub fn mul(&self, builder: &mut CircuitBuilder<F, D>, rhs: &Self) -> Self {
        let a_a = self.c0.mul(builder, &rhs.c0);
        let b_b = self.c1.mul(builder, &rhs.c1);
        let c_c = self.c2.mul(builder, &rhs.c2);

        // Construct t1
        let t1 = rhs.c1.clone();
        let t1 = t1.add(builder, &rhs.c2);

        let tmp = self.c1.add(builder, &self.c2);
        let t1 = t1.mul(builder, &tmp);
        let t1 = t1.sub(builder, &b_b);
        let t1 = t1.sub(builder, &c_c);
        let t1 = t1.mul_by_nonresidue(builder);
        let t1 = t1.add(builder, &a_a);

        // Construct t3
        let t3 = rhs.c0.clone();
        let t3 = t3.add(builder, &rhs.c2);

        let tmp = self.c0.add(builder, &self.c2);
        let t3 = t3.mul(builder, &tmp);
        let t3 = t3.sub(builder, &a_a);
        let t3 = t3.add(builder, &b_b);
        let t3 = t3.sub(builder, &c_c);

        // Construct t2
        let t2 = rhs.c0.clone();
        let t2 = t2.add(builder, &rhs.c1);

        let tmp = self.c0.add(builder, &self.c1);
        let t2 = t2.mul(builder, &tmp);
        let t2 = t2.sub(builder, &a_a);
        let t2 = t2.sub(builder, &b_b);
        let c_c_mul_by_nonres = c_c.mul_by_nonresidue(builder);
        let t2 = t2.add(builder, &c_c_mul_by_nonres);

        Self {
            c0: t1,
            c1: t2,
            c2: t3,
        }
    }

    // pub fn mul(&self, builder: &mut CircuitBuilder<F, D>, rhs: Self) -> Self {}

    /// Multiply by quadratic nonresidue v.
    pub fn mul_by_nonresidue(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        // Given a + bv + cv^2, this produces
        //     av + bv^2 + cv^3
        // but because v^3 = u + 1, we have
        //     c(u + 1) + av + v^2

        let c0 = self.c2.mul_by_nonresidue(builder);
        let c1 = self.c0.clone();
        let c2 = self.c1.clone();

        Self { c0, c1, c2 }
    }

    pub fn mul_by_01(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        c0: &Fq2Target<F, D>,
        c1: &Fq2Target<F, D>,
    ) -> Self {
        let a_a = self.c0.mul(builder, &c0);
        let b_b = self.c1.mul(builder, &c1);

        let t1 = self.c2.mul(builder, &c1);
        let t1 = t1.mul_by_nonresidue(builder);
        let t1 = t1.add(builder, &a_a);

        let t2 = c0.add(builder, &c1);
        let temp = self.c0.add(builder, &self.c1);
        let t2 = t2.mul(builder, &temp);
        let t2 = t2.sub(builder, &a_a);
        let t2 = t2.sub(builder, &b_b);

        let t3 = self.c2.mul(builder, c0);
        let t3 = t3.add(builder, &b_b);

        Self {
            c0: t1,
            c1: t2,
            c2: t3,
        }
    }

    pub fn mul_by_1(&self, builder: &mut CircuitBuilder<F, D>, c1: &Fq2Target<F, D>) -> Self {
        let c0 = self.c2.mul(builder, &c1);
        Self {
            c0: c0.mul_by_nonresidue(builder),
            c1: self.c0.mul(builder, &c1),
            c2: self.c1.mul(builder, &c1),
        }
    }

    pub fn square(&self, builder: &mut CircuitBuilder<F, D>) -> Self {
        let s0 = self.c0.square(builder);
        let ab = self.c0.mul(builder, &self.c1);
        let s1 = ab.add(builder, &ab);
        let s2 = self.c0.sub(builder, &self.c1);
        let s2 = s2.add(builder, &self.c2);
        let s2 = s2.square(builder);
        let bc = self.c1.mul(builder, &self.c2);
        let s3 = bc.add(builder, &bc);
        let s4 = self.c2.square(builder);

        let c0 = s3.mul_by_nonresidue(builder);
        let c0 = c0.add(builder, &s0);

        let c1 = s4.mul_by_nonresidue(builder);
        let c1 = c1.add(builder, &s1);

        let c2 = s1.add(builder, &s2);
        let c2 = c2.add(builder, &s3);
        let c2 = c2.sub(builder, &s0);
        let c2 = c2.sub(builder, &s4);

        Self { c0, c1, c2 }
    }

    pub fn connect(builder: &mut CircuitBuilder<F, D>, lhs: &Self, rhs: &Self) {
        builder.connect_nonnative(&lhs.c0.c0.target, &rhs.c0.c0.target);
        builder.connect_nonnative(&lhs.c0.c1.target, &rhs.c0.c1.target);
        builder.connect_nonnative(&lhs.c1.c0.target, &rhs.c1.c0.target);
        builder.connect_nonnative(&lhs.c1.c1.target, &rhs.c1.c1.target);
        builder.connect_nonnative(&lhs.c2.c0.target, &rhs.c2.c0.target);
        builder.connect_nonnative(&lhs.c2.c1.target, &rhs.c2.c1.target);
    }
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::Fq6;
    use ark_ff::{Field, UniformRand};
    use plonky2::{
        field::goldilocks_field::GoldilocksField,
        iop::witness::PartialWitness,
        plonk::{
            circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
            config::PoseidonGoldilocksConfig,
        },
    };

    use crate::{
        fields::{bls12_381base::Bls12_381Base, fq_target::FqTarget},
        fields_as_trees::fq2_target_tree::Fq2Target,
    };

    use super::Fq6Target;

    type F = GoldilocksField;
    type C = PoseidonGoldilocksConfig;
    const D: usize = 2;

    #[test]
    fn test_fq6_mul_circuit() {
        let rng = &mut rand::thread_rng();
        let a = Fq6::rand(rng);
        let b = Fq6::rand(rng);
        let c_expected = a * b;

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let a = Fq6Target {
            c0: Fq2Target {
                c0: FqTarget::constant(&mut builder, a.c0.c0),
                c1: FqTarget::constant(&mut builder, a.c0.c1),
            },
            c1: Fq2Target {
                c0: FqTarget::constant(&mut builder, a.c1.c0),
                c1: FqTarget::constant(&mut builder, a.c1.c1),
            },
            c2: Fq2Target {
                c0: FqTarget::constant(&mut builder, a.c2.c0),
                c1: FqTarget::constant(&mut builder, a.c2.c1),
            },
        };
        let b = Fq6Target {
            c0: Fq2Target {
                c0: FqTarget::constant(&mut builder, b.c0.c0),
                c1: FqTarget::constant(&mut builder, b.c0.c1),
            },
            c1: Fq2Target {
                c0: FqTarget::constant(&mut builder, b.c1.c0),
                c1: FqTarget::constant(&mut builder, b.c1.c1),
            },
            c2: Fq2Target {
                c0: FqTarget::constant(&mut builder, b.c2.c0),
                c1: FqTarget::constant(&mut builder, b.c2.c1),
            },
        };

        let c_t = a.mul(&mut builder, &b);
        let c_expected_t = Fq6Target {
            c0: Fq2Target {
                c0: FqTarget::constant(&mut builder, c_expected.c0.c0),
                c1: FqTarget::constant(&mut builder, c_expected.c0.c1),
            },
            c1: Fq2Target {
                c0: FqTarget::constant(&mut builder, c_expected.c1.c0),
                c1: FqTarget::constant(&mut builder, c_expected.c1.c1),
            },
            c2: Fq2Target {
                c0: FqTarget::constant(&mut builder, c_expected.c2.c0),
                c1: FqTarget::constant(&mut builder, c_expected.c2.c1),
            },
        };

        Fq6Target::connect(&mut builder, &c_expected_t, &c_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_fq6_arithmetic() {
        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let a = Fq6Target {
            c0: Fq2Target {
                c0: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0x47f9_cb98_b1b8_2d58,
                        0x5fe9_11eb_a3aa_1d9d,
                        0x96bf_1b5f_4dd8_1db3,
                        0x8100_d27c_c925_9f5b,
                        0xafa2_0b96_7464_0eab,
                        0x09bb_cea7_d8d9_497d,
                    ]),
                ),
                c1: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0x0303_cb98_b166_2daa,
                        0xd931_10aa_0a62_1d5a,
                        0xbfa9_820c_5be4_a468,
                        0x0ba3_643e_cb05_a348,
                        0xdc35_34bb_1f1c_25a6,
                        0x06c3_05bb_19c0_e1c1,
                    ]),
                ),
            },
            c1: Fq2Target {
                c0: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0x46f9_cb98_b162_d858,
                        0x0be9_109c_f7aa_1d57,
                        0xc791_bc55_fece_41d2,
                        0xf84c_5770_4e38_5ec2,
                        0xcb49_c1d9_c010_e60f,
                        0x0acd_b8e1_58bf_e3c8,
                    ]),
                ),
                c1: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0x8aef_cb98_b15f_8306,
                        0x3ea1_108f_e4f2_1d54,
                        0xcf79_f69f_a1b7_df3b,
                        0xe4f5_4aa1_d16b_1a3c,
                        0xba5e_4ef8_6105_a679,
                        0x0ed8_6c07_97be_e5cf,
                    ]),
                ),
            },
            c2: Fq2Target {
                c0: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0xcee5_cb98_b15c_2db4,
                        0x7159_1082_d23a_1d51,
                        0xd762_30e9_44a1_7ca4,
                        0xd19e_3dd3_549d_d5b6,
                        0xa972_dc17_01fa_66e3,
                        0x12e3_1f2d_d6bd_e7d6,
                    ]),
                ),
                c1: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0xad2a_cb98_b173_2d9d,
                        0x2cfd_10dd_0696_1d64,
                        0x0739_6b86_c6ef_24e8,
                        0xbd76_e2fd_b1bf_c820,
                        0x6afe_a7f6_de94_d0d5,
                        0x1099_4b0c_5744_c040,
                    ]),
                ),
            },
        };

        let b = Fq6Target {
            c0: Fq2Target {
                c0: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0xf120_cb98_b16f_d84b,
                        0x5fb5_10cf_f3de_1d61,
                        0x0f21_a5d0_69d8_c251,
                        0xaa1f_d62f_34f2_839a,
                        0x5a13_3515_7f89_913f,
                        0x14a3_fe32_9643_c247,
                    ]),
                ),
                c1: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0x3516_cb98_b16c_82f9,
                        0x926d_10c2_e126_1d5f,
                        0x1709_e01a_0cc2_5fba,
                        0x96c8_c960_b825_3f14,
                        0x4927_c234_207e_51a9,
                        0x18ae_b158_d542_c44e,
                    ]),
                ),
            },
            c1: Fq2Target {
                c0: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0xbf0d_cb98_b169_82fc,
                        0xa679_10b7_1d1a_1d5c,
                        0xb7c1_47c2_b8fb_06ff,
                        0x1efa_710d_47d2_e7ce,
                        0xed20_a79c_7e27_653c,
                        0x02b8_5294_dac1_dfba,
                    ]),
                ),
                c1: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0x9d52_cb98_b180_82e5,
                        0x621d_1111_5176_1d6f,
                        0xe798_8260_3b48_af43,
                        0x0ad3_1637_a4f4_da37,
                        0xaeac_737c_5ac1_cf2e,
                        0x006e_7e73_5b48_b824,
                    ]),
                ),
            },
            c2: Fq2Target {
                c0: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0xe148_cb98_b17d_2d93,
                        0x94d5_1104_3ebe_1d6c,
                        0xef80_bca9_de32_4cac,
                        0xf77c_0969_2827_95b1,
                        0x9dc1_009a_fbb6_8f97,
                        0x0479_3199_9a47_ba2b,
                    ]),
                ),
                c1: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0x253e_cb98_b179_d841,
                        0xc78d_10f7_2c06_1d6a,
                        0xf768_f6f3_811b_ea15,
                        0xe424_fc9a_ab5a_512b,
                        0x8cd5_8db9_9cab_5001,
                        0x0883_e4bf_d946_bc32,
                    ]),
                ),
            },
        };

        let c = Fq6Target {
            c0: Fq2Target {
                c0: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0x6934_cb98_b176_82ef,
                        0xfa45_10ea_194e_1d67,
                        0xff51_313d_2405_877e,
                        0xd0cd_efcc_2e8d_0ca5,
                        0x7bea_1ad8_3da0_106b,
                        0x0c8e_97e6_1845_be39,
                    ]),
                ),
                c1: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0x4779_cb98_b18d_82d8,
                        0xb5e9_1144_4daa_1d7a,
                        0x2f28_6bda_a653_2fc2,
                        0xbca6_94f6_8bae_ff0f,
                        0x3d75_e6b8_1a3a_7a5d,
                        0x0a44_c3c4_98cc_96a3,
                    ]),
                ),
            },
            c1: Fq2Target {
                c0: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0x8b6f_cb98_b18a_2d86,
                        0xe8a1_1137_3af2_1d77,
                        0x3710_a624_493c_cd2b,
                        0xa94f_8828_0ee1_ba89,
                        0x2c8a_73d6_bb2f_3ac7,
                        0x0e4f_76ea_d7cb_98aa,
                    ]),
                ),
                c1: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0xcf65_cb98_b186_d834,
                        0x1b59_112a_283a_1d74,
                        0x3ef8_e06d_ec26_6a95,
                        0x95f8_7b59_9214_7603,
                        0x1b9f_00f5_5c23_fb31,
                        0x125a_2a11_16ca_9ab1,
                    ]),
                ),
            },
            c2: Fq2Target {
                c0: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0x135b_cb98_b183_82e2,
                        0x4e11_111d_1582_1d72,
                        0x46e1_1ab7_8f10_07fe,
                        0x82a1_6e8b_1547_317d,
                        0x0ab3_8e13_fd18_bb9b,
                        0x1664_dd37_55c9_9cb8,
                    ]),
                ),
                c1: FqTarget::fp_constant(
                    &mut builder,
                    Bls12_381Base([
                        0xce65_cb98_b131_8334,
                        0xc759_0fdb_7c3a_1d2e,
                        0x6fcb_8164_9d1c_8eb3,
                        0x0d44_004d_1727_356a,
                        0x3746_b738_a7d0_d296,
                        0x136c_144a_96b1_34fc,
                    ]),
                ),
            },
        };

        let a_squared = a.square(&mut builder);
        let a_mul_a = a.mul(&mut builder, &a);

        let b_squared = b.square(&mut builder);
        let b_mul_b = b.mul(&mut builder, &b);

        let c_squared = c.square(&mut builder);
        let c_mul_c = c.mul(&mut builder, &c);

        Fq6Target::connect(&mut builder, &a_squared, &a_mul_a);
        Fq6Target::connect(&mut builder, &b_squared, &b_mul_b);
        Fq6Target::connect(&mut builder, &c_squared, &c_mul_c);

        let a_plus_b = a.add(&mut builder, b.clone());
        let a_plus_b_mul_c_squared = a_plus_b.mul(&mut builder, &c_squared);

        let c_mul_c_mul_a = c_mul_c.mul(&mut builder, &a);
        let c_mul_c_mul_b = c_mul_c.mul(&mut builder, &b);
        let c_c_a_plus_c_c_b = c_mul_c_mul_a.add(&mut builder, c_mul_c_mul_b);

        Fq6Target::connect(&mut builder, &c_c_a_plus_c_c_b, &a_plus_b_mul_c_squared);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }

    #[test]
    fn test_fq6_inversion_circuit() {
        let rng = &mut rand::thread_rng();
        let x: Fq6 = Fq6::rand(rng);
        let inv_x_expected = x.inverse().unwrap();

        let config = CircuitConfig::pairing_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x_t = Fq6Target {
            c0: Fq2Target {
                c0: FqTarget::constant(&mut builder, x.c0.c0),
                c1: FqTarget::constant(&mut builder, x.c0.c1),
            },
            c1: Fq2Target {
                c0: FqTarget::constant(&mut builder, x.c1.c0),
                c1: FqTarget::constant(&mut builder, x.c1.c1),
            },
            c2: Fq2Target {
                c0: FqTarget::constant(&mut builder, x.c2.c0),
                c1: FqTarget::constant(&mut builder, x.c2.c1),
            },
        };
        let inv_x_t = x_t.inv(&mut builder);
        let inv_x_expected_t = Fq6Target {
            c0: Fq2Target {
                c0: FqTarget::constant(&mut builder, inv_x_expected.c0.c0),
                c1: FqTarget::constant(&mut builder, inv_x_expected.c0.c1),
            },
            c1: Fq2Target {
                c0: FqTarget::constant(&mut builder, inv_x_expected.c1.c0),
                c1: FqTarget::constant(&mut builder, inv_x_expected.c1.c1),
            },
            c2: Fq2Target {
                c0: FqTarget::constant(&mut builder, inv_x_expected.c2.c0),
                c1: FqTarget::constant(&mut builder, inv_x_expected.c2.c1),
            },
        };

        Fq6Target::connect(&mut builder, &inv_x_t, &inv_x_expected_t);

        let pw = PartialWitness::new();
        let data = builder.build::<C>();
        dbg!(data.common.degree_bits());
        let _proof = data.prove(pw);
    }
}
