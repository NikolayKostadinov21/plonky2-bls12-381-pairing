use ark_bls12_381::Fq12;
use ark_ff::Field;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::target::BoolTarget,
    plonk::{circuit_builder::CircuitBuilder, circuit_data::CircuitConfig},
};

use crate::{
    curves::{
        g1_curve_target::G1AffineTarget,
        g2_curve_target::{G2AffineTarget, G2ProjectiveTarget},
    },
    fields::{fq12_target::Fq12Target, fq2_target::Fq2Target},
    utils::constants::{BLS_X, BLS_X_IS_NEGATIVE},
};

#[derive(Clone, Debug)]
pub struct MillerLoopResult<F: RichField + Extendable<D>, const D: usize>(pub Fq12Target<F, D>);

#[derive(Clone, Debug)]
pub struct G2PreparedTarget<F: RichField + Extendable<D>, const D: usize> {
    pub infinity: BoolTarget,
    pub coeffs: Vec<(Fq2Target<F, D>, Fq2Target<F, D>, Fq2Target<F, D>)>,
}

impl<F: RichField + Extendable<D>, const D: usize> From<G2AffineTarget<F, D>>
    for G2PreparedTarget<F, D>
{
    fn from(q: G2AffineTarget<F, D>) -> Self {
        struct Adder<A: RichField + Extendable<B>, const B: usize> {
            cur: G2ProjectiveTarget<A, B>,
            base: G2AffineTarget<A, B>,
            coeffs: Vec<(Fq2Target<A, B>, Fq2Target<A, B>, Fq2Target<A, B>)>,
        }

        impl<A: RichField + Extendable<B>, const B: usize> MillerLoopDriver for Adder<A, B> {
            type Output = ();

            fn point_doubling_and_line_evaluation(&mut self, _: Self::Output) -> Self::Output {
                let config = CircuitConfig::pairing_config();
                let mut builder = CircuitBuilder::<A, B>::new(config);
                let coeffs = point_doubling_and_line_evaluation(&mut builder, &mut self.cur);
                self.coeffs.push(coeffs);
            }
            fn point_addition_and_line_evaluation(&mut self, _: Self::Output) -> Self::Output {
                let config = CircuitConfig::pairing_config();
                let mut builder = CircuitBuilder::<A, B>::new(config);
                let coeffs =
                    point_addition_and_line_evaluation(&mut builder, &mut self.cur, &mut self.base);
                self.coeffs.push(coeffs);
            }
            fn square_output(_: Self::Output) -> Self::Output {}
            fn conjugate(_: Self::Output) -> Self::Output {}
            fn one() -> Self::Output {}
        }

        let is_identity = q.infinity;
        let q = G2AffineTarget::conditional_select(&q, &G2AffineTarget::identity(), is_identity);
        let mut adder = Adder {
            cur: G2ProjectiveTarget::from(q.clone()),
            base: q.clone(),
            coeffs: Vec::with_capacity(68),
        };

        miller_loop::<F, D, _>(&mut adder);

        assert_eq!(adder.coeffs.len(), 68);

        G2PreparedTarget {
            infinity: is_identity,
            coeffs: adder.coeffs,
        }
    }
}

trait MillerLoopDriver {
    type Output;

    fn point_doubling_and_line_evaluation(&mut self, f: Self::Output) -> Self::Output;
    fn point_addition_and_line_evaluation(&mut self, f: Self::Output) -> Self::Output;
    fn square_output(f: Self::Output) -> Self::Output;
    fn conjugate(f: Self::Output) -> Self::Output;
    fn one() -> Self::Output;
}

pub fn multi_miller_loop<F: RichField + Extendable<D>, const D: usize>(
    terms: &[(&G1AffineTarget<F, D>, &G2PreparedTarget<F, D>)],
) -> MillerLoopResult<F, D> {
    struct Adder<'a, 'b, 'c, A: RichField + Extendable<B>, const B: usize> {
        terms: &'c [(&'a G1AffineTarget<A, B>, &'b G2PreparedTarget<A, { B }>)],
        index: usize,
    }

    impl<'a, 'b, 'c, A: RichField + Extendable<B>, const B: usize> MillerLoopDriver
        for Adder<'a, 'b, 'c, A, B>
    {
        type Output = Fq12Target<A, B>;
        fn point_doubling_and_line_evaluation(&mut self, mut f: Self::Output) -> Self::Output {
            let config = CircuitConfig::pairing_config();
            let mut builder = CircuitBuilder::<A, B>::new(config);
            let index = self.index;
            for term in self.terms {
                let either_identity = builder.or(term.0.is_identity(), term.1.infinity);

                let new_f = ell(&mut builder, f.clone(), &term.1.coeffs[index], term.0);
                f = Fq12Target::select(&mut builder, &new_f, &f, &either_identity);
            }
            f
        }

        fn point_addition_and_line_evaluation(&mut self, mut f: Self::Output) -> Self::Output {
            let config = CircuitConfig::pairing_config();
            let mut builder = CircuitBuilder::<A, B>::new(config);
            let index = self.index;
            for term in self.terms {
                let either_identity = builder.or(term.0.is_identity(), term.1.infinity);

                let new_f = ell(&mut builder, f.clone(), &term.1.coeffs[index], term.0);
                f = Fq12Target::select(&mut builder, &new_f, &f, &either_identity);
            }
            f
        }

        fn square_output(f: Self::Output) -> Self::Output {
            let config = CircuitConfig::pairing_config();
            let mut builder = CircuitBuilder::<A, B>::new(config);
            f.square(&mut builder)
        }

        fn conjugate(f: Self::Output) -> Self::Output {
            let config = CircuitConfig::pairing_config();
            let mut builder = CircuitBuilder::<A, B>::new(config);
            f.confugate(&mut builder)
        }

        fn one() -> Self::Output {
            let config = CircuitConfig::pairing_config();
            let mut builder = CircuitBuilder::<A, B>::new(config);
            Fq12Target::constant(&mut builder, Fq12::ONE)
        }
    }

    let mut adder = Adder { terms, index: 0 };

    let tmp = miller_loop::<F, D, _>(&mut adder);

    MillerLoopResult(tmp)
}

// Adaptation of Algorithm 26, https://eprint.iacr.org/2010/354.pdf
fn point_doubling_and_line_evaluation<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    r: &mut G2ProjectiveTarget<F, D>,
) -> (Fq2Target<F, D>, Fq2Target<F, D>, Fq2Target<F, D>) {
    let tmp0 = r.x.square(builder);
    let tmp1 = r.y.square(builder);
    let tmp2 = tmp1.square(builder);
    let tmp3 = tmp1.add(builder, &r.x);
    let tmp3 = tmp3.square(builder);
    let tmp3 = tmp3.sub(builder, &tmp0);
    let tmp3 = tmp3.sub(builder, &tmp2);
    let tmp3 = tmp3.add(builder, &tmp3);
    let tmp0_double = tmp0.add(builder, &tmp0);
    let tmp4 = tmp0.add(builder, &tmp0_double);
    let tmp6 = r.x.add(builder, &tmp4);
    let tmp5 = tmp4.square(builder);
    let zsquared = r.z.square(builder);
    r.x = tmp5.sub(builder, &tmp3);
    r.x = r.x.sub(builder, &tmp3);
    let rz_ry = r.z.add(builder, &r.y);
    r.z = rz_ry.square(builder);
    r.z = r.z.sub(builder, &tmp1);
    r.z = r.z.sub(builder, &zsquared);
    let tmp3_min_rx = tmp3.sub(builder, &r.x);
    r.y = tmp3_min_rx.mul(builder, &tmp4);
    let tmp2 = tmp2.add(builder, &tmp2);
    let tmp2 = tmp2.add(builder, &tmp2);
    let tmp2 = tmp2.add(builder, &tmp2);
    r.y = r.y.sub(builder, &tmp2);
    let tmp3 = tmp4.mul(builder, &zsquared);
    let tmp3 = tmp3.add(builder, &tmp3);
    let tmp3 = tmp3.conjugate(builder);
    let tmp6 = tmp6.square(builder);
    let tmp6 = tmp6.sub(builder, &tmp0);
    let tmp6 = tmp6.sub(builder, &tmp5);
    let tmp1 = tmp1.add(builder, &tmp1);
    let tmp1 = tmp1.add(builder, &tmp1);
    let tmp6 = tmp6.sub(builder, &tmp1);
    let tmp0 = r.z.mul(builder, &zsquared);
    let tmp0 = tmp0.add(builder, &tmp0);

    (tmp0, tmp3, tmp6)
}

// Adaptation of Algorithm 27, https://eprint.iacr.org/2010/354.pdf
fn point_addition_and_line_evaluation<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    r: &mut G2ProjectiveTarget<F, D>,
    q: &G2AffineTarget<F, D>,
) -> (Fq2Target<F, D>, Fq2Target<F, D>, Fq2Target<F, D>) {
    let zsquared = r.z.square(builder);
    let ysquared = q.y.square(builder);
    let t0 = zsquared.mul(builder, &q.x);
    let qy_add_rz = q.y.add(builder, &r.z);
    let qy_rz_squared = qy_add_rz.square(builder);
    let qy_rz_squared = qy_rz_squared.sub(builder, &ysquared);
    let qy_rz_squared = qy_rz_squared.sub(builder, &zsquared);
    let t1 = qy_rz_squared.mul(builder, &zsquared);
    let t2 = t0.sub(builder, &r.x);
    let t3 = t2.square(builder);
    let t4 = t3.add(builder, &t3);
    let t4 = t4.add(builder, &t4);
    let t5 = t4.mul(builder, &t2);
    let t6 = t1.sub(builder, &r.y);
    let t6 = t6.sub(builder, &r.y);
    let t9 = t6.mul(builder, &q.x);
    let t7 = t4.mul(builder, &r.x);
    r.x = t6.square(builder);
    r.x = r.x.sub(builder, &t5);
    r.x = r.x.sub(builder, &t7);
    r.x = r.x.sub(builder, &t7);
    let rz_add_t2 = r.z.add(builder, &t2);
    r.z = rz_add_t2.square(builder);
    r.z = r.z.sub(builder, &zsquared);
    r.z = r.z.sub(builder, &t3);
    let t10 = q.y.add(builder, &r.z);
    let t7_sub_rx = t7.sub(builder, &r.x);
    let t8 = t7_sub_rx.mul(builder, &t6);
    let t0 = r.y.mul(builder, &t5);
    let t0 = t0.add(builder, &t0);
    r.y = t8.sub(builder, &t0);
    let t10 = t10.square(builder);
    let t10 = t10.sub(builder, &ysquared);
    let ztsquared = r.z.square(builder);
    let t10 = t10.sub(builder, &ztsquared);
    let t9 = t9.add(builder, &t9);
    let t9 = t9.sub(builder, &t10);
    let t10 = r.z.add(builder, &r.z);
    let t6 = t6.conjugate(builder);
    let t1 = t6.add(builder, &t6);

    (t10, t1, t9)
}

fn miller_loop<F: RichField + Extendable<D>, const D: usize, M: MillerLoopDriver>(
    driver: &mut M,
) -> M::Output {
    let mut f = M::one();
    let mut found_one = false;

    for i in (0..64).rev().map(|b| (((BLS_X >> 1) >> b) & 1) == 1) {
        if !found_one {
            found_one = i;
            continue;
        }

        f = driver.point_doubling_and_line_evaluation(f);

        if i {
            f = driver.point_addition_and_line_evaluation(f);
        }

        f = M::square_output(f);
    }

    f = driver.point_doubling_and_line_evaluation(f);

    if BLS_X_IS_NEGATIVE {
        f = M::conjugate(f);
    }

    f
}

fn ell<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    f: Fq12Target<F, D>,
    coeffs: &(Fq2Target<F, D>, Fq2Target<F, D>, Fq2Target<F, D>),
    p: &G1AffineTarget<F, D>,
) -> Fq12Target<F, D> {
    let c0 = &coeffs.0;
    let c1 = &coeffs.1;

    c0.coeffs[0].mul(builder, &p.y);
    c0.coeffs[1].mul(builder, &p.y);

    c1.coeffs[0].mul(builder, &p.x);
    c1.coeffs[1].mul(builder, &p.x);

    f.mul_by_014(builder, &coeffs.2, &c1, &c0)
}

// #[cfg(test)]
// mod tests {
//     use ark_bls12_381::Fq12;
//     use num::One;
//     use plonky2::{
//         field::goldilocks_field::GoldilocksField,
//         iop::witness::PartialWitness,
//         plonk::{
//             circuit_builder::CircuitBuilder, circuit_data::CircuitConfig,
//             config::PoseidonGoldilocksConfig,
//         },
//     };

//     use crate::{
//         curves::{g1_curve_target::G1AffineTarget, g2_curve_target::G2AffineTarget},
//         fields::fq12_target::Fq12Target,
//         miller_loop_target::multi_miller_loop,
//     };
//     type F = GoldilocksField;
//     type C = PoseidonGoldilocksConfig;
//     const D: usize = 2;

//     #[test]
//     fn miller_loop_result() {
//         let config = CircuitConfig::pairing_config();
//         let mut builder = CircuitBuilder::<F, D>::new(config);
//         let test_fq12_one = Fq12Target::constant(&mut builder, Fq12::one());
//         let result_mml = multi_miller_loop(&[(
//             &G1AffineTarget::<F, D>::identity(),
//             &G2AffineTarget::<F, D>::generator().into(),
//         )])
//         .0;

//         println!("====================================================================");
//         println!("result_mml is: {:?}", result_mml);
//         println!("====================================================================");

//         Fq12Target::connect(&mut builder, &result_mml, &test_fq12_one);

//         let pw = PartialWitness::new();
//         let data = builder.build::<C>();
//         dbg!(data.common.degree_bits());
//         let _proof = data.prove(pw);
//     }
// }
