use ark_bls12_381::{Fq12, Fq2, G1Affine, G2Affine, G2Projective};
use ark_ff::Field;
use ark_std::One;

use crate::utils::constants::{BLS_X, BLS_X_IS_NEGATIVE};

#[derive(Copy, Clone, Debug)]
pub struct MillerLoopResult(pub(crate) Fq12);

impl Default for MillerLoopResult {
    fn default() -> Self {
        MillerLoopResult(Fq12::one())
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

// Adaptation of Algorithm 26, https://eprint.iacr.org/2010/354.pdf
fn _point_doubling_and_line_evaluation(r: &mut G2Projective) -> (Fq2, Fq2, Fq2) {
    let tmp0 = r.x.square(); // check again -> Fq2 square
    let tmp1 = r.y.square();
    let tmp2 = tmp1.square();
    let tmp3 = (tmp1 + r.x).square() - tmp0 - tmp2;
    let tmp3 = tmp3 + tmp3;
    let tmp4 = tmp0 + tmp0 + tmp0;
    let tmp6 = r.x + tmp4;
    let tmp5 = tmp4.square();
    let zsquared = r.z.square();
    r.x = tmp5 - tmp3 - tmp3;
    r.z = (r.z + r.y).square() - tmp1 - zsquared;
    r.y = (tmp3 - r.x) * tmp4;
    let tmp2 = tmp2 + tmp2;
    let tmp2 = tmp2 + tmp2;
    let tmp2 = tmp2 + tmp2;
    r.y -= tmp2;
    let tmp3 = tmp4 * zsquared;
    let tmp3 = tmp3 + tmp3;
    let tmp3 = -tmp3;
    let tmp6 = tmp6.square() - tmp0 - tmp5;
    let tmp1 = tmp1 + tmp1;
    let tmp1 = tmp1 + tmp1;
    let tmp6 = tmp6 - tmp1;
    let tmp0 = r.z * zsquared;
    let tmp0 = tmp0 + tmp0;

    (tmp0, tmp3, tmp6)
}

// Adaptation of Algorithm 27, https://eprint.iacr.org/2010/354.pdf
fn _point_addition_and_line_evaluation(r: &mut G2Projective, q: &G2Affine) -> (Fq2, Fq2, Fq2) {
    let zsquared = r.z.square();
    let ysquared = q.y.square();
    let t0 = zsquared * q.x;
    let t1 = ((q.y + r.z).square() - ysquared - zsquared) * zsquared;
    let t2 = t0 - r.x;
    let t3 = t2.square();
    let t4 = t3 + t3;
    let t4 = t4 + t4;
    let t5 = t4 * t2;
    let t6 = t1 - r.y - r.y;
    let t9 = t6 * q.x;
    let t7 = t4 * r.x;
    r.x = t6.square() - t5 - t7 - t7;
    r.z = (r.z + t2).square() - zsquared - t3;
    let t10 = q.y + r.z;
    let t8 = (t7 - r.x) * t6;
    let t0 = r.y * t5;
    let t0 = t0 + t0;
    r.y = t8 - t0;
    let t10 = t10.square() - ysquared;
    let ztsquared = r.z.square();
    let t10 = t10 - ztsquared;
    let t9 = t9 + t9 - t10;
    let t10 = r.z + r.z;
    let t6 = -t6;
    let t1 = t6 + t6;

    (t10, t1, t9)
}

fn miller_loop<D: MillerLoopDriver>(driver: &mut D) -> D::Output {
    #[warn(unused_assignments)]
    let mut f = D::one();

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

        f = D::square_output(f);
    }

    f = driver.point_doubling_and_line_evaluation(f);

    if BLS_X_IS_NEGATIVE {
        f = D::conjugate(f);
    }

    f
}

// pub fn mul_by_014(
//     x: &mut Fq12,
//     c0: &Fp2<Fp2Config<P>>,
//     c1: &Fp2<Fp2Config<P>>,
//     c4: &Fp2<Fp2Config<P>>,
// ) -> Fq12 {
//     let mut aa = x.c0;
//     aa.mul_by_01(c0, c1);
//     let mut bb = x.c1;
//     bb.mul_by_1(c4);
//     let mut o = *c1;
//     o.add_assign(c4);
//     x.c1.add_assign(&x.c0);
//     x.c1.mul_by_01(c0, &o);
//     x.c1.sub_assign(&aa);
//     x.c1.sub_assign(&bb);
//     x.c0 = bb;
//     Fp12Config::mul_fp6_by_nonresidue_in_place(&mut x.c0);
//     x.c0.add_assign(&aa)
// }

// fn ell(f: Fq12, coeffs: &(Fq2, Fq2, Fq2), p: &G1Affine) -> Fq12 {
//     let mut c0 = coeffs.0;
//     let mut c1 = coeffs.1;

//     c0.c0 *= p.y; // maybe fix
//     c0.c1 *= p.y; // maybe fix

//     c1.c0 *= p.x; // maybe fix
//     c1.c1 *= p.x; // maybe fix

//     let mut p = f.clone();

//     mul_by_014(&mut p, &coeffs.2, &c1, &c0)
// }

pub fn multi_miller_loop(terms: &[(&G1Affine, &G2Affine)]) -> MillerLoopResult {
    struct Adder<'a, 'b, 'c> {
        terms: &'c [(&'a G1Affine, &'b G2Affine)],
        index: usize,
    }

    impl<'a, 'b, 'c> MillerLoopDriver for Adder<'a, 'b, 'c> {
        type Output = Fq12;

        fn point_doubling_and_line_evaluation(&mut self, f: Self::Output) -> Self::Output {
            let _index = self.index;

            for _term in self.terms {
                //     let either_identity = term.0.is_identity() | term.1.infinity;

                // let new_f = ell(f, &term.1.coeffs[index], term.0);
                //     f = Fp12::conditional_select(&new_f, &f, either_identity);
            }
            self.index += 1;

            f
        }

        fn point_addition_and_line_evaluation(&mut self, f: Self::Output) -> Self::Output {
            let _index = self.index;
            for _term in self.terms {
                //     let either_identity = term.0.is_identity() | term.1.infinity;

                //     let new_f = ell(f, &term.1.coeffs[index], term.0);
                //     f = Fp12::conditional_select(&new_f, &f, either_identity);
            }
            self.index += 1;

            f
        }

        fn square_output(f: Self::Output) -> Self::Output {
            f.square() //Fq2 squaring
        }

        fn conjugate(f: Self::Output) -> Self::Output {
            let mut p = f.clone();
            let x = p.conjugate_in_place();
            let y: Self::Output = (*x).into();

            y
        }

        fn one() -> Self::Output {
            Fq12::one()
        }
    }

    let mut adder = Adder { terms, index: 0 };

    let tmp = miller_loop(&mut adder);

    MillerLoopResult(tmp)
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{G1Affine, G2Affine};
    use ark_std::rand;
    use ark_std::UniformRand;
}
