use ark_bls12_381::{Fq, Fq12, Fq2, Fq6, G1Projective, G2Projective};
use ark_std::{One, Zero};
use num_bigint::BigInt;

use crate::global_constants::PSEUDO_BINARY_ENCODING;

#[allow(non_snake_case)]
fn optimized_line_function(Q: (G2Projective, G2Projective), P: G1Projective) -> (Fq12, Fq12) {
    let zero = Fq2::zero();
    let (x1, y1, z1) = (Q.0.x, Q.0.y, Q.0.z);
    let (x2, y2, z2) = (Q.1.x, Q.1.y, Q.1.z);
    let (xp, yp, zp) = (P.x, P.y, P.z);

    let mut lambda_numerator = y2 * z1 - y1 * z2;
    let mut lambda_denominator = x2 * z1 - x1 * z2;
    if lambda_denominator != zero {
        (
            Fq12::new(
                Fq6::new(
                    lambda_numerator
                        * (Fq2::new(xp, Fq::zero()) * z1 - x1 * Fq2::new(zp, Fq::zero()))
                        - lambda_denominator
                            * (Fq2::new(yp, Fq::zero()) * z1 - y1 * Fq2::new(zp, Fq::zero())),
                    Fq2::zero(),
                    Fq2::zero(),
                ),
                Fq6::zero(),
            ),
            Fq12::new(
                Fq6::new(
                    lambda_denominator * Fq2::new(zp, Fq::zero()) * z1,
                    Fq2::zero(),
                    Fq2::zero(),
                ),
                Fq6::zero(),
            ),
        )
    } else if lambda_numerator == zero {
        lambda_numerator = Fq2::from(3) * x1 * x1;
        lambda_denominator = Fq2::from(2) * y1 * z1;
        (
            Fq12::new(
                Fq6::new(
                    lambda_numerator
                        * (Fq2::new(xp, Fq::zero()) * z1 - x1 * Fq2::new(zp, Fq::zero()))
                        - lambda_denominator
                            * (Fq2::new(yp, Fq::zero()) * z1 - y1 * Fq2::new(zp, Fq::zero())),
                    Fq2::zero(),
                    Fq2::zero(),
                ),
                Fq6::zero(),
            ),
            Fq12::new(
                Fq6::new(
                    lambda_denominator * Fq2::new(zp, Fq::zero()) * z1,
                    Fq2::zero(),
                    Fq2::zero(),
                ),
                Fq6::zero(),
            ),
        )
    } else {
        (
            Fq12::new(
                Fq6::new(
                    Fq2::new(xp, Fq::zero()) * z1 - x1 * Fq2::new(zp, Fq::zero()),
                    Fq2::zero(),
                    Fq2::zero(),
                ),
                Fq6::zero(),
            ),
            Fq12::new(
                Fq6::new(z1 * Fq2::new(zp, Fq::zero()), Fq2::zero(), Fq2::zero()),
                Fq6::zero(),
            ),
        )
    }
}

#[allow(non_snake_case)]
pub fn optimized_miller_loop(P: G1Projective, Q: G2Projective) -> Fq12 {
    let mut R = Q;
    let mut f_num = Fq12::one();
    let mut f_den = Fq12::one();
    let _x = (f_num + f_den + f_den) * f_den;
    //println!("x is: {:?}", x);
    let mut f = Fq12::one();

    for v in PSEUDO_BINARY_ENCODING[..].iter() {
        let (_n, _d) = optimized_line_function((R, R), P);
        f_num = f_num * f_num * _n;
        f_den = f_den * f_den * _d;
        R = (R + R).into();
        if *v == 1 {
            let (_n, _d) = optimized_line_function((R, Q), P);
            f_num = f_num * _n;
            f_den = f_den * _d;
            R = (R + Q).into();
        }
    }

    f = f_num / f_den;

    let base_field_str = "4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787";
    let BASE_FIELD =
        BigInt::parse_bytes(base_field_str.as_bytes(), 10).expect("Invalid number format");

    // SCALAR_FIELD plays the role of the curve order.
    let SCALAR_FIELD = BigInt::parse_bytes(
        b"52435875175126190479447740508185965837690552500527637822603658699938581184513",
        10,
    )
    .expect("Invalid modulo format");
    let f_power = (BASE_FIELD.pow(12) - BigInt::one()) / SCALAR_FIELD;

    let mut i = BigInt::zero();
    while &i < &f_power {
        f = f * f;
        i += BigInt::one();
        break;
    }

    println!("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
    println!("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
    println!("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
    f
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{Bls12_381, Fq12, G1Projective, G2Projective};
    use ark_ec::{pairing::Pairing, AffineRepr};
    use ark_std::rand;
    use ark_std::UniformRand;

    use super::optimized_miller_loop;

    #[test]
    fn test() {
        let rng = &mut rand::thread_rng();
        let p1 = G1Projective::rand(rng);
        let q1 = G2Projective::rand(rng);
        let result = optimized_miller_loop(p1, q1);
        println!("result is: {:?}", result);
    }

    // #[test]
    // fn test_miller_loop_comparison() {
    //     let mock_pairing = |p: G1Projective, q: G2Projective| -> Fq12 {
    //         let r0: Fq12 =
    //             Bls12_381::miller_loop(G1Projective::generator(), G2Projective::generator())
    //                 .0
    //                 .into();
    //         let r1: Fq12 =
    //             optimized_miller_loop(G1Projective::generator(), G2Projective::generator()).into();
    //         let r: Fq12 = optimized_miller_loop(p, q);
    //         r * r0 / r1
    //     };

    //     let mut rng = rand::thread_rng();
    //     let p0 = G1Projective::rand(&mut rng);
    //     let p1 = G2Projective::rand(&mut rng);
    //     let result = Bls12_381::miller_loop(p0, p1).0;
    //     let result_optimized_miller_loop: Fq12 = optimized_miller_loop(p0, p1);

    //     let r_native_pairing = mock_pairing(p0, p1);
    //     assert_eq!(result, r_native_pairing);
    // }
}
