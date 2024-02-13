use std::ops::Add;

use ark_bls12_381::{Fq, Fq2, Fq6};
use ark_std::Zero;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MyFq6 {
    pub coeffs: [Fq; 6],
}

// impl from trait
impl From<Fq6> for MyFq6 {
    fn from(fq6: Fq6) -> Self {
        let c0: Fq2 = fq6.c0;
        let c1: Fq2 = fq6.c1;
        let c2: Fq2 = fq6.c2;

        let c00 = c0.c0; // w^0 u^0
        let c01 = c0.c1; // w^0 u^1
        let c10 = c1.c0; // w^1 u^0
        let c11 = c1.c1; // w^1 u^1
        let c20 = c2.c0; // w^2 u^0
        let c21 = c2.c1; // w^2 u^1

        let coeffs = [c00, c10, c20, c01, c11, c21];
        Self { coeffs }
    }
}

// from myfq6 to fq6
impl From<MyFq6> for Fq6 {
    fn from(fq6: MyFq6) -> Self {
        let coeffs = fq6.coeffs;

        let c00 = coeffs[0]; // w^0 u^0
        let c01 = coeffs[3]; // w^0 u^1
        let c10 = coeffs[1]; // w^1 u^0
        let c11 = coeffs[4]; // w^1 u^1
        let c20 = coeffs[2]; // w^2 u^0
        let c21 = coeffs[5]; // w^2 u^1

        Fq6::new(Fq2::new(c00, c01), Fq2::new(c10, c11), Fq2::new(c20, c21))
    }
}

impl Add for MyFq6 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut coeffs = [Fq::zero(); 6];
        for i in 0..6 {
            coeffs[i] = self.coeffs[i] + rhs.coeffs[i];
        }
        Self { coeffs }
    }
}
