extern crate std;

use super::{
    fq::{FROBENIUS_COEFF_FQ4_C1},
    fq2::Fq2,
};

use crate::{
    BitIterator,
    rand::{Rand, Rng},
    ff::Field,
};

use std::mem::swap;

/// An element of Fq4, represented by c0 + c1 * w.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Fq4 {
    pub c0: Fq2,
    pub c1: Fq2,
}

impl ::std::fmt::Display for Fq4 {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fq4({} + {} * w)", self.c0, self.c1)
    }
}

impl Rand for Fq4 {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        Fq4 {
            c0: rng.gen(),
            c1: rng.gen(),
        }
    }
}

impl Fq4 {

    #[inline(always)]
    pub fn conjugate(&mut self) {
        self.c1.negate();
    }

    // When the Fq4 element is known to be an r-th root of 
    // unity, we can use this function instead of squaring
    // TODO: Implement NAF
    #[inline(always)]
    pub fn cyclotomic_exp<S: AsRef<[u64]>>(&self, exp: S) -> Self {
        let mut res = Self::one();
        let mut found_one = false;

        for i in BitIterator::new(exp) {
            if found_one {
                res.cyclotomic_square();
            } else {
                found_one = i;
            }

            if i {
                res.mul_assign(self);
            }
        }

        res
    }

    // When the Fq4 element is known to be an r-th root of 
    // unity, we can use this function instead of squaring
    #[inline(always)]
    pub fn cyclotomic_square(&mut self) {
        swap(&mut self.c0, &mut self.c1);
        self.c1.add_assign(&self.c0);
        self.c1.square();
        self.c0.square();
        self.c1.sub_assign(&self.c0);
        self.c0.mul_by_nonresidue();
        self.c1.sub_assign(&self.c0);
        self.c0.double();
        let one = Fq2::one();
        self.c0.add_assign(&one);
        self.c1.sub_assign(&one);
    }
}

impl Field for Fq4 {
    
    #[inline(always)]
    fn zero() -> Self {
        Fq4 {
            c0: Fq2::zero(),
            c1: Fq2::zero(),
        }
    }

    #[inline(always)]
    fn one() -> Self {
        Fq4 {
            c0: Fq2::one(),
            c1: Fq2::zero(),
        }
    }

    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
    }

    #[inline(always)]
    fn double(&mut self) {
        self.c0.double();
        self.c1.double();
    }

    #[inline(always)]
    fn negate(&mut self) {
        self.c0.negate();
        self.c1.negate();
    }

    #[inline(always)]
    fn add_assign(&mut self, other: &Self) {
        self.c0.add_assign(&other.c0);
        self.c1.add_assign(&other.c1);
    }

    #[inline(always)]
    fn sub_assign(&mut self, other: &Self) {
        self.c0.sub_assign(&other.c0);
        self.c1.sub_assign(&other.c1);
    }

    #[inline(always)]
    fn frobenius_map(&mut self, power: usize) {
        self.c0.frobenius_map(power);
        self.c1.frobenius_map(power);

        self.c1.c0.mul_assign(&FROBENIUS_COEFF_FQ4_C1[power % 4]);
        self.c1.c1.mul_assign(&FROBENIUS_COEFF_FQ4_C1[power % 4]);
    }

    #[inline(always)]
    fn square(&mut self) {
        // Devegili OhEig Scott Dahab
        // --- 
        // Multiplication and Squaring on Pairing-Friendly Fields.pdf; 
        // Section 3 (Karatsuba squaring)
        let mut aa = self.c0;
        aa.square();
        let mut bb = self.c1;
        bb.square();
        self.c1.mul_assign(&self.c0);
        self.c1.double();
        self.c0 = aa;
        bb.mul_by_nonresidue();
        self.c0.add_assign(&bb);
    }

    #[inline(always)]
    fn mul_assign(&mut self, other: &Self) {
        let mut aa = self.c0;
        aa.mul_assign(&other.c0);
        let mut bb = self.c1;
        bb.mul_assign(&other.c1);
        let mut o = other.c0;
        o.add_assign(&other.c1);
        self.c1.add_assign(&self.c0);
        self.c1.mul_assign(&o);
        self.c1.sub_assign(&aa);
        self.c1.sub_assign(&bb);
        self.c0 = aa;
        bb.mul_by_nonresidue();
        self.c0.add_assign(&bb);
    }

    #[inline(always)]
    fn inverse(&self) -> Option<Self> {
        let mut c0s = self.c0;
        c0s.square();
        let mut c1s = self.c1;
        c1s.square();
        c1s.mul_by_nonresidue();
        c0s.sub_assign(&c1s);

        c0s.inverse().map(|t| {
            let mut tmp = Fq4 { c0: t, c1: t };
            tmp.c0.mul_assign(&self.c0);
            tmp.c1.mul_assign(&self.c1);
            tmp.c1.negate();

            tmp
        })
    }
}

#[test]
fn fq4_field_tests() {
    use ff::PrimeField;

    crate::tests::field::random_field_tests::<Fq4>();
    crate::tests::field::random_frobenius_tests::<Fq4, _>(super::fq::Fq::char(), 13);
}
