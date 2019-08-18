use super::{
    fq::{FROBENIUS_COEFF_FQ6_C1},
    fq3::Fq3,
};

use crate::{
    BitIterator,
    rand::{Rand, Rng},
    ff::Field,
};

/// An element of Fq6, represented by c0 + c1 * w.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Fq6 {
    pub c0: Fq3,
    pub c1: Fq3,
}

impl ::std::fmt::Display for Fq6 {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fq6({} + {} * w)", self.c0, self.c1)
    }
}

impl Rand for Fq6 {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        Fq6 {
            c0: rng.gen(),
            c1: rng.gen(),
        }
    }
}

impl Fq6 {
    #[inline(always)]
    pub fn conjugate(&mut self) {
        self.c1.negate();
    }

    #[inline(always)]
    pub fn cyclotomic_exp<S: AsRef<[u64]>>(&self, exp: S) -> Self {
        let mut res = Self::one();
        let mut found_one = false;

        for i in BitIterator::new(exp) {
            if found_one {
                res.square();
            } else {
                found_one = i;
            }

            if i {
                res.mul_assign(self);
            }
        }

        res
    }
}

impl Field for Fq6 {
    #[inline(always)]
    fn zero() -> Self {
        Fq6 {
            c0: Fq3::zero(),
            c1: Fq3::zero(),
        }
    }

    #[inline(always)]
    fn one() -> Self {
        Fq6 {
            c0: Fq3::one(),
            c1: Fq3::zero(),
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

        self.c1.mul_assign_by_fp(&FROBENIUS_COEFF_FQ6_C1[power % 6]);
    }

    #[inline(always)]
    fn square(&mut self) {
        let mut ab = self.c0;
        ab.mul_assign(&self.c1);
        let mut c0c1 = self.c0;
        c0c1.add_assign(&self.c1);
        let mut c0 = self.c1;
        c0.mul_by_nonresidue();
        c0.add_assign(&self.c0);
        c0.mul_assign(&c0c1);
        c0.sub_assign(&ab);
        self.c1 = ab;
        self.c1.add_assign(&ab);
        ab.mul_by_nonresidue();
        c0.sub_assign(&ab);
        self.c0 = c0;
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
        self.c0 = bb;
        self.c0.mul_by_nonresidue();
        self.c0.add_assign(&aa);
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
            let mut tmp = Fq6 { c0: t, c1: t };
            tmp.c0.mul_assign(&self.c0);
            tmp.c1.mul_assign(&self.c1);
            tmp.c1.negate();

            tmp
        })
    }
}

#[test]
fn fq6_field_tests() {
    use ff::PrimeField;

    crate::tests::field::random_field_tests::<Fq6>();
    crate::tests::field::random_frobenius_tests::<Fq6, _>(super::fq::Fq::char(), 13);
}