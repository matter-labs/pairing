use super::fq::{Fq, FROBENIUS_COEFF_FQ2_C1, NON_RESIDUE};
use ff::{Field, SqrtField};
use ff::LegendreSymbol::{ Zero, QuadraticResidue, QuadraticNonResidue };
use rand::{Rand, Rng};

use std::cmp::Ordering;

/// An element of Fq2, represented by c0 + c1 * u.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Fq2 {
    pub c0: Fq,
    pub c1: Fq,
}

impl ::std::fmt::Display for Fq2 {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fq2({} + {} * u)", self.c0, self.c1)
    }
}

/// `Fq2` elements are ordered lexicographically.
impl Ord for Fq2 {
    #[inline(always)]
    fn cmp(&self, other: &Fq2) -> Ordering {
        match self.c1.cmp(&other.c1) {
            Ordering::Greater => Ordering::Greater,
            Ordering::Less => Ordering::Less,
            Ordering::Equal => self.c0.cmp(&other.c0),
        }
    }
}

impl PartialOrd for Fq2 {
    #[inline(always)]
    fn partial_cmp(&self, other: &Fq2) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Fq2 {
    /// Multiply this element by the cubic and quadratic nonresidue 1 + u.
    #[inline(always)]
    pub fn mul_by_nonresidue(&mut self) {
        // From libff for Fq2 fields that are extended to Fp2^2
        use std::mem::swap;
        swap(&mut self.c0, &mut self.c1);
        self.c0.mul_assign(&NON_RESIDUE);
    }

    /// Norm of Fq2 as extension field in i over Fq
    #[inline(always)]
    pub fn mul_assign_by_fp(&mut self, f: &Fq) {
        self.c0.mul_assign(f);
        self.c1.mul_assign(f);
    }

    /// Norm of Fq2 as extension field in i over Fq
    #[inline(always)]
    pub fn norm(&self) -> Fq {
        let mut t0 = self.c0;
        t0.square();
        let mut t1 = self.c1;
        t1.square();
        t1.mul_assign(&NON_RESIDUE);
        t0.sub_assign(&t1);
        t0
    }
}

impl Rand for Fq2 {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        Fq2 {
            c0: rng.gen(),
            c1: rng.gen(),
        }
    }
}

impl Field for Fq2 {
    #[inline(always)]
    fn zero() -> Self {
        Fq2 {
            c0: Fq::zero(),
            c1: Fq::zero(),
        }
    }

    #[inline(always)]
    fn one() -> Self {
        Fq2 {
            c0: Fq::one(),
            c1: Fq::zero(),
        }
    }

    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero()
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
        bb.mul_assign(&NON_RESIDUE);
        self.c0.add_assign(&bb);
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
        bb.mul_assign(&NON_RESIDUE);
        self.c0.add_assign(&bb);
    }

    #[inline(always)]
    fn inverse(&self) -> Option<Self> {
        let mut t0 = self.c0;
        t0.square();
        let mut t1 = self.c1;
        t1.square();
        t1.mul_assign(&NON_RESIDUE);
        t0.sub_assign(&t1);
        t0.inverse().map(|t1| {
            let mut tmp = Fq2 {
                c0: self.c0,
                c1: self.c1,
            };
            tmp.c0.mul_assign(&t1);
            tmp.c1.mul_assign(&t1);
            tmp.c1.negate();

            tmp
        })
    }

    #[inline(always)]
    fn frobenius_map(&mut self, power: usize) {
        self.c1.mul_assign(&FROBENIUS_COEFF_FQ2_C1[power % 2]);
    }
}

impl SqrtField for Fq2 {

    #[inline(always)]
    fn legendre(&self) -> ::ff::LegendreSymbol {
        self.norm().legendre()
    }

    #[inline(always)]
    fn sqrt(&self) -> Option<Self> {
        if self.c1.is_zero() {
            return self.c0.sqrt().map(|c0| Self{c0: c0, c1: Fq::zero()});
        }
        match self.legendre() {
            // Square root based on the complex method. See
            // https://eprint.iacr.org/2012/685.pdf (page 15, algorithm 8)
            Zero => Some(*self),
            QuadraticNonResidue => None,
            QuadraticResidue => {
                let mut two_inv = Fq::one();
                two_inv.double();
                two_inv = two_inv.inverse().expect("Two should always have an inverse");

                let alpha = self.norm().sqrt().expect("We are in the QR case, the norm should have a square root");
                //let mut delta = (alpha + &self.c0) * &two_inv;
                let mut delta = self.c0;
                delta.add_assign(&alpha);
                delta.mul_assign(&two_inv);
                if delta.legendre() == QuadraticNonResidue {
                    delta.sub_assign(&alpha);
                }

                let c0 = delta.sqrt().expect("Delta must have a square root");
                let c0_inv = c0.inverse().expect("c0 must have an inverse");

                let mut c1 = self.c1;
                c1.mul_assign(&two_inv);
                c1.mul_assign(&c0_inv);
                Some(Fq2{c0: c0, c1: c1})
            },
        }
    }
}

#[test]
fn test_fq2_ordering() {
    let mut a = Fq2 {
        c0: Fq::zero(),
        c1: Fq::zero(),
    };

    let mut b = a.clone();

    assert!(a.cmp(&b) == Ordering::Equal);
    b.c0.add_assign(&Fq::one());
    assert!(a.cmp(&b) == Ordering::Less);
    a.c0.add_assign(&Fq::one());
    assert!(a.cmp(&b) == Ordering::Equal);
    b.c1.add_assign(&Fq::one());
    assert!(a.cmp(&b) == Ordering::Less);
    a.c0.add_assign(&Fq::one());
    assert!(a.cmp(&b) == Ordering::Less);
    a.c1.add_assign(&Fq::one());
    assert!(a.cmp(&b) == Ordering::Greater);
    b.c0.add_assign(&Fq::one());
    assert!(a.cmp(&b) == Ordering::Equal);
}

#[test]
fn test_fq2_basics() {
    assert_eq!(
        Fq2 {
            c0: Fq::zero(),
            c1: Fq::zero(),
        },
        Fq2::zero()
    );
    assert_eq!(
        Fq2 {
            c0: Fq::one(),
            c1: Fq::zero(),
        },
        Fq2::one()
    );
    assert!(Fq2::zero().is_zero());
    assert!(!Fq2::one().is_zero());
    assert!(!Fq2 {
        c0: Fq::zero(),
        c1: Fq::one(),
    }
    .is_zero());
}

#[cfg(test)]
use rand::{SeedableRng, XorShiftRng};

#[test]
fn fq2_frobenius_map_test() {
    let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
    for _ in 1..100 {
        let a = Fq2::rand(&mut rng);
        let mut b = a;
        for i in 1..3 {
            println!("{}", i);
            let mut c = a;
            c.frobenius_map(i);
            b.frobenius_map(1);
            assert_eq!(b, c);
        }
        assert_eq!(a, b);
    }
}

#[test]
fn test_fq2_legendre() {
    use ff::LegendreSymbol::*;

    assert_eq!(Zero, Fq2::zero().legendre());
    // i^2 = -1
    let mut m1 = Fq2::one();
    m1.negate();
    assert_eq!(QuadraticResidue, m1.legendre());
    m1.mul_by_nonresidue();
    assert_eq!(QuadraticNonResidue, m1.legendre());
}

#[test]
fn fq2_field_tests() {
    use ff::PrimeField;

    crate::tests::field::random_field_tests::<Fq2>();
    crate::tests::field::random_sqrt_tests::<Fq2>();
    crate::tests::field::random_frobenius_tests::<Fq2, _>(super::fq::Fq::char(), 13);
}

