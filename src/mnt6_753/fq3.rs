use super::fq::{Fq, FQ3_NQR_T, FQ3_T_MINUS_1, FROBENIUS_COEFF_FQ3_C1, FROBENIUS_COEFF_FQ3_C2};
use ff::{Field, SqrtField };
use rand::{Rand, Rng};
use ff::LegendreSymbol::{ QuadraticNonResidue, QuadraticResidue, Zero };

use std::cmp::Ordering;

/// An element of Fq3, represented by c0 + c1 * v + c2 * v^(2).
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Fq3 {
    pub c0: Fq,
    pub c1: Fq,
    pub c2: Fq,
}

impl ::std::fmt::Display for Fq3 {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "Fq3({} + {} * v, {} * v^2)", self.c0, self.c1, self.c2)
    }
}

/// `Fq3` elements are ordered lexicographically.
impl Ord for Fq3 {
    #[inline(always)]
    fn cmp(&self, other: &Fq3) -> Ordering {
        match self.c2.cmp(&other.c2) {
            Ordering::Greater => Ordering::Greater,
            Ordering::Less => Ordering::Less,
            Ordering::Equal => match self.c1.cmp(&other.c1) {
                Ordering::Greater => Ordering::Greater,
                Ordering::Less => Ordering::Less,
                Ordering::Equal => self.c0.cmp(&other.c0),
            },
        }
    }
}

impl PartialOrd for Fq3 {
    #[inline(always)]
    fn partial_cmp(&self, other: &Fq3) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Fq3 {

    #[inline(always)]
    pub fn mul_by_nonresidue(&mut self) {
        use std::mem::swap;
        swap(&mut self.c0, &mut self.c1); // (a, b, c) -> (b, a, c)
        swap(&mut self.c0, &mut self.c2); // (b, a, c) -> (c, a, b)
        self.c0.mul_by_nonresidue();
    }

    #[inline(always)]
    pub fn mul_assign_by_fp(&mut self, other: &Fq) {
        self.c0.mul_assign(&other);
        self.c1.mul_assign(&other);
        self.c2.mul_assign(&other);
    }

    /// Norm of Fq3 as extension field in i over Fq
    #[inline(always)]
    pub fn norm(&self) -> Fq {
        // From ZEXE's code
        let mut self_to_p2 = *self;
        self_to_p2.frobenius_map(2);
        let mut self_to_p = *self;
        self_to_p.frobenius_map(1);

        self_to_p.mul_assign(&self_to_p2); 
        self_to_p.mul_assign(&self);
        
        assert!(self_to_p.c1.is_zero() && self_to_p.c2.is_zero());
        self_to_p.c0
    }
}

impl Rand for Fq3 {
    fn rand<R: Rng>(rng: &mut R) -> Self {
        Fq3 {
            c0: rng.gen(),
            c1: rng.gen(),
            c2: rng.gen(),
        }
    }
}

impl Field for Fq3 {
    #[inline(always)]
    fn zero() -> Self {
        Fq3 {
            c0: Fq::zero(),
            c1: Fq::zero(),
            c2: Fq::zero(),
        }
    }

    #[inline(always)]
    fn one() -> Self {
        Fq3 {
            c0: Fq::one(),
            c1: Fq::zero(),
            c2: Fq::zero(),
        }
    }

    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.c0.is_zero() && self.c1.is_zero() && self.c2.is_zero()
    }

    #[inline(always)]
    fn double(&mut self) {
        self.c0.double();
        self.c1.double();
        self.c2.double();
    }

    #[inline(always)]
    fn negate(&mut self) {
        self.c0.negate();
        self.c1.negate();
        self.c2.negate();
    }

    #[inline(always)]
    fn add_assign(&mut self, other: &Self) {
        self.c0.add_assign(&other.c0);
        self.c1.add_assign(&other.c1);
        self.c2.add_assign(&other.c2);
    }

    #[inline(always)]
    fn sub_assign(&mut self, other: &Self) {
        self.c0.sub_assign(&other.c0);
        self.c1.sub_assign(&other.c1);
        self.c2.sub_assign(&other.c2);
    }

    #[inline(always)]
    fn frobenius_map(&mut self, power: usize) {
        self.c1.mul_assign(&FROBENIUS_COEFF_FQ3_C1[power % 3]);
        self.c2.mul_assign(&FROBENIUS_COEFF_FQ3_C2[power % 3]);
    }

    /* from https://github.com/scipr-lab/libff/blob/f2067162520f91438b44e71a2cab2362f1c3cab4/libff/algebra/fields/fp3.tcc#L100
    Devegili OhEig Scott Dahab --- Multiplication and Squaring on Pairing-Friendly Fields.pdf; Section 4 (CH-SQR2) */
    #[inline(always)]
    fn square(&mut self) {
        let mut s0 = self.c0;
        s0.square();
        let mut ab = self.c0;
        ab.mul_assign(&self.c1);
        let mut s1 = ab;
        s1.double();
        let mut s2 = self.c0;
        s2.sub_assign(&self.c1);
        s2.add_assign(&self.c2);
        s2.square();
        let mut bc = self.c1;
        bc.mul_assign(&self.c2);
        let mut s3 = bc;
        s3.double();
        let mut s4 = self.c2;
        s4.square();

        // return c0 = s0 + non_residue * s3,
        self.c0 = s3;
        self.c0.mul_by_nonresidue();
        self.c0.add_assign(&s0);

        // return c1 = s1 + non_residue * s4,
        self.c1 = s4;
        self.c1.mul_by_nonresidue();
        self.c1.add_assign(&s1);

        // return c2 = s1 + s2 + s3 - s0 - s4);
        self.c2 = s1;
        self.c2.add_assign(&s2);
        self.c2.add_assign(&s3);
        self.c2.sub_assign(&s0);
        self.c2.sub_assign(&s4);
    }

    #[inline(always)]
    fn mul_assign(&mut self, other: &Self) {
        let mut a_a = self.c0;
        let mut b_b = self.c1;
        let mut c_c = self.c2;
        a_a.mul_assign(&other.c0);
        b_b.mul_assign(&other.c1);
        c_c.mul_assign(&other.c2);

        // aA + non_residue * ( (b + c) * (B + C) - bB - cC )
        let mut t1 = other.c1;
        t1.add_assign(&other.c2);
        {
            let mut tmp = self.c1;
            tmp.add_assign(&self.c2);

            t1.mul_assign(&tmp);
            t1.sub_assign(&b_b);
            t1.sub_assign(&c_c);
            t1.mul_by_nonresidue();
            t1.add_assign(&a_a);
        }

        // (a + c) * (A + C) - aA + bB - cC
        let mut t3 = other.c0;
        t3.add_assign(&other.c2);
        {
            let mut tmp = self.c0;
            tmp.add_assign(&self.c2);

            t3.mul_assign(&tmp);
            t3.sub_assign(&a_a);
            t3.add_assign(&b_b);
            t3.sub_assign(&c_c);
        }

        // (a + b) * (A + B) - aA - bB + non_residue * cC
        let mut t2 = other.c0;
        t2.add_assign(&other.c1);
        {
            let mut tmp = self.c0;
            tmp.add_assign(&self.c1);

            t2.mul_assign(&tmp);
            t2.sub_assign(&a_a);
            t2.sub_assign(&b_b);
            c_c.mul_by_nonresidue();
            t2.add_assign(&c_c);
        }

        self.c0 = t1;
        self.c1 = t2;
        self.c2 = t3;
    }

    // from https://github.com/scipr-lab/libff/blob/f2067162520f91438b44e71a2cab2362f1c3cab4/libff/algebra/fields/fp3.tcc#L119
    /* From "High-Speed Software Implementation of the Optimal Ate Pairing over Barreto-Naehrig Curves"; Algorithm 17 */
    #[inline(always)]
    fn inverse(&self) -> Option<Self> {
        let mut t0 = self.c0;
        t0.square();
        let mut t1 = self.c1;
        t1.square();
        let mut t2 = self.c2;
        t2.square();
        let mut t3 = self.c0;
        t3.mul_assign(&self.c1);
        let mut t4 = self.c0;
        t4.mul_assign(&self.c2);
        let mut t5 = self.c1;
        t5.mul_assign(&self.c2);
        // c0 = t0 - non_residue * t5
        t5.mul_by_nonresidue();
        t0.sub_assign(&t5);
        // c1 = non_residue * t2 - t3
        t2.mul_by_nonresidue();
        t2.sub_assign(&t3);
        // c2 = t1 - t4
        t1.sub_assign(&t4);

        // (a * c0 + non_residue * (c * c1 + b * c2)).inverse()
        // a * c0 (= t0)
        let mut ac = self.c0;
        ac.mul_assign(&t0);
        // b * c2 (= t1)
        let mut bc = self.c1;
        bc.mul_assign(&t1);
        // c * c1 + b * c2
        let mut cc = self.c2;
        cc.mul_assign(&t2);
        cc.add_assign(&bc);
        cc.mul_by_nonresidue();
        cc.add_assign(&ac);

        match cc.inverse() {
            Some(t) => {
                let mut tmp = Fq3 {
                    c0: t,
                    c1: t,
                    c2: t,
                };
                // t6 * c0, t6 * c1, t6 * c2
                tmp.c0.mul_assign(&t0);
                tmp.c1.mul_assign(&t2);
                tmp.c2.mul_assign(&t1);

                Some(tmp)
            }
            None => None,
        }
    }
}

#[inline(always)]
fn pow(base: &Fq3, exp: [u64; 36]) -> Fq3 {
    let mut res = Fq3::one();

    let mut found_one = false;

    /*
          let n = t.as_ref().len() * 64;
          for i in BitIterator { t, n }
    */
    // BitIterator is from pairing
    for i in super::BitIterator::new(&exp[..]) {
        if found_one {
            res.square();
        } else {
            found_one = i;
        }

        if i {
            res.mul_assign(&base);
        }
    }
    res
}

#[inline(always)]
fn legendre(x: &Fq3) -> ::ff::LegendreSymbol {
    x.norm().legendre()
}


impl SqrtField for Fq3 {
    
    #[inline(always)]
    fn legendre(&self) -> ::ff::LegendreSymbol {
        legendre(self)
    }

    #[inline(always)]
    fn sqrt(&self) -> Option<Self> {
        match self.legendre() {
            Zero => Some(*self),
            QuadraticNonResidue => None,
            QuadraticResidue => {
                // size_t v = Fp3_model<n,modulus>::s;
                let mut v: i64 = 30;
                // Fp3_model<n,modulus> z = Fp3_model<n,modulus>::nqr_to_t;
                let mut z: Fq3 = FQ3_NQR_T.clone();
                // Fp3_model<n,modulus> w = (*this)^Fp3_model<n,modulus>::t_minus_1_over_2;
                let w0: Fq3 = pow(&self, FQ3_T_MINUS_1);
                // Fp3_model<n,modulus> x = (*this) * w;
                let mut x = w0.clone();
                x.mul_assign(&self);
                // Fp3_model<n,modulus> b = x * w; // b = (*this)^t
                let mut b = x.clone();
                b.mul_assign(&w0);

                while b != Self::one() {
                    let mut m = 0;
                    let mut b2m = b;
                    while b2m != Self::one() {
                        b2m.square();
                        m += 1;
                    }

                    let mut j = v - m - 1;
                    while j > 0 {
                        z.square();
                        j = j - 1;
                    } // z^2^(v-m-1)

                    x.mul_assign(&z);

                    z.square();
                    b.mul_assign(&z);
                    v = m;
                }

                Some(x)
            }
        }
    }
}

#[test]
fn fq3_field_tests() {
    use ff::PrimeField;

    crate::tests::field::random_field_tests::<Fq3>();
    crate::tests::field::random_sqrt_tests::<Fq3>();
    crate::tests::field::random_frobenius_tests::<Fq3, _>(super::fq::Fq::char(), 13);
}


