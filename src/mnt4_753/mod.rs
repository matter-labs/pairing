mod ec;
mod fq;
mod fq2;
mod fq4;
mod fr;

use self::{
    ec::g2::{AteAdditionCoefficients, AteDoubleCoefficients, G2ProjectiveExtended},
    fq::{EXP_W0, EXP_W0_IS_NEGATIVE, EXP_W1, MNT4_X, MNT4_X_IS_NEGATIVE, TWIST, TWIST_INV},
};

pub use self::ec::{
    G1Affine, G1Compressed, G1Prepared, G1Uncompressed, G2Affine, G2Compressed, G2Prepared,
    G2Uncompressed, G1, G2,
};

pub use self::fq::{Fq, FqRepr};
pub use self::fq2::Fq2;
pub use self::fq4::Fq4;
pub use self::fr::{Fr, FrRepr};

use super::{CurveAffine, Engine};

use ff::{BitIterator, Field, ScalarEngine};

#[derive(Clone, Debug)]
pub struct Mnt4;

impl Mnt4 {
    fn ate_pairing_loop(p: &G1Prepared, q: &G2Prepared) -> Fq4 {
        let mut l1_coeff = Fq2::zero();
        l1_coeff.c0 = p.p.x;
        l1_coeff.sub_assign(&q.x_over_twist);

        let mut f = Fq4::one();

        let mut dbl_idx: usize = 0;
        let mut add_idx: usize = 0;

        // The for loop is executed for all bits (EXCEPT the MSB itself) of
        let mut found_one = false;
        for bit in BitIterator::new(&MNT4_X).skip(1) {
            if !found_one {
                found_one = bit;
                continue;
            }

            let dc = &q.double_coefficients[dbl_idx];
            dbl_idx += 1;

            let mut g_rr_at_p = Fq4::zero();

            let mut t0 = dc.c_j;
            t0.mul_assign(&p.x_by_twist);
            t0.negate();
            t0.add_assign(&dc.c_l);
            t0.sub_assign(&dc.c_4c);

            let mut t1 = dc.c_h;
            t1.mul_assign(&p.y_by_twist);

            g_rr_at_p.c0 = t0;
            g_rr_at_p.c1 = t1;

            f.square();
            f.mul_assign(&g_rr_at_p);

            if bit {
                let ac = &q.addition_coefficients[add_idx];
                add_idx += 1;

                let mut g_rq_at_p = Fq4::zero();

                let mut t0 = ac.c_rz;
                t0.mul_assign(&p.y_by_twist);

                let mut t = l1_coeff;
                t.mul_assign(&ac.c_l1);

                let mut t1 = q.y_over_twist;
                t1.mul_assign(&ac.c_rz);
                t1.add_assign(&t);
                t1.negate();

                g_rq_at_p.c0 = t0;
                g_rq_at_p.c1 = t1;

                f.mul_assign(&g_rq_at_p);
            }
        }

        if MNT4_X_IS_NEGATIVE {
            let ac = &q.addition_coefficients[add_idx];

            let mut g_rnegr_at_p = Fq4::zero();

            let mut t0 = ac.c_rz;
            t0.mul_assign(&p.y_by_twist);

            let mut t = l1_coeff;
            t.mul_assign(&ac.c_l1);

            let mut t1 = q.y_over_twist;
            t1.mul_assign(&ac.c_rz);
            t1.add_assign(&t);
            t1.negate();

            g_rnegr_at_p.c0 = t0;
            g_rnegr_at_p.c1 = t1;

            f.mul_assign(&g_rnegr_at_p);
            f = f.inverse().expect("It should not throw");
        }

        f
    }

    fn final_exponentiation_part_one(elt: &Fq4, elt_inv: &Fq4) -> Fq4 {
        /* (q^2-1) */

        /* elt_q2 = elt^(q^2) */
        let mut elt_q2 = elt.clone();
        elt_q2.frobenius_map(2);
        /* elt_q2_over_elt = elt^(q^2-1) */
        let mut elt_q2_over_elt = elt_q2;
        elt_q2_over_elt.mul_assign(&elt_inv);

        elt_q2_over_elt
    }

    fn final_exponentiation_part_two(elt: &Fq4, &elt_inv: &Fq4) -> Fq4 {
        let mut elt_q = elt.clone();
        elt_q.frobenius_map(1);

        let mut w1_part = elt_q.clone().cyclotomic_exp(&EXP_W1);
        let w0_part = match EXP_W0_IS_NEGATIVE {
            true => elt_inv.clone().cyclotomic_exp(&EXP_W0),
            false => elt.clone().cyclotomic_exp(&EXP_W0),
        };

        w1_part.mul_assign(&w0_part);
        w1_part
    }
}

impl ScalarEngine for Mnt4 {
    type Fr = Fr;
}

impl Engine for Mnt4 {
    type G1 = G1;
    type G1Affine = G1Affine;
    type G2 = G2;
    type G2Affine = G2Affine;
    type Fq = Fq;
    type Fqe = Fq2;
    type Fqk = Fq4;

    fn miller_loop<'a, I>(i: I) -> Self::Fqk
    where
        I: IntoIterator<
            Item = &'a (
                &'a <Self::G1Affine as CurveAffine>::Prepared,
                &'a <Self::G2Affine as CurveAffine>::Prepared,
            ),
        >,
    {
        let mut f = Fq4::one();
        for (p, q) in i.into_iter() {
            if !p.is_zero() && !q.is_zero() {
                f.mul_assign(&Self::ate_pairing_loop(p, q));
            }
        }

        f
    }

    fn final_exponentiation(f: &Fq4) -> Option<Fq4> {
        let value_inv = f.inverse();
        if value_inv.is_none() {
            return None;
        }
        let value_inv = value_inv.expect("is some");
        let value_to_first_chunk = Self::final_exponentiation_part_one(f, &value_inv);
        let value_inv_to_first_chunk = Self::final_exponentiation_part_one(&value_inv, f);

        Some(Self::final_exponentiation_part_two(
            &value_to_first_chunk,
            &value_inv_to_first_chunk,
        ))
    }
}

impl G2Prepared {
    pub fn is_zero(&self) -> bool {
        self.p.infinity
    }

    pub fn from_affine(q: G2Affine) -> Self {
        let mut res = G2Prepared {
            p: q,
            x_over_twist: Fq2::zero(),
            y_over_twist: Fq2::zero(),
            double_coefficients: vec![],
            addition_coefficients: vec![],
        };
        res.precompute();
        res
    }

    fn doubling_step(r: &mut G2ProjectiveExtended) -> AteDoubleCoefficients {
        let mut a = r.t.clone();
        a.square();
        let mut b = r.x.clone();
        b.square();
        let mut c = r.y.clone();
        c.square();
        let mut d = c.clone();
        d.square();

        let mut e = r.x.clone();
        e.add_assign(&c);
        e.square();
        e.sub_assign(&b);
        e.sub_assign(&d);

        let mut f = G2::get_coeff_a();
        f.mul_assign(&a);
        f.add_assign(&b);
        f.add_assign(&b);
        f.add_assign(&b);

        let mut g = f.clone();
        g.square();

        let mut d_eight = d.clone();
        d_eight.double();
        d_eight.double();
        d_eight.double();

        let mut t0 = e.clone();
        t0.double();
        t0.double();

        let mut x = g.clone();
        x.sub_assign(&t0);

        let mut y = e.clone();
        y.double();
        y.sub_assign(&x);
        y.mul_assign(&f);
        y.sub_assign(&d_eight);

        let mut t0 = r.z.clone();
        t0.square();

        let mut z = r.y.clone();
        z.add_assign(&r.z);
        z.square();
        z.sub_assign(&c);
        z.sub_assign(&t0);

        let mut t = z.clone();
        t.square();

        let mut c_h = z.clone();
        c_h.add_assign(&r.t);
        c_h.square();
        c_h.sub_assign(&t);
        c_h.sub_assign(&a);

        let mut c_4c = c.clone();
        c_4c.double();
        c_4c.double();

        let mut c_j = f.clone();
        c_j.add_assign(&r.t);
        c_j.square();
        c_j.sub_assign(&g);
        c_j.sub_assign(&a);

        let mut c_l = f.clone();
        c_l.add_assign(&r.x);
        c_l.square();
        c_l.sub_assign(&g);
        c_l.sub_assign(&b);

        let coeff = AteDoubleCoefficients {
            c_h,
            c_4c,
            c_j,
            c_l,
        };

        r.x = x;
        r.y = y;
        r.z = z;
        r.t = t;

        coeff
    }

    fn addition_step(x: &Fq2, y: &Fq2, r: &mut G2ProjectiveExtended) -> AteAdditionCoefficients {
        let mut a = y.clone();
        a.square();
        let mut b = r.t.clone();
        b.mul_assign(&x);

        let mut d = r.z.clone();
        d.add_assign(&y);
        d.square();
        d.sub_assign(&a);
        d.sub_assign(&r.t);
        d.mul_assign(&r.t);

        let mut h = b.clone();
        h.sub_assign(&r.x);

        let mut i = h.clone();
        i.square();

        let mut e = i.clone();
        e.double();
        e.double();

        let mut j = h.clone();
        j.mul_assign(&e);

        let mut v = r.x.clone();
        v.mul_assign(&e);

        let mut l1 = d.clone();
        l1.sub_assign(&r.y);
        l1.sub_assign(&r.y);

        let mut x = l1.clone();
        x.square();
        x.sub_assign(&j);
        x.sub_assign(&v);
        x.sub_assign(&v);

        let mut t0 = r.y.clone();
        t0.double();
        t0.mul_assign(&j);

        let mut y = v.clone();
        y.sub_assign(&x);
        y.mul_assign(&l1);
        y.sub_assign(&t0);

        let mut z = r.z.clone();
        z.add_assign(&h);
        z.square();
        z.sub_assign(&r.t);
        z.sub_assign(&i);

        let mut t = z.clone();
        t.square();

        let coeff = AteAdditionCoefficients {
            c_l1: l1,
            c_rz: z.clone(),
        };

        r.x = x;
        r.y = y;
        r.z = z;
        r.t = t;

        coeff
    }

    fn precompute(&mut self) {
        if self.p.is_zero() {
            return;
        }

        // not asserting normalization, it will be asserted in the loop
        // precompute addition and doubling coefficients
        self.x_over_twist = self.p.x;
        self.x_over_twist.mul_assign(&TWIST_INV);

        self.y_over_twist = self.p.y;
        self.y_over_twist.mul_assign(&TWIST_INV);

        let mut r = G2ProjectiveExtended {
            x: self.p.x,
            y: self.p.y,
            z: Fq2::one(),
            t: Fq2::one(),
        };

        let mut found_one = false;
        for bit in BitIterator::new(&MNT4_X).skip(1) {
            if !found_one {
                found_one = bit;
                continue;
            }

            let coeff = Self::doubling_step(&mut r);
            self.double_coefficients.push(coeff);

            if bit {
                let coeff = Self::addition_step(&self.p.x, &self.p.y, &mut r);
                self.addition_coefficients.push(coeff);
            }
        }

        if MNT4_X_IS_NEGATIVE {
            let rz_inv = r.z.inverse().expect("z should not be equal to zero");
            let mut rz2_inv = rz_inv;
            rz2_inv.square();
            let mut rz3_inv = rz_inv;
            rz3_inv.mul_assign(&rz2_inv);

            let mut minus_r_affine_x = rz2_inv;
            minus_r_affine_x.mul_assign(&r.x);
            let mut minus_r_affine_y = rz3_inv;
            minus_r_affine_y.mul_assign(&r.y);
            minus_r_affine_y.negate();

            let coeff = Self::addition_step(&minus_r_affine_x, &minus_r_affine_y, &mut r);

            self.addition_coefficients.push(coeff);
        }
    }
}

impl G1Prepared {
    pub fn is_zero(&self) -> bool {
        return self.p.infinity;
    }

    pub fn from_affine(p: G1Affine) -> Self {
        let mut res = G1Prepared {
            p: p,
            x_by_twist: TWIST,
            y_by_twist: TWIST,
        };

        if p.is_zero() {
            return res;
        }

        res.x_by_twist.mul_assign_by_fp(&p.x);
        res.y_by_twist.mul_assign_by_fp(&p.y);
        res
    }
}

#[test]
fn mnt4_engine_tests() {
    crate::tests::engine::engine_tests::<Mnt4>();
}
