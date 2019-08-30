macro_rules! curve_impl {
    (
        $name:expr,
        $projective:ident,
        $affine:ident,
        $prepared:ident,
        $basefield:ident,
        $scalarfield:ident,
        $uncompressed:ident,
        $compressed:ident,
        $pairing:ident
    ) => {
        #[derive(Copy, Clone, PartialEq, Eq, Debug)]
        pub struct $affine {
            pub(crate) x: $basefield,
            pub(crate) y: $basefield,
            pub(crate) infinity: bool,
        }

        impl ::std::fmt::Display for $affine {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                if self.infinity {
                    write!(f, "{}(Infinity)", $name)
                } else {
                    write!(f, "{}(x={}, y={})", $name, self.x, self.y)
                }
            }
        }

        #[derive(Copy, Clone, Debug, Eq)]
        pub struct $projective {
            pub(crate) x: $basefield,
            pub(crate) y: $basefield,
            pub(crate) z: $basefield,
        }

        impl ::std::fmt::Display for $projective {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                write!(f, "{}", self.into_affine())
            }
        }

        impl PartialEq for $projective {
            #[inline(always)]
            fn eq(&self, other: &$projective) -> bool {
                if self.is_zero() {
                    return other.is_zero();
                }

                if other.is_zero() {
                    return false;
                }

                // The points (X, Y, Z) and (X', Y', Z')
                // are equal when (X * Z'^2) = (X' * Z^2)
                // and (Y * Z'^3) = (Y' * Z^3).

                let mut z1 = self.z;
                z1.square();
                let mut z2 = other.z;
                z2.square();

                let mut tmp1 = self.x;
                tmp1.mul_assign(&z2);

                let mut tmp2 = other.x;
                tmp2.mul_assign(&z1);

                if tmp1 != tmp2 {
                    return false;
                }

                z1.mul_assign(&self.z);
                z2.mul_assign(&other.z);
                z2.mul_assign(&self.y);
                z1.mul_assign(&other.y);

                if z1 != z2 {
                    return false;
                }

                true
            }
        }

        impl $affine {
            #[inline(always)]
            fn mul_bits<S: AsRef<[u64]>>(&self, bits: BitIterator<S>) -> $projective {
                let mut res = $projective::zero();
                for i in bits {
                    res.double();
                    if i {
                        res.add_assign_mixed(self)
                    }
                }
                res
            }

            /// Attempts to construct an affine point given an x-coordinate. The
            /// point is not guaranteed to be in the prime order subgroup.
            ///
            /// If and only if `greatest` is set will the lexicographically
            /// largest y-coordinate be selected.
            #[inline(always)]
            fn get_point_from_x(x: $basefield, greatest: bool) -> Option<$affine> {
                // Compute x^3 + ax + b
                let mut x3axb = x;
                let mut ax = x;
                x3axb.square();
                x3axb.mul_assign(&x);
                ax.mul_assign(&$affine::get_coeff_a());
                x3axb.add_assign(&ax);
                x3axb.add_assign(&$affine::get_coeff_b());

                x3axb.sqrt().map(|y| {
                    let mut negy = y;
                    negy.negate();

                    $affine {
                        x: x,
                        y: if (y < negy) ^ greatest { y } else { negy },
                        infinity: false,
                    }
                })
            }

            #[inline(always)]
            fn is_on_curve(&self) -> bool {
                if self.is_zero() {
                    true
                } else {
                    // Check that the point is on the curve
                    let mut y2 = self.y;
                    y2.square();

                    let mut x3axb = self.x;
                    x3axb.square(); // x^2
                    x3axb.add_assign(&Self::get_coeff_a()); // x^2 + a
                    x3axb.mul_assign(&self.x); // x^3 + ax
                    x3axb.add_assign(&Self::get_coeff_b()); // x^3 + ax + b

                    y2 == x3axb
                }
            }

            #[inline(always)]
            fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool {
                self.mul($scalarfield::char()).is_zero()
            }
        }

        impl CurveAffine for $affine {
            type Engine = Mnt6;
            type Scalar = $scalarfield;
            type Base = $basefield;
            type Projective = $projective;
            type Uncompressed = $uncompressed;
            type Compressed = $compressed;
            type Prepared = $prepared;
            type Pair = $pairing;
            type PairingResult = Fq6;

            #[inline(always)]
            fn zero() -> Self {
                $affine {
                    x: $basefield::zero(),
                    y: $basefield::one(),
                    infinity: true,
                }
            }

            #[inline(always)]
            fn one() -> Self {
                Self::get_generator()
            }

            #[inline(always)]
            fn is_zero(&self) -> bool {
                self.infinity
            }

            #[inline(always)]
            fn mul<S: Into<<Self::Scalar as PrimeField>::Repr>>(&self, by: S) -> $projective {
                let bits = BitIterator::new(by.into());
                self.mul_bits(bits)
            }

            #[inline(always)]
            fn negate(&mut self) {
                if !self.is_zero() {
                    self.y.negate();
                }
            }

            #[inline(always)]
            fn into_projective(&self) -> $projective {
                (*self).into()
            }

            #[inline(always)]
            fn prepare(&self) -> Self::Prepared {
                $prepared::from_affine(*self)
            }

            #[inline(always)]
            fn pairing_with(&self, other: &Self::Pair) -> Self::PairingResult {
                self.perform_pairing(other)
            }
        }

        impl Rand for $projective {
            #[inline(always)]
            fn rand<R: Rng>(rng: &mut R) -> Self {
                loop {
                    let x = rng.gen();
                    let greatest = rng.gen();

                    if let Some(p) = $affine::get_point_from_x(x, greatest) {
                        let p = p.scale_by_cofactor();

                        if !p.is_zero() {
                            return p;
                        }
                    }
                }
            }
        }

        impl CurveProjective for $projective {
            type Engine = Mnt6;
            type Scalar = $scalarfield;
            type Base = $basefield;
            type Affine = $affine;

            // The point at infinity is always represented by
            // Z = 0.
            #[inline(always)]
            fn zero() -> Self {
                $projective {
                    x: $basefield::zero(),
                    y: $basefield::one(),
                    z: $basefield::zero(),
                }
            }

            #[inline(always)]
            fn one() -> Self {
                $affine::one().into()
            }

            // The point at infinity is always represented by
            // Z = 0.
            #[inline(always)]
            fn is_zero(&self) -> bool {
                self.z.is_zero()
            }

            #[inline(always)]
            fn is_normalized(&self) -> bool {
                self.is_zero() || self.z == $basefield::one()
            }

            #[inline(always)]
            fn batch_normalization(v: &mut [Self]) {
                // Montgomery’s Trick and Fast Implementation of Masked AES
                // Genelle, Prouff and Quisquater
                // Section 3.2

                // First pass: compute [a, ab, abc, ...]
                let mut prod = Vec::with_capacity(v.len());
                let mut tmp = $basefield::one();
                for g in v
                    .iter_mut()
                    // Ignore normalized elements
                    .filter(|g| !g.is_normalized())
                {
                    tmp.mul_assign(&g.z);
                    prod.push(tmp);
                }

                // Invert `tmp`.
                tmp = tmp.inverse().unwrap(); // Guaranteed to be nonzero.

                // Second pass: iterate backwards to compute inverses
                for (g, s) in v
                    .iter_mut()
                    // Backwards
                    .rev()
                    // Ignore normalized elements
                    .filter(|g| !g.is_normalized())
                    // Backwards, skip last element, fill in one for last term.
                    .zip(
                        prod.into_iter()
                            .rev()
                            .skip(1)
                            .chain(Some($basefield::one())),
                    )
                {
                    // tmp := tmp * g.z; g.z := tmp * s = 1/z
                    let mut newtmp = tmp;
                    newtmp.mul_assign(&g.z);
                    g.z = tmp;
                    g.z.mul_assign(&s);
                    tmp = newtmp;
                }

                // Perform affine transformations
                for g in v.iter_mut().filter(|g| !g.is_normalized()) {
                    let mut z = g.z; // 1/z
                    z.square(); // 1/z^2
                    g.x.mul_assign(&z); // x/z^2
                    z.mul_assign(&g.z); // 1/z^3
                    g.y.mul_assign(&z); // y/z^3
                    g.z = $basefield::one(); // z = 1
                }
            }

            // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#doubling-dbl-2007-bl
            #[inline(always)]
            fn double(&mut self) {
                if self.is_zero() {
                    return;
                }

                // Other than the point at infinity, no points on E or E'
                // can double to equal the point at infinity, as y=0 is
                // never true for points on the curve. (-4 and -4u-4
                // are not cubic residue in their respective fields.)

                // XX = X1^2
                let mut xx = self.x;
                xx.square();

                // YY = Y1^2
                let mut yy = self.y;
                yy.square();

                // YYYY = YY^2
                let mut yyyy = yy;
                yyyy.square();

                // ZZ = Z1^2
                let mut zz = self.z;
                zz.square();

                // S = 2*((X1+YY)^2-XX-YYYY)
                let mut s = self.x;
                s.add_assign(&yy);
                s.square();
                s.sub_assign(&xx);
                s.sub_assign(&yyyy);
                s.double();

                // M = 3*XX + a*ZZ^2
                let mut m = zz;
                m.square();
                m.mul_assign(&Self::get_coeff_a());
                m.add_assign(&xx);
                m.add_assign(&xx);
                m.add_assign(&xx);

                // T = M^2 - 2*S
                let mut t = m;
                t.square();
                t.sub_assign(&s);
                t.sub_assign(&s);

                // X3 = T
                self.x = t;

                // Z3 = (Y1 + Z1)^2 - YY - ZZ
                self.z.add_assign(&self.y);
                self.z.square();
                self.z.sub_assign(&yy);
                self.z.sub_assign(&zz);

                // Y3 = M*(S - T) - 8*YYYY
                self.y = s;
                self.y.sub_assign(&t);
                self.y.mul_assign(&m);
                yyyy.double();
                yyyy.double();
                yyyy.double();
                self.y.sub_assign(&yyyy);
            }

            // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-add-2007-bl
            #[inline(always)]
            fn add_assign(&mut self, other: &Self) {
                if self.is_zero() {
                    *self = *other;
                    return;
                }

                if other.is_zero() {
                    return;
                }

                // Z1Z1 = Z1^2
                let mut z1z1 = self.z;
                z1z1.square();

                // Z2Z2 = Z2^2
                let mut z2z2 = other.z;
                z2z2.square();

                // U1 = X1*Z2Z2
                let mut u1 = self.x;
                u1.mul_assign(&z2z2);

                // U2 = X2*Z1Z1
                let mut u2 = other.x;
                u2.mul_assign(&z1z1);

                // S1 = Y1*Z2*Z2Z2
                let mut s1 = self.y;
                s1.mul_assign(&other.z);
                s1.mul_assign(&z2z2);

                // S2 = Y2*Z1*Z1Z1
                let mut s2 = other.y;
                s2.mul_assign(&self.z);
                s2.mul_assign(&z1z1);

                if u1 == u2 && s1 == s2 {
                    // The two points are equal, so we double.
                    self.double();
                } else {
                    // If we're adding -a and a together, self.z becomes zero as H becomes zero.

                    // H = U2-U1
                    let mut h = u2;
                    h.sub_assign(&u1);

                    // I = (2*H)^2
                    let mut i = h;
                    i.double();
                    i.square();

                    // J = H*I
                    let mut j = h;
                    j.mul_assign(&i);

                    // r = 2*(S2-S1)
                    let mut r = s2;
                    r.sub_assign(&s1);
                    r.double();

                    // V = U1*I
                    let mut v = u1;
                    v.mul_assign(&i);

                    // X3 = r^2 - J - 2*V
                    self.x = r;
                    self.x.square();
                    self.x.sub_assign(&j);
                    self.x.sub_assign(&v);
                    self.x.sub_assign(&v);

                    // Y3 = r*(V - X3) - 2*S1*J
                    self.y = v;
                    self.y.sub_assign(&self.x);
                    self.y.mul_assign(&r);
                    s1.mul_assign(&j); // S1 = S1 * J * 2
                    s1.double();
                    self.y.sub_assign(&s1);

                    // Z3 = ((Z1+Z2)^2 - Z1Z1 - Z2Z2)*H
                    self.z.add_assign(&other.z);
                    self.z.square();
                    self.z.sub_assign(&z1z1);
                    self.z.sub_assign(&z2z2);
                    self.z.mul_assign(&h);
                }
            }

            // For Z2 = 1
            // https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-madd-2007-bl
            #[inline(always)]
            fn add_assign_mixed(&mut self, other: &Self::Affine) {
                if other.is_zero() {
                    return;
                }

                if self.is_zero() {
                    self.x = other.x;
                    self.y = other.y;
                    self.z = $basefield::one();
                    return;
                }

                // Z1Z1 = Z1^2
                let mut z1z1 = self.z;
                z1z1.square();

                // U2 = X2*Z1Z1
                let mut u2 = other.x;
                u2.mul_assign(&z1z1);

                // S2 = Y2*Z1*Z1Z1
                let mut s2 = other.y;
                s2.mul_assign(&self.z);
                s2.mul_assign(&z1z1);

                if self.x == u2 && self.y == s2 {
                    // The two points are equal, so we double.
                    self.double();
                } else {
                    // If we're adding -a and a together, self.z becomes zero as H becomes zero.

                    // H = U2-X1
                    let mut h = u2;
                    h.sub_assign(&self.x);

                    // HH = H^2
                    let mut hh = h;
                    hh.square();

                    // I = 4*HH
                    let mut i = hh;
                    i.double();
                    i.double();

                    // J = H*I
                    let mut j = h;
                    j.mul_assign(&i);

                    // r = 2*(S2-Y1)
                    let mut r = s2;
                    r.sub_assign(&self.y);
                    r.double();

                    // V = X1*I
                    let mut v = self.x;
                    v.mul_assign(&i);

                    // X3 = r^2 - J - 2*V
                    self.x = r;
                    self.x.square();
                    self.x.sub_assign(&j);
                    self.x.sub_assign(&v);
                    self.x.sub_assign(&v);

                    // Y3 = r*(V-X3)-2*Y1*J
                    j.mul_assign(&self.y); // J = 2*Y1*J
                    j.double();
                    self.y = v;
                    self.y.sub_assign(&self.x);
                    self.y.mul_assign(&r);
                    self.y.sub_assign(&j);

                    // Z3 = (Z1+H)^2-Z1Z1-HH
                    self.z.add_assign(&h);
                    self.z.square();
                    self.z.sub_assign(&z1z1);
                    self.z.sub_assign(&hh);
                }
            }

            #[inline(always)]
            fn negate(&mut self) {
                if !self.is_zero() {
                    self.y.negate()
                }
            }

            #[inline(always)]
            fn mul_assign<S: Into<<Self::Scalar as PrimeField>::Repr>>(&mut self, other: S) {
                let mut res = Self::zero();

                let mut found_one = false;

                for i in BitIterator::new(other.into()) {
                    if found_one {
                        res.double();
                    } else {
                        found_one = i;
                    }

                    if i {
                        res.add_assign(self);
                    }
                }

                *self = res;
            }

            #[inline(always)]
            fn into_affine(&self) -> $affine {
                (*self).into()
            }

            #[inline(always)]
            fn recommended_wnaf_for_scalar(scalar: <Self::Scalar as PrimeField>::Repr) -> usize {
                Self::empirical_recommended_wnaf_for_scalar(scalar)
            }

            #[inline(always)]
            fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
                Self::empirical_recommended_wnaf_for_num_scalars(num_scalars)
            }
        }

        // The affine point X, Y is represented in the jacobian
        // coordinates with Z = 1.
        impl From<$affine> for $projective {
            #[inline(always)]
            fn from(p: $affine) -> $projective {
                if p.is_zero() {
                    $projective::zero()
                } else {
                    $projective {
                        x: p.x,
                        y: p.y,
                        z: $basefield::one(),
                    }
                }
            }
        }

        // The projective point X, Y, Z is represented in the affine
        // coordinates as X/Z^2, Y/Z^3.
        impl From<$projective> for $affine {
            #[inline(always)]
            fn from(p: $projective) -> $affine {
                if p.is_zero() {
                    $affine::zero()
                } else if p.z == $basefield::one() {
                    // If Z is one, the point is already normalized.
                    $affine {
                        x: p.x,
                        y: p.y,
                        infinity: false,
                    }
                } else {
                    // Z is nonzero, so it must have an inverse in a field.
                    let zinv = p.z.inverse().unwrap();
                    let mut zinv_powered = zinv;
                    zinv_powered.square();

                    // X/Z^2
                    let mut x = p.x;
                    x.mul_assign(&zinv_powered);

                    // Y/Z^3
                    let mut y = p.y;
                    zinv_powered.mul_assign(&zinv);
                    y.mul_assign(&zinv_powered);

                    $affine {
                        x: x,
                        y: y,
                        infinity: false,
                    }
                }
            }
        }
    };
}

pub mod g1 {
    use super::super::{Fq, Fq3, Fq6, FqRepr, Fr, FrRepr, Mnt6};
    use super::g2::G2Affine;
    use ff::{BitIterator, Field, PrimeField, PrimeFieldRepr, SqrtField};
    use crate::{RawEncodable, CurveAffine, CurveProjective, EncodedPoint, GroupDecodingError, Engine};
    use rand::{Rand, Rng};
    use std::fmt;

    curve_impl!(
        "G1",
        G1,
        G1Affine,
        G1Prepared,
        Fq,
        Fr,
        G1Uncompressed,
        G1Compressed,
        G2Affine
    );

    #[derive(Copy, Clone)]
    pub struct G1Uncompressed([u8; 192]);

    impl AsRef<[u8]> for G1Uncompressed {
        fn as_ref(&self) -> &[u8] {
            &self.0
        }
    }

    impl AsMut<[u8]> for G1Uncompressed {
        fn as_mut(&mut self) -> &mut [u8] {
            &mut self.0
        }
    }

    impl fmt::Debug for G1Uncompressed {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
            self.0[..].fmt(formatter)
        }
    }

    impl EncodedPoint for G1Uncompressed {
        type Affine = G1Affine;

        fn empty() -> Self {
            G1Uncompressed([0; 192])
        }
        fn size() -> usize {
            192
        }
        fn into_affine(&self) -> Result<G1Affine, GroupDecodingError> {
            let affine = self.into_affine_unchecked()?;

            if !affine.is_on_curve() {
                Err(GroupDecodingError::NotOnCurve)
            } else if !affine.is_in_correct_subgroup_assuming_on_curve() {
                Err(GroupDecodingError::NotInSubgroup)
            } else {
                Ok(affine)
            }
        }
        fn into_affine_unchecked(&self) -> Result<G1Affine, GroupDecodingError> {
            // Create a copy of this representation.
            let mut copy = self.0;

            if copy[0] & (1 << 7) != 0 {
                // Distinguisher bit is set, but this should be uncompressed!
                return Err(GroupDecodingError::UnexpectedCompressionMode);
            }

            if copy[0] & (1 << 6) != 0 {
                // This is the point at infinity, which means that if we mask away
                // the first two bits, the entire representation should consist
                // of zeroes.
                copy[0] &= 0x3f;

                if copy.iter().all(|b| *b == 0) {
                    Ok(G1Affine::zero())
                } else {
                    Err(GroupDecodingError::UnexpectedInformation)
                }
            } else {
                if copy[0] & (1 << 5) != 0 {
                    // The bit indicating the y-coordinate should be lexicographically
                    // largest is set, but this is an uncompressed element.
                    return Err(GroupDecodingError::UnexpectedInformation);
                }

                // Unset the three most significant bits.
                copy[0] &= 0x1f;

                let mut x = FqRepr([0; 12]);
                let mut y = FqRepr([0; 12]);

                {
                    let mut reader = &copy[..];

                    x.read_be(&mut reader).unwrap();
                    y.read_be(&mut reader).unwrap();
                }

                Ok(G1Affine {
                    x: Fq::from_repr(x).map_err(|e| {
                        GroupDecodingError::CoordinateDecodingError("x coordinate", e)
                    })?,
                    y: Fq::from_repr(y).map_err(|e| {
                        GroupDecodingError::CoordinateDecodingError("y coordinate", e)
                    })?,
                    infinity: false,
                })
            }
        }
        fn from_affine(affine: G1Affine) -> Self {
            let mut res = Self::empty();

            if affine.is_zero() {
                // Set the second-most significant bit to indicate this point
                // is at infinity.
                res.0[0] |= 1 << 6;
            } else {
                let mut writer = &mut res.0[..];

                affine.x.into_repr().write_be(&mut writer).unwrap();
                affine.y.into_repr().write_be(&mut writer).unwrap();
            }

            res
        }
    }

    #[derive(Copy, Clone)]
    pub struct G1Compressed([u8; 96]);

    impl AsRef<[u8]> for G1Compressed {
        fn as_ref(&self) -> &[u8] {
            &self.0
        }
    }

    impl AsMut<[u8]> for G1Compressed {
        fn as_mut(&mut self) -> &mut [u8] {
            &mut self.0
        }
    }

    impl fmt::Debug for G1Compressed {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
            self.0[..].fmt(formatter)
        }
    }

    impl EncodedPoint for G1Compressed {
        type Affine = G1Affine;

        fn empty() -> Self {
            G1Compressed([0; 96])
        }
        fn size() -> usize {
            96
        }
        fn into_affine(&self) -> Result<G1Affine, GroupDecodingError> {
            let affine = self.into_affine_unchecked()?;

            // NB: Decompression guarantees that it is on the curve already.

            if !affine.is_in_correct_subgroup_assuming_on_curve() {
                Err(GroupDecodingError::NotInSubgroup)
            } else {
                Ok(affine)
            }
        }
        fn into_affine_unchecked(&self) -> Result<G1Affine, GroupDecodingError> {
            // Create a copy of this representation.
            let mut copy = self.0;

            if copy[0] & (1 << 7) == 0 {
                // Distinguisher bit isn't set.
                return Err(GroupDecodingError::UnexpectedCompressionMode);
            }

            if copy[0] & (1 << 6) != 0 {
                // This is the point at infinity, which means that if we mask away
                // the first two bits, the entire representation should consist
                // of zeroes.
                copy[0] &= 0x3f;

                if copy.iter().all(|b| *b == 0) {
                    Ok(G1Affine::zero())
                } else {
                    Err(GroupDecodingError::UnexpectedInformation)
                }
            } else {
                // Determine if the intended y coordinate must be greater
                // lexicographically.
                let greatest = copy[0] & (1 << 5) != 0;

                // Unset the three most significant bits.
                copy[0] &= 0x1f;

                let mut x = FqRepr([0; 12]);

                {
                    let mut reader = &copy[..];

                    x.read_be(&mut reader).unwrap();
                }

                // Interpret as Fq element.
                let x = Fq::from_repr(x)
                    .map_err(|e| GroupDecodingError::CoordinateDecodingError("x coordinate", e))?;

                G1Affine::get_point_from_x(x, greatest).ok_or(GroupDecodingError::NotOnCurve)
            }
        }
        fn from_affine(affine: G1Affine) -> Self {
            let mut res = Self::empty();

            if affine.is_zero() {
                // Set the second-most significant bit to indicate this point
                // is at infinity.
                res.0[0] |= 1 << 6;
            } else {
                {
                    let mut writer = &mut res.0[..];

                    affine.x.into_repr().write_be(&mut writer).unwrap();
                }

                let mut negy = affine.y;
                negy.negate();

                // Set the third most significant bit if the correct y-coordinate
                // is lexicographically largest.
                if affine.y > negy {
                    res.0[0] |= 1 << 5;
                }
            }

            // Set highest bit to distinguish this as a compressed element.
            res.0[0] |= 1 << 7;

            res
        }
    }

    impl G1Affine {
        fn scale_by_cofactor(&self) -> G1 {
            // G1 cofactor = 1
            // just return as G1 ($projective) element
            self.into_projective()
        }

        fn get_generator() -> Self {
            G1Affine {
                x: super::super::fq::G1_GENERATOR_X,
                y: super::super::fq::G1_GENERATOR_Y,
                infinity: false,
            }
        }

        fn get_coeff_a() -> Fq {
            super::super::fq::A_COEFF
        }

        fn get_coeff_b() -> Fq {
            super::super::fq::B_COEFF
        }

        fn perform_pairing(&self, other: &G2Affine) -> Fq6 {
            super::super::Mnt6::pairing(*self, *other)
        }
    }

        impl RawEncodable for G1Affine {
        fn into_raw_uncompressed_le(&self) -> Self::Uncompressed {
            let mut res = Self::Uncompressed::empty();
            {
                let mut writer = &mut res.0[..];

                self.x.into_raw_repr().write_le(&mut writer).unwrap();
                self.y.into_raw_repr().write_le(&mut writer).unwrap();
            }

            res
        }

        fn from_raw_uncompressed_le_unchecked(
            encoded: &Self::Uncompressed, 
            _infinity: bool
        ) -> Result<Self, GroupDecodingError> {
            let copy = encoded.0;
            if copy.iter().all(|b| *b == 0) {
                return Ok(Self::zero());
            }

            let mut x = FqRepr([0; 12]);
            let mut y = FqRepr([0; 12]);

            {
                let mut reader = &copy[..];
                x.read_le(&mut reader).unwrap();
                y.read_le(&mut reader).unwrap();
            }

            Ok(G1Affine {
                x: Fq::from_raw_repr(x).map_err(|e| {
                    GroupDecodingError::CoordinateDecodingError("x coordinate", e)
                })?,
                y: Fq::from_raw_repr(y).map_err(|e| {
                    GroupDecodingError::CoordinateDecodingError("y coordinate", e)
                })?,
                infinity: false,
            })
        }

        fn from_raw_uncompressed_le(encoded: &Self::Uncompressed, _infinity: bool) -> Result<Self, GroupDecodingError> {
            let affine = Self::from_raw_uncompressed_le_unchecked(&encoded, _infinity)?;

            if !affine.is_on_curve() {
                Err(GroupDecodingError::NotOnCurve)
            } else {
                Ok(affine)
            }
        }
    }

    impl G1 {
        fn get_coeff_a() -> Fq {
            super::super::fq::A_COEFF
        }

        fn empirical_recommended_wnaf_for_scalar(scalar: FrRepr) -> usize {
            let num_bits = scalar.num_bits() as usize;

            if num_bits >= 130 {
                4
            } else if num_bits >= 34 {
                3
            } else {
                2
            }
        }

        fn empirical_recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
            const RECOMMENDATIONS: [usize; 12] =
                [1, 3, 7, 20, 43, 120, 273, 563, 1630, 3128, 7933, 62569];

            let mut ret = 4;
            for r in &RECOMMENDATIONS {
                if num_scalars > *r {
                    ret += 1;
                } else {
                    break;
                }
            }

            ret
        }
    }

    #[derive(Eq, PartialEq, Copy, Clone, Debug)]
    pub struct G1Prepared {
        pub p:       G1Affine,
        pub x_by_twist: Fq3,
        pub y_by_twist: Fq3,
    }

    #[test]
    fn g1_generator() {
        use SqrtField;
        let mut x = Fq::zero();
        loop {
            // y^2 = x^3 + ax + b
            let mut rhs = x;
            rhs.square(); // x^2
            rhs.add_assign(&G1Affine::get_coeff_a()); // x^2 + a
            rhs.mul_assign(&x); // x^3 + ax
            rhs.add_assign(&G1Affine::get_coeff_b()); // x^3 + ax + b

            if let Some(y) = rhs.sqrt() {
                let yrepr = y.into_repr();
                let mut negy = y;
                negy.negate();
                let negyrepr = negy.into_repr();

                let p = G1Affine {
                    x: x,
                    y: if yrepr < negyrepr { y } else { negy },
                    infinity: false,
                };
                assert!(p.is_on_curve());
                break;
            }
            x.add_assign(&Fq::one());
        }
    }

    #[cfg(test)]
    use crate::tests::curve::curve_tests;

    #[test]
    fn test_curve_g1() {
        curve_tests::<G1>();
        crate::tests::curve::random_transformation_tests::<G1>();
    }

    #[test]
    fn test_g1_addition_correctness() {
        let mut p = G1 {
            x: Fq::from_repr(FqRepr([
                0xfa3269471af7fc29,
                0xe75814faa6e78c3,
                0x49a7d9cd2dd6aa5b,
                0x78cb72dd40780e8f,
                0xa628467279c19e1,
                0xaa2dabe7aacacfa4,
                0xfd0449a399f5bc10,
                0xcc69871930e2b94,
                0xbd359add50190868,
                0xa430620337195647,
                0x870751af8ead4105,
                0x109e8f3cec114,
            ]))
            .unwrap(),
            y: Fq::from_repr(FqRepr([
                0xc072a5045a0eb716,
                0xaa7ea85fd88b5c40,
                0x28ba48f5173291fa,
                0x15530eef5481573d,
                0xdd1ad67618327dac,
                0xf5c0666ed192a3b2,
                0x2b70dfe53a20a8ce,
                0x3d354613aff0bd6a,
                0x7a0034d2e30de04b,
                0xc3eabcb628fe0291,
                0x5b3196b3e0ce308a,
                0xeda96045ae66,
            ]))
            .unwrap(),
            z: Fq::one(),
        };

        p.add_assign(&G1 {
            x: Fq::from_repr(FqRepr([
                0xb6f0a8e0b589ce8b,
                0x11d2007be6d43bcb,
                0x8cf5e84f9d1455e7,
                0xb3948e0450cfad43,
                0x3150075f6db70ae1,
                0x227254395f6e7f5c,
                0xd4013b9d00959599,
                0xb9b8b393ab316213,
                0x7cdd3853be3db699,
                0xb00bdce397d661ff,
                0xc1e075f0736f6f8d,
                0x1ae55bf692b13,
            ]))
            .unwrap(),
            y: Fq::from_repr(FqRepr([
                0x39354a603130591,
                0x65ef5dc8a3bb6cad,
                0x3dc56a836204653f,
                0x189514b20bb6a1e,
                0x51d29d2c02d4e641,
                0x1f7a4d415b6be19a,
                0x144dc1b1ffcc41b0,
                0x485d891f0870162b,
                0xa8a4ca2c5c8d5dd0,
                0xbfb746c7be9ecbfa,
                0x2bd71fee34ba3197,
                0x17c99c45f0909,
            ]))
            .unwrap(),
            z: Fq::one(),
        });

        let p = G1Affine::from(p);

        assert_eq!(
            p,
            G1Affine {
                x: Fq::from_repr(FqRepr([
                    0x4075f3c009273e85,
                    0x5d4bd293f6bcc9e6,
                    0x8e27c491f7573c54,
                    0xbd6387c831a6ca54,
                    0xc2dca28819554d1e,
                    0x347a4cfd65ecc90b,
                    0xcf2e71ba8fa7bb4c,
                    0x72338f027482c52c,
                    0x870a69b5ee0b8e64,
                    0xe54577a0ca314b35,
                    0x4227f07bb68b1667,
                    0xf2bb18a3958a,
                ]))
                .unwrap(),
                y: Fq::from_repr(FqRepr([
                    0x197f59872551b337,
                    0xea7728119a1c4aee,
                    0xa86d3ead69ab4e97,
                    0x2310388bf7be5af3,
                    0x3e2810110e19cfb2,
                    0x71ff5fc55bf03cc9,
                    0xe6b3608817306d89,
                    0xeb20fd323630411d,
                    0x7294ef5c1a0476b9,
                    0x33ed661992c99ae2,
                    0x593721f98fddb53d,
                    0xfd983ca844c2,
                ]))
                .unwrap(),
                infinity: false,
            }
        );
    }

    #[test]
    fn test_g1_doubling_correctness() {
        let mut p = G1 {
            x: Fq::from_repr(FqRepr([
                0xb19aed9b3dc15f89,
                0x29de7cb8bc671412,
                0x4c7542b9dea227d4,
                0x5dc4af9e491c7a5f,
                0xdee5857fa6bc0ca2,
                0xb26ed03d5845df9a,
                0x55dd26801730f0c7,
                0x277ca14f3ca740dc,
                0xcd92eab91d54a80b,
                0xb0511416f2a0a418,
                0x3002007605fcca03,
                0x157101f321264,
            ]))
            .unwrap(),
            y: Fq::from_repr(FqRepr([
                0xf1b7d78c336187eb,
                0x759be3b9a52861ef,
                0xbf535e3141e47420,
                0xc88cb29d5479ce23,
                0x8048c51c4a374a81,
                0xad6e60b0a50a47a7,
                0x15705b02b85cad3f,
                0x477910253eb87de5,
                0xe8c2425b4c8d3b25,
                0x8e64e07d1d7ab34a,
                0x3a4865ebe3d0bc24,
                0xc88df4f8a73c,
            ]))
            .unwrap(),
            z: Fq::one(),
        };

        p.double();

        let p = G1Affine::from(p);

        assert_eq!(
            p,
            G1Affine {
                x: Fq::from_repr(FqRepr([
                    0x532c93cfcb4a16fa,
                    0x5114f616cce055a6,
                    0xf314349b3be478bd,
                    0x421f32dbdfefbd72,
                    0xf77cce337c6eacad,
                    0xee7b6035844afe4d,
                    0x31c3609e58efa430,
                    0xa135db8c9f8a40bf,
                    0xa4e02fe151db05ee,
                    0x6ab8eb33c99569d3,
                    0xf610aaeea6d03ac5,
                    0x124da8c081bc9,
                ]))
                .unwrap(),
                y: Fq::from_repr(FqRepr([
                    0xf2e6d63d02d690d0,
                    0x742166cca7aa2dd1,
                    0xf878b8f47cd2b343,
                    0xbb6c5aa896dba201,
                    0x844652a50840d74c,
                    0xfed24238534ec2be,
                    0x32d3c6d354e0fec4,
                    0xb30eb0ae74a3fe0a,
                    0xa799f9a48370cded,
                    0x7511b3ce4a912397,
                    0x537b51139b80f575,
                    0x86c594e940e2,
                ]))
                .unwrap(),
                infinity: false,
            }
        );
    }
}

pub mod g2 {
    use super::super::{Fq, Fq3, Fq6, FqRepr, Fr, FrRepr, Mnt6};
    use super::g1::G1Affine;
    use ff::{BitIterator, Field, PrimeField, PrimeFieldRepr, SqrtField};
    use crate::{CurveAffine, CurveProjective, EncodedPoint, GroupDecodingError, Engine};
    use rand::{Rand, Rng};
    use std::fmt;

    curve_impl!(
        "G2",
        G2,
        G2Affine,
        G2Prepared,
        Fq3,
        Fr,
        G2Uncompressed,
        G2Compressed,
        G1Affine
    );

    #[derive(Copy, Clone)]
    pub struct G2Uncompressed([u8; 576]);

    impl AsRef<[u8]> for G2Uncompressed {
        fn as_ref(&self) -> &[u8] {
            &self.0
        }
    }

    impl AsMut<[u8]> for G2Uncompressed {
        fn as_mut(&mut self) -> &mut [u8] {
            &mut self.0
        }
    }

    impl fmt::Debug for G2Uncompressed {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
            self.0[..].fmt(formatter)
        }
    }

    impl EncodedPoint for G2Uncompressed {
        type Affine = G2Affine;

        fn empty() -> Self {
            G2Uncompressed([0; 576])
        }
        fn size() -> usize {
            576
        }
        fn into_affine(&self) -> Result<G2Affine, GroupDecodingError> {
            let affine = self.into_affine_unchecked()?;

            if !affine.is_on_curve() {
                Err(GroupDecodingError::NotOnCurve)
            } else if !affine.is_in_correct_subgroup_assuming_on_curve() {
                Err(GroupDecodingError::NotInSubgroup)
            } else {
                Ok(affine)
            }
        }
        fn into_affine_unchecked(&self) -> Result<G2Affine, GroupDecodingError> {
            // Create a copy of this representation.
            let mut copy = self.0;

            if copy[0] & (1 << 7) != 0 {
                // Distinguisher bit is set, but this should be uncompressed!
                return Err(GroupDecodingError::UnexpectedCompressionMode);
            }

            if copy[0] & (1 << 6) != 0 {
                // This is the point at infinity, which means that if we mask away
                // the first two bits, the entire representation should consist
                // of zeroes.
                copy[0] &= 0x3f;

                if copy.iter().all(|b| *b == 0) {
                    Ok(G2Affine::zero())
                } else {
                    Err(GroupDecodingError::UnexpectedInformation)
                }
            } else {
                if copy[0] & (1 << 5) != 0 {
                    // The bit indicating the y-coordinate should be lexicographically
                    // largest is set, but this is an uncompressed element.
                    return Err(GroupDecodingError::UnexpectedInformation);
                }

                // Unset the three most significant bits.
                copy[0] &= 0x1f;

                let mut x_c0 = FqRepr([0; 12]);
                let mut x_c1 = FqRepr([0; 12]);
                let mut x_c2 = FqRepr([0; 12]);
                let mut y_c0 = FqRepr([0; 12]);
                let mut y_c1 = FqRepr([0; 12]);
                let mut y_c2 = FqRepr([0; 12]);

                {
                    let mut reader = &copy[..];

                    x_c2.read_be(&mut reader).unwrap();
                    x_c1.read_be(&mut reader).unwrap();
                    x_c0.read_be(&mut reader).unwrap();
                    y_c2.read_be(&mut reader).unwrap();
                    y_c1.read_be(&mut reader).unwrap();
                    y_c0.read_be(&mut reader).unwrap();
                }

                Ok(G2Affine {
                    x: Fq3 {
                        c0: Fq::from_repr(x_c0).map_err(|e| {
                            GroupDecodingError::CoordinateDecodingError("x coordinate (c0)", e)
                        })?,
                        c1: Fq::from_repr(x_c1).map_err(|e| {
                            GroupDecodingError::CoordinateDecodingError("x coordinate (c1)", e)
                        })?,
                        c2: Fq::from_repr(x_c2).map_err(|e| {
                            GroupDecodingError::CoordinateDecodingError("x coordinate (c2)", e)
                        })?,
                    },
                    y: Fq3 {
                        c0: Fq::from_repr(y_c0).map_err(|e| {
                            GroupDecodingError::CoordinateDecodingError("y coordinate (c0)", e)
                        })?,
                        c1: Fq::from_repr(y_c1).map_err(|e| {
                            GroupDecodingError::CoordinateDecodingError("y coordinate (c1)", e)
                        })?,
                        c2: Fq::from_repr(y_c2).map_err(|e| {
                            GroupDecodingError::CoordinateDecodingError("y coordinate (c2)", e)
                        })?,
                    },
                    infinity: false,
                })
            }
        }
        fn from_affine(affine: G2Affine) -> Self {
            let mut res = Self::empty();

            if affine.is_zero() {
                // Set the second-most significant bit to indicate this point
                // is at infinity.
                res.0[0] |= 1 << 6;
            } else {
                let mut writer = &mut res.0[..];

                affine.x.c1.into_repr().write_be(&mut writer).unwrap();
                affine.x.c0.into_repr().write_be(&mut writer).unwrap();
                affine.y.c1.into_repr().write_be(&mut writer).unwrap();
                affine.y.c0.into_repr().write_be(&mut writer).unwrap();
            }

            res
        }
    }

    #[derive(Copy, Clone)]
    pub struct G2Compressed([u8; 288]);

    impl AsRef<[u8]> for G2Compressed {
        fn as_ref(&self) -> &[u8] {
            &self.0
        }
    }

    impl AsMut<[u8]> for G2Compressed {
        fn as_mut(&mut self) -> &mut [u8] {
            &mut self.0
        }
    }

    impl fmt::Debug for G2Compressed {
        fn fmt(&self, formatter: &mut fmt::Formatter) -> Result<(), fmt::Error> {
            self.0[..].fmt(formatter)
        }
    }

    impl EncodedPoint for G2Compressed {
        type Affine = G2Affine;

        fn empty() -> Self {
            G2Compressed([0; 288])
        }
        fn size() -> usize {
            288
        }
        fn into_affine(&self) -> Result<G2Affine, GroupDecodingError> {
            let affine = self.into_affine_unchecked()?;

            // NB: Decompression guarantees that it is on the curve already.

            if !affine.is_in_correct_subgroup_assuming_on_curve() {
                Err(GroupDecodingError::NotInSubgroup)
            } else {
                Ok(affine)
            }
        }
        fn into_affine_unchecked(&self) -> Result<G2Affine, GroupDecodingError> {
            // Create a copy of this representation.
            let mut copy = self.0;

            if copy[0] & (1 << 7) == 0 {
                // Distinguisher bit isn't set.
                return Err(GroupDecodingError::UnexpectedCompressionMode);
            }

            if copy[0] & (1 << 6) != 0 {
                // This is the point at infinity, which means that if we mask away
                // the first two bits, the entire representation should consist
                // of zeroes.
                copy[0] &= 0x3f;

                if copy.iter().all(|b| *b == 0) {
                    Ok(G2Affine::zero())
                } else {
                    Err(GroupDecodingError::UnexpectedInformation)
                }
            } else {
                // Determine if the intended y coordinate must be greater
                // lexicographically.
                let greatest = copy[0] & (1 << 5) != 0;

                // Unset the three most significant bits.
                copy[0] &= 0x1f;

                let mut x_c2 = FqRepr([0; 12]);
                let mut x_c1 = FqRepr([0; 12]);
                let mut x_c0 = FqRepr([0; 12]);

                {
                    let mut reader = &copy[..];

                    x_c2.read_be(&mut reader).unwrap();
                    x_c1.read_be(&mut reader).unwrap();
                    x_c0.read_be(&mut reader).unwrap();
                }

                // Interpret as Fq element.
                let x = Fq3 {
                    c0: Fq::from_repr(x_c0).map_err(|e| {
                        GroupDecodingError::CoordinateDecodingError("x coordinate (c0)", e)
                    })?,
                    c1: Fq::from_repr(x_c1).map_err(|e| {
                        GroupDecodingError::CoordinateDecodingError("x coordinate (c1)", e)
                    })?,
                    c2: Fq::from_repr(x_c2).map_err(|e| {
                        GroupDecodingError::CoordinateDecodingError("x coordinate (c2)", e)
                    })?,
                };

                G2Affine::get_point_from_x(x, greatest).ok_or(GroupDecodingError::NotOnCurve)
            }
        }
        fn from_affine(affine: G2Affine) -> Self {
            let mut res = Self::empty();

            if affine.is_zero() {
                // Set the second-most significant bit to indicate this point
                // is at infinity.
                res.0[0] |= 1 << 6;
            } else {
                {
                    let mut writer = &mut res.0[..];

                    affine.x.c1.into_repr().write_be(&mut writer).unwrap();
                    affine.x.c0.into_repr().write_be(&mut writer).unwrap();
                }

                let mut negy = affine.y;
                negy.negate();

                // Set the third most significant bit if the correct y-coordinate
                // is lexicographically largest.
                if affine.y > negy {
                    res.0[0] |= 1 << 5;
                }
            }

            // Set highest bit to distinguish this as a compressed element.
            res.0[0] |= 1 << 7;

            res
        }
    }

    impl G2Affine {
        fn get_generator() -> Self {
            G2Affine {
                x: Fq3 {
                    c0: super::super::fq::G2_GENERATOR_X_C0,
                    c1: super::super::fq::G2_GENERATOR_X_C1,
                    c2: super::super::fq::G2_GENERATOR_X_C2,
                },
                y: Fq3 {
                    c0: super::super::fq::G2_GENERATOR_Y_C0,
                    c1: super::super::fq::G2_GENERATOR_Y_C1,
                    c2: super::super::fq::G2_GENERATOR_Y_C2,
                },
                infinity: false,
            }
        }

        pub fn get_coeff_a() -> Fq3 {
            super::super::fq::G2_A_COEFF
        }

        fn get_coeff_b() -> Fq3 {
            super::super::fq::G2_B_COEFF
        }

        fn scale_by_cofactor(&self) -> G2 {
            // Multiply by G2_cofactor and return the projective associated point
            let mut projective = self.into_projective();
            let mut cx = projective;
            cx.mul_assign(super::super::fr::G2_COFACTOR_C);
            projective.mul_assign(super::super::fr::MINUS_ONE);
            projective.mul_assign(super::super::fr::G2_COFACTOR_B);
            projective.add_assign(&cx);
            projective.mul_assign(super::super::fr::G2_COFACTOR_A);
            projective
        }

        fn perform_pairing(&self, other: &G1Affine) -> Fq6 {
            super::super::Mnt6::pairing(*other, *self)
        }
    }

    impl G2 {
        pub fn get_coeff_a() -> Fq3 {
            super::super::fq::G2_A_COEFF
        }

        fn empirical_recommended_wnaf_for_scalar(scalar: FrRepr) -> usize {
            let num_bits = scalar.num_bits() as usize;

            if num_bits >= 103 {
                4
            } else if num_bits >= 37 {
                3
            } else {
                2
            }
        }

        fn empirical_recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
            const RECOMMENDATIONS: [usize; 11] =
                [1, 3, 8, 20, 47, 126, 260, 826, 1501, 4555, 84071];

            let mut ret = 4;
            for r in &RECOMMENDATIONS {
                if num_scalars > *r {
                    ret += 1;
                } else {
                    break;
                }
            }

            ret
        }
    }

        #[derive(Eq, PartialEq, Clone, Debug)]
    pub struct G2Prepared {
        pub p:                     G2Affine,
        pub x_over_twist:          Fq3,
        pub y_over_twist:          Fq3,
        pub double_coefficients:   Vec<AteDoubleCoefficients>,
        pub addition_coefficients: Vec<AteAdditionCoefficients>,
    }

    pub struct G2ProjectiveExtended {
        pub x: Fq3,
        pub y: Fq3,
        pub z: Fq3,
        pub t: Fq3,
    }

    #[derive(Eq, PartialEq, Copy, Clone, Debug)]
    pub struct AteDoubleCoefficients {
        pub c_h:  Fq3,
        pub c_4c: Fq3,
        pub c_j:  Fq3,
        pub c_l:  Fq3,
    }

    #[derive(Eq, PartialEq, Copy, Clone, Debug)]
    pub struct AteAdditionCoefficients {
        pub c_l1: Fq3,
        pub c_rz: Fq3,
    }

    #[cfg(test)]
    use rand::{SeedableRng, XorShiftRng};

    #[test]
    fn g2_generator() {
        use SqrtField;
        let mut x = Fq3::zero();
        loop {
            let mut rhs = x;
            rhs.square(); // x^2
            rhs.add_assign(&G2Affine::get_coeff_a()); // x^2 + a
            rhs.mul_assign(&x); // x^3 + ax
            rhs.add_assign(&G2Affine::get_coeff_b()); // x^3 + ax + b
            if let Some(y) = rhs.sqrt() {
                let mut negy = y;
                negy.negate();
                let p = G2Affine {
                    x: x,
                    y: if y < negy { y } else { negy },
                    infinity: false,
                };
                assert!(p.is_on_curve());
                break;
            }
            x.add_assign(&Fq3::one());
        }
    }

    #[test]
    fn g2_generator_on_curve() {
        let gen = G2Affine::get_generator();

        let mut lhs = gen.y;
        lhs.square();

        let mut rhs = gen.x;
        rhs.square();
        rhs.add_assign(&G2Affine::get_coeff_a());
        rhs.mul_assign(&gen.x);
        rhs.add_assign(&G2Affine::get_coeff_b());

        assert_eq!(lhs, rhs);

        // Test that generator belongs to the subgroup of order r
        let mut gen_proj = gen.into_projective();
        gen_proj.mul_assign(Fr::char());
        assert!(gen_proj.is_zero());
    }

    #[test]
    fn g2_cofactor_mnt6() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        for _ in 0..1000 {
            let mut g = G2::rand(&mut rng);
            g.mul_assign(Fr::char());
            assert!(g.is_zero());
        }
    }

    #[test]
    fn test_curve_g2() {
        crate::tests::curve::curve_tests::<G2>();
        crate::tests::curve::random_transformation_tests::<G2>();
    }

}
pub use self::g1::*;
pub use self::g2::*;
