#![allow(non_snake_case)]

use merlin::Transcript;
use rand::thread_rng;
use secp256kfun::{g, hash::Tag, s, Point, G};
extern crate sha2;
use sha2::{digest::Digest, Sha256};

use secp256kfun::{marker::*, Scalar};

pub type PubScalarZ = Scalar<Public, Zero>;
pub type PubScalarNz = Scalar<Public, NonZero>;

extern crate merlin;

/// Base generators used in the norm argument.
/// Unlike inner product arguments, G and H might not be of the
/// same length.
#[derive(Clone, Debug, PartialEq)]
pub struct BaseGens {
    /// The points Vec<G>
    pub G_vec: Vec<Point<NonNormal>>,
    /// The points H
    pub H_vec: Vec<Point<NonNormal>>,
}

impl BaseGens {
    /// Create a new base generator with the given G and H.
    pub fn new(num_g: u32, num_h: u32) -> Self {
        // generate a set of generators for G
        fn gen_tagged_points(n: u32, tag: &str) -> Vec<Point<NonNormal>> {
            let mut gs = Vec::with_capacity(n as usize);
            let mut i: u64 = 0;
            while gs.len() < n as usize {
                loop {
                    i = i + 1;
                    let mut hash_x = Sha256::default().tag_vectored([tag.as_bytes(), b"x"].into_iter());
                    hash_x.update(&i.to_be_bytes());
                    let gen_x = hash_x.finalize();
                    let mut hash_y =
                        sha2::Sha256::default().tag_vectored([tag.as_bytes(), b"y"].into_iter());
                    hash_y.update(&i.to_be_bytes());
                    let gen_y = hash_y.finalize();

                    let mut bytes = [0u8; 33];
                    bytes[1..].copy_from_slice(&gen_x);
                    bytes[0] = 2u8 + (gen_y[0] & 1u8);
                    match Point::from_bytes(bytes) {
                        Some(g) => {
                            gs.push(g.non_normal());
                            break;
                        }
                        None => continue,
                    }
                }
            }
            gs
        }

        let gs = gen_tagged_points(num_g, "BulletProofs/G");
        let hs = gen_tagged_points(num_h, "BulletProofs/H");
        Self {
            G_vec: gs,
            H_vec: hs,
        }
    }
}

/// A Norm Linear Proof
#[derive(Debug, Clone, PartialEq)]
pub struct NormProof {
    /// Vector of points X_i that used during norm recursion
    pub x_vec: Vec<Point<Normal, Public, Zero>>,
    /// Vector of points R_i that used during norm recursion
    pub r_vec: Vec<Point<Normal, Public, Zero>>,
    /// The norm vector reducing the recursion to 1.
    pub n: PubScalarZ,
    /// The l value
    pub l: PubScalarZ,
}

/// Compute the inner product of two vectors <l, c>.
fn inner_product<'a, A, B>(l_vec: &A, c_vec: &B) -> PubScalarZ
where
    A: Iterator<Item = &'a PubScalarZ> + Clone,
    B: Iterator<Item = &'a PubScalarZ> + Clone,
{
    let mut res = s!(0);
    for (a, b) in l_vec.clone().into_iter().zip(c_vec.clone().into_iter()) {
        res = s!(res + a * b);
    }
    res.public()
}

/// Compute the q-weighted inner product of two vectors.
fn weighted_inner_product<'a, A, B>(a_iter: &A, b_iter: &B, q: PubScalarNz) -> PubScalarZ
where
    A: Iterator<Item = &'a PubScalarZ> + Clone,
    B: Iterator<Item = &'a PubScalarZ> + Clone,
{
    let mut res = s!(0);
    let mut q_pow = s!(1).mark_zero();
    for (a, b) in a_iter.clone().into_iter().zip(b_iter.clone().into_iter()) {
        q_pow = s!(q_pow * q);
        res = s!(res + a * b * q_pow);
    }
    res.public()
}

// /// Compute the q-weighted inner product of two vectors.
// fn q_weighted_inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
//     a.iter().zip(b).map(|(a, b)| a * b).sum()
// }

/// Compute v*G + <G_vec, n> + <H_vec, l>
fn bp_comm<'a, A, B>(
    v: Scalar<Public, Zero>,
    G_vec: &A,
    H_vec: &A,
    n: &B,
    l: &B,
) -> Point<NonNormal, Public, Zero>
where
    A: Iterator<Item = &'a Point<NonNormal>> + Clone,
    B: Iterator<Item = &'a PubScalarZ> + Clone,
{
    let mut res = g!(v * G);
    for (g, n) in G_vec.clone().into_iter().zip(n.clone().into_iter()) {
        res = g!(res + n * g);
    }
    for (h, l) in H_vec.clone().into_iter().zip(l.clone().into_iter()) {
        res = g!(res + l * h);
    }
    res
}

/// Compute R + r*<l, G>
fn point_inner_product<'a, A, B>(Gs: &A, l: &B) -> Point<NonNormal, Public, Zero>
where
    A: Iterator<Item = &'a Point<NonNormal>> + Clone,
    B: Iterator<Item = &'a PubScalarZ> + Clone,
{
    let mut res = Point::zero();
    for (g, l) in Gs.clone().into_iter().zip(l.clone().into_iter()) {
        res = g!(res + l * g);
    }
    res
}

// Compute a scalar challenge from a transcript.
fn scalar_challenge(t: &mut merlin::Transcript) -> PubScalarNz {
    let mut dest = [0u8; 32];
    t.challenge_bytes(b"e", &mut dest);
    let e = Scalar::from_bytes(dest).unwrap().non_zero().unwrap();
    e
}

impl NormProof {
    /// Compute v = <n_vec, n_vec>^2_q + <l, c>

    pub(crate) fn v(
        n_vec: &[PubScalarZ],
        l_vec: &[PubScalarZ],
        c_vec: &[PubScalarZ],
        q: PubScalarNz,
    ) -> Scalar<Public, Zero> {
        let n_sq = weighted_inner_product(&n_vec.iter(), &n_vec.iter(), q);
        // Compute <l, c>
        let l_c = inner_product(&l_vec.iter(), &c_vec.iter());
        // Compute v = w*w*q + <l, c>
        s!(n_sq + l_c).public()
    }

    /// Prove that <n_vec, n_vec>^2_(r^2) + <l, c> = v
    pub fn prove(
        transcript: &mut merlin::Transcript,
        mut gens: BaseGens,
        mut n_vec: Vec<Scalar<Public, Zero>>,
        mut l_vec: Vec<Scalar<Public, Zero>>,
        mut c_vec: Vec<Scalar<Public, Zero>>,
        mut r: Scalar<Public>,
    ) -> Self {
        let mut n_len = n_vec.len();
        let mut l_len = l_vec.len();

        let mut Gs = &mut gens.G_vec[..];
        let mut Hs = &mut gens.H_vec[..];

        let mut n = &mut n_vec[..];
        let mut l = &mut l_vec[..];
        let mut c = &mut c_vec[..];

        assert_eq!(Gs.len(), n_len);
        assert_eq!(c.len(), l_len);
        assert_eq!(Hs.len(), l_len);
        assert!(n_len.is_power_of_two());
        assert!(l_len.is_power_of_two());

        let ln_n = std::cmp::max(l_len, n_len).next_power_of_two();
        let mut X_vec = Vec::with_capacity(ln_n);
        let mut R_vec = Vec::with_capacity(ln_n);
        let mut q = s!(r * r).public();

        fn alter_iter<T>(
            a: &mut [T],
        ) -> (
            impl Iterator<Item = &T> + Clone,
            impl Iterator<Item = &T> + Clone,
        ) {
            let iter0 = a.iter().step_by(2).map(|x| &*x);
            let iter1 = a.iter().skip(1).step_by(2).map(|x| &*x);
            (iter0, iter1)
        }

        while n_len != 1 || l_len != 1 {
            let (r_inv, q_old, q_sq, e) = {
                let (w0, w1) = alter_iter(n);
                let (g0, g1) = alter_iter(Gs);


                dbg!(&l);
                let (l0, l1) = alter_iter(l);
                let (c0, c1) = alter_iter(c);
                let (h0, h1) = alter_iter(Hs);

                let q_sq = s!(q * q).public();
                let r_inv = r.invert().public();
                let X_v0 = inner_product(&c0, &l1);
                let X_v1 = inner_product(&c1, &l0);
                let X_v2 = weighted_inner_product(&w0, &w1, q_sq);
                let X_v = &s!(X_v0 + X_v1 + 2 * r_inv * X_v2);
                // assert_eq!(*X_v, {let wa = w0[0]; let wb = w1[0]; s!(2*wa *wb*q_sq*r_inv)});

                dbg!(&X_v);
                let mut X = g!(X_v * G);

                // X = X + <g0, w1>*r + <g1, w0>/r + <h0, l1> + <h1, l0>
                let X1 = point_inner_product(&g0, &w1);
                let X2 = point_inner_product(&g1, &w0);
                let X3 = point_inner_product(&h0, &l1);
                let X4 = point_inner_product(&h1, &l0);
                dbg!(&X1);
                dbg!(&X2);
                dbg!(&X3);
                dbg!(&X4);
                X = g!(X + r * X1 + r_inv * X2 + X3 + X4);

                let R_v_0 = inner_product(&c1, &l1);
                let R_v_1 = weighted_inner_product(&w1, &w1, q_sq);
                let R_v = s!(R_v_0 + R_v_1).public();
                // assert_eq!(R_v, {let wa = w1[0]; s!(wa *wa*q_sq)});
                let R = bp_comm(R_v, &g1, &h1, &w1, &l1);

                let X = X.normalize();
                let R = R.normalize();
                transcript.append_message(b"L", &X.to_bytes());
                transcript.append_message(b"R", &R.to_bytes());

                X_vec.push(X);
                R_vec.push(R);

                let e = scalar_challenge(transcript);
                (r_inv, q, q_sq, e)
            };
            if n_len > 1 {
                let mut i = 0;
                while i < n_len {
                    let (wl, wr, gl, gr) = (n[i], n[i + 1], Gs[i], Gs[i + 1]);
                    n[i/2] = s!(r_inv * wl + e * wr).public();
                    Gs[i/2] = g!(r * gl + e * gr).non_zero().unwrap();
                    i = i + 2;
                }
            }

            if l_len > 1 {
                let mut i = 0;
                while i < l_len {
                    let (cl, cr, hl, hr) = (c[i], c[i + 1], Hs[i], Hs[i + 1]);
                    let (ll, lr) = (l[i], l[i + 1]);
                    c[i/2] = s!(cl + e * cr).public();
                    l[i/2] = s!(ll + e * lr).public();
                    Hs[i/2] = g!(hl + e * hr).non_zero().unwrap();
                    i += 2;
                }
            }
            n_len = (n_len + 1) / 2; // Adding 1 ensures that stop at 1 and don't go to zero.
            l_len = (l_len + 1) / 2;
            n = &mut n[..n_len];
            Gs = &mut Gs[..n_len];
            l = &mut l[..l_len];
            c = &mut c[..l_len];
            Hs = &mut Hs[..l_len];
            r = q_old;
            q = q_sq;
        }

        Self {
            x_vec: X_vec,
            r_vec: R_vec,
            n: n[0],
            l: l[0],
        }
    }

    // Return a vector of length n where the i-th element of the vector is equal to
    // product(j=0...challenges.len(), binary(i)[j]* e[j])
    fn s_vec(n: usize, challenges: &[PubScalarNz]) -> Vec<PubScalarZ> {
        let mut s = Vec::with_capacity(n);
        s.push(s!(1).public().mark_zero());
        for i in 1..n {
            let lg_i = log(i);
            let k = 1 << lg_i;
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let u_val = challenges[lg_i];
            let u_not_last_set_bit = s[i - k];
            s.push(
                s!(u_not_last_set_bit * u_val)
                    .public()
                    .mark_zero(),
            );
        }
        s
    }

    // Get the scalars to be used in verification in multi scalar exponentiation.
    fn verification_scalars(
        &self,
        t: &mut merlin::Transcript,
        r: PubScalarNz,
        g_n: usize,
        h_n: usize,
    ) -> (Vec<PubScalarNz>, Vec<PubScalarZ>, Vec<PubScalarZ>) {
        let mut challenges = Vec::with_capacity(self.x_vec.len());
        for (X, R) in self.x_vec.iter().zip(self.r_vec.iter()) {
            t.append_message(b"L", &X.to_bytes());
            t.append_message(b"R", &R.to_bytes());
            challenges.push(scalar_challenge(t));
        }

        // Similar to s used in dalek crypto bp implementation, but modified for bp++
        let mut s_g = Self::s_vec(g_n, &challenges);
        let s_h = Self::s_vec(h_n, &challenges);

        // Compute g_n powers of q
        let mut r_pows = Vec::with_capacity(g_n);
        r_pows.push(s!(1).public());
        for i in 1..g_n {
            let last = r_pows[i - 1];
            r_pows.push(s!(last * r).public());
        }
        // Compute s_g = s_g * q_pow_perm
        // where q_pows_perm[i] = r^(2^g_n - 1 - i)
        for i in 0..g_n {
            let (s_g_i, q_pow_perm_i) = (s_g[i], r_pows[g_n - 1 - i as usize]);
            s_g[i] = s!(s_g_i * q_pow_perm_i).public();
        }
        (challenges, s_g, s_h)
    }

    /// Verify that C = v*G + <n_vec, gens.G_vec> + <l_vec, gens.H_vec>
    /// where v = <n_vec, n_vec>_(r^2) + <c_vec, l_vec>
    pub fn verify(
        &self,
        gens: &BaseGens,
        transcript: &mut merlin::Transcript,
        C: Point::<Normal, Public, Zero>,
        c_vec: &[PubScalarZ],
        r: PubScalarNz,
    ) -> bool {
        // TODO: make sure the provided number of generators match with the proof

        // Verify that n^2 + l = v for the given commitment.
        let mut q = s!(r * r).public();
        // Factors with which we multiply the generators.
        let (challenges, s_g, s_h) =
            self.verification_scalars(transcript, r, gens.G_vec.len(), gens.H_vec.len());

        let lg_n = log(gens.G_vec.len());
        for _ in 0..lg_n {
            q = s!(q * q).public();
        }

        let l_c = inner_product(&s_h.iter(), &c_vec.iter());

        let v = s!(self.n * self.n * q + self.l * l_c);

        let one = s!(1).public();

        // These collects can be avoided if downstream allows borrow APIs
        let scalar_iter = std::iter::once(one)
            .chain(challenges.iter().copied())
            .chain(
                challenges
                    .iter()
                    .map(|e| s!(e * e - 1).public().non_zero().unwrap()),
            )
            .into_iter()
            .collect::<Vec<_>>();

        let point_iter = std::iter::once(C.non_normal())
            .chain(self.x_vec.iter().copied().map(|X| X.non_normal()))
            .chain(self.r_vec.iter().copied().map(|R| R.non_normal()))
            .into_iter()
            .collect::<Vec<_>>();

        let res = secp256kfun::op::lincomb(scalar_iter.iter(), point_iter.iter());

        let g_0 = secp256kfun::op::lincomb(s_g.iter(), gens.G_vec.iter());
        let h_0 = secp256kfun::op::lincomb(s_h.iter(), gens.H_vec.iter());

        let C_0 = g!(v * G + self.n * g_0 + self.l * h_0);
        C_0 == res
    }

    pub fn serialize(&self) -> Vec<u8> {
        let mut ret = vec![];
        for (x, r) in self.x_vec.iter().zip(self.r_vec.iter()) {
            let offset = ret.len();
            ret.extend(&x.to_bytes());
            ret[offset] = (ret[offset] & 1) << 1;
            let tmp = r.to_bytes();
            ret[offset] |= tmp[0] & 1;
            ret.extend_from_slice(&tmp[1..33]);
        }
        ret.extend(&self.n.to_bytes());
        ret.extend(&self.l.to_bytes());
        return ret;
    }

    pub fn deserialize(buf: &[u8]) -> Option<NormProof> {
        let len = buf.len();
        if len < 64
           || (len - 64) % 65 != 0 {
            return None;
        }
        let n_rounds = (len - 64) / 65;
        let mut x_vec = vec![];
        let mut r_vec = vec![];
        for i in 0..n_rounds {
            let mut tmp = vec![];
            let offset = i*65;
            for j in 0..2 {
                let sign = (buf[offset] & (2-(j as u8))) >> (1-j);
                let x = &buf[offset+j*32+1..offset+j*32+33];
                if x != [0u8;32] {
                    tmp.push(2 + sign);
                } else {
                    tmp.push(0);
                }
                tmp.extend(x);
            }
            x_vec.push(Point::<_, Public, Zero>::from_slice(&tmp[..33])?);
            r_vec.push(Point::<_, Public, Zero>::from_slice(&tmp[33..])?);
        }
        let n = Scalar::from_slice(&buf[len - 64..len - 32])?;
        let l = Scalar::from_slice(&buf[len - 32..len])?;

        return Some(NormProof {
            x_vec : x_vec,
            r_vec : r_vec,
            n: n,
            l: l,
        });
    }
}

pub(crate) fn log(n: usize) -> usize {
    32 - 1 - (n as u32).leading_zeros() as usize
}

// Test prove
fn rand_scalar() -> PubScalarZ {
    Scalar::random(&mut thread_rng())
        .public()
        .mark_zero()
}

fn rand_scalar_vec(l: u32) -> Vec<PubScalarZ> {
    (0..l).map(|_| rand_scalar()).collect()
}

pub(crate) fn tester(sz_n: u32, sz_l: u32) {
    let gens = BaseGens::new(sz_n, sz_l);

    let mut transcript = Transcript::new(b"test");

    let mut n = rand_scalar_vec(sz_n);
    let mut l = rand_scalar_vec(sz_l);
    let mut c = rand_scalar_vec(sz_l);
    n[0] = s!(1).public().mark_zero();
    n[1] = s!(3).public().mark_zero();
    n[2] = s!(5).public().mark_zero();
    n[3] = s!(7).public().mark_zero();

    l[0] = Scalar::zero();
    c[0] = Scalar::zero();

    let r = s!(2).public();
    let q = s!(r * r).public();

    let v = NormProof::v(&n, &l, &c, q);

    let C = bp_comm(
        v,
        &gens.G_vec.iter(),
        &gens.H_vec.iter(),
        &n.iter(),
        &l.iter(),
    );
    // test norm argument prove
    let prf = NormProof::prove(&mut transcript, gens.clone(), n, l, c.clone(), r);
    dbg!(&prf);

    let mut transcript = Transcript::new(b"test");
    assert!(prf.verify(
        &gens,
        &mut transcript,
        C.normalize(),
        &c,
        r,
    ))
}

#[derive(Debug, Clone, PartialEq)]
pub struct VerifyVector {
    pub gens: BaseGens,
    pub C: Point::<Normal, Public, Zero>,
    pub c_vec: Vec<PubScalarZ>,
    pub r: PubScalarNz,
    pub proof: Vec<u8>,
    pub result: bool,
    pub comment: String,
}


pub struct VerifyVectors {
    pub vectors: Vec<VerifyVector>,
}

impl VerifyVectors {
    pub fn new() -> Self {
        let mut vecs = vec![];

        // Vector 1: vector of size 1
        let gens = BaseGens::new(1, 1);
        let n_vec = vec![s!(-2).public().mark_zero()];
        let l_vec = vec![s!(-3).public().mark_zero()];
        let c_vec = vec![s!(-5).public().mark_zero()];
        let r = s!(-7).public();
        let q = s!(r*r).public();

        let proof = NormProof::prove(&mut Transcript::new(b"BPP/norm_arg/tests"), gens.clone(), n_vec.clone(), l_vec.clone(), c_vec.clone(), r);

        let v = NormProof::v(&n_vec, &l_vec, &c_vec, q);
        let C = bp_comm(v, &gens.G_vec.iter(), &gens.H_vec.iter(), &n_vec.iter(), &l_vec.iter()).normalize();
        assert!(proof.verify(&gens, &mut Transcript::new(b"BPP/norm_arg/tests"), C, &c_vec, r));
        vecs.push(VerifyVector {
            gens: gens,
            C: C,
            c_vec: c_vec,
            r: r,
            proof: proof.serialize(),
            result: true,
            comment: "".to_string(),
        });

        // Vector 2: wrong proof size
        vecs.push(vecs[0].clone());
        vecs[1].proof = vecs[0].proof[..vecs[0].proof.len()-1].to_vec();
        vecs[1].result = false;
        assert!(NormProof::deserialize(&vecs[1].proof).is_none());

        // Vector 3: invalid point in proof
        let gens = BaseGens::new(2, 1);
        let n_vec = vec![s!(-2).public().mark_zero(), s!(-7).public().mark_zero()];
        let l_vec = vec![s!(-3).public().mark_zero()];
        let c_vec = vec![s!(-5).public().mark_zero()];
        let r = s!(-11).public();
        let q = s!(r*r).public();

        let proof = NormProof::prove(&mut Transcript::new(b"BPP/norm_arg/tests"), gens.clone(), n_vec.clone(), l_vec.clone(), c_vec.clone(), r);
        let v = NormProof::v(&n_vec, &l_vec, &c_vec, q);
        let C = bp_comm(v, &gens.G_vec.iter(), &gens.H_vec.iter(), &n_vec.iter(), &l_vec.iter()).normalize();
        assert!(proof.verify(&gens, &mut Transcript::new(b"BPP/norm_arg/tests"), C, &c_vec, r));

        let mut invalid_x = [0u8;32];
        invalid_x[31] = 5;
        let proof = proof.serialize();
        let mut new_proof = proof[0..1].to_vec();
        new_proof.extend(invalid_x);
        new_proof.extend_from_slice(&proof[33..]);
        let proof = new_proof;
        assert!(NormProof::deserialize(&proof).is_none());

        vecs.push(VerifyVector {
            gens: gens,
            C: C,
            c_vec: c_vec,
            r: r,
            proof: proof,
            result: false,
            comment: "".to_string(),
        });

        return VerifyVectors { vectors: vecs };
    }

    // Given an array of bytes outputs a string with each element of the array
    // in hex. Example output: "{ 0x0F, 0xAB, 0x12 }"
    fn bytearray_to_C(array: &[u8]) -> String {
        let mut result = String::from("{ ");
        for byte in array {
            result.push_str(&format!("0x{:02X}, ", byte));
        }
        result.pop();
        result.pop();
        result.push_str(" }");
        result
    }

    fn scalars_to_C(scalars: &Vec<PubScalarZ>) -> String {
        let mut result = String::from("{ ");
        for s in scalars {
            result.push_str(&VerifyVectors::bytearray_to_C(&s.to_bytes()));
            result.push_str(", ");
        }
        result.pop();
        result.pop();
        result.push_str(" }");
        result
    }

    fn gens_to_C(G_vec: &Vec<Point<NonNormal>>, H_vec: &Vec<Point<NonNormal>>) -> String {
        let mut all_gens : Vec<Point<NonNormal>> = vec![];
        all_gens.extend(G_vec);
        all_gens.extend(H_vec);
        let mut result = String::from("{ ");
        for g in all_gens {
            for byte in g.normalize().to_bytes() {
                result.push_str(&format!("0x{:02X}, ", byte));
            }
        }
        result.pop();
        result.pop();
        result.push_str(" }");
        result
    }

    pub fn to_C(&self) -> String {
        let mut s = String::new();

        for (i, v) in self.vectors.iter().enumerate() {
            s.push_str(&format!("static const unsigned char verify_vector_{}_gens[{}] = {};\n", i, (v.gens.G_vec.len() + v.gens.H_vec.len())*33, VerifyVectors::gens_to_C(&v.gens.G_vec, &v.gens.H_vec)));
            s.push_str(&format!("static const unsigned char verify_vector_{}_commit33[33] = {};\n", i, &VerifyVectors::bytearray_to_C(&v.C.to_bytes())));
            s.push_str(&format!("static const unsigned char verify_vector_{}_c_vec32[{}][32] = {};\n", i, v.c_vec.len(), &VerifyVectors::scalars_to_C(&v.c_vec)));
            s.push_str(&format!("static secp256k1_scalar verify_vector_{}_c_vec[{}];\n", i, v.c_vec.len()));
            s.push_str(&format!("static const unsigned char verify_vector_{}_r32[32] = {};\n", i, &VerifyVectors::bytearray_to_C(&v.r.to_bytes())));
            s.push_str(&format!("static const unsigned char verify_vector_{}_proof[] = {};\n", i, &VerifyVectors::bytearray_to_C(&v.proof)));
            s.push_str(&format!("static const int verify_vector_{}_result = {};\n", i, &(v.result as u8)));
        }

        return s;
    }
}

#[cfg(test)]
mod tests{
    use super::*;

    use proptest::prelude::*;


    fn ts() -> Transcript {
        Transcript::new(b"BPP/norm_arg/tests")
    }

    #[test]
    fn test_secp256kfun_serialization() {
        let O = Point::<Normal, Public, Zero>::zero();
        assert_eq!(O.to_bytes(), [0u8; 33]);
    }


    #[test]
    fn test_norm_arg() {
        let gens = BaseGens::new(1, 1);
        let two = s!(2).public();
        let n_vec = vec![two.mark_zero()];
        let l_vec = vec![two.mark_zero()];
        let c_vec = vec![two.mark_zero()];
        let r = two;
        let q = s!(r*r).public();

        let proof = NormProof::prove(&mut ts(), gens.clone(), n_vec.clone(), l_vec.clone(), c_vec.clone(), r);

        let v = NormProof::v(&n_vec, &l_vec, &c_vec, q);
        let Cp = bp_comm(v, &gens.G_vec.iter(), &gens.H_vec.iter(), &n_vec.iter(), &l_vec.iter()).normalize();
        assert!(proof.verify(&gens, &mut ts(), Cp, &c_vec, r));

        tester(4,2);
        tester(32,16);
        tester(8,64);
        tester(4,8);
        tester(32,1);
        tester(64,64);
    }

    // n_vec and l_vec (and therefore v) are 0. This is fine
    #[test]
    fn test_norm_arg_zeros() {
        let n_vec = vec![Scalar::zero()];
        let l_vec = vec![Scalar::zero()];
        let gens = BaseGens::new(n_vec.len() as u32, l_vec.len() as u32);
        let c_vec = vec![rand_scalar().mark_zero()];
        let r = Scalar::random(&mut rand::thread_rng()).public();
        let q = s!(r*r).public();

        let v = NormProof::v(&n_vec, &l_vec, &c_vec, q);
        assert_eq!(v, Scalar::<Public, Zero>::zero());
        let Cp = bp_comm(v, &gens.G_vec.iter(), &gens.H_vec.iter(), &n_vec.iter(), &l_vec.iter()).normalize();
        assert_eq!(Cp, Point::<Normal, Public, Zero>::zero());

        let proof = NormProof::prove(&mut ts(), gens.clone(), n_vec.clone(), l_vec.clone(), c_vec.clone(), r);
        assert!(proof.verify(&gens, &mut ts(), Cp, &c_vec, r));

    }

    // If n is longer than l and w only contains zeros then X is the point at infinity.
    // Same if l is longer than n and only contains zeros then X or R (TODO: which one?) are the point at infinity.
    #[test]
    fn test_norm_arg_zeros2() {
        let n_vec = vec![Scalar::zero(), Scalar::zero()];
        let l_vec = vec![rand_scalar()];
        let gens = BaseGens::new(n_vec.len() as u32, l_vec.len() as u32);
        let c_vec = vec![rand_scalar().mark_zero()];
        let r = Scalar::random(&mut rand::thread_rng()).public();
        let q = s!(r*r).public();

        let proof = NormProof::prove(&mut ts(), gens.clone(), n_vec.clone(), l_vec.clone(), c_vec.clone(), r);
        let v = NormProof::v(&n_vec, &l_vec, &c_vec, q);
        let Cp = bp_comm(v, &gens.G_vec.iter(), &gens.H_vec.iter(), &n_vec.iter(), &l_vec.iter()).normalize();
        assert!(proof.verify(&gens, &mut ts(), Cp, &c_vec, r));

        let l_vec = n_vec;
        let n_vec = vec![rand_scalar()];
        let c_vec = vec![rand_scalar().mark_zero(); l_vec.len()];
        let gens = BaseGens::new(n_vec.len() as u32, l_vec.len() as u32);
        let proof = NormProof::prove(&mut ts(), gens.clone(), n_vec.clone(), l_vec.clone(), c_vec.clone(), r);
        let v = NormProof::v(&n_vec, &l_vec, &c_vec, q);
        let Cp = bp_comm(v, &gens.G_vec.iter(), &gens.H_vec.iter(), &n_vec.iter(), &l_vec.iter()).normalize();
        assert!(proof.verify(&gens, &mut ts(), Cp, &c_vec, r));
    }

    #[test]
    fn test_vectors() {
        VerifyVectors::new();
    }

    proptest! {
        #[test]
        fn norm_proof_serialize(x_vec in any::<Vec<Point::<Normal, Public, Zero>>>(),
                                r_diff in any::<Point::<Normal, Public, Zero>>(),
                                l in any::<Scalar<Public, Zero>>(),
                                n in any::<Scalar<Public, Zero>>()) {

            let mut r_vec = x_vec.clone();
            let r_len = r_vec.len();
            if r_len > 0 {
                r_vec[r_len - 1] = r_diff;
            }
            let proof = NormProof {
                x_vec: x_vec,
                r_vec: r_vec,
                l: l,
                n: n,
            };
            let buf = &proof.serialize();
            assert_eq!(proof, NormProof::deserialize(buf).unwrap());
        }

        // test that honest proof must verify
        #[test]
        fn norm_arg_completeness(rand in any::<Scalar<Public, Zero>>(),
                                 rand2 in any::<Scalar<Public, Zero>>(),
                                 n_len_exp in 0u32..3,
                                 l_len_exp in 0u32..3,
                                 r in any::<Scalar<Public, NonZero>>()) {
            // n_vec.len() must be power of two
            let n_len = 2u32.pow(n_len_exp);
            let l_len = 2u32.pow(l_len_exp);
            let n_vec = vec![rand; n_len as usize];
            let l_vec = vec![rand2; l_len as usize];

            let gens = BaseGens::new(n_vec.len() as u32, l_vec.len() as u32);
            let c_vec = vec![s!(rand + rand2*rand2).public(); l_len as usize];
            let q = s!(r*r).public();

            let proof = NormProof::prove(&mut ts(), gens.clone(), n_vec.clone(), l_vec.clone(), c_vec.clone(), r);
            let v = NormProof::v(&n_vec.to_vec(), &l_vec, &c_vec, q);
            let Cp = bp_comm(v, &gens.G_vec.iter(), &gens.H_vec.iter(), &n_vec.iter(), &l_vec.iter()).normalize();
            let gens = BaseGens::new(n_vec.len() as u32, l_vec.len() as u32);
            assert!(proof.verify(&gens, &mut ts(), Cp, &c_vec, r))
        }

        // test that an arbitrary proof doesn't verify
        #[test]
        fn norm_arg_verify(r in any::<Scalar<Public, NonZero>>(),
                           c_vec in any::<[Scalar<Public, Zero>; 2]>(),
                           X in any::<[Point<Normal, Public, Zero>; 2]>(),
                           R in any::<[Point<Normal, Public, Zero>; 2]>(),
                           len in 1..2usize,
                           n in any::<Scalar<Public, Zero>>(),
                           l in any::<Scalar<Public, Zero>>()) {
            let Cp = g!(43*G).normalize().mark_zero();
            let gens = BaseGens::new(X.len() as u32, R.len() as u32);
            let proof = NormProof {
                x_vec: X[0..len].to_vec(),
                r_vec: R[0..len].to_vec(),
                n: n,
                l: l,
            };
            assert!(!proof.verify(&gens, &mut ts(), Cp, &c_vec[0..len], r));
        }
    }
}
