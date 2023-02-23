#![allow(non_snake_case)]

/// Rangeproof implementation using norm argument
use crate::transcript::Transcript;
use crate::norm_arg::{self, NormProof};
use norm_arg::BaseGens;
use rand::{CryptoRng, RngCore};
use secp256kfun::{Point, Scalar, g, G, s, marker::{Secret, Zero, Public, NonNormal, NonZero, Secrecy, ZeroChoice}};

/// Round 1 artifacts
#[derive(Debug, Clone)]
struct Round1Commitments {
    /// Round 1 output: D
    D: Point<NonNormal>,
    /// Round 1 output: M
    M: Point<NonNormal>,
}

#[derive(Debug, Clone)]
struct Round1Secrets {
    /// Vector of digits committed with G_vec
    d: Vec<Scalar<Secret, Zero>>,
    /// Blinding factor for d in G
    b_d: Scalar,
    /// Blinding factor for d in H_vec
    l_d: Vec<Scalar<Secret, Zero>>,
    /// Vector of multiplicities
    m: Vec<Scalar<Secret, Zero>>,
    /// Blinding factor for m in G
    b_m: Scalar,
    /// Blinding factor for m in H_vec
    l_m: Vec<Scalar<Secret, Zero>>,
}

#[derive(Debug, Clone)]
struct Round2Commitments {
    /// Reciprocal commitment: R
    R: Point<NonNormal>,
}

#[derive(Debug, Clone)]
struct Round2Secrets {
    /// Reciprocal vector. This is non-zero, but having zero helps in code-dedup
    r: Vec<Scalar<Secret, Zero>>,
    /// Blinding factor for r in G
    b_r: Scalar,
    /// Blinding factor for r in H_vec
    l_r: Vec<Scalar<Secret, Zero>>,
}

#[derive(Debug, Clone)]
struct Round3Commitments {
    /// Round 3 blinding commitment S
    S: Point<NonNormal, Public, NonZero>,
}

#[derive(Debug, Clone)]
struct Round3Secrets {
    /// Round 3 blinding factor b_s
    #[allow(dead_code)]
    b_s: Scalar,
    /// Final w_v(T) polynomial
    w: Poly<Secret>,
    /// Final l_v(T) polynomial
    l: Poly<Secret>,
}


/// BP++ Rangeproof Prover state.
/// The prover state across rounds of the protocol.
///
/// # Notation
///
/// In each round of the protocol, the prover computes a commitment of the following form:
///
/// X = b_i * G + <x_i, G_i> + <l_x_i, H_i>. Here
///     - G is the base generator. G_i generators are associated with n_vec in norm argument
/// while H_i generators are associated with l_vec.
///     - X is the output commitment. (in our case: D, M, R, S) for each round
///     - x_i is the witness vector. (in our case: x = {d, m, r, s})
///     - l_x_i is the blinding vector. (in our case: l_x = {b_d, b_m, b_r, b_s})
#[derive(Debug, Clone)]
pub struct Prover<'a>{
    /// The base generators
    gens: &'a BaseGens,
    /// `b` base representation of the value to be proven(2, 4, 8, 16)
    base: u64,
    /// `n` number of bits in the value to be proven(32, 64, 128) in base 2
    num_bits: u64,
    /// The commitments to the values being proven. One commitment each per aggregated proof
    V: Vec<Point>,
    /// The corresponding values committed in V. One value each per aggregated proof
    v: Vec<u64>,
    /// Corresponding blinding factors for the commitments in V. One blinding factor each per aggregated proof
    gamma: Vec<Scalar<Secret, Zero>>,
    /// Round 1 commitments
    r1_comm: Option<Round1Commitments>,
    /// Round 1 secrets
    r1_sec: Option<Round1Secrets>,
    /// Round 2 commitments
    r2_comm: Option<Round2Commitments>,
    /// Round 2 secrets
    r2_sec: Option<Round2Secrets>,
    /// Round 3 commitments
    r3_comm: Option<Round3Commitments>,
    /// Round 3 secrets
    r3_sec: Option<Round3Secrets>,
}

#[derive(Debug, Clone)]
pub struct Verifier<'a>{
    /// The base generators
    gens: &'a BaseGens,
    /// `b` base representation of the value to be proven(2, 4, 8, 16)
    base: u64,
    /// `n` number of bits in the value to be proven(32, 64, 128)
    num_bits: u64,
    /// The commitment to the value
    V: Vec<Point>,
}

#[derive(Debug, Clone)]
pub struct Proof {
    /// Round 1 commitments
    r1_comm: Round1Commitments,
    /// Round 2 commitments
    r2_comm: Round2Commitments,
    /// Round 3 commitments
    r3_comm: Round3Commitments,
    /// norm proof
    norm_proof: NormProof,
}

/// Create a Bulletproofs++ pedersen commitment. For simplicity, we only blind
/// using the first component in H.
/// Create a commit C = vG + gamma*H_0
pub fn commit(gens: &BaseGens, v: u64, gamma: &Scalar<Secret, Zero>) -> Point<NonNormal> {
    let mut bytes = [0u8; 32];
    bytes[24..].copy_from_slice(&v.to_be_bytes());
    let v = Scalar::<Secret, Zero>::from_bytes(bytes).unwrap();
    let h_0 = gens.H_vec[0];
    g!(v * G + gamma * h_0).non_zero().expect("Zero commitment")
}

impl<'a> Prover<'a> {

    /// Number of proofs to aggregate
    pub fn num_proofs(&self) -> usize {
        self.V.len()
    }

    /// Creates a new prover instance.
    pub fn new(gens: &'a BaseGens, base: u64, num_bits: u64, V: Vec<Point>, v: Vec<u64>, gamma: Vec<Scalar<Secret, Zero>>) -> Self {
        assert!(base.is_power_of_two());
        assert!(num_bits.is_power_of_two());
        assert!(num_bits >= crate::log(base as usize) as u64);
        assert!(gens.H_vec.len() == 8);
        Self { gens, base, num_bits, V, v, gamma, r1_comm: None, r1_sec: None, r2_comm: None, r2_sec: None, r3_comm: None, r3_sec: None }
    }

    /// Obtain the number of digits in the base representation
    /// Num of digits in single proof times the number of proofs
    fn total_num_digits(&self) -> usize {
        self.num_digits_per_proof() * self.num_proofs()
    }

    /// Obtain the number of digits in the base representation
    fn num_digits_per_proof(&self) -> usize {
        self.num_bits as usize/ crate::log(self.base as usize)
    }

    /// Round 1: Commit to the base representation of the value and multiplicities
    ///
    /// # The digits commitment: D
    ///
    /// The prover first computes the base [Prover].base representation of the value to be proven.
    /// The computes the commitment D = b_d * G + <d_i, G_i> + <l_d_i, H_i> where d_i
    /// is the i-th digit of the base b representation of the value to be proven. The values
    /// b_d is chosen randomly, while l_d_i is chosen according to _some_ constraint that we will
    /// explain later. Informally, b_d being random is sufficient to prove that the commitment is hiding.
    ///
    /// When aggregating proofs, d_i is the concatenation of the base b representation of all values.
    /// For example, base 4, num_bits = 4, v = [9, 13] (two digits per value).
    ///             d_vec = [1, 2, 1, 3]
    ///                     (1, 2) (1, 3)
    ///                     (4*2 + 1) (4*3 + 1)
    ///                      9        13
    ///
    /// # The multiplicity commitment: M
    ///
    /// The prover computes the commitment M = b_m * G + <m_i, G_i> + <l_m_i, H_i> where m_i
    /// is the multiplicity of the i-th digit in the base b representation of the value to be proven.
    /// The values b_m, and l_m_i are chosen uniformly at random. Similar to the digits commitment,
    /// b_m being random is sufficient to prove that the commitment is hiding. Multiplicity denotes
    /// the number of times a digit appears in the base b representation of the value to be proven.
    ///
    /// Now, there are two choices for how we want to commit the multiplicities when aggregating proofs.
    /// 1) Inline multiplicity mode: In this mode, the prover commits to the multiplicities of all digits
    /// one after another by concatenating the base b representation of all values.
    /// For the above example, this would be: a) m_vec for 9 = [0, 1, 1, 0] and m_vec for 13 = [0, 1, 0, 1]
    /// The final m_vec would be [0, 1, 1, 0, 0, 1, 0, 1].
    /// 2) Shared multiplicity mode: In this mode, the prover commits to the multiplicities of all digits
    ///   in the base b representation of all values. For example, base 4, num_bits = 4, v = [9, 13] (two digits per value).
    ///   For the above example, the m_vec would be [0, 1, 1, 0] + [0, 1, 0, 1] = [0, 2, 1, 1].
    ///
    /// For the implementation, we use the shared multiplicity mode. The current implementation is not
    /// compatible for multi-party proving, since the prover needs to know the multiplicities of all
    /// digits in the base b representation of all values. We do not concern with this for now.
    fn prove_round_1<R: CryptoRng + RngCore>(&mut self, rng: &mut R) {
        let num_base_bits = crate::log(self.base as usize);
        let num_digits_per_proof = self.num_digits_per_proof();
        let total_num_digits = self.total_num_digits();

        let mut d = Vec::with_capacity(total_num_digits);
        for v in self.v.iter() {
            let mut v1 = *v;
            for _ in 0..num_digits_per_proof {
                d.push(v1 % self.base);
                v1 = v1 >> num_base_bits;
            }
        }

        // Shared multiplicity mode for now.
        let mut m = vec![0; self.base as usize];
        for dig in d.iter() {
            m[*dig as usize] += 1u64;
        }

        let d = d.into_iter().map(|x| Scalar::from(x as u32)).collect::<Vec<_>>();
        let m = m.into_iter().map(|x| Scalar::from(x as u32)).collect::<Vec<_>>();

        let l_m = std::iter::repeat(Scalar::random(rng).mark_zero()).take(6).collect::<Vec<_>>();
        let mut l_d = std::iter::repeat(Scalar::zero()).take(6).collect::<Vec<_>>();
        l_d[4] = -l_m[5].clone();
        l_d[2] = -l_m[3].clone();
        let (b_d, D) = bp_pp_comm(rng, &self.gens, &d, &l_d);
        let (b_m, M) = bp_pp_comm(rng, &self.gens, &m, &l_m);

        self.r1_sec = Some(Round1Secrets { d, b_d, l_d, m, b_m, l_m });
        self.r1_comm = Some(Round1Commitments { D, M });
    }


    /// Prover Round 2: Prover has committed to d_vec and m_vec in the previous round. Received challenge e.
    ///
    /// # The reciprocal commitment: R
    ///
    /// The prover computes the commitment R = b_r * G + <r_i, G_i> + <l_r_i, H_i> where r_i = (1/ (e + d_i))
    /// l_r_i are chosen to be all zeros. As before, the values b_r being random is sufficient to prove that the commitment is hiding.
    ///
    fn prove_round_2<R: CryptoRng + RngCore>(&mut self, rng: &mut R, e: Scalar<Public>) {
        // compute r_i = (1/ (e + d_i))
        let r = self.r1_sec.as_ref().unwrap().d.iter().
            map(|x| s!(e + x).non_zero().unwrap().invert().mark_zero()).collect::<Vec<_>>();

        let l_r = std::iter::repeat(Scalar::zero()).take(6).collect::<Vec<_>>();
        let (b_r, R) = bp_pp_comm(rng, &self.gens, &r, &l_r);
        self.r2_sec = Some(Round2Secrets { r, b_r, l_r});
        self.r2_comm = Some(Round2Commitments { R });
    }

    /// Prover Round 3: Prover has committed to r_vec in the previous round.
    ///                 Received challenge (x, y, q, lambda). Already has e from round 1
    ///
    /// # Witness algebraic relations:
    ///
    /// There are three relations of interest that we need to prove amongst the committed values. We will first
    /// explain the protocol without aggregation, and then explain how to aggregate the proofs.
    /// 1) v = <d_i, b^i> // We refer to this as "Sum value constraint"
    /// 2) r_i = (1/ (e + d_i)) // We refer to this as "Reciprocal value constraint"
    /// 3) <m_i, (1 / (e + i))> = <r_i, 1> // We refer to this as "Range check constraint"
    ///
    /// 3) is the most interesting one and a core contribution of BP++ paper. This proves that
    /// all the digits are in the range [0, b-1]. This can intuitively seen as follows:
    /// Sum_j(m_j/e + i) = Sum_i(1/(e + d_i)) where j = 0..b-1, i = 0..num_digits
    ///
    /// Since e is a random challenge, the above equation is true with high probability for all X.
    /// Sum_j(m_j/X + i) = Sum_i(1/(X + d_i)). Meaning, that d_i are representable using only
    /// (1/X + i) poles where i = 0..b-1. Therefore, d_i must be in the range [0, b-1].
    ///
    /// # Mapping to norm argument:
    ///
    /// To reduce this to norm argument, we construct n and l as follows:
    /// n_vec = s_vec + m_vec*T + d_vec*T^2 + r_vec*T^3 + alpha_m_vec*T^4 + alpha_d_vec*T^3 + alpha_r_vec*T^2
    /// l_vec = l_s_vec + l_m_vec*T + l_d_vec*T^2 + l_r_vec*T^3 + 2*gamma*T^5 (blinding factor)
    /// C = S + M*T + D*T^2 + R*T^3 + 2*V*T^5 + _P_ (P is some public value that we will compute as we proceed)
    ///
    /// P = 0
    /// P += <alpha_m_vec*t^4, G_vec> + <alpha_d_vec*t^3, G_vec> + <alpha_r_vec*t^2, G_vec> (We will update P as we balance other constraints)
    /// The values t denote concrete challenges, while T denotes the unknown challenge. Prover does not know `t` and
    /// must make sure that the above equation holds for all `t`.
    ///
    /// There are a few important points to note here:
    /// 1) All of the vectors are parameterized over unknown T. We want the norm argument to hold for all T,
    /// and in the co-efficient of T^5, is where we will check all our constraints. All other co-efficients
    /// of T^i will be made zero by choosing the l_s_i vector adaptively. In detail, we will choose l_s_i
    /// such that C, n_vec, l_vec following the relation in norm argument.
    /// C = <n_vec, G> + <l_vec, H> + (|n_vec|_q + <l_vec, c_vec>) G for all T.
    /// Here c_vec = y*[T, T^2, T^3, T^4, T^6, T^7, 0, 0]. Crucially, this is missing T^5, which is where we
    /// will check our constraints.
    /// Because we don't know the value of T(verifier chosen challenge from next round), we must choose l_s_i
    /// such that C, n_vec, l_vec following the relation in norm argument for all T. We can do this by expanding the expression
    /// and solving for l_s_i. But crucially, l_s_i cannot interfere with the co-efficients of T^5. l_s_i also cannot
    /// balance co-efficients above T^7. This is not an issue, because this simply translates into some constraints in
    /// choosing our blinding values. Refering back to Round 1, we can now see why we needed l_d(4) = -l_m(5). Skipping
    /// some calculation, if we expand n_vec here, we can see that co-eff of T^8 can only be zero is l_d(4) = -l_m(5).
    ///
    /// 2) We have also added public constants alpha_m_vec, alpha_d_vec, alpha_r_vec to the n_vec. These would be where
    /// we would check our relations. m_vec which has a T power 1, has a corresponding alpha_m_vec with T power 4 so that
    /// when multiplied, the result is in T^5 is alpha_m_vec. Similarly, d_vec has a T power 2, and alpha_d_vec has a
    /// T power 3. This is because we want to check the relations in T^5. We will see how this is done in the next step.
    ///
    /// # Combining constraints with multiple challenges:
    ///
    /// This is a general principle in cryptography and snarks. We can combine multiple constraints into one by
    /// using challenges. If C1 and C2 are two constraints, we can combine them into one constraint C by using
    /// a challenge x. C = C1 + x*C2. This can be extended to multiple constraints. If we have C1, C2, .. Ci.. Cn,
    /// we can use a single challenge q to combine all of them into one constraint C.
    /// C = C1 + q*C2 + q^2*C3 + ... + q^(n-1)*Cn. In the next section, we describe which challenges separate
    /// the constraints.
    ///
    /// # Diving into constraints:
    ///
    /// 1) Sum value constraint: We want to check that v = <d_i, b^i>. If we choose alpha_d_vec = [b^0/q^1, b^1/q^2, b^2/q^3, ...], then
    /// we can check this by checking that <d_i, alpha_d_vec>_q (q weighted norm) = v. This nicely cancels out the q^i
    /// that would have resulted from q weighted norm and brings everything without a power of Q. challenge constraints:
    /// (Q^0, X^0, Y^0)
    ///
    /// 2) Reciprocal constraint: We want to check that 1/(e + d_i) = r_i. We choose alpha_r1 = [e, e, e, ..e_n].
    /// When computing |n_vec|_q = |d_vec*T^2 + r_vec^3 + alpha_r_vec*T^2 + alpha_d_vec*T^3 + ....|_q.
    ///
    /// Let's consider the co-eff of q^i and x^0 = 2(d_i*r_i + e*r_i) = 2.
    /// (As per definition of r_i = 1/(e + d_i) =>  r_i*e + r_i*d_i = 1). To check against the constant 2, Verifier adds
    /// a commitment P += 2*T^5*<1_vec, q_pows_vec>G (We will keep on adding more terms to P later).
    ///
    /// So, challenges constraints at Q^i, X^0, Y^0 ensure all the n reciprocal constraints are satisfied.
    ///
    /// 3) Range check constraint: (Check each d_i in [0 b-1])
    ///
    /// Using the main theorem of set membership, we want to check the following:
    ///
    /// Sum_j(m_j/X + i) = Sum_i(1/(X + d_i)) = Sum_i(r_i) where j = 0..b-1, i = 0..n-1.
    /// To do this, we choose alpha_m_vec = [1/(e + 0), 1/(e + 1), 1/(e + 2), ... 1/(e + b-1)].
    /// and alpha_r2_vec = x*[1/q^1, 1/q^2, 1/q^3, ...].
    ///
    /// So, the challenge constraints in Q^0, X^1, Y^0 ensures these constraints are satisfied. Note that the challenge
    /// Y is not really used in these constraints. Y is used to separate out the terms coming in from the linear side(l_vec)
    /// into the the verification equation.
    ///
    ///
    /// # Balancing out everything else:
    ///
    /// We only need to deal with co-effs of T^0, T^5, and T^8 onwards. The co-effs of T^1, T^2, T^3, T^4, T^6, T^7 are
    /// can easily be made zero by choosing l_s_i adaptively. We simply state the constraints here, the constraints are
    /// computed by making sure (n_vec, l_vec and C, c_vec) follow the norm relation for all T's.
    ///
    /// T^0: Choose b_s = |s|^2_q.
    /// T^8: ld_vec(4) = -lm_vec(5)
    /// T^5: ld_vec(2) = -lm_vec(3)
    ///
    /// In our construction, all of the witness values that we want to enforce constraints are in n_vec. We have to
    /// make sure none of the terms from l_vec interfere with the co-efficients of T^5. This is done by choosing
    /// challange y and making c_vec = y*[T^1, T^2, T^3, T^4, T^6, T^7]. This ensure that resultant co-effs that
    /// can interfere with T^5 coming from linear side(l_vec side) are always multiplied by y. Overall, our verification
    /// equation looks something like:
    ///
    /// T^5 = Q^0X^0Y^0(a) + Q^iX^0Y^0(b) + Q^0X^1Y^0(c) + Q^0X^0Y^1(d)
    /// (a) = Sum-value constraint (1 total constraint)
    /// (b) = Reciprocal constraint in Q^i (n total contraints)
    /// (c) = Range check constraint in Q^0, X^1, Y^0 (1 total constraints)
    /// (d) = Linear side (l_vec side) in Y^1 (1 total constraints)
    ///
    /// The separation of these constraints by different challenges and using the schwartz-zippel lemma, we can
    /// say that all of (a), (b), (c) and (d) are satisfied with high probability. Which is some rough intuition as to why the
    /// protocol is sound. Reasoning about Zk is slightly complicated and we skip that for now.
    ///
    /// Lastly, we also need to add cross public terms to P, which are: (Restating all terms again)
    /// P = 0
    /// P += <alpha_m_vec*t^4, G_vec> + <alpha_d_vec*t^3, G_vec> + <alpha_r1_vec*t^2, G_vec> + <alpha_r2_vec*t^2, G_vec> // Commitments to alpha_i in G_vec
    /// P += 2*T^5*<alpha_d_vec, alpha_r2>*G // Reciprocal constraint public term i G // Refered as v_hat1 in code
    /// P += 2*T^5*x<q_pow_inv*alpha_d_vec, alpha_r1> // Range check constraint public term in G // Refered as v_hat2 in code
    /// P += 2*T^5*<1_vec, q_pows_vec>G // Sum value constant in G // Refered as v_hat3 in code
    /// P += 2*x^2T^8*|alpha_m|_q*G // T^8 public term in G // Refered as v_hat4 in code
    ///
    fn prove_round_3<R: CryptoRng + RngCore>(&mut self, rng: &mut R, x: Scalar<Public>, y: Scalar<Public>, q: Scalar<Public>, e: Scalar<Public>, lambda: Scalar<Public>) {
        let d = self.r1_sec.as_ref().unwrap().d.clone();
        let m = self.r1_sec.as_ref().unwrap().m.clone();
        let r = self.r2_sec.as_ref().unwrap().r.clone();
        let l_d = self.r1_sec.as_ref().unwrap().l_d.clone();
        let l_m = self.r1_sec.as_ref().unwrap().l_m.clone();
        let l_r = self.r2_sec.as_ref().unwrap().l_r.clone();
        let q_inv_pows = q_inv_pows(q, self.gens.G_vec.len());

        let alpha_r = alpha_r_q_inv_pow(self.total_num_digits(), x, e, &q_inv_pows);
        let alpha_d = alpha_d_q_inv_pow(self.base, self.num_digits_per_proof(), self.num_proofs(), &q_inv_pows, lambda);
        let alpha_m = alpha_m_q_inv_pows(e, x, self.base as usize, &q_inv_pows);
        let alpha_m = alpha_m.into_iter().map(|x| x.secret()).collect::<Vec<_>>();

        let t_2 = add_vecs(&d, &alpha_r);
        let t_3 = add_vecs(&r, &alpha_d);

        let s = std::iter::repeat(Scalar::random(rng).mark_zero()).take(self.gens.G_vec.len()).collect::<Vec<_>>();
        // let s = std::iter::repeat(Scalar::one().mark_zero()).take(self.gens.G_vec.len()).collect::<Vec<_>>();

        let w_vec = Poly{
            coeffs: vec![s.clone(), m.clone(), t_2, t_3, alpha_m],
        };

        let w_w_q = w_vec.w_q_norm(q);
        let y_inv = y.invert();
        let y = y.mark_zero();
        let c = c_poly(y);
        let mut gamma_delta = Scalar::zero();
        let mut lambda_pow_i = s!(1).public();
        for gamma in self.gamma.iter() {
            gamma_delta = s!(gamma_delta + 2*gamma*lambda_pow_i);
            lambda_pow_i = s!(lambda_pow_i * lambda).public();
        }
        let mut l_vec = Poly {
            coeffs: vec![Vec::new(), l_m, l_d, l_r, Vec::new(), vec![gamma_delta], Vec::new(), Vec::new()],
        };
        let l_vec_w_q = l_vec.mul_c(&c);
        let mut l_s = Vec::with_capacity(self.gens.H_vec.len());
        for i in 0..self.gens.H_vec.len() {
            let w_w_q_i = &w_w_q[i];
            let l_vec_w_q_i = &l_vec_w_q[i];
            l_s.push(s!(-w_w_q_i - l_vec_w_q_i));
        }
        let (b_m, b_d, b_r) = (&self.r1_sec.as_ref().unwrap().b_m, &self.r1_sec.as_ref().unwrap().b_d, &self.r2_sec.as_ref().unwrap().b_r);
        let arr = [b_m, b_d, b_r];
        for (i, b_i) in arr.into_iter().enumerate() {
            let l_s_i = &l_s[i + 1];
            l_s[i + 1] = s!(l_s_i + b_i);
        }
        l_s.remove(5);
        l_s.remove(0);
        for l_s_i in l_s.iter_mut() {
            let borrow_ls_i = &*l_s_i;
            *l_s_i = s!( borrow_ls_i * y_inv);
        }
        l_vec.coeffs[0] = l_s.clone();
        // Compute b_s = q^(i+1)s[i]
        let mut q_pow = q.clone();
        let mut b_s = Scalar::zero();
        let s = &w_vec.coeffs[0];
        for i in 0..s.len() {
            let s_i = &s[i];
            b_s = s!(b_s + q_pow * s_i * s_i);
            q_pow = s!(q_pow * q).public();
        }
        // Compute S = s*G_vec + l_s*H_vec + b_s*G
        let mut S = g!(b_s * G);
        for (g, w_i) in self.gens.G_vec.iter().zip(s.iter()) {
            S = g!(S + w_i * g);
        }
        for (h, w_i) in self.gens.H_vec.iter().zip(l_s.iter()) {
            S = g!(S + w_i * h);
        }

        // Recompute the secret w
        self.r3_sec = Some(Round3Secrets { b_s: b_s.non_zero().unwrap(), w: w_vec, l: l_vec });
        self.r3_comm = Some(Round3Commitments { S: S.non_zero().unwrap() });
    }

    fn r1_challenge_e(&self, t: &mut Transcript) -> Scalar<Public> {
        r1_challenge_e(t, self.r1_comm.as_ref().unwrap(), self.num_bits, self.base, &self.V)
    }

    fn r2_challenges(&self, t: &mut Transcript) -> (Scalar<Public>, Scalar<Public>, Scalar<Public>, Scalar<Public>, Scalar<Public>) {
        r2_challenges(t, self.r2_comm.as_ref().unwrap())
    }

    fn r3_challenge(&self, t: &mut Transcript) -> Scalar<Public> {
        r3_challenge(t, self.r3_comm.as_ref().unwrap())
    }

    /// Round 4:
    /// Run the norm argument on the obtained challenge t. If we have sent the correct commiments, we only
    /// need to evaluate the poly w_vec at t and the poly l_vec at t. and run the norm argument on them
    fn proof(self, y: Scalar<Public>, t: Scalar<Public>, r: Scalar<Public>, transcript: &mut Transcript) -> Proof {
        let r3_sec = self.r3_sec.unwrap();
        let w_eval = r3_sec.w.eval(t);
        let mut l_eval = r3_sec.l.eval(t);
        l_eval.push(Scalar::zero());
        l_eval.push(Scalar::zero());
        let t_pows = t_pows(t, self.gens.H_vec.len());

        let (t2, t3, t4, t6, t7) = (t_pows[2], t_pows[3], t_pows[4], t_pows[6], t_pows[7]);
        let c_vec = vec![
            s!(y* t).public().mark_zero(),
            s!(y* t2).public().mark_zero(),
            s!(y* t3).public().mark_zero(),
            s!(y* t4).public().mark_zero(),
            s!(y* t6).public().mark_zero(),
            s!(y* t7).public().mark_zero(),
            Scalar::zero(),
            Scalar::zero(),
        ];

        let norm_prf = norm_arg::NormProof::prove(
            transcript, self.gens.clone(), w_eval.clone(), l_eval.clone(), c_vec, r
        );
        Proof {
            r1_comm: self.r1_comm.unwrap(),
            r2_comm: self.r2_comm.unwrap(),
            r3_comm: self.r3_comm.unwrap(),
            norm_proof: norm_prf,
        }
    }

    pub fn prove<R: RngCore + CryptoRng>(mut self, rng: &mut R, transcript: &mut Transcript) -> Proof {

        // Round 1
        self.prove_round_1(rng);
        let e = self.r1_challenge_e(transcript);

        // Round 2
        self.prove_round_2(rng, e);
        let (x, y, r, q, lambda) = self.r2_challenges(transcript);

        // Round 3
        self.prove_round_3(rng, x, y, q, e, lambda);
        let t = self.r3_challenge(transcript);

        // Round 4
        self.proof(y, t, r, transcript)
    }
}

impl<'a> Verifier<'a> {

    pub fn new(gens: &'a BaseGens, base: u64, num_bits: u64, V: Vec<Point>) -> Self {
        assert!(base.is_power_of_two());
        assert!(num_bits.is_power_of_two());
        assert!(num_bits >= crate::log(base as usize) as u64);
        assert!(gens.H_vec.len() == 8);
        Self { gens, base, num_bits, V }
    }

    /// Obtain the number of digits
    fn num_digits_per_proof(&self) -> usize {
        (self.num_bits / crate::log(self.base as usize) as u64) as usize
    }

    fn num_proofs(&self) -> usize {
        self.V.len()
    }

    fn total_num_digits(&self) -> usize {
        self.num_digits_per_proof() * self.num_proofs()
    }

    fn r1_challenge_e(&self, t: &mut Transcript, prf: &Proof) -> Scalar<Public> {
        r1_challenge_e(t, &prf.r1_comm, self.num_bits, self.base, &self.V)
    }

    fn r2_challenges(&self, t: &mut Transcript, prf: &Proof) -> (Scalar<Public>, Scalar<Public>, Scalar<Public>, Scalar<Public>, Scalar<Public>) {
        r2_challenges(t, &prf.r2_comm)
    }

    fn r3_challenge(&self, t: &mut Transcript, prf: &Proof) -> Scalar<Public> {
        r3_challenge(t, &prf.r3_comm)
    }

    /// Compute the public offsets for P in along G_vec.
    /// This computes
    /// P = alpha_d_vec * t^3 + alpha_r1_vec * t^2 + alpha_r2_vec * t^2 + alpha_m_vec * t^4
    fn g_vec_pub_offsets(&self, e: Scalar<Public>, x: Scalar<Public>, q: Scalar<Public>, t: Scalar<Public>, lambda: Scalar<Public>) -> Vec<Scalar<Public, Zero>> {
        let t_pows = t_pows(t, self.gens.H_vec.len());
        let q_inv_pows = q_inv_pows(q, self.gens.G_vec.len());
        let num_digits = self.num_digits_per_proof();
        let num_proofs = self.num_proofs();
        let alpha_d = alpha_d_q_inv_pow(self.base, num_digits, num_proofs, &q_inv_pows, lambda);
        let alpha_r = alpha_r_q_inv_pow(self.total_num_digits(), x, e, &q_inv_pows);
        let alpha_m = alpha_m_q_inv_pows(e, x, self.base as usize, &q_inv_pows);

        let alpha_d_t_3 = scalar_mul_vec(&alpha_d, t_pows[3]);
        let alpha_r_t_2 = scalar_mul_vec(&alpha_r, t_pows[2]);
        let alpha_m_t_4 = scalar_mul_vec(&alpha_m, t_pows[4]);

        let res = add_vecs(&alpha_d_t_3, &alpha_r_t_2);
        add_vecs(&res, &alpha_m_t_4)
    }

    /// Compute the public offsets for P in along G
    /// This computes v_hat as (explained in prover round 3)
    /// P += 2*T^5*<alpha_d_vec, alpha_r2>*G // Reciprocal constraint public term i G // Refered as v_hat1 in code
    /// P += 2*T^5*x<q_pow_inv*alpha_d_vec, alpha_r1> // Range check constraint public term in G // Refered as v_hat2 in code
    /// P += 2*T^5*<1_vec, q_pows_vec>G // Sum value constant in G // Refered as v_hat3 in code
    /// P += 2*x^2T^8*|alpha_m|_q*G // T^8 public term in G // Refered as v_hat4 in code
    fn g_offset(&self, e: Scalar<Public>, x: Scalar<Public>, q: Scalar<Public>, t: Scalar<Public>, lambda: Scalar<Public>) -> Scalar<Public, Zero> {
        let t_pows = t_pows(t, self.gens.H_vec.len());
        let q_inv_pows = q_inv_pows(q, self.gens.G_vec.len());
        let q_pows = q_pows(q, self.gens.G_vec.len());

        let alpha_d = alpha_d(self.base, self.num_digits_per_proof(), self.num_proofs(), lambda);
        let alpha_r2 = alpha_r2(self.total_num_digits(), e);
        let alpha_d_q_inv_pow = alpha_d_q_inv_pow(self.base, self.num_digits_per_proof(), self.num_proofs(), &q_inv_pows, lambda);
        let alpha_r = alpha_r(self.total_num_digits(), x);
        let alpha_m_q_inv_pows = alpha_m_q_inv_pows(e, x, self.base as usize, &q_inv_pows);
        let alpha_m = alpha_m(e, x, self.base as usize);

        let t5 = &t_pows[5];
        let t4 = &t_pows[4];
        let two_t_5 = s!(t5 + t5).mark_zero().public();
        let two_t_5_v = vec![two_t_5; self.total_num_digits()];
        let v_hat_1 = dot(&two_t_5_v, &q_pows);

        let v_hat_2 = dot(&alpha_d, &alpha_r2);
        let v_hat_2 = s!(v_hat_2 * two_t_5).mark_zero().public();

        let v_hat_3 = dot(&alpha_d_q_inv_pow, &alpha_r);
        let v_hat_3 = s!(v_hat_3 * two_t_5).mark_zero().public();

        let v_hat_4 = dot(&alpha_m_q_inv_pows, &alpha_m);
        let v_hat_4 = s!(v_hat_4 * t4 * t4).mark_zero().public();

        s!(v_hat_1 + v_hat_2 + v_hat_3 + v_hat_4).mark_zero().public()
    }

    /// Compute the commitment C and run the norm arg on it
    /// C = S + t*M + t^2*D + t^3*R + 2t^5*V + P
    /// P = <g_vec_pub_offsets, G_vec> + g_offset*G
    pub fn verify(&self, transcript: &mut Transcript, prf: &Proof) -> bool {
        let e = self.r1_challenge_e(transcript, prf);
        let (x, y, r, q, lambda) = self.r2_challenges(transcript, prf);
        let t = self.r3_challenge(transcript, prf);
        let y = y.mark_zero();
        let t_pows = t_pows(t, self.gens.H_vec.len());

        let (t2, t3, t4, t6, t7) = (t_pows[2], t_pows[3], t_pows[4], t_pows[6], t_pows[7]);
        let c_vec = vec![
            s!(y* t).public(),
            s!(y* t2).public(),
            s!(y* t3).public(),
            s!(y* t4).public(),
            s!(y* t6).public(),
            s!(y* t7).public(),
            Scalar::zero(),
            Scalar::zero(),
        ];

        // Compute the commitment to the public values
        let g_offset = self.g_offset(e, x, q, t, lambda);
        let g_vec_pub_offsets = self.g_vec_pub_offsets(e, x, q, t, lambda);

        let Proof { r1_comm, r2_comm, r3_comm, norm_proof } = prf;
        let (S, M, D, R) = (&r3_comm.S, &r1_comm.M, &r1_comm.D, &r2_comm.R);
        let (t2, t3, t5) = (&t_pows[2], &t_pows[3], &t_pows[5]);

        let mut C = g!(S + t*M + t2*D + t3*R);
        let mut lambda_pow_i = s!(1);
        for V_i in self.V.iter() {
            let coeff = s!(lambda_pow_i * 2 * t5);
            C = g!(C + coeff*V_i);
            lambda_pow_i = s!(lambda_pow_i * lambda);
        }
        let P = secp256kfun::op::lincomb(g_vec_pub_offsets.iter(), &self.gens.G_vec);
        let C = g!(C + P + g_offset * G);

        norm_proof.verify(&self.gens, transcript, C.normalize(), &c_vec, r)
    }
}


fn r1_challenge_e(t: &mut Transcript, r1_comm: &Round1Commitments, n: u64, b: u64, V: &[Point]) -> Scalar<Public> {
    t.append_message(b"Bulletproofs++");
    for V_i in V {
        t.append_message(&V_i.to_bytes());
    }
    t.append_message(&n.to_le_bytes());
    t.append_message(&b.to_le_bytes());
    t.append_message(&r1_comm.D.normalize().to_bytes());
    t.append_message(&r1_comm.M.normalize().to_bytes());
    merlin_scalar(t, b"e")
}

fn r2_challenges(t: &mut Transcript, r2_comm: &Round2Commitments) -> (Scalar<Public>, Scalar<Public>, Scalar<Public>, Scalar<Public>, Scalar<Public>) {
    t.append_message(&r2_comm.R.normalize().to_bytes());
    let x = merlin_scalar(t, b"x");
    let y = merlin_scalar(t, b"y");
    let r = merlin_scalar(t, b"r");
    let lambda = Scalar::one();
    let q = s!(r * r).public();
    (x, y, r, q, lambda)
}

fn r3_challenge(t: &mut Transcript, r3_comm: &Round3Commitments) -> Scalar<Public> {
    t.append_message(&r3_comm.S.normalize().to_bytes());
    merlin_scalar(t, b"t")
}

fn bp_pp_comm<R: CryptoRng + RngCore>(rng: &mut R, gens: &BaseGens, w: &[Scalar<Secret, Zero>], l: &[Scalar<Secret, Zero>]) -> (Scalar, Point<NonNormal>) {
    let b_r = Scalar::random(rng);

    let mut res = g!(b_r * G).mark_zero();
    for (g, w_i) in gens.G_vec.iter().zip(w.iter()) {
        res = g!(res + w_i * g);
    }
    for (h, l_i) in gens.H_vec.iter().zip(l.iter()) {
        res = g!(res + l_i * h);
    }
    (b_r, res.non_zero().unwrap())
}

fn merlin_scalar(t: &mut Transcript, _label: &'static [u8]) -> Scalar<Public> {
    let bytes = t.challenge_bytes();
    Scalar::from_bytes(bytes).unwrap().non_zero().unwrap()
}

// Compute a vector with powers of q (q, q^2, q^3, ...)
fn q_pows(q: Scalar<Public>, n: usize) -> Vec<Scalar<Public>> {
    let mut res = Vec::with_capacity(n as usize);
    let mut q_pow = q;
    for _ in 0..n {
        res.push(q_pow);
        q_pow = s!(q_pow * q).public();
    }
    res
}

// compute powers of t with (1, t, t^2, t^3, ...)
fn t_pows(t: Scalar<Public>, n: usize) -> Vec<Scalar<Public>> {
    let mut res = Vec::with_capacity(n as usize);
    let mut t_pow = Scalar::one();
    for _ in 0..n {
        res.push(t_pow);
        t_pow = s!(t_pow * t).public();
    }
    res
}

// Add two vectors of scalars
fn add_vecs<S: Secrecy, S2: Secrecy>(a: &[Scalar<S, Zero>], b: &[Scalar<S2, Zero>]) -> Vec<Scalar<S, Zero>> {
    let (a_len, b_len) = (a.len(), b.len());
    let res_len = std::cmp::max(a_len, b_len);
    let mut res = Vec::with_capacity(res_len);
    for i in 0..res_len {
        let a_i = a.get(i).cloned().unwrap_or(s!(0).set_secrecy());
        let b_i = b.get(i).cloned().unwrap_or(s!(0).set_secrecy());
        res.push(s!(a_i + b_i).set_secrecy());
    }
    res
}

// Compute the dot product of two vectors
fn dot<S: Secrecy, Z2: ZeroChoice>(a: &[Scalar<S, Zero>], b: &[Scalar<Public, Z2>]) -> Scalar<S, Zero> {
    let mut res = Scalar::zero();
    for (a_i, b_i) in a.iter().zip(b.iter()) {
        res = s!(res + a_i * b_i).set_secrecy().mark_zero();
    }
    res
}

// Multiply every element of a vector by a scalar
fn scalar_mul_vec<S: Secrecy, Z: ZeroChoice>(a: &[Scalar<S, Z>], b: Scalar<Public>) -> Vec<Scalar<S, Zero>> {
    let mut res = Vec::with_capacity(a.len());
    for a_i in a.iter() {
        res.push(s!(a_i * b).set_secrecy().mark_zero());
    }
    res
}

// Hadamard product of two vectors of scalars
fn hadamard<S: Secrecy, Z: ZeroChoice>(a: &[Scalar<S, Z>], b: &[Scalar<Public>]) -> Vec<Scalar<S, Zero>> {
    // assert_eq!(a.len(), b.len());
    let mut res = Vec::with_capacity(a.len());
    for (a_i, b_i) in a.iter().zip(b.iter()) {
        res.push(s!(a_i * b_i).set_secrecy().mark_zero());
    }
    res
}

// computes powers of q_inv (q^-1, q^-2, q^-3, ...)
fn q_inv_pows(q: Scalar<Public>, n: usize) -> Vec<Scalar<Public>> {
    let mut res = Vec::with_capacity(n as usize);
    let q_inv = q.invert();
    let mut q_inv_pow = q_inv;
    for _ in 0..n {
        res.push(q_inv_pow);
        q_inv_pow = s!(q_inv_pow * q_inv).public();
    }
    res
}

/// Compute a vector of powers of b (1, b, b^2, b^3, ...) X q_inv_pows
/// Size must be number of digits
fn alpha_d_q_inv_pow(b: u64, num_digits: usize, num_proofs: usize, q_inv_pows: &[Scalar<Public>], lambda: Scalar<Public>) -> Vec<Scalar<Public, Zero>> {
    let res = alpha_d(b, num_digits, num_proofs, lambda);
    hadamard(&res, &q_inv_pows)
}

/// Compute a vector of powers of b (1, b, b^2, b^3, ...)
/// Size must be number of digits
fn alpha_d(b: u64, num_digits: usize, num_proofs: usize, lambda: Scalar<Public>) -> Vec<Scalar<Public, Zero>> {
    let b = Scalar::<Public, _>::from(b as u32);
    let mut res = Vec::with_capacity(num_digits as usize);
    let mut lambda_pow_i = Scalar::one();
    for _ in 0..num_proofs {
        let mut b_pow = Scalar::<Public>::one().mark_zero();
        for _ in 0..num_digits {
            res.push(s!(b_pow * lambda_pow_i).public());
            b_pow = s!(b_pow * b).public();
        }
        lambda_pow_i = s!(lambda_pow_i * lambda).public();
    }

    res
}

/// Compute alpha_m = vec![1/e, 1/(e + 1), 1/(e + 2), ...] X q_inv_pows
fn alpha_m_q_inv_pows(e: Scalar<Public>, x: Scalar<Public>, n: usize, q_inv_pows: &[Scalar<Public>]) -> Vec<Scalar<Public, Zero>> {
    let res = alpha_m(e, x, n);
    hadamard(&res, q_inv_pows)
}

/// Compute alpha_m = vec![1/e, 1/(e + 1), 1/(e + 2), ...]
fn alpha_m(e: Scalar<Public>, x: Scalar<Public>, n: usize) -> Vec<Scalar<Public, Zero>> {
    let mut res = Vec::with_capacity(n as usize);
    let mut curr_e = e;
    for _ in 0..n {
        let curr_e_inv = curr_e.invert();
        res.push(s!(curr_e_inv * x).public().mark_zero());
        curr_e = s!(curr_e + 1).public().non_zero().unwrap();
    }
    res
}

/// Compute a vector of scalar -x
fn alpha_r_q_inv_pow(n: usize, x: Scalar<Public>, e: Scalar<Public>, q_inv_pows: &[Scalar<Public>]) -> Vec<Scalar<Public, Zero>> {
    let res = alpha_r(n, x);
    let alpha_r = hadamard(&res, q_inv_pows);
    add_vecs(&alpha_r, &alpha_r2(n, e))
}

/// Compute a vector of scalar -x
fn alpha_r(n: usize, x: Scalar<Public>) -> Vec<Scalar<Public, Zero>> {
    let mut res = Vec::with_capacity(n as usize);
    let minus_one = Scalar::<Public,_>::minus_one().public();
    for _ in 0..n {
        res.push(s!(minus_one * x).public().mark_zero());
    }
    res
}

// Compute a vector of [e, e, e, e]
fn alpha_r2(n: usize, e: Scalar<Public>) -> Vec<Scalar<Public, Zero>> {
    std::iter::repeat(e).map(|e| e.mark_zero()).take(n).collect()
}

// obtain the c poly
fn c_poly(y: Scalar<Public, Zero>) -> Poly<Public> {
    let zero = Scalar::zero();
    Poly {
        coeffs: vec![vec![zero], vec![y], vec![y], vec![y], vec![y], vec![zero], vec![y], vec![y]],
    }
}

// Obtain the non-zero at i position
fn t_pow_in_c(mut i: usize) -> usize {
    i = i + 1; // i >= 0
    if i >= 5 {
        i = i + 1;
    }
    i
}

#[derive(Debug, Clone)]
struct Poly<S: Secrecy>{
    coeffs: Vec<Vec<Scalar<S, Zero>>>,
}

impl<S: Secrecy> Poly<S> {

    // evaluate the poly at t
    fn eval(&self, t: Scalar<Public>) -> Vec<Scalar<Public, Zero>> {
        let mut res = vec![Scalar::zero(); self.coeffs[0].len()];
        let mut t_pow = Scalar::one();
        for coeffs in self.coeffs.iter() {
            for (i, coeff) in coeffs.iter().enumerate() {
                let curr = &res[i];
                res[i] = s!(curr + t_pow * coeff).secret().mark_zero().public();
            }
            t_pow = s!(t_pow * t).public();
        }
        res
    }

    // Compute the inner product of two polynomials
    fn w_q_norm(&self, q: Scalar<Public>) -> Vec<Scalar<S, Zero>> {
        let mut res = vec![Scalar::zero(); 2 * self.coeffs.len() - 1];
        for i in 0..self.coeffs.len() {
            for j in 0..self.coeffs.len() {
                let mut q_pow_i = q;
                let a = &self.coeffs[i];
                let b = &self.coeffs[j];
                let mut inner_prod = Scalar::zero();
                let min_len = a.len().min(b.len());
                for k in 0..min_len {
                    let (a_k, b_k) = (&a[k], &b[k]);
                    inner_prod = s!(inner_prod + a_k * b_k * q_pow_i);
                    q_pow_i = s!(q_pow_i * q).public();
                }
                let res_prev = &res[i + j];
                res[i + j] = s!(res_prev +  inner_prod).set_secrecy::<S>();
            }
        }
        res
    }

    // mul c poly
    fn mul_c(&self, c: &Poly<Public>) -> Vec<Scalar<S, Zero>> {
        let mut res = vec![Scalar::zero(); self.coeffs.len() + c.coeffs.len() - 1];
        for l in 0..self.coeffs.len() {
            let l_vec = &self.coeffs[l];
            for i in 0..l_vec.len() {
                let l_i = &l_vec[i];
                let t_pow_in_c = t_pow_in_c(i);
                if t_pow_in_c >= c.coeffs.len() {
                    continue;
                }
                let c_i = &c.coeffs[t_pow_in_c][0]; // c_vec has exactly one element
                let inner_prod = s!(l_i * c_i);
                let res_prev = &res[l + t_pow_in_c];
                res[l + t_pow_in_c] = s!(res_prev +  inner_prod).set_secrecy();
            }
        }
        res
    }
}

#[cfg(test)]
mod tests{
    use rand::thread_rng;

    use super::*;

    // Test prove and verify
    fn _test_rangeproof(base: u64, num_bits: u64, v: Vec<u64>) {
        let num_h = 8;
        let num_base_bits = crate::log(base as usize) as u64;
        let num_digits_per_proof = num_bits / num_base_bits;
        let num_proofs = v.len() as u64;
        let num_g = (std::cmp::max(num_digits_per_proof, base) * num_proofs)  as u32;
        let mut gamma = vec![];
        for _ in 0..v.len() {
            gamma.push(Scalar::random(&mut thread_rng()).mark_zero());
            // gamma.push(s!(3).mark_zero());
        }

        let gens = BaseGens::new(num_g, num_h);
        let mut V = vec![];
        for (v_i, gamma_i) in v.iter().zip(gamma.iter()) {
            V.push(commit(&gens, *v_i, gamma_i).normalize());
        }
        let prover = Prover::new(&gens, base, num_bits, V.clone(), v, gamma);
        let mut transcript = Transcript::new(b"BPP/tests");
        let prf = prover.prove(&mut thread_rng(), &mut transcript);

        let mut transcript = Transcript::new(b"BPP/tests");
        let verifier = Verifier::new(&gens, base, num_bits, V);
        assert!(verifier.verify(&mut transcript, &prf));
    }

    #[test]
    fn test_rangeproof() {
        _test_rangeproof(2, 4, vec![1, 2, 3, 4]);
        for i in 0..16 {
            _test_rangeproof(2, 4, vec![i]);
            _test_rangeproof(2, 4, vec![i, 15 - i]);
        }
        _test_rangeproof(16, 4, vec![7]);
        _test_rangeproof(16, 8, vec![243]);
        _test_rangeproof(16, 16, vec![12431]);
        _test_rangeproof(16, 32, vec![134132, 14354, 981643, 875431]);
        for _ in 0..10 {
            let mut v = vec![];
            for _ in 0..8 {
                v.push(rand::random::<u64>());
            }
            _test_rangeproof(16, 64, v);
        }
        for _ in 0..10 {
            let v = rand::random::<u64>();
            _test_rangeproof(16, 64, vec![v]);
        }
    }

    #[test]
    fn test_inner_prod() {
        let q = s!(2).public();
        let a = Poly::<Secret> {
            coeffs: vec![
                vec![Scalar::from(1), Scalar::from(2)],
                vec![Scalar::from(1), Scalar::from(2)],
            ]
        };
        let _b = Poly::<Secret> {
            coeffs: vec![
                vec![Scalar::from(3), Scalar::from(4)],
                vec![Scalar::from(3), Scalar::from(4)],
            ]
        };
        let res = a.w_q_norm(q);
        assert_eq!(res, vec![s!(18), s!(36), s!(18)]);
    }
}
