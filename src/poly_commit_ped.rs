// Section 3.3 of the paper, PolyCommit_Ped

use crate::polynomial::Polynomial;

use amcl_wrapper::group_elem::{GroupElement, GroupElementVector};
use amcl_wrapper::group_elem_g1::{G1, G1Vector};
use amcl_wrapper::group_elem_g2::{G2, G2Vector};
use amcl_wrapper::field_elem::{FieldElement, FieldElementVector};
use amcl_wrapper::extension_field_gt::GT;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PublicKey {
    pub g1_powers: G1Vector,
    pub g2_powers: G2Vector,
    pub h1_powers: G1Vector,
    pub h2_powers: G2Vector,
}

impl PublicKey {
    /// Create new public key. Done by trusted party. `degree` is called `t` in the paper.
    /// The paper says to create powers of only 1 group element, i.e. from G but since we need
    /// type-3 pairings, so creating powers of element in G1 and G2 as `g1` and `g2`. The exponent
    /// is kept same. Similarly for `h`, elements in both groups G1 and G2 are created as `h1` and  
    /// `h2`. Both `h1` and `h2` must have the same discrete log wrt. `g1` and `g2` respectively.
    pub fn new(degree: usize, label: &[u8]) -> Self {
        // secret key, should not be persisted,
        let alpha = FieldElement::random();
        // alpha_vec = 1, alpha, alpha^2, alpha^3, ... alpha^degree
        let alpha_vec = FieldElementVector::new_vandermonde_vector(&alpha, degree + 1);

        // g1 and g2 come from random oracle. It probably is fine if trusted party knows the discrete log of g wrt. h
        let g1 = G1::from_msg_hash(&[label, " : g1".as_bytes()].concat());
        let g2 = G2::from_msg_hash(&[label, " : g2".as_bytes()].concat());

        // h1 and h2 must have the same discrete log wrt. g1 and g2 respectively.
        // r is the discrete log of h1 wrt. g1 and of h2 wrt. g2.
        let r = FieldElement::random();
        let h1 = &g1 * &r;
        let h2 = &g2 * &r;

        // g1_powers = g1, g1^alpha, g1^{alpha^2}, g1^{alpha^3}
        let mut g1_powers = G1Vector::with_capacity(degree+1);
        // g2_powers = g2, g2^alpha, g2^{alpha^2}, g2^{alpha^3}
        let mut g2_powers = G2Vector::with_capacity(degree+1);
        // h1_powers = h1, h1^alpha, h1^{alpha^2}, h1^{alpha^3}
        let mut h1_powers = G1Vector::with_capacity(degree+1);
        // h2_powers = h2, h2^alpha, h2^{alpha^2}, h2^{alpha^3}
        let mut h2_powers = G2Vector::with_capacity(degree+1);
        // skip 1st element since its 1
        for a in alpha_vec.iter().skip(1) {
            // TODO: Add an efficient way since the same group element is used.
            g1_powers.push(&g1 * a);
            g2_powers.push(&g2 * a);
            h1_powers.push(&h1 * a);
            h2_powers.push(&h2 * a);
        }
        // First element of g1_powers should be `g1`.
        g1_powers.insert(0, g1);
        // First element of g2_powers should be `g2`.
        g2_powers.insert(0, g2);
        // First element of h1_powers should be `h1`.
        h1_powers.insert(0, h1);
        // First element of h2_powers should be `h2`.
        h2_powers.insert(0, h2);
        Self { g1_powers, g2_powers, h1_powers, h2_powers }
    }

    pub fn is_valid(&self) -> bool {
        (self.g1_powers.len() == self.g2_powers.len()) && (self.h1_powers.len() == self.h2_powers.len()) && (self.g1_powers.len() == self.h1_powers.len())
    }

    pub fn is_degree_supported(&self, degree: usize) -> bool {
        self.g1_powers.len() >= degree
    }
}

pub struct PolyCommit_Ped {}

impl PolyCommit_Ped {
    /// Commit to a polynomial. Generates a random polynomial as well.
    pub fn commit(poly: &Polynomial, pk: &PublicKey) -> (Polynomial, G2) {
        assert!(pk.is_valid());
        let degree = poly.degree();
        assert!(pk.is_degree_supported(degree));
        let rand_poly = Polynomial::random(degree);
        let commitment = Self::compute_commitment(poly, &rand_poly, pk);
        (rand_poly, commitment)
    }

    /// Verify that the commitment to polynomial matches the expected
    pub fn verify_commitment(poly: &Polynomial, rand_poly: &Polynomial, commitment: &G2, pk: &PublicKey) -> bool {
        assert!(pk.is_valid());
        assert!(pk.is_degree_supported(poly.degree()));
        assert_eq!(poly.degree(), rand_poly.degree());

        // TODO: Reusing `compute_commitment` causes verifier to use constant time multi-exp
        // but the verifier can use variable time.
        let expected_commitment = Self::compute_commitment(poly, &rand_poly, pk);
        &expected_commitment == commitment
    }

    pub fn create_witness(poly: &Polynomial, rand_poly: &Polynomial, i: &FieldElement, pk: &PublicKey) -> (FieldElement, FieldElement, G1) {
        assert!(pk.is_valid());
        assert!(pk.is_degree_supported(poly.degree()));
        assert_eq!(poly.degree(), rand_poly.degree());

        let evaluation = poly.eval(i);
        // dividend = poly - evaluation
        let mut dividend = poly.clone();
        dividend[0] -= &evaluation;
        // divisor = x - i = -i + x
        let divisor = Polynomial(FieldElementVector::from(vec![-i, FieldElement::one()]));
        // witness_poly = dividend / divisor
        let witness_poly = Polynomial::long_division(&dividend, &divisor);

        let evaluation_rand = rand_poly.eval(i);
        // dividend = rand_poly - evaluation
        let mut dividend_rand = rand_poly.clone();
        dividend_rand[0] -= &evaluation_rand;
        // divisor = x - i = -i + x
        let divisor_rand = Polynomial(FieldElementVector::from(vec![-i, FieldElement::one()]));
        // witness_poly_rand = dividend_rand / divisor_rand
        let witness_poly_rand = Polynomial::long_division(&dividend_rand, &divisor_rand);

        // Question: Would witness_poly and witness_poly_rand always be of same degree?
        // Evaluate witness polynomials at `alpha`
        let mut bases = G1Vector::with_capacity(witness_poly.degree() + witness_poly_rand.degree());
        let mut exps = FieldElementVector::with_capacity(witness_poly.degree() + witness_poly_rand.degree());
        // TODO: Too many clonings, refactor multi_scalar_mul_*
        for i in 0..=witness_poly.degree() {
            bases.push(pk.g1_powers[i].clone());
            exps.push(witness_poly[i].clone());
        }
        for i in 0..=witness_poly_rand.degree() {
            bases.push(pk.h1_powers[i].clone());
            exps.push(witness_poly_rand[i].clone());
        }
        let witness = bases.multi_scalar_mul_const_time(&exps).unwrap();
        (evaluation, evaluation_rand, witness)
    }

    pub fn verify_eval(commitment: &G2, i: &FieldElement, eval_i: &FieldElement, eval_i_rand: &FieldElement, witness: &G1, pk: &PublicKey) -> bool {
        // e(g1, commitment) == e(witness, g2^alpha/g2^i) * e(g1^eval_i*h1^eval_i_rand, g2)
        // e(witness, g2^alpha/g2^i) * e(g1^eval_i*h1^eval_i_rand, g2) * e(g1, commitment)^-1 == 1
        // e(witness, g2^alpha/g2^i) * e(g1^eval_i*h1^eval_i_rand, g2) * e(g1^-1, commitment) == 1
        // Compute the above using a multi-pairing
        let mut pairing_elems = vec![];
        let g2_i = &pk.g2_powers[0] * i;    // g2^i
        let g2_alpha_divide_g2_i = &pk.g2_powers[1] - g2_i;      // g2^alpha/g2^i
        // For e(witness, g2^alpha/g2^i)
        pairing_elems.push((witness, &g2_alpha_divide_g2_i));
        // g1^eval_i*h1^eval_i_rand
        let g1_eval_i_h1_eval_i_rand = pk.g1_powers[0].binary_scalar_mul(&pk.h1_powers[0], eval_i, eval_i_rand);
        // For e(g1^eval_i*h1^eval_i_rand, g2)
        pairing_elems.push((&g1_eval_i_h1_eval_i_rand, &pk.g2_powers[0]));
        let neg_g1 = - &pk.g1_powers[0];      // g1^-1
        // For e(g1^-1, commitment)
        pairing_elems.push((&neg_g1, commitment));
        GT::ate_multi_pairing(pairing_elems).is_one()
    }

    fn compute_commitment(poly: &Polynomial, rand_poly: &Polynomial, pk: &PublicKey) -> G2 {
        let degree = poly.degree();
        let mut bases = G2Vector::with_capacity(2*degree);
        let mut exps = FieldElementVector::with_capacity(2*degree);
        for i in 0..=degree {
            // TODO: Too many clonings, refactor multi_scalar_mul_*
            bases.push(pk.g2_powers[i].clone());
            exps.push(poly[i].clone());
            bases.push(pk.h2_powers[i].clone());
            exps.push(rand_poly[i].clone());
        }
        bases.multi_scalar_mul_const_time(&exps).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_commit_verify() {
        let degree = 10;
        for _ in 0..10 {
            let pk = PublicKey::new(degree, "test".as_bytes());
            let poly = Polynomial(FieldElementVector::random(degree + 1));
            let (rand_poly, commitment) = PolyCommit_Ped::commit(&poly, &pk);
            assert!(PolyCommit_Ped::verify_commitment(&poly, &rand_poly, &commitment, &pk))
        }
    }

    #[test]
    fn test_witness_random_poly() {
        let degree = 10;
        let pk = PublicKey::new(degree, "test".as_bytes());
        let count_test_cases = 100;
        for _ in 0..count_test_cases {
            let poly = Polynomial::random(degree);
            let (rand_poly, commitment) = PolyCommit_Ped::commit(&poly, &pk);
            assert!(PolyCommit_Ped::verify_commitment(&poly, &rand_poly, &commitment, &pk));
            // prove evaluation at random
            let i = FieldElement::random();
            let (eval_i, eval_i_rand, witness) = PolyCommit_Ped::create_witness(&poly, &rand_poly, &i, &pk);
            assert!(PolyCommit_Ped::verify_eval(&commitment, &i, &eval_i, &eval_i_rand, &witness, &pk));
        }
    }
}