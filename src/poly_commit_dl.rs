// Section 3.2 of the paper, PolyCommit_DL

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
}

impl PublicKey {
    /// Create new public key. Done by trusted party. `degree` is called `t` in the paper.
    /// The paper says to create powers of only 1 group element, i.e. from G but since we need
    /// type-3 pairings, so creating powers of element in G1 and G2 as `g1` and `g2`. The exponent
    /// is kept same. 
    pub fn new(degree: usize, label: &[u8]) -> Self {
        // secret key, should not be persisted,
        let alpha = FieldElement::random();
        // alpha_vec = 1, alpha, alpha^2, alpha^3, ... alpha^degree
        let alpha_vec = FieldElementVector::new_vandermonde_vector(&alpha, degree+1);
        // g1 and g2 come from random oracle
        let g1 = G1::from_msg_hash(&[label, " : g1".as_bytes()].concat());
        let g2 = G2::from_msg_hash(&[label, " : g2".as_bytes()].concat());
        // g1_powers = g1, g1^alpha, g1^{alpha^2}, g1^{alpha^3}
        let mut g1_powers = G1Vector::with_capacity(degree+1);
        // g2_powers = g2, g2^alpha, g2^{alpha^2}, g2^{alpha^3}
        let mut g2_powers = G2Vector::with_capacity(degree+1);
        // skip 1st element since its 1
        for a in alpha_vec.iter().skip(1) {
            // TODO: Add an efficient way since the same group element is used.
            g1_powers.push(&g1 * a);
            g2_powers.push(&g2 * a);
        }
        // First element of g1_powers should be `g1`.
        g1_powers.insert(0, g1);
        // First element of g2_powers should be `g2`.
        g2_powers.insert(0, g2);
        Self { g1_powers, g2_powers }
    }

    pub fn is_valid(&self) -> bool {
        self.g1_powers.len() == self.g2_powers.len()
    }

    pub fn is_degree_supported(&self, degree: usize) -> bool {
        self.g1_powers.len() >= degree
    }
}

pub struct PolyCommit_DL {}

impl PolyCommit_DL {
    /// Given a polynomial `f(X) = f_0 + f_1*X + f_2*X^2...`, the commitment to `f(alpha)` (evaluation of `f` at `alpha`) is `g2^{f(alpha)}`
    /// `g2^{f(alpha)} = g2^{f_0 + f_1*alpha + f_2*alpha^2 ...} = g2^{f_0} * g2^{f_1*alpha} * g2^{f_2*alpha^2} * ....`
    /// But no one (except the trusted party) knows `alpha`, hence the above can be seen as g2^{f_0} * {g2^alpha}^f_1 * {g2^{alpha^2}}^f_2 * ...
    /// Since the terms `g2`, `g2^alpha`, `g2^{alpha^2}`, etc are known to all (committer, verifier), the above can be seen as a vector commitment
    /// to the coefficients of the polynomial which is another way of saying commitment to the polynomial.
    pub fn commit(poly: &Polynomial, pk: &PublicKey) -> G2 {
        assert!(pk.is_valid());
        assert!(pk.is_degree_supported(poly.degree()));
        let mut bases = G2Vector::with_capacity(poly.degree());
        for i in 0..=poly.degree() {
            //TODO: refactor multi_scalar_mul_* to avoid cloning
            bases.push(pk.g2_powers[i].clone());
        }
        bases.multi_scalar_mul_const_time(&poly.0).unwrap()
    }

    /// Verify that the commitment to polynomial matches the expected
    pub fn verify_commitment(poly: &Polynomial, commitment: &G2, pk: &PublicKey) -> bool {
        let expected_commitment = Self::commit(poly, pk);
        &expected_commitment == commitment
    }

    /// Evaluate the polynomial at a point and output the evaluation and the witness for the evaluation.
    pub fn create_witness(poly: &Polynomial, i: &FieldElement, pk: &PublicKey) -> (FieldElement, G1) {
        assert!(pk.is_valid());
        assert!(pk.is_degree_supported(poly.degree()));
        let evaluation = poly.eval(i);
        // dividend = poly - evaluation
        let mut dividend = poly.clone();
        dividend[0] -= &evaluation;
        // divisor = x - i = -i + x
        let divisor = Polynomial(FieldElementVector::from(vec![-i, FieldElement::one()]));
        // witness_poly = dividend / divisor
        let witness_poly = Polynomial::long_division(&dividend, &divisor);

        // Evaluate witness polynomial at `alpha`
        let mut bases = G1Vector::with_capacity(witness_poly.degree());
        for i in 0..=witness_poly.degree() {
            bases.push(pk.g1_powers[i].clone());
        }
        let witness = bases.multi_scalar_mul_const_time(&witness_poly.0).unwrap();
        (evaluation, witness)
    }

    /// Verify that the polynomial at the given point does evaluate to the given evaluation by verifying the witness.
    /// As an optimization, e(g1, g2) can be precomputed and used for all polynomials committed using this public key.
    /// Another optimization is precomputing e(g1, commitment) and used for all evaluations of th polynomial whose
    /// commitment is used.
    pub fn verify_eval(commitment: &G2, i: &FieldElement, eval_i: &FieldElement, witness: &G1, pk: &PublicKey) -> bool {
        // e(g1, commitment) == e(witness, g2^alpha/g2^i) * e(g1, g2)^eval_i
        // e(witness, g2^alpha/g2^i) * e(g1, g2)^eval_i * e(g1, commitment)^-1 == 1
        // e(witness, g2^alpha/g2^i) * e(g1^eval_i, g2) * e(g1^-1, commitment) == 1
        // Compute the above using a multi-pairing
        let mut pairing_elems = vec![];
        let g2_i = &pk.g2_powers[0] * i;    // g2^i
        let g2_alpha_divide_g2_i = &pk.g2_powers[1] - g2_i;      // g2^alpha/g2^i
        // For e(witness, g2^alpha/g2^i)
        pairing_elems.push((witness, &g2_alpha_divide_g2_i));
        let g1_eval_i = &pk.g1_powers[0] * eval_i;          // g1^eval_i
        // For e(g1^eval_i, g2)
        pairing_elems.push((&g1_eval_i, &pk.g2_powers[0]));
        let neg_g1 = - &pk.g1_powers[0];      // g1^-1
        // For e(g1^-1, commitment)
        pairing_elems.push((&neg_g1, commitment));
        GT::ate_multi_pairing(pairing_elems).is_one()
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
            let commitment = PolyCommit_DL::commit(&poly, &pk);
            assert!(PolyCommit_DL::verify_commitment(&poly, &commitment, &pk))
        }
    }

    #[test]
    fn test_witness() {
        let degree = 10;
        let pk = PublicKey::new(degree, "test".as_bytes());

        {
            // polynomial is x^2 - 1
            let c1 = vec![FieldElement::minus_one(), FieldElement::zero(), FieldElement::one()];
            let poly = Polynomial(FieldElementVector::from(c1));
            let commitment = PolyCommit_DL::commit(&poly, &pk);
            assert!(PolyCommit_DL::verify_commitment(&poly, &commitment, &pk));
            // prove evaluation at 1
            let i = FieldElement::one();
            let (eval_i, witness) = PolyCommit_DL::create_witness(&poly, &i, &pk);
            assert!(PolyCommit_DL::verify_eval(&commitment, &i, &eval_i, &witness, &pk));
        }

        {
            // polynomial is x^2 - 4
            let c1 = vec![-FieldElement::from(4u64), FieldElement::zero(), FieldElement::one()];
            let poly = Polynomial(FieldElementVector::from(c1));
            let commitment = PolyCommit_DL::commit(&poly, &pk);
            assert!(PolyCommit_DL::verify_commitment(&poly, &commitment, &pk));
            // prove evaluation at 2
            let i = FieldElement::from(2u64);
            let (eval_i, witness) = PolyCommit_DL::create_witness(&poly, &i, &pk);
            assert!(PolyCommit_DL::verify_eval(&commitment, &i, &eval_i, &witness, &pk));
        }

        {
            // polynomial is 2x^4 + 40x^3 + 3x^2 + 56x + 80
            let c1 = vec![FieldElement::from(80u64), FieldElement::from(56u64), FieldElement::from(3u64), FieldElement::from(40u64), FieldElement::from(2u64)];
            let poly = Polynomial(FieldElementVector::from(c1));
            let commitment = PolyCommit_DL::commit(&poly, &pk);
            assert!(PolyCommit_DL::verify_commitment(&poly, &commitment, &pk));
            // prove evaluation at 5
            let i = FieldElement::from(5u64);
            let (eval_i, witness) = PolyCommit_DL::create_witness(&poly, &i, &pk);
            assert!(PolyCommit_DL::verify_eval(&commitment, &i, &eval_i, &witness, &pk));
        }

        {
            // polynomial is 2x^4 - 40x^3 + 3x^2 - 56x - 80
            let c1 = vec![-FieldElement::from(80u64), -FieldElement::from(56u64), FieldElement::from(3u64), -FieldElement::from(40u64), FieldElement::from(2u64)];
            let poly = Polynomial(FieldElementVector::from(c1));
            let commitment = PolyCommit_DL::commit(&poly, &pk);
            assert!(PolyCommit_DL::verify_commitment(&poly, &commitment, &pk));
            // prove evaluation at 19
            let i = FieldElement::from(19u64);
            let (eval_i, witness) = PolyCommit_DL::create_witness(&poly, &i, &pk);
            assert!(PolyCommit_DL::verify_eval(&commitment, &i, &eval_i, &witness, &pk));
        }
    }

    #[test]
    fn test_witness_random_poly() {
        let degree = 10;
        let pk = PublicKey::new(degree, "test".as_bytes());
        let count_test_cases = 100;
        for _ in 0..count_test_cases {
            let poly = Polynomial::random(degree);
            let commitment = PolyCommit_DL::commit(&poly, &pk);
            assert!(PolyCommit_DL::verify_commitment(&poly, &commitment, &pk));
            // prove evaluation at random
            let i = FieldElement::random();
            let (eval_i, witness) = PolyCommit_DL::create_witness(&poly, &i, &pk);
            assert!(PolyCommit_DL::verify_eval(&commitment, &i, &eval_i, &witness, &pk));
        }
    }

}