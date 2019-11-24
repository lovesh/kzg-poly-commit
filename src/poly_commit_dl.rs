// Section 3.2 of the paper, PolyCommit_DL

use crate::polynomial::Polynomial;

use amcl_wrapper::extension_field_gt::GT;
use amcl_wrapper::field_elem::{FieldElement, FieldElementVector};
use amcl_wrapper::group_elem::{GroupElement, GroupElementVector};
use amcl_wrapper::group_elem_g1::{G1Vector, G1};
use amcl_wrapper::group_elem_g2::{G2Vector, G2};

#[macro_export]
macro_rules! commit_poly_to_group {
    ( $public_key: ident, $poly: ident, $vector: ident, $power_vec: expr) => {{
        let mut bases = $vector::with_capacity($poly.degree() + 1);
        for i in 0..=$poly.degree() {
            //TODO: refactor multi_scalar_mul_* to avoid cloning
            bases.push($power_vec[i].clone());
        }
        bases.multi_scalar_mul_const_time(&$poly.0).unwrap()
    }};
}

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
        let alpha_vec = FieldElementVector::new_vandermonde_vector(&alpha, degree + 1);
        // g1 and g2 come from random oracle
        let g1 = G1::from_msg_hash(&[label, " : g1".as_bytes()].concat());
        let g2 = G2::from_msg_hash(&[label, " : g2".as_bytes()].concat());
        // g1_powers = g1, g1^alpha, g1^{alpha^2}, g1^{alpha^3}
        let mut g1_powers = G1Vector::with_capacity(degree + 1);
        // g2_powers = g2, g2^alpha, g2^{alpha^2}, g2^{alpha^3}
        let mut g2_powers = G2Vector::with_capacity(degree + 1);
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
        Self {
            g1_powers,
            g2_powers,
        }
    }

    pub fn is_valid(&self) -> bool {
        self.g1_powers.len() == self.g2_powers.len()
    }

    pub fn is_degree_supported(&self, degree: usize) -> bool {
        self.g1_powers.len() >= degree
    }

    /// For given polynomial `poly`, compute g1^{poly(alpha)} since g1^alpha, g1^{alpha^2} , g1^{alpha^3},.. are known
    pub fn commit_poly_to_G1(&self, poly: &Polynomial) -> G1 {
        commit_poly_to_group!(self, poly, G1Vector, self.g1_powers)
    }

    /// For given polynomial `poly`, compute g2^{poly(alpha)} since g2^alpha, g2^{alpha^2} , g2^{alpha^3},.. are known
    pub fn commit_poly_to_G2(&self, poly: &Polynomial) -> G2 {
        commit_poly_to_group!(self, poly, G2Vector, self.g2_powers)
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
        pk.commit_poly_to_G2(poly)
    }

    /// Verify that the commitment to polynomial matches the expected
    pub fn verify_commitment(poly: &Polynomial, commitment: &G2, pk: &PublicKey) -> bool {
        let expected_commitment = Self::commit(poly, pk);
        &expected_commitment == commitment
    }

    /// Evaluate the polynomial at a point and output the evaluation at that point and the
    /// witness for the evaluation.
    pub fn create_witness(
        poly: &Polynomial,
        i: &FieldElement,
        pk: &PublicKey,
    ) -> (FieldElement, G1) {
        assert!(pk.is_valid());
        assert!(pk.is_degree_supported(poly.degree()));
        let evaluation = poly.eval(i);
        // dividend = poly - evaluation
        let mut dividend = poly.clone();
        dividend[0] -= &evaluation;
        // divisor = x - i = -i + x
        let divisor = Polynomial(FieldElementVector::from(vec![-i, FieldElement::one()]));
        // witness_poly = dividend / divisor
        let witness_poly = Polynomial::long_division(&dividend, &divisor).0;

        // Commit to evaluation of witness polynomial at `alpha`
        let witness = pk.commit_poly_to_G1(&witness_poly);
        (evaluation, witness)
    }

    /// Verify that the polynomial at the given point does evaluate to the given evaluation by verifying the witness.
    /// As an optimization, e(g1, g2) can be precomputed and used for all polynomials committed using this public key.
    /// Another optimization is precomputing e(g1, commitment) and used for all evaluations of th polynomial whose
    /// commitment is used.
    pub fn verify_eval(
        commitment: &G2,
        i: &FieldElement,
        eval_i: &FieldElement,
        witness: &G1,
        pk: &PublicKey,
    ) -> bool {
        // e(g1, commitment) == e(witness, g2^alpha/g2^i) * e(g1, g2)^eval_i
        // e(witness, g2^alpha/g2^i) * e(g1, g2)^eval_i * e(g1, commitment)^-1 == 1
        // e(witness, g2^alpha/g2^i) * e(g1^eval_i, g2) * e(g1^-1, commitment) == 1
        // Compute the above using a multi-pairing
        let mut pairing_elems = vec![];

        // For e(witness, g2^alpha/g2^i)
        let g2_i = &pk.g2_powers[0] * i; // g2^i
        let g2_alpha_divide_g2_i = &pk.g2_powers[1] - g2_i; // g2^alpha/g2^i
        pairing_elems.push((witness, &g2_alpha_divide_g2_i));

        // For e(g1^eval_i, g2)
        let g1_eval_i = &pk.g1_powers[0] * eval_i; // g1^eval_i
        pairing_elems.push((&g1_eval_i, &pk.g2_powers[0]));

        // For e(g1^-1, commitment)
        let neg_g1 = -&pk.g1_powers[0]; // g1^-1
        pairing_elems.push((&neg_g1, commitment));
        GT::ate_multi_pairing(pairing_elems).is_one()
    }

    /// Evaluate the polynomial at multiple points and output a new polynomial that evaluates to same
    /// values as the original polynomial at the given inputs and a single witness for those evaluations.
    /// As described in section 3.4 under "Batch opening".
    /// If number of different evaluations revealed are more than the degree of the polynomial then
    /// the polynomial can be learnt using Lagrange interpolation.
    pub fn create_witness_for_batch(
        poly: &Polynomial,
        inputs: &[FieldElement],
        pk: &PublicKey,
    ) -> (Polynomial, G1) {
        // Polynomial (x-inputs[0])*(x-inputs[1])*(x-inputs[2])...(x-inputs[last])
        let x_i_poly = Polynomial::from_given_roots(inputs);

        let (witness_poly, rem_poly) = Polynomial::long_division(poly, &x_i_poly);

        // Commit to evaluation of witness polynomial at `alpha`
        let witness = pk.commit_poly_to_G1(&witness_poly);
        (rem_poly, witness)
    }

    pub fn verify_eval_for_batch(
        commitment: &G2,
        inputs: &[FieldElement],
        rem_poly: &Polynomial,
        witness: &G1,
        pk: &PublicKey,
    ) -> bool {
        // e(g1, commitment) == e(witness, g2^{(alpha-inputs[0])*(alpha-inputs[1])*(alpha-inputs[2]...(alpha-inputs[last]))}) * e(g1^rem_poly(alpha), g2)
        // e(witness, g2^{(alpha-inputs[0])*(alpha-inputs[1])*(alpha-inputs[2]...(alpha-inputs[last]))}) * e(g1^rem_poly(alpha), g2) * e(g1, commitment)^-1 == 1
        // e(witness, g2^{(alpha-inputs[0])*(alpha-inputs[1])*(alpha-inputs[2]...(alpha-inputs[last]))}) * e(g1^rem_poly(alpha), g2) * e(g1^-1, commitment) == 1
        // Compute the above using a multi-pairing
        let mut pairing_elems = vec![];

        // For e(witness, g2^{(alpha-inputs[0])*(alpha-inputs[1])*(alpha-inputs[2]...(alpha-inputs[last]))})
        // alpha is not known to anyone but powers of alpha raised to g2 are.
        // g2^{(alpha-inputs[0])*(alpha-inputs[1])*(alpha-inputs[2]...(alpha-inputs[last]))}=g2^{evaluation of polynomial whose roots are `inputs` at alpha}
        // Lets call "polynomial whose roots are `inputs`" as P(x). We can compute g2^{P(alpha)} since g2^alpha, g2^{alpha^2} , g2^{alpha^3},.. are known
        // Tradeoff: Making the witness computation in G2 will make the next computation in G1.
        let P = Polynomial::from_given_roots(inputs); // Polynomial whose roots are `inputs`
                                                      // TODO: commit_poly_to_G2 and commit_poly_to_G1 use constant time operations but not needed for verifier
        let g2_P_alpha = pk.commit_poly_to_G2(&P); // g2^{P(alpha)}
        pairing_elems.push((witness, &g2_P_alpha));

        // For e(g1^rem_poly(alpha), g2)
        let g1_rem_alpha = pk.commit_poly_to_G1(&rem_poly); // g1^{rem_poly(alpha)}
        pairing_elems.push((&g1_rem_alpha, &pk.g2_powers[0]));

        // For e(g1^-1, commitment)
        let neg_g1 = -&pk.g1_powers[0]; // g1^-1
        pairing_elems.push((&neg_g1, commitment));
        GT::ate_multi_pairing(pairing_elems).is_one()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;
    use std::time::{Duration, Instant};

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
            let c1 = vec![
                FieldElement::minus_one(),
                FieldElement::zero(),
                FieldElement::one(),
            ];
            let poly = Polynomial(FieldElementVector::from(c1));
            let commitment = PolyCommit_DL::commit(&poly, &pk);
            assert!(PolyCommit_DL::verify_commitment(&poly, &commitment, &pk));
            // prove evaluation at 1
            let i = FieldElement::one();
            let (eval_i, witness) = PolyCommit_DL::create_witness(&poly, &i, &pk);
            assert!(PolyCommit_DL::verify_eval(
                &commitment,
                &i,
                &eval_i,
                &witness,
                &pk
            ));
        }

        {
            // polynomial is x^2 - 4
            let c1 = vec![
                -FieldElement::from(4u64),
                FieldElement::zero(),
                FieldElement::one(),
            ];
            let poly = Polynomial(FieldElementVector::from(c1));
            let commitment = PolyCommit_DL::commit(&poly, &pk);
            assert!(PolyCommit_DL::verify_commitment(&poly, &commitment, &pk));
            // prove evaluation at 2
            let i = FieldElement::from(2u64);
            let (eval_i, witness) = PolyCommit_DL::create_witness(&poly, &i, &pk);
            assert!(PolyCommit_DL::verify_eval(
                &commitment,
                &i,
                &eval_i,
                &witness,
                &pk
            ));
        }

        {
            // polynomial is 2x^4 + 40x^3 + 3x^2 + 56x + 80
            let c1 = vec![
                FieldElement::from(80u64),
                FieldElement::from(56u64),
                FieldElement::from(3u64),
                FieldElement::from(40u64),
                FieldElement::from(2u64),
            ];
            let poly = Polynomial(FieldElementVector::from(c1));
            let commitment = PolyCommit_DL::commit(&poly, &pk);
            assert!(PolyCommit_DL::verify_commitment(&poly, &commitment, &pk));
            // prove evaluation at 5
            let i = FieldElement::from(5u64);
            let (eval_i, witness) = PolyCommit_DL::create_witness(&poly, &i, &pk);
            assert!(PolyCommit_DL::verify_eval(
                &commitment,
                &i,
                &eval_i,
                &witness,
                &pk
            ));
        }

        {
            // polynomial is 2x^4 - 40x^3 + 3x^2 - 56x - 80
            let c1 = vec![
                -FieldElement::from(80u64),
                -FieldElement::from(56u64),
                FieldElement::from(3u64),
                -FieldElement::from(40u64),
                FieldElement::from(2u64),
            ];
            let poly = Polynomial(FieldElementVector::from(c1));
            let commitment = PolyCommit_DL::commit(&poly, &pk);
            assert!(PolyCommit_DL::verify_commitment(&poly, &commitment, &pk));
            // prove evaluation at 19
            let i = FieldElement::from(19u64);
            let (eval_i, witness) = PolyCommit_DL::create_witness(&poly, &i, &pk);
            assert!(PolyCommit_DL::verify_eval(
                &commitment,
                &i,
                &eval_i,
                &witness,
                &pk
            ));
        }
    }

    #[test]
    fn test_witness_random_poly() {
        let degree = 10;
        let pk = PublicKey::new(degree, "test".as_bytes());
        let num_test_cases = 100;
        for _ in 0..num_test_cases {
            let poly = Polynomial::random(degree);
            let commitment = PolyCommit_DL::commit(&poly, &pk);
            // prove evaluation at random
            let i = FieldElement::random();
            let (eval_i, witness) = PolyCommit_DL::create_witness(&poly, &i, &pk);
            assert!(PolyCommit_DL::verify_eval(
                &commitment,
                &i,
                &eval_i,
                &witness,
                &pk
            ));
        }
    }

    #[test]
    fn test_batch_witness_random_poly() {
        let degree = 100;
        let pk = PublicKey::new(degree, "test".as_bytes());
        let num_test_cases = 100;
        let mut rng = rand::thread_rng();
        for _ in 0..num_test_cases {
            let poly = Polynomial::random(degree);
            let commitment = PolyCommit_DL::commit(&poly, &pk);
            let batch_size = rng.gen_range(3, 55);
            let inputs = (0..batch_size)
                .map(|_| FieldElement::random())
                .collect::<Vec<FieldElement>>();
            let (rem_poly, witness) =
                PolyCommit_DL::create_witness_for_batch(&poly, inputs.as_slice(), &pk);
            for i in &inputs {
                // Check that the poly and rem_poly have same values at all `i`
                assert_eq!(poly.eval(i), rem_poly.eval(i));
            }
            assert!(PolyCommit_DL::verify_eval_for_batch(
                &commitment,
                inputs.as_slice(),
                &rem_poly,
                &witness,
                &pk
            ));
        }
    }

    #[test]
    fn timing_batch_witness_random_poly() {
        // Benchmark
        let mut rng = rand::thread_rng();
        // Number of batches created for each degree of a polynomial
        let checks_per_degree = 10;

        for degree in vec![20, 40, 50, 100, 150, 200, 250, 300] {
            let pk = PublicKey::new(degree, "test".as_bytes());
            let poly = Polynomial::random(degree);
            let commitment = PolyCommit_DL::commit(&poly, &pk);
            for _ in 0..checks_per_degree {
                let batch_size = rng.gen_range(5, degree - 1);
                let inputs = (0..batch_size)
                    .map(|_| FieldElement::random())
                    .collect::<Vec<FieldElement>>();

                let mut proving_time = Duration::new(0, 0);
                let mut verifying_time = Duration::new(0, 0);

                for i in &inputs {
                    let start = Instant::now();
                    let (eval_i, witness) = PolyCommit_DL::create_witness(&poly, &i, &pk);
                    proving_time += start.elapsed();

                    let start = Instant::now();
                    assert!(PolyCommit_DL::verify_eval(
                        &commitment,
                        &i,
                        &eval_i,
                        &witness,
                        &pk
                    ));
                    verifying_time += start.elapsed();
                }

                let proving_batch = Instant::now();
                let (rem_poly, witness) =
                    PolyCommit_DL::create_witness_for_batch(&poly, inputs.as_slice(), &pk);
                println!("PolyCommit_DL: For degree {} polynomial, creating witness for batch size {} takes {:?}. Creating witness individually takes {:?}", degree, batch_size, proving_batch.elapsed(), proving_time);

                for i in &inputs {
                    // Check that the poly and rem_poly have same values at all `i`
                    assert_eq!(poly.eval(i), rem_poly.eval(i));
                }

                let verifying_batch = Instant::now();
                assert!(PolyCommit_DL::verify_eval_for_batch(
                    &commitment,
                    inputs.as_slice(),
                    &rem_poly,
                    &witness,
                    &pk
                ));
                println!("PolyCommit_DL: For degree {} polynomial, verifying witness for batch size {} takes {:?}. Verifying witness individually takes {:?}", degree, batch_size, verifying_batch.elapsed(), verifying_time);
            }
        }
    }
}
