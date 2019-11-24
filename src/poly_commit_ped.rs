// Section 3.3 of the paper, PolyCommit_Ped

use crate::polynomial::Polynomial;

use amcl_wrapper::extension_field_gt::GT;
use amcl_wrapper::field_elem::{FieldElement, FieldElementVector};
use amcl_wrapper::group_elem::{GroupElement, GroupElementVector};
use amcl_wrapper::group_elem_g1::{G1Vector, G1};
use amcl_wrapper::group_elem_g2::{G2Vector, G2};

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
        let mut g1_powers = G1Vector::with_capacity(degree + 1);
        // g2_powers = g2, g2^alpha, g2^{alpha^2}, g2^{alpha^3}
        let mut g2_powers = G2Vector::with_capacity(degree + 1);
        // h1_powers = h1, h1^alpha, h1^{alpha^2}, h1^{alpha^3}
        let mut h1_powers = G1Vector::with_capacity(degree + 1);
        // h2_powers = h2, h2^alpha, h2^{alpha^2}, h2^{alpha^3}
        let mut h2_powers = G2Vector::with_capacity(degree + 1);
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
        Self {
            g1_powers,
            g2_powers,
            h1_powers,
            h2_powers,
        }
    }

    pub fn is_valid(&self) -> bool {
        (self.g1_powers.len() == self.g2_powers.len())
            && (self.h1_powers.len() == self.h2_powers.len())
            && (self.g1_powers.len() == self.h1_powers.len())
    }

    pub fn is_degree_supported(&self, degree: usize) -> bool {
        self.g1_powers.len() >= degree
    }

    // TODO: Remove duplicated code from commit_poly_to_G1 and commit_poly_to_G2 as done in other module.

    /// For given polynomial `poly`, compute g1^{poly(alpha)}*h1^{rand_poly(alpha)} since
    /// g1^alpha, g1^{alpha^2} , g1^{alpha^3},.. and h1^alpha, h1^{alpha^2} , h1^{alpha^3},.. are known
    pub fn commit_poly_to_G1(&self, poly: &Polynomial, rand_poly: &Polynomial) -> G1 {
        assert_eq!(poly.degree(), rand_poly.degree());
        let degree = poly.degree();
        let mut bases = G1Vector::with_capacity(2 * degree);
        let mut exps = FieldElementVector::with_capacity(2 * degree);
        for i in 0..=degree {
            // TODO: Too many clonings, refactor multi_scalar_mul_*
            bases.push(self.g1_powers[i].clone());
            exps.push(poly[i].clone());
            bases.push(self.h1_powers[i].clone());
            exps.push(rand_poly[i].clone());
        }
        bases.multi_scalar_mul_const_time(&exps).unwrap()
    }

    /// For given polynomial `poly`, compute g2^{poly(alpha)}*h2^{rand_poly(alpha)} since
    /// g2^alpha, g2^{alpha^2} , g2^{alpha^3},.. and h2^alpha, h2^{alpha^2} , h2^{alpha^3},.. are known
    pub fn commit_poly_to_G2(&self, poly: &Polynomial, rand_poly: &Polynomial) -> G2 {
        assert_eq!(poly.degree(), rand_poly.degree());
        let degree = poly.degree();
        let mut bases = G2Vector::with_capacity(2 * degree);
        let mut exps = FieldElementVector::with_capacity(2 * degree);
        for i in 0..=degree {
            // TODO: Too many clonings, refactor multi_scalar_mul_*
            bases.push(self.g2_powers[i].clone());
            exps.push(poly[i].clone());
            bases.push(self.h2_powers[i].clone());
            exps.push(rand_poly[i].clone());
        }
        bases.multi_scalar_mul_const_time(&exps).unwrap()
    }
}

pub struct PolyCommit_Ped {}

impl PolyCommit_Ped {
    /// Commit to a polynomial. Generates a random polynomial as well.
    pub fn commit(poly: &Polynomial, pk: &PublicKey) -> (Polynomial, G2) {
        assert!(pk.is_valid());
        let degree = poly.degree();
        assert!(pk.is_degree_supported(degree));
        // Random polynomial for blinding.
        let rand_poly = Polynomial::random(degree);
        let commitment = Self::compute_commitment(poly, &rand_poly, pk);
        (rand_poly, commitment)
    }

    /// Verify that the commitment to polynomial matches the expected
    pub fn verify_commitment(
        poly: &Polynomial,
        rand_poly: &Polynomial,
        commitment: &G2,
        pk: &PublicKey,
    ) -> bool {
        assert!(pk.is_valid());
        assert!(pk.is_degree_supported(poly.degree()));
        assert_eq!(poly.degree(), rand_poly.degree());

        // TODO: Reusing `compute_commitment` causes verifier to use constant time multi-exp
        // but the verifier can use variable time.
        let expected_commitment = Self::compute_commitment(poly, &rand_poly, pk);
        &expected_commitment == commitment
    }

    /// Evaluate the polynomial at a point and output the point, evaluation at that point and the
    /// witness for the evaluation.
    pub fn create_witness(
        poly: &Polynomial,
        rand_poly: &Polynomial,
        i: &FieldElement,
        pk: &PublicKey,
    ) -> (FieldElement, FieldElement, G1) {
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
        let witness_poly = Polynomial::long_division(&dividend, &divisor).0;

        let evaluation_rand = rand_poly.eval(i);
        // dividend = rand_poly - evaluation
        let mut dividend_rand = rand_poly.clone();
        dividend_rand[0] -= &evaluation_rand;
        // divisor = x - i = -i + x
        let divisor_rand = Polynomial(FieldElementVector::from(vec![-i, FieldElement::one()]));
        // witness_poly_rand = dividend_rand / divisor_rand
        let witness_poly_rand = Polynomial::long_division(&dividend_rand, &divisor_rand).0;

        // witness_poly and witness_poly_rand will always be of same degree since degrees of `poly` and
        // `rand_poly` are same and both are divided by polynomials of degree 1
        // Evaluate both witness polynomials (`witness_poly` and `witness_poly_rand`) at `alpha` and
        // multiply their product.

        let witness = pk.commit_poly_to_G1(&witness_poly, &witness_poly_rand);
        (evaluation, evaluation_rand, witness)
    }

    /// Verify that the polynomial at the given point does evaluate to the given evaluation by
    /// verifying the witness.
    pub fn verify_eval(
        commitment: &G2,
        i: &FieldElement,
        eval_i: &FieldElement,
        eval_i_rand: &FieldElement,
        witness: &G1,
        pk: &PublicKey,
    ) -> bool {
        // e(g1, commitment) == e(witness, g2^alpha/g2^i) * e(g1^eval_i*h1^eval_i_rand, g2)
        // e(witness, g2^alpha/g2^i) * e(g1^eval_i*h1^eval_i_rand, g2) * e(g1, commitment)^-1 == 1
        // e(witness, g2^alpha/g2^i) * e(g1^eval_i*h1^eval_i_rand, g2) * e(g1^-1, commitment) == 1
        // Compute the above using a multi-pairing
        let mut pairing_elems = vec![];

        // For e(witness, g2^alpha/g2^i)
        let g2_i = &pk.g2_powers[0] * i; // g2^i
        let g2_alpha_divide_g2_i = &pk.g2_powers[1] - g2_i; // g2^alpha/g2^i
        pairing_elems.push((witness, &g2_alpha_divide_g2_i));

        // For e(g1^eval_i*h1^eval_i_rand, g2)
        // g1^eval_i*h1^eval_i_rand
        // TODO: binary_scalar_mul is constant time but the verifier can use variable time
        let g1_eval_i_h1_eval_i_rand =
            pk.g1_powers[0].binary_scalar_mul(&pk.h1_powers[0], eval_i, eval_i_rand);
        pairing_elems.push((&g1_eval_i_h1_eval_i_rand, &pk.g2_powers[0]));

        // For e(g1^-1, commitment)
        let neg_g1 = -&pk.g1_powers[0]; // g1^-1
        pairing_elems.push((&neg_g1, commitment));
        GT::ate_multi_pairing(pairing_elems).is_one()
    }

    /// Evaluate the polynomial at multiple points and output 2 new polynomials that evaluates to same
    /// values as the original polynomial and the random polynomial respectively at the given inputs
    /// and a single witness for those evaluations.
    /// Adapted from section 3.4 under "Batch opening".
    /// If number of different evaluations revealed are more than the degree of the polynomial then
    /// the polynomial can be learnt using Lagrange interpolation.
    pub fn create_witness_for_batch(
        poly: &Polynomial,
        rand_poly: &Polynomial,
        inputs: &[FieldElement],
        pk: &PublicKey,
    ) -> (Polynomial, Polynomial, G1) {
        // Polynomial (x-inputs[0])*(x-inputs[1])*(x-inputs[2])...(x-inputs[last])
        let x_i_poly = Polynomial::from_given_roots(inputs);

        let (witness_poly, rem_poly) = Polynomial::long_division(poly, &x_i_poly);

        let (witness_rand_poly, rem_rand_poly) = Polynomial::long_division(rand_poly, &x_i_poly);

        // Commit to evaluation of witness polynomial at `alpha`
        let witness = pk.commit_poly_to_G1(&witness_poly, &witness_rand_poly);
        (rem_poly, rem_rand_poly, witness)
    }

    pub fn verify_eval_for_batch(
        commitment: &G2,
        inputs: &[FieldElement],
        rem_poly: &Polynomial,
        rem_rand_poly: &Polynomial,
        witness: &G1,
        pk: &PublicKey,
    ) -> bool {
        // e(g1, commitment) == e(witness, g2^{(alpha-inputs[0])*(alpha-inputs[1])*(alpha-inputs[2]...(alpha-inputs[last]))}) * e(g1^rem_poly(alpha)*h1^rem_rand_poly(alpha), g2)
        // e(witness, g2^{(alpha-inputs[0])*(alpha-inputs[1])*(alpha-inputs[2]...(alpha-inputs[last]))}) * e(g1^rem_poly(alpha)*h1^rem_rand_poly(alpha), g2) * e(g1, commitment)^-1 == 1

        // Compute the above using a multi-pairing
        let mut pairing_elems = vec![];

        // TODO: computation of `g2_P_alpha` is copied from `PolyCommit_DL::verify_eval_for_batch`. Remove this duplication.
        // For e(witness, g2^{(alpha-inputs[0])*(alpha-inputs[1])*(alpha-inputs[2]...(alpha-inputs[last]))})
        // alpha is not known to anyone but powers of alpha raised to g2 are.
        // g2^{(alpha-inputs[0])*(alpha-inputs[1])*(alpha-inputs[2]...(alpha-inputs[last]))}=g2^{evaluation of polynomial whose roots are `inputs` at alpha}
        // Lets call "polynomial whose roots are `inputs`" as P(x). We can compute g2^{P(alpha)} since g2^alpha, g2^{alpha^2} , g2^{alpha^3},.. are known
        // Tradeoff: Making the witness computation in G2 will make the next computation in G1.
        let P = Polynomial::from_given_roots(inputs); // Polynomial whose roots are `inputs`
                                                      // TODO: commit_poly_to_G2 and commit_poly_to_G1 use constant time operations but not needed for verifier
        let g2_P_alpha = commit_poly_to_group!(pk, P, G2Vector, pk.g2_powers); // g2^{P(alpha)}
        pairing_elems.push((witness, &g2_P_alpha));

        // For e(g1^rem_poly(alpha)*h1^rem_rand_poly(alpha), g2)
        let g1_rem_alpha_h1_rem_rand_alpha = pk.commit_poly_to_G1(&rem_poly, &rem_rand_poly); // g1^{rem_poly(alpha)}
        pairing_elems.push((&g1_rem_alpha_h1_rem_rand_alpha, &pk.g2_powers[0]));

        // For e(g1^-1, commitment)
        let neg_g1 = -&pk.g1_powers[0]; // g1^-1
        pairing_elems.push((&neg_g1, commitment));
        GT::ate_multi_pairing(pairing_elems).is_one()
    }

    fn compute_commitment(poly: &Polynomial, rand_poly: &Polynomial, pk: &PublicKey) -> G2 {
        pk.commit_poly_to_G2(poly, rand_poly)
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
            let (rand_poly, commitment) = PolyCommit_Ped::commit(&poly, &pk);
            assert!(PolyCommit_Ped::verify_commitment(
                &poly,
                &rand_poly,
                &commitment,
                &pk
            ))
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
            assert!(PolyCommit_Ped::verify_commitment(
                &poly,
                &rand_poly,
                &commitment,
                &pk
            ));
            // prove evaluation at random
            let i = FieldElement::random();
            let (eval_i, eval_i_rand, witness) =
                PolyCommit_Ped::create_witness(&poly, &rand_poly, &i, &pk);
            assert!(PolyCommit_Ped::verify_eval(
                &commitment,
                &i,
                &eval_i,
                &eval_i_rand,
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
            let (rand_poly, commitment) = PolyCommit_Ped::commit(&poly, &pk);
            assert!(PolyCommit_Ped::verify_commitment(
                &poly,
                &rand_poly,
                &commitment,
                &pk
            ));
            let batch_size = rng.gen_range(3, 55);
            let inputs = (0..batch_size)
                .map(|_| FieldElement::random())
                .collect::<Vec<FieldElement>>();
            let (rem_poly, rem_rand_poly, witness) =
                PolyCommit_Ped::create_witness_for_batch(&poly, &rand_poly, inputs.as_slice(), &pk);
            for i in &inputs {
                // Check that the poly and rem_poly have same values at all `i`
                assert_eq!(poly.eval(i), rem_poly.eval(i));
                // Check that the rand_poly and rem_rand_poly have same values at all `i`
                assert_eq!(rand_poly.eval(i), rem_rand_poly.eval(i));
            }
            assert!(PolyCommit_Ped::verify_eval_for_batch(
                &commitment,
                inputs.as_slice(),
                &rem_poly,
                &rem_rand_poly,
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
            let (rand_poly, commitment) = PolyCommit_Ped::commit(&poly, &pk);
            for _ in 0..checks_per_degree {
                let batch_size = rng.gen_range(5, degree - 1);
                let inputs = (0..batch_size)
                    .map(|_| FieldElement::random())
                    .collect::<Vec<FieldElement>>();
                let inputs = (0..batch_size)
                    .map(|_| FieldElement::random())
                    .collect::<Vec<FieldElement>>();

                let mut proving_time = Duration::new(0, 0);
                let mut verifying_time = Duration::new(0, 0);
                for i in &inputs {
                    let start = Instant::now();
                    let (eval_i, eval_i_rand, witness) =
                        PolyCommit_Ped::create_witness(&poly, &rand_poly, &i, &pk);
                    proving_time += start.elapsed();

                    let start = Instant::now();
                    assert!(PolyCommit_Ped::verify_eval(
                        &commitment,
                        &i,
                        &eval_i,
                        &eval_i_rand,
                        &witness,
                        &pk
                    ));
                    verifying_time += start.elapsed();
                }

                let proving_batch = Instant::now();
                let (rem_poly, rem_rand_poly, witness) = PolyCommit_Ped::create_witness_for_batch(
                    &poly,
                    &rand_poly,
                    inputs.as_slice(),
                    &pk,
                );
                println!("PolyCommit_Ped: For degree {} polynomial, creating witness for batch size {} takes {:?}. Creating witness individually takes {:?}", degree, batch_size, proving_batch.elapsed(), proving_time);

                for i in &inputs {
                    // Check that the poly and rem_poly have same values at all `i`
                    assert_eq!(poly.eval(i), rem_poly.eval(i));
                    // Check that the rand_poly and rem_rand_poly have same values at all `i`
                    assert_eq!(rand_poly.eval(i), rem_rand_poly.eval(i));
                }

                let verifying_batch = Instant::now();
                assert!(PolyCommit_Ped::verify_eval_for_batch(
                    &commitment,
                    inputs.as_slice(),
                    &rem_poly,
                    &rem_rand_poly,
                    &witness,
                    &pk
                ));
                println!("PolyCommit_Ped: For degree {} polynomial, verifying witness for batch size {} takes {:?}. Verifying witness individually takes {:?}", degree, batch_size, verifying_batch.elapsed(), verifying_time);
            }
        }
    }
}
