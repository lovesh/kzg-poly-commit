use std::ops::{Index, IndexMut};

use amcl_wrapper::field_elem::{FieldElementVector, FieldElement};

/// Polynomial represented with coefficients in a vector. The ith element of the vector is the coefficient of the ith degree term.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct Polynomial(pub FieldElementVector);

impl Polynomial {
    /// Return a zero polynomial of degree `degree`
    pub fn new(degree: usize) -> Self {
        let coeffs = FieldElementVector::new(degree + 1);
        Polynomial(coeffs)
    }

    pub fn degree(&self) -> usize {
        self.0.len() - 1
    }

    /// Polynomial is zero if all coefficients are 0
    pub fn is_zero(&self) -> bool {
        self.0.iter().all(|coeff| coeff.is_zero())
    }

    // Evaluate polynomial at given `x`
    pub fn eval(&self, x: &FieldElement) -> FieldElement {
        if x.is_zero() {
            self[0].clone()
        } else {
            let exp = FieldElementVector::new_vandermonde_vector(x, self.degree() + 1);
            self.0.inner_product(&exp).unwrap()
        }
    }

    /// Divides 2 polynomials i.e. `dividend` / `divisor` using long division. Assumes `divisor` divides the `dividend` exactly so no remainder
    pub fn long_division(dividend: &Self, divisor: &Self) -> Self {
        assert!(!divisor.is_zero());
        assert!(!divisor[divisor.degree()].is_zero());

        let mut remainder: Polynomial = dividend.clone();
        let mut quotient = vec![];
        // Inverse of coefficient of highest degree of the divisor polynomial. This will be multiplied
        // with the coefficient of highest degree of the remainder.
        let highest_degree_coeff_inv = divisor[divisor.degree()].inverse();
        let rem_degree = dividend.degree();
        let div_degree = divisor.degree();
        let quo_degree = dividend.degree() - div_degree;
        for i in (div_degree..=rem_degree).rev() {
            if remainder[i].is_zero() {
                quotient.push(FieldElement::zero());
                continue
            }

            let q = &highest_degree_coeff_inv * &remainder[i];
            for j in 0..div_degree {
                remainder[i-div_degree+j] -= &(&divisor[j] * &q);
            }
            quotient.push(q);
        }
        // Remove trailing 0s since the quotient has degree `quo_degree`
        quotient.drain(quo_degree+1..);
        // The coefficients of the quotient polynomial were computed from highest to lowest degree.
        quotient.reverse();
        Polynomial(FieldElementVector::from(quotient))
    }

    /// Multiply 2 polynomials
    pub fn multiply(left: &Self, right: &Self) -> Self {
        let mut res = Self::new(left.degree() + right.degree());
        for i in 0..=left.degree() {
            for j in 0..=right.degree() {
                res[i+j] += &left[i] * &right[j];
            }
        }
        res
    }

    // TODO: Add a coefficients method to avoid using self.0
    /// Return a randomly chosen polynomial (each coefficient is randomly chosen) of degree `degree`.
    pub fn random(degree: usize) -> Self {
        Self(FieldElementVector::random(degree + 1)) // +1 for constant term
    }
}

impl Index<usize> for Polynomial {
    type Output = FieldElement;

    fn index(&self, idx: usize) -> &FieldElement {
        &self.0[idx]
    }
}

impl IndexMut<usize> for Polynomial {
    fn index_mut(&mut self, idx: usize) -> &mut FieldElement {
        &mut self.0[idx]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    #[test]
    fn test_poly() {
        let degree = 10;
        let poly1 = Polynomial(FieldElementVector::random(degree + 1));
        assert!(!poly1.is_zero());

        let poly2 = Polynomial(FieldElementVector::new(degree + 1));
        assert!(poly2.is_zero());
    }

    #[test]
    fn test_poly_long_div() {
        // x^2 - 1 / x + 1 = x - 1
        // dividend = -1 + x^2
        let c1 = vec![FieldElement::minus_one(), FieldElement::zero(), FieldElement::one()];
        let dividend = Polynomial(FieldElementVector::from(c1));
        // divisor = 1 + x
        let c2 = vec![FieldElement::one(), FieldElement::one()];
        let divisor = Polynomial(FieldElementVector::from(c2));
        let quotient = Polynomial::long_division(&dividend, &divisor);
        println!("Quotient={:?}", &quotient);
        // quotient = -1 + x
        assert_eq!(quotient.degree(), 1);
        assert_eq!(quotient[0], FieldElement::minus_one());
        assert_eq!(quotient[1], FieldElement::one());

        let quotient = Polynomial::long_division(&dividend, &quotient);
        println!("Quotient={:?}", &quotient);
        // quotient = 1 + x
        assert_eq!(quotient.degree(), 1);
        assert_eq!(quotient[0], FieldElement::one());
        assert_eq!(quotient[1], FieldElement::one());

        // 2x^2 + 3x + 1 / x + 1 = 2x + 1
        // dividend = 1 + 3x + 2x^2
        let c1 = vec![FieldElement::one(), FieldElement::from(3u64), FieldElement::from(2u64)];
        let dividend = Polynomial(FieldElementVector::from(c1));
        // divisor = 1 + x
        let c2 = vec![FieldElement::one(), FieldElement::one()];
        let divisor = Polynomial(FieldElementVector::from(c2));
        let quotient = Polynomial::long_division(&dividend, &divisor);
        println!("Quotient={:?}", &quotient);
        // quotient = 1 + 2x
        assert_eq!(quotient.degree(), 1);
        assert_eq!(quotient[0], FieldElement::one());
        assert_eq!(quotient[1], FieldElement::from(2u64));

        // 4x - 4 / x - 1 = 4
        // dividend = -4 + 4x
        let c1 = vec![-FieldElement::from(4u64), FieldElement::from(4u64)];
        let dividend = Polynomial(FieldElementVector::from(c1));
        // divisor = -1 + x
        let c2 = vec![FieldElement::minus_one(), FieldElement::one()];
        let divisor = Polynomial(FieldElementVector::from(c2));
        let quotient = Polynomial::long_division(&dividend, &divisor);
        println!("Quotient={:?}", &quotient);

        // quotient = 4
        assert_eq!(quotient.degree(), 0);
        assert_eq!(quotient[0], FieldElement::from(4u64));

        // x^5 + x^3 + 4x^2 + 4 / x^2 + 1 = x^3 + 4
        // dividend = 4 + 4x^2 + x^3 + x^5
        let c1 = vec![FieldElement::from(4u64), FieldElement::zero(), FieldElement::from(4u64), FieldElement::one(), FieldElement::zero(), FieldElement::one()];
        let dividend = Polynomial(FieldElementVector::from(c1));
        // divisor = 1 + x^2
        let c2 = vec![FieldElement::one(), FieldElement::zero(), FieldElement::one()];
        let divisor = Polynomial(FieldElementVector::from(c2));
        let quotient = Polynomial::long_division(&dividend, &divisor);
        println!("Quotient={:?}", &quotient);

        // quotient = 4 + x^3
        assert_eq!(quotient.degree(), 3);
        assert_eq!(quotient[0], FieldElement::from(4u64));
        assert_eq!(quotient[1], FieldElement::zero());
        assert_eq!(quotient[2], FieldElement::zero());
        assert_eq!(quotient[3], FieldElement::one());

        // 2x^4 - 40x^3 + 3x^2 - 56x - 80 / x - 20 = 2x^3 + 3x + 4
        // dividend = -80 - 56x + 3x^2 - 40x^3 + 2x^4
        let c1 = vec![-FieldElement::from(80u64), -FieldElement::from(56u64), FieldElement::from(3u64), -FieldElement::from(40u64), FieldElement::from(2u64)];
        let dividend = Polynomial(FieldElementVector::from(c1));
        // divisor = -20 + x
        let c2 = vec![-FieldElement::from(20), FieldElement::one()];
        let divisor = Polynomial(FieldElementVector::from(c2));
        let quotient = Polynomial::long_division(&dividend, &divisor);
        println!("Quotient={:?}", &quotient);

        // quotient = 4 + 3x + 2x^3
        assert_eq!(quotient.degree(), 3);
        assert_eq!(quotient[0], FieldElement::from(4u64));
        assert_eq!(quotient[1], FieldElement::from(3u64));
        assert_eq!(quotient[2], FieldElement::zero());
        assert_eq!(quotient[3], FieldElement::from(2u64));
    }

    #[test]
    fn test_poly_multiply() {
        // (x + 1) * (x - 1) = x^2 - 1
        // x + 1
        let left = Polynomial(FieldElementVector::from(vec![FieldElement::one(), FieldElement::one()]));
        // -1 + x
        let right = Polynomial(FieldElementVector::from(vec![FieldElement::minus_one(), FieldElement::one()]));
        let product = Polynomial::multiply(&left, &right);
        // product = -1 + x^2
        assert_eq!(product.degree(), 2);
        assert_eq!(product[0], FieldElement::minus_one());
        assert_eq!(product[1], FieldElement::zero());
        assert_eq!(product[2], FieldElement::one());

        // (x + 1) * (2x + 1) = 2x^2 + 3x + 1
        // 1 + x
        let left = Polynomial(FieldElementVector::from(vec![FieldElement::one(), FieldElement::one()]));
        // 1 + 2x
        let right = Polynomial(FieldElementVector::from(vec![FieldElement::one(), FieldElement::from(2u64)]));
        let product = Polynomial::multiply(&left, &right);
        // product = 2x^2 + 3x + 1
        assert_eq!(product.degree(), 2);
        assert_eq!(product[0], FieldElement::one());
        assert_eq!(product[1], FieldElement::from(3u64));
        assert_eq!(product[2], FieldElement::from(2u64));

        // (x^2 + 1) * (x^3 + 4) = x^5 + x^3 + 4x^2 + 4
        // 1 + x^2
        let left = Polynomial(FieldElementVector::from(vec![FieldElement::one(), FieldElement::zero(), FieldElement::one()]));
        // 4 + x^3
        let right = Polynomial(FieldElementVector::from(vec![FieldElement::from(4u64), FieldElement::zero(), FieldElement::zero(), FieldElement::one()]));
        let product = Polynomial::multiply(&left, &right);
        // 4 + 4x^2 + x^3 + x^5
        assert_eq!(product.degree(), 5);
        assert_eq!(product[0], FieldElement::from(4u64));
        assert_eq!(product[1], FieldElement::zero());
        assert_eq!(product[2], FieldElement::from(4u64));
        assert_eq!(product[3], FieldElement::one());
        assert_eq!(product[4], FieldElement::zero());
        assert_eq!(product[5], FieldElement::one());
    }

    #[test]
    fn test_random_poly_long_div() {
        // Multiply 2 random polynomials and then use the result to check long division
        let count_test_cases = 100;
        let mut rng = rand::thread_rng();
        for _ in 0..count_test_cases {
            let left = Polynomial::random(rng.gen_range(1, 100));
            let right = Polynomial::random(rng.gen_range(1, 100));
            let product = Polynomial::multiply(&left, &right);

            // product / left == right
            let quotient_1 = Polynomial::long_division(&product, &left);
            assert_eq!(quotient_1, right);

            // product / right == left
            let quotient_2 = Polynomial::long_division(&product, &right);
            assert_eq!(quotient_2, left);
        }
    }
}