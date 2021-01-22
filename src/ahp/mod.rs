use crate::{String, ToString, Vec};
use algebra::{Field, PrimeField};
use std::{borrow::Borrow, marker::PhantomData};
use algebra_utils::{EvaluationDomain, get_best_evaluation_domain, DensePolynomial, Evaluations};
use poly_commit::{LCTerm, LabeledPolynomial, LinearCombination};
use r1cs_core::SynthesisError;

use rayon::prelude::*;

pub(crate) mod constraint_systems;
/// Describes data structures and the algorithms used by the AHP indexer.
pub mod indexer;
/// Describes data structures and the algorithms used by the AHP prover.
pub mod prover;
/// Describes data structures and the algorithms used by the AHP verifier.
pub mod verifier;

/// The algebraic holographic proof defined in [CHMMVW19](https://eprint.iacr.org/2019/1047).
/// Currently, this AHP only supports inputs of size one
/// less than a power of 2 (i.e., of the form 2^n - 1).
pub struct AHPForR1CS<F: Field> {
    field: PhantomData<F>,
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// The labels for the polynomials output by the AHP indexer.
    #[rustfmt::skip]
    pub const INDEXER_POLYNOMIALS: [&'static str; 12] = [
        // Polynomials for A
        "a_row", "a_col", "a_val", "a_row_col",
        // Polynomials for B
        "b_row", "b_col", "b_val", "b_row_col",
        // Polynomials for C
        "c_row", "c_col", "c_val", "c_row_col",
    ];

    /// The labels for the polynomials output by the AHP prover.
    #[rustfmt::skip]
    pub const PROVER_POLYNOMIALS: [&'static str; 8] = [
        // First sumcheck
        "w", "z_a", "z_b", "t", "z_1", "h_1",
        // Second sumcheck
        "z_2", "h_2",
    ];

    /// THe linear combinations that are statically known to evaluate to zero.
    pub const LC_WITH_ZERO_EVAL: [&'static str; 2] = ["inner_sumcheck", "outer_sumcheck"];

    pub(crate) fn polynomial_labels() -> impl Iterator<Item = String> {
        Self::INDEXER_POLYNOMIALS
            .iter()
            .chain(&Self::PROVER_POLYNOMIALS)
            .map(|s| s.to_string())
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn num_formatted_public_inputs_is_admissible(num_inputs: usize) -> bool {
        num_inputs.count_ones() == 1
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn formatted_public_input_is_admissible(input: &[F]) -> bool {
        Self::num_formatted_public_inputs_is_admissible(input.len())
    }

    /// The maximum degree of polynomials produced by the indexer and prover
    /// of this protocol.
    /// The number of the variables must include the "one" variable. That is, it
    /// must be with respect to the number of formatted public inputs.
    pub fn max_degree(
        num_constraints: usize,
        num_variables: usize,
        num_non_zero: usize,
    ) -> Result<usize, Error> {
        let padded_matrix_dim =
            constraint_systems::padded_matrix_dim(num_variables, num_constraints);
        let domain_h_size = get_best_evaluation_domain::<F>(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?.size();
        let domain_k_size = get_best_evaluation_domain::<F>(num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?.size();
        let zk_bound = 2; // Due to our way of "batching" polynomials we need an extra query.
        Ok(*[
            2 * domain_h_size + 2 * zk_bound - 3, // h_1 max degree
            domain_h_size - 1, // For exceptional case of high zk_bound
            3 * domain_k_size - 4, // h_2 max degree
        ]
        .iter()
        .max()
        .unwrap()) // This is really the degree not the number of coefficients
    }

    /// Get all the strict degree bounds enforced in the AHP.
    pub fn get_degree_bounds(_info: &indexer::IndexInfo<F>) -> [usize; 2] { [0usize; 2] }

    /// Construct the linear combinations that are checked by the AHP.
    #[allow(non_snake_case)]
    pub fn construct_linear_combinations<E>(
        public_input: &[F],
        evals: &E,
        state: &verifier::VerifierState<F>,
    ) -> Result<Vec<LinearCombination<F>>, Error>
    where
        E: EvaluationsProvider<F>,
    {
        let domain_h = &state.domain_h;
        let g_h = domain_h.group_gen();

        let domain_k = &state.domain_k;
        let g_k = domain_k.group_gen();
        let k_size = domain_k.size_as_field_element();

        let public_input =
            constraint_systems::ProverConstraintSystem::format_public_input(public_input);
        if !Self::formatted_public_input_is_admissible(&public_input) {
            Err(Error::InvalidPublicInputLength)?
        }
        let x_domain = get_best_evaluation_domain::<F>(public_input.len())
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let first_round_msg = state.first_round_msg.unwrap();
        let alpha = first_round_msg.alpha;
        let eta_a = first_round_msg.eta_a;
        let eta_b = first_round_msg.eta_b;
        let eta_c = first_round_msg.eta_c;

        let beta = state.second_round_msg.unwrap().beta;
        let gamma = state.gamma.unwrap();

        let mut linear_combinations = Vec::new();

        // Outer sumcheck:
        let z_b = LinearCombination::new("z_b", vec![(F::one(), "z_b")]);
        let z_1 = LinearCombination::new("z_1", vec![(F::one(), "z_1")]);
        let t = LinearCombination::new("t", vec![(F::one(), "t")]);

        let r_alpha_at_beta = domain_h.eval_unnormalized_bivariate_lagrange_poly(alpha, beta);
        let v_H_at_alpha = domain_h.evaluate_vanishing_polynomial(alpha);
        let v_H_at_beta = domain_h.evaluate_vanishing_polynomial(beta);
        let v_X_at_beta = x_domain.evaluate_vanishing_polynomial(beta);

        let z_b_at_beta = evals.get_lc_eval(&z_b, beta)?;
        let t_at_beta = evals.get_lc_eval(&t, beta)?;
        let z_1_at_beta = evals.get_lc_eval(&z_1, beta)?;
        let z_1_at_g_beta = evals.get_lc_eval(&z_1, g_h * beta)?;

        let x_at_beta = x_domain
            .evaluate_all_lagrange_coefficients(beta)
            .into_iter()
            .zip(public_input)
            .map(|(l, x)| l * &x)
            .fold(F::zero(), |x, y| x + &y);

        #[rustfmt::skip]
        let outer_sumcheck = LinearCombination::new(
            "outer_sumcheck",
            vec![

                (r_alpha_at_beta * (eta_a + eta_c * z_b_at_beta), "z_a".into()),
                (r_alpha_at_beta * eta_b * z_b_at_beta, LCTerm::One),

                (-t_at_beta * v_X_at_beta, "w".into()),
                (-t_at_beta * x_at_beta, LCTerm::One),

                (-v_H_at_beta, "h_1".into()),
                (z_1_at_beta, LCTerm::One),
                (-z_1_at_g_beta, LCTerm::One),
            ],
        );
        debug_assert!(evals.get_lc_eval(&outer_sumcheck, beta)?.is_zero());

        linear_combinations.push(z_b);
        linear_combinations.push(z_1);
        linear_combinations.push(t);
        linear_combinations.push(outer_sumcheck);

        //  Inner sumcheck:
        let beta_alpha = beta * alpha;
        let z_2 = LinearCombination::new("z_2", vec![(F::one(), "z_2")]);

        let a_denom = LinearCombination::new(
            "a_denom",
            vec![
                (beta_alpha, LCTerm::One),
                (-alpha, "a_row".into()),
                (-beta, "a_col".into()),
                (F::one(), "a_row_col".into()),
            ],
        );

        let b_denom = LinearCombination::new(
            "b_denom",
            vec![
                (beta_alpha, LCTerm::One),
                (-alpha, "b_row".into()),
                (-beta, "b_col".into()),
                (F::one(), "b_row_col".into()),
            ],
        );

        let c_denom = LinearCombination::new(
            "c_denom",
            vec![
                (beta_alpha, LCTerm::One),
                (-alpha, "c_row".into()),
                (-beta, "c_col".into()),
                (F::one(), "c_row_col".into()),
            ],
        );

        let a_denom_at_gamma = evals.get_lc_eval(&a_denom, gamma)?;
        let b_denom_at_gamma = evals.get_lc_eval(&b_denom, gamma)?;
        let c_denom_at_gamma = evals.get_lc_eval(&c_denom, gamma)?;
        let z_2_at_gamma = evals.get_lc_eval(&z_2, gamma)?;
        let z_2_at_g_gamma = evals.get_lc_eval(&z_2, g_k * gamma)?;

        let v_K_at_gamma = domain_k.evaluate_vanishing_polynomial(gamma);

        let mut a = LinearCombination::new(
            "a_poly",
            vec![
                (eta_a * b_denom_at_gamma * c_denom_at_gamma, "a_val"),
                (eta_b * a_denom_at_gamma * c_denom_at_gamma, "b_val"),
                (eta_c * b_denom_at_gamma * a_denom_at_gamma, "c_val"),
            ],
        );

        a *= v_H_at_alpha * v_H_at_beta;
        let b_at_gamma = a_denom_at_gamma * b_denom_at_gamma * c_denom_at_gamma;
        let b_expr_at_gamma = b_at_gamma * (z_2_at_g_gamma - z_2_at_gamma + &(t_at_beta / &k_size));

        a -= &LinearCombination::new("b_expr", vec![(b_expr_at_gamma, LCTerm::One)]);
        a -= &LinearCombination::new("h_2", vec![(v_K_at_gamma, "h_2")]);

        a.label = "inner_sumcheck".into();
        let inner_sumcheck = a;
        debug_assert!(evals.get_lc_eval(&inner_sumcheck, gamma)?.is_zero());

        linear_combinations.push(z_2);
        linear_combinations.push(a_denom);
        linear_combinations.push(b_denom);
        linear_combinations.push(c_denom);
        linear_combinations.push(inner_sumcheck);

        linear_combinations.sort_by(|a, b| a.label.cmp(&b.label));
        Ok(linear_combinations)
    }
}

/// Abstraction that provides evaluations of (linear combinations of) polynomials
///
/// Intended to provide a common interface for both the prover and the verifier
/// when constructing linear combinations via `AHPForR1CS::construct_linear_combinations`.
pub trait EvaluationsProvider<F: Field> {
    /// Get the evaluation of linear combination `lc` at `point`.
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, Error>;
}

impl<'a, F: Field> EvaluationsProvider<F> for poly_commit::Evaluations<'a, F> {
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, Error> {
        let key = (lc.label.clone(), point);
        self.get(&key)
            .map(|v| *v)
            .ok_or(Error::MissingEval(lc.label.clone()))
    }
}

impl<'a, F: Field, T: Borrow<LabeledPolynomial<F>>> EvaluationsProvider<F> for Vec<T> {
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, Error> {
        let mut eval = F::zero();
        for (coeff, term) in lc.iter() {
            let value = if let LCTerm::PolyLabel(label) = term {
                self.iter()
                    .find(|p| {
                        let p: &LabeledPolynomial<F> = (*p).borrow();
                        p.label() == label
                    })
                    .ok_or(Error::MissingEval(format!(
                        "Missing {} for {}",
                        label, lc.label
                    )))?
                    .borrow()
                    .evaluate(point)
            } else {
                assert!(term.is_one());
                F::one()
            };
            eval += *coeff * value
        }
        Ok(eval)
    }
}

/// Describes the failure modes of the AHP scheme.
#[derive(Debug)]
pub enum Error {
    /// During verification, a required evaluation is missing
    MissingEval(String),
    /// The number of public inputs is incorrect.
    InvalidPublicInputLength,
    /// The instance generated during proving does not match that in the index.
    InstanceDoesNotMatchIndex,
    /// Currently we only support square constraint matrices.
    NonSquareMatrix,
    /// An error occurred during constraint generation.
    ConstraintSystemError(SynthesisError),
    /// The coboundary polynomial evaluations over the domain don't sum to zero.
    InvalidBoundaryPolynomial,
}

impl From<SynthesisError> for Error {
    fn from(other: SynthesisError) -> Self {
        Error::ConstraintSystemError(other)
    }
}

/// The derivative of the vanishing polynomial
pub trait UnnormalizedBivariateLagrangePoly<F: PrimeField> {
    /// Evaluate the polynomial
    fn eval_unnormalized_bivariate_lagrange_poly(&self, x: F, y: F) -> F;

    /// Evaluate over a batch of inputs
    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(&self, x: F) -> Vec<F>;

    /// Evaluate the magic polynomial over `self`
    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs(&self) -> Vec<F>;
}

impl<F: PrimeField> UnnormalizedBivariateLagrangePoly<F> for Box<dyn EvaluationDomain<F>> {
    fn eval_unnormalized_bivariate_lagrange_poly(&self, x: F, y: F) -> F {
        if x != y {
            (self.evaluate_vanishing_polynomial(x) - self.evaluate_vanishing_polynomial(y))
                / (x - y)
        } else {
            self.size_as_field_element() * x.pow(&[(self.size() - 1) as u64])
        }
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(&self, x: F) -> Vec<F> {
        let vanish_x = self.evaluate_vanishing_polynomial(x);
        let mut inverses: Vec<F> = self.elements().map(|y| x - y).collect();
        algebra::fields::batch_inversion(&mut inverses);

        inverses.par_iter_mut().for_each(|denominator| *denominator *= vanish_x);
        inverses
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs(&self) -> Vec<F> {
        let mut elems: Vec<F> = self
            .elements()
            .map(|e| e * self.size_as_field_element())
            .collect();
        elems[1..].reverse();
        elems
    }
}

/// A coboundary polynomial over a domain D is a polynomial P
/// s.t. sum_{x_in_D}(P(x)) = 0.
/// Given a coboundary polynomial P over a domain D, a boundary
/// polynomial is a polynomial Z s.t. P(x) = Z(g*x) - Z(x).
pub struct BoundaryPolynomial<F: PrimeField> {
    /// The boundary polynomial.
    poly: DensePolynomial<F>,
    /// Evaluations of the boundary polynomial over the D domain.
    evals: Evaluations<F>,
}

impl<F: PrimeField> Clone for BoundaryPolynomial<F> {
    fn clone(&self) -> Self {
        let cloned_evals = Evaluations::<F>::from_vec_and_domain(
            self.evals.evals.clone(),
            self.evals.domain.clone_and_box(),
        );
        Self {
            poly: self.poly.clone(),
            evals: cloned_evals
        }
    }
}

impl<F: PrimeField> BoundaryPolynomial<F> {

    /// Construct a `self` instance from a boundary polynomial.
    pub fn new(
        boundary_poly: DensePolynomial<F>,
        domain: Box<dyn EvaluationDomain<F>>
    ) -> Result<Self, Error>
    {
        let poly_evals = (&boundary_poly).evaluate_over_domain_by_ref(domain);

        // Poly evals over domain should sum to zero
        if poly_evals.evals.par_iter().sum::<F>() != F::zero() {
            Err(Error::InvalidBoundaryPolynomial)?
        }

        Ok( Self { poly: boundary_poly, evals: poly_evals } )
    }

    /// Return the underlying boundary polynomial, consuming `self`.
    pub fn polynomial(self) -> DensePolynomial<F> { self.poly }

    /// Borrow the underlying boundary polynomial.
    pub fn polynomial_ref(&self) -> &DensePolynomial<F> { &self.poly }

    /// Return the evaluations over D of the boundary polynomial, consuming `self`.
    pub fn evals(self) -> Evaluations<F> { self.evals }

    /// Return the evaluations over D of the boundary polynomial, borrowing `self`.
    pub fn evals_ref(&self) -> &Evaluations<F> { &self.evals }

    /// Compute the boundary polynomial given a coboundary polynomial
    /// evaluations `poly_evals` over the elements of a domain D.
    pub fn from_coboundary_polynomial_evals(
        poly_evals: Evaluations<F>
    ) -> Result<Self, Error>
    {
        let domain = poly_evals.domain;
        let evals = poly_evals.evals;

        // Z(1) = 0, or any arbitrary value
        let mut z_evals = Vec::with_capacity(evals.len());
        z_evals.push(F::zero());

        // The other coefficients of the boundary polynomial will be the cumulative sum
        // of the evaluations of the coboundary poly over the domain, e.g.:
        // Z(g) = Z(1) + p'(g),
        // ....
        // Z(g^|H| - 1) = Z(g^|H| - 2) + p'(g^|H| - 1) = p'(g) + p'(g^2) + ... + p'(g^|H - 1|)
        // Z(g^|H|) = 0 = p'(g) + p'(g^2) + ... + p'(g^|H - 1|) + p'(g^|H|), will be excluded
        //TODO: Prefix sum here. Parallelize ? Is it worth it ? (rayon (crossbeam too) has no parallel impl for scan())
        let mut poly_cum_sum_evals = evals.into_iter().scan(F::zero(), |acc, x| {
            *acc += x;
            Some(*acc)
        }).collect::<Vec<_>>();

        // Poly evals over domain should sum to zero
        if poly_cum_sum_evals[poly_cum_sum_evals.len() - 1] != F::zero() {
            Err(Error::InvalidBoundaryPolynomial)?
        }

        z_evals.append(&mut poly_cum_sum_evals);
        z_evals.pop(); // Pop the last zero

        let z_evals = Evaluations::from_vec_and_domain(
            z_evals,
            domain,
        );

        let z_poly = z_evals.interpolate_by_ref();

        Ok(Self {
            poly: z_poly,
            evals: z_evals
        })
    }

    /// Compute the boundary polynomial given a coboundary
    /// polynomial `poly` over a domain `domain`.
    pub fn from_coboundary_polynomial(
        poly:   &DensePolynomial<F>,
        domain: Box<dyn EvaluationDomain<F>>
    ) -> Result<Self, Error>
    {
        Self::from_coboundary_polynomial_evals(poly.evaluate_over_domain_by_ref(domain))
    }

    /// Compute the boundary polynomial given a non-coboundary polynomial
    /// evaluations `poly_evals` over the elements of a domain D.
    /// To make the poly sum to 0 over D, its evaluations are shifted by
    /// a factor v = sum(`poly_evals`)/|D|.
    /// Return the boundary polynomial and v.
    pub fn from_non_coboundary_polynomial_evals(
        poly_evals: Evaluations<F>
    ) -> Result<(Self, F), Error>
    {
        let v = poly_evals.evals.par_iter().sum::<F>();
        let v_over_domain = v * poly_evals.domain.size_inv();
        let normalized_poly_evals = Evaluations::from_vec_and_domain(
            poly_evals.evals.into_par_iter().map(|eval| eval - v_over_domain).collect(),
            poly_evals.domain
        );
        let boundary_poly = Self::from_coboundary_polynomial_evals(normalized_poly_evals)?;
        Ok((boundary_poly, v_over_domain))
    }

    /// Compute the boundary polynomial given a non coboundary
    /// polynomial `poly` over a domain `domain`.
    pub fn from_non_coboundary_polynomial(
        poly:   &DensePolynomial<F>,
        domain: Box<dyn EvaluationDomain<F>>
    ) -> Result<(Self, F), Error> {
        Self::from_non_coboundary_polynomial_evals(poly.evaluate_over_domain_by_ref(domain))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::fields::tweedle::fr::Fr;
    use algebra::UniformRand;
    use algebra_utils::{DenseOrSparsePolynomial, DensePolynomial, get_best_evaluation_domain};
    use rand::thread_rng;

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly() {
        for domain_size in 1..10 {
            let domain = get_best_evaluation_domain::<Fr>(1 << domain_size).unwrap();
            let manual: Vec<_> = domain
                .elements()
                .map(|elem| domain.eval_unnormalized_bivariate_lagrange_poly(elem, elem))
                .collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs();
            assert_eq!(fast, manual);
        }
    }

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly_diff_inputs() {
        let rng = &mut thread_rng();
        for domain_size in 1..10 {
            let domain = get_best_evaluation_domain::<Fr>(1 << domain_size).unwrap();
            let x = Fr::rand(rng);
            let manual: Vec<_> = domain
                .elements()
                .map(|y| domain.eval_unnormalized_bivariate_lagrange_poly(x, y))
                .collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(x);
            assert_eq!(fast, manual);
        }
    }

    #[test]
    fn test_summation() {
        let rng = &mut thread_rng();
        let size = 1 << 4;
        let domain = get_best_evaluation_domain::<Fr>(1 << 4).unwrap();
        let size_as_fe = domain.size_as_field_element();
        let poly = DensePolynomial::rand(size, rng);

        let mut sum: Fr = Fr::zero();
        for eval in domain.elements().map(|e| poly.evaluate(e)) {
            sum += eval;
        }
        let first = poly.coeffs[0] * size_as_fe;
        let last = *poly.coeffs.last().unwrap() * size_as_fe;
        println!("sum: {:?}", sum);
        println!("a_0: {:?}", first);
        println!("a_n: {:?}", last);
        println!("first + last: {:?}\n", first + last);
        assert_eq!(sum, first + last);
    }

    #[test]
    fn test_alternator_polynomial() {
        use algebra_utils::Evaluations;
        let domain_k = get_best_evaluation_domain::<Fr>(1 << 4).unwrap();
        let domain_h = get_best_evaluation_domain::<Fr>(1 << 3).unwrap();
        let domain_h_elems = domain_h
            .elements()
            .collect::<std::collections::HashSet<_>>();
        let alternator_poly_evals = domain_k
            .elements()
            .map(|e| {
                if domain_h_elems.contains(&e) {
                    Fr::one()
                } else {
                    Fr::zero()
                }
            })
            .collect();
        let v_k: DenseOrSparsePolynomial<_> = domain_k.vanishing_polynomial().into();
        let v_h: DenseOrSparsePolynomial<_> = domain_h.vanishing_polynomial().into();
        let (divisor, remainder) = v_k.divide_with_q_and_r(&v_h).unwrap();
        assert!(remainder.is_zero());
        println!("Divisor: {:?}", divisor);
        println!(
            "{:#?}",
            divisor
                .coeffs
                .iter()
                .filter_map(|f| if !f.is_zero() {
                    Some(f.into_repr())
                } else {
                    None
                })
                .collect::<Vec<_>>()
        );

        for e in domain_h.elements() {
            println!("{:?}", divisor.evaluate(e));
        }
        // Let p = v_K / v_H;
        // The alternator polynomial is p * t, where t is defined as
        // the LDE of p(h)^{-1} for all h in H.
        //
        // Because for each h in H, p(h) equals a constant c, we have that t
        // is the constant polynomial c^{-1}.
        //
        // Q: what is the constant c? Why is p(h) constant? What is the easiest
        // way to calculate c?
        let alternator_poly =
            Evaluations::from_vec_and_domain(alternator_poly_evals, domain_k).interpolate();
        let (quotient, remainder) = DenseOrSparsePolynomial::from(alternator_poly.clone())
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(divisor))
            .unwrap();
        assert!(remainder.is_zero());
        println!("quotient: {:?}", quotient);
        println!(
            "{:#?}",
            quotient
                .coeffs
                .iter()
                .filter_map(|f| if !f.is_zero() {
                    Some(f.into_repr())
                } else {
                    None
                })
                .collect::<Vec<_>>()
        );

        println!("{:?}", alternator_poly);
    }

    #[test]
    fn test_coboundary_polynomial() {
        let rng = &mut thread_rng();

        for domain_size in 1..20 {
            let domain = get_best_evaluation_domain::<Fr>(1 << domain_size).unwrap();
            let size = domain.size();

            // Get random poly
            let p = DensePolynomial::<Fr>::rand(size, rng);

            // Compute the boundary polynomial Z
            let (z_poly, v) = BoundaryPolynomial::from_non_coboundary_polynomial(&p, domain.clone()).unwrap();
            let z_evals = z_poly.evals();

            // Compute the coboundary polynomial P'(X) = P(X) - v/|domain|
            let mut p_coeffs = p.coeffs;
            p_coeffs[0] -= v;
            let p_prime = DensePolynomial::from_coefficients_vec(p_coeffs);

            // Compute the evaluations of p_prime over domain
            let p_prime_evals = p_prime.evaluate_over_domain(domain);

            // Test that indeed Z is a boundary polynomial, e.g. :
            // Z(g^i) - z(g^i-1) == p'(g^i) <=> Z(g*x) - Z(x) = p'(x) for each x in domain
            for i in 1..size {
                assert_eq!(
                    z_evals[i] - z_evals[i - 1], p_prime_evals[i - 1],
                    "{}", format!("Equality {} failed on domain size 2^{}", i, size)
                );
            }
        }
    }
}