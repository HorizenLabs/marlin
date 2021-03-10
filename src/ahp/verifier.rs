#![allow(non_snake_case)]

use crate::ahp::indexer::IndexInfo;
use crate::ahp::*;
use rand_core::RngCore;

use algebra::PrimeField;
use algebra_utils::{EvaluationDomain, get_best_evaluation_domain, sample_element_outside_domain};
use poly_commit::QuerySet;

/// State of the AHP verifier
pub struct VerifierState<F: PrimeField> {
    pub(crate) domain_h: Box<dyn EvaluationDomain<F>>,
    pub(crate) domain_k: Box<dyn EvaluationDomain<F>>,

    pub(crate) first_round_msg: Option<VerifierFirstMsg<F>>,
    pub(crate) second_round_msg: Option<VerifierSecondMsg<F>>,

    pub(crate) gamma: Option<F>,
}

/// First message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierFirstMsg<F> {
    /// Query for the random polynomial.
    pub alpha: F,
    /// Randomizer for the lincheck for `A`.
    pub eta_a: F,
    /// Randomizer for the lincheck for `B`.
    pub eta_b: F,
    /// Randomizer for the lincheck for `C`.
    pub eta_c: F,
}

/// Second verifier message.
#[derive(Copy, Clone)]
pub struct VerifierSecondMsg<F> {
    /// Query for the second round of polynomials.
    pub beta: F,
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// Output the first message and next round state.
    pub fn verifier_first_round<R: RngCore>(
        index_info: IndexInfo<F>,
        rng: &mut R,
    ) -> Result<(VerifierFirstMsg<F>, VerifierState<F>), Error> {
        if index_info.num_constraints != index_info.num_variables {
            return Err(Error::NonSquareMatrix);
        }

        let domain_h = get_best_evaluation_domain::<F>(index_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_k = get_best_evaluation_domain::<F>(index_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let alpha = sample_element_outside_domain(&domain_h, rng);
        let eta_a = F::rand(rng);
        let eta_b = F::rand(rng);
        let eta_c = F::rand(rng);

        let msg = VerifierFirstMsg {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        };

        let new_state = VerifierState {
            domain_h,
            domain_k,
            first_round_msg: Some(msg),
            second_round_msg: None,
            gamma: None,
        };

        Ok((msg, new_state))
    }

    /// Output the second message and next round state.
    pub fn verifier_second_round<R: RngCore>(
        mut state: VerifierState<F>,
        rng: &mut R,
    ) -> (VerifierSecondMsg<F>, VerifierState<F>) {
        let beta = sample_element_outside_domain(&state.domain_h, rng);
        let msg = VerifierSecondMsg { beta };
        state.second_round_msg = Some(msg);

        (msg, state)
    }

    /// Output the third message and next round state.
    pub fn verifier_third_round<R: RngCore>(
        mut state: VerifierState<F>,
        rng: &mut R,
    ) -> VerifierState<F> {
        state.gamma = Some(F::rand(rng));
        state
    }

    /// Output the query state and next round state.
    pub fn verifier_lcs_query_set<'a, 'b, R: RngCore>(
        state: VerifierState<F>,
        _: &'a mut R,
    ) -> (QuerySet<'b, F>, VerifierState<F>) {
        let beta = state.second_round_msg.unwrap().beta;
        let gamma = state.gamma.unwrap();

        let g_h = state.domain_h.group_gen();
        let g_k = state.domain_k.group_gen();

        let mut query_set = QuerySet::new();

        // Outer sumcheck test:
        //   r(alpha, beta) * (sum_M eta_M z_M(beta)) - t(beta) * z(beta)
        // = z_1(g_H * beta) - z_1(beta) + h_1(beta) * v_H(beta)
        query_set.insert(("z_1".into(), ("beta".into(), beta)));
        query_set.insert(("z_1".into(), ("g * beta".into(), g_h * beta)));
        query_set.insert(("z_b".into(), ("beta".into(), beta)));
        query_set.insert(("t".into(), ("beta".into(), beta)));
        query_set.insert(("outer_sumcheck".into(), ("beta".into(), beta)));

        // For the second linear combination
        // Inner sumcheck test:
        //   h_2(gamma) * v_K(gamma)
        // = a(gamma) - b(gamma) * (z_2(g_K * gamma) - z_2(gamma) + t(beta) / |K|)
        //
        // where
        //   a(X) := sum_M (eta_M v_H(beta) v_H(alpha) val_M(X) prod_N (beta - row_N(X)) (alpha - col_N(X)))
        //   b(X) := prod_M (beta - row_M(X)) (alpha - col_M(X))
        query_set.insert(("z_2".into(), ("gamma".into(), gamma)));
        query_set.insert(("z_2".into(), ("g * gamma".into(), g_k * gamma)));
        query_set.insert(("a_denom".into(), ("gamma".into(), gamma)));
        query_set.insert(("b_denom".into(), ("gamma".into(), gamma)));
        query_set.insert(("c_denom".into(), ("gamma".into(), gamma)));
        query_set.insert(("inner_sumcheck".into(), ("gamma".into(), gamma)));

        (query_set, state)
    }

    /// Output the query state and next round state.
    pub fn verifier_query_set<'a, 'b, R: RngCore>(
        state: VerifierState<F>,
        _: &'a mut R,
    ) -> (QuerySet<'b, F>, VerifierState<F>) {

        let beta = state.second_round_msg.unwrap().beta;
        let gamma = state.gamma.unwrap();

        let g_h = state.domain_h.group_gen();
        let g_k = state.domain_k.group_gen();

        let mut query_set = QuerySet::new();

        // Inner sumcheck

        // First round polys
        query_set.insert(("w".into(), ("beta".into(), beta)));
        query_set.insert(("z_a".into(), ("beta".into(), beta)));
        query_set.insert(("z_b".into(), ("beta".into(), beta)));

        // Second round polys
        query_set.insert(("t".into(), ("beta".into(), beta)));
        query_set.insert(("z_1".into(), ("beta".into(), beta)));
        query_set.insert(("z_1".into(), ("g * beta".into(), g_h * beta)));
        query_set.insert(("h_1".into(), ("beta".into(), beta)));

        // Outer sumcheck

        // Third round polys
        query_set.insert(("z_2".into(), ("gamma".into(), gamma)));
        query_set.insert(("z_2".into(), ("g * gamma".into(), g_k * gamma)));
        query_set.insert(("h_2".into(), ("gamma".into(), gamma)));
        query_set.insert(("a_row".into(), ("gamma".into(), gamma)));
        query_set.insert(("a_col".into(), ("gamma".into(), gamma)));
        query_set.insert(("a_row_col".into(), ("gamma".into(), gamma)));
        query_set.insert(("a_val".into(), ("gamma".into(), gamma)));
        query_set.insert(("b_row".into(), ("gamma".into(), gamma)));
        query_set.insert(("b_col".into(), ("gamma".into(), gamma)));
        query_set.insert(("b_row_col".into(), ("gamma".into(), gamma)));
        query_set.insert(("b_val".into(), ("gamma".into(), gamma)));
        query_set.insert(("c_row".into(), ("gamma".into(), gamma)));
        query_set.insert(("c_col".into(), ("gamma".into(), gamma)));
        query_set.insert(("c_row_col".into(), ("gamma".into(), gamma)));
        query_set.insert(("c_val".into(), ("gamma".into(), gamma)));

        (query_set, state)
    }
}
