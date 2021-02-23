#![allow(non_snake_case)]

use crate::ahp::constraint_systems::{ProverConstraintSystem, pad_input};
use crate::ahp::indexer::*;
use crate::ahp::verifier::*;
use crate::ahp::*;

use crate::{ToString, Vec};
use algebra::{Field, PrimeField};
use algebra_utils::{
    EvaluationDomain, Evaluations as EvaluationsOnDomain,
    get_best_evaluation_domain,
};
use poly_commit::{LabeledPolynomial, Polynomial};
use r1cs_core::{ConstraintSynthesizer, SynthesisError};
use rand_core::RngCore;

/// State for the AHP prover.
pub struct ProverState<'a, F: PrimeField> {
    formatted_input_assignment: Vec<F>,
    witness_assignment: Vec<F>,
    /// Az
    z_a: Option<Vec<F>>,
    /// Bz
    z_b: Option<Vec<F>>,
    /// query bound b
    zk_bound: usize,

    pub x_poly: Option<LabeledPolynomial<F>>,
    w_poly: Option<LabeledPolynomial<F>>,
    mz_polys: Option<(LabeledPolynomial<F>, LabeledPolynomial<F>)>,

    index: &'a Index<F>,

    /// the random values sent by the verifier in the first round
    verifier_first_msg: Option<VerifierFirstMsg<F>>,

    /// domain X, sized for the public input
    domain_x: Box<dyn EvaluationDomain<F>>,

    /// domain H, sized for constraints
    domain_h: Box<dyn EvaluationDomain<F>>,

    /// domain K, sized for matrix nonzero elements
    domain_k: Box<dyn EvaluationDomain<F>>,
}

impl<'a, F: PrimeField> ProverState<'a, F> {
    /// Get the public input.
    pub fn public_input(&self) -> Vec<F> {
        ProverConstraintSystem::unformat_public_input(&self.formatted_input_assignment)
    }
}

/// Each prover message that is not a list of oracles is a list of field elements.
#[derive(Clone)]
pub enum ProverMsg<F: Field> {
    /// Some rounds, the prover sends only oracles. (This is actually the case for all
    /// rounds in Marlin.)
    EmptyMessage,
    /// Otherwise, it's one or more field elements.
    FieldElements(Vec<F>),
}

impl<F: Field> algebra::ToBytes for ProverMsg<F> {
    fn write<W: std::io::Write>(&self, w: W) -> std::io::Result<()> {
        match self {
            ProverMsg::EmptyMessage => Ok(()),
            ProverMsg::FieldElements(field_elems) => field_elems.write(w),
        }
    }
}

/// The first set of prover oracles.
pub struct ProverFirstOracles<F: Field> {
    /// The LDE of `w`.
    pub w: LabeledPolynomial<F>,
    /// The LDE of `Az`.
    pub z_a: LabeledPolynomial<F>,
    /// The LDE of `Bz`.
    pub z_b: LabeledPolynomial<F>,
}

impl<F: Field> ProverFirstOracles<F> {
    /// Iterate over the polynomials output by the prover in the first round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![&self.w, &self.z_a, &self.z_b].into_iter()
    }
}

/// The second set of prover oracles.
pub struct ProverSecondOracles<F: Field> {
    /// The polynomial `t` that is produced in the first round.
    pub t: LabeledPolynomial<F>,
    /// The boundary polynomial `z_1` resulting from the first sumcheck.
    pub z_1: LabeledPolynomial<F>,
    /// The polynomial `h_1` resulting from the first sumcheck.
    pub h_1: LabeledPolynomial<F>,
}

impl<F: Field> ProverSecondOracles<F> {
    /// Iterate over the polynomials output by the prover in the second round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![&self.t, &self.z_1, &self.h_1].into_iter()
    }
}

/// The third set of prover oracles.
pub struct ProverThirdOracles<F: Field> {
    /// The boundary polynomial `z_2` resulting from the second sumcheck.
    pub z_2: LabeledPolynomial<F>,
    /// The polynomial `h_2` resulting from the second sumcheck.
    pub h_2: LabeledPolynomial<F>,
}

impl<F: Field> ProverThirdOracles<F> {
    /// Iterate over the polynomials output by the prover in the third round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![&self.z_2, &self.h_2].into_iter()
    }
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// Initialize the AHP prover.
    pub fn prover_init<'a, C: ConstraintSynthesizer<F>>(
        index: &'a Index<F>,
        c: C,
        zk: bool,
    ) -> Result<ProverState<'a, F>, Error> {
        let init_time = start_timer!(|| "AHP::Prover::Init");

        let constraint_time = start_timer!(|| "Generating constraints and witnesses");
        let mut pcs = ProverConstraintSystem::new();
        c.generate_constraints(&mut pcs)?;
        end_timer!(constraint_time);

        let padding_time = start_timer!(|| "Padding matrices to make them square");
        let num_inputs = pcs.num_input_variables;
        pad_input(&mut pcs, num_inputs);
        pcs.make_matrices_square();
        end_timer!(padding_time);

        let num_non_zero = index.index_info.num_non_zero;

        let ProverConstraintSystem {
            input_assignment: formatted_input_assignment,
            witness_assignment,
            num_constraints,
            ..
        } = pcs;

        let num_input_variables = formatted_input_assignment.len();
        let num_witness_variables = witness_assignment.len();
        if index.index_info.num_constraints != num_constraints
            || num_input_variables + num_witness_variables != index.index_info.num_variables
        {
            Err(Error::InstanceDoesNotMatchIndex)?;
        }

        if !Self::formatted_public_input_is_admissible(&formatted_input_assignment) {
            Err(Error::InvalidPublicInputLength)?
        }

        // Perform matrix multiplications
        let inner_prod_fn = |row: &[(F, usize)]| {
            let mut acc = F::zero();
            for &(ref coeff, i) in row {
                let tmp = if i < num_input_variables {
                    formatted_input_assignment[i]
                } else {
                    witness_assignment[i - num_input_variables]
                };

                acc += &(if coeff.is_one() { tmp } else { tmp * coeff });
            }
            acc
        };

        let eval_z_a_time = start_timer!(|| "Evaluating z_A");
        let z_a = index.a.iter().map(|row| inner_prod_fn(row)).collect();
        end_timer!(eval_z_a_time);

        let eval_z_b_time = start_timer!(|| "Evaluating z_B");
        let z_b = index.b.iter().map(|row| inner_prod_fn(row)).collect();
        end_timer!(eval_z_b_time);

        // Due to our way of "batching" polynomials we need an extra query.
        let zk_bound = if zk { 2 } else { 0 };

        let domain_h = get_best_evaluation_domain::<F>(num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_k = get_best_evaluation_domain::<F>(num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_x = get_best_evaluation_domain::<F>(num_input_variables)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        end_timer!(init_time);

        Ok(ProverState {
            formatted_input_assignment,
            witness_assignment,
            z_a: Some(z_a),
            z_b: Some(z_b),
            x_poly: None,
            w_poly: None,
            mz_polys: None,
            zk_bound,
            index,
            verifier_first_msg: None,
            domain_h,
            domain_k,
            domain_x,
        })
    }

    /// Output the first round message and the next state.
    pub fn prover_first_round<'a, R: RngCore>(
        mut state: ProverState<'a, F>,
        rng: &mut Option<R>,
    ) -> Result<
        (
            ProverMsg<F>,
            ProverFirstOracles<F>,
            ProverState<'a, F>,
        ),
        Error,
    > {
        let zk_bound = state.zk_bound;

        let round_time = start_timer!(|| "AHP::Prover::FirstRound");
        let domain_h = &state.domain_h;

        let v_H = domain_h.vanishing_polynomial().into();

        let x_time = start_timer!(|| "Computing x polynomial and evals");
        let domain_x = &state.domain_x;
        let x_poly = EvaluationsOnDomain::from_vec_and_domain(
            state.formatted_input_assignment.clone(),
            domain_x.clone(),
        )
        .interpolate();
        let x_evals = domain_h.fft(&x_poly);
        end_timer!(x_time);

        let ratio = domain_h.size() / domain_x.size();

        let mut w_extended = state.witness_assignment.clone();
        w_extended.extend(vec![
            F::zero();
            domain_h.size()
                - domain_x.size()
                - state.witness_assignment.len()
        ]);

        let w_poly_time = start_timer!(|| "Computing w polynomial");
        let w_poly_evals = (0..domain_h.size()).into_iter()
            .map(|k| {
                if k % ratio == 0 {
                    F::zero()
                } else {
                    w_extended[k - (k / ratio) - 1] - &x_evals[k]
                }
            })
            .collect();

        // Degree of w_poly before dividing by v_X equals max(|H| - 1 , (zk_bound - 1) + |H|) = (zk_bound - 1) + |H|
        let w_poly = {
            let w = EvaluationsOnDomain::from_vec_and_domain(w_poly_evals, domain_h.clone())
                .interpolate();
            if rng.is_some() {
                &w + &(&Polynomial::from_coefficients_slice(&vec![F::rand(rng.as_mut().unwrap()); zk_bound]) * &v_H)
            } else {
                w
            }
        };
        let (w_poly, remainder) = w_poly.divide_by_vanishing_poly(&domain_x).unwrap();
        assert!(remainder.is_zero()); // w_poly is divisible by v_X because we set w = 0 on X.
        end_timer!(w_poly_time);

        let z_a_poly_time = start_timer!(|| "Computing z_A polynomial");
        let z_a = state.z_a.clone().unwrap();
        let z_a_poly = {
            let z_a = EvaluationsOnDomain::from_vec_and_domain(z_a, domain_h.clone()).interpolate();
            if rng.is_some(){
                &z_a + &(&Polynomial::from_coefficients_slice(&vec![F::rand(rng.as_mut().unwrap()); zk_bound]) * &v_H)
            } else {
                z_a
            }
        };
        end_timer!(z_a_poly_time);

        let z_b_poly_time = start_timer!(|| "Computing z_B polynomial");
        let z_b = state.z_b.clone().unwrap();
        let z_b_poly = {
            let z_b = EvaluationsOnDomain::from_vec_and_domain(z_b, domain_h.clone()).interpolate();
            if rng.is_some() {
                &z_b + &(&Polynomial::from_coefficients_slice(&vec![F::rand(rng.as_mut().unwrap()); zk_bound]) * &v_H)
            } else {
                z_b
            }
        };
        end_timer!(z_b_poly_time);

        let msg = ProverMsg::EmptyMessage;

        assert!(w_poly.degree() <= domain_h.size() - domain_x.size() + zk_bound - 1);
        assert!(z_a_poly.degree() <= domain_h.size() + zk_bound - 1);
        assert!(z_b_poly.degree() <= domain_h.size() + zk_bound - 1);

        let hiding_bound = if rng.is_some() { Some(1) } else { None };
        let w = LabeledPolynomial::new("w".to_string(), w_poly, None, hiding_bound);
        let z_a = LabeledPolynomial::new("z_a".to_string(), z_a_poly, None, hiding_bound);
        let z_b = LabeledPolynomial::new("z_b".to_string(), z_b_poly, None, hiding_bound);
        let x = LabeledPolynomial::new("x".to_string(), x_poly, None, None);

        let oracles = ProverFirstOracles {
            w: w.clone(),
            z_a: z_a.clone(),
            z_b: z_b.clone(),
        };

        state.x_poly = Some(x);
        state.w_poly = Some(w);
        state.mz_polys = Some((z_a, z_b));
        end_timer!(round_time);

        Ok((msg, oracles, state))
    }

    fn calculate_t<'a>(
        matrices: impl Iterator<Item = &'a Matrix<F>>,
        matrix_randomizers: &[F],
        input_domain: &Box<dyn EvaluationDomain<F>>,
        domain_h: Box<dyn EvaluationDomain<F>>,
        r_alpha_x_on_h: Vec<F>,
    ) -> Polynomial<F> {
        let mut t_evals_on_h = vec![F::zero(); domain_h.size()];
        for (matrix, eta) in matrices.zip(matrix_randomizers) {
            for (r, row) in matrix.iter().enumerate() {
                for (coeff, c) in row.iter() {
                    let index = domain_h.reindex_by_subdomain(input_domain.size(), *c);
                    t_evals_on_h[index] += *eta * coeff * r_alpha_x_on_h[r];
                }
            }
        }
        EvaluationsOnDomain::from_vec_and_domain(t_evals_on_h, domain_h).interpolate()
    }

    /// Output the number of oracles sent by the prover in the first round.
    pub fn prover_num_first_round_oracles() -> usize {
        3
    }

    /// Output the degree bounds of oracles in the first round.
    pub fn prover_first_round_degree_bounds(
        _info: &IndexInfo<F>,
    ) -> impl Iterator<Item = Option<usize>> {
        vec![None; 3].into_iter()
    }

    /// Output the second round message and the next state.
    pub fn prover_second_round<'a, R: RngCore>(
        ver_message: &VerifierFirstMsg<F>,
        mut state: ProverState<'a, F>,
        rng: &mut Option<R>,
    ) -> (
        ProverMsg<F>,
        ProverSecondOracles<F>,
        ProverState<'a, F>,
    ) {
        let round_time = start_timer!(|| "AHP::Prover::SecondRound");

        let domain_h = &state.domain_h;
        let zk_bound = state.zk_bound;

        let VerifierFirstMsg {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        } = *ver_message;

        let summed_z_m_poly_time = start_timer!(|| "Compute z_m poly");
        let (z_a_poly, z_b_poly) = state.mz_polys.as_ref().unwrap();

        // Performed via FFT using a domain of size = deg(z_a) + deg(z_b) + 1
        let z_c_poly = z_a_poly.polynomial() * z_b_poly.polynomial();

        let mut summed_z_m_coeffs = z_c_poly.coeffs;
        // Note: Can't combine these two loops, because z_c_poly has 2x the degree
        // of z_a_poly and z_b_poly, so the second loop gets truncated due to
        // the `zip`s.
        summed_z_m_coeffs.par_iter_mut().for_each(|c| *c *= &eta_c);
        summed_z_m_coeffs.par_iter_mut()
            .zip(&z_a_poly.polynomial().coeffs)
            .zip(&z_b_poly.polynomial().coeffs)
            .for_each(|((c, a), b)| *c += &(eta_a * a + &(eta_b * b)));

        let summed_z_m = Polynomial::from_coefficients_vec(summed_z_m_coeffs);
        end_timer!(summed_z_m_poly_time);

        let r_alpha_x_evals_time = start_timer!(|| "Compute r_alpha_x evals");
        let r_alpha_x_evals =
            domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(alpha);
        end_timer!(r_alpha_x_evals_time);

        let r_alpha_poly_time = start_timer!(|| "Compute r_alpha_x poly");
        let r_alpha_poly = Polynomial::from_coefficients_vec(domain_h.ifft(&r_alpha_x_evals));
        end_timer!(r_alpha_poly_time);

        let t_poly_time = start_timer!(|| "Compute t poly");
        let t_poly = Self::calculate_t(
            vec![&state.index.a, &state.index.b, &state.index.c].into_iter(),
            &[eta_a, eta_b, eta_c],
            &state.domain_x,
            domain_h.clone(),
            r_alpha_x_evals,
        );
        end_timer!(t_poly_time);

        let z_poly_time = start_timer!(|| "Compute z poly");

        let x_poly = state.x_poly.as_ref().unwrap();
        let w_poly = state.w_poly.as_ref().unwrap();

        // deg(z_poly) = |H|- 1 + zk_bound
        let mut z_poly = w_poly.polynomial().mul_by_vanishing_poly(state.domain_x.size());
        z_poly.coeffs.par_iter_mut()
            .zip(&x_poly.coeffs)
            .for_each(|(z, x)| *z += x);
        assert!(z_poly.degree() <= domain_h.size() + zk_bound - 1);

        end_timer!(z_poly_time);

        let outer_poly_time = start_timer!(|| "Compute outer sumcheck poly");

        let mul_domain_size = *[
            r_alpha_poly.degree() + summed_z_m.degree(),
            t_poly.degree() + z_poly.degree(),
        ]
        .iter()
        .max()
        .unwrap() + 1;
        let mul_domain = get_best_evaluation_domain::<F>(mul_domain_size)
            .expect("field is not smooth enough to construct domain");
        let mut r_alpha_evals = r_alpha_poly.evaluate_over_domain_by_ref(mul_domain.clone());
        let summed_z_m_evals = summed_z_m.evaluate_over_domain_by_ref(mul_domain.clone());
        let z_poly_evals = z_poly.evaluate_over_domain_by_ref(mul_domain.clone());
        let t_poly_m_evals = t_poly.evaluate_over_domain_by_ref(mul_domain.clone());

        r_alpha_evals.evals.par_iter_mut()
            .zip(&summed_z_m_evals.evals)
            .zip(&z_poly_evals.evals)
            .zip(&t_poly_m_evals.evals)
            .for_each(|(((a, b), &c), d)| {
                *a *= b;
                *a -= c * d;
            });
        let outer_poly = r_alpha_evals.interpolate_by_ref();
        end_timer!(outer_poly_time);

        let z_1_time = start_timer!(|| "Compute z_1 poly");

        // In order to re-use the outer_poly_evals for computing z_1 (because z_1 shall be
        // computed over domain H, while outer_poly_evals are on mul_domain), we ensure that
        // H is a sub-domain of mul_domain.
        assert_eq!(mul_domain.size() % domain_h.size(), 0);
        let step = mul_domain.size()/domain_h.size();
        assert_eq!(domain_h.group_gen(), mul_domain.group_gen().pow(&[step as u64]));

        let outer_poly_evals_on_H = EvaluationsOnDomain::from_vec_and_domain(
            r_alpha_evals.evals.clone().into_iter().step_by(step).collect(),
            domain_h.clone()
        );
        let (z_1, rand_poly_degree) = {
            let z_1_t = BoundaryPolynomial::from_coboundary_polynomial_evals(
                outer_poly_evals_on_H
            ).unwrap().polynomial();

            if rng.is_some() {
                // Let b = zk_bound. This blinding polynomial is of type
                // (c_0 + ... c_(2b-1) * X ^ (2b - 1) )
                // since the boundary poly is queried twice as much as the others
                let mut randomization_poly = Polynomial::rand(2 * zk_bound - 1, rng.as_mut().unwrap());
                randomization_poly = randomization_poly.mul_by_vanishing_poly(domain_h.size());

                // Add the blinding polynomial to z_1
                let z_1 = &z_1_t + &randomization_poly;

                (z_1, 2 * zk_bound - 1)
            } else {
                (z_1_t, 0)
            }
        };

        assert!(z_1.degree() <= domain_h.size() + rand_poly_degree);

        end_timer!(z_1_time);

        let z_1_g_time = start_timer!(|| "Compute z_1_g poly");
        let z_1_g = {

            // z_1 has higher degree with respect to |H| due to randomization;
            // therefore, when constructing z_1_g we have to take care of the
            // higher powers of g. So the g vector will be:
            // (1, g, g^2,...., g^n-1, 1, g, ..., g^((deg(z1) - 1) - |H|)
            let size_diff = z_1.coeffs.len() as i32 - domain_h.size() as i32;

            // Exclude extraordinary high zk_bound
            assert!(size_diff >= 0 && size_diff <= domain_h.size() as i32);

            let mut g_s = domain_h.elements().collect::<Vec<F>>();
            g_s.append(&mut g_s[..size_diff as usize].to_vec());

            let mut z_1_g = z_1.clone();
            z_1_g.coeffs.par_iter_mut().zip(g_s).for_each(|(a, b)| { *a *= b } );
            z_1_g
        };
        end_timer!(z_1_g_time);

        // h1(X) = (outer_poly(X) + z1(X) - z1(g*X)) / v_H
        let h_1_time = start_timer!(|| "Compute h_1 poly");

        let mut h_1 = &outer_poly + &(&z_1 - &z_1_g);
        h_1 = h_1.divide_by_vanishing_poly(domain_h).unwrap().0;
        end_timer!(h_1_time);

        let msg = ProverMsg::EmptyMessage;

        assert!(h_1.degree() <= 2 * domain_h.size() + rand_poly_degree - 2);

        let hiding_bound = if rng.is_some() { Some(1) } else { None };
        let oracles = ProverSecondOracles {
            t: LabeledPolynomial::new("t".into(), t_poly, None, None),
            z_1: LabeledPolynomial::new(
                "z_1".into(),
                z_1,
                None,
                hiding_bound,
            ),
            h_1: LabeledPolynomial::new("h_1".into(), h_1, None, hiding_bound),
        };

        state.x_poly = None;
        state.w_poly = None;
        state.verifier_first_msg = Some(*ver_message);
        end_timer!(round_time);

        (msg, oracles, state)
    }

    /// Output the number of oracles sent by the prover in the second round.
    pub fn prover_num_second_round_oracles() -> usize {
        3
    }

    /// Output the degree bounds of oracles in the second round.
    pub fn prover_second_round_degree_bounds(
        _info: &IndexInfo<F>,
    ) -> impl Iterator<Item = Option<usize>> { vec![None; 3].into_iter() }

    /// Output the third round message and the next state.
    pub fn prover_third_round<'a, R: RngCore>(
        ver_message: &VerifierSecondMsg<F>,
        prover_state: ProverState<'a, F>,
        _r: &mut Option<R>,
    ) -> Result<(ProverMsg<F>, ProverThirdOracles<F>), Error> {
        let round_time = start_timer!(|| "AHP::Prover::ThirdRound");

        let ProverState {
            index,
            verifier_first_msg,
            domain_h,
            domain_k,
            ..
        } = prover_state;

        let VerifierFirstMsg {
            eta_a,
            eta_b,
            eta_c,
            alpha,
        } = verifier_first_msg.expect(
            "ProverState should include verifier_first_msg when prover_third_round is called",
        );

        let beta = ver_message.beta;

        let v_H_at_alpha = domain_h.evaluate_vanishing_polynomial(alpha);
        let v_H_at_beta = domain_h.evaluate_vanishing_polynomial(beta);

        let (a_star, b_star, c_star) = (
            &index.a_star_arith,
            &index.b_star_arith,
            &index.c_star_arith,
        );

        let f_evals_time = start_timer!(|| "Computing f evals on K");
        let mut f_vals_on_K = Vec::with_capacity(domain_k.size());
        let mut inverses_a = Vec::with_capacity(domain_k.size());
        let mut inverses_b = Vec::with_capacity(domain_k.size());
        let mut inverses_c = Vec::with_capacity(domain_k.size());

        for i in 0..domain_k.size() {
            inverses_a.push((beta - a_star.evals_on_K.row[i]) * (alpha - a_star.evals_on_K.col[i]));
            inverses_b.push((beta - b_star.evals_on_K.row[i]) * (alpha - b_star.evals_on_K.col[i]));
            inverses_c.push((beta - c_star.evals_on_K.row[i]) * (alpha - c_star.evals_on_K.col[i]));
        }
        algebra::batch_inversion(&mut inverses_a);
        algebra::batch_inversion(&mut inverses_b);
        algebra::batch_inversion(&mut inverses_c);

        for i in 0..domain_k.size() {
            let t = eta_a * a_star.evals_on_K.val[i] * inverses_a[i]
                + eta_b * b_star.evals_on_K.val[i] * inverses_b[i]
                + eta_c * c_star.evals_on_K.val[i] * inverses_c[i];
            let f_at_kappa = v_H_at_beta * v_H_at_alpha * t;
            f_vals_on_K.push(f_at_kappa);
        }
        end_timer!(f_evals_time);

        let z_2_time = start_timer!(|| "Compute z_2 poly");
        let (z_2, normalized_v) = BoundaryPolynomial::from_non_coboundary_polynomial_evals(
            EvaluationsOnDomain::from_vec_and_domain(f_vals_on_K, domain_k.clone())
        ).unwrap();
        let z_2 = z_2.polynomial();
        end_timer!(z_2_time);

        let z_2_g_time = start_timer!(|| "Compute z_2_g poly");
        let z_2_g = {
            let mut z_2_g = z_2.clone();
            let g_s = domain_k.elements().collect::<Vec<F>>();
            z_2_g.coeffs.par_iter_mut().zip(g_s).for_each(|(a, b)| { *a *= b });
            z_2_g
        };
        end_timer!(z_2_g_time);

        let domain_b = get_best_evaluation_domain(3 * domain_k.size() - 3)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let denom_eval_time = start_timer!(|| "Computing denominator evals on B");
        let a_denom: Vec<_> = a_star.evals_on_B.row.evals.par_iter()
            .zip(&a_star.evals_on_B.col.evals)
            .zip(&a_star.row_col_evals_on_B.evals)
            .map(|((&r, c), r_c)| beta * alpha - (r * alpha) - (beta * c) + r_c)
            .collect();

        let b_denom: Vec<_> = b_star.evals_on_B.row.evals.par_iter()
            .zip(&b_star.evals_on_B.col.evals)
            .zip(&b_star.row_col_evals_on_B.evals)
            .map(|((&r, c), r_c)| beta * alpha - (r * alpha) - (beta * c) + r_c)
            .collect();

        let c_denom: Vec<_> = c_star.evals_on_B.row.evals.par_iter()
            .zip(&c_star.evals_on_B.col.evals)
            .zip(&c_star.row_col_evals_on_B.evals)
            .map(|((&r, c), r_c)| beta * alpha - (r * alpha) - (beta * c) + r_c)
            .collect();
        end_timer!(denom_eval_time);

        let a_evals_time = start_timer!(|| "Computing a evals on B");
        let a_poly_on_B = (0..domain_b.size()).into_iter()
            .map(|i| {
                let t = eta_a * a_star.evals_on_B.val.evals[i] * b_denom[i] * c_denom[i]
                    + eta_b * b_star.evals_on_B.val.evals[i] * a_denom[i] * c_denom[i]
                    + eta_c * c_star.evals_on_B.val.evals[i] * a_denom[i] * b_denom[i];
                v_H_at_beta * v_H_at_alpha * t
            })
            .collect();
        end_timer!(a_evals_time);

        let a_poly_time = start_timer!(|| "Computing a poly");
        let a_poly = EvaluationsOnDomain::from_vec_and_domain(a_poly_on_B, domain_b.clone()).interpolate();
        end_timer!(a_poly_time);

        let b_evals_time = start_timer!(|| "Computing b evals on B");
        let b_poly_on_B = (0..domain_b.size()).into_iter()
            .map(|i| a_denom[i] * b_denom[i] * c_denom[i])
            .collect();
        end_timer!(b_evals_time);

        let b_poly_time = start_timer!(|| "Computing b poly");
        let b_poly = EvaluationsOnDomain::from_vec_and_domain(b_poly_on_B, domain_b).interpolate();
        end_timer!(b_poly_time);

        let h_2_poly_time = start_timer!(|| "Computing h_2 poly");
        let mut f_poly = &z_2_g - &z_2;
        f_poly.coeffs[0] += normalized_v;
        let h_2 = (&a_poly - &(&b_poly * &f_poly))
            .divide_by_vanishing_poly(&domain_k)
            .unwrap()
            .0;
        end_timer!(h_2_poly_time);

        let msg = ProverMsg::EmptyMessage;

        let oracles = ProverThirdOracles {
            z_2: LabeledPolynomial::new(
                "z_2".to_string(),
                z_2,
                None,
                None,
            ),
            h_2: LabeledPolynomial::new("h_2".to_string(), h_2, None, None),
        };
        end_timer!(round_time);

        Ok((msg, oracles))
    }

    /// Output the number of oracles sent by the prover in the third round.
    pub fn prover_num_third_round_oracles() -> usize {
        2
    }

    /// Output the degree bounds of oracles in the third round.
    pub fn prover_third_round_degree_bounds(
        _info: &IndexInfo<F>,
    ) -> impl Iterator<Item = Option<usize>> { vec![None; 2].into_iter() }
}