use algebra::{Field, PrimeField, AffineCurve};
use r1cs_std::{
    alloc::AllocGadget,
    bits::boolean::Boolean,
    eq::EqGadget,
    fields::{
        fp::FpGadget,
        FieldGadget,
        nonnative::nonnative_field_gadget::NonNativeFieldGadget
    },
    ToBitsGadget,
    to_field_gadget_vec::ToConstraintFieldGadget,
};
use r1cs_core::{ConstraintSystem, SynthesisError};
use crate::constraints::{
        data_structures::{PreparedIndexVerifierKeyGadget, ProofGadget},
        polynomial::AlgebraForAHP,
};
use poly_commit::{
    PolynomialCommitment,
    constraints::{
        EvaluationsGadget, PolynomialCommitmentGadget,
        PrepareGadget, QuerySetGadget,
    },
    fiat_shamir::constraints::FiatShamirRngGadget,
};
use std::marker::PhantomData;
use std::collections::{HashMap, HashSet};
use poly_commit::constraints::LabeledPointGadget;

#[derive(Clone)]
pub struct VerifierStateGadget<SimulationF: PrimeField, ConstraintF: PrimeField> {
    domain_h_size: u64,
    domain_k_size: u64,

    first_round_msg: Option<VerifierFirstMsgGadget<SimulationF, ConstraintF>>,
    second_round_msg: Option<VerifierSecondMsgGadget<SimulationF, ConstraintF>>,

    gamma: Option<NonNativeFieldGadget<SimulationF, ConstraintF>>,
}

#[derive(Clone)]
pub struct VerifierFirstMsgGadget<SimulationF: PrimeField, ConstraintF: PrimeField> {
    pub alpha: NonNativeFieldGadget<SimulationF, ConstraintF>,
    pub eta_a: NonNativeFieldGadget<SimulationF, ConstraintF>,
    pub eta_b: NonNativeFieldGadget<SimulationF, ConstraintF>,
    pub eta_c: NonNativeFieldGadget<SimulationF, ConstraintF>,
}

#[derive(Clone)]
pub struct VerifierSecondMsgGadget<SimulationF: PrimeField, ConstraintF: PrimeField> {
    pub beta: NonNativeFieldGadget<SimulationF, ConstraintF>,
}

#[derive(Clone)]
pub struct VerifierThirdMsgGadget<SimulationF: PrimeField, ConstraintF: PrimeField> {
    pub gamma: NonNativeFieldGadget<SimulationF, ConstraintF>,
}

pub struct AHPForR1CSGadget<
    G: AffineCurve,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentGadget<G, PC>,
> where
    PCG::VerifierKeyGadget: ToConstraintFieldGadget<<G::BaseField as Field>::BasePrimeField>,
    PCG::CommitmentGadget: ToConstraintFieldGadget<<G::BaseField as Field>::BasePrimeField>,
{
    curve: PhantomData<G>,
    polynomial_commitment: PhantomData<PC>,
    pc_check: PhantomData<PCG>,
}

impl<
    G: AffineCurve,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentGadget<G, PC>,
> AHPForR1CSGadget<G, PC, PCG>
where
    PCG::VerifierKeyGadget: ToConstraintFieldGadget<<G::BaseField as Field>::BasePrimeField>,
    PCG::CommitmentGadget: ToConstraintFieldGadget<<G::BaseField as Field>::BasePrimeField, FieldGadget = FpGadget<<G::BaseField as Field>::BasePrimeField>>,
{
    /// Output the first message and next round state.
    pub fn verifier_first_round<CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(
        mut cs: CS,
        domain_h_size: u64,
        domain_k_size: u64,
        fs_rng: &mut PCG::RandomOracleGadget,
        comms: &[PCG::CommitmentGadget], // Init round commitments sent by the prover (w, za, zb)
        message: &[NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>] // Empty actually,
    ) -> Result<
        (
            VerifierFirstMsgGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
            VerifierStateGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>
        ), SynthesisError>
    {
        // absorb the first commitments and messages
        {
            let mut elems = Vec::<FpGadget<<G::BaseField as Field>::BasePrimeField>>::new();
            comms.iter().enumerate().for_each(|(i, comm)| {
                elems.append(
                    &mut comm.to_field_gadget_elements(cs.ns(|| format!("comms {} to field elements", i))).unwrap()
                );
            });
            fs_rng.enforce_absorb_native_field_elements(cs.ns(|| "absorb comms"), &elems)?;
            fs_rng.enforce_absorb_nonnative_field_elements(cs.ns(|| "absorb prover message"), &message)?;
        }

        // obtain four elements from the sponge
        let elems = fs_rng.enforce_squeeze_nonnative_field_elements(
            cs.ns(||"squeeze round chals"),
            4
        )?;
        let alpha = elems[0].clone();
        let eta_a = elems[1].clone();
        let eta_b = elems[2].clone();
        let eta_c = elems[3].clone();

        let msg = VerifierFirstMsgGadget {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        };

        let new_state = VerifierStateGadget {
            domain_h_size,
            domain_k_size,
            first_round_msg: Some(msg.clone()),
            second_round_msg: None,
            gamma: None,
        };

        Ok((msg, new_state))
    }
    
    pub fn verifier_second_round<CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(
        mut cs: CS,
        state: VerifierStateGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
        fs_rng: &mut PCG::RandomOracleGadget,
        comms: &[PCG::CommitmentGadget],
        message: &[NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>],
    ) -> Result<
        (
            VerifierSecondMsgGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
            VerifierStateGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>
        ), SynthesisError>
    {
        let VerifierStateGadget {
            domain_h_size,
            domain_k_size,
            first_round_msg,
            ..
        } = state;

        // absorb the second commitments and messages
        {
            let mut elems = Vec::<FpGadget<<G::BaseField as Field>::BasePrimeField>>::new();
            comms.iter().enumerate().for_each(|(i, comm)| {
                elems.append(
                    &mut comm.to_field_gadget_elements(cs.ns(|| format!("comms {} to field elements", i))).unwrap()
                );
            });
            fs_rng.enforce_absorb_native_field_elements(cs.ns(|| "absorb comms"), &elems)?;
            fs_rng.enforce_absorb_nonnative_field_elements(cs.ns(|| "absorb prover message"), &message)?;
        }

        // obtain one element from the sponge
        let elems = fs_rng.enforce_squeeze_nonnative_field_elements(
            cs.ns(||"squeeze round chals"),
            1
        )?;
        let beta = elems[0].clone();

        let msg = VerifierSecondMsgGadget { beta };

        let new_state = VerifierStateGadget {
            domain_h_size,
            domain_k_size,
            first_round_msg,
            second_round_msg: Some(msg.clone()),
            gamma: None,
        };

        Ok((msg, new_state))
    }

    pub fn verifier_third_round<CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(
        mut cs: CS,
        state: VerifierStateGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
        fs_rng: &mut PCG::RandomOracleGadget,
        comms: &[PCG::CommitmentGadget],
        message: &[NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>],
    ) -> Result<VerifierStateGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>, SynthesisError> {
        let VerifierStateGadget {
            domain_h_size,
            domain_k_size,
            first_round_msg,
            second_round_msg,
            ..
        } = state;

        // absorb the third commitments and messages
        {
            let mut elems = Vec::<FpGadget<<G::BaseField as Field>::BasePrimeField>>::new();
            comms.iter().enumerate().for_each(|(i, comm)| {
                elems.append(
                    &mut comm.to_field_gadget_elements(cs.ns(|| format!("comms {} to field elements", i))).unwrap()
                );
            });
            fs_rng.enforce_absorb_native_field_elements(cs.ns(|| "absorb comms"), &elems)?;
            fs_rng.enforce_absorb_nonnative_field_elements(cs.ns(|| "absorb prover message"), &message)?;
        }

        // obtain one element from the sponge
        let elems = fs_rng.enforce_squeeze_nonnative_field_elements(
            cs.ns(||"squeeze round chals"),
            1
        )?;
        let gamma = elems[0].clone();

        let new_state = VerifierStateGadget {
            domain_h_size,
            domain_k_size,
            first_round_msg,
            second_round_msg,
            gamma: Some(gamma),
        };

        Ok(new_state)
    }

    pub fn verifier_decision<CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(
        mut cs:              CS,
        public_input:        &[NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>],
        evals:               &HashMap<String, NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>>,
        state:               VerifierStateGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
        domain_k_size_in_vk: &FpGadget<<G::BaseField as Field>::BasePrimeField>,
    ) -> Result<(), SynthesisError> {
        let VerifierStateGadget {
            domain_k_size,
            first_round_msg,
            second_round_msg,
            ..
        } = state;

        let first_round_msg = first_round_msg.expect(
            "VerifierState should include first_round_msg when verifier_decision is called",
        );
        let second_round_msg = second_round_msg.expect(
            "VerifierState should include second_round_msg when verifier_decision is called",
        );

        let zero = NonNativeFieldGadget::<G::ScalarField, <G::BaseField as Field>::BasePrimeField>::zero(
            cs.ns(|| "hardcode zero")
        )?;

        let VerifierFirstMsgGadget {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        } = first_round_msg;
        let beta: NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField> = second_round_msg.beta;

        //TODO: Return the missing value too instead of a generic AssignmentMissing
        let v_h_at_alpha = evals
            .get("vanishing_poly_h_alpha")
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;

        v_h_at_alpha.enforce_not_equal(cs.ns(|| "v_H_at_alpha != zero"), &zero)?;

        let v_h_at_beta = evals
            .get("vanishing_poly_h_beta")
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;
        v_h_at_beta.enforce_not_equal(cs.ns(|| "v_H_at_beta != zero"), &zero)?;

        let t_at_beta = evals
            .get("t")
            .ok_or_else(|| SynthesisError::AssignmentMissing)?;

        //TODO: Optimize inner and outer sumcheck verification by using mul_without_reduce()

        // Outer sumcheck
        let outer_sumcheck = {

            let r_alpha_at_beta = AlgebraForAHP::prepared_eval_bivariable_vanishing_polynomial(
                cs.ns(|| "r_alpha_at_beta"),
                &alpha,
                &beta,
                &v_h_at_alpha,
                &v_h_at_beta,
            )?;


            let w_at_beta = evals
                .get("w")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let z_a_at_beta = evals
                .get("z_a")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let z_b_at_beta = evals
                .get("z_b")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let x_at_beta = evals
                .get("x")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let v_x_at_beta = {
                let x_padded_len = public_input.len().next_power_of_two() as u64;
                let pow_x_at_beta = AlgebraForAHP::prepare(cs.ns(|| "pow_x_at_beta"), &x_at_beta, x_padded_len)?;
                AlgebraForAHP::prepared_eval_vanishing_polynomial(cs.ns(|| "v_X at beta"), &pow_x_at_beta)
            }?;

            let z_1_at_beta = evals
                .get("z_1_beta")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let z_1_at_g_beta = evals
                .get("z_1_g_beta")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let h_1_at_beta = evals
                .get("h_1")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;


            let first_term = eta_c.mul(cs.ns(|| "eta_c * z_b_at_beta"), &z_b_at_beta)?
                .add(cs.ns(|| "eta_a + eta_c * z_b_at_beta"), &eta_a)?
                .mul(cs.ns(|| "r_alpha_at_beta * (eta_a + eta_c * z_b_at_beta)"), &r_alpha_at_beta)?
                .mul(cs.ns(|| "r_alpha_at_beta * (eta_a + eta_c * z_b_at_beta) * z_a_at_beta"), &z_a_at_beta)?;

            let second_term = r_alpha_at_beta.mul(cs.ns(|| "r_alpha_at_beta * eta_b"), &eta_b)?
                .mul(cs.ns(|| "r_alpha_at_beta * eta_b * z_b_at_beta"), &z_b_at_beta)?;

            let third_term = t_at_beta.mul(cs.ns(|| "t_at_beta * v_X_at_beta"), &v_x_at_beta)?
                .mul(cs.ns(|| "t_at_beta * v_X_at_beta * w_at_beta"), &w_at_beta)?;

            let fourth_term = t_at_beta.mul(cs.ns(|| "t_at_beta * x_at_beta"), &x_at_beta)?;

            let fifth_term = v_h_at_beta.mul(cs.ns(|| "v_H_at_beta * h_1_at_beta"), &h_1_at_beta)?;

            let mut outer_sumcheck_cs = cs.ns(|| "outer_sumcheck");

            first_term.add(outer_sumcheck_cs.ns(|| "first + second"), &second_term)?
                .sub(outer_sumcheck_cs.ns(|| "first + second - third"), &third_term)?
                .sub(outer_sumcheck_cs.ns(|| "first + second - third - fourth"), &fourth_term)?
                .sub(outer_sumcheck_cs.ns(|| "first + second - third - fourth - fifth"), &fifth_term)?
                .add(outer_sumcheck_cs.ns(|| "first + second - third - fourth - fifth + sixth"), &z_1_at_beta)?
                .add(outer_sumcheck_cs.ns(|| "first + second - third - fourth - fifth + sixth - seventh"), &z_1_at_g_beta)
        }?;

        outer_sumcheck.enforce_equal(cs.ns(|| "outer_sumcheck == 0"), &zero)?;

        // Inner sumcheck
        let inner_sumcheck = {

            let v_k_at_gamma = evals
                .get("vanishing_poly_k")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let z_2_at_gamma = evals
                .get("z_2_gamma")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let z_2_at_g_gamma = evals
                .get("z_2_g_gamma")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let h_2_at_gamma = evals
                .get("h_2")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let a_row_at_gamma = evals
                .get("a_row")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let a_col_at_gamma = evals
                .get("a_col")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let a_row_col_at_gamma = evals
                .get("a_row_col")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let a_val_at_gamma = evals
                .get("a_val")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let b_row_at_gamma = evals
                .get("b_row")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let b_col_at_gamma = evals
                .get("b_col")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let b_row_col_at_gamma = evals
                .get("b_row_col")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let b_val_at_gamma = evals
                .get("b_val")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let c_row_at_gamma = evals
                .get("c_row")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let c_col_at_gamma = evals
                .get("c_col")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let c_row_col_at_gamma = evals
                .get("c_row_col")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let c_val_at_gamma = evals
                .get("c_val")
                .ok_or_else(|| SynthesisError::AssignmentMissing)?;

            let beta_alpha = beta.mul(cs.ns(|| "beta * alpha"), &alpha)?;

            let a_denom_at_gamma = {
                let alpha_a_row = alpha.mul(cs.ns(|| "alpha * a_row_at_gamma"), &a_row_at_gamma)?;
                let beta_a_col = beta.mul(cs.ns(|| "beta * a_col_at_gamma"), &a_col_at_gamma)?;
                beta_alpha
                    .sub(cs.ns(|| "beta_alpha - (alpha * a_row_at_gamma)"), &alpha_a_row)?
                    .sub(cs.ns(|| "beta_alpha - (alpha * a_row_at_gamma) - (beta * a_col_at_gamma)"), &beta_a_col)?
                    .add(cs.ns(|| "beta_alpha - (alpha * a_row_at_gamma) - (beta * a_col_at_gamma) + a_row_col_at_gamma"), &a_row_col_at_gamma)
            }?;

            let b_denom_at_gamma = {
                let alpha_b_row = alpha.mul(cs.ns(|| "alpha * b_row_at_gamma"), &b_row_at_gamma)?;
                let beta_b_col = beta.mul(cs.ns(|| "beta * b_col_at_gamma"), &b_col_at_gamma)?;
                beta_alpha
                    .sub(cs.ns(|| "beta_alpha - (alpha * b_row_at_gamma)"), &alpha_b_row)?
                    .sub(cs.ns(|| "beta_alpha - (alpha * b_row_at_gamma) - (beta * b_col_at_gamma)"), &beta_b_col)?
                    .add(cs.ns(|| "beta_alpha - (alpha * b_row_at_gamma) - (beta * b_col_at_gamma) + b_row_col_at_gamma"), &b_row_col_at_gamma)
            }?;

            let c_denom_at_gamma = {
                let alpha_c_row = alpha.mul(cs.ns(|| "alpha * c_row_at_gamma"), &c_row_at_gamma)?;
                let beta_c_col = beta.mul(cs.ns(|| "beta * c_col_at_gamma"), &c_col_at_gamma)?;
                beta_alpha
                    .sub(cs.ns(|| "beta_alpha - (alpha * c_row_at_gamma)"), &alpha_c_row)?
                    .sub(cs.ns(|| "beta_alpha - (alpha * c_row_at_gamma) - (beta * c_col_at_gamma)"), &beta_c_col)?
                    .add(cs.ns(|| "beta_alpha - (alpha * c_row_at_gamma) - (beta * c_col_at_gamma) + c_row_col_at_gamma"), &c_row_col_at_gamma)
            }?;

            let b_at_gamma = a_denom_at_gamma
                .mul(cs.ns(|| "a_denom_at_gamma * b_denom_at_gamma"), &b_denom_at_gamma)?
                .mul(cs.ns(|| "a_denom_at_gamma * b_denom_at_gamma * c_denom_at_gamma"), &c_denom_at_gamma)?;

            //TODO: What this piece of code is useful for ? Can't we just take the domain_k_size coming from
            //      the vk ?
            let inv_domain_k_size_gadget = {
                let domain_k_size_gadget =
                    NonNativeFieldGadget::<G::ScalarField, <G::BaseField as Field>::BasePrimeField>::alloc(
                        cs.ns(|| "domain_k"),
                        || {
                            Ok(G::ScalarField::from(domain_k_size as u128))
                        })?;

                let mut domain_k_size_bit_decomposition = domain_k_size_gadget.to_bits_strict(
                    cs.ns(|| "domain_k_size_gadget_to_bits_strict")
                )?;
                domain_k_size_bit_decomposition.reverse();

                let mut domain_k_size_in_vk_bit_decomposition = domain_k_size_in_vk.to_bits_strict(
                    cs.ns(|| "domain_k_size_in_vk_gadget_to_bits_strict")
                )?;
                domain_k_size_in_vk_bit_decomposition.reverse();

                // This is not the most efficient implementation; an alternative is to check if the last limb of domain_k_size_gadget
                // can be bit composed by the bits in domain_k_size_in_vk, which would save a lot of constraints.
                // Nevertheless, doing so is using the nonnative field gadget in a non-black-box manner and is somehow not encouraged.
                for (i, (left, right)) in domain_k_size_bit_decomposition
                    .iter()
                    .take(32)
                    .zip(domain_k_size_in_vk_bit_decomposition.iter())
                    .enumerate()
                    {
                        left.enforce_equal(cs.ns(|| format!("left_{} == right_{}", i, i)),&right)?;
                    }

                for (i, bit) in domain_k_size_bit_decomposition.iter().skip(32).enumerate() {
                    bit.enforce_equal(cs.ns(|| format!("bit_{} == false", i)), &Boolean::constant(false))?;
                }

                domain_k_size_gadget.inverse(cs.ns(|| "inv_domain_k_size_gadget"))
            }?;

            let b_expr_at_gamma = {
                let t_div_k = t_at_beta.mul(cs.ns(|| "t_at_beta * k_size_inv"), &inv_domain_k_size_gadget)?;
                z_2_at_g_gamma
                    .sub(cs.ns(|| "z_2_at_g_gamma - z_2_at_gamma"), &z_2_at_gamma)?
                    .add(cs.ns(|| "(z_2_at_g_gamma - z_2_at_gamma) + (t_at_beta * k_size_inv)"), &t_div_k)?
                    .mul(cs.ns(|| "b_at_gamma * ((z_2_at_g_gamma - z_2_at_gamma) + (t_at_beta * k_size_inv))"), &b_at_gamma)
            }?;

            let first_term = eta_a
                .mul(cs.ns(|| "eta_a * b_denom_at_gamma"), &b_denom_at_gamma)?
                .mul(cs.ns(|| "eta_a * b_denom_at_gamma * c_denom_at_gamma"), &c_denom_at_gamma)?
                .mul(cs.ns(|| "eta_a * b_denom_at_gamma * c_denom_at_gamma * a_val_at_gamma"), &a_val_at_gamma)?;

            let second_term = eta_b
                .mul(cs.ns(|| "eta_b * a_denom_at_gamma"), &a_denom_at_gamma)?
                .mul(cs.ns(|| "eta_b * a_denom_at_gamma * c_denom_at_gamma"), &c_denom_at_gamma)?
                .mul(cs.ns(|| "eta_b * a_denom_at_gamma * c_denom_at_gamma * b_val_at_gamma"), &b_val_at_gamma)?;

            let third_term = eta_c
                .mul(cs.ns(|| "eta_c * b_denom_at_gamma"), &b_denom_at_gamma)?
                .mul(cs.ns(|| "eta_c * b_denom_at_gamma * a_denom_at_gamma"), &a_denom_at_gamma)?
                .mul(cs.ns(|| "eta_c * b_denom_at_gamma * a_denom_at_gamma * c_val_at_gamma"), &c_val_at_gamma)?;

            let fourth_term = v_h_at_alpha.mul(cs.ns(|| "v_H_at_alpha * v_H_at_beta"), &v_h_at_beta)?;
            let fifth_term = b_expr_at_gamma;
            let sixth_term = v_k_at_gamma.mul(cs.ns(|| "v_K_at_gamma * h_2_at_gamma"), &h_2_at_gamma)?;

            let mut inner_sumcheck_cs = cs.ns(|| "inner_sumcheck");

            first_term
                .add(inner_sumcheck_cs.ns(|| "first + second"), &second_term)?
                .add(inner_sumcheck_cs.ns(|| "first + second + third"), &third_term)?
                .mul(inner_sumcheck_cs.ns(|| "(first + second - third) * fourth"), &fourth_term)?
                .sub(inner_sumcheck_cs.ns(|| "(first + second - third) * fourth - fifth"), &fifth_term)?
                .sub(inner_sumcheck_cs.ns(|| "(first + second - third) * fourth - fifth + sixth"), &sixth_term)
        }?;

        inner_sumcheck.enforce_equal(cs.ns(|| "inner_sumcheck == 0"), &zero)?;

        Ok(())
    }

    pub fn verifier_comm_query_eval_set<CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(
        mut cs:     CS,
        index_pvk:  &PreparedIndexVerifierKeyGadget<G, PC, PCG>,
        proof:      &ProofGadget<G, PC, PCG>,
        state:      &VerifierStateGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
    ) -> Result<
        (
            Vec<PCG::PreparedLabeledCommitmentGadget>,
            QuerySetGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
            EvaluationsGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
        ),
        SynthesisError,
    > {
        let VerifierStateGadget {
            first_round_msg,
            second_round_msg,
            gamma,
            ..
        } = state;

        let first_round_msg = first_round_msg.as_ref().expect(
            "VerifierState should include first_round_msg when verifier_query_set is called",
        );

        let second_round_msg = second_round_msg.as_ref().expect(
            "VerifierState should include second_round_msg when verifier_query_set is called",
        );

        let alpha = first_round_msg.alpha.clone();

        let beta = second_round_msg.beta.clone();

        let gamma_ref = gamma
            .as_ref()
            .expect("VerifierState should include gamma when verifier_query_set is called")
            .clone();

        let gamma = gamma_ref;

        let g_h_times_beta = index_pvk.domain_h_gen_gadget.mul(cs.ns(|| "g_H * beta"), &beta)?;
        let g_k_times_gamma = index_pvk.domain_k_gen_gadget.mul(cs.ns(|| "g_K * gamma"), &gamma)?;

        const TO_EVAL_AT_BETA: [&str; 6] = [
            "x", "w", "z_a", "z_b", "t", "h_1"
        ];

        const TO_EVAL_AT_GAMMA: [&str; 14] = [
            "a_col", "a_row", "a_row_col", "a_val",
            "b_col", "b_row", "b_row_col", "b_val",
            "c_col", "c_row", "c_row_col", "c_val",
            "h_2", "vanishing_poly_k"
        ];

        // Construct QuerySetGadget
        let mut query_set_gadget = QuerySetGadget::<G::ScalarField, <G::BaseField as Field>::BasePrimeField>{ 0: HashSet::new() };

        for poly_label in TO_EVAL_AT_BETA.iter() {
            query_set_gadget.0.insert((poly_label.to_string(), LabeledPointGadget("beta".to_string(), beta.clone())));
        }

        for poly_label in TO_EVAL_AT_GAMMA.iter() {
            query_set_gadget.0.insert((poly_label.to_string(), LabeledPointGadget("gamma".to_string(), gamma.clone())));
        }

        query_set_gadget
            .0
            .insert(("z_1".to_string(), LabeledPointGadget("beta".to_string(), beta.clone())));

        query_set_gadget
            .0
            .insert(("z_1".to_string(), LabeledPointGadget("g * beta".to_string(), g_h_times_beta.clone())));

        query_set_gadget
            .0
            .insert(("z_2".to_string(), LabeledPointGadget("gamma".to_string(), gamma.clone())));

        query_set_gadget
            .0
            .insert(("z_2".to_string(), LabeledPointGadget("g * gamma".to_string(), g_k_times_gamma.clone())));

        query_set_gadget
            .0
            .insert(("vanishing_poly_h".to_string(), LabeledPointGadget("alpha".to_string(), alpha.clone())));

        query_set_gadget
            .0
            .insert(("vanishing_poly_h".to_string(), LabeledPointGadget("beta".to_string(), beta.clone())));


        //Construct EvaluationsGadget
        let mut evaluations_gadget = EvaluationsGadget::<G::ScalarField, <G::BaseField as Field>::BasePrimeField>{ 0: HashMap::new() };

        for poly_label in TO_EVAL_AT_BETA.iter() {
            evaluations_gadget.0.insert(
                LabeledPointGadget(poly_label.to_string(), beta.clone()),
                (*proof.evaluations.get(&poly_label.to_string()).unwrap()).clone(),
            );
        }

        for poly_label in TO_EVAL_AT_GAMMA.iter() {
            evaluations_gadget.0.insert(
                LabeledPointGadget(poly_label.to_string(), gamma.clone()),
                (*proof.evaluations.get(&poly_label.to_string()).unwrap()).clone(),
            );
        }

        evaluations_gadget.0.insert(
            LabeledPointGadget("z_1".to_string(), beta.clone()),
            (*proof.evaluations.get("z_1_beta").unwrap()).clone(),
        );

        evaluations_gadget.0.insert(
            LabeledPointGadget("z_1".to_string(), g_h_times_beta),
            (*proof.evaluations.get("z_1_g_beta").unwrap()).clone(),
        );

        evaluations_gadget.0.insert(
            LabeledPointGadget("z_2".to_string(), gamma),
            (*proof.evaluations.get("z_2_gamma").unwrap()).clone(),
        );

        evaluations_gadget.0.insert(
            LabeledPointGadget("z_2".to_string(), g_k_times_gamma),
            (*proof.evaluations.get("z_2_g_gamma").unwrap()).clone(),
        );

        evaluations_gadget.0.insert(
            LabeledPointGadget("vanishing_poly_h".to_string(), alpha),
            (*proof.evaluations.get("vanishing_poly_h_alpha").unwrap()).clone(),
        );

        evaluations_gadget.0.insert(
            LabeledPointGadget("vanishing_poly_h".to_string(), beta),
            (*proof.evaluations.get("vanishing_poly_h_beta").unwrap()).clone(),
        );

        let mut comms = vec![];

        const INDEX_LABELS: [&str; 14] = [
            "a_row",
            "a_col",
            "a_val",
            "a_row_col",
            "b_row",
            "b_col",
            "b_val",
            "b_row_col",
            "c_row",
            "c_col",
            "c_val",
            "c_row_col",
            "vanishing_poly_h",
            "vanishing_poly_k",
        ];

        // 14 comms for gamma from the index_vk
        for (comm, label) in index_pvk
            .prepared_index_comms
            .iter()
            .zip(INDEX_LABELS.iter())
        {
            comms.push(PCG::create_prepared_labeled_commitment(
                label.to_string(),
                comm.clone(),
                None,
            ));
        }

        // 4 comms for beta from the round 1
        const PROOF_1_LABELS: [&str; 4] = ["w", "z_a", "z_b", "x"];
        for (i, (comm, label)) in proof.commitments[0].iter().zip(PROOF_1_LABELS.iter()).enumerate() {
            let prepared_comm = PCG::PreparedCommitmentGadget::prepare(
                cs.ns(|| format!("prepare comm 1_{}", i)),
                comm
            )?;

            comms.push(PCG::create_prepared_labeled_commitment(
                label.to_string(),
                prepared_comm,
                None,
            ));
        }

        // 3 comms for beta from the round 2
        const PROOF_2_LABELS: [&str; 3] = ["t", "z_1", "h_1"];
        for (i, (comm, label)) in proof.commitments[1]
            .iter()
            .zip(PROOF_2_LABELS.iter())
            .enumerate()
        {
            let prepared_comm = PCG::PreparedCommitmentGadget::prepare(
                cs.ns(|| format!("prepare comm 2_{}", i)),
                comm
            )?;

            comms.push(PCG::create_prepared_labeled_commitment(
                label.to_string(),
                prepared_comm,
                None,
            ));
        }

        // 2 comms for gamma from the round 3
        const PROOF_3_LABELS: [&str; 2] = ["z_2", "h_2"];
        for (i, (comm, label)) in proof.commitments[2]
            .iter()
            .zip(PROOF_3_LABELS.iter())
            .enumerate()
        {
            let prepared_comm = PCG::PreparedCommitmentGadget::prepare(
                cs.ns(|| format!("prepare comm 3_{}", i)),
                comm
            )?;
            comms.push(PCG::create_prepared_labeled_commitment(
                label.to_string(),
                prepared_comm,
                None,
            ));
        }

        Ok((
            comms,
            query_set_gadget,
            evaluations_gadget,
        ))
    }
}

#[cfg(test)]
mod test {
    use algebra::{AffineCurve, Field};
    use poly_commit::{
        constraints::PolynomialCommitmentGadget,
        PolynomialCommitment, LabeledPolynomial
    };
    use algebra_utils::{get_best_evaluation_domain, DensePolynomial};
    use rand::thread_rng;
    use crate::constraints::data_structures::compute_lagrange_polynomials_commitments;
    use r1cs_std::test_constraint_system::TestConstraintSystem;
    use r1cs_core::ConstraintSystem;
    use r1cs_std::fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget;
    use r1cs_std::alloc::AllocGadget;

    fn poly_commit_lagrange<
        G:   AffineCurve,
        PC:  PolynomialCommitment<G>,
        PCG: PolynomialCommitmentGadget<G, PC>
    >(ck: &PC::CommitterKey, log_max_degree: usize)
    {
        let rng = &mut thread_rng();
        for size in 1..log_max_degree {
            let mut cs = TestConstraintSystem::<<G::BaseField as Field>::BasePrimeField>::new();
            let domain = get_best_evaluation_domain::<G::ScalarField>(1 << size).unwrap();

            // Sample a random polynomial and compute its commitment
            let random_poly = DensePolynomial::<G::ScalarField>::rand((1 << size) - 1, rng);
            let evaluations = random_poly.evaluate_over_domain_by_ref(domain).evals;
            let expected_comm = PC::commit(
                ck,
                vec![LabeledPolynomial::new("test".into(), random_poly, None, None)].iter(),
                Some(rng)
            ).unwrap().0;

            // Compute the commitments of the Lagrange polynomials over domain
            let lagrange_comms = compute_lagrange_polynomials_commitments::<G, PC>(1 << size, ck);

            // Alloc expected comm on the circuit
            let expected_comm_gadget = PCG::CommitmentGadget::alloc(
                cs.ns(|| "alloc expected commitment"),
                || Ok(expected_comm[0].commitment().clone())
            ).unwrap();

            // Alloc poly evals
            let mut poly_coords_gadget = Vec::new();
            for (i, poly_coord) in evaluations.into_iter().enumerate() {
                let t = NonNativeFieldGadget::alloc(
                    cs.ns(|| format!("alloc poly coord {}", i)),
                    || Ok(poly_coord)
                ).unwrap();
                poly_coords_gadget.push(t);
            }

            // Check equality
            PCG::verify_polynomial_commitment_from_lagrange_representation(
                cs.ns(|| "verify"),
                &expected_comm_gadget,
                lagrange_comms.as_slice(),
                poly_coords_gadget.as_slice()
            ).unwrap();

            if !cs.is_satisfied() {
                println!("{:?}", cs.which_is_unsatisfied());
            }

            assert!(cs.is_satisfied());
        }
    }

    #[test]
    fn test_verify_polynomial_commitment_from_lagrange_representation() {
        use algebra::{
            fields::tweedle::{
                fq::Fq, fr::Fr,
            }, curves::tweedle::dum::{
                Affine, TweedledumParameters as AffineParameters
            }
        };
        use primitives::crh::poseidon::parameters::TweedleFrPoseidonSponge;
        use poly_commit::ipa_pc::InnerProductArgPC;
        use poly_commit::ipa_pc::constraints::InnerProductArgPCGadget;
        use r1cs_std::{
            fields::fp::FpGadget,
            groups::curves::short_weierstrass::short_weierstrass_jacobian::AffineGadget as GroupGadget
        };
        use r1cs_crypto::crh::poseidon::tweedle::TweedleFrPoseidonSpongeGadget;
        use blake2::Blake2s;

        type AffineGadget = GroupGadget<AffineParameters, Fr, FpGadget<Fr>>;
        type IPAPC = InnerProductArgPC<Fr, Affine, TweedleFrPoseidonSponge>;
        type IPAPCGadget = InnerProductArgPCGadget<Fq, Fr, Affine, AffineGadget, TweedleFrPoseidonSpongeGadget>;

        let log_max_degree = 8;
        let rng = &mut thread_rng();
        let pp = IPAPC::setup::<_, Blake2s>(1 << log_max_degree, rng).unwrap();
        let (ck, _) = IPAPC::trim(&pp, 1 << log_max_degree, 0, None).unwrap();
        poly_commit_lagrange::<Affine, IPAPC, IPAPCGadget>(&ck, log_max_degree);
    }
}