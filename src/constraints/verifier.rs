use algebra::{
    //PrimeField,
    AffineCurve, Field};
use r1cs_std::{
    bits::boolean::Boolean,
    fields::nonnative::nonnative_field_gadget::NonNativeFieldGadget,
    //fields::FieldGadget,
    to_field_gadget_vec::ToConstraintFieldGadget,
};
use r1cs_core::{ConstraintSystem, SynthesisError};
use poly_commit::{
    PolynomialCommitment,
    constraints::PolynomialCommitmentGadget,
    fiat_shamir::constraints::FiatShamirRngGadget,
    //fiat_shamir::FiatShamirRng
};
use crate::constraints::{
        ahp::AHPForR1CSGadget,
        data_structures::{IndexVerifierKeyGadget, PreparedIndexVerifierKeyGadget, ProofGadget},
};
use std::marker::PhantomData;
use r1cs_std::fields::fp::FpGadget;

pub struct MarlinVerifierGadget<
    G: AffineCurve,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentGadget<G, PC>
>(
    PhantomData<G>,
    PhantomData<PC>,
    PhantomData<PCG>,
);

impl<G, PC, PCG> MarlinVerifierGadget<G, PC, PCG>
    where
        G:  AffineCurve,
        PC: PolynomialCommitment<G>,
        PCG: PolynomialCommitmentGadget<G, PC>,
        PCG::VerifierKeyGadget: ToConstraintFieldGadget<<G::BaseField as Field>::BasePrimeField>,
        PCG::CommitmentGadget: ToConstraintFieldGadget<
            <G::BaseField as Field>::BasePrimeField,
            FieldGadget = FpGadget<<G::BaseField as Field>::BasePrimeField>
        >,
{
    pub const PROTOCOL_NAME: &'static [u8] = b"MARLIN-2019";

    /// verify with an established hashchain initial state
    pub fn prepared_verify<CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(
        mut cs: CS,
        index_pvk: &PreparedIndexVerifierKeyGadget<G, PC, PCG>,
        public_input: &[NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>],
        proof: &ProofGadget<G, PC, PCG>,
    ) -> Result<Boolean, SynthesisError> {

        // fs_rng has been already initialized with (PROTOCOL_NAME, vk_hash)
        let mut fs_rng = index_pvk.fs_rng.clone();

        fs_rng.enforce_absorb_nonnative_field_elements(
            cs.ns(|| "absorb public input"),
            &public_input
        )?;

        let (_, verifier_state) = AHPForR1CSGadget::<G, PC, PCG>::verifier_first_round(
            cs.ns(|| "first round"),
            index_pvk.domain_h_size,
            index_pvk.domain_k_size,
            &mut fs_rng,
            &proof.commitments[0],
            &proof.prover_messages[0].field_elements,
        )?;

        let (_, verifier_state) = AHPForR1CSGadget::<G, PC, PCG>::verifier_second_round(
            cs.ns(|| "second round"),
            verifier_state,
            &mut fs_rng,
            &proof.commitments[1],
            &proof.prover_messages[1].field_elements,
        )?;

        let _verifier_state = AHPForR1CSGadget::<G, PC, PCG>::verifier_third_round(
            cs.ns(|| "third round"),
            verifier_state,
            &mut fs_rng,
            &proof.commitments[2],
            &proof.prover_messages[2].field_elements,
        )?;

        /*let mut formatted_public_input = vec![NonNativeFieldGadget::one()];
        for elem in public_input.iter().cloned() {
            formatted_public_input.push(elem);
        }

        let lc = AHPForR1CSGadget::<G, PC, PCG>::verifier_decision(
            ns!(cs, "ahp").cs(),
            &formatted_public_input,
            &proof.evaluations,
            verifier_state.clone(),
            &index_pvk.domain_k_size_gadget,
        )?;

        let (num_opening_challenges, num_batching_rands, comm, query_set, evaluations) =
            AHPForR1CSGadget::<G, PC, PCG>::verifier_comm_query_eval_set(
                &index_pvk,
                &proof,
                &verifier_state,
            )?;

        let mut evaluations_labels = Vec::<(String, NonNativeFieldGadget<F, CF>)>::new();
        for q in query_set.0.iter().cloned() {
            evaluations_labels.push((q.0.clone(), (q.1).1.clone()));
        }
        evaluations_labels.sort_by(|a, b| a.0.cmp(&b.0));

        let mut evals_vec: Vec<NonNativeFieldGadget<F, CF>> = Vec::new();
        for (label, point) in evaluations_labels.iter() {
            if label != "outer_sumcheck" && label != "inner_sumcheck" {
                evals_vec.push(evaluations.get_lc_eval(label, point).unwrap());
            }
        }

        fs_rng.absorb_nonnative_field_elements(&evals_vec)?;

        let (opening_challenges, opening_challenges_bits) =
            fs_rng.squeeze_128_bits_field_elements_and_bits(num_opening_challenges)?;
        let (batching_rands, batching_rands_bits) =
            fs_rng.squeeze_128_bits_field_elements_and_bits(num_batching_rands)?;

        eprintln!("before PC checks: constraints: {}", cs.num_constraints());

        Ok(PCG::prepared_check_combinations(
            ns!(cs, "pc_check").cs(),
            &index_pvk.prepared_verifier_key,
            &lc,
            &comm,
            &query_set,
            &evaluations,
            &proof.pc_batch_proof,
            &opening_challenges,
            &opening_challenges_bits,
            &batching_rands,
            &batching_rands_bits,
        )?)*/
        Ok(Boolean::Constant(true))
    }

    pub fn verify<CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(
        mut cs:         CS,
        index_vk:       &IndexVerifierKeyGadget<G, PC, PCG>,
        public_input:   &[NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>],
        proof:          &ProofGadget<G, PC, PCG>,
    ) -> Result<Boolean, SynthesisError>
    {
        let index_pvk = PreparedIndexVerifierKeyGadget::<G, PC, PCG>::prepare(
            cs.ns(|| "prepare vk"),
            &index_vk
        )?;

        Self::prepared_verify(
            cs.ns(|| "verify with prepared vk"),
            &index_pvk,
            public_input,
            proof
        )
    }
}