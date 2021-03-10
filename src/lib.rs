//! A crate for the Marlin preprocessing zkSNARK for R1CS.
//!
//! # Note
//!
//! Currently, Marlin only supports R1CS instances where the number of inputs
//! is the same as the number of constraints (i.e., where the constraint
//! matrices are square). Furthermore, Marlin only supports instances where the
//! public inputs are of size one less than a power of 2 (i.e., 2^n - 1).
#![deny(unused_import_braces, unused_qualifications, trivial_casts)]
#![deny(trivial_numeric_casts, private_in_public)]
#![deny(stable_features, unreachable_pub, non_shorthand_field_patterns)]
#![deny(unused_attributes, unused_imports, unused_mut, missing_docs)]
#![deny(renamed_and_removed_lints, stable_features, unused_allocation)]
#![deny(unused_comparisons, bare_trait_objects, unused_must_use, const_err)]
#![forbid(unsafe_code)]

#[macro_use]
extern crate bench_utils;

use algebra::to_bytes;
use algebra::PrimeField;
use algebra::ToBytes;
use algebra::UniformRand;
use std::marker::PhantomData;
use digest::Digest;
use poly_commit::{Evaluations, LabeledPolynomial, LabeledRandomness, BatchLCProof, QuerySet, evaluate_query_set_to_vec};
use poly_commit::{LabeledCommitment, PCUniversalParams, PolynomialCommitment};
use r1cs_core::ConstraintSynthesizer;
use rand_core::RngCore;

use std::{
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};

/// Implements a Fiat-Shamir based Rng that allows one to incrementally update
/// the seed based on new messages in the proof transcript.
pub mod rng;
use rng::FiatShamirRng;

mod error;
pub use error::*;

mod data_structures;
pub use data_structures::*;

/// Implements an Algebraic Holographic Proof (AHP) for the R1CS indexed relation.
pub mod ahp;
pub use ahp::AHPForR1CS;
use ahp::EvaluationsProvider;
use algebra_utils::get_best_evaluation_domain;
use crate::ahp::verifier::VerifierState;
use crate::ahp::prover::ProverMsg;

#[cfg(test)]
mod test;

/// Configuration parameters for the Marlin proving system, modifying the
/// internal behaviour of both prover and verifier.
pub trait MarlinConfig: Clone {
    /// If set, an optimization exploiting LC of polynomials will be enabled.
    /// This optimization allows to include less opening values in the proof,
    /// thus reducing its size, but comes with additional variable base scalar
    /// multiplications to be performed by the verifier in order to verify the
    /// sumcheck equations, that are expensive to circuitize.
    /// If unset, all the opening values of all the polynomials are included in
    /// the proof (thus increasing its size), but doesn't come with any additional
    /// operation to be performed by the verifier, apart from the lincheck of course.
    const LC_OPT: bool;
    /// Enable or disable zero-knowledge
    const ZK: bool = true;
}

/// The compiled argument system.
pub struct Marlin<F: PrimeField, PC: PolynomialCommitment<F>, D: Digest, MC: MarlinConfig>(
    #[doc(hidden)] PhantomData<F>,
    #[doc(hidden)] PhantomData<PC>,
    #[doc(hidden)] PhantomData<D>,
    #[doc(hidden)] PhantomData<MC>,
);

impl<F: PrimeField, PC: PolynomialCommitment<F>, D: Digest, MC: MarlinConfig> Marlin<F, PC, D, MC> {
    /// The personalization string for this protocol. Used to personalize the
    /// Fiat-Shamir rng.
    pub const PROTOCOL_NAME: &'static [u8] = b"MARLIN-2019";

    /// Generate the universal prover and verifier keys for the
    /// argument system.
    pub fn universal_setup<R: RngCore>(
        num_constraints: usize,
        num_variables: usize,
        num_non_zero: usize,
        rng: &mut R,
    ) -> Result<UniversalSRS<F, PC>, Error<PC::Error>> {
        let max_degree = AHPForR1CS::<F>::max_degree(
            num_constraints,
            num_variables,
            num_non_zero,
            MC::ZK
        )?;
        let setup_time = start_timer!(|| {
            format!(
            "Marlin::UniversalSetup with max_degree {}, computed for a maximum of {} constraints, {} vars, {} non_zero",
            max_degree, num_constraints, num_variables, num_non_zero,
        )
        });

        let srs = PC::setup(max_degree, rng).map_err(Error::from_pc_err);
        end_timer!(setup_time);
        srs
    }

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys. This is a deterministic algorithm that anyone can rerun.
    pub fn index<C: ConstraintSynthesizer<F>>(
        srs: &UniversalSRS<F, PC>,
        c: C,
    ) -> Result<(IndexProverKey<F, PC>, IndexVerifierKey<F, PC>), Error<PC::Error>> {
        let index_time = start_timer!(|| "Marlin::Index");

        // TODO: Add check that c is in the correct mode.
        let index = AHPForR1CS::index(c)?;
        if srs.max_degree() < index.max_degree(MC::ZK) {
            Err(Error::IndexTooLarge)?;
        }

        let coeff_support = AHPForR1CS::get_degree_bounds(&index.index_info);
        // Marlin only needs degree 2 random polynomials
        let supported_hiding_bound = if MC::ZK { 1 } else { 0 };

        let (committer_key, verifier_key) =
            PC::trim(srs,
                     index.max_degree(MC::ZK),
                     supported_hiding_bound,
                     Some(&coeff_support)
            ).map_err(Error::from_pc_err)?;

        let commit_time = start_timer!(|| "Commit to index polynomials");
        let (index_comms, index_comm_rands): (_, _) =
            PC::commit(&committer_key, index.iter(), None).map_err(Error::from_pc_err)?;
        end_timer!(commit_time);

        let index_comms = index_comms
            .into_iter()
            .map(|c| c.commitment().clone())
            .collect();
        let index_vk = IndexVerifierKey {
            index_info: index.index_info,
            index_comms,
            verifier_key,
        };

        let index_pk = IndexProverKey {
            index,
            index_comm_rands,
            index_vk: index_vk.clone(),
            committer_key,
        };

        end_timer!(index_time);

        Ok((index_pk, index_vk))
    }

    // Cast a generic type to its dynamic type
    fn get_rng<R: RngCore>(zk_rng: &mut Option<R>) -> Option<&mut dyn RngCore> {
        let zk_rng_mut = zk_rng.as_mut();
        if zk_rng_mut.is_some() { Some(zk_rng_mut.unwrap()) } else { None }
    }

    /// Create a zkSNARK asserting that the constraint system is satisfied.
    pub fn prove<C: ConstraintSynthesizer<F>, R: RngCore>(
        index_pk: &IndexProverKey<F, PC>,
        c: C,
        zk_rng: &mut Option<R>,
    ) -> Result<Proof<F, PC>, Error<PC::Error>> {
        // let mut none_zk_rng: Option<R> = None;
        assert!(zk_rng.is_some() && MC::ZK || zk_rng.is_none() && !MC::ZK);
        let prover_time = start_timer!(|| "Marlin::Prover");
        // Add check that c is in the correct mode.

        let prover_init_state = AHPForR1CS::prover_init(&index_pk.index, c, MC::ZK)?;
        let public_input = prover_init_state.public_input();
        let mut fs_rng = FiatShamirRng::<D>::from_seed(
            &to_bytes![&Self::PROTOCOL_NAME, &index_pk.index_vk, &public_input].unwrap(),
        );

        // --------------------------------------------------------------------
        // First round

        let (prover_first_msg, prover_first_oracles, prover_state) =
            AHPForR1CS::prover_first_round(prover_init_state, zk_rng)?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_comms, first_comm_rands) = PC::commit(
            &index_pk.committer_key,
            prover_first_oracles.iter(),
            Self::get_rng(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(first_round_comm_time);

        fs_rng.absorb(&to_bytes![first_comms, prover_first_msg].unwrap());

        let (verifier_first_msg, verifier_state) =
            AHPForR1CS::verifier_first_round(index_pk.index_vk.index_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let (prover_second_msg, prover_second_oracles, prover_state) =
            AHPForR1CS::prover_second_round(&verifier_first_msg, prover_state, zk_rng);

        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_comms, second_comm_rands) = PC::commit(
            &index_pk.committer_key,
            prover_second_oracles.iter(),
            Self::get_rng(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(second_round_comm_time);

        fs_rng.absorb(&to_bytes![second_comms, prover_second_msg].unwrap());

        let (verifier_second_msg, verifier_state) =
            AHPForR1CS::verifier_second_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let (prover_third_msg, prover_third_oracles) =
            AHPForR1CS::prover_third_round(&verifier_second_msg, prover_state, zk_rng)?;

        let third_round_comm_time = start_timer!(|| "Committing to third round polys");
        let (third_comms, third_comm_rands) = PC::commit(
            &index_pk.committer_key,
            prover_third_oracles.iter(),
            Self::get_rng(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(third_round_comm_time);

        fs_rng.absorb(&to_bytes![third_comms, prover_third_msg].unwrap());

        let verifier_state = AHPForR1CS::verifier_third_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = index_pk
            .index
            .iter()
            .chain(prover_first_oracles.iter())
            .chain(prover_second_oracles.iter())
            .chain(prover_third_oracles.iter())
            .collect();

        // Gather commitments in one vector.
        #[rustfmt::skip]
        let commitments = vec![
            first_comms.iter().map(|p| p.commitment().clone()).collect(),
            second_comms.iter().map(|p| p.commitment().clone()).collect(),
            third_comms.iter().map(|p| p.commitment().clone()).collect(),
        ];
        let labeled_comms: Vec<_> = index_pk
            .index_vk
            .iter()
            .cloned()
            .zip(&AHPForR1CS::<F>::INDEXER_POLYNOMIALS)
            .map(|(c, l)| LabeledCommitment::new(l.to_string(), c, None))
            .chain(first_comms.iter().cloned())
            .chain(second_comms.iter().cloned())
            .chain(third_comms.iter().cloned())
            .collect();

        // Gather commitment randomness together.
        let comm_rands: Vec<LabeledRandomness<PC::Randomness>> = index_pk
            .index_comm_rands
            .clone()
            .into_iter()
            .chain(first_comm_rands)
            .chain(second_comm_rands)
            .chain(third_comm_rands)
            .collect();

        // Gather prover messages together.
        let prover_messages = vec![prover_first_msg, prover_second_msg, prover_third_msg];

        let proof = if MC::LC_OPT {
            Self::prove_lcs(
                index_pk,
                public_input,
                verifier_state,
                polynomials,
                commitments,
                labeled_comms,
                comm_rands,
                prover_messages,
                fs_rng,
                zk_rng
            )
        } else {
            Self::prove_no_lcs(
                index_pk,
                verifier_state,
                polynomials,
                commitments,
                labeled_comms,
                comm_rands,
                prover_messages,
                fs_rng,
                zk_rng
            )
        }?;
        end_timer!(prover_time);

        proof.print_size_info();
        Ok(proof)
    }

    fn prove_no_lcs<R: RngCore>(
        index_pk:        &IndexProverKey<F, PC>,
        verifier_state:  VerifierState<F>,
        polynomials:     Vec<&LabeledPolynomial<F>>,
        commitments:     Vec<Vec<PC::Commitment>>,
        labeled_comms:   Vec<LabeledCommitment<PC::Commitment>>,
        comm_rands:      Vec<LabeledRandomness<PC::Randomness>>,
        prover_messages: Vec<ProverMsg<F>>,
        mut fs_rng:      FiatShamirRng<D>,
        zk_rng: &mut Option<R>,
    ) -> Result<Proof<F, PC>, Error<PC::Error>> {

        // Compute the AHP verifier's query set.
        let (query_set, _) =
            AHPForR1CS::verifier_query_set(verifier_state, &mut fs_rng);

        let eval_time = start_timer!(|| "Evaluating polynomials over query set");

        let mut evaluations = evaluate_query_set_to_vec(
            polynomials.clone(), &query_set
        );

        evaluations.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations.into_iter().map(|x| x.1).collect::<Vec<F>>();
        end_timer!(eval_time);

        fs_rng.absorb(&evaluations);
        let opening_challenge: F = u128::rand(&mut fs_rng).into();
        let opening_challenges = |pow| opening_challenge.pow(&[pow]);

        let opening_time = start_timer!(|| "Compute opening proof");
        let proof = PC::batch_open_individual_opening_challenges(
            &index_pk.committer_key,
            polynomials.clone(),
            &labeled_comms,
            &query_set,
            &opening_challenges,
            &comm_rands,
            Self::get_rng(zk_rng),
        ).map_err(Error::from_pc_err)?;
        end_timer!(opening_time);

        Ok(Proof::new(commitments, evaluations, prover_messages, BatchLCProof::<F, PC>{ proof, evals: None }))
    }

    fn prove_lcs<R: RngCore>(
        index_pk:        &IndexProverKey<F, PC>,
        public_input:    Vec<F>,
        verifier_state:  VerifierState<F>,
        polynomials:     Vec<&LabeledPolynomial<F>>,
        commitments:     Vec<Vec<PC::Commitment>>,
        labeled_comms:   Vec<LabeledCommitment<PC::Commitment>>,
        comm_rands:      Vec<LabeledRandomness<PC::Randomness>>,
        prover_messages: Vec<ProverMsg<F>>,
        mut fs_rng:      FiatShamirRng<D>,
        zk_rng: &mut Option<R>,
    ) -> Result<Proof<F, PC>, Error<PC::Error>>
    {
        // Compute the AHP verifier's query set.
        let (query_set, verifier_state) =
            AHPForR1CS::verifier_lcs_query_set(verifier_state, &mut fs_rng);
        let lc_s = AHPForR1CS::construct_linear_combinations(
            &public_input,
            &polynomials,
            &verifier_state,
        )?;

        let eval_time = start_timer!(|| "Evaluating linear combinations over query set");
        let mut evaluations = Vec::new();
        for (label, (point_label, point)) in &query_set {
            let lc = lc_s
                .iter()
                .find(|lc| &lc.label == label)
                .ok_or(ahp::Error::MissingEval(label.to_string()))?;
            let eval = polynomials.get_lc_eval(&lc, *point)?;
            if !AHPForR1CS::<F>::LC_WITH_ZERO_EVAL.contains(&lc.label.as_ref()) {
                evaluations.push(((label.to_string(), point_label.to_string()), eval));
            }
        }
        evaluations.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations.into_iter().map(|x| x.1).collect::<Vec<F>>();
        end_timer!(eval_time);

        fs_rng.absorb(&evaluations);
        let opening_challenge: F = u128::rand(&mut fs_rng).into();

        let opening_time = start_timer!(|| "Compute opening proof");
        let pc_proof = PC::open_combinations(
            &index_pk.committer_key,
            &lc_s,
            polynomials,
            &labeled_comms,
            &query_set,
            opening_challenge,
            &comm_rands,
            Self::get_rng(zk_rng),
        ).map_err(Error::from_pc_err)?;
        end_timer!(opening_time);

        Ok(Proof::new(commitments, evaluations, prover_messages, pc_proof))
    }

    /// Verify that a proof for the constrain system defined by `C` asserts that
    /// all constraints are satisfied.
    pub fn verify<R: RngCore>(
        index_vk: &IndexVerifierKey<F, PC>,
        public_input: &[F],
        proof: &Proof<F, PC>,
        rng: &mut R,
    ) -> Result<bool, Error<PC::Error>> {
        let verifier_time = start_timer!(|| "Marlin Verifier");

        if !MC::LC_OPT {
            // Check AHP (e.g. sumcheck equations)
            let ahp_result = Self::verify_ahp(
                index_vk,
                &public_input,
                proof,
            );

            if ahp_result.is_err() {
                end_timer!(verifier_time);
                println!("AHP Verification failed: {:?}", ahp_result.err());
                return Ok(false)
            }

            let (query_set, evaluations, commitments, mut fs_rng) = ahp_result.unwrap();

            // Check opening proof
            let opening_result = Self::verify_opening(
                index_vk,
                proof,
                commitments,
                query_set,
                evaluations,
                &mut fs_rng,
                rng
            );

            if opening_result.is_err() {
                end_timer!(verifier_time);
                println!("Opening proof Verification failed: {:?}", opening_result.err());
                return Ok(false)
            }

            end_timer!(verifier_time);
            opening_result
        } else {
            let result = Self::verify_lcs(
                index_vk,
                proof,
                public_input,
                rng
            );

            if result.is_err() {
                end_timer!(verifier_time);
                println!("AHP Verification failed: {:?}", result.err());
                return Ok(false)
            }

            end_timer!(verifier_time);
            result
        }
    }

    /// Verify that a proof for the constrain system defined by `C` asserts that
    /// all constraints are satisfied. Checks only that the sumcheck equations
    /// are satisfied.
    pub fn verify_ahp<'a>(
        index_vk:       &IndexVerifierKey<F, PC>,
        public_input:   &[F],
        proof:          &Proof<F, PC>,
    )  -> Result<(
            QuerySet<'a, F>,
            Evaluations<'a, F>,
            Vec<LabeledCommitment<PC::Commitment>>,
            FiatShamirRng<D>
        ), Error<PC::Error>> {
        assert!(!MC::LC_OPT);

        let ahp_verification_time = start_timer!(|| "Verify Sumcheck equations");

        let public_input = {
            let domain_x = get_best_evaluation_domain::<F>(public_input.len() + 1).unwrap();

            let mut unpadded_input = public_input.to_vec();
            unpadded_input.resize(
                std::cmp::max(public_input.len(), domain_x.size() - 1),
                F::zero(),
            );

            unpadded_input
        };

        let mut fs_rng = FiatShamirRng::<D>::from_seed(
            &to_bytes![&Self::PROTOCOL_NAME, &index_vk, &public_input].unwrap(),
        );

        // --------------------------------------------------------------------
        // First round

        let first_comms = &proof.commitments[0];
        fs_rng.absorb(&to_bytes![first_comms, proof.prover_messages[0]].unwrap());

        let (_, verifier_state) =
            AHPForR1CS::verifier_first_round(index_vk.index_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        let second_comms = &proof.commitments[1];
        fs_rng.absorb(&to_bytes![second_comms, proof.prover_messages[1]].unwrap());

        let (_, verifier_state) = AHPForR1CS::verifier_second_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let third_comms = &proof.commitments[2];
        fs_rng.absorb(&to_bytes![third_comms, proof.prover_messages[2]].unwrap());

        let verifier_state = AHPForR1CS::verifier_third_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // Collect degree bounds for commitments. Indexed polynomials have *no*
        // degree bounds because we know the committed index polynomial has the
        // correct degree.
        let index_info = index_vk.index_info;
        let degree_bounds = vec![None; index_vk.index_comms.len()]
            .into_iter()
            .chain(AHPForR1CS::prover_first_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::prover_second_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::prover_third_round_degree_bounds(&index_info))
            .collect::<Vec<_>>();

        // Gather commitments in one vector.
        let commitments: Vec<_> = index_vk
            .iter()
            .chain(first_comms)
            .chain(second_comms)
            .chain(third_comms)
            .cloned()
            .zip(AHPForR1CS::<F>::polynomial_labels())
            .zip(degree_bounds)
            .map(|((c, l), d)| LabeledCommitment::new(l, c, d))
            .collect();

        // Check sumchecks equations
        let (query_set, verifier_state) =
            AHPForR1CS::verifier_query_set(verifier_state, &mut fs_rng);

        let mut evaluations = Evaluations::new();
        let mut evaluation_labels = Vec::new();
        for (poly_label, (point_label, point)) in query_set.iter().cloned() {
            evaluation_labels.push(((poly_label, point_label), point));
        }

        evaluation_labels.sort_by(|a, b| a.0.cmp(&b.0));
        for (q, eval) in evaluation_labels.into_iter().zip(&proof.evaluations) {
            evaluations.insert(((q.0).0, q.1), *eval);
        }

        AHPForR1CS::verify_sumchecks(
            &public_input,
            &evaluations,
            &verifier_state,
        )?;

        end_timer!(ahp_verification_time);

        Ok((query_set, evaluations, commitments, fs_rng))
    }

    /// Verify that a proof for the constrain system defined by `C` asserts that
    /// all constraints are satisfied. Checks only that the opening proof is
    /// satisfied.
    pub fn verify_opening<'a, R: RngCore>(
        index_vk:       &IndexVerifierKey<F, PC>,
        proof:          &Proof<F, PC>,
        labeled_comms:  Vec<LabeledCommitment<PC::Commitment>>,
        query_set:      QuerySet<'a, F>,
        evaluations:    Evaluations<'a, F>,
        fs_rng:         &mut FiatShamirRng<D>,
        rng:            &mut R,
    ) -> Result<bool, Error<PC::Error>> {
        assert!(!MC::LC_OPT);

        let check_time = start_timer!(|| "Check opening proof");

        fs_rng.absorb(&proof.evaluations);
        let opening_challenge: F = u128::rand(fs_rng).into();
        let opening_challenges = |pow| opening_challenge.pow(&[pow]);

        let result = PC::batch_check_individual_opening_challenges(
            &index_vk.verifier_key,
            &labeled_comms,
            &query_set,
            &evaluations,
            &proof.pc_proof.proof,
            &opening_challenges,
            rng,
        ).map_err(Error::from_pc_err);

        end_timer!(check_time);

        result
    }

    fn verify_lcs<R: RngCore>(
        index_vk:       &IndexVerifierKey<F, PC>,
        proof:          &Proof<F, PC>,
        public_input:   &[F],
        rng:         &mut R,
    ) -> Result<bool, Error<PC::Error>> {
        let check_time = start_timer!(|| "Check sumchecks and opening proofs");

        let public_input = {
            let domain_x = get_best_evaluation_domain::<F>(public_input.len() + 1).unwrap();

            let mut unpadded_input = public_input.to_vec();
            unpadded_input.resize(
                std::cmp::max(public_input.len(), domain_x.size() - 1),
                F::zero(),
            );

            unpadded_input
        };

        let mut fs_rng = FiatShamirRng::<D>::from_seed(
            &to_bytes![&Self::PROTOCOL_NAME, &index_vk, &public_input].unwrap(),
        );

        // --------------------------------------------------------------------
        // First round

        let first_comms = &proof.commitments[0];
        fs_rng.absorb(&to_bytes![first_comms, proof.prover_messages[0]].unwrap());

        let (_, verifier_state) =
            AHPForR1CS::verifier_first_round(index_vk.index_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        let second_comms = &proof.commitments[1];
        fs_rng.absorb(&to_bytes![second_comms, proof.prover_messages[1]].unwrap());

        let (_, verifier_state) = AHPForR1CS::verifier_second_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let third_comms = &proof.commitments[2];
        fs_rng.absorb(&to_bytes![third_comms, proof.prover_messages[2]].unwrap());

        let verifier_state = AHPForR1CS::verifier_third_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // Collect degree bounds for commitments. Indexed polynomials have *no*
        // degree bounds because we know the committed index polynomial has the
        // correct degree.
        let index_info = index_vk.index_info;
        let degree_bounds = vec![None; index_vk.index_comms.len()]
            .into_iter()
            .chain(AHPForR1CS::prover_first_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::prover_second_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::prover_third_round_degree_bounds(&index_info))
            .collect::<Vec<_>>();

        // Gather commitments in one vector.
        let commitments: Vec<_> = index_vk
            .iter()
            .chain(first_comms)
            .chain(second_comms)
            .chain(third_comms)
            .cloned()
            .zip(AHPForR1CS::<F>::polynomial_labels())
            .zip(degree_bounds)
            .map(|((c, l), d)| LabeledCommitment::new(l, c, d))
            .collect();

        let (query_set, verifier_state) =
            AHPForR1CS::verifier_lcs_query_set(verifier_state, &mut fs_rng);

        fs_rng.absorb(&proof.evaluations);
        let opening_challenge: F = u128::rand(&mut fs_rng).into();

        let mut evaluations = Evaluations::new();
        let mut evaluation_labels = Vec::new();
        for (poly_label, (point_label, point)) in query_set.iter().cloned() {
            if AHPForR1CS::<F>::LC_WITH_ZERO_EVAL.contains(&poly_label.as_ref()) {
                evaluations.insert((poly_label, point), F::zero());
            } else {
                evaluation_labels.push(((poly_label, point_label), point));
            }
        }

        evaluation_labels.sort_by(|a, b| a.0.cmp(&b.0));
        for (q, eval) in evaluation_labels.into_iter().zip(&proof.evaluations) {
            evaluations.insert(((q.0).0, q.1), *eval);
        }

        let lc_s = AHPForR1CS::construct_linear_combinations(
            &public_input,
            &evaluations,
            &verifier_state,
        )?;

        let evaluations_are_correct = PC::check_combinations(
            &index_vk.verifier_key,
            &lc_s,
            &commitments,
            &query_set,
            &evaluations,
            &proof.pc_proof,
            opening_challenge,
            rng,
        ).map_err(Error::from_pc_err);
        end_timer!(check_time);

        evaluations_are_correct
    }
}