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

use algebra::{Field, ToConstraintField, ToBytes, to_bytes, AffineCurve};
use std::marker::PhantomData;
use poly_commit::{Evaluations, LabeledPolynomial};
use poly_commit::{LabeledCommitment, PCUniversalParams, PolynomialCommitment};
use poly_commit::fiat_shamir::FiatShamirRng;
use r1cs_core::{ConstraintSynthesizer, SynthesisError};
use rand_core::RngCore;
use digest::Digest;

use std::{
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};

mod error;
pub use error::*;

mod data_structures;
pub use data_structures::*;

/// Implements an Algebraic Holographic Proof (AHP) for the R1CS indexed relation.
pub mod ahp;
pub use ahp::AHPForR1CS;
use ahp::EvaluationsProvider;
use algebra_utils::get_best_evaluation_domain;
use crate::ahp::prover::ProverMsg;

#[cfg(test)]
mod test;

/// Configuration parameters for the Marlin proving system
pub trait MarlinConfig: Clone {
    /// Modify internal behaviour for usage with recursive SNARKs
    const FOR_RECURSION: bool;
}

#[derive(Clone)]
/// For standard usage
pub struct MarlinDefaultConfig;

impl MarlinConfig for MarlinDefaultConfig {
    const FOR_RECURSION: bool = false;
}

#[derive(Clone)]
/// For PCD applications
pub struct MarlinRecursiveConfig;

impl MarlinConfig for MarlinRecursiveConfig {
    const FOR_RECURSION: bool = true;
}

/// The compiled argument system.
pub struct Marlin<
    G: AffineCurve,
    PC: PolynomialCommitment<G, RandomOracle = FS>,
    FS: FiatShamirRng<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
    MC: MarlinConfig,
>(
    #[doc(hidden)] PhantomData<G>,
    #[doc(hidden)] PhantomData<PC>,
    #[doc(hidden)] PhantomData<FS>,
    #[doc(hidden)] PhantomData<MC>,
);

fn compute_vk_hash<G, PC, FS>(vk: &IndexVerifierKey<G, PC>) -> Vec<<G::BaseField as Field>::BasePrimeField>
    where
        G: AffineCurve,
        FS: FiatShamirRng<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
        PC: PolynomialCommitment<G, RandomOracle = FS>,
        PC::Commitment: ToConstraintField<<G::BaseField as Field>::BasePrimeField>,
{
    let mut vk_hash_rng = FS::new();
    vk_hash_rng.absorb_native_field_elements(&vk.index_comms);
    vk_hash_rng.squeeze_native_field_elements(1)
}

impl<G: AffineCurve, PC, FS, MC> Marlin<G, PC, FS, MC>
    where
        PC: PolynomialCommitment<G, RandomOracle = FS>,
        PC::VerifierKey: ToConstraintField<<G::BaseField as Field>::BasePrimeField>,
        PC::Commitment: ToConstraintField<<G::BaseField as Field>::BasePrimeField>,
        FS: FiatShamirRng<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
        MC: MarlinConfig,
{
    /// The personalization string for this protocol. Used to personalize the
    /// Fiat-Shamir rng.
    pub const PROTOCOL_NAME: &'static [u8] = b"MARLIN-2019";

    /// Generate the universal prover and verifier keys for the
    /// argument system.
    pub fn universal_setup<R: RngCore, D: Digest>(
        num_constraints: usize,
        num_variables: usize,
        num_non_zero: usize,
        rng: &mut R,
    ) -> Result<UniversalSRS<G, PC>, Error<PC::Error>> {
        let max_degree = AHPForR1CS::<G::ScalarField>::max_degree(num_constraints, num_variables, num_non_zero)?;
        let setup_time = start_timer!(|| {
            format!(
            "Marlin::UniversalSetup with max_degree {}, computed for a maximum of {} constraints, {} vars, {} non_zero",
            max_degree, num_constraints, num_variables, num_non_zero,
        )
        });

        let srs = PC::setup::<_, D>(max_degree, rng).map_err(Error::from_pc_err);
        end_timer!(setup_time);
        srs
    }

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys. This is a deterministic algorithm that anyone can rerun.
    pub fn index<C: ConstraintSynthesizer<G::ScalarField>>(
        srs: &UniversalSRS<G, PC>,
        c: C,
    ) -> Result<(IndexProverKey<G, PC>, IndexVerifierKey<G, PC>), Error<PC::Error>> {
        let index_time = start_timer!(|| "Marlin::Index");

        // TODO: Add check that c is in the correct mode.
        let index = AHPForR1CS::index(c)?;
        if srs.max_degree() < index.max_degree() {
            return Err(Error::IndexTooLarge(index.max_degree()));
        }

        let coeff_support = AHPForR1CS::get_degree_bounds(&index.index_info);

        // Marlin only needs degree 2 random polynomials
        let supported_hiding_bound = 1;
        let (committer_key, verifier_key) =
            PC::trim(srs,
                     index.max_degree(),
                     supported_hiding_bound,
                     Some(&coeff_support)
            ).map_err(Error::from_pc_err)?;

        let mut vanishing_polys = vec![];

        if MC::FOR_RECURSION {
            // To avoid the verifier circuit evaluate these polynomials in non-native field,
            // they are committed and their evaluations at the challenge points is checked
            // via the opening proof (they are very cheap to commit and open anyway)
            let domain_h = get_best_evaluation_domain::<G::ScalarField>(index.index_info.num_constraints)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
            let domain_k = get_best_evaluation_domain::<G::ScalarField>(index.index_info.num_non_zero)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

            vanishing_polys = vec![
                LabeledPolynomial::new(
                    "vanishing_poly_h".to_string(),
                    domain_h.vanishing_polynomial().into(),
                    None,
                    None,
                ),
                LabeledPolynomial::new(
                    "vanishing_poly_k".to_string(),
                    domain_k.vanishing_polynomial().into(),
                    None,
                    None,
                ),
            ];
        }

        let commit_time = start_timer!(|| "Commit to index polynomials");
        let (index_comms, index_comm_rands): (_, _) =
            PC::commit(
                &committer_key,
                index.iter().chain(vanishing_polys.iter()),
                None
            ).map_err(Error::from_pc_err)?;
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

    /// Create a zkSNARK asserting that the constraint system is satisfied.
    pub fn prove<C: ConstraintSynthesizer<G::ScalarField>, R: RngCore>(
        index_pk: &IndexProverKey<G, PC>,
        c: C,
        zk_rng: &mut R,
    ) -> Result<Proof<G, PC>, Error<PC::Error>> {
        let prover_time = start_timer!(|| "Marlin::Prover");
        // Add check that c is in the correct mode.

        let for_recursion = MC::FOR_RECURSION;

        let prover_init_state = AHPForR1CS::prover_init(&index_pk.index, c)?;
        let public_input = prover_init_state.public_input();

        let mut fs_rng = FS::new();
        
        fs_rng.absorb_bytes(&to_bytes![&Self::PROTOCOL_NAME].unwrap());
        fs_rng.absorb_native_field_elements(&compute_vk_hash::<G, PC, FS>(
            &index_pk.index_vk,
        ));
        fs_rng.absorb_nonnative_field_elements(&public_input);

        // --------------------------------------------------------------------
        // First round

        let (prover_first_msg, prover_first_oracles, prover_state) =
            AHPForR1CS::prover_first_round(prover_init_state, zk_rng)?;

        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_comms, first_comm_rands) = PC::commit(
            &index_pk.committer_key,
            prover_first_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(first_round_comm_time);
        
        fs_rng.absorb_native_field_elements(&first_comms);
        match prover_first_msg.clone() {
            ProverMsg::EmptyMessage => (),
            ProverMsg::FieldElements(v) => fs_rng.absorb_nonnative_field_elements(&v),
        }

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
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(second_round_comm_time);

        fs_rng.absorb_native_field_elements(&second_comms);
        match prover_second_msg.clone() {
            ProverMsg::EmptyMessage => (),
            ProverMsg::FieldElements(v) => fs_rng.absorb_nonnative_field_elements(&v),
        }

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
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(third_round_comm_time);

        fs_rng.absorb_native_field_elements(&third_comms);
        match prover_third_msg.clone() {
            ProverMsg::EmptyMessage => (),
            ProverMsg::FieldElements(v) => fs_rng.absorb_nonnative_field_elements(&v),
        }

        let verifier_state = AHPForR1CS::verifier_third_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        let vanishing_polys = if for_recursion {
            let domain_h = get_best_evaluation_domain::<G::ScalarField>(index_pk.index.index_info.num_constraints)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
            let domain_k = get_best_evaluation_domain::<G::ScalarField>(index_pk.index.index_info.num_non_zero)
                .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

            vec![
                LabeledPolynomial::new(
                    "vanishing_poly_h".to_string(),
                    domain_h.vanishing_polynomial().into(),
                    None,
                    None,
                ),
                LabeledPolynomial::new(
                    "vanishing_poly_k".to_string(),
                    domain_k.vanishing_polynomial().into(),
                    None,
                    None,
                ),
            ]
        } else {
            vec![]
        };

        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = index_pk
            .index
            .iter()
            .chain(vanishing_polys.iter())
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

        let indexer_polynomials = if for_recursion {
            AHPForR1CS::<G::ScalarField>::INDEXER_POLYNOMIALS_WITH_VANISHING
                .clone()
                .to_vec()
        } else {
            AHPForR1CS::<G::ScalarField>::INDEXER_POLYNOMIALS.clone().to_vec()
        };

        let labeled_comms: Vec<_> = index_pk
            .index_vk
            .iter()
            .cloned()
            .zip(indexer_polynomials)
            .map(|(c, l)| LabeledCommitment::new(l.to_string(), c, None))
            .chain(first_comms.iter().cloned())
            .chain(second_comms.iter().cloned())
            .chain(third_comms.iter().cloned())
            .collect();

        // Gather commitment randomness together.
        let comm_rands: Vec<PC::Randomness> = index_pk
            .index_comm_rands
            .clone()
            .into_iter()
            .chain(first_comm_rands)
            .chain(second_comm_rands)
            .chain(third_comm_rands)
            .collect();

        // Compute the AHP verifier's query set.
        let (query_set, verifier_state) =
            AHPForR1CS::verifier_query_set(verifier_state, &mut fs_rng, for_recursion);
        let lc_s = AHPForR1CS::construct_linear_combinations(
            &public_input,
            &polynomials,
            &verifier_state,
            for_recursion
        )?;

        let eval_time = start_timer!(|| "Evaluating linear combinations over query set");
        let mut evaluations = Vec::new();
        for (label, (_, point)) in &query_set {
            let lc = lc_s
                .iter()
                .find(|lc| &lc.label == label)
                .ok_or(ahp::Error::MissingEval(label.to_string()))?;
            let eval = polynomials.get_lc_eval(&lc, *point)?;
            if !AHPForR1CS::<G::ScalarField>::LC_WITH_ZERO_EVAL.contains(&lc.label.as_ref()) {
                evaluations.push((label.to_string(), eval));
            }
        }
        evaluations.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations.into_iter().map(|x| x.1).collect::<Vec<G::ScalarField>>();
        end_timer!(eval_time);
        
        fs_rng.absorb_nonnative_field_elements(&evaluations);

        let pc_proof = if for_recursion {
            let num_open_challenges: usize = polynomials.len();

            let mut opening_challenges = Vec::<G::ScalarField>::new();
            opening_challenges
                .append(&mut fs_rng.squeeze_128_bits_nonnative_field_elements(num_open_challenges));

            let opening_challenges_f = |i| opening_challenges[i as usize];

            PC::open_combinations_individual_opening_challenges(
                &index_pk.committer_key,
                &lc_s,
                polynomials,
                &labeled_comms,
                &query_set,
                &opening_challenges_f,
                &comm_rands,
                Some(zk_rng),
                &mut fs_rng
            )
                .map_err(Error::from_pc_err)?
        } else {
            let opening_challenge: G::ScalarField = fs_rng.squeeze_128_bits_nonnative_field_elements(1)[0];

            PC::open_combinations(
                &index_pk.committer_key,
                &lc_s,
                polynomials,
                &labeled_comms,
                &query_set,
                opening_challenge,
                &comm_rands,
                Some(zk_rng),
                &mut fs_rng
            )
                .map_err(Error::from_pc_err)?
        };

        // Gather prover messages together.
        let prover_messages = vec![prover_first_msg, prover_second_msg, prover_third_msg];

        let proof = Proof::new(commitments, evaluations, prover_messages, pc_proof);
        proof.print_size_info();
        end_timer!(prover_time);
        Ok(proof)
    }

    /// Verify that a proof for the constrain system defined by `C` asserts that
    /// all constraints are satisfied.
    pub fn verify<R: RngCore>(
        index_vk: &IndexVerifierKey<G, PC>,
        public_input: &[G::ScalarField],
        proof: &Proof<G, PC>,
        rng: &mut R,
    ) -> Result<bool, Error<PC::Error>> {
        let verifier_time = start_timer!(|| "Marlin::Verify");

        let for_recursion = MC::FOR_RECURSION;

        let public_input = {
            let domain_x = get_best_evaluation_domain::<G::ScalarField>(public_input.len() + 1).unwrap();

            let mut unpadded_input = public_input.to_vec();
            unpadded_input.resize(
                std::cmp::max(public_input.len(), domain_x.size() - 1),
                G::ScalarField::zero(),
            );

            unpadded_input
        };

        let mut fs_rng = FS::new();
        
        fs_rng.absorb_bytes(&to_bytes![&Self::PROTOCOL_NAME].unwrap());
        fs_rng.absorb_native_field_elements(&compute_vk_hash::<G, PC, FS>(index_vk));
        fs_rng.absorb_nonnative_field_elements(&public_input);

        // --------------------------------------------------------------------
        // First round

        let first_comms = &proof.commitments[0];
        fs_rng.absorb_native_field_elements(&first_comms);
        match proof.prover_messages[0].clone() {
            ProverMsg::EmptyMessage => (),
            ProverMsg::FieldElements(v) => fs_rng.absorb_nonnative_field_elements(&v),
        };

        let (_, verifier_state) =
            AHPForR1CS::verifier_first_round(index_vk.index_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        let second_comms = &proof.commitments[1];
        fs_rng.absorb_native_field_elements(&second_comms);
        match proof.prover_messages[1].clone() {
            ProverMsg::EmptyMessage => (),
            ProverMsg::FieldElements(v) => fs_rng.absorb_nonnative_field_elements(&v),
        };

        let (_, verifier_state) = AHPForR1CS::verifier_second_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Third round
        let third_comms = &proof.commitments[2];
        fs_rng.absorb_native_field_elements(&third_comms);
        match proof.prover_messages[2].clone() {
            ProverMsg::EmptyMessage => (),
            ProverMsg::FieldElements(v) => fs_rng.absorb_nonnative_field_elements(&v),
        };

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

        let polynomial_labels: Vec<String> = if for_recursion {
            AHPForR1CS::<G::ScalarField>::polynomial_labels_with_vanishing().collect()
        } else {
            AHPForR1CS::<G::ScalarField>::polynomial_labels().collect()
        };

        // Gather commitments in one vector.
        let commitments: Vec<_> = index_vk
            .iter()
            .chain(first_comms)
            .chain(second_comms)
            .chain(third_comms)
            .cloned()
            .zip(polynomial_labels)
            .zip(degree_bounds)
            .map(|((c, l), d)| LabeledCommitment::new(l, c, d))
            .collect();

        let (query_set, verifier_state) =
            AHPForR1CS::verifier_query_set(verifier_state, &mut fs_rng, for_recursion);

        fs_rng.absorb_nonnative_field_elements(&proof.evaluations);

        let mut evaluations = Evaluations::new();
        let mut evaluation_labels = Vec::new();
        for (poly_label, (_, point)) in query_set.iter().cloned() {
            if AHPForR1CS::<G::ScalarField>::LC_WITH_ZERO_EVAL.contains(&poly_label.as_ref()) {
                evaluations.insert((poly_label, point), G::ScalarField::zero());
            } else {
                evaluation_labels.push((poly_label, point));
            }
        }

        evaluation_labels.sort_by(|a, b| a.0.cmp(&b.0));
        for (q, eval) in evaluation_labels.into_iter().zip(&proof.evaluations) {
            evaluations.insert(q, *eval);
        }

        let lc_s = AHPForR1CS::construct_linear_combinations(
            &public_input,
            &evaluations,
            &verifier_state,
            for_recursion,
        )?;

        let evaluations_are_correct = if for_recursion {
            let num_open_challenges: usize = commitments.len();

            let mut opening_challenges = Vec::<G::ScalarField>::new();
            opening_challenges
                .append(&mut fs_rng.squeeze_128_bits_nonnative_field_elements(num_open_challenges));

            let opening_challenges_f = |i| opening_challenges[i as usize];
            PC::check_combinations_individual_opening_challenges(
                &index_vk.verifier_key,
                &lc_s,
                &commitments,
                &query_set,
                &evaluations,
                &proof.pc_proof,
                &opening_challenges_f,
                rng,
                &mut fs_rng
            )
                .map_err(Error::from_pc_err)?
        } else {
            let opening_challenge: G::ScalarField = fs_rng.squeeze_128_bits_nonnative_field_elements(1)[0];

            PC::check_combinations(
                &index_vk.verifier_key,
                &lc_s,
                &commitments,
                &query_set,
                &evaluations,
                &proof.pc_proof,
                opening_challenge,
                rng,
                &mut fs_rng
            )
                .map_err(Error::from_pc_err)?
        };

        if !evaluations_are_correct {
            eprintln!("PC::Check failed");
        }
        end_timer!(verifier_time, || format!(
            " PC::Check for AHP Verifier linear equations: {}",
            evaluations_are_correct
        ));
        Ok(evaluations_are_correct)
    }
}
