use crate::ahp::indexer::*;
use crate::ahp::prover::ProverMsg;
use crate::Vec;
use algebra::{Field, PrimeField, AffineCurve};
use algebra_utils::get_best_evaluation_domain;
use poly_commit::{BatchLCProof, PolynomialCommitment, PCPreparedCommitment, PCPreparedVerifierKey};
use r1cs_core::SynthesisError;

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// The universal public parameters for the argument system.
pub type UniversalSRS<G, PC> = <PC as PolynomialCommitment<G>>::UniversalParams;

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// Verification key for a specific index (i.e., R1CS matrices).
pub struct IndexVerifierKey<G: AffineCurve, PC: PolynomialCommitment<G>>
{
    /// Stores information about the size of the index, as well as its field of
    /// definition.
    pub index_info: IndexInfo<G::ScalarField>,
    /// Commitments to the indexed polynomials.
    pub index_comms: Vec<PC::Commitment>,
    /// The verifier key for this index, trimmed from the universal SRS.
    pub verifier_key: PC::VerifierKey,
}

impl<G: AffineCurve, PC: PolynomialCommitment<G>> algebra::ToBytes
    for IndexVerifierKey<G, PC>
{
    fn write<W: std::io::Write>(&self, mut w: W) -> std::io::Result<()> {
        self.index_info.write(&mut w)?;
        self.index_comms.write(&mut w)
    }
}

impl<G: AffineCurve, PC: PolynomialCommitment<G>> Clone
    for IndexVerifierKey<G, PC>
{
    fn clone(&self) -> Self {
        Self {
            index_comms: self.index_comms.clone(),
            index_info: self.index_info.clone(),
            verifier_key: self.verifier_key.clone(),
        }
    }
}

impl<G: AffineCurve, PC: PolynomialCommitment<G>>
    IndexVerifierKey<G, PC>
{
    /// Iterate over the commitments to indexed polynomials in `self`.
    pub fn iter(&self) -> impl Iterator<Item = &PC::Commitment> {
        self.index_comms.iter()
    }
}

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// Verification key, prepared (preprocessed) for use in pairings.
pub struct PreparedIndexVerifierKey<G: AffineCurve, PC: PolynomialCommitment<G>>
{
    /// Size of the variable domain.
    pub domain_h_size: u64,
    /// Size of the matrix domain.
    pub domain_k_size: u64,
    /// Commitments to the index polynomials, prepared.
    pub prepared_index_comms: Vec<PC::PreparedCommitment>,
    /// Prepared version of the poly-commit scheme's verification key.
    pub prepared_verifier_key: PC::PreparedVerifierKey,
    /// Non-prepared verification key, for use in native "prepared verify" (which
    /// is actually standard verify), as well as in absorbing the original vk into
    /// the Fiat-Shamir sponge.
    pub orig_vk: IndexVerifierKey<G, PC>,
}

impl<G, PC> Clone for PreparedIndexVerifierKey<G, PC>
    where
        G: AffineCurve,
        PC: PolynomialCommitment<G>,
{
    fn clone(&self) -> Self {
        PreparedIndexVerifierKey {
            domain_h_size: self.domain_h_size,
            domain_k_size: self.domain_k_size,
            prepared_index_comms: self.prepared_index_comms.clone(),
            prepared_verifier_key: self.prepared_verifier_key.clone(),
            orig_vk: self.orig_vk.clone(),
        }
    }
}

impl<G, PC> PreparedIndexVerifierKey<G, PC>
    where
        G: AffineCurve,
        PC: PolynomialCommitment<G>,
{
    pub fn prepare(vk: &IndexVerifierKey<G, PC>) -> Self {
        let mut prepared_index_comms = Vec::<PC::PreparedCommitment>::new();
        for (_, comm) in vk.index_comms.iter().enumerate() {
            prepared_index_comms.push(PC::PreparedCommitment::prepare(comm));
        }

        let prepared_verifier_key = PC::PreparedVerifierKey::prepare(&vk.verifier_key);

        let domain_h = get_best_evaluation_domain::<G::ScalarField>(vk.index_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();
        let domain_k = get_best_evaluation_domain::<G::ScalarField>(vk.index_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();

        let domain_h_size = domain_h.size();
        let domain_k_size = domain_k.size();

        Self {
            domain_h_size: domain_h_size as u64,
            domain_k_size: domain_k_size as u64,
            prepared_index_comms,
            prepared_verifier_key,
            orig_vk: vk.clone(),
        }
    }
}

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// Proving key for a specific index (i.e., R1CS matrices).
pub struct IndexProverKey<
    G: AffineCurve,
    PC: PolynomialCommitment<G>,
> {
    /// The index verifier key.
    pub index_vk: IndexVerifierKey<G, PC>,
    /// The randomness for the index polynomial commitments.
    pub index_comm_rands: Vec<PC::Randomness>,
    /// The index itself.
    pub index: Index<G::ScalarField>,
    /// The committer key for this index, trimmed from the universal SRS.
    pub committer_key: PC::CommitterKey,
}

impl<G: AffineCurve, PC: PolynomialCommitment<G>> Clone
    for IndexProverKey<G, PC>
where
    PC::Commitment: Clone,
{
    fn clone(&self) -> Self {
        Self {
            index_vk: self.index_vk.clone(),
            index_comm_rands: self.index_comm_rands.clone(),
            index: self.index.clone(),
            committer_key: self.committer_key.clone(),
        }
    }
}

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// A zkSNARK proof.
pub struct Proof<G: AffineCurve, PC: PolynomialCommitment<G>> {
    /// Commitments to the polynomials produced by the AHP prover.
    pub commitments: Vec<Vec<PC::Commitment>>,
    /// Evaluations of these polynomials.
    pub evaluations: Vec<G::ScalarField>,
    /// The field elements sent by the prover.
    pub prover_messages: Vec<ProverMsg<G::ScalarField>>,
    /// An evaluation proof from the polynomial commitment.
    pub pc_proof: BatchLCProof<G, PC>,
}

impl<G: AffineCurve, PC: PolynomialCommitment<G>> Proof<G, PC> {
    /// Construct a new proof.
    pub fn new(
        commitments: Vec<Vec<PC::Commitment>>,
        evaluations: Vec<G::ScalarField>,
        prover_messages: Vec<ProverMsg<G::ScalarField>>,
        pc_proof: BatchLCProof<G, PC>,
    ) -> Self {
        Self {
            commitments,
            evaluations,
            prover_messages,
            pc_proof,
        }
    }

    /// Prints information about the size of the proof.
    pub fn print_size_info(&self) {
        use poly_commit::{PCCommitment, PCProof};

        let size_of_fe_in_bytes = G::ScalarField::zero().into_repr().as_ref().len() * 8;
        let mut num_comms_without_degree_bounds = 0;
        let mut num_comms_with_degree_bounds = 0;
        let mut size_bytes_comms_without_degree_bounds = 0;
        let mut size_bytes_comms_with_degree_bounds = 0;
        let mut size_bytes_proofs = 0;
        for c in self.commitments.iter().flat_map(|c| c) {
            if !c.has_degree_bound() {
                num_comms_without_degree_bounds += 1;
                size_bytes_comms_without_degree_bounds += c.size_in_bytes();
            } else {
                num_comms_with_degree_bounds += 1;
                size_bytes_comms_with_degree_bounds += c.size_in_bytes();
            }
        }

        let proofs: Vec<PC::Proof> = self.pc_proof.proof.clone().into();
        let num_proofs = proofs.len();
        for proof in &proofs {
            size_bytes_proofs += proof.size_in_bytes();
        }

        let num_evals = self.evaluations.len();
        let evals_size_in_bytes = num_evals * size_of_fe_in_bytes;
        let num_prover_messages: usize = self
            .prover_messages
            .iter()
            .map(|v| match v {
                ProverMsg::EmptyMessage => 0,
                ProverMsg::FieldElements(elems) => elems.len(),
            })
            .sum();
        let prover_msg_size_in_bytes = num_prover_messages * size_of_fe_in_bytes;
        let arg_size = size_bytes_comms_with_degree_bounds
            + size_bytes_comms_without_degree_bounds
            + size_bytes_proofs
            + prover_msg_size_in_bytes
            + evals_size_in_bytes;
        let stats = format!(
            "Argument size in bytes: {}\n\n\
             Number of commitments without degree bounds: {}\n\
             Size (in bytes) of commitments without degree bounds: {}\n\
             Number of commitments with degree bounds: {}\n\
             Size (in bytes) of commitments with degree bounds: {}\n\n\
             Number of evaluation proofs: {}\n\
             Size (in bytes) of evaluation proofs: {}\n\n\
             Number of evaluations: {}\n\
             Size (in bytes) of evaluations: {}\n\n\
             Number of field elements in prover messages: {}\n\
             Size (in bytes) of prover message: {}\n",
            arg_size,
            num_comms_without_degree_bounds,
            size_bytes_comms_without_degree_bounds,
            num_comms_with_degree_bounds,
            size_bytes_comms_with_degree_bounds,
            num_proofs,
            size_bytes_proofs,
            num_evals,
            evals_size_in_bytes,
            num_prover_messages,
            prover_msg_size_in_bytes,
        );
        add_to_trace!(|| "Statistics about proof", || stats);
    }
}
