use algebra::{ToBytes, to_bytes, ToConstraintField, PrimeField, AffineCurve, Field};
use algebra_utils::domain::get_best_evaluation_domain;
use crate::ahp::prover::ProverMsg;
use crate::{
    constraints::verifier::MarlinVerifierGadget,
    data_structures::{IndexVerifierKey, PreparedIndexVerifierKey, Proof},
};
use poly_commit::{
    fiat_shamir::{constraints::FiatShamirRngGadget, FiatShamirRng},
    constraints::{PolynomialCommitmentGadget, PrepareGadget},
    PolynomialCommitment
};
use r1cs_std::{
    alloc::{AllocGadget, ConstantGadget},
    fields::{
        FieldGadget,
        fp::FpGadget,
        nonnative::nonnative_field_gadget::NonNativeFieldGadget,
    },
    uint8::UInt8,
    ToBytesGadget, to_field_gadget_vec::ToConstraintFieldGadget,
};
use r1cs_core::{ConstraintSystem, SynthesisError};
use std::{collections::HashMap, borrow::Borrow};

pub struct IndexVerifierKeyGadget<
    G: AffineCurve,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentGadget<G, PC>,
> {
    pub domain_h_size:        u64,
    pub domain_k_size:        u64,
    pub domain_h_size_gadget: FpGadget<<G::BaseField as Field>::BasePrimeField>,
    pub domain_k_size_gadget: FpGadget<<G::BaseField as Field>::BasePrimeField>,
    pub domain_h_gen_gadget:  NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
    pub domain_k_gen_gadget:  NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
    pub index_comms:          Vec<PCG::CommitmentGadget>,
    pub verifier_key:         PCG::VerifierKeyGadget,
}

impl<G, PC, PCG> IndexVerifierKeyGadget<G, PC, PCG>
    where
        G: AffineCurve,
        PC: PolynomialCommitment<G>,
        PCG: PolynomialCommitmentGadget<G, PC>,
{
    pub fn iter(&self) -> impl Iterator<Item = &PCG::CommitmentGadget> {
        self.index_comms.iter()
    }
}

impl<G, PC, PCG> AllocGadget<IndexVerifierKey<G, PC>, <G::BaseField as Field>::BasePrimeField> for IndexVerifierKeyGadget<G, PC, PCG>
where
    G: AffineCurve,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentGadget<G, PC>,
{
    fn alloc<F, T, CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(mut cs: CS, f: F) -> Result<Self, SynthesisError> where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<IndexVerifierKey<G, PC>>
    {
        let t = f()?;
        let ivk = t.borrow();

        let mut index_comms = Vec::<PCG::CommitmentGadget>::new();
        for (i, index_comm) in ivk.index_comms.iter().enumerate() {
            index_comms.push(PCG::CommitmentGadget::alloc(
                cs.ns(|| format!("alloc index comm {}", i)),
                || Ok(index_comm),
            )?);
        }

        let verifier_key = PCG::VerifierKeyGadget::alloc(
            cs.ns(|| "alloc verifier_key"),
            || Ok(&ivk.verifier_key),
        )?;

        let domain_h = get_best_evaluation_domain::<G::ScalarField>(ivk.index_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = get_best_evaluation_domain::<G::ScalarField>(ivk.index_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_h_size_gadget = FpGadget::<<G::BaseField as Field>::BasePrimeField>::alloc(
            cs.ns(|| "alloc domain_h_size"),
            || Ok(<G::BaseField as Field>::BasePrimeField::from(domain_h.size() as u128)),
        )?;

        let domain_k_size_gadget = FpGadget::<<G::BaseField as Field>::BasePrimeField>::alloc(
            cs.ns(|| "alloc domain_k_size"),
            || Ok(<G::BaseField as Field>::BasePrimeField::from(domain_k.size() as u128)),
        )?;

        let domain_h_gen_gadget = NonNativeFieldGadget::alloc(
            cs.ns(|| "alloc domain_h_gen"),
            || Ok(domain_h.group_gen()),
        )?;

        let domain_k_gen_gadget = NonNativeFieldGadget::alloc(
            cs.ns(|| "alloc domain_k_gen"),
            || Ok(domain_k.group_gen()),
        )?;

        Ok(IndexVerifierKeyGadget {
            domain_h_size: domain_h.size() as u64,
            domain_k_size: domain_k.size() as u64,
            domain_h_size_gadget,
            domain_k_size_gadget,
            domain_h_gen_gadget,
            domain_k_gen_gadget,
            index_comms,
            verifier_key,
        })
    }

    fn alloc_input<F, T, CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(mut cs: CS, f: F) -> Result<Self, SynthesisError> where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<IndexVerifierKey<G, PC>>
    {
        let t = f()?;
        let ivk = t.borrow();

        let mut index_comms = Vec::<PCG::CommitmentGadget>::new();
        for (i, index_comm) in ivk.index_comms.iter().enumerate() {
            index_comms.push(PCG::CommitmentGadget::alloc_input(
                cs.ns(|| format!("alloc input index comm {}", i)),
                || Ok(index_comm),
            )?);
        }

        let verifier_key = PCG::VerifierKeyGadget::alloc_input(
            cs.ns(|| "alloc input verifier_key"),
            || Ok(&ivk.verifier_key),
        )?;

        let domain_h = get_best_evaluation_domain::<G::ScalarField>(ivk.index_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = get_best_evaluation_domain::<G::ScalarField>(ivk.index_info.num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_h_size_gadget = FpGadget::<<G::BaseField as Field>::BasePrimeField>::alloc_input(
            cs.ns(|| "alloc input domain_h_size"),
            || Ok(<G::BaseField as Field>::BasePrimeField::from(domain_h.size() as u128)),
        )?;

        let domain_k_size_gadget = FpGadget::<<G::BaseField as Field>::BasePrimeField>::alloc_input(
            cs.ns(|| "alloc input domain_k_size"),
            || Ok(<G::BaseField as Field>::BasePrimeField::from(domain_k.size() as u128)),
        )?;

        let domain_h_gen_gadget = NonNativeFieldGadget::alloc_input(
            cs.ns(|| "alloc input domain_h_gen"),
            || Ok(domain_h.group_gen()),
        )?;

        let domain_k_gen_gadget = NonNativeFieldGadget::alloc_input(
            cs.ns(|| "alloc input domain_k_gen"),
            || Ok(domain_k.group_gen()),
        )?;

        Ok(IndexVerifierKeyGadget {
            domain_h_size: domain_h.size() as u64,
            domain_k_size: domain_k.size() as u64,
            domain_h_size_gadget,
            domain_k_size_gadget,
            domain_h_gen_gadget,
            domain_k_gen_gadget,
            index_comms,
            verifier_key,
        })
    }
}

impl<G, PC, PCG> ToBytesGadget<<G::BaseField as Field>::BasePrimeField> for IndexVerifierKeyGadget<G, PC, PCG>
    where
        G: AffineCurve,
        PC: PolynomialCommitment<G>,
        PCG: PolynomialCommitmentGadget<G, PC>,
{
    fn to_bytes<CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError>
    {
        let mut res = Vec::<UInt8>::new();

        res.append(&mut self.domain_h_size_gadget.to_bytes(cs.ns(|| "domain_h_size to bytes"))?);
        res.append(&mut self.domain_k_size_gadget.to_bytes(cs.ns(|| "domain_k_size to bytes"))?);
        res.append(&mut self.domain_h_gen_gadget.to_bytes(cs.ns(|| "domain_h_gen to bytes"))?);
        res.append(&mut self.domain_k_gen_gadget.to_bytes(cs.ns(|| "domain_k_gen to bytes"))?);
        res.append(&mut self.verifier_key.to_bytes(cs.ns(|| "vk to bytes"))?);

        for (i, comm) in self.index_comms.iter().enumerate() {
            res.append(&mut comm.to_bytes(cs.ns(|| format!("index_comm_{} to bytes", i)))?);
        }

        Ok(res)
    }

    fn to_bytes_strict<CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(&self, mut cs: CS) -> Result<Vec<UInt8>, SynthesisError>
    {
        let mut res = Vec::<UInt8>::new();

        res.append(&mut self.domain_h_size_gadget.to_bytes_strict(cs.ns(|| "domain_h_size to bytes strict"))?);
        res.append(&mut self.domain_k_size_gadget.to_bytes_strict(cs.ns(|| "domain_k_size to bytes strict"))?);
        res.append(&mut self.domain_h_gen_gadget.to_bytes_strict(cs.ns(|| "domain_h_gen to bytes strict"))?);
        res.append(&mut self.domain_k_gen_gadget.to_bytes_strict(cs.ns(|| "domain_k_gen to bytes strict"))?);
        res.append(&mut self.verifier_key.to_bytes_strict(cs.ns(|| "vk to bytes strict"))?);

        for (i, comm) in self.index_comms.iter().enumerate() {
            res.append(&mut comm.to_bytes_strict(cs.ns(|| format!("index_comm_{} to bytes strict", i)))?);
        }

        Ok(res)
    }
}

impl<G, PC, PCG> Clone for IndexVerifierKeyGadget<G, PC, PCG>
    where
        G: AffineCurve,
        PC: PolynomialCommitment<G>,
        PCG: PolynomialCommitmentGadget<G, PC>,
{
    fn clone(&self) -> Self {
        Self {
            domain_h_size: self.domain_h_size,
            domain_k_size: self.domain_k_size,
            domain_h_size_gadget: self.domain_h_size_gadget.clone(),
            domain_k_size_gadget: self.domain_k_size_gadget.clone(),
            domain_h_gen_gadget: self.domain_h_gen_gadget.clone(),
            domain_k_gen_gadget: self.domain_k_gen_gadget.clone(),
            index_comms: self.index_comms.clone(),
            verifier_key: self.verifier_key.clone(),
        }
    }
}

pub struct PreparedIndexVerifierKeyGadget<
    G: AffineCurve,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentGadget<G, PC>,
> {
    pub domain_h_size: u64,
    pub domain_k_size: u64,
    pub domain_h_size_gadget:  FpGadget<<G::BaseField as Field>::BasePrimeField>,
    pub domain_k_size_gadget:  FpGadget<<G::BaseField as Field>::BasePrimeField>,
    pub domain_h_gen_gadget:   NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
    pub domain_k_gen_gadget:   NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
    pub prepared_index_comms:  Vec<PCG::PreparedCommitmentGadget>,
    pub prepared_verifier_key: PCG::PreparedVerifierKeyGadget,
    pub fs_rng:                PCG::RandomOracleGadget,
}

impl<
    G: AffineCurve,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentGadget<G, PC>,
    > Clone for PreparedIndexVerifierKeyGadget<G, PC, PCG>
{
    fn clone(&self) -> Self {
        PreparedIndexVerifierKeyGadget {
            domain_h_size: self.domain_h_size,
            domain_k_size: self.domain_k_size,
            domain_h_size_gadget: self.domain_h_size_gadget.clone(),
            domain_k_size_gadget: self.domain_k_size_gadget.clone(),
            domain_h_gen_gadget: self.domain_h_gen_gadget.clone(),
            domain_k_gen_gadget: self.domain_k_gen_gadget.clone(),
            prepared_index_comms: self.prepared_index_comms.clone(),
            prepared_verifier_key: self.prepared_verifier_key.clone(),
            fs_rng: self.fs_rng.clone(),
        }
    }
}

impl<G, PC, PCG> PreparedIndexVerifierKeyGadget<G, PC, PCG>
where
    G: AffineCurve,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentGadget<G, PC>,
    PCG::VerifierKeyGadget: ToConstraintFieldGadget<<G::BaseField as Field>::BasePrimeField>,
    PCG::CommitmentGadget: ToConstraintFieldGadget<
        <G::BaseField as Field>::BasePrimeField,
        FieldGadget = FpGadget<<G::BaseField as Field>::BasePrimeField>
    >,
{
    pub fn prepare<CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(
        mut cs: CS,
        vk: &IndexVerifierKeyGadget<G, PC, PCG>
    ) -> Result<Self, SynthesisError> {

        let mut fs_rng_raw = PC::RandomOracle::new();
        fs_rng_raw
            .absorb_bytes(&to_bytes![&MarlinVerifierGadget::<G, PC, PCG>::PROTOCOL_NAME].unwrap());

        let index_vk_hash = {
            let mut vk_hash_rng = PC::RandomOracle::new();

            let mut vk_elems = Vec::<<G::BaseField as Field>::BasePrimeField>::new();
            vk.index_comms.iter().enumerate().for_each(|(i, index_comm)| {
                vk_elems.append(
                    &mut index_comm
                        .to_field_gadget_elements(cs.ns(|| format!("index comm {} to field elements", i)))
                        .unwrap()
                        .iter()
                        .map(|elem| elem.get_value().unwrap_or_default())
                        .collect(),
                );
            });
            vk_hash_rng.absorb_native_field_elements(&vk_elems);
            FpGadget::<<G::BaseField as Field>::BasePrimeField>::alloc(
                cs.ns(|| "alloc vk_hash"),
                || {
                Ok(vk_hash_rng.squeeze_native_field_elements(1)[0])
            })
        }?;

        // Init Fiat Shamir by hardcoding initial state
        let fs_rng = {
            let mut fs_rng = PCG::RandomOracleGadget::from_value(cs.ns(|| "hardcode fs rng"), &fs_rng_raw);
            // in our case the vk hash will be part of our Merkle Tree
            // of admissible keys, the root of which is passed to the circuit.
            fs_rng.enforce_absorb_native_field_elements(
                cs.ns(|| "absorb vk hash"),
                &[index_vk_hash]
            )?;
            fs_rng
        };

        // Most likely only used in Kate to prepare for pairing.
        // In IPA case, prepared_comm = unprepared_comm.
        let mut prepared_index_comms = Vec::<PCG::PreparedCommitmentGadget>::new();
        for (i, comm) in vk.index_comms.iter().enumerate() {
            prepared_index_comms.push(PCG::PreparedCommitmentGadget::prepare(
                cs.ns(|| format!("prepare comm {}", i)),
                comm
            )?);
        }

        let prepared_verifier_key = PCG::PreparedVerifierKeyGadget::prepare(
            cs.ns(|| "prepare verifier key"),
            &vk.verifier_key
        )?;

        Ok(Self {
            domain_h_size: vk.domain_h_size,
            domain_k_size: vk.domain_k_size,
            domain_h_size_gadget: vk.domain_h_size_gadget.clone(),
            domain_k_size_gadget: vk.domain_k_size_gadget.clone(),
            domain_h_gen_gadget: vk.domain_h_gen_gadget.clone(),
            domain_k_gen_gadget: vk.domain_k_gen_gadget.clone(),
            prepared_index_comms,
            prepared_verifier_key,
            fs_rng,
        })
    }
}

impl<G, PC, PCG> AllocGadget<PreparedIndexVerifierKey<G, PC>, <G::BaseField as Field>::BasePrimeField>
    for PreparedIndexVerifierKeyGadget<G, PC, PCG>
where
    G: AffineCurve,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentGadget<G, PC>,
    PC::VerifierKey: ToConstraintField<<G::BaseField as Field>::BasePrimeField>,
    PC::Commitment: ToConstraintField<<G::BaseField as Field>::BasePrimeField>,
    PCG::VerifierKeyGadget: ToConstraintFieldGadget<<G::BaseField as Field>::BasePrimeField>,
    PCG::CommitmentGadget: ToConstraintFieldGadget<
        <G::BaseField as Field>::BasePrimeField,
        FieldGadget = FpGadget<<G::BaseField as Field>::BasePrimeField>
    >,
{
    fn alloc<F, T, CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(mut cs: CS, f: F) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedIndexVerifierKey<G, PC>>
    {
        let t = f()?;
        let obj = t.borrow();

        let mut prepared_index_comms = Vec::<PCG::PreparedCommitmentGadget>::new();
        for (i, index_comm) in obj.prepared_index_comms.iter().enumerate() {
            prepared_index_comms.push(PCG::PreparedCommitmentGadget::alloc(
                cs.ns(|| format!("alloc index_comm {}", i)),
                || Ok(index_comm),
            )?);
        }

        let prepared_verifier_key = PCG::PreparedVerifierKeyGadget::alloc(
            cs.ns(|| "alloc pvk"),
            || Ok(&obj.prepared_verifier_key),
        )?;

        let mut vk_elems = Vec::<<G::BaseField as Field>::BasePrimeField>::new();
        obj.orig_vk.index_comms.iter().for_each(|index_comm| {
            vk_elems.append(&mut index_comm.to_field_elements().unwrap());
        });

        let index_vk_hash = {
            let mut vk_hash_rng = PC::RandomOracle::new();

            vk_hash_rng.absorb_native_field_elements(&vk_elems);
            FpGadget::<<G::BaseField as Field>::BasePrimeField>::alloc(
                cs.ns(|| "alloc vk_hash"),
                || Ok(vk_hash_rng.squeeze_native_field_elements(1)[0]),
            )
        }?;

        let mut fs_rng_raw = PC::RandomOracle::new();
        fs_rng_raw
            .absorb_bytes(&to_bytes![&MarlinVerifierGadget::<G, PC, PCG>::PROTOCOL_NAME].unwrap());

        let fs_rng = {
            let mut fs_rng = PCG::RandomOracleGadget::from_value(cs.ns(|| "init fs gadget"), &fs_rng_raw);
            fs_rng.enforce_absorb_native_field_elements(cs.ns(|| "absorb index vk hash"), &[index_vk_hash])?;
            fs_rng
        };

        let domain_h_size_gadget = FpGadget::<<G::BaseField as Field>::BasePrimeField>::alloc(
            cs.ns(|| "alloc domain_h_size"),
            || Ok(<G::BaseField as Field>::BasePrimeField::from(obj.domain_h_size as u128)),
        )?;

        let domain_k_size_gadget = FpGadget::<<G::BaseField as Field>::BasePrimeField>::alloc(
            cs.ns(|| "alloc domain_k_size"),
            || Ok(<G::BaseField as Field>::BasePrimeField::from(obj.domain_k_size as u128)),
        )?;

        let domain_h = get_best_evaluation_domain::<G::ScalarField>(obj.domain_h_size as usize)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = get_best_evaluation_domain::<G::ScalarField>(obj.domain_k_size as usize)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_h_gen_gadget = NonNativeFieldGadget::alloc(
            cs.ns(|| "alloc domain_h_gen"),
            || Ok(domain_h.group_gen()),
        )?;

        let domain_k_gen_gadget = NonNativeFieldGadget::alloc(
            cs.ns(|| "alloc domain_k_gen"),
            || Ok(domain_k.group_gen()),
        )?;

        Ok(Self {
            domain_h_size: obj.domain_h_size,
            domain_k_size: obj.domain_k_size,
            domain_h_size_gadget,
            domain_k_size_gadget,
            domain_h_gen_gadget,
            domain_k_gen_gadget,
            prepared_index_comms,
            prepared_verifier_key,
            fs_rng,
        })
    }

    fn alloc_input<F, T, CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(mut cs: CS, f: F) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<PreparedIndexVerifierKey<G, PC>>
    {
        let t = f()?;
        let obj = t.borrow();

        let mut prepared_index_comms = Vec::<PCG::PreparedCommitmentGadget>::new();
        for (i, index_comm) in obj.prepared_index_comms.iter().enumerate() {
            prepared_index_comms.push(PCG::PreparedCommitmentGadget::alloc_input(
                cs.ns(|| format!("alloc input index_comm {}", i)),
                || Ok(index_comm),
            )?);
        }

        let prepared_verifier_key = PCG::PreparedVerifierKeyGadget::alloc_input(
            cs.ns(|| "alloc input pvk"),
            || Ok(&obj.prepared_verifier_key),
        )?;

        let mut vk_elems = Vec::<<G::BaseField as Field>::BasePrimeField>::new();
        obj.orig_vk.index_comms.iter().for_each(|index_comm| {
            vk_elems.append(&mut index_comm.to_field_elements().unwrap());
        });

        let index_vk_hash = {
            let mut vk_hash_rng = PC::RandomOracle::new();

            vk_hash_rng.absorb_native_field_elements(&vk_elems);
            FpGadget::<<G::BaseField as Field>::BasePrimeField>::alloc_input(
                cs.ns(|| "alloc input vk_hash"),
                || Ok(vk_hash_rng.squeeze_native_field_elements(1)[0]),
            )
        }?;

        let mut fs_rng_raw = PC::RandomOracle::new();
        fs_rng_raw
            .absorb_bytes(&to_bytes![&MarlinVerifierGadget::<G, PC, PCG>::PROTOCOL_NAME].unwrap());

        let fs_rng = {
            let mut fs_rng = PCG::RandomOracleGadget::from_value(cs.ns(|| "input init fs gadget"), &fs_rng_raw);
            fs_rng.enforce_absorb_native_field_elements(cs.ns(|| "input absorb index vk hash"), &[index_vk_hash])?;
            fs_rng
        };

        let domain_h_size_gadget = FpGadget::<<G::BaseField as Field>::BasePrimeField>::alloc_input(
            cs.ns(|| "alloc input domain_h_size"),
            || Ok(<G::BaseField as Field>::BasePrimeField::from(obj.domain_h_size as u128)),
        )?;

        let domain_k_size_gadget = FpGadget::<<G::BaseField as Field>::BasePrimeField>::alloc_input(
            cs.ns(|| "alloc input domain_k_size"),
            || Ok(<G::BaseField as Field>::BasePrimeField::from(obj.domain_k_size as u128)),
        )?;

        let domain_h = get_best_evaluation_domain::<G::ScalarField>(obj.domain_h_size as usize)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = get_best_evaluation_domain::<G::ScalarField>(obj.domain_k_size as usize)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let domain_h_gen_gadget = NonNativeFieldGadget::alloc(
            cs.ns(|| "alloc input domain_h_gen"),
            || Ok(domain_h.group_gen()),
        )?;

        let domain_k_gen_gadget = NonNativeFieldGadget::alloc(
            cs.ns(|| "alloc input domain_k_gen"),
            || Ok(domain_k.group_gen()),
        )?;

        Ok(Self {
            domain_h_size: obj.domain_h_size,
            domain_k_size: obj.domain_k_size,
            domain_h_size_gadget,
            domain_k_size_gadget,
            domain_h_gen_gadget,
            domain_k_gen_gadget,
            prepared_index_comms,
            prepared_verifier_key,
            fs_rng,
        })
    }
}

pub struct ProofGadget<
    G: AffineCurve,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentGadget<G, PC>,
> {
    pub commitments:     Vec<Vec<PCG::CommitmentGadget>>,
    pub evaluations:     HashMap<String, NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>>,
    pub prover_messages: Vec<ProverMsgGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>>,
    pub pc_batch_proof:  PCG::BatchProofGadget,
}

impl<G, PC, PCG> ProofGadget<G, PC, PCG>
where
    G: AffineCurve,
    PC: PolynomialCommitment<G>,
    PCG: PolynomialCommitmentGadget<G, PC>,
{
    pub fn new(
        commitments:     Vec<Vec<PCG::CommitmentGadget>>,
        evaluations:     HashMap<String, NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>>,
        prover_messages: Vec<ProverMsgGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>>,
        pc_batch_proof:  PCG::BatchProofGadget,
    ) -> Self {
        Self {
            commitments,
            evaluations,
            prover_messages,
            pc_batch_proof,
        }
    }
}

impl<G, PC, PCG> AllocGadget<Proof<G, PC>, <G::BaseField as Field>::BasePrimeField> for ProofGadget<G, PC, PCG>
where
    G:                      AffineCurve,
    PC:                     PolynomialCommitment<G>,
    PCG:                    PolynomialCommitmentGadget<G, PC>,
    PC::VerifierKey:        ToConstraintField<<G::BaseField as Field>::BasePrimeField>,
    PC::Commitment:         ToConstraintField<<G::BaseField as Field>::BasePrimeField>,
    PCG::VerifierKeyGadget: ToConstraintFieldGadget<<G::BaseField as Field>::BasePrimeField>,
    PCG::CommitmentGadget:  ToConstraintFieldGadget<<G::BaseField as Field>::BasePrimeField>,
{
    fn alloc<F, T, CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(mut cs: CS, f: F) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Proof<G, PC>>
    {
        let t = f()?;
        let Proof {
            commitments,
            evaluations,
            prover_messages,
            pc_proof,
            ..
        } = t.borrow();

        let commitment_gadgets: Vec<Vec<PCG::CommitmentGadget>> = commitments
            .iter()
            .enumerate()
            .map(|(i, lst)| {
                lst.iter().enumerate()
                    .map(|(j, comm)| {
                        PCG::CommitmentGadget::alloc(
                            cs.ns(|| format!("alloc commitment {}{}", i, j)),
                            || Ok(comm),
                        ).unwrap()
                    }).collect()
            }).collect();

        let evaluation_gadgets_vec: Vec<NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>> = evaluations
            .iter()
            .enumerate()
            .map(|(i, eval)| {
                NonNativeFieldGadget::alloc(
                    cs.ns(|| format!("alloc evaluation {}", i)),
                    || Ok(eval),
                ).unwrap()
            }).collect();

        let prover_message_gadgets: Vec<ProverMsgGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>> = 
            prover_messages
            .iter()
            .enumerate()
            .map(|(i, msg)| {
                let field_elements: Vec<NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>> = match msg {
                    ProverMsg::EmptyMessage => Vec::new(),
                    ProverMsg::FieldElements(f) => f
                        .iter()
                        .enumerate()
                        .map(|(j, elem)| {
                            NonNativeFieldGadget::alloc(
                                cs.ns(|| format!("alloc prover message {}{}", i, j)),
                                || Ok(elem),
                            ).unwrap()
                        }).collect(),
                };
                ProverMsgGadget { field_elements }
            }).collect();

        let pc_batch_proof = PCG::BatchProofGadget::alloc(
            cs.ns(|| "alloc proof"),
            || Ok(pc_proof.proof.clone()),
        )?;

        let mut evaluation_gadgets = HashMap::<String, NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>>::new();

        const ALL_POLYNOMIALS: [&str; 26] = [
            "a_col", "a_row", "a_row_col", "a_val",
            "b_col", "b_row", "b_row_col", "b_val",
            "c_col", "c_row", "c_row_col", "c_val",
            "h_1", "h_2", "t",
            "vanishing_poly_h_alpha", "vanishing_poly_h_beta",
            "vanishing_poly_k",
            "w", "x",
            "z_1_beta", "z_1_g_beta",
            "z_2_g_gamma", "z_2_gamma",
            "z_a", "z_b",
        ];

        for (s, eval) in ALL_POLYNOMIALS.iter().zip(evaluation_gadgets_vec.iter()) {
            evaluation_gadgets.insert(s.to_string(), (*eval).clone());
        }

        Ok(ProofGadget {
            commitments: commitment_gadgets,
            evaluations: evaluation_gadgets,
            prover_messages: prover_message_gadgets,
            pc_batch_proof,
        })
    }

    fn alloc_input<F, T, CS: ConstraintSystem<<G::BaseField as Field>::BasePrimeField>>(mut cs: CS, f: F) -> Result<Self, SynthesisError>
    where
        F: FnOnce() -> Result<T, SynthesisError>,
        T: Borrow<Proof<G, PC>>
    {
        let t = f()?;
        let Proof {
            commitments,
            evaluations,
            prover_messages,
            pc_proof,
            ..
        } = t.borrow();

        let commitment_gadgets: Vec<Vec<PCG::CommitmentGadget>> = commitments
            .iter()
            .enumerate()
            .map(|(i, lst)| {
                lst.iter().enumerate()
                    .map(|(j, comm)| {
                        PCG::CommitmentGadget::alloc_input(
                            cs.ns(|| format!("alloc input commitment {}{}", i, j)),
                            || Ok(comm),
                        ).unwrap()
                    }).collect()
            }).collect();

        let evaluation_gadgets_vec: Vec<NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>> = evaluations
            .iter()
            .enumerate()
            .map(|(i, eval)| {
                NonNativeFieldGadget::alloc_input(
                    cs.ns(|| format!("alloc input evaluation {}", i)),
                    || Ok(eval),
                ).unwrap()
            }).collect();

        let prover_message_gadgets: Vec<ProverMsgGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>> =
            prover_messages
                .iter()
                .enumerate()
                .map(|(i, msg)| {
                    let field_elements: Vec<NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>> = match msg {
                        ProverMsg::EmptyMessage => Vec::new(),
                        ProverMsg::FieldElements(f) => f
                            .iter()
                            .enumerate()
                            .map(|(j, elem)| {
                                NonNativeFieldGadget::alloc_input(
                                    cs.ns(|| format!("alloc input prover message {}{}", i, j)),
                                    || Ok(elem),
                                ).unwrap()
                            }).collect(),
                    };
                    ProverMsgGadget { field_elements }
                }).collect();

        let pc_batch_proof = PCG::BatchProofGadget::alloc_input(
            cs.ns(|| "alloc input proof"),
            || Ok(pc_proof.proof.clone()),
        )?;

        let mut evaluation_gadgets = HashMap::<String, NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>>::new();

        const ALL_POLYNOMIALS: [&str; 26] = [
            "a_col", "a_row", "a_row_col", "a_val",
            "b_col", "b_row", "b_row_col", "b_val",
            "c_col", "c_row", "c_row_col", "c_val",
            "h_1", "h_2", "t",
            "vanishing_poly_h_alpha", "vanishing_poly_h_beta",
            "vanishing_poly_k",
            "w", "x",
            "z_1_beta", "z_1_g_beta",
            "z_2_g_gamma", "z_2_gamma",
            "z_a", "z_b",
        ];

        for (s, eval) in ALL_POLYNOMIALS.iter().zip(evaluation_gadgets_vec.iter()) {
            evaluation_gadgets.insert(s.to_string(), (*eval).clone());
        }

        Ok(ProofGadget {
            commitments: commitment_gadgets,
            evaluations: evaluation_gadgets,
            prover_messages: prover_message_gadgets,
            pc_batch_proof,
        })
    }
}

impl<G, PC, PCG> Clone for ProofGadget<G, PC, PCG>
    where
        G:                      AffineCurve,
        PC:                     PolynomialCommitment<G>,
        PCG:                    PolynomialCommitmentGadget<G, PC>,
{
    fn clone(&self) -> Self {
        ProofGadget {
            commitments: self.commitments.clone(),
            evaluations: self.evaluations.clone(),
            prover_messages: self.prover_messages.clone(),
            pc_batch_proof: self.pc_batch_proof.clone(),
        }
    }
}

#[repr(transparent)]
pub struct ProverMsgGadget<SimulationF: PrimeField, ConstraintF: PrimeField> {
    pub field_elements: Vec<NonNativeFieldGadget<SimulationF, ConstraintF>>,
}

impl<SimulationF: PrimeField, ConstraintF: PrimeField> Clone
    for ProverMsgGadget<SimulationF, ConstraintF>
{
    fn clone(&self) -> Self {
        ProverMsgGadget {
            field_elements: self.field_elements.clone(),
        }
    }
}

fn compute_lagrange_polynomials_commitments<
    G: AffineCurve,
    PC: PolynomialCommitment<G>
>(ins_len: usize, ck: &PC::CommitterKey) -> Vec<PC::Commitment>
{
    use poly_commit::LabeledPolynomial;

    let domain_x = get_best_evaluation_domain::<G::ScalarField>(ins_len).unwrap();
    let lagrange_polys = domain_x
        .compute_all_lagrange_polynomials()
        .into_iter()
        .enumerate()
        .map(|(i, l_poly)| {
            LabeledPolynomial::new(
                format!("lagrange_poly_{}", i).into(),
                l_poly,
                None,
                None
            )
        }).collect::<Vec<_>>();

    PC::commit(ck, lagrange_polys.iter(), None).unwrap()
        .0
        .into_iter()
        .map(|labeled_comm| { labeled_comm.commitment().clone() }).collect()
}

pub struct PublicInputsGadget<G: AffineCurve, PC: PolynomialCommitment<G>> {
    pub ins:                     Vec<NonNativeFieldGadget<G::ScalarField, <G::BaseField as Field>::BasePrimeField>>,
    pub lagrange_poly_comms:     Vec<PC::Commitment>,
}