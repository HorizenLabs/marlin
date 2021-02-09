#[cfg(test)]
mod tests {
    use algebra::{fields::tweedle::{
        fq::Fq, fr::Fr,
    }, curves::tweedle::dum::{
        Affine, TweedledumParameters as AffineParameters
    }, Field, UniformRand};
    use primitives::crh::poseidon::parameters::TweedleFrPoseidonSponge;
    use poly_commit::ipa_pc::InnerProductArgPC;
    use poly_commit::ipa_pc::constraints::InnerProductArgPCGadget;
    use r1cs_std::{
        fields::{
            fp::FpGadget,
            nonnative::nonnative_field_gadget::NonNativeFieldGadget,
        },
        groups::curves::short_weierstrass::short_weierstrass_jacobian::AffineGadget as GroupGadget,
        test_constraint_system::TestConstraintSystem,
        prelude::*,
    };
    use r1cs_crypto::crh::poseidon::tweedle::TweedleFrPoseidonSpongeGadget;
    use r1cs_core::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};
    use crate::{
        Marlin, MarlinRecursiveConfig,
        constraints::{
            data_structures::{
                IndexVerifierKeyGadget, ProofGadget,
                compute_lagrange_polynomials_commitments, PublicInputsGadget
            },
            verifier::MarlinVerifierGadget
        }
    };
    use rand::thread_rng;
    use std::ops::MulAssign;
    use blake2::Blake2s;

    type AffineGadget = GroupGadget<AffineParameters, Fr, FpGadget<Fr>>;
    type IPAPC = InnerProductArgPC<Fr, Affine, TweedleFrPoseidonSponge>;
    type IPAPCGadget = InnerProductArgPCGadget<Fq, Fr, Affine, AffineGadget, TweedleFrPoseidonSpongeGadget>;
    type MarlinInst = Marlin<Affine, IPAPC, TweedleFrPoseidonSponge, MarlinRecursiveConfig>;

    #[derive(Copy, Clone)]
    struct Circuit<F: Field> {
        a: Option<F>,
        b: Option<F>,
        num_constraints: usize,
        num_variables: usize,
    }

    impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Circuit<ConstraintF> {
        fn generate_constraints<CS: ConstraintSystem<ConstraintF>>(
            self,
            cs: &mut CS,
        ) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| "a", || self.a.ok_or(SynthesisError::AssignmentMissing))?;
            let b = cs.alloc(|| "b", || self.b.ok_or(SynthesisError::AssignmentMissing))?;
            let c = cs.alloc_input(
                || "c",
                || {
                    let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                    let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                    a.mul_assign(&b);
                    Ok(a)
                },
            )?;
            //TODO: Test with inputs not being powers of 2
            /*let d = cs.alloc_input(
                || "d",
                || {
                    let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                    let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                    a.mul_assign(&b);
                    a.mul_assign(&b);
                    Ok(a)
                },
            )?;*/

            for i in 0..(self.num_variables - 3) {
                let _ = cs.alloc(
                    || format!("var {}", i),
                    || self.a.ok_or(SynthesisError::AssignmentMissing),
                )?;
            }

            for i in 0..self.num_constraints{
                cs.enforce(
                    || format!("constraint {}", i),
                    |lc| lc + a,
                    |lc| lc + b,
                    |lc| lc + c,
                );
            }
            //TODO: Test with inputs not being powers of 2
            /*cs.enforce(
                || format!("constraint {}", self.num_constraints - 1),
                |lc| lc + c,
                |lc| lc + b,
                |lc| lc + d,
            );*/
            Ok(())
        }
    }

    #[test]
    fn verifier_test() {
        let rng = &mut thread_rng();

        let universal_srs = MarlinInst::universal_setup::<_, Blake2s>(100, 25, 100, rng).unwrap();

        let num_constraints = 100;
        let num_variables = 25;

        for _ in 0..10 {
            let a = Fq::rand(rng);
            let b = Fq::rand(rng);
            let mut c = a;
            c.mul_assign(&b);

            let circ = Circuit {
                a: Some(a),
                b: Some(b),
                num_constraints,
                num_variables,
            };

            let (index_pk, index_vk) = MarlinInst::index(&universal_srs, circ).unwrap();
            println!("Called index");

            let proof = MarlinInst::prove(&index_pk, circ, rng).unwrap();
            println!("Called prover");

            assert!(MarlinInst::verify(&index_vk, &[c], &proof, rng).unwrap());
            println!("Called verifier");

            // Native works; now convert to the constraint world!

            let mut cs = TestConstraintSystem::<Fr>::new();

            // BEGIN: ivk to ivk_gadget
            let ivk_gadget: IndexVerifierKeyGadget<Affine, IPAPC, IPAPCGadget> =
                IndexVerifierKeyGadget::alloc(cs.ns(|| "alloc index vk"), || Ok(index_vk)).unwrap();
            // END: ivk to ivk_gadget

            // BEGIN: public input to public_input_gadget
            let public_input: Vec<Fq> = vec![c];

            let ins: Vec<NonNativeFieldGadget<Fq, Fr>> = public_input
                .iter()
                .enumerate()
                .map(|(i, x)| {
                    NonNativeFieldGadget::alloc_input(
                        cs.ns(|| format!("alloc public input {}", i)),
                        || Ok(x)
                    ).unwrap()
                })
                .collect();

            // Collect Lagrange Polynomials commitments
            let lagrange_poly_comms = compute_lagrange_polynomials_commitments::<Affine, IPAPC>(
                (public_input.len() + 1).next_power_of_two(),
                &index_pk.committer_key
            );

            // Construct public input gadget
            let public_input_gadget = PublicInputsGadget::<Affine, IPAPC> {
                ins,
                lagrange_poly_comms
            };
            // END: public input to public_input_gadget

            // BEGIN: proof to proof_gadget
            let proof_gadget: ProofGadget<Affine, IPAPC, IPAPCGadget> = ProofGadget::alloc(
                cs.ns(|| "alloc proof"),
                || Ok(proof)
            ).unwrap();
            // END: proof to proof_gadget

            MarlinVerifierGadget::<Affine, IPAPC, IPAPCGadget>::verify(
                cs.ns(|| "verify proof"),
                &ivk_gadget,
                public_input_gadget,
                &proof_gadget
            ).unwrap().enforce_equal(
                cs.ns(|| "final check"),
                &Boolean::Constant(true)
            ).unwrap();

            println!(
                "after Marlin, num_of_constraints = {}",
                cs.num_constraints()
            );

            assert!(
                cs.is_satisfied(),
                "Constraints not satisfied: {:?}",
                cs.which_is_unsatisfied()
            );
        }
    }
}
