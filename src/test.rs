use algebra::Field;
use r1cs_core::{ConstraintSynthesizer, ConstraintSystem, SynthesisError};

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
        let d = cs.alloc_input(
            || "d",
            || {
                let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
                let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

                a.mul_assign(&b);
                a.mul_assign(&b);
                Ok(a)
            },
        )?;

        for i in 0..(self.num_variables - 3) {
            let _ = cs.alloc(
                || format!("var {}", i),
                || self.a.ok_or(SynthesisError::AssignmentMissing),
            )?;
        }

        for i in 0..(self.num_constraints - 1){
            cs.enforce(
                || format!("constraint {}", i),
                |lc| lc + a,
                |lc| lc + b,
                |lc| lc + c,
            );
        }
        cs.enforce(
            || format!("constraint {}", self.num_constraints - 1),
            |lc| lc + c,
            |lc| lc + b,
            |lc| lc + d,
        );
        Ok(())
    }
}

mod marlin {
    use super::*;
    use crate::{
        Marlin,
        MarlinRecursiveConfig,
        MarlinDefaultConfig,
    };

    use algebra::UniformRand;
    use algebra::{
        fields::bn_382::{
            fq::Fq, fr::Fr,
        }, curves::bn_382::g::Affine
    };
    use primitives::crh::poseidon::parameters::BN382FrPoseidonSponge;
    use poly_commit::ipa_pc::InnerProductArgPC;
    use blake2::Blake2s;
    use std::ops::MulAssign;
    use rand::thread_rng;

    type MultiPC = InnerProductArgPC<Fr, Affine, BN382FrPoseidonSponge>;
    type MarlinInstDefault = Marlin<Affine, MultiPC, BN382FrPoseidonSponge, MarlinDefaultConfig>;
    type MarlinInstRecursive = Marlin<Affine, MultiPC, BN382FrPoseidonSponge, MarlinRecursiveConfig>;

    fn test_circuit(num_constraints: usize, num_variables: usize) {
        let rng = &mut thread_rng();

        let universal_srs = MarlinInstDefault::universal_setup::<_, Blake2s>(100, 25, 100, rng).unwrap();

        for _ in 0..50 {
            let a = Fq::rand(rng);
            let b = Fq::rand(rng);
            let mut c = a;
            c.mul_assign(&b);
            let mut d = c;
            d.mul_assign(&b);

            let circ = Circuit {
                a: Some(a),
                b: Some(b),
                num_constraints,
                num_variables,
            };

            let (index_pk, index_vk) = MarlinInstDefault::index(&universal_srs, circ.clone()).unwrap();
            println!("Called index");

            let proof = MarlinInstDefault::prove(&index_pk, circ, rng).unwrap();
            println!("Called prover");

            assert!(MarlinInstDefault::verify(&index_vk, &[c, d], &proof, rng).unwrap());
            println!("Called verifier");
            println!("\nShould not verify (i.e. verifier messages should print below):");
            assert!(!MarlinInstDefault::verify(&index_vk, &[a, a], &proof, rng).unwrap());
        }

        let universal_srs = MarlinInstRecursive::universal_setup::<_, Blake2s>(100, 25, 100, rng).unwrap();

        for _ in 0..50 {
            let a = Fq::rand(rng);
            let b = Fq::rand(rng);
            let mut c = a;
            c.mul_assign(&b);
            let mut d = c;
            d.mul_assign(&b);

            let circ = Circuit {
                a: Some(a),
                b: Some(b),
                num_constraints,
                num_variables,
            };

            let (index_pk, index_vk) = MarlinInstRecursive::index(&universal_srs, circ.clone()).unwrap();
            println!("Called index");

            let proof = MarlinInstRecursive::prove(&index_pk, circ, rng).unwrap();
            println!("Called prover");

            assert!(MarlinInstRecursive::verify(&index_vk, &[c, d], &proof, rng).unwrap());
            println!("Called verifier");
            println!("\nShould not verify (i.e. verifier messages should print below):");
            assert!(!MarlinInstRecursive::verify(&index_vk, &[a, a], &proof, rng).unwrap());
        }
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_big() {
        let num_constraints = 100;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_small() {
        let num_constraints = 26;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_big() {
        let num_constraints = 25;
        let num_variables = 100;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_small() {
        let num_constraints = 25;
        let num_variables = 26;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_square_matrix() {
        let num_constraints = 25;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
    }
}
