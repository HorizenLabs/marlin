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
    use crate::{Marlin, MarlinRecursiveConfig, MarlinRecursiveConfigNoZk, MarlinDefaultConfig, MarlinDefaultConfigNoZk, MarlinConfig};

    use algebra::{UniformRand, AffineCurve};
    use algebra::{
        fields::tweedle::fr::Fr,
        curves::tweedle::dum::Affine
    };
    use primitives::crh::poseidon::parameters::tweedle::TweedleFrPoseidonSponge;
    use poly_commit::ipa_pc::InnerProductArgPC;
    use blake2::Blake2s;
    use std::ops::MulAssign;
    use rand::thread_rng;
    use poly_commit::PolynomialCommitment;
    use poly_commit::fiat_shamir::FiatShamirRng;
    use r1cs_core::ToConstraintField;

    type MultiPC = InnerProductArgPC<Fr, Affine, TweedleFrPoseidonSponge>;

    fn test_circuit<
        G: AffineCurve,
        PC: PolynomialCommitment<G, RandomOracle = FS>,
        FS: FiatShamirRng<G::ScalarField, <G::BaseField as Field>::BasePrimeField>,
        MC: MarlinConfig,
    >(
        num_samples: usize,
        num_constraints: usize,
        num_variables: usize,
    )
    where
        PC::VerifierKey: ToConstraintField<<G::BaseField as Field>::BasePrimeField>,
        PC::Commitment: ToConstraintField<<G::BaseField as Field>::BasePrimeField>,
    {
        let rng = &mut thread_rng();

        let universal_srs = Marlin::<G, PC, FS, MC>::universal_setup::<_, Blake2s>(100, 25, 100, rng).unwrap();

        for _ in 0..num_samples {
            let a = G::ScalarField::rand(rng);
            let b = G::ScalarField::rand(rng);
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

            let (index_pk, index_vk) = Marlin::<G, PC, FS, MC>::index(&universal_srs, circ.clone()).unwrap();
            println!("Called index");

            let proof = Marlin::<G, PC, FS, MC>::prove(&index_pk, circ,  &mut if MC::ZK { Some(thread_rng()) } else { None }).unwrap();
            println!("Called prover");

            assert!(Marlin::<G, PC, FS, MC>::verify(&index_vk, &[c, d], &proof, rng).unwrap());
            println!("Called verifier");
            println!("\nShould not verify (i.e. verifier messages should print below):");
            assert!(!Marlin::<G, PC, FS, MC>::verify(&index_vk, &[a, a], &proof, rng).unwrap());
        }
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_big() {
        let num_constraints = 100;
        let num_variables = 25;

        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinDefaultConfig>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinRecursiveConfig>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinDefaultConfigNoZk>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinRecursiveConfigNoZk>(25, num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_small() {
        let num_constraints = 26;
        let num_variables = 25;

        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinDefaultConfig>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinRecursiveConfig>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinDefaultConfigNoZk>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinRecursiveConfigNoZk>(25, num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_big() {
        let num_constraints = 25;
        let num_variables = 100;

        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinDefaultConfig>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinRecursiveConfig>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinDefaultConfigNoZk>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinRecursiveConfigNoZk>(25, num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_small() {
        let num_constraints = 25;
        let num_variables = 26;

        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinDefaultConfig>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinRecursiveConfig>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinDefaultConfigNoZk>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinRecursiveConfigNoZk>(25, num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_square_matrix() {
        let num_constraints = 25;
        let num_variables = 25;

        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinDefaultConfig>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinRecursiveConfig>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinDefaultConfigNoZk>(25, num_constraints, num_variables);
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinRecursiveConfigNoZk>(25, num_constraints, num_variables);
    }

    //TODO: Fix this test
    #[test]
    // See https://github.com/HorizenLabs/marlin/issues/3 for the rationale behind this test
    fn prove_and_verify_with_trivial_index_polynomials() {
        let num_constraints = 1 << 6;
        let num_variables = 1 << 4;

        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinDefaultConfig>(25, num_constraints, num_variables);
        println!("Passed 1");
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinRecursiveConfig>(25, num_constraints, num_variables);
        println!("Passed 2");
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinDefaultConfigNoZk>(25, num_constraints, num_variables);
        println!("Passed 3");
        test_circuit::<Affine, MultiPC, TweedleFrPoseidonSponge, MarlinRecursiveConfigNoZk>(25, num_constraints, num_variables);
        println!("Passed 4");
    }
}
