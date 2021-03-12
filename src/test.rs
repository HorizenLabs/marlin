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
    use crate::Marlin;

    use algebra::{
        fields::tweedle::fq::Fq,
        curves::tweedle::dum::Affine,
        PrimeField,
    };
    use poly_commit::ipa_pc::InnerProductArgPC;
    use blake2::Blake2s;
    use rand::thread_rng;
    use poly_commit::PolynomialCommitment;
    use digest::Digest;

    type MultiPC = InnerProductArgPC<Affine, Blake2s>;

    fn test_circuit<
        F:  PrimeField,
        PC: PolynomialCommitment<F>,
        D:  Digest,
    >(
        num_samples: usize,
        num_constraints: usize,
        num_variables: usize,
        zk: bool,
    )
    {
        let rng = &mut thread_rng();

        let universal_srs = Marlin::<F, PC, D>::universal_setup(100, 25, 100, zk, rng).unwrap();

        for _ in 0..num_samples {
            let a = F::rand(rng);
            let b = F::rand(rng);
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

            let (index_pk, pc_pk, index_vk, pc_vk) = Marlin::<F, PC, D>::index(&universal_srs, circ.clone(), zk).unwrap();
            println!("Called index");

            let proof = Marlin::<F, PC, D>::prove(
                &index_pk,
                &pc_pk,
                circ,
                zk,
                &mut if zk { Some(thread_rng()) } else { None }
            ).unwrap();
            println!("Called prover");

            assert!(Marlin::<F, PC, D>::verify(&index_vk, &pc_vk,&[c, d], &proof, rng).unwrap());
            println!("Called verifier");
            println!("\nShould not verify (i.e. verifier messages should print below):");
            assert!(!Marlin::<F, PC, D>::verify(&index_vk, &pc_vk, &[a, a], &proof, rng).unwrap());
        }
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_big() {
        let num_constraints = 100;
        let num_variables = 25;

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_small() {
        let num_constraints = 26;
        let num_variables = 25;

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_big() {
        let num_constraints = 25;
        let num_variables = 100;

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_small() {
        let num_constraints = 25;
        let num_variables = 26;

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    fn prove_and_verify_with_square_matrix() {
        let num_constraints = 25;
        let num_variables = 25;

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, false);
        println!("Marlin No ZK passed");

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }

    #[test]
    // See https://github.com/HorizenLabs/marlin/issues/3 for the rationale behind this test
    fn prove_and_verify_with_trivial_index_polynomials() {
        let num_constraints = 1 << 6;
        let num_variables = 1 << 4;

        //TODO: Fix non passing tests
        //test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables);
        //println!("Marlin No LC, No ZK passed");

        test_circuit::<Fq, MultiPC, Blake2s>(25, num_constraints, num_variables, true);
        println!("Marlin ZK passed");
    }
}