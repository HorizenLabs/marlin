use algebra::{
    fields::bn_382::{Fq, Fr},
    curves::bn_382::g::Affine,
    UniformRand, PrimeField
};
use marlin::*;
use blake2::Blake2s;
use poly_commit::ipa_pc::InnerProductArgPC;

use r1cs_core::{SynthesisError, ConstraintSynthesizer, ConstraintSystem};

use criterion::{BenchmarkId, BatchSize};
use criterion::Criterion;
use r1cs_std::Assignment;
use r1cs_std::fields::fp::FpGadget;
use r1cs_std::eq::EqGadget;
use r1cs_std::fields::FieldGadget;
use r1cs_std::alloc::AllocGadget;

use primitives::crh::poseidon::BN382FrPoseidonSponge;

use rand::{
    rngs::OsRng, thread_rng
};

use std::time::{SystemTime, UNIX_EPOCH};

#[macro_use]
extern crate criterion;

#[macro_use]
extern crate bench_utils;

type IPAPC = InnerProductArgPC<Fr, Affine, BN382FrPoseidonSponge>;
type MarlinInst = Marlin<Affine, IPAPC, BN382FrPoseidonSponge, MarlinDefaultConfig>;

#[derive(Clone)]
pub struct TestCircuit1a<F: PrimeField> {
    num_constraints: usize,
    a: Option<F>,
    b: Option<F>,
}

#[derive(Clone)]
pub struct TestCircuit1b<F: PrimeField> {
    num_constraints: usize,
    a: Option<F>,
    b: Option<F>,
}

#[derive(Clone)]
pub struct TestCircuit1c<F: PrimeField> {
    num_constraints: usize,
    a: Option<F>,
    b: Option<F>,
}

#[derive(Clone)]
pub struct TestCircuit2a<F: PrimeField> {
    num_constraints: usize,
    a: Option<F>,
    b: Option<F>,
}

#[derive(Clone)]
pub struct TestCircuit2b<F: PrimeField> {
    num_constraints: usize,
    a: Option<F>,
    b: Option<F>,
}

#[derive(Clone)]
pub struct TestCircuit2c<F: PrimeField> {
    num_constraints: usize,
    a: Option<F>,
    b: Option<F>,
}


impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit1a<F> {
    fn generate_constraints<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {

        let mut a_k_minus_1 = FpGadget::<F>::alloc_input(
            cs.ns(|| "alloc a"),
            || self.a.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let mut b_k_minus_1 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc b"),
            || self.b.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let zero = FpGadget::<F>::zero(cs.ns(|| "alloc zero"))?;

        a_k_minus_1.enforce_not_equal(cs.ns(|| "a_0 != 0"), &zero)?;
        b_k_minus_1.enforce_not_equal(cs.ns(|| "b_0 != 0"), &zero)?;

        for k in 0..(self.num_constraints - 5)/2 {

            let a_k = FpGadget::<F>::alloc(
                cs.ns(|| format!("alloc a_{}", k)),
                || Ok(a_k_minus_1.value.get()? * &b_k_minus_1.value.get()?)
            )?;

            let b_k = FpGadget::<F>::alloc(
                cs.ns(|| format!("alloc b_{}", k)),
                || Ok(b_k_minus_1.value.get()? * &a_k_minus_1.value.get()?)
            )?;

            a_k_minus_1.mul_equals(
                cs.ns(|| format!("a_{} * b_{} = a_{}", k - 1, k - 1, k)),
                &b_k_minus_1,
                &a_k
            )?;

            b_k_minus_1.mul_equals(
                cs.ns(|| format!("b_{} * a_{} = b_{}", k - 1, k - 1, k)),
                &a_k_minus_1,
                &b_k
            )?;

            a_k_minus_1 = a_k;
            b_k_minus_1 = b_k;
        }

        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit1b<F> {
    fn generate_constraints<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let mut a_k_minus_2 = FpGadget::<F>::alloc_input(
            cs.ns(|| "alloc a0"),
            || self.a.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let mut b_k_minus_2 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc b0"),
            || self.b.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let zero = FpGadget::<F>::zero(cs.ns(|| "alloc zero"))?;

        a_k_minus_2.enforce_not_equal(cs.ns(|| "a_0 != 0"), &zero)?;
        b_k_minus_2.enforce_not_equal(cs.ns(|| "b_0 != 0"), &zero)?;

        let mut a_k_minus_1 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc a1"),
            || Ok(F::rand(&mut thread_rng()))
        )?;

        let mut b_k_minus_1 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc b1"),
            || Ok(F::rand(&mut thread_rng()))
        )?;

        for k in 2..(self.num_constraints - 5) / 2 {
            let a_k = FpGadget::<F>::alloc(
                cs.ns(|| format!("alloc a_{}", k)),
                || {
                    let term_1 = a_k_minus_1.value.get()? + &a_k_minus_2.value.get()?;
                    let term_2 = b_k_minus_1.value.get()?;
                    Ok(term_1 * &term_2)
                }
            )?;

            let b_k = FpGadget::<F>::alloc(
                cs.ns(|| format!("alloc b_{}", k)),
                || {
                    let term_1 = a_k_minus_1.value.get()? + &a_k_minus_1.value.get()?;
                    let term_2 = b_k_minus_1.value.get()?;
                    Ok(term_1 * &term_2)
                }
            )?;

            a_k_minus_1.add(cs.ns(|| format!("a_{} + a_{}", k - 1, k - 2)), &a_k_minus_2)?
                .mul_equals(
                    cs.ns(|| format!("(a_{} + a_{}) * b_{} = a_{}", k - 1, k - 2, k - 1, k)),
                    &b_k_minus_1,
                    &a_k
                )?;

            a_k_minus_1.double(cs.ns(|| format!("a_{} + a_{}", k - 1, k - 1)))?
                .mul_equals(
                    cs.ns(|| format!("(a_{} + a_{}) * b_{} = b_{}", k - 1, k - 1, k - 1, k)),
                    &b_k_minus_1,
                    &b_k
                )?;

            a_k_minus_2 = a_k_minus_1;
            b_k_minus_2 = b_k_minus_1;
            a_k_minus_1 = a_k;
            b_k_minus_1 = b_k;
        }
        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit1c<F> {
    fn generate_constraints<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {
        let mut a_k_minus_2 = FpGadget::<F>::alloc_input(
            cs.ns(|| "alloc a0"),
            || self.a.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let mut b_k_minus_2 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc b0"),
            || self.b.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let zero = FpGadget::<F>::zero(cs.ns(|| "alloc zero"))?;

        a_k_minus_2.enforce_not_equal(cs.ns(|| "a_0 != 0"), &zero)?;
        b_k_minus_2.enforce_not_equal(cs.ns(|| "b_0 != 0"), &zero)?;

        let mut a_k_minus_1 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc a1"),
            || Ok(F::rand(&mut thread_rng()))
        )?;

        let mut b_k_minus_1 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc b1"),
            || Ok(F::rand(&mut thread_rng()))
        )?;

        for k in 2..(self.num_constraints - 5) / 2 {
            let a_k = FpGadget::<F>::alloc(
                cs.ns(|| format!("alloc a_{}", k)),
                || {
                    let term_1 = a_k_minus_1.value.get()? + &a_k_minus_2.value.get()?;
                    let term_2 = b_k_minus_1.value.get()? + &b_k_minus_2.value.get()?;
                    Ok(term_1 * &term_2)
                }
            )?;

            let b_k = FpGadget::<F>::alloc(
                cs.ns(|| format!("alloc b_{}", k)),
                || {
                    let term_1 = a_k_minus_1.value.get()? + &a_k_minus_1.value.get()?;
                    let term_2 = b_k_minus_1.value.get()? + &b_k_minus_2.value.get()?;
                    Ok(term_1 * &term_2)
                }
            )?;

            let a_k_minus_1_plus_a_k_minus_2 = a_k_minus_1.add(
                cs.ns(|| format!("a_{} + a_{}", k - 1, k - 2)),
                &a_k_minus_2
            )?;

            let b_k_minus_1_plus_b_k_minus_2 = b_k_minus_1.add(
                cs.ns(|| format!("b_{} + b_{}", k - 1, k - 2)),
                &b_k_minus_2
            )?;

            a_k_minus_1_plus_a_k_minus_2.mul_equals(
                cs.ns(|| format!("(a_{} + a_{}) * (b_{} + b_{}) = a_{}", k - 1, k - 2, k - 1, k - 2, k)),
                &b_k_minus_1_plus_b_k_minus_2,
                &a_k
            )?;

            a_k_minus_1.double(cs.ns(|| format!("a_{} + a_{}", k - 1, k - 1)))?
                .mul_equals(
                    cs.ns(|| format!("(a_{} + a_{}) * (b_{} + b_{}) = b_{}", k - 1, k - 1, k - 1, k - 2, k)),
                    &b_k_minus_1_plus_b_k_minus_2,
                    &b_k
                )?;

            a_k_minus_2 = a_k_minus_1;
            b_k_minus_2 = b_k_minus_1;
            a_k_minus_1 = a_k;
            b_k_minus_1 = b_k;
        }
        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit2a<F> {
    fn generate_constraints<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {

        let mut a_k_minus_1 = FpGadget::<F>::alloc_input(
            cs.ns(|| "alloc a"),
            || self.a.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let mut b_k_minus_1 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc b"),
            || self.b.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let zero = FpGadget::<F>::zero(cs.ns(|| "alloc zero"))?;

        a_k_minus_1.enforce_not_equal(cs.ns(|| "a_0 != 0"), &zero)?;
        b_k_minus_1.enforce_not_equal(cs.ns(|| "b_0 != 0"), &zero)?;

        for k in 0..(self.num_constraints - 5)/2 {

            let a_k = FpGadget::<F>::alloc(
                cs.ns(|| format!("alloc a_{}", k)),
                || Ok(a_k_minus_1.value.get()? * &b_k_minus_1.value.get()?.inverse().get()?)
            )?;

            let b_k = FpGadget::<F>::alloc(
                cs.ns(|| format!("alloc b_{}", k)),
                || Ok(b_k_minus_1.value.get()? * &a_k_minus_1.value.get()?)
            )?;

            a_k.mul_equals(
                cs.ns(|| format!("a_{} * b_{} = a_{}", k, k - 1, k - 1)),
                &b_k_minus_1,
                &a_k_minus_1
            )?;

            b_k_minus_1.mul_equals(
                cs.ns(|| format!("b_{} * a_{} = b_{}", k - 1, k - 1, k)),
                &a_k_minus_1,
                &b_k
            )?;

            a_k_minus_1 = a_k;
            b_k_minus_1 = b_k;
        }

        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit2b<F> {
    fn generate_constraints<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {

        let mut a_k_minus_2 = FpGadget::<F>::alloc_input(
            cs.ns(|| "alloc a0"),
            || self.a.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let mut b_k_minus_2 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc b0"),
            || self.b.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let zero = FpGadget::<F>::zero(cs.ns(|| "alloc zero"))?;

        a_k_minus_2.enforce_not_equal(cs.ns(|| "a_0 != 0"), &zero)?;
        b_k_minus_2.enforce_not_equal(cs.ns(|| "b_0 != 0"), &zero)?;

        let mut a_k_minus_1 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc a1"),
            || Ok(F::rand(&mut thread_rng()))
        )?;

        let mut b_k_minus_1 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc b1"),
            || Ok(F::rand(&mut thread_rng()))
        )?;

        for k in 2..(self.num_constraints - 5)/2 {

            let a_k = FpGadget::<F>::alloc(
                cs.ns(|| format!("alloc a_{}", k)),
                || {
                    let term_1 = a_k_minus_1.value.get()? + &a_k_minus_2.value.get()?;
                    let term_2 = b_k_minus_1.value.get()? + &b_k_minus_2.value.get()?;
                    Ok(term_1 * &(term_2.inverse().get()?))
                }
            )?;

            let b_k = FpGadget::<F>::alloc(
                cs.ns(|| format!("alloc b_{}", k)),
                || {
                    let term_1 = a_k_minus_1.value.get()?;
                    let term_2 = b_k_minus_1.value.get()? + &b_k_minus_1.value.get()?;
                    Ok(term_1 * &term_2)
                }
            )?;

            let a_k_minus_1_plus_a_k_minus_2 = a_k_minus_1.add(
                cs.ns(|| format!("a_{} + a_{}", k - 1, k - 2)),
                &a_k_minus_2
            )?;

            let b_k_minus_1_plus_b_k_minus_2 = b_k_minus_1.add(
                cs.ns(|| format!("b_{} + b_{}", k - 1, k - 2)),
                &b_k_minus_2
            )?;

            let b_k_minus_1_plus_b_k_minus_1 = b_k_minus_1.double(
                cs.ns(|| format!("b_{} + b_{}", k - 1, k - 1)),
            )?;

            a_k.mul_equals(
                cs.ns(|| format!("a_{} * (b_{} + b_{}) = (a_{} + a_{})", k, k - 1, k - 2, k - 1, k - 2)),
                &b_k_minus_1_plus_b_k_minus_2,
                &a_k_minus_1_plus_a_k_minus_2
            )?;

            a_k_minus_1.mul_equals(
                cs.ns(|| format!("a_{} * (b_{} + b_{}) = b_{}", k - 1, k - 1, k - 1, k)),
                &b_k_minus_1_plus_b_k_minus_1,
                &b_k
            )?;

            a_k_minus_2 = a_k_minus_1;
            b_k_minus_2 = b_k_minus_1;
            a_k_minus_1 = a_k;
            b_k_minus_1 = b_k;
        }

        Ok(())
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TestCircuit2c<F> {
    fn generate_constraints<CS: ConstraintSystem<F>>(
        self,
        cs: &mut CS,
    ) -> Result<(), SynthesisError> {

        let mut a_k_minus_2 = FpGadget::<F>::alloc_input(
            cs.ns(|| "alloc a0"),
            || self.a.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let mut b_k_minus_2 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc b0"),
            || self.b.ok_or(SynthesisError::AssignmentMissing)
        )?;

        let zero = FpGadget::<F>::zero(cs.ns(|| "alloc zero"))?;

        a_k_minus_2.enforce_not_equal(cs.ns(|| "a_0 != 0"), &zero)?;
        b_k_minus_2.enforce_not_equal(cs.ns(|| "b_0 != 0"), &zero)?;

        let mut a_k_minus_1 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc a1"),
            || Ok(F::rand(&mut thread_rng()))
        )?;

        let mut b_k_minus_1 = FpGadget::<F>::alloc(
            cs.ns(|| "alloc b1"),
            || Ok(F::rand(&mut thread_rng()))
        )?;

        for k in 2..(self.num_constraints - 5)/2 {

            let a_k = FpGadget::<F>::alloc(
                cs.ns(|| format!("alloc a_{}", k)),
                || {
                    let term_1 = a_k_minus_1.value.get()? + &a_k_minus_2.value.get()?;
                    let term_2 = b_k_minus_1.value.get()? + &b_k_minus_2.value.get()?;
                    Ok(term_1 * &(term_2.inverse().get()?))
                }
            )?;

            let b_k = FpGadget::<F>::alloc(
                cs.ns(|| format!("alloc b_{}", k)),
                || {
                    let term_1 = a_k_minus_1.value.get()? + &a_k_minus_1.value.get()?;
                    let term_2 = b_k_minus_1.value.get()? + &b_k_minus_1.value.get()?;
                    Ok(term_1 * &term_2)
                }
            )?;

            let a_k_minus_1_plus_a_k_minus_2 = a_k_minus_1.add(
                cs.ns(|| format!("a_{} + a_{}", k - 1, k - 2)),
                &a_k_minus_2
            )?;

            let b_k_minus_1_plus_b_k_minus_2 = b_k_minus_1.add(
                cs.ns(|| format!("b_{} + b_{}", k - 1, k - 2)),
                &b_k_minus_2
            )?;

            let a_k_minus_1_plus_a_k_minus_1 = a_k_minus_1.double(
                cs.ns(|| format!("a_{} + a_{}", k - 1, k - 1)),
            )?;

            let b_k_minus_1_plus_b_k_minus_1 = b_k_minus_1.double(
                cs.ns(|| format!("b_{} + b_{}", k - 1, k - 1)),
            )?;

            a_k.mul_equals(
                cs.ns(|| format!("a_{} * (b_{} + b_{}) = (a_{} + a_{})", k, k - 1, k - 2, k - 1, k - 2)),
                &b_k_minus_1_plus_b_k_minus_2,
                &a_k_minus_1_plus_a_k_minus_2
            )?;

            a_k_minus_1_plus_a_k_minus_1.mul_equals(
                cs.ns(|| format!("(a_{} + a_{}) * (b_{} + b_{}) = b_{}", k - 1, k - 1, k - 1, k - 1, k)),
                &b_k_minus_1_plus_b_k_minus_1,
                &b_k
            )?;

            a_k_minus_2 = a_k_minus_1;
            b_k_minus_2 = b_k_minus_1;
            a_k_minus_1 = a_k;
            b_k_minus_1 = b_k;
        }

        Ok(())
    }
}

fn bench_prover_circuit1a(c: &mut Criterion){

    let mut rng = thread_rng();

    let mut group = c.benchmark_group("marlin-bn382-test circuit 1a-variable constraints-segment_size=num_constraints");

    let num_constraints = (14..=22).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &num_constraints in num_constraints.iter()
        {
            let universal_srs = MarlinInst::universal_setup::<_, Blake2s>(num_constraints, num_constraints, num_constraints, &mut rng).unwrap();
            let c = TestCircuit1a::<Fq>{ num_constraints, a: None, b: None };

            let (index_pk, _) = MarlinInst::index(
                &universal_srs,
                c.clone(),
            ).unwrap();

            add_to_trace!(
             || format!("****************{}*******************", num_constraints),
             || format!("--->START TIMESTAMP: {:?}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs())
             );

            group.bench_with_input(BenchmarkId::from_parameter(num_constraints), &num_constraints, |bn, _constraints| {
                bn.iter_batched(
                    || {
                        let mut rng = OsRng::default();
                        let a = Fq::rand(&mut rng);
                        let b = Fq::rand(&mut rng);
                        (a, b)
                    },
                    |(a, b)| {
                        let c = TestCircuit1a{ num_constraints, a: Some(a), b: Some(b) };

                        MarlinInst::prove(
                            &index_pk,
                            c,
                            &mut rng,
                        ).unwrap();
                    },
                    BatchSize::PerIteration
                );
            });
            add_to_trace!(
             || format!("****************{}*******************", num_constraints),
             || format!("--->END TIMESTAMP: {:?}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs())
             );        }
    group.finish();
}

fn bench_prover_circuit1b(c: &mut Criterion){

    let mut rng = thread_rng();

    let mut group = c.benchmark_group("marlin-bn382-test circuit 1b-variable constraints-segment_size=num_constraints");

    let num_constraints = (14..=22).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &num_constraints in num_constraints.iter()
        {
            let universal_srs = MarlinInst::universal_setup::<_, Blake2s>(num_constraints, num_constraints, num_constraints, &mut rng).unwrap();
            let c = TestCircuit1b::<Fq>{ num_constraints, a: None, b: None };

            let (index_pk, _) = MarlinInst::index(
                &universal_srs,
                c.clone(),
            ).unwrap();

            add_to_trace!(
             || format!("****************{}*******************", num_constraints),
             || format!("--->START TIMESTAMP: {:?}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs())
             );

            group.bench_with_input(BenchmarkId::from_parameter(num_constraints), &num_constraints, |bn, _constraints| {
                bn.iter_batched(
                    || {
                        let mut rng = OsRng::default();
                        let a = Fq::rand(&mut rng);
                        let b = Fq::rand(&mut rng);
                        (a, b)
                    },
                    |(a, b)| {
                        let c = TestCircuit1b{ num_constraints, a: Some(a), b: Some(b) };

                        MarlinInst::prove(
                            &index_pk,
                            c,
                            &mut rng,
                        ).unwrap();
                    },
                    BatchSize::PerIteration
                );
            });
            add_to_trace!(
             || format!("****************{}*******************", num_constraints),
             || format!("--->END TIMESTAMP: {:?}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs())
             );        }
    group.finish();
}

fn bench_prover_circuit1c(c: &mut Criterion){


    let mut rng = thread_rng();

    let mut group = c.benchmark_group("marlin-bn382-test circuit 1c-variable constraints-segment_size=num_constraints");

    let num_constraints = (14..=22).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &num_constraints in num_constraints.iter()
        {
            let universal_srs = MarlinInst::universal_setup::<_, Blake2s>(num_constraints, num_constraints, num_constraints, &mut rng).unwrap();
            let c = TestCircuit1c::<Fq>{ num_constraints, a: None, b: None };

            let (index_pk, _) = MarlinInst::index(
                &universal_srs,
                c.clone(),
            ).unwrap();

            add_to_trace!(
             || format!("****************{}*******************", num_constraints),
             || format!("--->START TIMESTAMP: {:?}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs())
             );

            group.bench_with_input(BenchmarkId::from_parameter(num_constraints), &num_constraints, |bn, _constraints| {
                bn.iter_batched(
                    || {
                        let mut rng = OsRng::default();
                        let a = Fq::rand(&mut rng);
                        let b = Fq::rand(&mut rng);
                        (a, b)
                    },
                    |(a, b)| {
                        let c = TestCircuit1c{ num_constraints, a: Some(a), b: Some(b) };

                        MarlinInst::prove(
                            &index_pk,
                            c,
                            &mut rng,
                        ).unwrap();
                    },
                    BatchSize::PerIteration
                );
            });
            add_to_trace!(
             || format!("****************{}*******************", num_constraints),
             || format!("--->END TIMESTAMP: {:?}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs())
             );        }
    group.finish();
}

fn bench_prover_circuit2a(c: &mut Criterion){


    let mut rng = thread_rng();

    let mut group = c.benchmark_group("marlin-bn382-test circuit 2a-variable constraints-segment_size=num_constraints");

    let num_constraints = (14..=22).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &num_constraints in num_constraints.iter()
        {
            let universal_srs = MarlinInst::universal_setup::<_, Blake2s>(num_constraints, num_constraints, num_constraints, &mut rng).unwrap();
            let c = TestCircuit2a::<Fq>{ num_constraints, a: None, b: None };

            let (index_pk, _) = MarlinInst::index(
                &universal_srs,
                c.clone(),
            ).unwrap();

            add_to_trace!(
             || format!("****************{}*******************", num_constraints),
             || format!("--->START TIMESTAMP: {:?}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs())
             );

            group.bench_with_input(BenchmarkId::from_parameter(num_constraints), &num_constraints, |bn, _constraints| {
                bn.iter_batched(
                    || {
                        let mut rng = OsRng::default();
                        let a = Fq::rand(&mut rng);
                        let b = Fq::rand(&mut rng);
                        (a, b)
                    },
                    |(a, b)| {
                        let c = TestCircuit2a{ num_constraints, a: Some(a), b: Some(b) };

                        MarlinInst::prove(
                            &index_pk,
                            c,
                            &mut rng,
                        ).unwrap();
                    },
                    BatchSize::PerIteration
                );
            });
            add_to_trace!(
             || format!("****************{}*******************", num_constraints),
             || format!("--->END TIMESTAMP: {:?}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs())
             );        }
    group.finish();
}

fn bench_prover_circuit2b(c: &mut Criterion){


    let mut rng = thread_rng();

    let mut group = c.benchmark_group("marlin-bn382-test circuit 2b-variable constraints-segment_size=num_constraints");

    let num_constraints = (14..=22).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &num_constraints in num_constraints.iter()
        {
            let universal_srs = MarlinInst::universal_setup::<_, Blake2s>(num_constraints, num_constraints, num_constraints, &mut rng).unwrap();
            let c = TestCircuit2b::<Fq>{ num_constraints, a: None, b: None };

            let (index_pk, _) = MarlinInst::index(
                &universal_srs,
                c.clone(),
            ).unwrap();

            add_to_trace!(
             || format!("****************{}*******************", num_constraints),
             || format!("--->START TIMESTAMP: {:?}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs())
             );

            group.bench_with_input(BenchmarkId::from_parameter(num_constraints), &num_constraints, |bn, _constraints| {
                bn.iter_batched(
                    || {
                        let mut rng = OsRng::default();
                        let a = Fq::rand(&mut rng);
                        let b = Fq::rand(&mut rng);
                        (a, b)
                    },
                    |(a, b)| {
                        let c = TestCircuit2b{ num_constraints, a: Some(a), b: Some(b) };

                        MarlinInst::prove(
                            &index_pk,
                            c,
                            &mut rng,
                        ).unwrap();
                    },
                    BatchSize::PerIteration
                );
            });
            add_to_trace!(
             || format!("****************{}*******************", num_constraints),
             || format!("--->END TIMESTAMP: {:?}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs())
             );        }
    group.finish();
}

fn bench_prover_circuit2c(c: &mut Criterion){


    let mut rng = thread_rng();

    let mut group = c.benchmark_group("marlin-bn382-test circuit 2c-variable constraints-segment_size=num_constraints");

    let num_constraints = (14..=22).map(|i| 2usize.pow(i)).collect::<Vec<_>>();

    for &num_constraints in num_constraints.iter()
        {
            let universal_srs = MarlinInst::universal_setup::<_, Blake2s>(num_constraints, num_constraints, num_constraints, &mut rng).unwrap();
            let c = TestCircuit2c::<Fq>{ num_constraints, a: None, b: None };

            let (index_pk, _) = MarlinInst::index(
                &universal_srs,
                c.clone(),
            ).unwrap();

            add_to_trace!(
             || format!("****************{}*******************", num_constraints),
             || format!("--->START TIMESTAMP: {:?}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs())
             );

            group.bench_with_input(BenchmarkId::from_parameter(num_constraints), &num_constraints, |bn, _constraints| {
                bn.iter_batched(
                    || {
                        let mut rng = OsRng::default();
                        let a = Fq::rand(&mut rng);
                        let b = Fq::rand(&mut rng);
                        (a, b)
                    },
                    |(a, b)| {
                        let c = TestCircuit2c{ num_constraints, a: Some(a), b: Some(b) };

                        MarlinInst::prove(
                            &index_pk,
                            c,
                            &mut rng,
                        ).unwrap();
                    },
                    BatchSize::PerIteration
                );
            });
            add_to_trace!(
             || format!("****************{}*******************", num_constraints),
             || format!("--->END TIMESTAMP: {:?}", SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs())
             );        }
    group.finish();
}

criterion_group!(
name = bn382_test_circuits;
config = Criterion::default().sample_size(10);
targets = bench_prover_circuit1a, bench_prover_circuit1b, bench_prover_circuit1c,
          bench_prover_circuit2a, bench_prover_circuit2b, bench_prover_circuit2c,
);

criterion_main!(bn382_test_circuits);