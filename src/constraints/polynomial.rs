use algebra::PrimeField;
use r1cs_std::fields::{
    nonnative::nonnative_field_gadget::NonNativeFieldGadget,
    FieldGadget,
};
use r1cs_core::{ConstraintSystem, SynthesisError};
use std::marker::PhantomData;

pub struct AlgebraForAHP<F: PrimeField, ConstraintF: PrimeField> {
    field: PhantomData<F>,
    constraint_field: PhantomData<ConstraintF>,
}

impl<F: PrimeField, ConstraintF: PrimeField> AlgebraForAHP<F, ConstraintF> {
    pub fn prepare<CS: ConstraintSystem<ConstraintF>>(
        cs: CS,
        x: &NonNativeFieldGadget<F, ConstraintF>,
        domain_size: u64,
    ) -> Result<NonNativeFieldGadget<F, ConstraintF>, SynthesisError> {
        x.pow_by_constant(cs, &[domain_size])
    }

    pub fn prepared_eval_vanishing_polynomial<CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        x_prepared: &NonNativeFieldGadget<F, ConstraintF>,
    ) -> Result<NonNativeFieldGadget<F, ConstraintF>, SynthesisError> {
        let one = NonNativeFieldGadget::<F, ConstraintF>::one(cs.ns(|| "alloc one"))?;
        let result = x_prepared.sub(cs.ns(|| "x_prepared - one"), &one)?;
        Ok(result)
    }

    pub fn eval_vanishing_polynomial<CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        x: &NonNativeFieldGadget<F, ConstraintF>,
        domain_size: u64,
    ) -> Result<NonNativeFieldGadget<F, ConstraintF>, SynthesisError> {
        let x_prepared = Self::prepare(cs.ns(|| "prepare x"), x, domain_size)?;
        Self::prepared_eval_vanishing_polynomial(
            cs.ns(|| "compute eval vanishing poly"),
            &x_prepared
        )
    }

    pub fn prepared_eval_bivariable_vanishing_polynomial<CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        x: &NonNativeFieldGadget<F, ConstraintF>,
        y: &NonNativeFieldGadget<F, ConstraintF>,
        x_prepared: &NonNativeFieldGadget<F, ConstraintF>,
        y_prepared: &NonNativeFieldGadget<F, ConstraintF>,
    ) -> Result<NonNativeFieldGadget<F, ConstraintF>, SynthesisError> {
        let denominator = x.sub(cs.ns(|| "denominator"), &y)?;

        let numerator = x_prepared.sub(cs.ns(|| "numerator"), &y_prepared)?;
        let denominator_invert = denominator.inverse(cs.ns(|| "invert denominator"))?;

        let result = numerator.mul(cs.ns(|| "mul * denominator_inverse"), &denominator_invert)?;

        Ok(result)
    }

    pub fn eval_bivariate_vanishing_polynomial<CS: ConstraintSystem<ConstraintF>>(
        mut cs: CS,
        x: &NonNativeFieldGadget<F, ConstraintF>,
        y: &NonNativeFieldGadget<F, ConstraintF>,
        domain_size: u64,
    ) -> Result<NonNativeFieldGadget<F, ConstraintF>, SynthesisError> {
        let x_prepared = Self::prepare(cs.ns(|| "prepare x"), x, domain_size)?;
        let y_prepared = Self::prepare(cs.ns(|| "prepare y"), y, domain_size)?;

        Self::prepared_eval_bivariable_vanishing_polynomial(
            cs.ns(|| "eval bivariate vanishing poly"),
            x,
            y,
            &x_prepared,
            &y_prepared
        )
    }
}
