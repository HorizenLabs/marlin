#![allow(non_snake_case)]

use crate::ahp::{
    constraint_systems::{arithmetize_matrix, IndexerConstraintSystem, MatrixArithmetization, pad_input},
    AHPForR1CS, Error,
};
use crate::Vec;
use algebra::PrimeField;
use derivative::Derivative;
use algebra_utils::get_best_evaluation_domain;
use poly_commit::LabeledPolynomial;
use r1cs_core::{ConstraintSynthesizer, SynthesisError};

use std::marker::PhantomData;

/// Information about the index, including the field of definition, the number of
/// variables, the number of constraints, and the maximum number of non-zero
/// entries in any of the constraint matrices.
#[derive(Derivative)]
#[derivative(Clone(bound = ""), Copy(bound = ""))]
pub struct IndexInfo<F> {
    /// The total number of variables in the constraint system.
    pub num_variables: usize,
    /// The number of constraints.
    pub num_constraints: usize,
    /// The maximum number of non-zero entries in any constraint matrix.
    pub num_non_zero: usize,

    #[doc(hidden)]
    f: PhantomData<F>,
}

impl<F: PrimeField> algebra::ToBytes for IndexInfo<F> {
    fn write<W: std::io::Write>(&self, mut w: W) -> std::io::Result<()> {
        (self.num_variables as u64).write(&mut w)?;
        (self.num_constraints as u64).write(&mut w)?;
        (self.num_non_zero as u64).write(&mut w)
    }
}

impl<F: PrimeField> IndexInfo<F> {
    /// The maximum degree of polynomial required to represent this index in the
    /// the AHP.
    pub fn max_degree(&self, zk: bool) -> usize {
        AHPForR1CS::<F>::max_degree(self.num_constraints, self.num_variables, self.num_non_zero, zk)
            .unwrap()
    }
}

/// Represents a matrix.
pub type Matrix<F> = Vec<Vec<(F, usize)>>;

#[derive(Derivative)]
#[derivative(Clone(bound = "F: PrimeField"))]
/// The indexed version of the constraint system.
/// This struct contains three kinds of objects:
/// 1) `index_info` is information about the index, such as the size of the
///     public input
/// 2) `{a,b,c}` are the matrices defining the R1CS instance
/// 3) `{a,b,c}_star_arith` are structs containing information about A^*, B^*, and C^*,
/// which are matrices defined as `M^*(i, j) = M(j, i) * u_H(j, j)`.
pub struct Index<F: PrimeField> {
    /// Information about the index.
    pub index_info: IndexInfo<F>,

    /// The A matrix for the R1CS instance
    pub a: Matrix<F>,
    /// The B matrix for the R1CS instance
    pub b: Matrix<F>,
    /// The C matrix for the R1CS instance
    pub c: Matrix<F>,

    /// Arithmetization of the A* matrix.
    pub a_star_arith: MatrixArithmetization<F>,
    /// Arithmetization of the B* matrix.
    pub b_star_arith: MatrixArithmetization<F>,
    /// Arithmetization of the C* matrix.
    pub c_star_arith: MatrixArithmetization<F>,
}

impl<F: PrimeField> Index<F> {
    /// The maximum degree required to represent polynomials of this index.
    pub fn max_degree(&self, zk: bool) -> usize {
        self.index_info.max_degree(zk)
    }

    /// Iterate over the indexed polynomials.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![
            &self.a_star_arith.row,
            &self.a_star_arith.col,
            &self.a_star_arith.val,
            &self.a_star_arith.row_col,
            &self.b_star_arith.row,
            &self.b_star_arith.col,
            &self.b_star_arith.val,
            &self.b_star_arith.row_col,
            &self.c_star_arith.row,
            &self.c_star_arith.col,
            &self.c_star_arith.val,
            &self.c_star_arith.row_col,
        ]
        .into_iter()
    }
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// Generate the index for this constraint system.
    pub fn index<C: ConstraintSynthesizer<F>>(c: C) -> Result<Index<F>, Error> {
        let index_time = start_timer!(|| "AHP::Index");

        let constraint_time = start_timer!(|| "Generating constraints");
        let mut ics = IndexerConstraintSystem::new();
        c.generate_constraints(&mut ics)?;
        end_timer!(constraint_time);

        let padding_time = start_timer!(|| "Padding matrices to make them square");
        let num_inputs = ics.num_input_variables;
        pad_input(&mut ics, num_inputs);
        ics.make_matrices_square();
        end_timer!(padding_time);
        let matrix_processing_time = start_timer!(|| "Processing matrices");
        ics.process_matrices();
        end_timer!(matrix_processing_time);

        let num_formatted_input_variables = ics.num_input_variables;
        let num_witness_variables = ics.num_witness_variables;
        let num_constraints = ics.num_constraints;
        let num_non_zero = ics.num_non_zero();
        let num_variables = num_formatted_input_variables + num_witness_variables;

        if num_constraints != num_formatted_input_variables + num_witness_variables {
            eprintln!(
                "number of (formatted) input_variables: {}",
                num_formatted_input_variables
            );
            eprintln!("number of witness_variables: {}", num_witness_variables);
            eprintln!("number of num_constraints: {}", num_constraints);
            eprintln!("number of num_non_zero: {}", ics.num_non_zero());
            return Err(Error::NonSquareMatrix);
        }

        if !Self::num_formatted_public_inputs_is_admissible(num_formatted_input_variables) {
            Err(Error::InvalidPublicInputLength)?
        }

        let index_info = IndexInfo {
            num_variables,
            num_constraints,
            num_non_zero,

            f: PhantomData,
        };

        let domain_h = get_best_evaluation_domain::<F>(num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k = get_best_evaluation_domain::<F>(num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let x_domain = get_best_evaluation_domain(num_formatted_input_variables)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let b_domain = get_best_evaluation_domain(3 * domain_k.size() - 3)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let (mut a, mut b, mut c) = ics.constraint_matrices().expect("should not be `None`");

        let a_arithmetization_time = start_timer!(|| "Arithmetizing A");
        let a_star_arith = arithmetize_matrix("a", &mut a, &domain_k, &domain_h, &x_domain, &b_domain);
        end_timer!(a_arithmetization_time);

        let b_arithmetization_time = start_timer!(|| "Arithmetizing B");
        let b_star_arith = arithmetize_matrix("b", &mut b, &domain_k, &domain_h, &x_domain, &b_domain);
        end_timer!(b_arithmetization_time);

        let c_arithmetization_time = start_timer!(|| "Arithmetizing C");
        let c_star_arith = arithmetize_matrix("c", &mut c, &domain_k, &domain_h, &x_domain, &b_domain);
        end_timer!(c_arithmetization_time);

        end_timer!(index_time);
        Ok(Index {
            index_info,

            a,
            b,
            c,

            a_star_arith,
            b_star_arith,
            c_star_arith,
        })
    }
}
