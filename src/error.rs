use crate::ahp::Error as AHPError;
use r1cs_core::SynthesisError;

/// A `enum` specifying the possible failure modes of the `SNARK`.
#[derive(Debug)]
pub enum Error<E> {
    /// The index is too large for the universal public parameters.
    IndexTooLarge(usize),
    /// There was an error in the underlying holographic IOP.
    AHPError(AHPError),
    /// There was a synthesis error.
    R1CSError(SynthesisError),
    /// There was an error in the underlying polynomial commitment.
    PolynomialCommitmentError(E),
}

impl<E> From<AHPError> for Error<E> {
    fn from(err: AHPError) -> Self {
        Error::AHPError(err)
    }
}

impl<E> From<SynthesisError> for Error<E> {
    fn from(err: SynthesisError) -> Self {
        Error::R1CSError(err)
    }
}

impl<E> Error<E> {
    /// Convert an error in the underlying polynomial commitment scheme
    /// to a `Error`.
    pub fn from_pc_err(err: E) -> Self {
        Error::PolynomialCommitmentError(err)
    }
}
