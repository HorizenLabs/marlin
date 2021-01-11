use algebra::{PrimeField, ToConstraintField, FpParameters};
use primitives::{PoseidonParameters, PoseidonSBox, PoseidonHash, AlgebraicSponge};
use crate::fiat_shamir::FiatShamirRng;

impl<F, P, SB> FiatShamirRng<F> for PoseidonHash<F, P, SB>
where
    F: PrimeField,
    P: PoseidonParameters<Fr = F>,
    SB: PoseidonSBox<P>
{
    fn new() -> Self {
        <Self as AlgebraicSponge<F>>::new()
    }

    fn absorb_field_elements<T: ToConstraintField<F>>(&mut self, elems: &[T]) {
        self.absorb(elems.iter().flat_map(|t| t.to_field_elements().unwrap()).collect())
    }

    fn absorb_bytes(&mut self, elems: &[u8]) {
        self.absorb(elems.to_field_elements().unwrap())
    }

    fn squeeze_field_elements(&mut self, num: usize) -> Vec<F> {
        self.squeeze(num)
    }

    fn squeeze_128_bits_field_elements(&mut self, num: usize) -> Vec<F> {

        // Compute number of challenges we can extract from a single field element
        let capacity = F::Params::CAPACITY as usize;
        // TODO: Always true basically, but for completeness handle the case when this is not true.
        assert!(capacity >= 128);
        let challenges_per_fe = capacity/128;

        // Compute number of field elements we need in order to provide the requested 'num'
        // 128 bits field elements
        let to_squeeze = ((num/challenges_per_fe) as f64).ceil() as usize;

        // Squeeze the required number of field elements
        let outputs_bits = self
            .squeeze_field_elements(to_squeeze)
            .into_iter()
            .flat_map(|fe|{ (&fe.write_bits()[..capacity]).to_vec() }).collect::<Vec<_>>();

        // Take the required amount of 128 bits chunks and read a field element out of each
        // of them.
        outputs_bits.chunks(128).take(num).map(|bits| {
            F::read_bits(bits.to_vec()).expect("Should be able to read a field element from 128 bits")
        }).collect()
    }
}