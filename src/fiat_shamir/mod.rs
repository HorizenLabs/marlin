use algebra::{PrimeField, ToConstraintField};
use rand_core::{
    RngCore, SeedableRng,
};
use digest::Digest;
use rand_chacha::ChaChaRng;
use std::marker::PhantomData;

/// Implementation of FiatShamirRNG using Poseidon Hash
pub mod poseidon;

/// the trait for Fiat-Shamir RNG
pub trait FiatShamirRng<F: PrimeField> {
    /// initialize the RNG
    fn new() -> Self;

    /// take in field elements
    fn absorb_field_elements<T: ToConstraintField<F>>(&mut self, elems: &[T]);
    /// take in bytes
    fn absorb_bytes(&mut self, elems: &[u8]);

    /// take in field elements
    fn squeeze_field_elements(&mut self, num: usize) -> Vec<F>;
    /// take out field elements of 128 bits
    fn squeeze_128_bits_field_elements(&mut self, num: usize) -> Vec<F>;
}

/// use a ChaCha stream cipher to generate the actual pseudorandom bits
/// use a digest funcion to do absorbing
pub struct FiatShamirChaChaRng<F: PrimeField, D: Digest> {
    /// the rng
    pub r: ChaChaRng,
    /// seed for the rng
    pub seed: Vec<u8>,
    #[doc(hidden)]
    field: PhantomData<F>,
    digest: PhantomData<D>,
}

impl<F: PrimeField, D: Digest> FiatShamirRng<F> for FiatShamirChaChaRng<F, D>
{
    fn new() -> Self {
        let seed = [0; 32];
        let r = ChaChaRng::from_seed(seed);
        Self {
            r,
            seed: seed.to_vec(),
            field: PhantomData,
            digest: PhantomData,
        }
    }

    fn absorb_field_elements<T: ToConstraintField<F>>(&mut self, src: &[T]) {
        let mut elems = Vec::<F>::new();
        for elem in src.iter() {
            elems.append(&mut elem.to_field_elements().unwrap());
        }

        let mut bytes = Vec::new();
        for elem in elems.iter() {
            elem.write(&mut bytes).expect("failed to convert to bytes");
        }
        self.absorb_bytes(&bytes);
    }

    fn absorb_bytes(&mut self, elems: &[u8]) {
        let mut bytes = elems.to_vec();
        bytes.extend_from_slice(&self.seed);

        let new_seed = D::digest(&bytes);
        self.seed = (*new_seed.as_slice()).to_vec();

        let mut seed = [0u8; 32];
        for (i, byte) in self.seed.as_slice().iter().enumerate() {
            seed[i] = *byte;
        }

        self.r = ChaChaRng::from_seed(seed);
    }

    fn squeeze_field_elements(&mut self, num: usize) -> Vec<F> {
        let mut res = Vec::<F>::new();
        for _ in 0..num {
            res.push(F::rand(&mut self.r));
        }
        res
    }

    fn squeeze_128_bits_field_elements(&mut self, num: usize) -> Vec<F> {
        let mut res = Vec::<F>::new();
        for _ in 0..num {
            let mut x = [0u8; 16];
            self.r.fill_bytes(&mut x);
            res.push(F::from_random_bytes(&x).unwrap());
        }
        res
    }
}