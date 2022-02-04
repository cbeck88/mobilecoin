// Copyright (c) 2018-2021 The MobileCoin Foundation

//! An RCT_TYPE_BULLETPROOFS_2 signature.
//!
//! # References
//! * [Ring Confidential Transactions](https://eprint.iacr.org/2015/1098.pdf)
//! * [Bulletproofs](https://eprint.iacr.org/2017/1066.pdf)

extern crate alloc;

use alloc::vec::Vec;
use bulletproofs_og::RangeProof;
use core::convert::TryFrom;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use mc_common::HashSet;
use mc_crypto_digestible::{DigestTranscript, Digestible, MerlinTranscript};
use mc_crypto_keys::{CompressedRistrettoPublic, RistrettoPrivate};
use mc_util_serial::prost::Message;
use rand_core::{CryptoRng, RngCore};
use serde::{Deserialize, Serialize};

use crate::{
    constants::FEE_BLINDING,
    domain_separators::EXTENDED_MESSAGE_DOMAIN_TAG,
    range_proofs::{check_range_proofs, generate_range_proofs},
    ring_signature::{generators, mlsag::RingMLSAG, Error, KeyImage, Scalar},
    Commitment, CompressedCommitment, CompressedProofOfOpening, ProofOfOpening,
};

/// An RCT_TYPE_BULLETPROOFS_2 signature, plus optionally a proof of opening.
///
/// Proofs of opening are required to support confidential token ids. The
/// proof of opening confirms that token ids are not being mixed in a
/// transaction, without revealing any of the commitments.
///
/// A signature without a proof of opening is an "old-style" signature.
/// It will fail verification unless `token_id = 0`.
/// (Separately from this verification, such a Tx should be rejected unless
/// every input and output is an old-style TxOut without masked_token_id.
/// This is because if any of the inputs or outputs are masked token ids,
/// we cannot be sure that someone is not maliciously mixing token ids.)
///
/// A signature with a proof of opening is a "new-style" signature.
/// It may pass verification with a nonzero token id, if the proof of opening
/// checks out.
/// (Separately from this verification, such a Tx should be rejected unless
/// every output is a new-style TxOut with masked token id.)
#[derive(Clone, Digestible, Eq, PartialEq, Serialize, Deserialize, Message)]
pub struct SignatureRctBulletproofs {
    /// Signature for each input ring.
    #[prost(message, repeated, tag = "1")]
    pub ring_signatures: Vec<RingMLSAG>,

    /// Commitments of value equal to each real input.
    #[prost(message, repeated, tag = "2")]
    pub pseudo_output_commitments: Vec<CompressedCommitment>,

    /// Proof that all pseudo_outputs and transaction outputs are in [0, 2^64).
    /// This contains range_proof.to_bytes(). It is stored this way so that this
    /// struct may derive Default, which is a requirement for serializing
    /// with Prost.
    #[prost(bytes, tag = "3")]
    pub range_proof_bytes: Vec<u8>,

    /// Proof that all pseudo outputs are over the specified Pedersen
    /// generators. This implies that all confidential token ids are of the
    /// correct type.
    /// If present, then this is a new-style Tx.
    ///
    /// If omitted, then this is an old-style Tx.
    ///
    /// In the future we may make this field required and drop support for
    /// old-style Tx.
    #[prost(message, optional, tag = "4")]
    pub proof_of_opening: Option<CompressedProofOfOpening>,
}

impl SignatureRctBulletproofs {
    /// Sign.
    ///
    /// # Arguments
    /// * `block_version` - The block-version we should target for this
    ///   signature
    /// * `message` - The messages to be signed, e.g. Hash(TxPrefix).
    /// * `rings` - One or more rings of one-time addresses and amount
    ///   commitments.
    /// * `real_input_indices` - The index of the real input in each ring.
    /// * `input_secrets` - One-time private key, amount value, and amount
    ///   blinding for each real input.
    /// * `output_values_and_blindings` - Value and blinding for each output
    ///   amount commitment.
    /// * `fee` - Value of the implicit fee output.
    pub fn sign<CSPRNG: RngCore + CryptoRng>(
        block_version: u32,
        message: &[u8; 32],
        rings: &[Vec<(CompressedRistrettoPublic, CompressedCommitment)>],
        real_input_indices: &[usize],
        input_secrets: &[(RistrettoPrivate, u64, Scalar)],
        output_values_and_blindings: &[(u64, Scalar)],
        fee: u64,
        token_id: u32,
        rng: &mut CSPRNG,
    ) -> Result<Self, Error> {
        sign_with_balance_check(
            message,
            rings,
            real_input_indices,
            input_secrets,
            output_values_and_blindings,
            fee,
            token_id,
            true,
            true,
            // We enable building proof of opening if block_version > 1
            block_version > 1,
            rng,
        )
    }

    /// Verify.
    ///
    /// # Arguments
    /// * `message` - The signed message.
    /// * `rings` - One or more rings of one-time addresses and amount
    ///   commitments.
    /// * `output_commitments` - Output amount commitments.
    /// * `fee` - Value of the implicit fee output.
    /// * `rng` -
    pub fn verify<CSPRNG: RngCore + CryptoRng>(
        &self,
        message: &[u8; 32],
        rings: &[Vec<(CompressedRistrettoPublic, CompressedCommitment)>],
        output_commitments: &[CompressedCommitment],
        fee: u64,
        token_id: u32,
        rng: &mut CSPRNG,
    ) -> Result<(), Error> {
        // Signature must contain one ring signature for each ring.
        if rings.len() != self.ring_signatures.len() {
            return Err(Error::LengthMismatch(
                rings.len(),
                self.ring_signatures.len(),
            ));
        }

        // Signature must contain one pseudo_output for each ring.
        if rings.len() != self.pseudo_output_commitments.len() {
            return Err(Error::LengthMismatch(
                rings.len(),
                self.pseudo_output_commitments.len(),
            ));
        }

        // Key images must be unique.
        {
            let key_images_are_unique = {
                let mut uniq = HashSet::default();
                self.key_images().into_iter().all(move |x| uniq.insert(x))
            };
            if !key_images_are_unique {
                return Err(Error::DuplicateKeyImage);
            }
        }

        // output_commitments must decompress.
        // This ensures that each commitment encodes a valid Ristretto point.
        let mut decompressed_output_commitments: Vec<Commitment> = Vec::new();
        for output_commitment in output_commitments {
            let commitment = Commitment::try_from(output_commitment)?;
            decompressed_output_commitments.push(commitment);
        }

        // pseudo_output_commitments must decompress.
        // This ensures that each commitment encodes a valid Ristretto point.
        let mut decompressed_pseudo_output_commitments: Vec<Commitment> = Vec::new();
        for pseudo_output in &self.pseudo_output_commitments {
            let commitment = Commitment::try_from(pseudo_output)?;
            decompressed_pseudo_output_commitments.push(commitment);
        }

        // Compute the pedersen generators for this token_id
        let generator = generators(token_id);

        // pseudo_output_commitments and output commitments must be in [0, 2^64).
        {
            let commitments: Vec<CompressedRistretto> = self
                .pseudo_output_commitments
                .iter()
                .chain(output_commitments.iter())
                .map(|compressed_commitment| compressed_commitment.point)
                .collect();

            let range_proof = RangeProof::from_bytes(&self.range_proof_bytes)
                .map_err(|_e| Error::RangeProofError)?;

            check_range_proofs(&range_proof, &commitments, &generator, rng)
                .map_err(|_e| Error::RangeProofError)?;
        }

        // Compute sum of pseudo outputs
        let sum_of_pseudo_output_commitments: RistrettoPoint =
            decompressed_pseudo_output_commitments
                .iter()
                .map(|commitment| commitment.point)
                .sum();

        // Output commitments - pseudo_outputs must be zero.
        {
            let sum_of_output_commitments: RistrettoPoint = decompressed_output_commitments
                .iter()
                .map(|commitment| commitment.point)
                .sum();

            // The implicit fee output.
            let fee_commitment = generator.commit(Scalar::from(fee), *FEE_BLINDING);
            let difference =
                sum_of_output_commitments + fee_commitment - sum_of_pseudo_output_commitments;
            if difference != generator.commit(Scalar::zero(), Scalar::zero()) {
                return Err(Error::ValueNotConserved);
            }
        }

        // Extend the message with the range proof and pseudo_output_commitments, and
        // proof of opening if present
        let extended_message = compute_extended_message_either_version(
            message,
            &self.pseudo_output_commitments,
            &self.range_proof_bytes,
            self.proof_of_opening.as_ref(),
        );

        // Each MLSAG must be valid.
        for (i, ring) in rings.iter().enumerate() {
            let ring_signature = &self.ring_signatures[i];
            let pseudo_output = self.pseudo_output_commitments[i];
            ring_signature.verify(&extended_message, ring, &pseudo_output)?;
        }

        // Verify proof of opening against sum of pseudo outputs
        if let Some(proof_of_opening) = self.proof_of_opening.as_ref() {
            let proof_of_opening = ProofOfOpening::try_from(proof_of_opening)?;
            if !proof_of_opening.verify(&sum_of_pseudo_output_commitments, &generator) {
                return Err(Error::InvalidProofOfOpening);
            }
        } else if token_id != 0 {
            // Backwards compat: If proof of opening is omitted, then this is an old-style
            // Tx, and the token id must be 0.
            // We must ALSO ensure that all inputs and outputs are old style TxOut's that
            // do not have masked token id,
            // but that happens in transaction validation layer, since this layer can't
            // see the TxOut's.
            return Err(Error::MissingProofOfOpening);
        }

        // Signature is valid.
        Ok(())
    }

    /// Key images spent by this signature.
    pub fn key_images(&self) -> Vec<KeyImage> {
        self.ring_signatures
            .iter()
            .map(|mlsag| mlsag.key_image)
            .collect()
    }
}

/// Sign, with optional check for inputs = outputs.
///
/// # Arguments
/// * `message` - The messages to be signed, e.g. Hash(TxPrefix).
/// * `rings` - One or more rings of one-time addresses and amount commitments.
/// * `real_input_indices` - The index of the real input in each ring.
/// * `input_secrets` - One-time private key, amount value, and amount blinding
///   for each real input.
/// * `output_values_and_blindings` - Value and blinding for each output amount
///   commitment.
/// * `fee` - Value of the implicit fee output.
/// * `check_value_is_preserved` - If true, check that the value of inputs
/// * `check_proof_of_opening` - If true, check that the proof of opening is
///   valid equals value of outputs.
fn sign_with_balance_check<CSPRNG: RngCore + CryptoRng>(
    message: &[u8; 32],
    rings: &[Vec<(CompressedRistrettoPublic, CompressedCommitment)>],
    real_input_indices: &[usize],
    input_secrets: &[(RistrettoPrivate, u64, Scalar)],
    output_values_and_blindings: &[(u64, Scalar)],
    fee: u64,
    token_id: u32,
    check_value_is_preserved: bool,
    check_proof_of_opening: bool,
    use_proof_of_opening: bool,
    rng: &mut CSPRNG,
) -> Result<SignatureRctBulletproofs, Error> {
    if rings.is_empty() {
        return Err(Error::NoInputs);
    }
    let num_inputs = rings.len();
    let ring_size = rings[0].len();
    if ring_size == 0 {
        return Err(Error::InvalidRingSize(0));
    }

    // Each ring must have the same size.
    for ring in rings {
        if ring.len() != ring_size {
            return Err(Error::InvalidRingSize(ring.len()));
        }
    }

    // `input_secrets` must contain an element for each input.
    if input_secrets.len() != num_inputs {
        return Err(Error::InvalidInputSecretsSize(input_secrets.len()));
    }

    // Each `real_input_index` must be in [0,ring_size - 1].
    for i in real_input_indices {
        if *i >= ring_size {
            return Err(Error::IndexOutOfBounds);
        }
    }

    // Blindings for pseudo_outputs. All but the last are random.
    // Constructing blindings in this way ensures that sum_of_outputs -
    // sum_of_pseudo_outputs = 0 if the sum of outputs and the sum of
    // pseudo_outputs have equal value.
    let mut pseudo_output_blindings: Vec<Scalar> = Vec::new();
    for _i in 0..num_inputs - 1 {
        pseudo_output_blindings.push(Scalar::random(rng));
    }
    // The implicit fee output is ommitted because its blinding is zero.
    let sum_of_output_blindings: Scalar = output_values_and_blindings
        .iter()
        .map(|(_, blinding)| blinding)
        .sum();

    let sum_of_pseudo_output_blindings: Scalar = pseudo_output_blindings.iter().sum();
    let last_blinding: Scalar = sum_of_output_blindings - sum_of_pseudo_output_blindings;
    pseudo_output_blindings.push(last_blinding);

    // Create Range proofs for outputs and pseudo-outputs.
    let pseudo_output_values_and_blindings: Vec<(u64, Scalar)> = input_secrets
        .iter()
        .zip(pseudo_output_blindings.iter())
        .map(|((_, value, _), blinding)| (*value, *blinding))
        .collect();

    // Compute the pedersen generators for this token_id
    let generator = generators(token_id);

    let (range_proof, commitments) = {
        // The implicit fee output is omitted from the range proof because it is known.

        let (values, blindings): (Vec<_>, Vec<_>) = pseudo_output_values_and_blindings
            .iter()
            .chain(output_values_and_blindings.iter())
            .map(|(value, blinding)| (*value, *blinding))
            .unzip();
        generate_range_proofs(&values, &blindings, &generator, rng)
            .map_err(|_e| Error::RangeProofError)?
    };

    let sum_of_pseudo_output_values: Scalar = pseudo_output_values_and_blindings
        .iter()
        .map(|(value, _)| Scalar::from(*value))
        .sum();

    // Build a proof of opening if enabled
    let proof_of_opening: Option<CompressedProofOfOpening> = if use_proof_of_opening {
        let proof = ProofOfOpening::new(
            sum_of_pseudo_output_values,
            sum_of_pseudo_output_blindings + last_blinding,
            &generator,
        );
        Some((&proof).into())
    } else {
        None
    };

    if check_value_is_preserved {
        let sum_of_output_commitments: RistrettoPoint = output_values_and_blindings
            .iter()
            .map(|(value, blinding)| generator.commit(Scalar::from(*value), *blinding))
            .sum();

        let sum_of_pseudo_output_commitments: RistrettoPoint = pseudo_output_values_and_blindings
            .iter()
            .map(|(value, blinding)| generator.commit(Scalar::from(*value), *blinding))
            .sum();

        // The implicit fee output.
        let fee_commitment = generator.commit(Scalar::from(fee), *FEE_BLINDING);

        let difference =
            sum_of_output_commitments + fee_commitment - sum_of_pseudo_output_commitments;
        if difference != generator.commit(Scalar::zero(), Scalar::zero()) {
            return Err(Error::ValueNotConserved);
        }
    }

    let pseudo_output_commitments: Vec<CompressedCommitment> = commitments
        .iter()
        .take(num_inputs)
        .map(CompressedCommitment::from)
        .collect();

    if use_proof_of_opening && check_proof_of_opening {
        let sum_of_pseudo_output_commitments = commitments
            .iter()
            .take(num_inputs)
            .filter_map(|x| x.decompress())
            .sum();

        let proof_of_opening =
            ProofOfOpening::try_from(proof_of_opening.as_ref().unwrap()).unwrap();
        if !proof_of_opening.verify(&sum_of_pseudo_output_commitments, &generator) {
            return Err(Error::InvalidProofOfOpening);
        }
    }

    // Extend the message with the range proof and pseudo_output_commitments.
    // This ensures that they are signed by each RingMLSAG.
    let range_proof_bytes = range_proof.to_bytes();

    let extended_message = compute_extended_message_either_version(
        message,
        &pseudo_output_commitments,
        &range_proof_bytes,
        proof_of_opening.as_ref(),
    );

    // Prove that the signer is allowed to spend a public key in each ring, and that
    // the input's value equals the value of the pseudo_output.
    let mut ring_signatures: Vec<RingMLSAG> = Vec::new();
    for i in 0..num_inputs {
        let real_index = real_input_indices[i];
        let (onetime_private_key, value, blinding) = input_secrets[i];
        let ring_signature = RingMLSAG::sign(
            &extended_message,
            &rings[i],
            real_index,
            &onetime_private_key,
            value,
            &blinding,
            &pseudo_output_blindings[i],
            &generator,
            rng,
        )?;
        ring_signatures.push(ring_signature);
    }

    Ok(SignatureRctBulletproofs {
        ring_signatures,
        pseudo_output_commitments,
        range_proof_bytes,
        proof_of_opening,
    })
}

/// Toggles between old-style and new-style extended message
fn compute_extended_message_either_version(
    message: &[u8],
    pseudo_output_commitments: &[CompressedCommitment],
    range_proof_bytes: &[u8],
    maybe_proof_of_opening: Option<&CompressedProofOfOpening>,
) -> Vec<u8> {
    if let Some(proof_of_opening) = maybe_proof_of_opening {
        // New-style extended message using merlin
        digest_extended_message(
            message,
            &pseudo_output_commitments,
            &range_proof_bytes,
            proof_of_opening,
        )
        .to_vec()
    } else {
        // Old-style extended message
        extend_message(message, &pseudo_output_commitments, &range_proof_bytes)
    }
}

/// Concatenates [message || pseudo_output_commitments || range_proof].
/// (old-style Tx's)
fn extend_message(
    message: &[u8],
    pseudo_output_commitments: &[CompressedCommitment],
    range_proof_bytes: &[u8],
) -> Vec<u8> {
    let mut extended_message: Vec<u8> = Vec::with_capacity(
        message.len() + pseudo_output_commitments.len() * 32 + range_proof_bytes.len(),
    );
    extended_message.extend_from_slice(message);
    for commitment in pseudo_output_commitments {
        extended_message.extend_from_slice(commitment.as_ref());
    }
    extended_message.extend_from_slice(range_proof_bytes);
    extended_message
}

/// Computes a merlin digest of message, pseudo_output_commitments, range proof,
/// proof_of_opening
fn digest_extended_message(
    message: &[u8],
    pseudo_output_commitments: &[CompressedCommitment],
    range_proof_bytes: &[u8],
    proof_of_opening: &CompressedProofOfOpening,
) -> [u8; 32] {
    let mut transcript = MerlinTranscript::new(EXTENDED_MESSAGE_DOMAIN_TAG.as_bytes());
    message.append_to_transcript(b"message", &mut transcript);
    pseudo_output_commitments.append_to_transcript(b"pseudo_output_commitments", &mut transcript);
    range_proof_bytes.append_to_transcript(b"range_proof_bytes", &mut transcript);
    proof_of_opening.append_to_transcript(b"proof_of_opening", &mut transcript);

    let mut output = [0u8; 32];
    transcript.extract_digest(&mut output);
    output
}

#[cfg(test)]
mod rct_bulletproofs_tests {
    use super::sign_with_balance_check;
    use crate::{
        range_proofs::generate_range_proofs,
        ring_signature::{generators, Error, KeyImage, PedersenGens, SignatureRctBulletproofs},
        CompressedCommitment,
    };
    use alloc::vec::Vec;
    use curve25519_dalek::scalar::Scalar;
    use mc_crypto_keys::{CompressedRistrettoPublic, RistrettoPrivate, RistrettoPublic};
    use mc_util_from_random::FromRandom;
    use proptest::prelude::*;
    use rand::{rngs::StdRng, CryptoRng, SeedableRng};
    use rand_core::RngCore;

    extern crate std;

    struct SignatureParams {
        /// Message to be signed.
        message: [u8; 32],

        /// Rings of input onetime addresses and amount commitments.
        rings: Vec<Vec<(CompressedRistrettoPublic, CompressedCommitment)>>,

        /// The index of the real input in each ring.
        real_input_indices: Vec<usize>,

        /// One-time private key, amount value, and amount blinding for each
        /// real input.
        input_secrets: Vec<(RistrettoPrivate, u64, Scalar)>,

        /// Value and blinding for each output amount commitment.
        output_values_and_blindings: Vec<(u64, Scalar)>,

        /// Token id
        token_id: u32,
    }

    impl SignatureParams {
        fn generator(&self) -> PedersenGens {
            generators(self.token_id)
        }

        fn random<RNG: RngCore + CryptoRng>(
            num_inputs: usize,
            num_mixins: usize,
            rng: &mut RNG,
        ) -> Self {
            let mut message = [0u8; 32];
            rng.fill_bytes(&mut message);

            let token_id = rng.next_u32();
            let generator = generators(token_id);

            let mut rings = Vec::new();
            let mut real_input_indices = Vec::new();
            let mut input_secrets = Vec::new();

            for _i in 0..num_inputs {
                let mut ring: Vec<(CompressedRistrettoPublic, CompressedCommitment)> = Vec::new();
                // Create random mixins.
                for _i in 0..num_mixins {
                    let address =
                        CompressedRistrettoPublic::from(RistrettoPublic::from_random(rng));
                    let commitment = {
                        let value = rng.next_u64();
                        let blinding = Scalar::random(rng);
                        CompressedCommitment::new(value, blinding, &generator)
                    };
                    ring.push((address, commitment));
                }
                // The real input.
                let onetime_private_key = RistrettoPrivate::from_random(rng);
                let onetime_public_key =
                    CompressedRistrettoPublic::from(RistrettoPublic::from(&onetime_private_key));

                let value = rng.next_u64();
                let blinding = Scalar::random(rng);
                let commitment = CompressedCommitment::new(value, blinding, &generator);

                let real_index = rng.next_u64() as usize % (num_mixins + 1);
                ring.insert(real_index, (onetime_public_key, commitment));

                rings.push(ring);
                real_input_indices.push(real_index);
                input_secrets.push((onetime_private_key, value, blinding));
            }

            // Create one output with the same value as each input.
            let output_values_and_blindings: Vec<_> = input_secrets
                .iter()
                .map(|(_, value, _)| {
                    let blinding = Scalar::random(rng);
                    (*value, blinding)
                })
                .collect();

            SignatureParams {
                message,
                rings,
                real_input_indices,
                input_secrets,
                output_values_and_blindings,
                token_id,
            }
        }

        fn get_output_commitments(&self) -> Vec<CompressedCommitment> {
            self.output_values_and_blindings
                .iter()
                .map(|(value, blinding)| {
                    CompressedCommitment::new(*value, *blinding, &self.generator())
                })
                .collect()
        }

        fn sign<RNG: RngCore + CryptoRng>(
            &self,
            fee: u64,
            rng: &mut RNG,
        ) -> Result<SignatureRctBulletproofs, Error> {
            SignatureRctBulletproofs::sign(
                2,
                &self.message,
                &self.rings,
                &self.real_input_indices,
                &self.input_secrets,
                &self.output_values_and_blindings,
                fee,
                self.token_id,
                rng,
            )
        }

        fn sign_without_balance_check<RNG: RngCore + CryptoRng>(
            &self,
            fee: u64,
            rng: &mut RNG,
        ) -> Result<SignatureRctBulletproofs, Error> {
            sign_with_balance_check(
                &self.message,
                &self.rings,
                &self.real_input_indices,
                &self.input_secrets,
                &self.output_values_and_blindings,
                fee,
                self.token_id,
                false,
                false,
                true,
                rng,
            )
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(6))]

        #[test]
        // `sign`should return an error if `rings` is empty.
        fn sign_rejects_empty_rings(
            num_inputs in 1..8usize,
            num_mixins in 1..17usize,
            seed in any::<[u8; 32]>(),
        ) {
            let mut rng: StdRng = SeedableRng::from_seed(seed);
            let mut params = SignatureParams::random(num_inputs, num_mixins, &mut rng);
            params.rings = Vec::new();

            let result = params.sign(0, &mut rng);

            match result {
                Err(Error::NoInputs) => {} // OK,
                _ => panic!(),
            }
        }

        #[test]
        // `sign`should return an error if `rings[0]` is empty.
        // The first ring is used to infer the ring size.
        fn sign_rejects_empty_rings_zero(
            num_inputs in 1..8usize,
            num_mixins in 1..17usize,
            seed in any::<[u8; 32]>(),
        ) {
            let mut rng: StdRng = SeedableRng::from_seed(seed);
            let mut params = SignatureParams::random(num_inputs, num_mixins, &mut rng);
            params.rings[0] = Vec::new();

            let result = params.sign(0, &mut rng);

            match result {
                Err(Error::InvalidRingSize(0)) => {} // OK,
                _ => panic!(),
            }
        }

        #[test]
        // `sign` should produce a signature with one ring signature and one pseudo-output per input.
        fn sign_signature_has_correct_lengths(
            num_inputs in 1..8usize,
            num_mixins in 1..17usize,
            seed in any::<[u8; 32]>(),
        ) {
            let mut rng: StdRng = SeedableRng::from_seed(seed);
            let params = SignatureParams::random(num_inputs, num_mixins, &mut rng);
            let signature = params.sign(0, &mut rng).unwrap();

            // The signature must contain one ring signature per input.
            assert_eq!(signature.ring_signatures.len(), num_inputs);

            // The signature must contain one pseudo-output per input.
            assert_eq!(signature.pseudo_output_commitments.len(), num_inputs);

            let ring_size = num_mixins + 1;
            for ring_signature in &signature.ring_signatures {
                assert_eq!(ring_signature.responses.len(), 2 * ring_size);
            }
        }

        #[test]
        // `verify` should accept valid signatures.
        fn verify_accepts_valid_signatures(
            num_inputs in 1..8usize,
            num_mixins in 1..17usize,
            seed in any::<[u8; 32]>(),
        ) {
            let mut rng: StdRng = SeedableRng::from_seed(seed);
            let params = SignatureParams::random(num_inputs, num_mixins, &mut rng);
            let fee = 0;
            let signature = params.sign(fee, &mut rng).unwrap();

            let result = signature.verify(
                &params.message,
                &params.rings,
                &params.get_output_commitments(),
                fee,
                params.token_id,
                &mut rng,
            );
            result.unwrap();
        }

        #[test]
        // `verify` should reject a signature that contains an invalid MLSAG signature.
        fn test_verify_rejects_signature_signed_with_invalid_mlsag(
            num_inputs in 1..8usize,
            num_mixins in 1..17usize,
            seed in any::<[u8; 32]>(),
        ) {
            let mut rng: StdRng = SeedableRng::from_seed(seed);
            let params = SignatureParams::random(num_inputs, num_mixins, &mut rng);
            let fee = 0;

            let mut signature = params.sign(fee, &mut rng).unwrap();

            // Modify an MLSAG ring signature
            let index = rng.next_u64() as usize % (num_inputs);
            signature.ring_signatures[index].key_image = KeyImage::from(rng.next_u64());

            let result = signature.verify(
                &params.message,
                &params.rings,
                &params.get_output_commitments(),
                fee,
                params.token_id,
                &mut rng,
            );

            assert_eq!(result, Err(Error::InvalidSignature));
        }

        #[test]
        // `verify` rejects a signature if the sum of the outputs minus the sum of the pseudo-outputs is not zero.
        fn test_verify_rejects_signature_when_value_not_conserved(
            num_inputs in 1..8usize,
            num_mixins in 1..17usize,
            seed in any::<[u8; 32]>(),
        ) {
            let mut rng: StdRng = SeedableRng::from_seed(seed);
            let mut params = SignatureParams::random(num_inputs, num_mixins, &mut rng);
            let fee = 0;
            // Modify an output value
            {
                let index = rng.next_u64() as usize % (num_inputs);
                let (_value, blinding) = params.output_values_and_blindings[index].clone();
                params.output_values_and_blindings[index] = (rng.next_u64(), blinding);
            }

            // Sign, without checking that value is preserved.
            let invalid_signature = params.sign_without_balance_check(fee, &mut rng).unwrap();

            let result = invalid_signature.verify(
                &params.message,
                &params.rings,
                &params.get_output_commitments(),
                fee,
                params.token_id,
                &mut rng,
            );

            assert_eq!(result, Err(Error::ValueNotConserved));
        }

        #[test]
        // `verify` rejects a signature with invalid range proof.
        fn test_verify_rejects_signature_with_invalid_range_proof(
            num_inputs in 1..8usize,
            num_mixins in 1..17usize,
            seed in any::<[u8; 32]>(),
        ) {
            let mut rng: StdRng = SeedableRng::from_seed(seed);
            let params = SignatureParams::random(num_inputs, num_mixins, &mut rng);
            let fee = 0;
            let mut signature = params.sign(fee, &mut rng).unwrap();

            // Modify the range proof
            let wrong_range_proof = {
                let values = [13; 6];
                let blindings: Vec<Scalar> = values
                    .iter()
                    .map(|_value| Scalar::random(&mut rng))
                    .collect();
                let (range_proof, _commitments) =
                    generate_range_proofs(&values, &blindings, &params.generator(), &mut rng).unwrap();
                range_proof
            };

            signature.range_proof_bytes = wrong_range_proof.to_bytes();

            let result = signature.verify(
                &params.message,
                &params.rings,
                &params.get_output_commitments(),
                fee,
                params.token_id,
                &mut rng,
            );

            assert_eq!(result, Err(Error::RangeProofError));
        }

        #[test]
        // `verify` rejects a signature that spends the same input in two different rings.
        fn test_verify_rejects_signature_with_duplicate_key_images(
            num_inputs in 4..8usize,
            num_mixins in 1..17usize,
            seed in any::<[u8; 32]>(),
        ) {
            let mut rng: StdRng = SeedableRng::from_seed(seed);
            let mut params = SignatureParams::random(num_inputs, num_mixins, &mut rng);
            let fee = 0;

            // Duplicate one of the rings.
            params.rings[2] = params.rings[3].clone();
            params.output_values_and_blindings[2] = params.output_values_and_blindings[3].clone();
            params.input_secrets[2] = params.input_secrets[3].clone();
            params.real_input_indices[2] = params.real_input_indices[3];

            let signature = params.sign(fee, &mut rng).unwrap();

            let result = signature.verify(
                &params.message,
                &params.rings,
                &params.get_output_commitments(),
                fee,
                params.token_id,
                &mut rng,
            );

            assert_eq!(result, Err(Error::DuplicateKeyImage));
        }

        #[test]
        // decode(encode(&signature)) should be the identity function.
        fn test_encode_decode(
            num_inputs in 4..8usize,
            num_mixins in 1..17usize,
            seed in any::<[u8; 32]>(),
        ) {
            let mut rng: StdRng = SeedableRng::from_seed(seed);
            let params = SignatureParams::random(num_inputs, num_mixins, &mut rng);
            let fee = 0;
            let signature = params.sign(fee, &mut rng).unwrap();

            use mc_util_serial::prost::Message;

            // The encoded bytes should have the correct length.
            let bytes = mc_util_serial::encode(&signature);
            assert_eq!(bytes.len(), signature.encoded_len());

            // decode(encode(&signature)) should be the identity function.
            let recovered_signature : SignatureRctBulletproofs = mc_util_serial::decode(&bytes).unwrap();
            assert_eq!(signature, recovered_signature);
        }

        #[test]
        // `verify` should accept valid signatures with correct fee.
        fn verify_with_fee(
            num_inputs in 2..8usize,
            num_mixins in 1..17usize,
            seed in any::<[u8; 32]>(),
        ) {
            let mut rng: StdRng = SeedableRng::from_seed(seed);
            let mut params = SignatureParams::random(num_inputs, num_mixins, &mut rng);
            // Remove one of the outputs, and use its value as the fee. This conserves value.
            let (fee, _) = params.output_values_and_blindings.pop().unwrap();

            let signature = params.sign(fee, &mut rng).unwrap();

            let result = signature.verify(
                &params.message,
                &params.rings,
                &params.get_output_commitments(),
                fee,
                params.token_id,
                &mut rng,
            );
            result.unwrap();

            // Verify should fail if the signature disagrees with the fee.
            let wrong_fee = fee + 1;
            match signature.verify(
                &params.message,
                &params.rings,
                &params.get_output_commitments(),
                wrong_fee,
                params.token_id,
                &mut rng,
            ) {
                Err(Error::ValueNotConserved) => {} // Expected
                Err(e) => {
                    panic!("Unexpected error {}", e);
                }
                _ => panic!("Unexpected success")
            }

        }

    } // end proptest
}
