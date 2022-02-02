//! Code related to zero knowledge "proof of opening" for a Pedersen Commitment
//!
//! TODO: Add appropriate references
//! (Page 27): https://www.cs.purdue.edu/homes/ninghui/courses/555_Spring12/handouts/555_Spring12_topic23.pdf

use crate::{
    domain_separators::{PROOF_OF_OPENING_PUBLIC_DOMAIN_TAG, PROOF_OF_OPENING_SECRET_DOMAIN_TAG},
    ring_signature::{CurveScalar, PedersenGens},
    Commitment,
};
use core::convert::TryFrom;
use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
};
use mc_crypto_digestible::{Digestible, MerlinTranscript};
use mc_crypto_keys::CompressedRistrettoPublic;
use prost::Message;
use serde::{Deserialize, Serialize};

/// This object is the transcript of a non-interactive "proof of opening"
/// for a Pedersen commitment (c = g^x h^r).
/// This transcript convinces a verifier that the
/// prover is capable of opening a Pedersen commitment, without revealing the
/// commitment in the process.
///
/// The proof may be verified relative to the target commitment.
#[derive(Copy, Clone, Default, Digestible)]
pub struct ProofOfOpening {
    /// A commitment to the prover's secret blinding values (d = g^y h^s)
    d: RistrettoPoint,
    /// A blinded version of the value of the target commitment
    /// (u = y + ex)
    u: Scalar,
    /// A blinded version of the blinding factor of the target commitment
    /// (v = s + er)
    v: Scalar,
}

impl ProofOfOpening {
    /// Create a new Proof of Opening, given the parameters to the target
    /// commitment.
    ///
    /// Argumets:
    /// * value: The 64-bit value being committed to
    /// * blinding: The blinding factor for the commitment
    /// * gens: The pedersen generators for the commitment
    ///
    /// Returns:
    /// * A proof of opening, which is like a digital signature which can be
    ///   verified relative to the commitment and the generators.
    pub fn new(value: Scalar, blinding: Scalar, gens: &PedersenGens) -> Self {
        let target_commitment = gens.commit(value, blinding);
        Self::new_with_target_commitment(value, blinding, gens, &target_commitment)
    }

    /// This is a faster version of new, if you have already built the
    /// target_commitment from its parameters.
    ///
    /// Argumets:
    /// * value: The 64-bit value being committed to
    /// * blinding: The blinding factor for the commitment
    /// * gens: The pedersen generators for the commitment
    /// * target_commitment: The pre-computed target_commitment, which must be
    ///   equal to gens.commit(Scalar::from(value), blinding)
    ///
    /// Returns:
    /// * A proof of opening, which is like a digital signature which can be
    ///   verified relative to the commitment and the generators.
    pub fn new_with_target_commitment(
        value: Scalar,
        blinding: Scalar,
        gens: &PedersenGens,
        target_commitment: &RistrettoPoint,
    ) -> Self {
        debug_assert!(
            target_commitment.clone() == gens.commit(value, blinding),
            "bad target commitment was passed"
        );

        // Compute prover secrets y and s, and the commitment based on these.
        //
        // These are unpredictable assuming that the blinding factor is unpredictable
        // and that Merlin adequately implements Fiat Shamir.
        let (y, s) = {
            let mut transcript =
                MerlinTranscript::new(PROOF_OF_OPENING_SECRET_DOMAIN_TAG.as_bytes());
            value.append_to_transcript(b"x", &mut transcript);
            blinding.append_to_transcript(b"r", &mut transcript);

            let mut y_bytes = [0u8; 32];
            let mut s_bytes = [0u8; 32];

            transcript.challenge_bytes(b"y", &mut y_bytes);
            transcript.challenge_bytes(b"s", &mut s_bytes);

            (Scalar::from_bits(y_bytes), Scalar::from_bits(s_bytes))
        };

        // Compute prover's commitment to these
        let d = gens.commit(y, s);

        // Make the challenge value "e" based on the transcript the verifier can see
        let e = Self::compute_challenge_value(&target_commitment, &d);

        let x = value;
        let r = blinding;

        // Compute "blinded" values u, v which the prover sends.
        let u = y + (e * x);
        let v = s + (e * r);

        let result = Self { d, u, v };
        debug_assert!(result.verify(target_commitment, gens));
        result
    }

    /// Verify the proof of opening relative to the target commitment, and
    /// generators it is based on.
    ///
    /// This checks the equation
    /// d * c^e = g^u h^v mod p (in the multiplicative notation),
    /// or in the additive notation, `d + e * c = u * g + v * h`
    pub fn verify(&self, target_commitment: &RistrettoPoint, gens: &PedersenGens) -> bool {
        // Make the challenge value "e" based on the transcript the verifier can see
        let e = Self::compute_challenge_value(target_commitment, &self.d);

        // Check the verification equation
        (self.d + (e * target_commitment)) == gens.commit(self.u, self.v)
    }

    /// Same as verify but takes a Commitment object for convenience
    pub fn verify_commitment(&self, target_commitment: &Commitment, gens: &PedersenGens) -> bool {
        self.verify(&target_commitment.point, gens)
    }

    /// This computes the challenge value `e` using Fiat-Shamir heuristic.
    ///
    /// The data visible to verifier at this point in the protocol are, the
    /// target commitment, and the prover's commitment (to y and s), which
    /// is defined `d = g^y h^s`.
    ///
    /// Note: We could hash additional stuff into the transcript, or take the
    /// transcript as a parameter, if we wanted to make this more like the
    /// Schnorrkel API for digital signatures. But we don't have a use-case
    /// for that right now.
    fn compute_challenge_value(
        target_commitment: &RistrettoPoint,
        prover_commitment: &RistrettoPoint,
    ) -> Scalar {
        let mut transcript = MerlinTranscript::new(PROOF_OF_OPENING_PUBLIC_DOMAIN_TAG.as_bytes());
        target_commitment.append_to_transcript(b"c", &mut transcript);
        prover_commitment.append_to_transcript(b"d", &mut transcript);

        let mut e_bytes = [0u8; 32];
        transcript.challenge_bytes(b"e", &mut e_bytes);
        Scalar::from_bits(e_bytes)
    }
}

/// A compressed form of the ProofOfOpening suitable for serialization
#[derive(Clone, Eq, PartialEq, Serialize, Deserialize, Digestible, Message)]
pub struct CompressedProofOfOpening {
    /// A commitment to the prover's secret blinding values (d = g^y h^s)
    #[prost(message, required, tag = "1")]
    pub d: CompressedRistrettoPublic,
    /// A blinded version of the value of the target commitment
    /// (u = y + ex)
    #[prost(message, required, tag = "2")]
    pub u: CurveScalar,
    /// A blinded version of the blinding factor of the target commitment
    /// (v = s + er)
    #[prost(message, required, tag = "3")]
    pub v: CurveScalar,
}

impl From<&ProofOfOpening> for CompressedProofOfOpening {
    fn from(src: &ProofOfOpening) -> Self {
        Self {
            d: src.d.into(),
            u: (src.u).into(),
            v: (src.v).into(),
        }
    }
}

impl TryFrom<&CompressedProofOfOpening> for ProofOfOpening {
    type Error = crate::ring_signature::Error;

    fn try_from(src: &CompressedProofOfOpening) -> Result<Self, Self::Error> {
        let compressed: &CompressedRistretto = src.d.as_ref();
        let point = compressed
            .decompress()
            .ok_or(Self::Error::InvalidCurvePoint)?;
        Ok(Self {
            d: point,
            u: src.u.scalar,
            v: src.v.scalar,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ring_signature::generators;
    use proptest::prelude::*;
    use rand::{rngs::StdRng, CryptoRng, SeedableRng};
    use rand_core::RngCore;

    struct ProofOfOpeningParams {
        pub value: Scalar,
        pub blinding: Scalar,
        pub generator: PedersenGens,
        pub commitment: Commitment,
    }

    impl ProofOfOpeningParams {
        fn random<RNG: RngCore + CryptoRng>(rng: &mut RNG) -> Self {
            let value = rng.next_u64();
            let blinding = Scalar::random(rng);
            let generator = generators(rng.next_u32());
            let commitment = Commitment::new(value, blinding, &generator);

            Self {
                value: Scalar::from(value),
                blinding,
                generator,
                commitment,
            }
        }

        fn build(&self) -> ProofOfOpening {
            ProofOfOpening::new(self.value, self.blinding, &self.generator)
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(6))]

        // test that verification succeeds when expected, for random inputs
        #[test]
        fn test_verification_expected_success(
            seed in any::<[u8; 32]>(),
        ) {
            let mut rng: StdRng = SeedableRng::from_seed(seed);

            let params = ProofOfOpeningParams::random(&mut rng);
            let proof = params.build();

            // Test expected success case
            assert!(proof.verify_commitment(&params.commitment, &params.generator));

            // Test expected failures
            let other = ProofOfOpeningParams::random(&mut rng);
            assert!(!proof.verify_commitment(&other.commitment, &params.generator));
            assert!(!proof.verify_commitment(&params.commitment, &other.generator));
            assert!(!proof.verify_commitment(&other.commitment, &other.generator));
        }

        // test that verification succeeds when expected, for random inputs,
        // after round-tripping through compressed proof of opening
        #[test]
        fn test_verification_round_trip_expected_success(
            seed in any::<[u8; 32]>(),
        ) {
            let mut rng: StdRng = SeedableRng::from_seed(seed);

            let params = ProofOfOpeningParams::random(&mut rng);
            let proof = params.build();
            let proof = CompressedProofOfOpening::from(&proof);
            let proof = ProofOfOpening::try_from(&proof).unwrap();

            // Test expected success case
            assert!(proof.verify_commitment(&params.commitment, &params.generator));

            // Test expected failures
            let other = ProofOfOpeningParams::random(&mut rng);
            assert!(!proof.verify_commitment(&other.commitment, &params.generator));
            assert!(!proof.verify_commitment(&params.commitment, &other.generator));
            assert!(!proof.verify_commitment(&other.commitment, &other.generator));
        }

    } // proptest
}
