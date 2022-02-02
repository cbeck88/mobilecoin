//! Convert to/from external::CompressedProofOfOpening

use crate::{convert::ConversionError, external};
use mc_crypto_keys::CompressedRistrettoPublic;
use mc_transaction_core::{ring_signature::CurveScalar, CompressedProofOfOpening};
use std::convert::{TryFrom, TryInto};

impl From<&CompressedProofOfOpening> for external::CompressedProofOfOpening {
    fn from(source: &CompressedProofOfOpening) -> Self {
        let mut proof = external::CompressedProofOfOpening::new();

        proof.set_d((&source.d).into());
        proof.set_u((&source.u).into());
        proof.set_v((&source.v).into());

        proof
    }
}

impl TryFrom<&external::CompressedProofOfOpening> for CompressedProofOfOpening {
    type Error = ConversionError;

    fn try_from(source: &external::CompressedProofOfOpening) -> Result<Self, Self::Error> {
        let d: CompressedRistrettoPublic = source.get_d().try_into()?;
        let u: CurveScalar = source.get_u().try_into()?;
        let v: CurveScalar = source.get_v().try_into()?;

        Ok(CompressedProofOfOpening { d, u, v })
    }
}
