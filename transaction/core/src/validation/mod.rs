// Copyright (c) 2018-2021 The MobileCoin Foundation

//! Validation routines for a MobileCoin transaction

mod error;
mod validate;

pub use error::{TransactionValidationError, TransactionValidationResult};
pub use validate::{validate, validate_signature, validate_tombstone};
