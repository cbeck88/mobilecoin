// Copyright (c) 2018-2022 The MobileCoin Foundation

//! Validation routines for a MobileCoin transaction

mod error;
mod validate;

pub use self::{
    error::{TransactionValidationError, TransactionValidationResult},
    validate::{
        validate, validate_all_input_rules, validate_inputs_are_sorted,
        validate_outputs_are_sorted, validate_ring_elements_are_sorted, validate_signature,
        validate_tombstone, validate_tx_out,
    },
};
