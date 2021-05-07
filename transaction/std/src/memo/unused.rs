// Copyright (c) 2018-2021 The MobileCoin Foundation

//! Object for 0x0000 Unused memo type

use super::RegisteredMemoType;

/// A memo that the sender declined to use to convey any information.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct UnusedMemo;

impl RegisteredMemoType for UnusedMemo {
    const MEMO_TYPE_BYTES: [u8; 2] = [0x00, 0x00];
}

impl From<&[u8; 44]> for UnusedMemo {
    fn from(_: &[u8; 44]) -> Self {
        Self
    }
}

impl Into<[u8; 44]> for UnusedMemo {
    fn into(self) -> [u8; 44] {
        [0u8; 44]
    }
}
