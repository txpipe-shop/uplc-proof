use aiken/fuzz

/// A spend is allowed when the vault is open or the signer is the owner.
pub fn can_spend(is_open: Bool, signer: ByteArray, owner: ByteArray) -> Bool {
  is_open || signer == owner
}

/// The owner can always spend.
test prop_owner_can_always_spend(args via fuzz.both(fuzz.bool(), fuzz.bytearray())) {
  let (is_open, owner) = args
  can_spend(is_open, owner, owner)
}

/// A wrong property: a stranger can never spend (false when the vault is open).
test prop_stranger_can_never_spend(
  args via fuzz.tuple3(fuzz.bool(), fuzz.bytearray(), fuzz.bytearray()),
) {
  let (is_open, signer, owner) = args
  if signer != owner {
    !can_spend(is_open, signer, owner)
  } else {
    True
  }
}

// ---- Each test body as a function of its inputs, for `aiken export` ----

pub fn prop_owner_can_always_spend_body(is_open: Bool, owner: ByteArray) -> Bool {
  can_spend(is_open, owner, owner)
}

pub fn prop_stranger_can_never_spend_body(
  is_open: Bool,
  signer: ByteArray,
  owner: ByteArray,
) -> Bool {
  if signer != owner {
    !can_spend(is_open, signer, owner)
  } else {
    True
  }
}
