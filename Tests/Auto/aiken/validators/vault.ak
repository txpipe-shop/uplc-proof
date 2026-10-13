use aiken/fuzz
use cardano/transaction.{OutputReference, Transaction}

pub type Datum {
  cap: Int,
}

/// A vault: a withdrawal (the redeemer) is allowed up to the `cap` of its datum.
validator vault {
  spend(datum: Option<Datum>, redeemer: Int, _own: OutputReference, _tx: Transaction) {
    expect Some(d) = datum
    redeemer <= d.cap
  }

  else(_) {
    fail
  }
}

/// The property: the vault accepts a withdrawal only up to its cap.
test prop_accepts_only_up_to_cap(args via fuzz.both(fuzz.int(), fuzz.int())) {
  let (cap, amount) = args
  let ok =
    vault.spend(Some(Datum { cap }), amount, OutputReference(#"00", 0), transaction.placeholder)
  if ok {
    amount <= cap
  } else {
    True
  }
}

// ---- The test body as a function of its inputs, for `aiken export` ----

pub fn prop_accepts_only_up_to_cap_body(cap: Int, amount: Int) -> Bool {
  let ok =
    vault.spend(Some(Datum { cap }), amount, OutputReference(#"00", 0), transaction.placeholder)
  if ok {
    amount <= cap
  } else {
    True
  }
}
