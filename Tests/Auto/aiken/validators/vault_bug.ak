use aiken/fuzz
use cardano/transaction.{OutputReference, Transaction}

pub type Datum {
  cap: Int,
}

/// The same vault with an off-by-one: it accepts one unit above the cap.
validator vault_bug {
  spend(datum: Option<Datum>, redeemer: Int, _own: OutputReference, _tx: Transaction) {
    expect Some(d) = datum
    redeemer - 1 <= d.cap
  }

  else(_) {
    fail
  }
}

/// Wrong (the bug); `aiken check` usually passes: its 100 random pairs hit
/// `amount = cap + 1` in about one run in five (8 of 40 seeds, aiken v1.1.24).
test prop_bug_accepts_only_up_to_cap(args via fuzz.both(fuzz.int(), fuzz.int())) {
  let (cap, amount) = args
  let ok =
    vault_bug.spend(Some(Datum { cap }), amount, OutputReference(#"00", 0), transaction.placeholder)
  if ok {
    amount <= cap
  } else {
    True
  }
}

// ---- The test body as a function of its inputs, for `aiken export` ----

pub fn prop_bug_accepts_only_up_to_cap_body(cap: Int, amount: Int) -> Bool {
  let ok =
    vault_bug.spend(Some(Datum { cap }), amount, OutputReference(#"00", 0), transaction.placeholder)
  if ok {
    amount <= cap
  } else {
    True
  }
}
