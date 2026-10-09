# UPLC test fixtures

The functions of `../aiken/lib/fixtures.ak`, compiled to Plutus V3, one
single-CBOR-hex program per file: `check_signer`, `count_true`, `signed_by`,
`require_ref`, `same_data` and `same_refs` with aiken v1.1.24, the others with aiken
v1.1.21+42babe5 (in
[aiken-blaster-examples](https://github.com/txpipe-shop/aiken-blaster-examples),
then copied here). To regenerate:
`AIKEN=/path/to/aiken ../aiken/export.sh [fn ...]` (deterministic output for a
given aiken version).

`UplcProofTests/Induction/{Positive,Run}.lean` load them with `#import_uplc` (paths
relative to the package root; `UplcProofTests/Cex/{Positive,Negative}.lean` and
`UplcProofTests/Readme.lean` load `factorial.hex` too) and pass arguments as `Data` constants built with
`UplcProof.Encode`, in the order of the Aiken parameters: `int x`, `list xs`,
`bool b`, `bytes b`, `boolList bs`, `bytesList bs`. An `Int` result halts as
`VCon (.Integer i)`, a `List<Int>` result as `VCon (.ConstDataList [.I ..])`, a
`Bool` result as `VCon (.Bool b)`.

Aiken compiles each recursive function to an inlined first iteration whose
recursive call is `(λs. s s next) (λf λy. LOOP)`; in `LOOP` the call is `f f next'`.
An argument that changes at each call (an accumulator) is passed too
(`λf λy λacc. LOOP`); one that does not is captured.

| Fixture | Recursion | Tactic |
|---|---|---|
| `factorial`, `sum_to`, `countdown` | on `n : Int` down to 0 | proved |
| `power(b, e)` | on `e`; `b` captured by the loop | proved |
| `sum`, `product`, `alternating_sum`, `length`, `sum_squares`, `double_all` | on a list | proved |
| `sum_acc(xs, acc)`, `count_positive_acc`, `reverse_acc` | on a list, with an accumulator (`Int`, `List<Int>`) | proved (`generalizing acc`) |
| `last_or(xs, acc)` | on a list; the accumulator replaced by the head | proved (`generalizing acc`) |
| `factorial_acc(n, acc)` | on `n : Int`, with an accumulator | proved (`generalizing acc`) |
| `sum_acc_first(acc, xs)` | the accumulator before the list | refused (limitation) |
| `count_positive` | on a list, branching on `x > 0` | proved |
| `require_member(xs, x)` | `has(xs, x)` on a list, then `True` or `fail` | proved (`Halts` and `Fails`; also `uplc_run` on a known list) |
| `sum_if_positive(xs, t)` | `sum(xs)` if `t > 0`, else `fail` | proved (`Halts` and `Fails`; also `uplc_run` on a known list) |
| `fib`, `half` | on `n - 1` and `n - 2` (`half`: on `n - 2`) | proved (induction on pairs) |
| `tribonacci` | on `n - 1`, `n - 2` and `n - 3` | refused (limitation) |
| `even_or_fail` | on `n - 2`; fails for odd `n` | refused (limitation) |
| `sum_pairs` | on a list, two elements at a time | refused (limitation) |
| `check_signer(is_open, signer, owner)` | none; `Bool` and `ByteArray` parameters | `uplc_run` (`cases` on the `Bool`) |
| `signed_by(keys, key)` | on a `List<ByteArray>` | proved |
| `count_true(bs)` | on a `List<Bool>` (matches on each symbolic `Bool`) | refused (limitation); `#guard` runs only |
| `require_ref(r, expected)` | none; `if r == expected` on a record (`equalsData`) | `uplc_run`, `evalRun` (closed: decided; symbolic: split) |
| `same_data(a, b)` | none; `a == b` on `Data` as the result | `uplc_run`, `evalRun` |
| `same_refs(xs, ys)` | none; `==` on `List<Ref>` (`equalsData` of lists) | `uplc_run` |

`math_factorial.hex` (aiken-blaster-examples `verify/Scripts/math_factorial.hex`)
differs from `factorial.hex` only in the decrement's operand order
(`addInteger (-1) n` there, `addInteger n (-1)` here): it was built by another
compiler build (its aiken version is not recorded). The tests prove both.
