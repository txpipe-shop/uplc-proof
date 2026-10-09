import Lean
import UplcProof.Cex.Pretty
import UplcProof.Cex.Render
import UplcProof.Cex.Json

/-!
# `UplcProof.Cex.Report`: the message tools and `uplc_auto` read

The contract (documented in `UplcProof.Cex`): the first line of the message is

```
UPLC-RESULT {"status":…,"kernel":…,"cex":{name: json},"lean":{name: "lean text"}}
```

one line of valid JSON, keys in that order, possibly followed by more keys
(`"closer"`, `"defaults"`, `"reason"`, `"ms"`); then human-readable lines: the
counterexample as `name := <lean>` lines and the refutation as a ready-to-paste
Lean snippet.
-/

open Lean Meta Elab Term

namespace UplcProof.Cex

register_option uplc.cex.timings : Bool := {
  defValue := true
  descr := "include timings (key \"ms\", in milliseconds) in the UPLC-RESULT line"
}

/-- The outcome. -/
inductive Status where
  /-- Blaster found a model and a refutation built from it was checked by the kernel. -/
  | refuted
  /-- Blaster found a model, but no kernel-checked refutation could be built from it. -/
  | falsified
  /-- Blaster says the goal holds; there is no kernel proof. -/
  | oracle
  /-- Blaster could not decide, or failed. -/
  | unknown
deriving Inhabited, BEq, Repr

/-- The status as it appears in the `UPLC-RESULT` line (`"refuted"`, …). -/
def Status.toString : Status → String
  | .refuted => "refuted"
  | .falsified => "falsified"
  | .oracle => "oracle"
  | .unknown => "unknown"

instance : ToString Status := ⟨Status.toString⟩

/-- One binder of the counterexample. -/
structure Entry where
  name : String
  json : Json := .null
  /-- The Lean text (round-trip checked), if one elaborates back to the value. -/
  lean? : Option Rendered := none
  /-- z3's own text, cleaned (display only, when there is no Lean text). -/
  z3? : Option String := none
  /-- E.g. why a default value was used. -/
  note? : Option String := none
  /-- Blaster's model has no concrete value for the binder (it leaves it out, or
      gives an abstract value): a default value was used. -/
  isDefault : Bool := false
deriving Inhabited

/-- Everything the message says. -/
structure Report where
  status : Status
  kernel : Bool := false
  entries : Array Entry := #[]
  /-- The Lean text of the refuted proposition `¬ S`, when it re-elaborates. -/
  negation? : Option String := none
  /-- The closer that refuted the conclusion. -/
  closer? : Option String := none
  /-- Why there is no kernel-checked refutation (status `falsified`), or why
      Blaster failed (status `unknown`). -/
  reason? : Option String := none
  /-- Milliseconds per phase. -/
  timings : Array (String × Nat) := #[]
deriving Inhabited

/-- `s` as a JSON string (quoted, escaped). -/
def jsonStr (s : String) : String := (Json.str s).compress

/-- The JSON object `{k₁:v₁,…}`, the values already JSON text, the keys in the
    given order (the caller keeps them distinct). -/
def jsonObj (kvs : List (String × String)) : String :=
  "{" ++ ",".intercalate (kvs.map fun (k, v) => jsonStr k ++ ":" ++ v) ++ "}"

/-- The names made distinct, in order: a name already used gets `_1`, `_2`, …
    appended (the first suffix not used yet). The keys of `"cex"`, `"lean"` and
    `uplc_auto`'s `"spurious"`. -/
def distinctNames (names : Array String) : Array String := Id.run do
  let mut used : Array String := #[]
  for base in names do
    let mut name := base
    let mut i := 1
    while used.contains name do
      name := s!"{base}_{i}"
      i := i + 1
    used := used.push name
  return used

/-- The `UPLC-RESULT {…}` line. -/
def Report.resultLine (r : Report) (timings : Bool := true) : String := Id.run do
  let mut kvs : List (String × String) := [
    ("status", jsonStr r.status.toString),
    ("kernel", toString r.kernel),
    ("cex", jsonObj (r.entries.toList.map fun e => (e.name, e.json.compress))),
    ("lean", jsonObj (r.entries.toList.map fun e =>
      (e.name, match e.lean? with | some l => jsonStr l.line | none => "null")))]
  if let some c := r.closer? then kvs := kvs ++ [("closer", jsonStr c)]
  let defaults := r.entries.filter (·.isDefault) |>.map (jsonStr ·.name)
  unless defaults.isEmpty do kvs := kvs ++ [("defaults", "[" ++ ",".intercalate defaults.toList ++ "]")]
  if let some why := r.reason? then kvs := kvs ++ [("reason", jsonStr why)]
  if timings && !r.timings.isEmpty then
    kvs := kvs ++ [("ms", jsonObj (r.timings.toList.map fun (k, v) => (k, toString v)))]
  return "UPLC-RESULT " ++ jsonObj kvs

private def indentRest (s : String) (n : Nat) : String :=
  let pad := "".pushn ' ' n
  "\n".intercalate <| match s.splitOn "\n" with
    | [] => []
    | l :: ls => l :: ls.map (pad ++ ·)

/-- The `name := <lean>` lines. -/
def Report.cexLines (r : Report) : List String :=
  r.entries.toList.map fun e =>
    match e.lean? with
    | some l =>
        let note := match e.note? with | some n => s!"  -- {n}" | none => ""
        s!"  {e.name} := {indentRest l.pretty (e.name.length + 6)}{note}"
    | none =>
        let z3 := match e.z3? with | some t => s!"; z3 gave: {t}" | none => ""
        s!"  -- {e.name}: no Lean term elaborates to this value{z3}"

/-- The ready-to-paste refutation, if every value has Lean text. -/
def Report.snippet? (r : Report) : Option String := do
  let neg ← r.negation?
  let vals ← r.entries.mapM (·.lean?.map (·.line))
  let tac := if vals.isEmpty then "refute_with" else "refute_with " ++ ", ".intercalate vals.toList
  return s!"example : {indentRest neg 4} := by\n  {tac}"

/-- The whole message: the `UPLC-RESULT` line, then the human-readable lines. -/
def Report.message (r : Report) (timings : Bool := true) : String := Id.run do
  let mut ls := [r.resultLine timings]
  match r.status with
  | .refuted =>
      let how := match r.closer? with | some c => s!", closer {c}" | none => ""
      ls := ls ++ [s!"Counterexample (refutation checked by the kernel{how}):"] ++ r.cexLines
      if let some s := r.snippet? then ls := ls ++ ["Refutation:", s]
  | .falsified =>
      ls := ls ++ ["Counterexample from Blaster, NOT confirmed: no kernel-checked refutation \
        could be built from it."] ++ r.cexLines
      if let some why := r.reason? then ls := ls ++ [s!"Why: {why}"]
      if let some s := r.snippet? then ls := ls ++ ["Attempted refutation:", s]
  | .oracle =>
      ls := ls ++ ["Blaster (z3) says the goal holds. There is no kernel proof: the goal is \
        closed with the axiom Blaster.Tactic.blasterProven."]
  | .unknown =>
      ls := ls ++ ["Blaster could not decide the goal."]
      if let some why := r.reason? then ls := ls ++ [s!"Why: {why}"]
  return "\n".intercalate ls

/-- The entry for binder `name` with value `value : type` (in the current local
    context): its JSON (`jsonOf`) and its Lean text (`renderLean`, round-trip
    checked; `source?`, the text the value came from, is the last resort). -/
def mkEntry (name : String) (value type : Expr) (source? : Option String := none)
    (z3? : Option String := none) (note? : Option String := none) (isDefault := false) :
    TermElabM Entry := do
  return { name, json := ← jsonOf value type, lean? := ← renderLean value type source?,
           z3?, note?, isDefault }

/-- Lean text for the proposition `p` that elaborates back to it (`pp` as is,
    then with full names), or `none`. -/
def renderProp (p : Expr) : TermElabM (Option String) := do
  for full in [false, true] do
    let f ← withOptions (fun o => o.setBool `pp.fullNames full) (ppExpr p)
    let text := f.pretty (width := 100)
    if ← roundTrips text (mkSort .zero) p then return some text
  return none

end UplcProof.Cex
