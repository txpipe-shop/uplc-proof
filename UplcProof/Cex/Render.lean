import Lean
import UplcProof.Cex.Pretty
import UplcProof.Cex.Bridge
import UplcProof.Cex.Value

/-!
# `UplcProof.Cex.Render`: a value as Lean text that elaborates back to it

The counterexample shown to the user is Lean source. That is
enforced by construction: `renderLean v ty` writes candidate texts for the value
`v`, from the most readable to the most explicit, and keeps the first one that,
parsed and elaborated at `ty` *in the current file* (its `open`s, its namespace),
is definitionally equal to `v`. A text that fails this round trip is never
returned. The candidates:

1. `short`: constructor names as short as the file's `open`s allow
   (`Data.Constr 0 [Data.I 5]`), structures with named fields
   (`{ txOutRefId := ⟨""⟩, txOutRefIdx := 3 }`), a `ByteString` as `⟨"…"⟩`,
   lists `[1, 2]`, pairs `(a, b)`, `some x`, negative numerals `-3`.
2. `dot`: the same with constructors written `.Constr 0 [.I 5]` (tried first when
   nothing in the file shortens the names).
3. `full`: fully qualified names, constructors applied positionally.
4. `source`: the text the value was elaborated from (the cleaned z3 text), when
   given.

A `ByteString` literal: `PlutusCore` has no hex literal syntax; a `ByteString` is
`structure ByteString where data : String`, one character per byte, so the
literal is the anonymous constructor `⟨"…"⟩` with bytes outside printable ASCII
as `\xhh` escapes (`⟨"\xde\xad\xbe\xef"⟩`). It elaborates to exactly the
`ByteString.mk "…"` value (no coercion, no computation), so `rfl` and `decide`
see it as it is.

No unexpander or delaborator is registered: how goals print in a file that
imports `UplcProof` does not change.
-/

open Lean Meta Elab Term

namespace UplcProof.Cex

/-- How constructor names are written. -/
private inductive Mode where
  | short | dot | full
deriving Inhabited, BEq, Repr

private def paren (arg : Bool) (f : Format) : Format := if arg then Format.paren f else f

/-- The text of constructor `c` (of inductive `I`) in `mode`. -/
private def ctorName (mode : Mode) (c I : Name) : MetaM String := do
  match mode with
  | .full => return c.toString
  | .dot => return "." ++ (c.replacePrefix I .anonymous).toString
  | .short => return (← unresolveNameGlobalAvoidingLocals c).toString

/-- Renders a `Val` as a `Format` (`arg`: in argument position). -/
private partial def fmtVal (mode : Mode) (arg : Bool) : Val → MetaM Format
  | .int i => return if i < 0 then paren arg (toString i) else toString i
  | .bool b => return toString b
  | .str s => return leanStringLit s
  | .bytes s =>
      if mode == .full then
        return paren arg (byteStringName.toString ++ ".mk " ++ leanStringLit s)
      else return "⟨" ++ leanStringLit s ++ "⟩"
  | .list xs => do
      let fs ← xs.mapM (fmtVal mode false)
      return Format.bracket "[" (Format.joinSep fs.toList ("," ++ Format.line)) "]"
  | .pair a b => do
      return Format.paren ((← fmtVal mode false a) ++ "," ++ Format.line ++ (← fmtVal mode false b))
  | .some v => do
      let s := if mode == .full then "Option.some" else "some"
      return paren arg (Format.group (Format.nest 2 (s ++ Format.line ++ (← fmtVal mode true v))))
  | .none => return if mode == .full then "Option.none" else "none"
  | .ctor c I fields struct => do
      if struct && mode != .full && !fields.isEmpty then
        let fs ← fields.mapM fun (n, v) => do
          return Format.group (Format.nest 2 (n.toString ++ " :=" ++ Format.line ++ (← fmtVal mode false v)))
        return Format.bracket "{ " (Format.joinSep fs.toList ("," ++ Format.line)) " }"
      let name ← ctorName mode c I
      if fields.isEmpty then return name
      let as ← fields.mapM fun (_, v) => fmtVal mode true v
      return paren arg (Format.group (Format.nest 2
        (name ++ Format.line ++ Format.joinSep as.toList Format.line)))
  | .opaque e => do
      let f ← withOptions (fun o => o.setBool `pp.fullNames (mode == .full)) (ppExpr e)
      return paren arg f

/-- One line, however long. -/
private def oneLine (f : Format) : String := f.pretty (width := 1000000000)

/-- Whether `text`, parsed and elaborated at `type`, is definitionally equal to
    `value`. Leaves no trace (state, messages, info trees). -/
def roundTrips (text : String) (type value : Expr) : TermElabM Bool := do
  let s ← saveState
  let hb ← IO.getNumHeartbeats
  -- runtime exceptions (heartbeats, recursion depth) count as a failed round trip
  let ok ← tryCatchRuntimeEx
    (do
      let stx ← parseTerm text
      let e ← elabValue stx type
      withCurrHeartbeats <| withNewMCtxDepth (isDefEq e value))
    fun _ => do IO.setNumHeartbeats hb; return false
  s.restore
  return ok

/-- A value's Lean text: `line` on one line, `pretty` laid out at width 100 for
    display (equal to `line` when short); both passed the round trip. -/
structure Rendered where
  line : String
  pretty : String
  /-- Which candidate won: `short`, `dot`, `full` or `source`. -/
  mode : String
deriving Inhabited, Repr

/-- The candidate texts for `v`, most readable first (see the module doc). -/
private def candidates (v : Val) (source? : Option String) : MetaM (Array (String × Format)) := do
  let short ← fmtVal .short false v
  let dot ← fmtVal .dot false v
  let full ← fmtVal .full false v
  let mut cs := if oneLine short == oneLine dot then #[("short", short), ("full", full)]
    else if oneLine short == oneLine full then #[("dot", dot), ("short", short), ("full", full)]
    else #[("short", short), ("dot", dot), ("full", full)]
  if let some src := source? then cs := cs.push ("source", (src : Format))
  -- drop duplicates
  let mut seen : Array String := #[]
  let mut out := #[]
  for (m, f) in cs do
    let l := oneLine f
    unless seen.contains l do
      seen := seen.push l
      out := out.push (m, f)
  return out

/-- Lean text for `value : type` that elaborates back to `value` in the current
    file, or `none` if no candidate does (then nothing may be shown as Lean).
    `source?`: the text `value` was elaborated from, the last resort. -/
def renderLean (value type : Expr) (source? : Option String := none) :
    TermElabM (Option Rendered) := do
  let v ← toVal value
  for (mode, f) in ← candidates v source? do
    let line := oneLine f
    if ← roundTrips line type value then
      let p := f.pretty (width := 100)
      let pretty ← if p == line then pure line
        else if ← roundTrips p type value then pure p else pure line
      return some { line, pretty, mode }
  return none

end UplcProof.Cex
