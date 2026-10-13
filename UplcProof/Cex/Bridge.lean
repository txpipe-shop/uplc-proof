import Lean
import UplcProof.Cex.Pretty

/-!
# `UplcProof.Cex.Bridge`: clean text to a Lean value

`elabCexValue raw ty` cleans one raw z3 value with `prettyFull`, parses it as a
term and elaborates it at the binder's type `ty`, in the current file (its
`open`s, its namespace). The result is a closed `Expr`: no `sorry` (error
recovery is off), no holes, no error message logged on the way. Elaboration
leaves no messages and no info trees behind.

`elabValue` is the same for a term already parsed (`Render`'s round trip).
-/

open Lean Meta Elab Term

namespace UplcProof.Cex

/-- Parses `text` as a Lean term, in the current environment's syntax. -/
def parseTerm (text : String) : TermElabM Syntax := do
  match Parser.runParserCategory (← getEnv) `term text with
  | .ok stx => return stx
  | .error e => throwError "not a Lean term: {e}"

/-- Elaborates `stx` at `expectedType` to a closed value: no error recovery (no
    `sorry`), every hole solved, and an error logged during elaboration is an
    exception. Messages and info trees produced on the way are discarded. -/
def elabValue (stx : Syntax) (expectedType : Expr) : TermElabM Expr := do
  let saved := (← getThe Core.State).messages
  modifyThe Core.State fun s => { s with messages := {} }
  try
    withEnableInfoTree false do
      let e ← withoutErrToSorry <| withSynthesize <| elabTermEnsuringType stx expectedType
      let e ← instantiateMVars e
      let msgs := (← getThe Core.State).messages
      if msgs.hasErrors then
        let errs ← msgs.toList.filter (·.severity == .error) |>.mapM (·.toString)
        throwError "{"\n".intercalate (errs.map String.trim)}"
      if e.hasExprMVar || e.hasLevelMVar then
        throwError "the value has unsolved holes: {e}"
      if e.hasSyntheticSorry || e.hasSorry then
        throwError "the value contains `sorry`"
      return e
  finally
    modifyThe Core.State fun s => { s with messages := saved }

/-- Cleans the raw z3 value `raw` (`prettyFull`), parses and elaborates it at
    `expectedType`. Returns the value and the clean text it came from. Errors
    name what failed: the z3 text (ill-formed), the parse, or the elaboration. -/
def elabCexValue (raw : String) (expectedType : Expr) : TermElabM (Expr × String) := do
  let text ← match prettyFull raw with
    | .ok t => pure t
    | .error e => throwError "ill-formed counterexample text ({e}):{indentD raw}"
  let stx ← try parseTerm text catch ex =>
    throwError "the counterexample text does not parse as Lean ({ex.toMessageData}):{indentD text}"
  let v ← try elabValue stx expectedType catch ex =>
    throwError "the counterexample does not elaborate at type {expectedType}:{indentD text}\n{ex.toMessageData}"
  return (v, text)

end UplcProof.Cex
