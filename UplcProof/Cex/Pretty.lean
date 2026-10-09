/-!
# `UplcProof.Cex.Pretty`: z3 text to clean text

Blaster reports a counterexample as one entry per binder, `"<binder>: <z3 value>"`,
where the value is an SMT-LIB s-expression whose symbols are already Lean names
(`(PlutusCore.Data.PlutusCore.DataInternal.Data.I 5)`). Four kinds of z3 noise
separate it from a Lean term, all removed here, as pure text (no elaboration):

1. `(let ((a!1 v) …) body)`: z3's sharing; inlined (SMT-LIB `let` is parallel).
2. `(as List.nil (@List @T))`: type ascriptions; dropped.
3. `(- 3)`: negative numerals; become `-3` (parenthesised as an argument).
4. `"\u{c3}\u{bf}"`, `""""`: z3's string escapes; decoded, then re-escaped as a
   Lean string literal (`"\xc3\xbf"`, `"\""`).

`prettyFull` keeps the full names and is valid Lean: it is what `Bridge`
elaborates. `prettyCex` shortens the names for display and is *not* guaranteed
to be Lean (it is only shown as a comment when nothing elaborates). Malformed
input (unbalanced parentheses, an unterminated string) is an error, never a
guess.
-/

namespace UplcProof.Cex

/-- A z3 value as an s-expression. String literals are kept apart, decoded. -/
private inductive SExp where
  | atom (s : String)
  | str (s : String)
  | list (xs : List SExp)
deriving Inhabited, Repr, BEq

/-- Tokens of a z3 value. -/
private inductive Tok where
  | lp | rp
  | atom (s : String)
  | str (s : String)
deriving Inhabited, Repr, BEq

private def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def hexNum? (cs : List Char) : Option Nat :=
  if cs.isEmpty then none else
  cs.foldlM (fun acc c => (hexVal? c).map (acc * 16 + ·)) 0

/-- Reads the body of a z3 string literal (after the opening `"`), decoding
    `""` (an escaped quote, SMT-LIB 2.6), `\u{h…}` and `\uhhhh`. Returns the
    decoded string and the rest of the input. -/
private partial def readZ3String : List Char → String → Except String (String × List Char)
  | [], _ => .error "unterminated string literal"
  | '"' :: '"' :: rest, acc => readZ3String rest (acc.push '"')
  | '"' :: rest, acc => .ok (acc, rest)
  | '\\' :: 'u' :: '{' :: rest, acc =>
      let digits := rest.takeWhile (· != '}')
      let after := rest.drop (digits.length + 1)
      if digits.length == rest.length then .error "unterminated \\u{…} escape in a string literal"
      else match hexNum? digits with
        | some n => readZ3String after (acc.push (Char.ofNat n))
        | none => .error s!"bad \\u\{…} escape in a string literal: {String.mk digits}"
  | '\\' :: 'u' :: a :: b :: c :: d :: rest, acc =>
      match hexNum? [a, b, c, d] with
      | some n => readZ3String rest (acc.push (Char.ofNat n))
      | none => readZ3String (a :: b :: c :: d :: rest) (acc.push '\\' |>.push 'u')
  | c :: rest, acc => readZ3String rest (acc.push c)

/-- Reads a `|quoted symbol|` body (after the opening `|`). -/
private partial def readQuoted : List Char → String → Except String (String × List Char)
  | [], _ => .error "unterminated |quoted symbol|"
  | '|' :: rest, acc => .ok (acc, rest)
  | c :: rest, acc => readQuoted rest (acc.push c)

private def isSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-- Splits z3 text into tokens. -/
private partial def tokenize (cs : List Char) (cur : String := "") (acc : Array Tok := #[]) :
    Except String (Array Tok) :=
  let flush (acc : Array Tok) := if cur.isEmpty then acc else acc.push (.atom cur)
  match cs with
  | [] => .ok (flush acc)
  | c :: rest =>
    if c == '"' then do
      let (s, rest') ← readZ3String rest ""
      tokenize rest' "" ((flush acc).push (.str s))
    else if c == '|' && cur.isEmpty then do
      let (s, rest') ← readQuoted rest ""
      tokenize rest' "" ((flush acc).push (.atom s))
    else if c == '(' then tokenize rest "" ((flush acc).push .lp)
    else if c == ')' then tokenize rest "" ((flush acc).push .rp)
    else if isSpace c then tokenize rest "" (flush acc)
    else tokenize rest (cur.push c) acc

mutual
  /-- Parses one s-expression. -/
  private partial def parseOne : List Tok → Except String (SExp × List Tok)
    | .lp :: rest => parseSeq rest #[]
    | .rp :: _ => .error "unbalanced parentheses: unexpected `)`"
    | .atom a :: rest => .ok (.atom a, rest)
    | .str s :: rest => .ok (.str s, rest)
    | [] => .error "empty value"
  /-- Parses the elements of a list, up to its `)`. -/
  private partial def parseSeq : List Tok → Array SExp → Except String (SExp × List Tok)
    | .rp :: rest, acc => .ok (.list acc.toList, rest)
    | [], _ => .error "unbalanced parentheses: missing `)`"
    | toks, acc => do
      let (e, rest) ← parseOne toks
      parseSeq rest (acc.push e)
end

/-- Parses exactly one s-expression; anything left over is an error. -/
private def parseSExp (input : String) : Except String SExp := do
  let toks ← tokenize input.toList
  let (e, rest) ← parseOne toks.toList
  unless rest.isEmpty do
    throw (if rest.head? == some .rp then "unbalanced parentheses: unexpected `)`"
      else "more than one value")
  return e

/-- `true` for a decimal numeral (`12`, not `-1`). -/
private def isNumeral (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

/-- Inlines z3's `let`s (parallel, as SMT-LIB), drops `(as x T)` ascriptions and
    turns `(- n)` into the atom `-n`. -/
private partial def clean (env : List (String × SExp)) : SExp → SExp
  | .atom a => (env.lookup a).getD (.atom a)
  | .str s => .str s
  | .list [.atom "as", x, _ty] => clean env x
  | .list [.atom "let", .list binds, body] =>
      let new := binds.filterMap fun
        | .list [.atom name, val] => some (name, clean env val)
        | _ => none
      clean (new ++ env) body
  | .list [.atom "-", x] =>
      match clean env x with
      | .atom n => if isNumeral n then .atom ("-" ++ n) else .list [.atom "-", .atom n]
      | x' => .list [.atom "-", x']
  | .list xs => .list (xs.map (clean env))

private def hex2 (n : Nat) : String :=
  let d := fun (k : Nat) => "0123456789abcdef".get ⟨k⟩
  String.mk [d (n / 16 % 16), d (n % 16)]

private def hex4 (n : Nat) : String := hex2 (n / 256) ++ hex2 (n % 256)

/-- A Lean string literal for `s`: printable ASCII as is, `"` and `\` escaped,
    every other character below 256 as `\xhh` (a `ByteString` holds one byte per
    character), up to `0xffff` as `\uhhhh`, above that the character itself. -/
def leanStringLit (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    let n := c.toNat
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if 0x20 ≤ n ∧ n < 0x7f then out := out.push c
    else if n < 0x100 then out := out ++ "\\x" ++ hex2 n
    else if n ≤ 0xffff then out := out ++ "\\u" ++ hex4 n
    else out := out.push c
  return out ++ "\""

/-- Renders a cleaned s-expression as Lean text. `short` shortens names for
    display; `arg` parenthesises applications and negative numerals.
    `List.cons a (List.cons b List.nil)` becomes `[a, b]`, `Prod.mk a b`
    becomes `(a, b)`. -/
private partial def toLean (short : Bool) (arg : Bool) : SExp → String
  | .str s => leanStringLit s
  | .atom a =>
      if a.startsWith "-" && isNumeral (a.drop 1) then (if arg then s!"({a})" else a)
      else if a == "List.nil" then "[]"
      else name a
  | .list [] => "()"
  | .list [x] => toLean short arg x
  | e@(.list [.atom "List.cons", _, _]) =>
      match listElems e with
      | some xs => "[" ++ ", ".intercalate (xs.map (toLean short false)) ++ "]"
      | none => app e
  | .list [.atom "Prod.mk", a, b] => s!"({toLean short false a}, {toLean short false b})"
  | e => app e
where
  name (a : String) : String :=
    if !short then a else
    match a with
    | "Option.some" => "some"
    | "Option.none" => "none"
    | "Bool.true" => "true"
    | "Bool.false" => "false"
    | _ => match (a.splitOn ".").reverse with
      | last :: prev :: _ => if prev.isEmpty then a else prev ++ "." ++ last
      | _ => a
  listElems : SExp → Option (List SExp)
    | .atom "List.nil" => some []
    | .list [.atom "List.cons", x, xs] => (listElems xs).map (x :: ·)
    | _ => none
  app : SExp → String
    | .list (f :: xs) =>
        let s := " ".intercalate (toLean short true f :: xs.map (toLean short true))
        if arg then s!"({s})" else s
    | e => toLean short arg e

/-- z3 text to full-name Lean text, ready to elaborate. -/
def prettyFull (input : String) : Except String String := do
  return toLean false false (clean [] (← parseSExp input))

/-- z3 text to short readable text, for display only (not guaranteed Lean). -/
def prettyCex (input : String) : Except String String := do
  return toLean true false (clean [] (← parseSExp input))

/-- `true` if z3 gives no concrete value: a single atom `$n` (a variable the
    solver eliminated) or an abstract element `…!val!n` (`@@ArrowT2!val!0`, an
    unconstrained function). The binder is unconstrained: any value will do. -/
def isAbstractValue (raw : String) : Bool :=
  let r := raw.trim
  !r.isEmpty && !r.any (fun c => c == ' ' || c == '(' || c == ')' || c == '"') &&
    (r.startsWith "$" || (r.splitOn "!val!").length > 1)

/-- Splits one Blaster entry `"<binder>: <value>"` (tolerating surrounding
    whitespace, Blaster's trailing newline and a leading `- ` as in Blaster's own
    log) into the binder name and the raw value. -/
def splitEntry (entry : String) : Except String (String × String) := do
  let e := entry.trim
  let e := if e.startsWith "- " then (e.drop 2).trimLeft else e
  match e.splitOn ": " with
  | name :: rest@(_ :: _) =>
      let name := name.trim
      if name.isEmpty then throw s!"no binder name in counterexample entry {repr entry}"
      return (name, ": ".intercalate rest |>.trim)
  | _ => throw s!"counterexample entry {repr entry} is not of the form \"<binder>: <value>\""

end UplcProof.Cex
