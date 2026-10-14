import NLAlib
open Lean Elab Command Meta

/-! # Data for the explore site

Writes the JSON the `explore` website (nla-lib.org/explore) is generated from: every module of
the library with its docstring and direct library imports, and every public declaration declared
in a library module (including `NLAlib.ForMathlib.*`, whose declarations live in Mathlib's
namespaces) with its kind, source range, docstring, pretty-printed signature, source statement,
library dependencies of its type and of its value, and whether it depends on `sorryAx`.

Run from the repository root after `lake build NLAlib`:
`lake env lean -M 8000 scripts/Explore.lean`. The output path is `$EXPLORE_OUT`, default
`explore-data.json`. `scripts/explore_data.sh` wraps it and stamps the commit.

Not part of the library: structure constructors and projections, recursors, equation lemmas,
matchers, `_proof_N` and other auxiliary constants, private declarations, and instances that have
neither a docstring nor a user-chosen name (`instFoo…`). References to constructors,
projections, recursors, equation lemmas and matchers count as references to their parent; the
other excluded constants are expanded into whatever they themselves reference. -/

/-! The scope the signatures are printed in: names under these namespaces print short, and the
scoped notation the library uses prints as notation. -/
open NLAlib Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder MatrixOrder ENNReal NNReal Real Topology Kronecker
set_option pp.unicode.fun true
set_option format.width 100
set_option maxHeartbeats 0

namespace NLAlib.Explore

/-- Name components Lean generates for inductives, structures and definitions. -/
def generatedSuffixes : List String :=
  ["rec", "recOn", "casesOn", "below", "ibelow", "brecOn", "binductionOn", "noConfusion",
    "noConfusionType", "ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType", "inj", "injEq",
    "sizeOf_spec", "congr_simp", "proxyType", "proxyTypeEquiv", "induct", "mutual_induct",
    "induct_unfolding", "fun_cases", "eq_def", "eq_unfold"]

/-- The library's modules, indexed by module index (`none` for other modules). Looking this up
is much faster in the interpreter than going through `env.header` for every constant. -/
def libModules (env : Environment) : Array (Option Name) :=
  env.header.moduleNames.map fun m => if (`NLAlib).isPrefixOf m then some m else none

/-- The module a constant was declared in, if it is a library module. -/
def libModule? (env : Environment) (lib : Array (Option Name)) (n : Name) : Option Name := do
  let i ← env.getModuleIdxFor? n
  lib[i.toNat]?.getD none

/-- The declaration a generated constant belongs to: the inductive of a constructor, the
structure of a projection, the prefix of a recursor, equation lemma, matcher or other generated
name. `none` for a constant that is not generated from another. -/
def structuralParent? (env : Environment) (n : Name) : Option Name :=
  match env.find? n with
  | some (.ctorInfo c) => some c.induct
  | some (.recInfo _) => some n.getPrefix
  | _ =>
    if let some p := env.getProjectionFnInfo? n then
      match env.find? p.ctorName with
      | some (.ctorInfo c) => some c.induct
      | _ => some n.getPrefix
    else if isAuxRecursor env n || isNoConfusion env n || Meta.isMatcherCore env n then
      some n.getPrefix
    else match n with
      | .str p s =>
        if generatedSuffixes.contains s || Meta.isEqnReservedNameSuffix s then some p else none
      | _ => none

/-- Whether a library constant is an auxiliary one that is never shown. -/
def isAuxiliary (env : Environment) (n : Name) : Bool :=
  isPrivateName n || n.isInternal || n.isInternalDetail || (structuralParent? env n).isSome

/-- The constants an inductive's definition mentions: its constructors' types. -/
def ctorTypes (env : Environment) (ctors : List Name) : Array Expr :=
  ctors.toArray.filterMap fun c => (env.find? c).map (·.type)

/-- The expressions making up the "value" of a constant: the body of a definition or theorem,
the constructor types of an inductive, nothing for an axiom. -/
def valueExprs (env : Environment) : ConstantInfo → Array Expr
  | .defnInfo d => #[d.value]
  | .thmInfo t => #[t.value]
  | .opaqueInfo o => #[o.value]
  | .inductInfo i => ctorTypes env i.ctors
  | _ => #[]

/-- Constants used in any of the expressions (each listed once per expression). -/
def usedIn (es : Array Expr) : Array Name :=
  es.foldl (fun s e => s ++ e.getUsedConstants) #[]

/-- What the extractor needs to know about the environment. -/
structure Ctx where
  env : Environment
  /-- `libModules env`. -/
  lib : Array (Option Name)
  /-- The constants that are entries of `decls`. -/
  decls : NameSet

/-- The shown declarations a reference to `n` stands for: `n` itself if shown, the parent of a
generated constant, and the expansion of an auxiliary one (cached; cycles cut). -/
partial def resolve (c : Ctx) (n : Name) : StateM (Std.HashMap Name NameSet) NameSet := do
  if c.decls.contains n then return ({} : NameSet).insert n
  if (libModule? c.env c.lib n).isNone then
    -- equation lemmas of public definitions may carry private names that are not in `env`
    if isPrivateName n && (c.env.find? n).isNone then
      if let some u := privateToUserName? n then return ← resolve c u
    return {}
  let some ci := c.env.find? n | return {}
  if let some s := (← get)[n]? then return s
  modify (·.insert n {})
  let r ← match structuralParent? c.env n with
    | some p => resolve c p
    | none =>
      let mut acc : NameSet := {}
      for u in usedIn (#[ci.type] ++ valueExprs c.env ci) do
        if u != n then
          for d in ← resolve c u do acc := acc.insert d
      pure acc
  modify (·.insert n r)
  return r

/-- Whether `sorryAx` is reachable from `n` through library constants (cached). -/
partial def hasSorry (env : Environment) (lib : Array (Option Name)) (n : Name) :
    StateM (Std.HashMap Name Bool) Bool := do
  if let some b := (← get)[n]? then return b
  modify (·.insert n false)
  let some ci := env.find? n | return false
  let mut r := false
  for u in usedIn (#[ci.type] ++ valueExprs env ci) do
    if u == ``sorryAx then r := true; break
    if (libModule? env lib u).isSome && u != n then
      if ← hasSorry env lib u then r := true; break
  modify (·.insert n r)
  return r

/-- Resolve the references in some expressions to sorted shown declarations, minus `self`. -/
def depsOf (c : Ctx) (self : Name) (es : Array Expr) :
    StateM (Std.HashMap Name NameSet) (Array Name) := do
  let mut out : NameSet := {}
  for u in usedIn es do
    for d in ← resolve c u do
      out := out.insert d
  return (out.erase self).toArray.qsort (·.toString < ·.toString)

/-- The `kind` field. -/
def kind (env : Environment) (n : Name) (isInst : Bool) (ci : ConstantInfo) : String :=
  if isInst then "instance" else
  match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo d => if d.hints.isAbbrev then "abbrev" else "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ =>
    if isClass env n then "class" else if isStructure env n then "structure" else "inductive"
  | _ => "other"

/-! ## The statement as written -/

def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '.' || c == '!' || c == '?' || c.toNat > 127

def openers : List Char := ['(', '[', '{', '⦃', '⟨', '⟦', '⟪', '⁅']
def closers : List Char := [')', ']', '}', '⦄', '⟩', '⟧', '⟫', '⁆']

/-- The index just past the block comment opening at `i` (comments nest). -/
partial def skipComment (s : Array Char) (i : Nat) (depth : Nat := 0) : Nat :=
  if i + 1 ≥ s.size then s.size
  else if s[i]! == '/' && s[i+1]! == '-' then skipComment s (i + 2) (depth + 1)
  else if s[i]! == '-' && s[i+1]! == '/' then
    if depth ≤ 1 then i + 2 else skipComment s (i + 2) (depth - 1)
  else skipComment s (i + 1) depth

/-- Whether the characters at `i` are `pat`. -/
def matchAt (s : Array Char) (i : Nat) (pat : String) : Bool :=
  let p := pat.toList.toArray
  (List.range p.size).all fun k => s[i + k]? == p[k]?

/-- Whether `i` is the first non-blank character of its line. -/
def firstOnLine (s : Array Char) (i : Nat) : Bool := Id.run do
  let mut j := i
  while j > 0 do
    j := j - 1
    if s[j]! == '\n' then return true
    if s[j]! != ' ' && s[j]! != '\t' then return false
  return true

/-- Whether the rest of the line from `i` contains `=>`. -/
def lineHasArrow (s : Array Char) (i : Nat) : Bool := Id.run do
  let mut j := i
  while j + 1 < s.size && s[j]! != '\n' do
    if s[j]! == '=' && s[j+1]! == '>' then return true
    j := j + 1
  return false

/-- The index where the body starts: the first `:=`, `where`, or pattern-matching `|` outside
brackets, comments and strings. -/
def bodyStart? (s : Array Char) (start : Nat) (isInductive : Bool) : Option Nat := Id.run do
  let mut i := start
  let mut depth : Nat := 0
  while i < s.size do
    let c := s[i]!
    if matchAt s i "--" then
      while i < s.size && s[i]! != '\n' do i := i + 1
    else if matchAt s i "/-" then
      i := skipComment s i
    else if c == '"' then
      i := i + 1
      while i < s.size && s[i]! != '"' do
        i := i + (if s[i]! == '\\' then 2 else 1)
      i := i + 1
    else if openers.contains c then
      depth := depth + 1; i := i + 1
    else if closers.contains c then
      depth := depth - 1; i := i + 1
    else if depth == 0 && matchAt s i ":=" then
      return some i
    else if depth == 0 && matchAt s i "where" && (i == 0 || !isIdentChar s[i-1]!) &&
        !(s[i+5]?.map isIdentChar |>.getD false) then
      return some i
    else if depth == 0 && c == '|' && firstOnLine s i && (isInductive || lineHasArrow s i) then
      return some i
    else
      i := i + 1
  return none

/-- The characters of `lines` from `(line, col)` to `(endLine, endCol)`, 1-based lines and
codepoint columns. -/
def rangeChars (lines : Array String) (p e : Position) : Array Char := Id.run do
  let mut out : Array Char := #[]
  for l in [p.line:e.line + 1] do
    let cs := (lines[l - 1]?.getD "").toList.toArray
    let a := if l == p.line then p.column else 0
    let b := if l == e.line then min e.column cs.size else cs.size
    out := out ++ cs.extract a b
    if l != e.line then out := out.push '\n'
  return out

/-- Words a declaration's source can start with once the docstring is skipped. -/
def leadingWords : List String :=
  ["@[", "private", "protected", "public", "noncomputable", "nonrec", "partial", "unsafe",
    "theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive", "opaque",
    "axiom", "irreducible_def", "scoped", "local", "alias"]

/-- The source of a declaration from its first modifier after the docstring up to its body.
`none` when the range is not a declaration's source (a constant generated by an attribute, such
as an `ext_iff` lemma, has the attribute's range). -/
def statement (lines : Array String) (r : DeclarationRange) (isInductive : Bool) :
    Option String :=
  let s := rangeChars lines r.pos r.endPos
  let skipWs (i : Nat) : Nat := Id.run do
    let mut j := i
    while j < s.size && s[j]!.isWhitespace do j := j + 1
    return j
  let i := skipWs 0
  let i := if matchAt s i "/--" then skipWs (skipComment s i) else i
  let txt (j : Nat) := (String.ofList (s.extract i j).toList).trimAsciiEnd.toString
  if !leadingWords.any (matchAt s i ·) then none else
  match bodyStart? s i isInductive with
  | some j => some (txt j)
  | none => some ((txt s.size).take 3000).toString

end NLAlib.Explore

open NLAlib.Explore in
run_cmd do
  let env ← getEnv
  -- the library's modules
  let mods := (env.header.moduleNames.filter (`NLAlib).isPrefixOf).qsort
    (·.toString < ·.toString)
  let mut modJson : Array Json := #[]
  for m in mods do
    let idx := (env.getModuleIdx? m).get!
    let imports := env.header.moduleData[idx.toNat]!.imports.map (·.module)
      |>.filter (`NLAlib).isPrefixOf |>.qsort (·.toString < ·.toString)
    let doc := (getModuleDoc? env m).bind (·[0]?) |>.map (·.doc.trimAscii.toString)
    modJson := modJson.push <| Json.mkObj [
      ("name", toString m),
      ("path", "/".intercalate (m.components.map toString) ++ ".lean"),
      ("doc", toJson doc),
      ("imports", toJson (imports.map toString))]
  -- the shown declarations
  -- instances, including scoped ones whose namespace is not open here
  let scopedInsts : NameSet :=
    (Meta.instanceExtension.ext.getState env).scopedEntries.map.toList.foldl
      (fun s (_, es) => es.foldl (fun s e => (e.globalName?.map s.insert).getD s) s) {}
  let mut decls : Array (Name × Name × ConstantInfo × Bool) := #[]
  let mut dropped : Nat := 0
  for m in mods do
    let idx := (env.getModuleIdx? m).get!
    for n in env.header.moduleData[idx.toNat]!.constNames do
      let some ci := env.find? n | continue
      if isAuxiliary env n then continue
      let isInst := Meta.isInstanceCore env n || scopedInsts.contains n
      if isInst then
        let hasDoc := (← findDocString? env n).isSome
        let userNamed := match n with | .str _ s => !s.startsWith "inst" | _ => false
        unless hasDoc || userNamed do dropped := dropped + 1; continue
      decls := decls.push (n, m, ci, isInst)
  let ctx : Ctx :=
    { env, lib := libModules env, decls := decls.foldl (fun s d => s.insert d.1) {} }
  let mut cache : Std.HashMap Name NameSet := {}
  let mut sorryCache : Std.HashMap Name Bool := {}
  let mut files : Std.HashMap Name (Array String) := {}
  let mut rows : Array (String × Nat × Json) := #[]
  for (n, m, ci, isInst) in decls do
    let k := kind env n isInst ci
    let (typeDeps, c1) := (depsOf ctx n #[ci.type]).run cache
    let (valDeps, c2) := (depsOf ctx n (valueExprs env ci)).run c1
    cache := c2
    let valDeps := valDeps.filter (!typeDeps.contains ·)
    let (sorried, s1) := (hasSorry env ctx.lib n).run sorryCache
    sorryCache := s1
    let sig ← liftTermElabM do
      try pure ((← PrettyPrinter.ppSignature n).fmt.pretty 100)
      catch _ => pure (toString n)
    let ranges ← findDeclarationRanges? n
    let path : System.FilePath :=
      System.mkFilePath (m.components.map toString) |>.addExtension "lean"
    unless files.contains m do
      let src ← try IO.FS.readFile path catch _ => pure ""
      files := files.insert m (src.splitOn "\n").toArray
    let stmt := ranges.bind fun r =>
      statement files[m]! r.range (k == "inductive" || k == "structure" || k == "class")
    let doc := (← findDocString? env n).map (·.trimAscii.toString)
    let line := ranges.map (·.range.pos.line)
    rows := rows.push (m.toString, line.getD 0, Json.mkObj [
      ("name", toString n), ("module", toString m), ("kind", k),
      ("line", toJson line), ("endLine", toJson (ranges.map (·.range.endPos.line))),
      ("doc", toJson doc), ("signature", sig), ("statement", toJson stmt),
      ("typeDeps", toJson (typeDeps.map toString)), ("valueDeps", toJson (valDeps.map toString)),
      ("sorry", sorried)])
  let sorted := rows.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)
  let out := Json.mkObj [("schema", (1 : Nat)), ("commit", Json.null), ("date", Json.null),
    ("modules", Json.arr modJson), ("decls", Json.arr (sorted.map (·.2.2)))]
  let path := (← IO.getEnv "EXPLORE_OUT").getD "explore-data.json"
  IO.FS.writeFile path (out.compress ++ "\n")
  logInfo m!"wrote {mods.size} modules and {rows.size} declarations to {path} \
    ({dropped} undocumented instances with generated names left out)"
