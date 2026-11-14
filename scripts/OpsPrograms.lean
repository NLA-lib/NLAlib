import NLAlib
open Lean Meta Elab Command

/-! # Fixed Ops programs and canonical certificates

Programs are finite first-order `Ops.Program` values. `Ops.Algorithm` certifies the declared
problem, jointly realizable primitive model and output/resource specification on the same
total instrumented execution. These requirements are checked by Lean's types, without the
former registry of `Computation.Prog` trees.

This integration check inventories the new program and certificate interfaces, checks that
declared programs have executable definitions, and rejects an imported old execution core.
The whole-library axiom audit and kernel replay remain separate mandatory checks. The
canonical rejection and accounting fixtures are checked by importing the library below.

## What the types do not say, reported per certificate

An `Ops.Algorithm M S` is as meaningful as its model `M` and specification `S`. For every
certificate declaration the check prints one line (the format of
`scripts/ops_certificates.txt`):

* `hyps`: the number of hypotheses (propositional binders) of the declaration;
* `uniform`, `confined`, `charged`: whether an instance of `Ops.AccessModel.Uniform`,
  `Ops.AccessModel.Confined`, `Ops.AccessModel.Charged` is found for the model, after unfolding
  its definition (`NLAlib/Ops/Confined.lean`). A model that is not uniform has an oracle; one
  that is not confined has a primitive or query that is not in operand form; one that is not
  charged has free or zero weights;
* `budget`, `scratch`: `closed` when the specification does not mention the static count or
  static workspace of a program, `manifest` when it does (a bound by the program's own syntax).

The lines are compared with `scripts/ops_certificates.txt`:

* a certificate of that file may not lose `uniform`, `confined`, `charged` or a `closed` bound,
  nor gain hypotheses: update its line in the same change, which makes the weakening visible;
* a certificate that is not in the file must be `confined` with a `closed` budget, or be added
  to the file.

Program declarations with parameters are listed: a tree built from a parameter is one tree per
value, not one fixed program, when the parameter also fixes the admitted sizes.
Run with `OPS_CERTIFICATES_WRITE=1` to rewrite the file from the current library.
-/

/-- Whether an instance of the class `cls` is found for the model `M`, unfolding the definition
of the model a few times. -/
def modelHas (cls : Name) (M : Expr) : MetaM Bool := do
  let mut e := M
  for _ in [0:8] do
    let found ← try
        let goal ← mkAppM cls #[e]
        pure (← synthInstance? goal).isSome
      catch _ => pure false
    if found then return true
    let e' ← whnfCore e
    match ← withTransparency .all (unfoldDefinition? e') with
    | some e'' => e := e''
    | none => return false
  return false

/-- Whether the expression mentions one of `targets`, through the definitions (not the
theorems) of the library. -/
def mentions (env : Environment) (targets : List Name) (e : Expr) : Bool := Id.run do
  let mut todo := e.getUsedConstants.toList
  let mut seen : NameSet := {}
  let mut fuel := 20000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => return false
    | c :: rest =>
      todo := rest
      if seen.contains c then continue
      seen := seen.insert c
      if targets.contains c then return true
      let inLibrary := match env.getModuleIdxFor? c with
        | some i => (`NLAlib).isPrefixOf env.header.moduleNames[i.toNat]!
        | none => false
      unless inLibrary do continue
      if let some (.defnInfo d) := env.find? c then
        todo := d.value.getUsedConstants.toList ++ todo
  return false

/-- One line of `scripts/ops_certificates.txt`. -/
structure CertLine where
  name : Name
  hyps : Nat
  uniform : Bool
  confined : Bool
  charged : Bool
  budgetClosed : Bool
  scratchClosed : Bool

def CertLine.format (c : CertLine) : String :=
  let mark (b : Bool) := if b then "yes" else "no"
  let bound (b : Bool) := if b then "closed" else "manifest"
  s!"{c.name} hyps={c.hyps} uniform={mark c.uniform} confined={mark c.confined} {""
    }charged={mark c.charged} budget={bound c.budgetClosed} scratch={bound c.scratchClosed}"

def CertLine.parse (line : String) : Option CertLine := do
  let name :: fields := line.splitOn " " | none
  let get (key : String) : Option String :=
    fields.findSome? fun f => match f.splitOn "=" with
      | [k, v] => if k == key then some v else none
      | _ => none
  let hyps ← get "hyps"
  let uniform ← get "uniform"
  let confined ← get "confined"
  let charged ← get "charged"
  let budget ← get "budget"
  let scratch ← get "scratch"
  some ⟨name.toName, hyps.toNat!, uniform == "yes", confined == "yes", charged == "yes",
    budget == "closed", scratch == "closed"⟩

run_cmd liftTermElabM do
  let env ← getEnv
  let mut programs : Nat := 0
  let mut algorithms : Nat := 0
  let mut lines : Array CertLine := #[]
  for moduleName in env.header.moduleNames do
    if (`NLAlib.Computation).isPrefixOf moduleName ||
        (`NLAlib.Matrix.Computation).isPrefixOf moduleName ||
        (`NLAlib.RandomMatrix.Computation).isPrefixOf moduleName then
      logError m!"retired execution module is still imported: {moduleName}"
  for (name, info) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? name | continue
    unless (`NLAlib).isPrefixOf env.header.moduleNames[i.toNat]! do continue
    if name.isInternal then continue
    let head ← forallTelescopeReducing info.type fun _ target =>
      pure target.getAppFn.constName?
    if head == some ``NLAlib.Ops.Program then
      programs := programs + 1
      if let .opaqueInfo _ := info then
        logError m!"E2 program {name} is opaque"
      if info.isUnsafe || info.isPartial then
        logError m!"E2 program {name} is unsafe or partial"
      if (Compiler.implementedByAttr.getParam? env name).isSome then
        logError m!"E2 program {name} has implemented_by"
      if isNoncomputable env name then
        logError m!"E2 program {name} is noncomputable"
      let params ← forallTelescopeReducing info.type fun xs _ => do
        let mut out : Array MessageData := #[]
        for x in xs do
          let decl ← x.fvarId!.getDecl
          let ty ← inferType x
          if decl.binderInfo.isExplicit && !(← isProp ty) && !ty.isSort then
            out := out.push m!"({decl.userName} : {ty})"
        pure out
      let core := [`NLAlib.Ops.Program, `NLAlib.Ops.Algorithm, `NLAlib.Ops.Impl].any
        (·.isPrefixOf name)
      unless params.isEmpty || core do
        logInfo m!"parametrised program {name} {MessageData.joinSep params.toList " "}"
    if head == some ``NLAlib.Ops.Algorithm then
      algorithms := algorithms + 1
      -- a constructor or combinator of the core is stated for an arbitrary model
      let generic ← forallTelescopeReducing info.type fun _ target =>
        pure target.getAppArgs[target.getAppNumArgs - 2]!.getAppFn.isFVar
      if generic then continue
      let line ← forallTelescopeReducing info.type fun xs target => do
        let args := target.getAppArgs
        let M := args[args.size - 2]!
        let S := args[args.size - 1]!
        let mut hyps := 0
        for x in xs do
          if ← isProp (← inferType x) then hyps := hyps + 1
        let uniform ← modelHas ``NLAlib.Ops.AccessModel.Uniform M
        let confined ← modelHas ``NLAlib.Ops.AccessModel.Confined M
        let charged ← modelHas ``NLAlib.Ops.AccessModel.Charged M
        let budget := !mentions env [``NLAlib.Ops.staticCost, ``NLAlib.Ops.stmtCost] S
        let scratch := !mentions env [``NLAlib.Ops.staticPeak, ``NLAlib.Ops.stmtPeak] S
        pure (⟨name, hyps, uniform, confined, charged, budget, scratch⟩ : CertLine)
      lines := lines.push line
  if programs = 0 ∨ algorithms = 0 then
    logError m!"missing Ops coverage: {programs} programs, {algorithms} certificates"
  lines := lines.qsort fun a b => a.name.toString < b.name.toString
  let path : System.FilePath := "scripts" / "ops_certificates.txt"
  let text := String.intercalate "\n" (lines.map CertLine.format).toList ++ "\n"
  if (← IO.getEnv "OPS_CERTIFICATES_WRITE").isSome then
    IO.FS.writeFile path text
  let known := (← IO.FS.lines path).filterMap CertLine.parse
  for c in lines do
    match known.find? (·.name == c.name) with
    | some k =>
      if (k.uniform && !c.uniform) || (k.confined && !c.confined) || (k.charged && !c.charged) ||
          (k.budgetClosed && !c.budgetClosed) || (k.scratchClosed && !c.scratchClosed) ||
          k.hyps < c.hyps then
        logError m!"certificate {c.name} is weaker than scripts/ops_certificates.txt records:{""
          }\n  recorded: {k.format}\n  now:      {c.format}"
    | none =>
      unless c.confined && c.budgetClosed do
        logError m!"new certificate {c.name} must have a confined model and a closed-form {""
          }budget, or a reviewed line in scripts/ops_certificates.txt:\n  {c.format}"
  for k in known do
    unless lines.any (·.name == k.name) do
      logError m!"scripts/ops_certificates.txt lists {k.name}, which is not a certificate"
  let count (p : CertLine → Bool) := (lines.filter p).size
  logInfo m!"ops programs: {programs} program declarations, {algorithms} certificate declarations"
  logInfo m!"ops certificates: {count (·.uniform)} uniform, {count (·.confined)} confined, {""
    }{count (·.charged)} charged, {count (·.budgetClosed)} closed budgets, {""
    }{count (·.scratchClosed)} closed scratch, {count (·.hyps == 0)} without hypotheses"

-- These are total canonical proofs, rather than conclusions accepted by a heuristic linter.
#check NLAlib.Ops.Examples.Certification.certifies_repeatProgram
#check NLAlib.Ops.Examples.Certification.repeatAlgorithmLinked
#check NLAlib.Ops.Tools.profileProgram_work
#check NLAlib.Ops.Tools.profileProgram_span

-- Structural rejection laws used by the kernel-checked examples: totality cannot be replaced
-- by a liberal assertion, and the program cannot be an unconditional abort.
#check NLAlib.Ops.Algorithm.not_nonempty
#check NLAlib.Ops.Algorithm.body_ne_abort
#check NLAlib.Ops.Algorithm.run_ne_none
