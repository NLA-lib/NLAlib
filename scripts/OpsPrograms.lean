import NLAlib
open Lean Meta Elab Command

/-! # Fixed Ops programs and canonical certificates

Programs are finite first-order `Ops.Program` values. `Ops.Algorithm` certifies the declared
problem, jointly realizable primitive model and output/resource specification on the same
total instrumented execution. These requirements are checked by Lean's types, without the
former registry of `Computation.Prog` trees.

This integration check inventories the program and certificate interfaces, checks that
declared programs have executable definitions, and rejects an imported old execution core.
The whole-library axiom audit and kernel replay remain separate mandatory checks. The
canonical rejection and accounting fixtures are checked by importing the library below.

## What the types do not say, reported per certificate

An `Ops.Algorithm M S` is as meaningful as its problem, its model `M` and its specification
`S`. For every certificate declaration the check computes one line (the format of
`scripts/ops_certificates.txt`), `Name key=value …`, with these keys:

* `hyps`: the number of hypotheses (propositional binders) of the declaration;
* `uniform`, `confined`, `charged` (`yes`, `no`, `unknown`): whether an instance of
  `Ops.AccessModel.Uniform`, `Ops.AccessModel.Confined`, `Ops.AccessModel.Charged` is found for
  the model, unfolding its definition (`NLAlib/Ops/Confined.lean`). `no` means the definition
  was unfolded to the end and no instance was found; `unknown` means the search stopped at its
  limit of unfoldings. A model that is not uniform has an oracle; one that is not confined has
  a primitive or query that is not in operand form; one that is not charged has free or zero
  weights;
* `budget`, `work`, `scratch` (`closed`, `manifest`, `unknown`), for the count budget, for the
  work and the span, and for the scratch of the specification. The dependencies of the field
  are followed through every definition of the library (not through proofs):
  - `manifest`: a dependency has a type that mentions a tree (`Ops.Stmt`, `Ops.Program`,
    `Ops.Routine`, `Ops.Impl`, `Ops.Algorithm`); the bound is read off the syntax of a program
    (`staticCost`, `staticPeak`, an instruction polynomial of the program, …);
  - `closed`: the search finished, and the field depends on no tree and on nothing that the
    search cannot inspect. This is the evidence that the bound is an expression in the sizes:
    every definition of the library under it was opened, and what is left are constructors,
    arithmetic and functions of Mathlib and of Lean's core;
  - `unknown`: the search reached its limit, or met a constant it cannot inspect: an axiom or
    an opaque constant, or a non-constructive choice (`nonConstructive` below: `Classical.choose`,
    `Nat.find`, a supremum or infimum over a set, …), or the specification did not unfold to its
    fields. The reason is printed. `unknown` counts as `manifest` wherever `closed` is required.
  Functions of Mathlib and of core are not opened; apart from the listed non-constructive ones
  they are taken to be what their names say;
* `problem` (`derived`, `handwritten`): whether the problem of the certificate is the problem of
  a `Ops.Routine.Domain` (mathematical inputs, an acceptance predicate and one slot per
  operand, with coverage by construction) or a hand-written `Ops.Problem`;
* `derived` (a number, `?`, or `-`): for a derived problem, the number of operands whose buffer
  holds words computed from the inputs (`Slot.derived`); `?` when the slots do not reduce;
* `unstored` (`yes`, `no`, `-`): for a derived problem, whether it declares inputs that no
  buffer holds;
* `oracles` (`declared`, `related`, `missing`, `none`): for a model that is not `uniform=yes`,
  `declared` when a declaration of type `Ops.Routine.Domain.Oracles D M` (the operations that
  may depend on the input, and the proof that no other does) is about this certificate: its
  binders are instantiated so that `D` is the domain of the problem (below `Domain.cast`) and
  `M` the model of the certificate. `related` when declarations exist for a domain built from
  the same constant but none unifies with this domain and model; `none` for a uniform model;
* `claim` (names joined by `+`, `related:` and names, `exempt`, `none`, `required-missing`):
  the declarations of type `Ops.RandomizedClaim A` whose `A`, with the binders of the claim
  instantiated, is this certificate applied to its own parameters. `related:` and the names
  when claims exist about the same certificate declaration but only at other arguments (a
  fixed field, a bundle of operations): such a claim is not a claim of this certificate. A
  certificate whose routine specification is `Routine.Spec.terminates` states nothing of the
  values written; it must have a claim that applies (`required-missing` is an error; a related
  claim does not count) unless it is listed in `exempt` with its reason.

The comparison is by unification up to reducible definitions; the hypotheses that a
declaration which applies adds to those of the certificate are printed by the report.

The lines are compared with `scripts/ops_certificates.txt`:

* a certificate of that file may not lose `uniform=yes`, `confined=yes`, `charged=yes`, a
  `closed` bound, `problem=derived`, `oracles=declared` or its claim (`related` values do
  not keep either), nor gain hypotheses:
  update its line in the same change, which makes the weakening visible;
* a certificate that is not in the file must be `confined=yes` with `closed` work and a
  `derived` problem, or be added to the file.

Program declarations with parameters are listed: a tree built from a parameter is one tree per
value, not one fixed program, when the parameter also fixes the admitted sizes.

## Environment variables

* `OPS_CERTIFICATES_WRITE=1`: rewrite the file from the current library.
* `OPS_CERTIFICATES_FILE=path`: the file to compare with (and to rewrite), instead of
  `scripts/ops_certificates.txt`.
* `OPS_CERTIFICATES_REPORT=1`, or `=Name` for the certificates whose name contains `Name`:
  print, for each certificate, what it states: its line, the admitted sizes and the acceptance
  predicate as written, the derived slots with their formulas, the unstored inputs with the
  operations that reach them, the model with the contracts of its operations and of its
  queries and the three weights, every binder of the certificate (parameters and hypotheses),
  its output condition and its resource fields. For each oracle declaration and each claim it
  says whether it applies to this instance; for one that applies, which of its binders this
  instance fixes, which parameters remain, which hypotheses are also hypotheses of the
  certificate and which are not; for a claim, the law of the tape (realizable: a field of the
  claim), `admits`, `interprets`, the event and the bound; for one that does not apply, the
  instance it is about and where it differs. The report never writes the fixture.
* `OPS_CERTIFICATES_REPORT_FILE=path`: write the report to that file instead of printing it.
-/

namespace OpsCertificates

/-- The answer of an instance search. -/
inductive Tri where
  | yes | no | unknown
  deriving BEq, Inhabited

def Tri.format : Tri → String
  | .yes => "yes" | .no => "no" | .unknown => "unknown"

def Tri.parse (s : String) : Tri :=
  if s == "yes" then .yes else if s == "unknown" then .unknown else .no

/-- The classification of a resource field. -/
inductive Bound where
  | closed | manifest | unknown
  deriving BEq, Inhabited

def Bound.format : Bound → String
  | .closed => "closed" | .manifest => "manifest" | .unknown => "unknown"

def Bound.parse (s : String) : Bound :=
  if s == "closed" then .closed else if s == "unknown" then .unknown else .manifest

/-- For each module of the environment, whether it is a module of the library. Computed once:
the list of modules is not cheap to read for every constant. -/
def libraryModules (env : Environment) : Array Bool :=
  env.header.moduleNames.map (`NLAlib).isPrefixOf

/-- Whether the constant is declared in a module of the library. -/
def inLibrary (lib : Array Bool) (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some i => lib[i.toNat]!
  | none => false

/-- The types of trees. -/
def treeTypes : List Name :=
  [`NLAlib.Ops.Stmt, `NLAlib.Ops.Program, `NLAlib.Ops.Routine, `NLAlib.Ops.Impl,
    `NLAlib.Ops.Algorithm]

/-- Types whose values describe a problem, not a run: a domain, its slots and codecs, and the
problem itself. Their constants and the functions of their namespaces are not opened. -/
def problemTypes : List Name :=
  [`NLAlib.Ops.Problem, `NLAlib.Ops.Routine.Domain, `NLAlib.Ops.Slot, `NLAlib.Ops.Codec]

/-- Constants outside the library that the search does not accept in a closed bound: a value
obtained by choice, by search, or as a bound of a set says nothing explicit. -/
def nonConstructive : List Name :=
  [`Classical.choice, `Classical.choose, `Classical.indefiniteDescription, `Classical.epsilon,
    `Classical.strongIndefiniteDescription, `Exists.choose, `Nat.find, `Nat.findGreatest,
    `Classical.propDecidable, `Classical.dec, `Classical.decEq, `Classical.decPred,
    `Classical.decRel, `sSup, `sInf, `iSup, `iInf, `SupSet.sSup, `InfSet.sInf,
    `WellFounded.fix, `WellFounded.min, `Function.invFun, `Classical.arbitrary]

/-- The result type of a type: what is left under its binders. -/
def resultType : Expr → Expr
  | .forallE _ _ b _ => resultType b
  | .mdata _ e => resultType e
  | e => e

/-- Whether a binder of the type has a type that mentions a tree. -/
def takesTree : Expr → Bool
  | .forallE _ t b _ => t.getUsedConstants.any treeTypes.contains || takesTree b
  | .mdata _ e => takesTree e
  | _ => false

/-- How the search treats a constant. -/
inductive Kind where
  /-- A function that reads a number, a count or other data off a tree. -/
  | readsTree
  /-- A tree, a problem, a domain, or a function of their namespaces: not opened. -/
  | leaf
  /-- Anything else. -/
  | other

/-- The kind of a constant, from its name and its type. -/
def kind (env : Environment) (c : Name) : Kind :=
  match env.find? c with
  | none => .other
  | some info =>
    let result := resultType info.type
    let head := result.getAppFn.constName?
    if problemTypes.any (·.isPrefixOf c) then .leaf
    else if (head.map fun h => treeTypes.contains h || problemTypes.contains h) == some true then
      .leaf
    else if result.isSort then .other
    else if takesTree info.type then .readsTree
    else .other

/-- The classification of the cone of a constant: of everything it depends on through the
definitions of the library. Memoised. -/
partial def cone (lib : Array Bool) (env : Environment) (c : Name) :
    StateM (Std.HashMap Name (Bound × String)) (Bound × String) := do
  if let some v := (← get)[c]? then return v
  let verdict ← (do
    match kind env c with
    | .readsTree => return (Bound.manifest, s!"{c} reads a tree")
    | .leaf => return (Bound.closed, "")
    | .other => pure ()
    if nonConstructive.contains c then return (Bound.unknown, s!"non-constructive {c}")
    match env.find? c with
    | none => return (Bound.unknown, s!"unknown constant {c}")
    | some (.defnInfo d) =>
      if inLibrary lib env c then
        let mut out : Bound × String := (.closed, "")
        for u in d.value.getUsedConstants do
          let v ← cone lib env u
          match v.1 with
          | .manifest => return v
          | .unknown => if out.1 == .closed then out := v
          | .closed => pure ()
        return out
      else return (Bound.closed, "")
    | some (.opaqueInfo _) => return (Bound.unknown, s!"opaque {c}")
    | some (.axiomInfo _) =>
      if c == ``propext || c == ``Quot.sound then return (Bound.closed, "")
      else return (Bound.unknown, s!"axiom {c}")
    | some _ => return (Bound.closed, ""))
  modify fun m => m.insert c verdict
  return verdict

/-- Classify an expression by its dependencies, through the definitions of the library. The
string is the reason of a `manifest` or `unknown` answer. -/
def classify (lib : Array Bool) (env : Environment) (e : Expr) :
    StateM (Std.HashMap Name (Bound × String)) (Bound × String) := do
  let mut out : Bound × String := (.closed, "")
  for u in e.getUsedConstants do
    let v ← cone lib env u
    match v.1 with
    | .manifest => return v
    | .unknown => if out.1 == .closed then out := v
    | .closed => pure ()
  return out

/-- Whether an instance of the class `cls` is found for the model `M`, unfolding the definition
of the model. -/
def modelHas (cls : Name) (M : Expr) : MetaM Tri := do
  let mut e := M
  for _ in [0:8] do
    let found ← try
        let goal ← mkAppM cls #[e]
        pure (← synthInstance? goal).isSome
      catch _ => pure false
    if found then return .yes
    let e' ← whnfCore e
    match ← withTransparency .all (unfoldDefinition? e') with
    | some e'' => e := e''
    | none => return .no
  return .unknown

/-- The fields of a specification (budget, scratch, work, span, memory, good), when its
definition unfolds to the constructor. -/
def specFields (S : Expr) : MetaM (Option (Array Expr)) := do
  let mut e := S
  for _ in [0:12] do
    let e' ← whnfCore e
    if e'.getAppFn.isConstOf ``NLAlib.Ops.Specification.mk then
      let args := e'.getAppArgs
      return some (args.extract (args.size - 6) args.size)
    match ← withTransparency .all (unfoldDefinition? e') with
    | some e'' => e := e''
    | none => return none
  return none

/-- The domain of a problem that is `Routine.Domain.problem` of a domain. -/
def findDomain (P : Expr) : MetaM (Option Expr) := do
  let mut e := P
  for _ in [0:12] do
    let e' ← whnfCore e
    if e'.isAppOf ``NLAlib.Ops.Routine.Domain.problem then return e'.getAppArgs.back?
    match ← withTransparency .all (unfoldDefinition? e') with
    | some e'' => e := e''
    | none => return none
  return none

/-- The constant a domain is built from: the head of the domain, below `Domain.cast`. -/
partial def domainHead (D : Expr) : MetaM (Option Name) := do
  let D ← whnfCore D
  if D.isAppOf ``NLAlib.Ops.Routine.Domain.cast then
    let args := D.getAppArgs
    if args.size ≥ 4 then domainHead args[args.size - 4]! else pure none
  else
    match D.getAppFn.constName? with
    | some c =>
      -- an abbreviation of a cast domain
      match ← withTransparency .all (unfoldDefinition? D) with
      | some D' =>
        let D'' ← whnfCore D'
        if D''.isAppOf ``NLAlib.Ops.Routine.Domain.cast then domainHead D'' else pure (some c)
      | none => pure (some c)
    | none => pure none

/-- The domain below `Domain.cast`: a cast changes the types the domain is read at, not the
domain. -/
partial def domainBase (D : Expr) : MetaM Expr := do
  let D ← whnfCore D
  if D.isAppOf ``NLAlib.Ops.Routine.Domain.cast then
    let args := D.getAppArgs
    if args.size ≥ 4 then domainBase args[args.size - 4]! else pure D
  else if D.getAppFn.isConst then
    match ← withTransparency .all (unfoldDefinition? D) with
    | some D' =>
      let D'' ← whnfCore D'
      if D''.isAppOf ``NLAlib.Ops.Routine.Domain.cast then domainBase D'' else pure D
    | none => pure D
  else pure D

/-- The applications of `Slot.derived` (or `Slot.derivedOfLength`) in an expression, without
entering them. -/
partial def derivedSlots (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  if e.isAppOf ``NLAlib.Ops.Slot.derived || e.isAppOf ``NLAlib.Ops.Slot.derivedOfLength then
    acc.push e
  else match e with
    | .app f a => derivedSlots a (derivedSlots f acc)
    | .lam _ _ b _ => derivedSlots b acc
    | .letE _ _ v b _ => derivedSlots b (derivedSlots v acc)
    | .mdata _ b => derivedSlots b acc
    | .proj _ _ b => derivedSlots b acc
    | _ => acc

/-- The number of derived slots of a domain, whether it declares unstored inputs, and the
derived slots as written. The slots are read off the definition of `slot`: `?` when it is not
a function written out with its slots. -/
def domainSlots (D : Expr) : MetaM (String × String × Array String) := do
  let unstored ← try
      let u ← whnf (← mkAppM ``NLAlib.Ops.Routine.Domain.Unstored #[D])
      let body := match u with
        | .lam _ _ b _ => b
        | e => e
      pure (if body.isConstOf ``Unit || body.isAppOf ``PUnit then "no" else "yes")
    catch _ => pure "?"
  try
    let slot ← whnf (← mkAppM ``NLAlib.Ops.Routine.Domain.slot #[D])
    lambdaTelescope slot fun _ body => do
      let known := body.getUsedConstants.any fun c =>
        c == ``NLAlib.Ops.Slot.stored || c == ``NLAlib.Ops.Slot.blank ||
          c == ``NLAlib.Ops.Slot.derived || c == ``NLAlib.Ops.Slot.derivedOfLength
      let ds := derivedSlots body
      let mut shown : Array String := #[]
      for s in ds do
        let fmt ← try
            withOptions (fun o => o.setBool `pp.proofs false) (ppExpr s)
          catch _ => pure "(not printed)"
        shown := shown.push (fmt.pretty 100)
      return (if known then toString ds.size else "?", unstored, shown)
  catch _ => return ("?", unstored, #[])

/-- Termination-only certificates that need no claim of their own, each with its reason. -/
def exempt : List (Name × String) :=
  [(`NLAlib.Schur.schurPipelineAlgorithm,
    "generic in its four stages, which are hypotheses; the claim is that of its instance " ++
      "NLAlib.Schur.denseSchurAlgorithm")]

/-- Whether the definition of `c` uses `Routine.Spec.terminates`, through the definitions of
the constants in `follow` (the certificates and the routine specifications of the library).
The specification of a certificate is data of its definition, so proofs are not searched.
Memoised. -/
partial def usesTerminates (env : Environment) (follow : NameSet) (c : Name) :
    StateM (Std.HashMap Name (Option Bool)) (Option Bool) := do
  if let some v := (← get)[c]? then return v
  let verdict ← (do
    let some (.defnInfo info) := env.find? c | return some false
    let used := info.value.getUsedConstants
    if used.contains ``NLAlib.Ops.Routine.Spec.terminates then return some true
    let mut out : Option Bool := some false
    for u in used do
      if follow.contains u && u != c then
        match ← usesTerminates env follow u with
        | some true => return some true
        | none => out := none
        | some false => pure ()
    return out)
  modify fun m => m.insert c verdict
  return verdict

/-- One line of `scripts/ops_certificates.txt`. -/
structure CertLine where
  name : Name
  hyps : Nat
  uniform : Tri
  confined : Tri
  charged : Tri
  budget : Bound
  work : Bound
  scratch : Bound
  problem : String
  derived : String
  unstored : String
  oracles : String
  claim : String
  deriving Inhabited

def CertLine.format (c : CertLine) : String :=
  s!"{c.name} hyps={c.hyps} uniform={c.uniform.format} confined={c.confined.format} {""
    }charged={c.charged.format} budget={c.budget.format} work={c.work.format} {""
    }scratch={c.scratch.format} problem={c.problem} derived={c.derived} {""
    }unstored={c.unstored} oracles={c.oracles} claim={c.claim}"

def CertLine.parse (line : String) : Option CertLine := do
  let name :: fields := line.splitOn " " | none
  if name.isEmpty then none
  let get (key : String) : Option String :=
    fields.findSome? fun f => match f.splitOn "=" with
      | [k, v] => if k == key then some v else none
      | _ => none
  let hyps ← get "hyps"
  some {
    name := name.toName, hyps := hyps.toNat!
    uniform := Tri.parse ((get "uniform").getD "no")
    confined := Tri.parse ((get "confined").getD "no")
    charged := Tri.parse ((get "charged").getD "no")
    budget := Bound.parse ((get "budget").getD "manifest")
    work := Bound.parse ((get "work").getD "manifest")
    scratch := Bound.parse ((get "scratch").getD "manifest")
    problem := (get "problem").getD "handwritten"
    derived := (get "derived").getD "-"
    unstored := (get "unstored").getD "-"
    oracles := (get "oracles").getD "none"
    claim := (get "claim").getD "none" }

/-- Whether a claim value names a claim. -/
def hasClaim (s : String) : Bool :=
  s != "none" && s != "required-missing" && !s.startsWith "related:"

/-- Whether the certificate `c` is weaker than its recorded line `k`. -/
def weaker (k c : CertLine) : Bool :=
  (k.uniform == .yes && c.uniform != .yes) || (k.confined == .yes && c.confined != .yes) ||
    (k.charged == .yes && c.charged != .yes) ||
    (k.budget == .closed && c.budget != .closed) || (k.work == .closed && c.work != .closed) ||
    (k.scratch == .closed && c.scratch != .closed) ||
    (k.problem == "derived" && c.problem != "derived") ||
    (k.oracles == "declared" && (c.oracles == "missing" || c.oracles == "related")) ||
    (hasClaim k.claim && !hasClaim c.claim) || k.hyps < c.hyps

/-- Print an expression on one paragraph of bounded size. -/
def render (e : Expr) : MetaM String := do
  let fmt ← try
      withOptions (fun o => (o.setBool `pp.proofs false).set `pp.maxSteps (20000 : Nat))
        (ppExpr e)
    catch _ => pure "(not printed)"
  let s := fmt.pretty 100
  return if s.length > 2400 then (s.take 2400).toString ++ " …" else s

/-- The value of a field of a structure-valued expression, as written. -/
def field (proj : Name) (e : Expr) : MetaM String := do
  try
    let p ← mkAppM proj #[e]
    render (← whnf p)
  catch _ => pure "(not available)"

/-- A related declaration read at one certificate: whether its type is that of this instance,
and how its binders are met. -/
structure Applied where
  /-- The declaration. -/
  name : Name
  /-- Its type unifies with this instance. -/
  applies : Bool
  /-- Binders fixed by this instance, parameters left free, hypotheses met by a hypothesis of
  the certificate, and hypotheses of the declaration only: each as written. -/
  fixed : Array String
  free : Array String
  shared : Array String
  extra : Array String
  /-- The declaration applied to its binders, when it applies. -/
  term : Option Expr
  /-- When it does not apply: the arguments at which its instance and this one differ. -/
  differs : Array String := #[]

/-- Read the declaration `c`, whose type ends in an application `F … a₁ … aₖ`, at this
instance: its binders become unknowns, and the last `k` arguments must unify with `targets`
(`check` may replace the comparison of one argument). Unknowns that remain are parameters, or
hypotheses, which are looked up among the hypotheses `hyps` of the certificate. -/
def applyAt (c : Name) (targets : Array Expr) (hyps : Array Expr)
    (check : Nat → Expr → Expr → MetaM Bool := fun _ a b => withReducible (isDefEq a b)) :
    MetaM Applied := do
  let env ← getEnv
  let some info := env.find? c | return ⟨c, false, #[], #[], #[], #[], none, #[]⟩
  let names ← forallTelescopeReducing info.type fun ys _ =>
    ys.mapM fun y => do pure (← y.fvarId!.getDecl).userName
  let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let (mvars, _, target) ← forallMetaTelescopeReducing
    (info.type.instantiateLevelParams info.levelParams lvls)
  let args := target.getAppArgs
  let k := targets.size
  let mut ok := decide (args.size ≥ k)
  if ok then
    for i in [0:k] do
      let a := args[args.size - k + i]!
      let good ← try check i a targets[i]! catch _ => pure false
      unless good do ok := false
  let mut fixed := #[]
  let mut free := #[]
  let mut shared := #[]
  let mut extra := #[]
  let mut differs := #[]
  if !ok && args.size ≥ k then
    -- where the two instances part: argument by argument, for the report
    for i in [0:k] do
      let a := args[args.size - k + i]!
      let b := targets[i]!
      if a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs then
        for (x, y) in a.getAppArgs.zip b.getAppArgs do
          let same ← try withReducible (isDefEq x y) catch _ => pure false
          unless same do
            differs := differs.push
              s!"{← render (← instantiateMVars x)}  (this instance: {← render y})"
      else
        differs := differs.push s!"{← render (← instantiateMVars a)}  (this instance: {← render b})"
  if ok then
    for i in [0:mvars.size] do
      let m := mvars[i]!
      let nm := names[i]?.getD `_
      let ty ← instantiateMVars (← inferType m)
      let v ← instantiateMVars m
      let shown ← render ty
      if !v.isMVar then
        if !(← isProp ty) then fixed := fixed.push s!"({nm} := {← render v})"
      else if ← isProp ty then
        let mut met := false
        for h in hyps do
          if !met then
            if ← (try withReducible (isDefEq (← inferType h) ty) catch _ => pure false) then
              try m.mvarId!.assign h catch _ => pure ()
              met := true
        if met then shared := shared.push s!"({nm} : {shown})"
        else extra := extra.push s!"({nm} : {shown})"
      else
        -- instance arguments are found by the claim itself
        let inst ← try synthInstance? ty catch _ => pure none
        match inst with
        | some i => (try m.mvarId!.assign i catch _ => pure ())
        | none => free := free.push s!"({nm} : {shown})"
  let term ← if ok then
      pure (some (← instantiateMVars
        (mkAppN (mkConst c lvls) mvars)))
    else pure none
  return ⟨c, ok, fixed, free, shared, extra, term, differs⟩

/-- What is known of one certificate. -/
structure Entry where
  line : CertLine
  notes : Array String
  report : String

end OpsCertificates

open OpsCertificates in
run_cmd liftTermElabM do
  let env ← getEnv
  let lib := libraryModules env
  let mut programs : Nat := 0
  let mut algorithms : Nat := 0
  let mut certificates : Array Name := #[]
  let mut follow : NameSet := {}
  let mut claims : Array (Name × Name) := #[]
  let mut oracles : Array (Name × Name) := #[]
  for moduleName in env.header.moduleNames do
    if (`NLAlib.Computation).isPrefixOf moduleName ||
        (`NLAlib.Matrix.Computation).isPrefixOf moduleName ||
        (`NLAlib.RandomMatrix.Computation).isPrefixOf moduleName then
      logError m!"retired execution module is still imported: {moduleName}"
  for (name, info) in env.constants.map₁.toList do
    unless inLibrary lib env name do continue
    if name.isInternal then continue
    let (head, generic, last, domain) ← forallTelescopeReducing info.type fun _ target => do
      let args := target.getAppArgs
      let head := target.getAppFn.constName?
      let generic := args.size ≥ 2 && args[args.size - 2]!.getAppFn.isFVar
      let last := args.back?.bind fun a => a.getAppFn.constName?
      let domain ← if head == some ``NLAlib.Ops.Routine.Domain.Oracles && args.size ≥ 2 then
          domainHead args[args.size - 2]!
        else pure none
      pure (head, generic, last, domain)
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
      follow := follow.insert name
      -- a constructor or combinator of the core is stated for an arbitrary model
      unless generic do certificates := certificates.push name
    if head == some ``NLAlib.Ops.Routine.Spec then follow := follow.insert name
    if head == some ``NLAlib.Ops.RandomizedClaim then
      if let some certificate := last then claims := claims.push (name, certificate)
    if head == some ``NLAlib.Ops.Routine.Domain.Oracles then
      if let some dom := domain then oracles := oracles.push (name, dom)
  if programs = 0 ∨ algorithms = 0 then
    logError m!"missing Ops coverage: {programs} programs, {algorithms} certificates"
  let reportSel ← IO.getEnv "OPS_CERTIFICATES_REPORT"
  let wanted (name : Name) : Bool := match reportSel with
    | none => false
    | some s => s == "1" || s.isEmpty || (name.toString.splitOn s).length > 1
  let mut entries : Array Entry := #[]
  let memoRef ← IO.mkRef ({} : Std.HashMap Name (Bound × String))
  let termRef ← IO.mkRef ({} : Std.HashMap Name (Option Bool))
  for name in certificates.qsort (·.toString < ·.toString) do
    let some info := env.find? name | continue
    let entry ← forallTelescopeReducing info.type fun xs target => do
      let args := target.getAppArgs
      let M := args[args.size - 2]!
      let S := args[args.size - 1]!
      let mut hyps : Array Expr := #[]
      for x in xs do
        if ← isProp (← inferType x) then hyps := hyps.push x
      let uniform ← modelHas ``NLAlib.Ops.AccessModel.Uniform M
      let confined ← modelHas ``NLAlib.Ops.AccessModel.Confined M
      let charged ← modelHas ``NLAlib.Ops.AccessModel.Charged M
      let fields ← specFields S
      -- a field that is a projection of another specification is reduced to that field
      let reduced ← match fields with
        | some f => pure (some (← f.mapM fun e => do
            try whnf e catch _ => pure e))
        | none => pure none
      let mut notes : Array String := #[]
      let mut reasons : Array String := #[]
      let cls (label : String) (es : List Expr) :
          StateM (Std.HashMap Name (Bound × String)) (Bound × Array String × String) := do
        let mut out := Bound.closed
        let mut ns : Array String := #[]
        for e in es do
          let (b, reason) ← classify lib env e
          match b with
          | .manifest => return (.manifest, #[], s!"{label}: {reason}")
          | .unknown =>
            out := .unknown
            ns := ns.push s!"{label}: {reason}"
          | .closed => pure ()
        return (out, ns, "")
      let mut memo ← memoRef.get
      let (budget, work, scratch) ← match reduced with
        | some f =>
          let ((b, n1, r1), m1) := (cls "budget" [f[0]!]).run memo
          let ((w, n2, r2), m2) := (cls "work" [f[2]!, f[3]!]).run m1
          let ((s, n3, r3), m3) := (cls "scratch" [f[1]!]).run m2
          memo := m3
          notes := notes ++ n1 ++ n2 ++ n3
          reasons := #[r1, r2, r3].filter (!·.isEmpty)
          pure (b, w, s)
        | none =>
          notes := notes.push "the specification does not unfold to its fields"
          pure (Bound.unknown, Bound.unknown, Bound.unknown)
      memoRef.set memo
      for (label, t) in [("uniform", uniform), ("confined", confined), ("charged", charged)] do
        if t == .unknown then
          notes := notes.push s!"{label}: the model was not unfolded to the end"
      -- the problem
      let MTy ← whnf (← inferType M)
      let P := MTy.getAppArgs.back!
      let dom ← findDomain P
      let (problem, derived, unstored, formulas) ← match dom with
        | some D =>
          let (n, u, fs) ← domainSlots D
          pure ("derived", n, u, fs)
        | none => pure ("handwritten", "-", "-", #[])
      let domName ← match dom with
        | some D => domainHead D
        | none => pure none
      -- oracle declarations on this domain, read at this domain and this model: the domain
      -- may be read through a cast, the model must be this one
      let relatedOracles := oracles.filter fun o => some o.2 == domName
      let mut oracleApps : Array Applied := #[]
      for (o, _) in relatedOracles do
        let targets := match dom with
          | some D => #[D, M]
          | none => #[M]
        let a ← applyAt o targets hyps fun i a b => do
          if targets.size == 2 && i == 0 then
            withReducible (isDefEq (← domainBase a) (← domainBase b))
          else withReducible (isDefEq a b)
        oracleApps := oracleApps.push a
      let own := oracleApps.filter (·.applies)
      let oraclesField := if uniform == .yes then "none"
        else if !own.isEmpty then "declared"
        else if !relatedOracles.isEmpty then "related" else "missing"
      -- claims about this certificate's declaration, read at this instance
      let self := mkAppN (mkConst name (info.levelParams.map mkLevelParam)) xs
      let relatedClaims := ((claims.filter (·.2 == name)).map (·.1)).qsort
        (·.toString < ·.toString)
      let mut claimApps : Array Applied := #[]
      for c in relatedClaims do claimApps := claimApps.push (← applyAt c #[self] hyps)
      let ownClaims := (claimApps.filter (·.applies)).map (·.name)
      let (terminates, tmemo) := (usesTerminates env follow name).run (← termRef.get)
      termRef.set tmemo
      if terminates.isNone then
        notes := notes.push "claim: the search for a termination-only specification did not finish"
      let claim :=
        if !ownClaims.isEmpty then
          String.intercalate "+" (ownClaims.toList.map (·.toString))
        else if (exempt.find? (·.1 == name)).isSome && terminates != some false then "exempt"
        else if terminates != some false then "required-missing"
        else if !relatedClaims.isEmpty then
          "related:" ++ String.intercalate "+" (relatedClaims.toList.map (·.toString))
        else "none"
      let line : CertLine := {
        name, hyps := hyps.size, uniform, confined, charged, budget, work, scratch, problem,
        derived, unstored, oracles := oraclesField, claim }
      -- the report
      let mut report := ""
      if wanted name then
        let mut out : Array String := #[s!"== {line.format}"]
        for n in notes do out := out.push s!"  note: {n}"
        for r in reasons do out := out.push s!"  manifest because {r}"
        match dom with
        | some D =>
          out := out.push s!"  admitted sizes (valid): {← field ``NLAlib.Ops.Routine.Domain.valid D}"
          out := out.push s!"  inputs (In): {← field ``NLAlib.Ops.Routine.Domain.In D}"
          out := out.push s!"  accepts: {← field ``NLAlib.Ops.Routine.Domain.accepts D}"
          out := out.push s!"  slots: {← field ``NLAlib.Ops.Routine.Domain.slot D}"
          for f in formulas do out := out.push s!"  derived slot: {f}"
          if unstored == "yes" then
            out := out.push
              s!"  unstored inputs: {← field ``NLAlib.Ops.Routine.Domain.unstored D}"
        | none =>
          out := out.push s!"  admitted sizes (valid): {← field ``NLAlib.Ops.Problem.valid P}"
          out := out.push s!"  data: {← field ``NLAlib.Ops.Problem.Data P}"
          out := out.push s!"  admissible: {← field ``NLAlib.Ops.Problem.admissible P}"
        for a in oracleApps do
          if a.applies then
            let ops ← match a.term with
              | some t => field ``NLAlib.Ops.Routine.Domain.Oracles.ops t
              | none => pure "(not available)"
            out := out.push (s!"  oracles {a.name} [applies to this domain and model]: " ++
              s!"operations that may depend on the input: {ops}")
            for e in a.fixed do out := out.push s!"    fixed by this instance: {e}"
            for e in a.free do out := out.push s!"    parameter of the declaration: {e}"
            for e in a.shared do out := out.push s!"    hypothesis shared with the certificate: {e}"
            for e in a.extra do
              out := out.push s!"    hypothesis NOT of the certificate: {e}"
          else
            out := out.push
              s!"  oracles {a.name} [related declaration; not about this domain and model]"
            for e in a.differs do out := out.push s!"    it is about: {e}"
        out := out.push s!"  model: {← render M}"
        out := out.push
          s!"  contracts of the operations: {← field ``NLAlib.Ops.AccessModel.operation M}"
        out := out.push
          s!"  contracts of the queries: {← field ``NLAlib.Ops.AccessModel.query M}"
        let weight (proj : Name) : MetaM String := do
          try
            let rm ← mkAppM ``NLAlib.Ops.AccessModel.resources #[M]
            field proj (← whnf rm)
          catch _ => pure "(not available)"
        out := out.push s!"  weights of the operations (operationWork): {
          ← weight ``NLAlib.Ops.ResourceModel.operationWork}"
        out := out.push s!"  weights of the queries (queryWork): {
          ← weight ``NLAlib.Ops.ResourceModel.queryWork}"
        out := out.push s!"  weights of the structural instructions (coreWork): {
          ← weight ``NLAlib.Ops.ResourceModel.coreWork}"
        for x in xs do
          let decl ← x.fvarId!.getDecl
          let ty ← inferType x
          let label := if ← isProp ty then "hypothesis" else "parameter"
          out := out.push s!"  {label} ({decl.userName} : {← render ty})"
        match fields with
        | some f =>
          out := out.push s!"  budget [{budget.format}]: {← render f[0]!}"
          out := out.push s!"  work [{work.format}]: {← render f[2]!}"
          out := out.push s!"  span: {← render f[3]!}"
          out := out.push s!"  scratch [{scratch.format}]: {← render f[1]!}"
          out := out.push s!"  memory: {← render f[4]!}"
          out := out.push s!"  output condition (good): {← render f[5]!}"
        | none => out := out.push s!"  specification: {← render S}"
        for a in claimApps do
          unless a.applies do
            out := out.push (s!"  claim {a.name} [related declaration; about another instance " ++
              "of this certificate, not this one]")
            let some cinfo := env.find? a.name | continue
            let about ← forallTelescopeReducing cinfo.type fun _ t => do
              render (t.getAppArgs.back?.getD t)
            out := out.push s!"    it is about: {about}"
            for e in a.differs do out := out.push s!"    where it differs: {e}"
            continue
          let some e := a.term | continue
          out := out.push s!"  claim {a.name} [applies to this instance]"
          for b in a.fixed do out := out.push s!"    fixed by this instance: {b}"
          for b in a.free do out := out.push s!"    parameter of the claim: {b}"
          for b in a.shared do out := out.push s!"    hypothesis shared with the certificate: {b}"
          for b in a.extra do
            out := out.push s!"    hypothesis of the claim, NOT of the certificate: {b}"
          out := out.push s!"    law of the tape: {← field ``NLAlib.Ops.RandomizedClaim.law e}"
          out := out.push "    the law is realizable: proved (field `realizable` of the claim)"
          out := out.push (s!"    hypotheses on the input (admits): " ++
            s!"{← field ``NLAlib.Ops.RandomizedClaim.admits e}")
          out := out.push (s!"    hypotheses on the interpretation (interprets): " ++
            s!"{← field ``NLAlib.Ops.RandomizedClaim.interprets e}")
          out := out.push s!"    event: {← field ``NLAlib.Ops.RandomizedClaim.event e}"
          out := out.push s!"    failure bound: {← field ``NLAlib.Ops.RandomizedClaim.bound e}"
        report := String.intercalate "\n" out.toList
      pure ({ line, notes, report } : Entry)
    entries := entries.push entry
  let lines := entries.map (·.line)
  for e in entries do
    for n in e.notes do logInfo m!"ops certificate {e.line.name}: {n}"
    if e.line.claim == "required-missing" then
      logError m!"the certificate {e.line.name} is termination-only and has no RandomizedClaim"
  for (name, _) in exempt do
    unless certificates.contains name do
      logError m!"the exempt name {name} is not a certificate"
  -- the report
  if reportSel.isSome then
    let text := String.intercalate "\n\n" ((entries.filter (!·.report.isEmpty)).map (·.report)).toList
    match ← IO.getEnv "OPS_CERTIFICATES_REPORT_FILE" with
    | some file => IO.FS.writeFile file (text ++ "\n")
    | none => logInfo m!"{text}"
  -- the fixture
  let path : System.FilePath := match ← IO.getEnv "OPS_CERTIFICATES_FILE" with
    | some p => p
    | none => "scripts" / "ops_certificates.txt"
  let text := String.intercalate "\n" (lines.map CertLine.format).toList ++ "\n"
  if (← IO.getEnv "OPS_CERTIFICATES_WRITE").isSome then
    IO.FS.writeFile path text
  let known := (← IO.FS.lines path).filterMap CertLine.parse
  for c in lines do
    match known.find? (·.name == c.name) with
    | some k =>
      if weaker k c then
        logError m!"certificate {c.name} is weaker than {path} records:{""
          }\n  recorded: {k.format}\n  now:      {c.format}"
    | none =>
      unless c.confined == .yes && c.work == .closed && c.problem == "derived" do
        logError m!"new certificate {c.name} must have a confined model, closed-form work {""
          }and span and a derived problem, or a reviewed line in {path}:\n  {c.format}"
  for k in known do
    unless lines.any (·.name == k.name) do
      logError m!"{path} lists {k.name}, which is not a certificate"
  let count (p : CertLine → Bool) := (lines.filter p).size
  logInfo m!"ops programs: {programs} program declarations, {algorithms} certificate declarations"
  logInfo m!"ops certificates: {count (·.uniform == .yes)} uniform, {""
    }{count (·.confined == .yes)} confined, {count (·.charged == .yes)} charged, {""
    }{count (·.budget == .closed)} closed budgets, {count (·.work == .closed)} closed work, {""
    }{count (·.scratch == .closed)} closed scratch, {count (·.hyps == 0)} without hypotheses, {""
    }{count (·.problem == "derived")} derived problems, {""
    }{count (·.oracles == "declared")} with declared oracles, {""
    }{count (fun c => hasClaim c.claim && c.claim != "exempt")} with a randomized claim"

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
