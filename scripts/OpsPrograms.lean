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
  the same constant (below `Domain.cast` and `Domain.castOps`) but none unifies with this
  domain and model; `none` for a uniform model;
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

## Fixtures

The classification of one certificate is the function `classifyCert`, and the errors of its
line are `lineErrors`. Each run of this file also calls them on the artificial declarations of
`OpsCertificates.Fixtures` and compares the result with the tables `expectations` and
`ratchet`; a difference is an error naming the fixture, what was expected and what was
computed. The run prints `ops report fixtures: N cases`.

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
definitions that `opens` selects (those of the library). Memoised. -/
partial def cone (opens : Name → Bool) (env : Environment) (c : Name) :
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
      if opens c then
        let mut out : Bound × String := (.closed, "")
        for u in d.value.getUsedConstants do
          let v ← cone opens env u
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
def classify (opens : Name → Bool) (env : Environment) (e : Expr) :
    StateM (Std.HashMap Name (Bound × String)) (Bound × String) := do
  let mut out : Bound × String := (.closed, "")
  for u in e.getUsedConstants do
    let v ← cone opens env u
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

/-- The constant a domain is built from: the head of the domain, below `Domain.cast` and
`Domain.castOps` (the same domain read at another routine). -/
partial def domainHead (D : Expr) : MetaM (Option Name) := do
  let D ← whnfCore D
  let args := D.getAppArgs
  if D.isAppOf ``NLAlib.Ops.Routine.Domain.cast then
    if args.size ≥ 4 then domainHead args[args.size - 4]! else pure none
  else if D.isAppOf ``NLAlib.Ops.Routine.Domain.castOps then
    if args.size ≥ 6 then domainHead args[args.size - 6]! else pure none
  else
    match D.getAppFn.constName? with
    | some c =>
      -- an abbreviation of a cast domain
      match ← withTransparency .all (unfoldDefinition? D) with
      | some D' =>
        let D'' ← whnfCore D'
        if D''.isAppOf ``NLAlib.Ops.Routine.Domain.cast ||
            D''.isAppOf ``NLAlib.Ops.Routine.Domain.castOps then domainHead D''
        else pure (some c)
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
  -- a parameter that stays free is printed by its name
  for i in [0:mvars.size] do
    if let some nm := names[i]? then
      unless nm.hasMacroScopes do (try mvars[i]!.mvarId!.setUserName nm catch _ => pure ())
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
        -- a hypothesis about a free parameter is not one of the certificate, even when a
        -- value of the parameter would make it one
        for h in hyps do
          if !met && !ty.hasExprMVar then
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

/-- The declarations the check reads, among a list of constants. -/
structure Inventory where
  /-- The number of declarations of a program. -/
  programs : Nat := 0
  /-- The number of declarations of an `Ops.Algorithm`, generic ones included. -/
  algorithms : Nat := 0
  /-- The certificates: the `Ops.Algorithm` declarations for a model that is not a variable. -/
  certificates : Array Name := #[]
  /-- The certificates and the routine specifications, searched for `Routine.Spec.terminates`. -/
  follow : NameSet := {}
  /-- The randomized claims, each with the certificate declaration it is about. -/
  claims : Array (Name × Name) := #[]
  /-- The oracle declarations, each with the constant its domain is built from. -/
  oracles : Array (Name × Name) := #[]

/-- Read the constants `consts` whose name satisfies `keep`: the programs (with the E2 checks),
the certificates, the claims and the oracle declarations. -/
def scan (keep : Name → Bool) (consts : List (Name × ConstantInfo)) : MetaM Inventory := do
  let env ← getEnv
  let mut inv : Inventory := {}
  for (name, info) in consts do
    unless keep name do continue
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
      inv := { inv with programs := inv.programs + 1 }
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
      inv := { inv with algorithms := inv.algorithms + 1, follow := inv.follow.insert name }
      -- a constructor or combinator of the core is stated for an arbitrary model
      unless generic do inv := { inv with certificates := inv.certificates.push name }
    if head == some ``NLAlib.Ops.Routine.Spec then
      inv := { inv with follow := inv.follow.insert name }
    if head == some ``NLAlib.Ops.RandomizedClaim then
      if let some certificate := last then
        inv := { inv with claims := inv.claims.push (name, certificate) }
    if head == some ``NLAlib.Ops.Routine.Domain.Oracles then
      if let some dom := domain then inv := { inv with oracles := inv.oracles.push (name, dom) }
  return inv

/-- What the classification of one certificate reads besides the certificate. -/
structure Setting where
  /-- The constants whose definitions the search for the dependencies of a bound opens. -/
  opens : Name → Bool
  /-- The declarations the certificate is read against. -/
  inv : Inventory
  /-- The termination-only certificates that need no claim. -/
  exempt : List (Name × String)
  /-- The memory of the search for the dependencies of a bound. -/
  memo : IO.Ref (Std.HashMap Name (Bound × String))
  /-- The memory of the search for `Routine.Spec.terminates`. -/
  term : IO.Ref (Std.HashMap Name (Option Bool))

/-- The line of the certificate `name` and, when `wanted`, its report. This is the whole
classification of one certificate: the check of the library and the fixtures below call it. -/
def classifyCert (s : Setting) (name : Name) (wanted : Bool) : MetaM (Option Entry) := do
  let env ← getEnv
  let some info := env.find? name | return none
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
        let (b, reason) ← classify s.opens env e
        match b with
        | .manifest => return (.manifest, #[], s!"{label}: {reason}")
        | .unknown =>
          out := .unknown
          ns := ns.push s!"{label}: {reason}"
        | .closed => pure ()
      return (out, ns, "")
    let mut memo ← s.memo.get
    let (budget, work, scratch) ← match reduced with
      | some f =>
        let ((b, n1, r1), m1) := (cls "budget" [f[0]!]).run memo
        let ((w, n2, r2), m2) := (cls "work" [f[2]!, f[3]!]).run m1
        let ((sc, n3, r3), m3) := (cls "scratch" [f[1]!]).run m2
        memo := m3
        notes := notes ++ n1 ++ n2 ++ n3
        reasons := #[r1, r2, r3].filter (!·.isEmpty)
        pure (b, w, sc)
      | none =>
        notes := notes.push "the specification does not unfold to its fields"
        pure (Bound.unknown, Bound.unknown, Bound.unknown)
    s.memo.set memo
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
    let relatedOracles := s.inv.oracles.filter fun o => some o.2 == domName
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
    let relatedClaims := ((s.inv.claims.filter (·.2 == name)).map (·.1)).qsort
      (·.toString < ·.toString)
    let mut claimApps : Array Applied := #[]
    for c in relatedClaims do claimApps := claimApps.push (← applyAt c #[self] hyps)
    let ownClaims := (claimApps.filter (·.applies)).map (·.name)
    let (terminates, tmemo) := (usesTerminates env s.inv.follow name).run (← s.term.get)
    s.term.set tmemo
    if terminates.isNone then
      notes := notes.push "claim: the search for a termination-only specification did not finish"
    let claim :=
      if !ownClaims.isEmpty then
        String.intercalate "+" (ownClaims.toList.map (·.toString))
      else if (s.exempt.find? (·.1 == name)).isSome && terminates != some false then "exempt"
      else if terminates != some false then "required-missing"
      else if !relatedClaims.isEmpty then
        "related:" ++ String.intercalate "+" (relatedClaims.toList.map (·.toString))
      else "none"
    let line : CertLine := {
      name, hyps := hyps.size, uniform, confined, charged, budget, work, scratch, problem,
      derived, unstored, oracles := oraclesField, claim }
    -- the report
    let mut report := ""
    if wanted then
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
  return some entry

/-- The errors of one certificate line: against its recorded line `known` in the file `path`,
or, for a certificate that is not recorded, against the rule for new certificates. -/
def lineErrors (path : String) (known : Option CertLine) (c : CertLine) : List String :=
  (if c.claim == "required-missing" then
      [s!"the certificate {c.name} is termination-only and has no RandomizedClaim"]
    else []) ++
  match known with
  | some k =>
    if weaker k c then
      [s!"certificate {c.name} is weaker than {path} records:{""
        }\n  recorded: {k.format}\n  now:      {c.format}"]
    else []
  | none =>
    if c.confined == .yes && c.work == .closed && c.problem == "derived" then []
    else
      [s!"new certificate {c.name} must have a confined model, closed-form work {""
        }and span and a derived problem, or a reviewed line in {path}:\n  {c.format}"]

/-! ## Fixtures of the report

Artificial declarations, one per case of the classification, with the line and the parts of
the report each must give (`expectations`). They are declared here, in the file of the check,
and not in the library: the check of the library reads imported constants only, so they are
in no inventory and in no line of `scripts/ops_certificates.txt`. Their proofs are postulated
(`postulate`): what is tested is how the check reads the statements. -/

namespace Fixtures

open NLAlib NLAlib.Ops

/-- Fills the proof fields of the fixtures. It is never used in a resource field: an axiom
there makes the bound `unknown`, which `certAxiom` tests with an axiom of its own. -/
axiom postulate (p : Prop) : p

def routine : Routine Empty Empty := routine% [n] (x : n) → (z : 1) := .skip
def routine' : Routine Empty Empty := routine% [n] (x : n) → (z : 1) := .abort

/-- Every input is in memory. -/
def inputs : routine.Domain ℝ 1 2 where
  valid _ := True
  In d := Fin (d 0) → ℝ
  accepts _ _ := True
  slot d := ![.stored (Codec.vector (d 0)) id, .blank 1]
  fits := postulate _
  faithful := postulate _
  admitted := ⟨fun _ => 0, trivial⟩
  inhabited _ _ := ⟨fun _ => 0, trivial⟩

/-- One derived slot, and an input that no buffer holds. -/
def inputs2 : routine.Domain ℝ 1 2 where
  valid _ := True
  In d := (Fin (d 0) → ℝ) × ℝ
  accepts _ _ := True
  slot d := ![.stored (Codec.vector (d 0)) Prod.fst, .derived 1 (fun x => [x.2]) fun _ => rfl]
  Unstored _ := ℝ
  unstored _ x := x.2
  fits := postulate _
  faithful := postulate _
  admitted := ⟨fun _ => 0, trivial⟩
  inhabited _ _ := ⟨(fun _ => 0, 0), trivial⟩

abbrev problem : Problem ℝ 1 2 := inputs.problem
abbrev problem2 : Problem ℝ 1 2 := inputs2.problem
abbrev problemCast : Problem ℝ 1 2 := (inputs2.cast routine' rfl rfl).problem
abbrev problemOps : Problem ℝ 1 2 := (inputs.castOps routine' rfl rfl).problem
abbrev problem2Ops : Problem ℝ 1 2 := (inputs2.castOps routine' rfl rfl).problem

def handProblem : Problem ℝ 1 2 where
  formats _ := .cell
  valid _ := True
  Data _ := Unit
  admissible _ _ _ := True
  admitted := ⟨fun _ => 0, trivial⟩
  supply _ _ := ⟨(), fun _ => [], trivial⟩

def resources : ResourceModel Empty Empty where
  formats := [.cell]
  operation _ := ⟨[], []⟩
  testInputs q := nomatch q
  indexInputs q := nomatch q
  workspace _ _ := 0
  queryWorkspace q := nomatch q
  operationWork _ _ := 1
  operationSpan _ _ := 1
  queryWork q := nomatch q
  querySpan q := nomatch q
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le q := nomatch q
  core_span_le _ _ := le_rfl

/-- A model with no instance of the three classes. -/
def mkModel (P : Problem ℝ 1 2) : AccessModel Empty Empty P where
  word := 0
  operation _ _ o := nomatch o
  query _ _ q := nomatch q
  resources := resources
  realize := postulate _

/-- A model with the three instances. -/
def mkFull (P : Problem ℝ 1 2) : AccessModel Empty Empty P := mkModel P
instance (P : Problem ℝ 1 2) : (mkFull P).Uniform := postulate _
instance (P : Problem ℝ 1 2) : (mkFull P).Confined := postulate _
instance (P : Problem ℝ 1 2) : (mkFull P).Charged := postulate _

/-- The instances are found after one unfolding. -/
def modelFull : AccessModel Empty Empty problem := mkFull problem
/-- No instance: the definition unfolds to the constructor. -/
def modelPlain : AccessModel Empty Empty problem := mkModel problem
/-- One instance of the three. -/
def modelConfined : AccessModel Empty Empty problem := mkModel problem
instance : modelConfined.Confined := postulate _
/-- Two models of one domain, one with declared oracles. -/
def modelA : AccessModel Empty Empty problem := mkModel problem
def modelB : AccessModel Empty Empty problem := mkModel problem
def modelE (_ : ℕ) : AccessModel Empty Empty problem := mkModel problem
def modelOps : AccessModel Empty Empty problemOps := mkModel _
/-- A chain of definitions longer than the search for an instance unfolds. -/
def deep0 : AccessModel Empty Empty problem := mkModel problem
def deep1 := deep0
def deep2 := deep1
def deep3 := deep2
def deep4 := deep3
def deep5 := deep4
def deep6 := deep5
def deep7 := deep6
def deep8 := deep7
instance : deep0.Uniform := postulate _

def program : Program Empty Empty 1 2 := routine.close 1 2

abbrev Sizes := Fin 1 → ℕ

def spec (P : Problem ℝ 1 2) (budget : Sizes → Count (Empty ⊕ Bookkeeping) Empty)
    (scratch work span : Sizes → ℕ) : Specification Empty Empty P where
  budget := budget
  scratch := scratch
  work := work
  span := span
  memory _ := 0
  good _ _ _ _ _ := True

/-- Explicit polynomials in the sizes. -/
def closedSpec (P : Problem ℝ 1 2) : Specification Empty Empty P :=
  spec P (fun _ => 0) (fun d => 8 * d 0) (fun d => d 0 ^ 2 + 3 * d 0) fun d => d 0

/-- The specification with one field replaced. -/
def workSpec (work : Sizes → ℕ) : Specification Empty Empty problem :=
  spec problem (fun _ => 0) (fun _ => 0) work fun d => d 0

/-- The proof is postulated. The model is a variable, so this is not a certificate. -/
def cert {P : Problem ℝ 1 2} (M : AccessModel Empty Empty P) (S : Specification Empty Empty P) :
    Algorithm M S := ⟨program, postulate _⟩

/-- A certificate whose definition mentions a routine specification. -/
def withSpec {P : Problem ℝ 1 2} {M : AccessModel Empty Empty P}
    {S : Specification Empty Empty P} (_ : Routine.Spec ℝ) (A : Algorithm M S) :
    Algorithm M S := A

def claim {P : Problem ℝ 1 2} {M : AccessModel Empty Empty P} {S : Specification Empty Empty P}
    (A : Algorithm M S) : RandomizedClaim A where
  law _ _ _ _ _ _ := True
  admits _ _ := True
  interprets _ _ _ := True
  event _ _ _ _ _ := True
  bound _ _ := 1
  realizable := postulate _
  holds := postulate _

def oracles {R : Routine Empty Empty} (D : R.Domain ℝ 1 2)
    (M : AccessModel Empty Empty D.problem) : D.Oracles M :=
  ⟨[], postulate _, postulate _, postulate _⟩

/-! ### Claims: general, specialised, with further hypotheses -/

def certP (p : ℕ) : Algorithm modelFull (workSpec fun d => d 0 + p) := cert _ _
def claimGeneral (p : ℕ) : RandomizedClaim (certP p) := claim _
def claimSpecial : RandomizedClaim (certP 0) := claim _
def claimExtra (p : ℕ) (_h : 0 < p) : RandomizedClaim (certP p) := claim _

def certOnlySpecial (p : ℕ) : Algorithm modelFull (workSpec fun d => d 0 + p) := cert _ _
def claimOnlySpecial : RandomizedClaim (certOnlySpecial 0) := claim _

def certH (p : ℕ) (_h : 0 < p) : Algorithm modelFull (workSpec fun d => d 0 + p) := cert _ _
def claimH (p q : ℕ) (h : 0 < p) (_again : 0 < p) (_small : p < 5) (_other : 0 < q) :
    RandomizedClaim (certH p h) := claim _

/-! ### Oracles: two models on one domain, a further hypothesis, none, a cast domain -/

def certA : Algorithm modelA (closedSpec _) := cert _ _
def certB : Algorithm modelB (closedSpec _) := cert _ _
def oraclesA : inputs.Oracles modelA := oracles _ _
def certE (p : ℕ) : Algorithm (modelE p) (closedSpec _) := cert _ _
def oraclesE (p : ℕ) (_h : 0 < p) : inputs.Oracles (modelE p) := oracles _ _
def certMissing : Algorithm (mkModel problem2) (closedSpec _) := cert _ _
def certOps : Algorithm modelOps (closedSpec _) := cert _ _
def oraclesOps : (inputs.castOps routine' rfl rfl).Oracles modelOps := oracles _ _
def certOpsOther : Algorithm (mkModel problem2Ops) (closedSpec _) := cert _ _

/-! ### Resource fields -/

def certClosed : Algorithm modelFull (closedSpec _) := cert _ _
noncomputable def certStaticCost : Algorithm modelFull (spec problem (fun d => staticCost program d)
    (fun _ => 0) (fun d => resources.work (staticCost program d)) fun d => d 0) := cert _ _
def certStmtPeak : Algorithm modelFull (spec problem (fun _ => 0)
    (fun d => stmtPeak (fun _ _ => 0) program.body (List.ofFn d)) (fun d => d 0) fun d => d 0) :=
  cert _ _
def certCountPoly : Algorithm modelFull
    (workSpec fun d => CountPoly.eval (List.ofFn d) program.countPoly) := cert _ _
/-- The span alone is read off the tree. -/
def certWorkCoefficient : Algorithm modelFull (spec problem (fun _ => 0) (fun _ => 0)
    (fun d => d 0) fun _ => program.body.workCoefficient) := cert _ _
def readsTree (d : Sizes) : ℕ := program.body.workCoefficient * d 0
def readsTwice (d : Sizes) : ℕ := readsTree d + 1
/-- The tree is two definitions below the field. -/
def certTwoLevels : Algorithm modelFull (workSpec fun d => readsTwice d + d 0) := cert _ _
noncomputable def certChoose : Algorithm modelFull
    (workSpec fun _ => Classical.choose (⟨0, trivial⟩ : ∃ _ : ℕ, True)) := cert _ _
def certNatFind : Algorithm modelFull
    (workSpec fun _ => Nat.find (⟨0, trivial⟩ : ∃ _ : ℕ, True)) := cert _ _
noncomputable def certSSup : Algorithm modelFull (workSpec fun d => sSup {n | n ≤ d 0}) :=
  cert _ _
axiom axiomBound : ℕ
opaque opaqueBound : ℕ
noncomputable def certAxiom : Algorithm modelFull (workSpec fun _ => axiomBound) := cert _ _
def certOpaque : Algorithm modelFull (workSpec fun _ => opaqueBound) := cert _ _
/-- The specification is a variable: it does not unfold to its fields. -/
def certSpecParam (S : Specification Empty Empty problem) : Algorithm modelFull S := cert _ _
/-- A tree in the span wins over a constant that cannot be inspected in the work. -/
noncomputable def certUnknownAndManifest : Algorithm modelFull (spec problem (fun _ => 0)
    (fun _ => axiomBound) (fun _ => opaqueBound) fun _ => program.body.workCoefficient) :=
  cert _ _

/-! ### Model classes -/

def certPlain : Algorithm modelPlain (closedSpec _) := cert _ _
def certConfined : Algorithm modelConfined (closedSpec _) := cert _ _
def certDeep : Algorithm deep8 (closedSpec _) := cert _ _

/-! ### Termination-only certificates -/

def termSpec : Routine.Spec ℝ := .terminates fun _ _ _ => True
/-- Through a routine specification of its own. -/
def certTermNone : Algorithm modelFull (closedSpec _) := withSpec termSpec (cert _ _)
def certTermRelated (p : ℕ) : Algorithm modelFull (workSpec fun d => d 0 + p) :=
  withSpec (.terminates fun _ _ _ => True) (cert _ _)
def claimTermRelated : RandomizedClaim (certTermRelated 0) := claim _
def certTermClaimed : Algorithm modelFull (closedSpec _) := withSpec termSpec (cert _ _)
def claimTerm : RandomizedClaim certTermClaimed := claim _
def certTermExempt : Algorithm modelFull (closedSpec _) := withSpec termSpec (cert _ _)
/-- Listed as exempt, but not termination-only: the list does not apply. -/
def certExemptNotTerm : Algorithm modelFull (closedSpec _) := cert _ _

/-! ### Problems -/

def certDerived : Algorithm (mkFull problem2) (closedSpec _) := cert _ _
def certCast : Algorithm (mkFull problemCast) (closedSpec _) := cert _ _
def certCastOps : Algorithm (mkFull problem2Ops) (closedSpec _) := cert _ _
def certHand : Algorithm (mkFull handProblem) (closedSpec _) := cert _ _

end Fixtures

/-- The fixtures that the fixture pass treats as exempt. -/
def fixtureExempt : List (Name × String) :=
  [(`OpsCertificates.Fixtures.certTermExempt, "fixture"),
    (`OpsCertificates.Fixtures.certExemptNotTerm, "fixture")]

/-- What one fixture certificate must give. Names are written without the namespace
`OpsCertificates.Fixtures`. The defaults are those of a certificate in good order: the three
classes, closed bounds, the problem of `Fixtures.inputs`, no oracle, no claim, no error. -/
structure Expect where
  name : String
  hyps : Nat := 0
  /-- `uniform`, `confined`, `charged`. -/
  classes : String := "yes yes yes"
  /-- `budget`, `work`, `scratch`. -/
  bounds : String := "closed closed closed"
  /-- `problem`, `derived`, `unstored`. -/
  problem : String := "derived 0 no"
  oracles : String := "none"
  claim : String := "none"
  /-- A word of each error the line gives as a certificate that is not recorded. -/
  errors : List String := []
  /-- Pieces of text the report must contain. -/
  report : List String := []

def Expect.line (e : Expect) : String :=
  s!"{e.name} hyps={e.hyps} classes={e.classes} bounds={e.bounds} problem={e.problem} {""
    }oracles={e.oracles} claim={e.claim}"

/-- The same summary of a computed line. -/
def CertLine.summary (c : CertLine) (name : String) : String :=
  s!"{name} hyps={c.hyps} classes={c.uniform.format} {c.confined.format} {c.charged.format} {""
    }bounds={c.budget.format} {c.work.format} {c.scratch.format} {""
    }problem={c.problem} {c.derived} {c.unstored} oracles={c.oracles} claim={c.claim}"

/-- The expected classification of every fixture certificate. To add a case: declare the
certificate (and its claims or oracles) in `Fixtures` and add its row here; a fixture
certificate without a row is an error. -/
def expectations : List Expect := [
  -- claims
  { name := "certP", claim := "claimExtra+claimGeneral",
    report := ["claim claimGeneral [applies to this instance]",
      "claim claimExtra [applies to this instance]",
      "hypothesis of the claim, NOT of the certificate: (_h : 0 < p)",
      "claim claimSpecial [related declaration; about another instance",
      "it is about: certP 0", "where it differs: 0  (this instance: p)"] },
  { name := "certOnlySpecial", claim := "related:claimOnlySpecial",
    report := ["it is about: certOnlySpecial 0", "where it differs: 0  (this instance: p)"] },
  { name := "certH", hyps := 1, claim := "claimH",
    report := ["hypothesis (_h : 0 < p)", "parameter of the claim: (q : ℕ)",
      "hypothesis shared with the certificate: (_again : 0 < p)",
      "hypothesis of the claim, NOT of the certificate: (_small : p < 5)",
      "hypothesis of the claim, NOT of the certificate: (_other : 0 < ?q)"] },
  -- oracles
  { name := "certA", classes := "no no no", oracles := "declared", errors := ["new certificate"],
    report := ["oracles oraclesA [applies to this domain and model]",
      "oracles oraclesE [related declaration; not about this domain and model]"] },
  { name := "certB", classes := "no no no", oracles := "related", errors := ["new certificate"],
    report := ["oracles oraclesA [related declaration; not about this domain and model]",
      "it is about: modelA  (this instance: modelB)"] },
  { name := "certE", classes := "no no no", oracles := "declared", errors := ["new certificate"],
    report := ["oracles oraclesE [applies to this domain and model]",
      "hypothesis NOT of the certificate: (_h : 0 < p)"] },
  { name := "certMissing", classes := "no no no", problem := "derived 1 yes",
    oracles := "missing", errors := ["new certificate"] },
  { name := "certOps", classes := "no no no", oracles := "declared",
    errors := ["new certificate"],
    report := ["oracles oraclesOps [applies to this domain and model]",
      "oracles oraclesA [related declaration; not about this domain and model]"] },
  { name := "certOpsOther", classes := "no no no", problem := "derived 1 yes",
    oracles := "missing", errors := ["new certificate"] },
  -- resource fields
  { name := "certClosed" },
  { name := "certStaticCost", bounds := "manifest manifest closed",
    errors := ["new certificate"],
    report := ["manifest because budget: NLAlib.Ops.staticCost reads a tree",
      "manifest because work: NLAlib.Ops.staticCost reads a tree"] },
  { name := "certStmtPeak", bounds := "closed closed manifest",
    report := ["manifest because scratch: NLAlib.Ops.stmtPeak reads a tree"] },
  { name := "certCountPoly", bounds := "closed manifest closed", errors := ["new certificate"],
    report := ["manifest because work: NLAlib.Ops.Program.countPoly reads a tree"] },
  { name := "certWorkCoefficient", bounds := "closed manifest closed",
    errors := ["new certificate"],
    report := ["manifest because work: NLAlib.Ops.Stmt.workCoefficient reads a tree"] },
  { name := "certTwoLevels", bounds := "closed manifest closed", errors := ["new certificate"],
    report := ["manifest because work: NLAlib.Ops.Stmt.workCoefficient reads a tree"] },
  { name := "certChoose", bounds := "closed unknown closed", errors := ["new certificate"],
    report := ["note: work: non-constructive Classical.choose"] },
  { name := "certNatFind", bounds := "closed unknown closed", errors := ["new certificate"],
    report := ["note: work: non-constructive Nat.find"] },
  { name := "certSSup", bounds := "closed unknown closed", errors := ["new certificate"],
    report := ["note: work: non-constructive SupSet.sSup"] },
  { name := "certAxiom", bounds := "closed unknown closed", errors := ["new certificate"],
    report := ["note: work: axiom axiomBound"] },
  { name := "certOpaque", bounds := "closed unknown closed", errors := ["new certificate"],
    report := ["note: work: opaque opaqueBound"] },
  { name := "certSpecParam", bounds := "unknown unknown unknown", errors := ["new certificate"],
    report := ["note: the specification does not unfold to its fields", "specification: S"] },
  { name := "certUnknownAndManifest", bounds := "closed manifest unknown",
    errors := ["new certificate"],
    report := ["manifest because work: NLAlib.Ops.Stmt.workCoefficient reads a tree",
      "note: scratch: axiom axiomBound"] },
  -- model classes
  { name := "certPlain", classes := "no no no", oracles := "related",
    errors := ["new certificate"] },
  { name := "certConfined", classes := "no yes no", oracles := "related" },
  { name := "certDeep", classes := "unknown unknown unknown", oracles := "related",
    errors := ["new certificate"],
    report := ["note: uniform: the model was not unfolded to the end"] },
  -- termination-only certificates
  { name := "certTermNone", claim := "required-missing", errors := ["termination-only"] },
  { name := "certTermRelated", claim := "required-missing", errors := ["termination-only"],
    report := ["claim claimTermRelated [related declaration; about another instance"] },
  { name := "certTermClaimed", claim := "claimTerm" },
  { name := "certTermExempt", claim := "exempt" },
  { name := "certExemptNotTerm" },
  -- problems
  { name := "certDerived", problem := "derived 1 yes",
    report := ["derived slot: NLAlib.Ops.Slot.derived 1 (fun x => [x.2])",
      "unstored inputs: fun x x_1 => x_1.2"] },
  { name := "certCast", problem := "derived 1 yes" },
  { name := "certCastOps", problem := "derived 1 yes" },
  { name := "certHand", problem := "handwritten - -", errors := ["new certificate"],
    report := ["admissible: fun x x_1 x_2 => True"] }]

/-- A line in good order, and the same line with one field changed. -/
def goodLine : String :=
  "C hyps=1 uniform=yes confined=yes charged=yes budget=closed work=closed scratch=closed " ++
    "problem=derived derived=0 unstored=no oracles=declared claim=C.claim"

def goodLineWith (key value : String) : String :=
  " ".intercalate <| (goodLine.splitOn " ").map fun f =>
    if f.startsWith (key ++ "=") then s!"{key}={value}" else f

/-- The comparison with a recorded line: the field, its recorded value, its value now, and
whether that is an error. Every other field is that of `goodLine` on both sides. -/
def ratchet : List (String × String × String × Bool) := [
  ("hyps", "1", "1", false), ("hyps", "1", "2", true), ("hyps", "1", "0", false),
  ("uniform", "yes", "no", true), ("uniform", "yes", "unknown", true),
  ("uniform", "no", "yes", false), ("uniform", "unknown", "no", false),
  ("confined", "yes", "no", true), ("confined", "no", "yes", false),
  ("charged", "yes", "unknown", true), ("charged", "no", "yes", false),
  ("budget", "closed", "manifest", true), ("budget", "closed", "unknown", true),
  ("budget", "manifest", "closed", false), ("budget", "manifest", "unknown", false),
  ("work", "closed", "manifest", true), ("work", "unknown", "closed", false),
  ("scratch", "closed", "unknown", true), ("scratch", "manifest", "closed", false),
  ("problem", "derived", "handwritten", true), ("problem", "handwritten", "derived", false),
  ("derived", "0", "2", false), ("unstored", "no", "yes", false),
  ("oracles", "declared", "missing", true), ("oracles", "declared", "related", true),
  ("oracles", "declared", "none", false), ("oracles", "related", "missing", false),
  ("oracles", "missing", "declared", false),
  ("claim", "C.claim", "none", true), ("claim", "C.claim", "related:C.claim", true),
  ("claim", "C.claim", "required-missing", true), ("claim", "C.claim", "C.other", false),
  ("claim", "C.claim", "exempt", false), ("claim", "related:C.claim", "none", false),
  ("claim", "none", "C.claim", false)]

/-- Run the fixtures: classify every certificate of `Fixtures` and compare with
`expectations`, then the comparisons of `ratchet`. Returns the number of cases; every failure
is an error that names the fixture, what was expected and what was computed. -/
def runFixtures (lib : Array Bool) : MetaM Nat := do
  let env ← getEnv
  let ns := `OpsCertificates.Fixtures
  let consts := env.constants.map₂.toList.filter fun c => ns.isPrefixOf c.1
  let inv ← scan (fun _ => true) consts
  let setting : Setting := {
    opens := fun c => inLibrary lib env c || ns.isPrefixOf c,
    inv, exempt := fixtureExempt,
    memo := ← IO.mkRef {}, term := ← IO.mkRef {} }
  let short (s : String) : String :=
    (s.replace "OpsCertificates.Fixtures." "").replace "Fixtures." ""
  let mut cases := 0
  for name in inv.certificates.qsort (·.toString < ·.toString) do
    cases := cases + 1
    let nm := short name.toString
    let some e := expectations.find? (·.name == nm)
      | logError m!"ops report fixture {nm}: no expectation is written for it"
    let some entry ← classifyCert setting name true
      | logError m!"ops report fixture {nm}: not classified"
    let actual := short (entry.line.summary nm)
    unless actual == e.line do
      logError m!"ops report fixture {nm}: line\n  expected: {e.line}\n  actual:   {actual}"
    let errors := lineErrors "the fixture file" none entry.line
    unless errors.length == e.errors.length &&
        (errors.zip e.errors).all (fun (a, b) => (a.splitOn b).length > 1) do
      logError m!"ops report fixture {nm}: errors\n  expected: {e.errors}\n  actual:   {errors}"
    let report := short entry.report
    for piece in e.report do
      unless (report.splitOn piece).length > 1 do
        logError m!"ops report fixture {nm}: report\n  expected to contain: {piece}{""
          }\n  actual:\n{report}"
  for e in expectations do
    unless inv.certificates.any (fun c => short c.toString == e.name) do
      logError m!"ops report fixture {e.name}: expected, but not a certificate of the fixtures"
  for (key, recorded, now, bad) in ratchet do
    cases := cases + 1
    let (some k, some c) := (CertLine.parse (goodLineWith key recorded),
        CertLine.parse (goodLineWith key now))
      | logError m!"ops report fixture ratchet {key}: the line does not parse"
    unless k.format == goodLineWith key recorded do
      logError m!"ops report fixture ratchet {key}: a line is not read back as written\n  {""
        }expected: {goodLineWith key recorded}\n  actual:   {k.format}"
    let errors := lineErrors "the fixture file" (some k) c
    unless errors.isEmpty != bad do
      logError m!"ops report fixture ratchet {key}: recorded {recorded}, now {now}\n  {""
        }expected: {if bad then "an error" else "no error"}\n  actual:   {errors}"
  return cases

end OpsCertificates

open OpsCertificates in
run_cmd liftTermElabM do
  let env ← getEnv
  let lib := libraryModules env
  for moduleName in env.header.moduleNames do
    if (`NLAlib.Computation).isPrefixOf moduleName ||
        (`NLAlib.Matrix.Computation).isPrefixOf moduleName ||
        (`NLAlib.RandomMatrix.Computation).isPrefixOf moduleName then
      logError m!"retired execution module is still imported: {moduleName}"
  -- imported constants only: the fixtures of this file are in no inventory of the library
  let inv ← scan (inLibrary lib env) env.constants.map₁.toList
  if inv.programs = 0 ∨ inv.algorithms = 0 then
    logError m!"missing Ops coverage: {inv.programs} programs, {inv.algorithms} certificates"
  let reportSel ← IO.getEnv "OPS_CERTIFICATES_REPORT"
  let wanted (name : Name) : Bool := match reportSel with
    | none => false
    | some s => s == "1" || s.isEmpty || (name.toString.splitOn s).length > 1
  let setting : Setting := {
    opens := inLibrary lib env, inv, exempt,
    memo := ← IO.mkRef {}, term := ← IO.mkRef {} }
  let mut entries : Array Entry := #[]
  for name in inv.certificates.qsort (·.toString < ·.toString) do
    if let some entry ← classifyCert setting name (wanted name) then
      entries := entries.push entry
  let lines := entries.map (·.line)
  for e in entries do
    for n in e.notes do logInfo m!"ops certificate {e.line.name}: {n}"
  for (name, _) in exempt do
    unless inv.certificates.contains name do
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
    for e in lineErrors path.toString (known.find? (·.name == c.name)) c do logError m!"{e}"
  for k in known do
    unless lines.any (·.name == k.name) do
      logError m!"{path} lists {k.name}, which is not a certificate"
  let count (p : CertLine → Bool) := (lines.filter p).size
  logInfo m!"ops programs: {inv.programs} program declarations, {""
    }{inv.algorithms} certificate declarations"
  logInfo m!"ops certificates: {count (·.uniform == .yes)} uniform, {""
    }{count (·.confined == .yes)} confined, {count (·.charged == .yes)} charged, {""
    }{count (·.budget == .closed)} closed budgets, {count (·.work == .closed)} closed work, {""
    }{count (·.scratch == .closed)} closed scratch, {count (·.hyps == 0)} without hypotheses, {""
    }{count (·.problem == "derived")} derived problems, {""
    }{count (·.oracles == "declared")} with declared oracles, {""
    }{count (fun c => hasClaim c.claim && c.claim != "exempt")} with a randomized claim"
  -- the fixtures of the report
  let cases ← runFixtures lib
  logInfo m!"ops report fixtures: {cases} cases"

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

/-! # The trusted base of an Ops certificate

A certificate is checked by Lean's kernel, so its proof need not be read. What a reader must
believe is what its statement means: the definitions the statement is made of. This section
computes them and compares them with `scripts/ops_trusted_base.txt`, so that the set is known,
has a size, and cannot change without the change being seen.

## The roots

The roots are the forms a claim of the library takes, for every problem, model and bound:

* `Ops.Algorithm` (a certificate), with `Ops.Program.Certifies`, `Ops.Specification`,
  `Ops.Problem`, `Ops.AccessModel` and `Ops.exec` (they are reached from it; they are named so
  that a renaming is noticed);
* `Ops.Reference.Execution` and `Ops.Reference.Accepts`: the same execution stated by inference
  rules, which a reader may use in place of the evaluator
  (`Ops.Reference.execution_iff_exec`);
* `Ops.RandomizedClaim`, with `Ops.Algorithm.FailsAtMost` and `Ops.TapeModel.Realizable`;
* `Ops.Routine.Domain`, `Ops.Routine.Domain.problem`, `Ops.Routine.Domain.Oracles` and
  `Ops.Routine.Domain.Checked`: a derived problem, declared unstored inputs, and the form of
  the readable `_checked` statements;
* `Ops.AccessModel.Uniform`, `.Confined`, `.Charged`: the properties of a model that the
  certificate report prints.

What a particular certificate adds (its codecs, its tape law, its machine and the contracts of
its operations, its bounds) is not here: it is read with that certificate, and
`OPS_CERTIFICATES_REPORT` prints it. Tactics, static bounds, routines, their judgment and
linking are not here either: they produce certificates, which are checked against these roots.

## The closure

From a declaration the closure follows the constants of its type and, for a definition, of its
body; for an inductive type or a structure, of the types of its constructors. A theorem is not
followed and not listed: no statement depends on a proof. A constructor, projection or recursor
stands for its type. Declarations that Lean generates (matchers, recursion auxiliaries,
`casesOn`, derived `decEq`) are followed and not listed, and their content is hashed with the
declaration they belong to. Only declarations of the library are listed; Mathlib and Lean are
counted.

## The file

One line for each declaration, sorted:

`Name kind=… module=… root=yes|no route=… type=… body=…`

* `route`: `evaluator` if the declaration is reached from `Ops.exec` and not from
  `Ops.Reference.Execution`; `reference` for the converse; `execution` if from both; `claim`
  if from neither (problems, models, specifications, randomized claims);
* `type`, `body`: hashes of the statement and of the content. A changed `type` is a changed
  statement; a changed `body` alone is a changed definition with the same statement.

The check fails when the computed lines differ from the file, naming each declaration that
entered, left or changed. `OPS_TRUSTED_BASE_WRITE=1` rewrites the file; `OPS_TRUSTED_BASE_FILE`
names another file. Source lines are reported in the summary and not recorded, so that editing
a docstring does not change the file. -/

namespace OpsTrustedBase

/-- The roots: the forms of the claims of the library (see the section docstring). -/
def roots : List Name := [
  `NLAlib.Ops.Algorithm, `NLAlib.Ops.Program.Certifies, `NLAlib.Ops.Specification,
  `NLAlib.Ops.Problem, `NLAlib.Ops.AccessModel, `NLAlib.Ops.exec,
  `NLAlib.Ops.Reference.Execution, `NLAlib.Ops.Reference.Accepts,
  `NLAlib.Ops.RandomizedClaim, `NLAlib.Ops.Algorithm.FailsAtMost,
  `NLAlib.Ops.TapeModel.Realizable,
  `NLAlib.Ops.Routine.Domain, `NLAlib.Ops.Routine.Domain.problem,
  `NLAlib.Ops.Routine.Domain.Oracles, `NLAlib.Ops.Routine.Domain.Checked,
  `NLAlib.Ops.AccessModel.Uniform, `NLAlib.Ops.AccessModel.Confined,
  `NLAlib.Ops.AccessModel.Charged]

/-- The execution by the evaluator. -/
def evaluatorRoot : Name := `NLAlib.Ops.exec
/-- The execution by the reference rules. -/
def referenceRoot : Name := `NLAlib.Ops.Reference.Execution

/-- Whether Lean generated the declaration: it is followed and not listed. -/
def generated (env : Environment) (c : Name) : Bool :=
  c.isInternalDetail || isAuxRecursor env c || isNoConfusion env c || isRecCore env c ||
  isMatcherCore env c || c.components.any (fun n => n == `brecOn || n == `below) ||
  (match c with
    | .str p s => s == "ctorIdx" || s == "toCtorIdx" || s == "sizeOf_spec" || s == "injEq" ||
        s == "inj" || (s == "decEq" && (match p with
          | .str _ t => t.startsWith "inst" | _ => false))
    | _ => false)

/-- The declaration a reader reads for the constant: a constructor, a projection or a recursor
stands for its type. -/
def owner (env : Environment) (c : Name) : Name :=
  match env.find? c with
  | some (.ctorInfo v) => v.induct
  | some (.recInfo v) => v.getMajorInduct
  | _ => match env.getProjectionFnInfo? c with
    | some p => (match env.find? p.ctorName with | some (.ctorInfo v) => v.induct | _ => c)
    | none => c

/-- The expressions a declaration's meaning consists of: its type, and its body or the types
of its constructors. -/
def content (env : Environment) (ci : ConstantInfo) : Expr × List Expr :=
  match ci with
  | .inductInfo v => (ci.type, v.ctors.filterMap fun k => (env.find? k).map (·.type))
  | .defnInfo v => (ci.type, [v.value])
  | _ => (ci.type, [])

/-- The result of a closure: the declarations of the library that were reached (generated ones
included) and the constants outside it that they mention. -/
structure Closure where
  reached : NameSet := {}
  outside : NameSet := {}

/-- The closure from `todo`. `keep` says which constants are of the library; `stop` is not
entered. -/
partial def close (env : Environment) (keep : Name → Bool) (stop : NameSet) (todo : List Name)
    (acc : Closure := {}) : Closure :=
  match todo with
  | [] => acc
  | c :: rest =>
    let c := owner env c
    if acc.reached.contains c || stop.contains c then close env keep stop rest acc else
    match env.find? c with
    | none => close env keep stop rest acc
    | some ci =>
      if !keep c then close env keep stop rest { acc with outside := acc.outside.insert c } else
      if ci.isTheorem then close env keep stop rest acc else
      let (type, body) := content env ci
      let used := (type :: body).foldl (fun l e => e.getUsedConstants.toList ++ l) []
      close env keep stop (used ++ rest) { acc with reached := acc.reached.insert c }

/-- The listed declarations of a closure, sorted. -/
def Closure.listed (env : Environment) (c : Closure) : Array Name :=
  (c.reached.toArray.filter (!generated env ·)).qsort (·.toString < ·.toString)

/-- The generated declarations reached from `c` through generated declarations only. -/
partial def generatedOf (env : Environment) (keep : Name → Bool) (c : Name)
    (acc : NameSet := {}) : NameSet := Id.run do
  let some ci := env.find? c | return acc
  let (type, body) := content env ci
  let mut acc := acc
  for e in type :: body do
    for u in e.getUsedConstants do
      if keep u && generated env u && !acc.contains u then
        acc := generatedOf env keep u (acc.insert u)
  return acc

/-- Eight hexadecimal digits of a hash. -/
def hex (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 (h.toNat % 4294967296))
  String.ofList (List.replicate (8 - s.length) '0') ++ s

/-- The hashes of the statement and of the content of a declaration. The content includes the
generated declarations that belong to it, in the order of their names. -/
def hashes (env : Environment) (keep : Name → Bool) (c : Name) : UInt64 × UInt64 :=
  match env.find? c with
  | none => (0, 0)
  | some ci =>
    let (type, body) := content env ci
    let own := body.foldl (fun h e => mixHash h e.hash) 7
    let gens := (generatedOf env keep c).toArray.qsort (·.toString < ·.toString)
    let all := gens.foldl (fun h g =>
      match env.find? g with
      | none => h
      | some gi =>
        let (t, b) := content env gi
        (t :: b).foldl (fun h e => mixHash h e.hash) (mixHash h (hash g))) own
    (type.hash, all)

/-- One line of the file. -/
structure Line where
  name : Name
  kind : String
  modName : Name
  root : Bool
  route : String
  type : String
  body : String
  deriving BEq

/-- The line as it is written. -/
def Line.format (l : Line) : String :=
  s!"{l.name} kind={l.kind} module={l.modName} root={if l.root then "yes" else "no"} {""
    }route={l.route} type={l.type} body={l.body}"

/-- The line that was written. -/
def Line.parse (s : String) : Option Line := do
  let name :: rest := s.splitOn " " | none
  let get (key : String) : Option String :=
    rest.findSome? fun kv => match kv.splitOn "=" with
      | [k, v] => if k == key then some v else none
      | _ => none
  some { name := name.toName, kind := ← get "kind", modName := (← get "module").toName,
         root := (← get "root") == "yes", route := ← get "route", type := ← get "type",
         body := ← get "body" }

/-- The kind of a listed declaration. -/
def kindOf (env : Environment) (c : Name) : MetaM String := do
  match env.find? c with
  | some (.inductInfo _) =>
    return if isClass env c then "class" else if isStructure env c then "structure"
      else "inductive"
  | some (.defnInfo _) => return if ← isInstance c then "instance" else "def"
  | some (.opaqueInfo _) => return "opaque"
  | some (.axiomInfo _) => return "axiom"
  | _ => return "other"

/-- The number of source lines of a declaration, with its docstring; zero when unknown. -/
def sourceLines (c : Name) : MetaM Nat := do
  match ← findDeclarationRanges? c with
  | some r => return r.range.endPos.line - r.range.pos.line + 1
  | none => return 0

/-- The differences between the recorded and the computed lines, as messages. -/
def differences (path : String) (known computed : Array Line) : List String := Id.run do
  let mut out : List String := []
  for c in computed do
    match known.find? (·.name == c.name) with
    | none => out := s!"{c.name} entered the trusted base ({c.kind}, {c.modName})" :: out
    | some k =>
      if k.type != c.type then out := s!"the statement of {c.name} changed" :: out
      else if k.body != c.body then
        out := s!"the definition of {c.name} changed (same statement)" :: out
      else if k != c then
        out := s!"the line of {c.name} changed: {c.format}" :: out
  for k in known do
    unless computed.any (·.name == k.name) do
      out := s!"{k.name} left the trusted base" :: out
  if out.isEmpty then return []
  return (s!"{path} is not the trusted base of the certificates. A reviewer reads the change, {""
    }then OPS_TRUSTED_BASE_WRITE=1 records it (docs/contributing/checks.md, \"The trusted {""
    }base\")") :: out.reverse

namespace Fixtures

/-- A type of the fixtures. -/
inductive T | a | b
/-- A definition by cases, with a generated matcher. -/
def f : T → Nat | .a => 0 | .b => 1
/-- The same statement and matcher, another value. -/
def f' : T → Nat | .a => 0 | .b => 2
/-- A definition that only a proof mentions. -/
def onlyInProof : Nat := 3
theorem proof : 0 = f .a := by have := onlyInProof; rfl
/-- A definition whose body mentions a theorem. -/
def k : { n : Nat // n = f .a } := ⟨0, proof⟩
/-- A structure with a proof field. -/
structure S where
  x : T
  h : f x = f x
/-- A definition that is not reached. -/
def unused : Nat := 5
/-- The root: it uses a projection of `S`, a constructor of `T` and `k`. -/
def root (s : S) : Nat := k.1 + f s.x + f T.b

end Fixtures

/-- The closure rule on the fixtures: a body is followed, a proof is not, a constructor and a
projection stand for their type, generated declarations are not listed, and the content hash
sees a changed value under the same statement. Returns the number of checks. -/
def runFixtures (env : Environment) : Except String Nat := do
  let keep (c : Name) : Bool := (`OpsTrustedBase.Fixtures).isPrefixOf c
  let got := (close env keep {} [`OpsTrustedBase.Fixtures.root]).listed env
  let want := #[`OpsTrustedBase.Fixtures.S, `OpsTrustedBase.Fixtures.T,
    `OpsTrustedBase.Fixtures.f, `OpsTrustedBase.Fixtures.k, `OpsTrustedBase.Fixtures.root]
  unless got == want do throw s!"closure of the fixture root: {got}, expected {want}"
  let stopped := (close env keep (NameSet.empty.insert `OpsTrustedBase.Fixtures.k)
    [`OpsTrustedBase.Fixtures.root]).listed env
  unless stopped == want.filter (· != `OpsTrustedBase.Fixtures.k) do
    throw s!"closure with a stop: {stopped}"
  let (t, b) := hashes env keep `OpsTrustedBase.Fixtures.f
  let (t', b') := hashes env keep `OpsTrustedBase.Fixtures.f'
  unless t == t' do throw "the statements of f and f' have different hashes"
  if b == b' then throw "the contents of f and f' have the same hash"
  let line (n : Name) (ty bo : String) : Line :=
    { name := n, kind := "def", modName := `M, root := false, route := "claim", type := ty,
      body := bo }
  let d := differences "file" #[line `a "1" "1", line `b "1" "1", line `c "1" "1"]
    #[line `a "1" "1", line `b "2" "1", line `c "1" "2", line `d "1" "1"]
  unless d.length == 4 do throw s!"differences: {d}"
  unless (differences "file" #[line `a "1" "1"] #[line `a "1" "1"]).isEmpty do
    throw "equal lines differ"
  unless Line.parse (line `a "1" "2").format == some (line `a "1" "2") do
    throw "a line does not parse to itself"
  return 6

end OpsTrustedBase

open OpsTrustedBase in
run_cmd liftTermElabM do
  let env ← getEnv
  let lib := OpsCertificates.libraryModules env
  let keep := OpsCertificates.inLibrary lib env
  for r in roots do
    unless (env.find? r).isSome do logError m!"trusted base: the root {r} does not exist"
  let all := close env keep {} roots
  let evaluator := close env keep {} [evaluatorRoot]
  let reference := close env keep {} [referenceRoot]
  let names := all.listed env
  let mut lines : Array Line := #[]
  let mut total := 0
  let mut evalOnly := (0, 0)
  let mut refOnly := (0, 0)
  let mut modules : NameSet := {}
  for c in names do
    let some i := env.getModuleIdxFor? c | continue
    let modName := env.header.moduleNames[i.toNat]!
    modules := modules.insert modName
    let kind ← kindOf env c
    if kind == "axiom" then logError m!"trusted base: {c} is an axiom"
    let inE := evaluator.reached.contains c
    let inR := reference.reached.contains c
    let n ← sourceLines c
    total := total + n
    if inE && !inR then evalOnly := (evalOnly.1 + 1, evalOnly.2 + n)
    if inR && !inE then refOnly := (refOnly.1 + 1, refOnly.2 + n)
    let (t, b) := hashes env keep c
    let route := if inE && inR then "execution" else if inE then "evaluator"
      else if inR then "reference" else "claim"
    let isRoot := roots.contains c
    lines := lines.push
      { name := c, kind := kind, modName := modName, root := isRoot, route := route,
        type := hex t, body := hex b }
  let path : System.FilePath := match ← IO.getEnv "OPS_TRUSTED_BASE_FILE" with
    | some p => p
    | none => "scripts" / "ops_trusted_base.txt"
  if (← IO.getEnv "OPS_TRUSTED_BASE_WRITE").isSome then
    IO.FS.writeFile path (String.intercalate "\n" (lines.map Line.format).toList ++ "\n")
  let mut known : Array Line := #[]
  if ← path.pathExists then
    known := (← IO.FS.lines path).filterMap Line.parse
  for e in differences path.toString known lines do logError m!"{e}"
  -- the base if the reference rules were the definition: the evaluator is not entered
  let withoutEvaluator := (close env keep (NameSet.empty.insert evaluatorRoot) roots).listed env
  logInfo m!"ops trusted base: {lines.size} declarations in {modules.size} modules, {""
    }{total} source lines, {all.outside.size} constants of Mathlib and Lean; {""
    }the evaluator reaches {(evaluator.listed env).size} ({evalOnly.1} only it, {""
    }{evalOnly.2} lines), the reference rules {(reference.listed env).size} ({refOnly.1} only {""
    }they, {refOnly.2} lines); without the evaluator {withoutEvaluator.size}"
  match runFixtures env with
  | .ok n => logInfo m!"ops trusted base fixtures: {n} checks"
  | .error e => logError m!"trusted base fixture: {e}"
