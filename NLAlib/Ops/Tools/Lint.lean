/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public meta import NLAlib.Ops.Tools.LintRegistry
public meta import NLAlib.Ops.Law
public meta import NLAlib.Ops.Profile

/-!
# Tools: the target linter

Canonical certification enforces a fixed symbolic program, realized
access models, total execution, format typing, and full resource accounting in the core. This
linter provides additional heuristic statement guidance for raw conditional proof consumers.

This is heuristic guidance for conditional judgments, not a certification boundary.
Canonical `Runs`, `Program.Certifies`, and `Impl.Meets` are recognized but reported as
unsupported by these conditional heuristics, never marked as passing them.

A **conditional headline** contains `ConditionalRuns`, `ConditionalRunsW`, `ConditionalRunsL`,
`ConditionalRunsLaw`, or `Impl.Triple`. For each conditional occurrence the linter checks:

* **(a) uniformity.** The program (the tree of `ConditionalRuns …`, or the implementation
  of `Impl.Triple`),
  with the tables of `Stmt.link` set apart, mentions no variable of the statement other than
  universally quantified sizes (`ℕ`), rational constants (`ℚ`), types and instances; and
  reaches no `noncomputable` definition (a function of the sizes that no machine computes).
* **(b) universality.** The interpretation is a variable of the statement (or `Interp.link` of
  one, or a registered model primitive, `ops_register_model`), not existentially quantified, not
  fixed by an equation, and constrained by at least one hypothesis (its contracts).
* **(c) joint witness.** The contract set of the statement is the set of `NLAlib` predicates of
  its hypotheses on the interpretation, closed under the parameters they share (the machine, the
  decoding, the law of the tape, …). Some witness theorem covers all of it at once. A witness is a
  theorem named `exists_…` (or registered by `ops_register_witness`). Its conclusion starts with
  one or more existential quantifiers, then states the `NLAlib` predicates together. The check
  uses predicate heads, including parent structures and field predicates. It matches declarations,
  not proof or axiom provenance. Core certification and the
  independent safety/axiom audit provide those guarantees. It does not compare arguments or
  verify parameter ranges, so distinct interpretations in the leading quantifiers
  can still satisfy the head check independently.
* **(d) closed-form counts.** The counts and the workspace of the statement reach no
  `Count.push`, `stmtCost`, `stmtPeak`, `staticCost`, `staticPeak`, `Count.upper` or `Profile.cost`.
* **(e) liberal headlines.** A liberal statement (`ConditionalRunsL`,
  `Impl.Triple … .liberal`) has a
  companion success statement (`ConditionalRuns`, `ConditionalRunsW`, `ConditionalRunsLaw`,
  or a total `Impl.Triple`) about the same program. The companion is in the same module or
  named `<name>_success`. Its conclusion must
  establish the success judgment, either directly or in a conjunction. Programs are compared
  syntactically up to renaming of parameters, including the arguments of linked tables.
  The companion's program and interpretation must be independent of existential choices.
* **(f) ξ only in tables.** The algorithm's tree (the program with its tables set apart) reaches
  no ξ-taking primitive (`ops_register_xi`, or a constructor named `…Xi`). An `Impl.Triple` about an
  implementation that a table or profile uses is exempt.

Commands: `#ops_lint c₁ c₂ …` (an error per conditional violation, information for a pass
or explicit `UNSUPPORTED` schema diagnostic) and
`#ops_lint_scan` (all headlines of the modules `NLAlib.Ops.*` other than the core files, the
program logic `NLAlib.Ops.Logic.*` (generic rules, not headlines) and the tools; one line per
theorem; an information).

## Main results

`#ops_lint` and `#ops_lint_scan` provide conditional statement guidance and explicit
schema diagnostics.
-/

@[expose] public section

meta section

namespace NLAlib.Ops.Tools.Lint

open Lean Meta Elab Command

/-- A headline judgment: its name, the binder of its program, whether it is liberal, and the
binders of its counts. -/
structure Head where
  /-- The constant. -/
  name : Name
  /-- The binder of the program. -/
  prog : Name
  /-- The binders of the counts and the workspace. -/
  counts : List Name
  /-- Liberal judgment. -/
  liberal : Bool

/-- The headline judgments. -/
def heads : List Head :=
  [⟨``NLAlib.Ops.ConditionalRuns, `s, [`B, `M], false⟩,
   ⟨``NLAlib.Ops.ConditionalRunsW, `s, [`M, `Q], false⟩,
   ⟨``NLAlib.Ops.ConditionalRunsL, `s, [], true⟩,
   ⟨``NLAlib.Ops.ConditionalRunsLaw, `s, [`B, `M], false⟩,
   ⟨``NLAlib.Ops.Impl.Triple, `R, [], false⟩,
   ⟨``NLAlib.Ops.Runs, `p, [], false⟩,
   ⟨``NLAlib.Ops.Program.Certifies, `p, [], false⟩,
   ⟨``NLAlib.Ops.Impl.Meets, `R, [], false⟩,
   ⟨``NLAlib.Ops.Profile.Refines, `P, [], false⟩]

/-- An occurrence of a headline judgment in a conclusion. -/
structure Occ where
  /-- The judgment. -/
  head : Head
  /-- Its arguments. -/
  args : Array Expr
  /-- Variables bound by universal quantifiers around it. -/
  vars : Array Expr
  /-- Variables bound by existential quantifiers around it. -/
  exVars : Array Expr
  /-- The local context in which the arguments were opened. -/
  lctx : LocalContext
  /-- The local instances of that context. -/
  localInsts : LocalInstances

/-- The argument of `c` bound to the binder `nm`. -/
def argByName (c : Name) (args : Array Expr) (nm : Name) : MetaM (Option Expr) := do
  forallTelescope (← getConstInfo c).type fun xs _ => do
    for h : i in [:xs.size] do
      if (← xs[i].fvarId!.getUserName) == nm then return args[i]?
    return none

/-- The occurrences of headline judgments in an expression. For success statements, only
descend through quantifiers and conjunctions. -/
def findOccs (e : Expr) (fuel : ℕ := 64) (successOnly := false)
    (vars : Array Expr := #[]) (ex : Array Expr := #[]) : MetaM (Array Occ) := do
  match fuel with
  | 0 => return #[]
  | f + 1 =>
    let e ← instantiateMVars e
    if let some c := e.getAppFn.constName? then
      if let some h := heads.find? (·.name == c) then
        return #[⟨h, e.getAppArgs, vars, ex, ← getLCtx, ← getLocalInstances⟩]
      if c == ``Exists && e.getAppNumArgs == 2 then
        return ← lambdaTelescope e.appArg! fun xs b => findOccs b f successOnly vars (ex ++ xs)
    match e with
    | .forallE .. => forallTelescope e fun xs b => findOccs b f successOnly (vars ++ xs) ex
    | .lam .. => lambdaTelescope e fun xs b => findOccs b f successOnly (vars ++ xs) ex
    | .app .. =>
      let c := e.getAppFn.constName?.getD .anonymous
      if c == ``And || (!successOnly && [``Or, ``Iff, ``Not].contains c) then
        e.getAppArgs.foldlM (fun acc a => return acc ++ (← findOccs a f successOnly vars ex)) #[]
      else return #[]
    | .mdata _ b => findOccs b f successOnly vars ex
    | _ => return #[]

/-- A constant of the library. -/
def inLib (n : Name) : Bool := (`NLAlib).isPrefixOf n

/-- The head constant of a statement, under its universal quantifiers. -/
def headOf (ty : Expr) : MetaM (Option Name) :=
  forallTelescope ty fun _ b => return (← instantiateMVars b).getAppFn.constName?

/-- The type of `e` is a table or a profile. -/
def isTableLike (ty : Expr) : MetaM Bool :=
  forallTelescope ty fun _ b => do
    let b ← whnfR b
    return b.isAppOf ``NLAlib.Ops.Profile || b.getAppFn.constName? == some ``NLAlib.Ops.Table ||
      b.isAppOf ``Sum && (b.getArg! 0).isAppOf ``NLAlib.Ops.Impl

/-- The library definitions reached from `e` through their values, not entering tables and
profiles. -/
def reach (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let mut todo := e.getUsedConstants.toList
  let mut seen : NameSet := {}
  let mut out := #[]
  let mut fuel := 2000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | c :: rest =>
      todo := rest
      if seen.contains c then continue
      seen := seen.insert c
      out := out.push c
      if !inLib c then continue
      let some (.defnInfo d) := env.find? c | continue
      if ← isTableLike d.type then continue
      todo := todo ++ d.value.getUsedConstants.toList
  return out

/-- Peel `Stmt.link`: the algorithm's tree and the tables. -/
def peelLink (s : Expr) (fuel : ℕ := 64) : Expr × Array Expr :=
  match fuel with
  | 0 => (s, #[])
  | f + 1 =>
    if s.isAppOf ``NLAlib.Ops.Stmt.link && s.getAppNumArgs ≥ 2 then
      let a := s.getAppArgs
      let (t, ts) := peelLink a[a.size - 1]! f
      (t, ts.push a[a.size - 2]!)
    else (s, #[])

/-- A variable a uniform program may mention: a size, a rational, a type or an instance. -/
def allowedInProg (x : Expr) : MetaM Bool := do
  let d ← x.fvarId!.getDecl
  if d.binderInfo.isInstImplicit then return true
  let ty ← instantiateMVars d.type
  if ty.isSort || (← isClass? ty).isSome then return true
  -- an operation or query variable: its type is a type variable (`o : Op`)
  if ty.isFVar then return true
  return ty.isConstOf ``Nat || ty.isConstOf ``Rat

/-- A type of data or sizes: its variables do not carry a contract. -/
def dataType (ty : Expr) : MetaM Bool := do
  if ty.isSort || (← isProp ty) then return true
  if (← isClass? ty).isSome then return true
  match ty.getAppFn.constName? with
  | some c => return [``Nat, ``Real, ``Rat, ``Int, ``Bool, ``List, ``Prod, ``Fin, ``Option,
      ``Matrix, ``NLAlib.Ops.Mem, ``NLAlib.Ops.Env, ``NLAlib.Ops.Tape, ``NLAlib.Ops.Store,
      ``NLAlib.Ops.Stmt, ``NLAlib.Ops.Mode].contains c
  | none => return false

/-- The ξ-taking primitives reached. -/
def xiPrims (cs : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  return cs.filter fun c => registered env .xi c ||
    (env.isConstructor c && match c with | .str _ s => s.endsWith "Xi" | _ => false)

/-- The `NLAlib` predicates of the fields of a structure (its parents' included). -/
def fieldHeads (h : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for f in getStructureFieldsFlattened env h (includeSubobjectFields := false) do
    let some proj := (findField? env h f).bind fun s => getProjFnForField? env s f | continue
    let ty := (← getConstInfo proj).type
    let hd ← forallTelescope ty fun _ b => do
      if ← isProp b then return (← instantiateMVars b).getAppFn.constName? else return none
    if let some c := hd then if inLib c then out := out.push c
  return out

namespace witnessHeads

/-- Flatten conjunctions without opening independent existential branches. -/
def conjuncts (e : Expr) (fuel : ℕ) : Array Expr :=
  match fuel with
  | 0 => #[]
  | f + 1 =>
    let e := e.consumeMData
    if e.isAppOfArity ``And 2 then
      conjuncts (e.getArg! 0) f ++ conjuncts (e.getArg! 1) f
    else #[e]

/-- Collect predicate heads only after opening the leading existential telescope. -/
def collect (e : Expr) (fuel : ℕ) (opened : Bool) : MetaM NameSet := do
  match fuel with
  | 0 => return {}
  | f + 1 =>
    let e := e.consumeMData
    if e.isAppOfArity ``Exists 2 then
      return ← lambdaTelescope e.appArg! fun _ b => collect b f true
    unless opened do return {}
    let mut s : NameSet := {}
    for p in conjuncts e 64 do
      if let some h ← headOf p then
        if inLib h then
          s := s.insert h
          if isStructure (← getEnv) h then
            for q in ← getAllParentStructures h do s := s.insert q
            for q in ← fieldHeads h do s := s.insert q
    return s

end witnessHeads

/-- The `NLAlib` predicates a witness declaration covers, including parent structures and fields.
Only leading existential quantifiers introduce witnesses for these predicates. -/
def witnessHeads (ty : Expr) : MetaM NameSet :=
  forallTelescope ty fun _ b => witnessHeads.collect b 64 false

/-- Public module interfaces represent imported theorems by their statement as axiom info.
This classifies declarations for guidance, not proof or axiom provenance. It neither trusts
nor constructs a certificate. -/
def proofStatement (ci : ConstantInfo) : Bool :=
  match ci with
  | .thmInfo _ | .axiomInfo _ => true
  | _ => false

/-- The witness theorems of the environment and what they cover. -/
def witnesses : MetaM (Array (Name × NameSet)) := do
  let env ← getEnv
  let mut out := #[]
  for (n, _) in env.constants.toList do
    let some ci := env.find? n | continue
    unless proofStatement ci do continue
    let isW := match n with
      | .str _ s => s.startsWith "exists_" && inLib n
      | _ => false
    if isW || registered env .witness n then
      out := out.push (n, ← witnessHeads ci.type)
  return out

/-- The contract set of a statement: the `NLAlib` predicates of the hypothesis types on the
interpretation `I`, closed under the parameters they share. -/
def contractSet (hyps : Array Expr) (I : Expr) : MetaM NameSet := do
  let mut vars : Array Expr := (collectFVars {} I).fvarIds.map Expr.fvar
  let mut used : Array Bool := hyps.map fun _ => false
  let mut set : NameSet := {}
  let mut changed := true
  while changed do
    changed := false
    for h : i in [:hyps.size] do
      if used[i]! then continue
      let ty := hyps[i]
      let some hd ← headOf ty | continue
      if !inLib hd then continue
      if !(vars.any fun v => ty.containsFVar v.fvarId!) then continue
      used := used.set! i true
      changed := true
      set := set.insert hd
      for x in (collectFVars {} ty).fvarIds do
        if !(← dataType (← instantiateMVars (← x.getType))) then vars := vars.push (.fvar x)
  return set

/-- Whether a hypothesis fixes the interpretation by a direct equality, possibly in a
conjunction. -/
def pinsInterp (I hyp : Expr) (fuel : ℕ := 64) : Bool :=
  match fuel with
  | 0 => false
  | f + 1 =>
    let hyp := hyp.consumeMData
    if hyp.isAppOfArity ``And 2 then
      pinsInterp I (hyp.getArg! 0) f || pinsInterp I (hyp.getArg! 1) f
    else if hyp.isAppOfArity ``Eq 3 then
      let lhs := (hyp.getArg! 1).consumeMData
      let rhs := (hyp.getArg! 2).consumeMData
      lhs != rhs && (lhs == I || rhs == I)
    else false

/-- The interpretation of an occurrence, and what is wrong with it. -/
def interpIssue (I : Expr) (ex hyps : Array Expr) (fuel : ℕ := 64) : MetaM (Option String) := do
  match fuel with
  | 0 => return some "the interpretation is too deeply linked"
  | f + 1 =>
    let I := I.consumeMData
    if hyps.any (pinsInterp I ·) then
      return some "a hypothesis fixes the interpretation by an equation"
    if I.isFVar then
      if ex.contains I then return some "the interpretation is existentially quantified"
      return none
    if I.isAppOf ``NLAlib.Ops.Interp.link && I.getAppNumArgs ≥ 2 then
      return ← interpIssue (I.getArg! (I.getAppNumArgs - 2)) ex hyps f
    if let some c := I.getAppFn.constName? then
      if registered (← getEnv) .model c then return none
    let hd := (I.getAppFn.constName?.map toString).getD "a non-constant"
    return some s!"the interpretation is a specific term (head `{hd}`), not a variable"

/-- A program key that abstracts over free variables in their order of occurrence. -/
def progKey (p : Expr) : Expr :=
  let p := p.consumeMData
  p.abstract ((collectFVars {} p).fvarIds.map Expr.fvar)

/-- The constants declared in the module `mod` (the current module included). -/
def modConsts (mod : Name) : CoreM (Array Name) := do
  let env ← getEnv
  if mod == env.mainModule then
    return env.constants.map₂.toList.toArray.map (·.1)
  match env.header.moduleNames.idxOf? mod with
  | some i => return env.header.moduleData[i]!.constNames
  | none => return #[]

/-- The module of a constant. -/
def modOf (n : Name) : CoreM Name := do
  let env ← getEnv
  return match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => env.mainModule

/-- The keys of the programs that a theorem establishes succeed. -/
def successKeysOf (n : Name) : MetaM (Array Expr) := do
  let env ← getEnv
  let some ci := env.find? n | return #[]
  unless proofStatement ci do return #[]
  let occs ← findOccs ci.type (successOnly := true)
  let mut keys := #[]
  for o in occs do
    if o.head.liberal then continue
    if o.head.name == ``NLAlib.Ops.Impl.Triple then
      let some md ← argByName o.head.name o.args `md | continue
      let md ← withLCtx o.lctx o.localInsts (whnf md)
      unless md.isConstOf ``NLAlib.Ops.Mode.total do continue
    let some p ← argByName o.head.name o.args o.head.prog | continue
    let some I ← argByName o.head.name o.args `I | continue
    if o.exVars.any (fun x => p.containsFVar x.fvarId! || I.containsFVar x.fvarId!) then continue
    keys := keys.push (progKey p)
  return keys

/-- The success statements of a module: the keys of their programs. -/
def successKeys (mod : Name) : MetaM ExprSet := do
  let mut s : ExprSet := {}
  for n in ← modConsts mod do
    for k in ← successKeysOf n do
      s := s.insert k
  return s

/-- The implementations used by tables and profiles. -/
def tableImpls : MetaM NameSet := do
  let env ← getEnv
  let mut s : NameSet := {}
  for (n, _) in env.constants.toList do
    let some (.defnInfo d) := env.find? n | continue
    if !inLib n then continue
    if !(← isTableLike d.type) then continue
    for c in d.value.getUsedConstants do s := s.insert c
  return s

/-- The forbidden constants of closed-form counts. -/
def countForbidden : List Name :=
  [``NLAlib.Ops.Count.push, ``NLAlib.Ops.stmtCost,
   ``NLAlib.Ops.stmtPeak, ``NLAlib.Ops.staticCost, ``NLAlib.Ops.staticPeak,
   ``NLAlib.Ops.Count.upper, ``NLAlib.Ops.Profile.cost]

/-- The context of a run of the linter: witnesses and table implementations, computed once. -/
structure Ctx where
  /-- The witnesses. -/
  wits : Array (Name × NameSet)
  /-- The implementations of tables. -/
  impls : NameSet

/-- Schemas that are recognized but are outside conditional headline guidance. -/
def schemaIssue (h : Head) : Option String :=
  if [``NLAlib.Ops.Runs, ``NLAlib.Ops.Program.Certifies,
      ``NLAlib.Ops.Impl.Meets].contains h.name then
    some ("canonical structural certificate: conditional (a)-(f) guidance does " ++
      "not inspect this schema; totality, formats, and accounting are enforced by the core")
  else if h.name == ``NLAlib.Ops.Profile.Refines then
    some ("conditional profile refinement: (a)-(f) guidance does not " ++
      "inspect this schema; it is not a canonical algorithm certificate")
  else none

/-- The violations of one occurrence, in the context of its binders. -/
def lintOcc (ctx : Ctx) (n : Name) (o : Occ) : MetaM (Array (String × String)) :=
  withLCtx o.lctx o.localInsts do
    let env ← getEnv
    let hyps ← o.vars.filterMapM fun x => do
      let ty ← instantiateMVars (← inferType x)
      if ← isProp ty then pure (some ty) else pure none
    let mut out : Array (String × String) := #[]
    let h := o.head
    if let some msg := schemaIssue h then return #[("schema", msg)]
    let some p ← argByName h.name o.args h.prog |
      return #[("schema", "recognized judgment has no supported program argument")]
    let some I ← argByName h.name o.args `I |
      return #[("schema", "recognized judgment has no supported interpretation argument")]
    let (tree, tables) := peelLink p
    -- (a)
    for x in (collectFVars {} (← instantiateMVars tree)).fvarIds do
      if o.exVars.contains (.fvar x) then
        out := out.push ("a", s!"the program mentions existential variable `{← x.getUserName}`")
      else unless ← allowedInProg (.fvar x) do
        out := out.push ("a", s!"the program mentions `{← x.getUserName}` : \
          {← ppExpr (← x.getType)}, not a size")
    for t in tables do
      for x in (collectFVars {} (← instantiateMVars t)).fvarIds do
        if o.exVars.contains (.fvar x) then
          out := out.push ("a", s!"a table mentions existential variable `{← x.getUserName}`")
        else unless ← allowedInProg (.fvar x) do
          out := out.push ("a", s!"a table mentions `{← x.getUserName}`, not a size")
    let cs ← reach tree
    for c in cs do
      if inLib c && isNoncomputable env c then
        out := out.push ("a", s!"the program reaches the noncomputable `{c}`")
    -- (b)
    if let some msg ← interpIssue I o.exVars hyps then out := out.push ("b", msg)
    -- (c)
    let cset ← contractSet hyps I
    let isModel := match I.getAppFn.constName? with
      | some c => registered env .model c
      | none => false
    let interpBad := out.any (·.1 == "b")
    if cset.isEmpty then
      unless isModel || interpBad do
        out := out.push ("b", "no hypothesis constrains the interpretation")
    else if !(ctx.wits.any fun w => cset.toList.all w.2.contains) then
      let score (w : Name × NameSet) := (cset.toList.filter w.2.contains).length
      let best := ctx.wits.foldl (fun acc w => if score w > score acc then w else acc)
        (`none, {})
      let miss := if score best = 0 then "" else
        s!"; best `{best.1}` misses {cset.toList.filter fun c => !best.2.contains c}"
      out := out.push ("c", s!"no joint witness for the contract set {cset.toList}{miss}")
    -- (d)
    for nm in h.counts do
      if let some e ← argByName h.name o.args nm then
        for c in ← reach e do
          if countForbidden.contains c then
            out := out.push ("d", s!"the bound `{nm}` is not in closed form: it uses `{c}`")
    -- (e)
    let mdLib ← do
      if h.name == ``NLAlib.Ops.Impl.Triple then
        match ← argByName h.name o.args `md with
        | some md => pure ((← whnf md).isConstOf ``NLAlib.Ops.Mode.liberal)
        | none => pure false
      else pure false
    if h.liberal || mdLib then
      let k := progKey p
      let named := (← successKeysOf (n.appendAfter "_success")).contains k
      let ok ← if named then pure true else pure ((← successKeys (← modOf n)).contains k)
      unless ok do
        out := out.push ("e", "a liberal statement without a success statement about the \
          same program")
    -- (f)
    let exempt := h.name == ``NLAlib.Ops.Impl.Triple &&
      ((p.getAppFn.constName?).map ctx.impls.contains).getD false
    unless exempt do
      for c in ← xiPrims cs do
        out := out.push ("f", s!"the algorithm's tree calls the ξ-taking primitive `{c}`")
    return out

/-- The violations of a theorem as `(rule, message)`. Diagnostics inspect the full environment;
exported module views may hide theorem bodies and private helper declarations. -/
def lintDecl (ctx : Ctx) (n : Name) :
    MetaM (Array (String × String)) := withoutExporting do
  let occs ← findOccs (← getConstInfo n).type
  if occs.isEmpty then return #[("schema", "no recognized headline judgment")]
  let out ← occs.foldlM (fun acc o => return acc ++ (← lintOcc ctx n o)) #[]
  return out.toList.eraseDups.toArray

/-- The headline theorems of the library modules other than the core, the program logic and the
tools. -/
def scanTargets : MetaM (Array Name) := withoutExporting do
  let env ← getEnv
  let mut out := #[]
  for mod in env.header.moduleNames do
    if !(`NLAlib.Ops).isPrefixOf mod || (`NLAlib.Ops.Tools).isPrefixOf mod ||
      (`NLAlib.Ops.Logic).isPrefixOf mod then continue
    if mod.getNumParts ≤ 3 then continue
    for n in ← modConsts mod do
      let some ci := env.find? n | continue
      unless proofStatement ci do continue
      if n.isInternalDetail then continue
      let occs ← findOccs ci.type
      if !occs.isEmpty then out := out.push n
  return out.qsort (·.toString < ·.toString)

/-- The context, computed once. -/
def mkCtx : MetaM Ctx := withoutExporting do return ⟨← witnesses, ← tableImpls⟩

/-- `#ops_lint c …`: check the statements of the theorems. -/
syntax (name := opsLint) "#ops_lint " ident+ : command

/-- Elaborate `#ops_lint`. -/
@[command_elab opsLint] def elabOpsLint : CommandElab := fun stx => liftTermElabM do
  let ctx ← mkCtx
  for id in stx[1].getArgs do
    let n ← realizeGlobalConstNoOverload id
    let vs ← lintDecl ctx n
    if vs.isEmpty then logInfoAt id m!"ops_lint: `{n}` passes (a)-(f)"
    for (r, msg) in vs do
      if r == "schema" then logInfoAt id m!"ops_lint UNSUPPORTED ({r}) `{n}`: {msg}"
      else logErrorAt id m!"ops_lint ({r}) `{n}`: {msg}"

/-- `#ops_lint_scan`: lint every headline of the library modules; one line per theorem. -/
syntax (name := opsLintScan) "#ops_lint_scan" : command

/-- Elaborate `#ops_lint_scan`. -/
@[command_elab opsLintScan] def elabOpsLintScan : CommandElab := fun _ => liftTermElabM do
  let ctx ← mkCtx
  let ts ← scanTargets
  let mut lines : Array String := #[]
  let mut bad : ℕ := 0
  let mut unsupported : ℕ := 0
  for n in ts do
    let vs ← lintDecl ctx n
    if vs.isEmpty then lines := lines.push s!"PASS {n}"
    else
      if vs.any (fun v => v.1 != "schema") then bad := bad + 1
      if vs.any (fun v => v.1 == "schema") then unsupported := unsupported + 1
      for (r, msg) in vs do
        let status := if r == "schema" then "UNSUPPORTED" else "FAIL"
        lines := lines.push s!"{status} ({r}) {n}: {msg}"
  let body := "\n".intercalate lines.toList
  logInfo (m!"ops_lint_scan: {ts.size} headlines, {bad} with conditional violations, " ++
    m!"{unsupported} with unsupported schemas\n{body}")

end NLAlib.Ops.Tools.Lint
