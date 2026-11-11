/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Ops.Tools.LintRegistry
import NLAlib.Ops.Law
import NLAlib.Ops.Profile

/-!
# Tools: the target linter

Outside the trusted base. The core cannot enforce that a theorem says what it should; the rules
of the Fable review (finding 2) and of the builder brief are rules on **statements**. This linter
checks them mechanically on the statement of a theorem (never its proof).

A **headline** is a theorem whose conclusion contains `Runs`, `RunsW`, `RunsL`, `RunsLaw` or
`Impl.Meets`. For each occurrence the linter checks:

* **(a) uniformity.** The program (the tree of `Runs …`, the implementation of `Impl.Meets`),
  with the tables of `Stmt.link` set apart, mentions no variable of the statement other than
  universally quantified sizes (`ℕ`), rational constants (`ℚ`), types and instances; and
  reaches no `noncomputable` definition (a function of the sizes that no machine computes).
* **(b) universality.** The interpretation is a variable of the statement (or `Interp.link` of
  one, or a registered model primitive, `ops_register_model`), not existentially quantified, not
  fixed by an equation, and constrained by at least one hypothesis (its contracts).
* **(c) joint witness.** The contract set of the statement is the set of `NLAlib` predicates of
  its hypotheses on the interpretation, closed under the parameters they share (the machine, the
  decoding, the law of the tape, …). Some witness theorem covers all of it at once. A witness is a
  theorem named `exists_…` (or registered by `ops_register_witness`); it covers the `NLAlib`
  predicates conjoined under its existential quantifiers, and their parent structures.
* **(d) closed-form counts.** The counts and the workspace of the statement reach no
  `Count.push`, `staticCost`, `staticPeak`, `Count.upper` or `Profile.cost`.
* **(e) liberal headlines.** A liberal statement (`RunsL`, `Impl.Meets … .liberal`) has a
  companion success statement (`Runs`, `RunsW`, `RunsLaw` or a total `Impl.Meets`) about the same
  program. The companion is in the same module or named `<name>_success`. Its conclusion must
  establish the success judgment, either directly or in a conjunction.
* **(f) ξ only in tables.** The algorithm's tree (the program with its tables set apart) reaches
  no ξ-taking primitive (`ops_register_xi`, or a constructor named `…Xi`). An `Impl.Meets` about an
  implementation that a table or profile uses is exempt.

Commands: `#ops_lint c₁ c₂ …` (an error per violation, an information if it passes) and
`#ops_lint_scan` (all headlines of the modules `NLAlib.Ops.*` other than the core files, the
program logic `NLAlib.Ops.Logic.*` (generic rules, not headlines) and the tools; one line per
theorem; an information).
-/

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
  [⟨``NLAlib.Ops.Runs, `s, [`B, `M], false⟩, ⟨``NLAlib.Ops.RunsW, `s, [`M, `Q], false⟩,
   ⟨``NLAlib.Ops.RunsL, `s, [], true⟩, ⟨``NLAlib.Ops.RunsLaw, `s, [`B, `M], false⟩,
   ⟨``NLAlib.Ops.Impl.Meets, `R, [], false⟩]

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

/-- The `NLAlib` predicates a witness covers, with their parent structures and the predicates of
their fields. -/
def witnessHeads (ty : Expr) : MetaM NameSet := do
  let rec conj (e : Expr) (fuel : ℕ) : MetaM (Array Expr) := do
    match fuel with
    | 0 => return #[e]
    | f + 1 =>
      let e ← instantiateMVars e
      if e.isAppOfArity ``Exists 2 then
        lambdaTelescope e.appArg! fun _ b => conj b f
      else if e.isAppOfArity ``And 2 then
        return (← conj (e.getArg! 0) f) ++ (← conj (e.getArg! 1) f)
      else return #[e]
  forallTelescope ty fun _ b => do
    let mut s : NameSet := {}
    for p in ← conj b 64 do
      if let some h ← headOf p then
        if inLib h then
          s := s.insert h
          if isStructure (← getEnv) h then
            for q in ← getAllParentStructures h do s := s.insert q
            for q in ← fieldHeads h do s := s.insert q
    return s

/-- The witness theorems of the environment and what they cover. -/
def witnesses : MetaM (Array (Name × NameSet)) := do
  let env ← getEnv
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    let some (.thmInfo _) := some ci | continue
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

/-- A program key: the head constants of the algorithm's tree and of its tables. -/
def progKey (p : Expr) : Option Name :=
  let (t, ts) := peelLink p
  t.getAppFn.constName?.map fun c =>
    ts.foldl (fun acc T => acc ++ (T.getAppFn.constName?.getD `_)) c

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
def successKeysOf (n : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some (.thmInfo ci) := env.find? n | return #[]
  let occs ← findOccs ci.type (successOnly := true)
  let mut keys := #[]
  for o in occs do
    if o.head.liberal then continue
    if o.head.name == ``NLAlib.Ops.Impl.Meets then
      let some md ← argByName o.head.name o.args `md | continue
      unless md.isConstOf ``NLAlib.Ops.Mode.total do continue
    if let some p ← argByName o.head.name o.args o.head.prog then
      if let some k := progKey p then keys := keys.push k
  return keys

/-- The success statements of a module: the keys of their programs. -/
def successKeys (mod : Name) : MetaM NameSet := do
  let mut s : NameSet := {}
  for n in ← modConsts mod do
    for k in ← successKeysOf n do
      s := s.insert k
  return s

/-- The implementations used by tables and profiles. -/
def tableImpls : MetaM NameSet := do
  let env ← getEnv
  let mut s : NameSet := {}
  for (n, ci) in env.constants.toList do
    let some (.defnInfo d) := some ci | continue
    if !inLib n then continue
    if !(← isTableLike d.type) then continue
    for c in d.value.getUsedConstants do s := s.insert c
  return s

/-- The forbidden constants of closed-form counts. -/
def countForbidden : List Name :=
  [``NLAlib.Ops.Count.push, ``NLAlib.Ops.staticCost, ``NLAlib.Ops.staticPeak,
   ``NLAlib.Ops.Count.upper, ``NLAlib.Ops.Profile.cost]

/-- The context of a run of the linter: witnesses and table implementations, computed once. -/
structure Ctx where
  /-- The witnesses. -/
  wits : Array (Name × NameSet)
  /-- The implementations of tables. -/
  impls : NameSet

/-- The violations of one occurrence, in the context of its binders. -/
def lintOcc (ctx : Ctx) (n : Name) (o : Occ) : MetaM (Array (String × String)) :=
  withLCtx o.lctx o.localInsts do
    let env ← getEnv
    let hyps ← o.vars.filterMapM fun x => do
      let ty ← instantiateMVars (← inferType x)
      if ← isProp ty then pure (some ty) else pure none
    let mut out : Array (String × String) := #[]
    let h := o.head
    let some p ← argByName h.name o.args h.prog | return #[]
    let some I ← argByName h.name o.args `I | return #[]
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
      if h.name == ``NLAlib.Ops.Impl.Meets then
        match ← argByName h.name o.args `md with
        | some md => pure (md.isConstOf ``NLAlib.Ops.Mode.liberal)
        | none => pure false
      else pure false
    if h.liberal || mdLib then
      let ok ← match progKey p with
        | some k => do
          if (← successKeysOf (n.appendAfter "_success")).contains k then pure true
          else pure ((← successKeys (← modOf n)).contains k)
        | none => pure false
      unless ok do
        out := out.push ("e", "a liberal statement without a success statement about the \
          same program")
    -- (f)
    let exempt := h.name == ``NLAlib.Ops.Impl.Meets &&
      ((p.getAppFn.constName?).map ctx.impls.contains).getD false
    unless exempt do
      for c in ← xiPrims cs do
        out := out.push ("f", s!"the algorithm's tree calls the ξ-taking primitive `{c}`")
    return out

/-- **The violations of a theorem**, as `(rule, message)`. -/
def lintDecl (ctx : Ctx) (n : Name) : MetaM (Array (String × String)) := do
  let occs ← findOccs (← getConstInfo n).type
  let out ← occs.foldlM (fun acc o => return acc ++ (← lintOcc ctx n o)) #[]
  return out.toList.eraseDups.toArray

/-- The headline theorems of the library modules other than the core, the program logic and the
tools. -/
def scanTargets : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for mod in env.header.moduleNames do
    if !(`NLAlib.Ops).isPrefixOf mod || (`NLAlib.Ops.Tools).isPrefixOf mod ||
      (`NLAlib.Ops.Logic).isPrefixOf mod then continue
    if mod.getNumParts ≤ 3 then continue
    for n in ← modConsts mod do
      let some (.thmInfo ci) := env.find? n | continue
      if n.isInternalDetail then continue
      let occs ← findOccs ci.type
      if !occs.isEmpty then out := out.push n
  return out.qsort (·.toString < ·.toString)

/-- The context, computed once. -/
def mkCtx : MetaM Ctx := return ⟨← witnesses, ← tableImpls⟩

/-- `#ops_lint c …`: check the statements of the theorems. -/
syntax (name := opsLint) "#ops_lint " ident+ : command

/-- Elaborate `#ops_lint`. -/
@[command_elab opsLint] def elabOpsLint : CommandElab := fun stx => liftTermElabM do
  let ctx ← mkCtx
  for id in stx[1].getArgs do
    let n ← realizeGlobalConstNoOverload id
    let vs ← lintDecl ctx n
    if vs.isEmpty then logInfoAt id m!"ops_lint: `{n}` passes (a)-(f)"
    for (r, msg) in vs do logErrorAt id m!"ops_lint ({r}) `{n}`: {msg}"

/-- `#ops_lint_scan`: lint every headline of the library modules; one line per theorem. -/
syntax (name := opsLintScan) "#ops_lint_scan" : command

/-- Elaborate `#ops_lint_scan`. -/
@[command_elab opsLintScan] def elabOpsLintScan : CommandElab := fun _ => liftTermElabM do
  let ctx ← mkCtx
  let ts ← scanTargets
  let mut lines : Array String := #[]
  let mut bad : ℕ := 0
  for n in ts do
    let vs ← lintDecl ctx n
    if vs.isEmpty then lines := lines.push s!"PASS {n}"
    else
      bad := bad + 1
      for (r, msg) in vs do lines := lines.push s!"FAIL ({r}) {n}: {msg}"
  let body := "\n".intercalate lines.toList
  logInfo m!"ops_lint_scan: {ts.size} headlines, {bad} with violations\n{body}"

end NLAlib.Ops.Tools.Lint
