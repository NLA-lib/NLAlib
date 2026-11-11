/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Tools.Program
public import NLAlib.Ops.Tools.Machines

/-!
# Tools: the runnable evaluator and the cost profiler

Diagnostic and compute support. **Raw entry point**: `NLAlib.Ops.Tools.profile I W τ s ρ m`,
for any tree
`s : Stmt Op Tst` (written by hand, produced by a builder, or linked by `Stmt.link`), any
interpretation `I`, workspace `W`, tape `τ`, environment `ρ` and initial memory `m`. It runs the
computable counted run `NLAlib.Ops.Tools.execC` (equal to the core's raw `evalCounted` by
`NLAlib.Ops.Tools.map_toSt_execC`) and returns a `NLAlib.Ops.Tools.Report`: the final memory,
the counts per key `(operation or query, dimensions)`, the scratch payload-byte peak, and
them the static bounds of the tree at `ρ.idx` (`stmtCost`, via
`NLAlib.Ops.Tools.staticAt_eq`,
and `stmtPeak`). `#eval` prints it. This raw entry point omits mandatory instrumentation
and format validation; use `profileProgram` for canonical execution diagnostics.

## Main results

`NLAlib.Ops.Tools.profileFrame` is the common case: whole buffers as operands
(`NLAlib.Ops.Tools.frameOf`), buffers given as lists (`NLAlib.Ops.Tools.memOf`).

A failed raw evaluation prints `FAILED` with its static bounds.
-/

@[expose] public section

namespace NLAlib.Ops.Tools

open NLAlib.Ops

variable {Op Tst K : Type}

/-- Count the entries of a list of keys, in the order of their first occurrence. -/
def tally [DecidableEq Op] [DecidableEq Tst] (l : List (Key Op Tst)) : List (Key Op Tst × ℕ) :=
  l.foldl (fun acc k =>
    if acc.any (·.1 == k) then acc.map fun e => if e.1 = k then (e.1, e.2 + 1) else e
    else acc ++ [(k, 1)]) []

/-- **A report of a run**: the outcome, the counts, the peak, and the static bounds. -/
structure Report (Op Tst K : Type) where
  /-- The final memory, or `none` if the run failed. -/
  out : Option (Mem K)
  /-- Per key: the count of the run and the static count of the tree. -/
  rows : List (Key Op Tst × ℕ × ℕ)
  /-- The peak of scratch payload bytes of the run. -/
  peak : Option ℕ
  /-- The static workspace of the tree. -/
  staticPk : ℕ

/-- Remove repeated entries, keeping the first. -/
def dedup' {α : Type} [DecidableEq α] (l : List α) : List α :=
  l.foldl (fun acc a => if acc.contains a then acc else acc ++ [a]) []

/-- **Run and profile a tree.** -/
def profile [DecidableEq Op] [DecidableEq Tst] (I : Interp Op Tst K) (W : Op → List ℕ → ℕ)
    (τ : Tape K) (s : Stmt Op Tst) (ρ : Env) (m : Mem K) : Report Op Tst K :=
  let r := execC I W τ s ρ (CSt.init m)
  let counts := tally ((r.map (·.log)).getD []).reverse
  let keys := dedup' (counts.map (·.1) ++ staticKeys s ρ.idx)
  { out := r.map (·.mem)
    rows := keys.map fun k => (k, ((counts.find? (·.1 == k)).map (·.2)).getD 0, staticAt s ρ.idx k)
    peak := r.map (·.peak)
    staticPk := stmtPeak W s ρ.idx }

/-- Run and profile a tree on whole buffers: dimensions `dims`, operands the buffers `args` of
the memory made of `bufs`. -/
def profileFrame [DecidableEq Op] [DecidableEq Tst] (I : Interp Op Tst K) (W : Op → List ℕ → ℕ)
    (τ : Tape K) (s : Stmt Op Tst) (dims : List ℕ) (args : List ℕ) (bufs : List (List (Option K))) :
    Report Op Tst K :=
  profile I W τ s (frameOf dims args) (memOf bufs)

/-- The run is within its static bounds: every count at most the static count, the peak at most
the static workspace. -/
def Report.within (r : Report Op Tst K) : Bool :=
  r.out.isSome && r.rows.all (fun e => e.2.1 ≤ e.2.2) &&
    r.peak.any (· ≤ r.staticPk)

/-- A key as text. -/
def showKey' [ShowKey Op] [ShowKey Tst] (k : Key Op Tst) : String :=
  s!"{ShowKey.showKey k.1} {k.2}"

/-- Pad a string on the right. -/
def padR (n : ℕ) (s : String) : String := s ++ String.ofList (List.replicate (n - s.length) ' ')

/-- A buffer as text, `_` for an uninitialised cell. -/
def showBuf [ToString K] (b : List (Option K)) : String :=
  "[" ++ ", ".intercalate (b.map fun c => (c.map toString).getD "_") ++ "]"

/-- The report as text. -/
def Report.render [ShowKey Op] [ShowKey Tst] [ToString K] (r : Report Op Tst K) : String :=
  let outcome := match r.out with
    | none => "FAILED (the run returned none)\n"
    | some m => "memory:\n" ++ String.join (m.store.zipIdx.map fun (b, i) =>
        s!"  buf {i}: {showBuf b}\n") ++ s!"  tape position: {m.pos}\n"
  let w := (r.rows.map fun e => (showKey' e.1).length).foldl max 10
  let head := s!"{padR w "key"}  {padR 7 "run"}  static\n"
  let rows := String.join (r.rows.map fun e =>
    let flag := if e.2.1 ≤ e.2.2 then "" else "  EXCEEDS"
    s!"{padR w (showKey' e.1)}  {padR 7 (toString e.2.1)}  {e.2.2}{flag}\n")
  let pk := s!"{padR w "peak bytes"}  {padR 7 ((r.peak.map toString).getD "-")}  {r.staticPk}\n"
  "RAW CONDITIONAL diagnostics (no format check or mandatory instrumentation)\n" ++
    outcome ++ "counts (raw run vs stmtCost):\n" ++ head ++ rows ++ pk ++
    s!"within static bounds: {r.within}"

instance [ShowKey Op] [ShowKey Tst] [ToString K] : ToString (Report Op Tst K) := ⟨Report.render⟩

instance [ShowKey Op] [ShowKey Tst] [ToString K] : Repr (Report Op Tst K) :=
  ⟨fun r _ => Std.Format.text r.render⟩

/-- Canonical diagnostics display full accounting and payload-byte resources, not a certificate. -/
def ProgramReport.render [DecidableEq Op] [DecidableEq Tst] [ShowKey Op] [ShowKey Tst]
    (r : ProgramReport Op Tst K) : String :=
  let banner := "CANONICAL execution diagnostics (not a certification proof)\n"
  match r.result with
  | none => banner ++ "FAILED (format/arity rejection or runtime failure)"
  | some st =>
    let rows := String.join ((tally st.log.reverse).map fun (k, n) =>
      s!"  {showKey' k}: {n}\n")
    banner ++ "full counts (operations, queries, bookkeeping):\n" ++ rows ++
      s!"scratch payload bytes: {st.peak}\n" ++
      s!"resident payload bytes: {r.memory}\n" ++
      s!"modeled work: {r.work}; sequential modeled span: {r.span}\n" ++
      s!"final tape position: {st.mem.pos}"

instance [DecidableEq Op] [DecidableEq Tst] [ShowKey Op] [ShowKey Tst] :
    ToString (ProgramReport Op Tst K) := ⟨ProgramReport.render⟩

instance [DecidableEq Op] [DecidableEq Tst] [ShowKey Op] [ShowKey Tst] :
    Repr (ProgramReport Op Tst K) := ⟨fun r _ => Std.Format.text r.render⟩

end NLAlib.Ops.Tools
