/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Ops.Tools.Lint
import NLAlib.Ops.Examples.Gemm
import NLAlib.Ops.Examples.StochRound

/-!
# Tools: fixtures of the target linter

Outside the trusted base. Each cheat of the Fable review is a true theorem here whose
**statement** breaks one rule; `#guard_msgs` records what `#ops_lint` says of it. The accepted
statements are headlines of the examples.
-/

namespace NLAlib.Ops.Tools.LintFixtures

open NLAlib.Ops NLAlib.Ops.Examples

variable {K : Type}

theorem runs_skip {Op Tst : Type} (I : Interp Op Tst K) (W : Op → List ℕ → ℕ) (τ : Tape K)
    (ρ : Env) (m : Mem K) : Runs I W τ .skip ρ m 0 0 (· = m) :=
  ⟨St.init m, rfl, le_rfl, le_rfl, rfl⟩

/-! ### (a) A program that depends on the memory -/

/-- A tree chosen by looking at the memory (here `skip` either way). -/
def memProg (m : Mem K) : Stmt ScalarOp Empty := if m.pos = 0 then .skip else .skip

theorem cheat_memProg {M : Machine K} {u : ℝ} {dec : K → ℝ} (_hM : StdModel u dec M)
    {I : Interp ScalarOp Empty K} (_hI : IsScalar M I) (W : ScalarOp → List ℕ → ℕ) (τ : Tape K)
    (ρ : Env) (m : Mem K) : Runs I W τ (memProg m) ρ m 0 0 (· = m) := by
  unfold memProg
  split <;> exact runs_skip I W τ ρ m

theorem cheat_nestedMem {M : Machine K} {u : ℝ} {dec : K → ℝ} (_hM : StdModel u dec M)
    {I : Interp ScalarOp Empty K} (_hI : IsScalar M I) (W : ScalarOp → List ℕ → ℕ) (τ : Tape K)
    (ρ : Env) : True ∧ (∀ m, Runs I W τ (memProg m) ρ m 0 0 (· = m)) :=
  ⟨trivial, cheat_memProg _hM _hI W τ ρ⟩

/-- A loop with the number of repetitions baked into the tree. -/
def sizeProg (n : ℕ) : Stmt ScalarOp Empty := .loop (.const n) .skip

theorem cheat_existsSize {M : Machine K} {u : ℝ} {dec : K → ℝ} (_hM : StdModel u dec M)
    {I : Interp ScalarOp Empty K} (_hI : IsScalar M I) (W : ScalarOp → List ℕ → ℕ) (τ : Tape K)
    (ρ : Env) (m : Mem K) : ∃ n, Runs I W τ (sizeProg n) ρ m 0 0 (· = m) :=
  ⟨0, St.init m, rfl, le_rfl, le_rfl, rfl⟩

/-! ### (b) An existential and a specific interpretation -/

theorem cheat_exists :
    ∃ I : Interp ScalarOp Empty ℚ, Runs I (fun _ _ => 0) (fun _ _ => 0) .skip ⟨[], []⟩ ⟨[], 0⟩
      0 0 (· = ⟨[], 0⟩) :=
  ⟨Interp.ofFns fun _ => .const 0, runs_skip _ _ _ _ _⟩

theorem cheat_specific :
    Runs (Interp.ofFns fun _ => .const 0 : Interp ScalarOp Empty ℚ) (fun _ _ => 0)
      (fun _ _ => 0) .skip ⟨[], []⟩ ⟨[], 0⟩ 0 0 (· = ⟨[], 0⟩) :=
  runs_skip _ _ _ _ _

theorem cheat_linkPinned {M : Machine K} {u : ℝ} {dec : K → ℝ} (_hM : StdModel u dec M)
    {I : Interp ScalarOp Empty K} (_hI : IsScalar M I)
    (_hfix : True ∧ I = Interp.ofFns (fun _ => .un some)) (W : ScalarOp → List ℕ → ℕ)
    (τ : Tape K) (ρ : Env) (m : Mem K) :
    Runs (I.link (Table.id : Table ScalarOp ScalarOp Empty)) W τ .skip ρ m 0 0 (· = m) :=
  runs_skip _ W τ ρ m

theorem runs_nested {M : Machine K} {u : ℝ} {dec : K → ℝ} (_hM : StdModel u dec M)
    (W : ScalarOp → List ℕ → ℕ) (τ : Tape K) (ρ : Env) (m : Mem K) :
    True ∧ (∀ I : Interp ScalarOp Empty K, IsScalar M I → Runs I W τ .skip ρ m 0 0 (· = m)) :=
  ⟨trivial, fun I _ => runs_skip I W τ ρ m⟩

/-! ### (c) A contract without a witness -/

/-- A contract that no interpretation meets. -/
structure Oracle (I : Interp ScalarOp Empty K) : Prop where
  /-- Never. -/
  never : False

/-- One addition. -/
def oneAdd : Stmt ScalarOp Empty := .call .add [] [⟨0, .const 0⟩, ⟨0, .const 0⟩] [⟨0, .const 0⟩]

theorem cheat_noWitness {I : Interp ScalarOp Empty K} (hI : Oracle I) (W : ScalarOp → List ℕ → ℕ)
    (τ : Tape K) (ρ : Env) (m : Mem K) : Runs I W τ oneAdd ρ m 0 0 fun _ => False :=
  hI.never.elim

/-- An interpretation with a constant test. -/
def fixedTest (b : Bool) : Interp Empty Unit Unit where
  call := fun _ _ _ _ _ _ => none
  test := fun _ _ _ _ => some b
  index := fun _ _ _ => none

/-- The test accepts on the empty memory. -/
def Accepts (I : Interp Empty Unit Unit) : Prop := I.test () [] [] ⟨[], 0⟩ = some true

/-- The test rejects on the empty memory. -/
def Rejects (I : Interp Empty Unit Unit) : Prop := I.test () [] [] ⟨[], 0⟩ = some false

theorem exists_separateWitnesses : (∃ I, Accepts I) ∧ (∃ J, Rejects J) :=
  ⟨⟨fixedTest true, rfl⟩, ⟨fixedTest false, rfl⟩⟩

theorem exists_nestedSeparateWitnesses : ∃ I, Accepts I ∧ (∃ J, Rejects J) := by
  obtain ⟨⟨I, hI⟩, hJ⟩ := exists_separateWitnesses
  exact ⟨I, hI, hJ⟩

theorem cheat_separateWitnesses (I : Interp Empty Unit Unit) (_hA : Accepts I) (_hR : Rejects I)
    (W : Empty → List ℕ → ℕ) (τ : Tape Unit) (ρ : Env) (m : Mem Unit) :
    Runs I W τ .skip ρ m 0 0 (· = m) :=
  runs_skip I W τ ρ m

/-! ### (e) A liberal headline over a table of aborts -/

/-- Every scalar operation implemented by `abort`. -/
def abortT : Table ScalarOp ScalarOp Empty := fun _ => .inl ⟨0, 2, 1, .abort⟩

theorem cheat_liberalAbort {M : Machine K} {u : ℝ} {dec : K → ℝ} (_hM : StdModel u dec M)
    {I : Interp ScalarOp Empty K} (_hI : IsScalar M I) (τ : Tape K) (ρ : Env) (m : Mem K) :
    RunsL I τ (oneAdd.link abortT) ρ m fun _ => False := by
  intro m' h
  simp only [oneAdd, abortT, Stmt.link, Impl.Fits, List.length_nil, List.length_cons, and_self,
    if_true, run, Option.bind_eq_some_iff] at h
  obtain ⟨_, -, _, -, h⟩ := h
  split_ifs at h

/-- A matching name alone is insufficient. -/
theorem cheat_liberalAbort_success : True := trivial

/-- A disjunction containing a total run can hold when the run fails. -/
theorem cheat_disjunctiveCompanion (I : Interp ScalarOp Empty K) (W : ScalarOp → List ℕ → ℕ)
    (τ : Tape K) (ρ : Env) (m : Mem K) :
    True ∨ Runs I W τ (oneAdd.link abortT) ρ m 0 0 (fun _ => False) :=
  Or.inl trivial

/-- An implementation that always fails. -/
def abortImpl : Impl ScalarOp Empty := ⟨0, 2, 1, .abort⟩

theorem cheat_liberalCertificate {M : Machine K} {u : ℝ} {dec : K → ℝ} (_hM : StdModel u dec M)
    {I : Interp ScalarOp Empty K} (_hI : IsScalar M I) (C : Contract K)
    (hfit : ∀ d ins outs τ m, (C.on .liberal d ins outs τ m).pre m →
      d.length = 0 ∧ ins.length = 2 ∧ outs.length = 1) : abortImpl.Meets I .liberal C :=
  Impl.meets_liberal_abort 0 2 1 I C hfit

/-- Wrapping the liberal mode in `id` supplies no evidence of success. -/
theorem cheat_nonliteralModeCompanion {M : Machine K} {u : ℝ} {dec : K → ℝ}
    (_hM : StdModel u dec M) {I : Interp ScalarOp Empty K} (_hI : IsScalar M I) (C : Contract K)
    (hfit : ∀ d ins outs τ m, (C.on .liberal d ins outs τ m).pre m →
      d.length = 0 ∧ ins.length = 2 ∧ outs.length = 1) : abortImpl.Meets I (id .liberal) C :=
  cheat_liberalCertificate _hM _hI C hfit

/-! ### (f) A ξ-taking primitive in an algorithm -/

/-- A tree that contains `sraddXi` (in a branch never taken). -/
def xiProg : Stmt SrLo Empty :=
  .ifZero (.const 1) (.call .sraddXi [] [⟨0, .const 0⟩, ⟨0, .const 0⟩, ⟨0, .const 0⟩]
    [⟨0, .const 0⟩])

theorem cheat_xi [MeasurableSpace K] {u : ℝ} {dec : K → ℝ} {μ : MeasureTheory.Measure K}
    {f : K → K → K → K} (_hf : SrModel u dec μ f) {I : Interp SrLo Empty K} (_hI : IsSrLo f I)
    (W : SrLo → List ℕ → ℕ) (τ : Tape K) (ρ : Env) (m : Mem K) :
    Runs I W τ xiProg ρ m 0 0 (· = m) :=
  ⟨St.init m, rfl, le_rfl, le_rfl, rfl⟩

/-! ### Each cheat is rejected by its rule -/

/--
error: ops_lint (a) `NLAlib.Ops.Tools.LintFixtures.cheat_memProg`: the program mentions `m` :
Mem K, not a size
-/
#guard_msgs (whitespace := lax) in
#ops_lint cheat_memProg

/--
error: ops_lint (a) `NLAlib.Ops.Tools.LintFixtures.cheat_nestedMem`: the program mentions `m` :
Mem K, not a size
-/
#guard_msgs (whitespace := lax) in
#ops_lint cheat_nestedMem

/--
error: ops_lint (a) `NLAlib.Ops.Tools.LintFixtures.cheat_existsSize`: the program mentions
existential variable `n`
-/
#guard_msgs (whitespace := lax) in
#ops_lint cheat_existsSize

/--
error: ops_lint (b) `NLAlib.Ops.Tools.LintFixtures.cheat_exists`: the interpretation is
existentially quantified
-/
#guard_msgs (whitespace := lax) in
#ops_lint cheat_exists

/--
error: ops_lint (b) `NLAlib.Ops.Tools.LintFixtures.cheat_specific`: the interpretation is a
specific term (head `NLAlib.Ops.Interp.ofFns`), not a variable
-/
#guard_msgs (whitespace := lax) in
#ops_lint cheat_specific

/--
error: ops_lint (b) `NLAlib.Ops.Tools.LintFixtures.cheat_linkPinned`: a hypothesis fixes the
interpretation by an equation
-/
#guard_msgs (whitespace := lax) in
#ops_lint cheat_linkPinned

/--
error: ops_lint (c) `NLAlib.Ops.Tools.LintFixtures.cheat_noWitness`: no joint witness for the
contract set [NLAlib.Ops.Tools.LintFixtures.Oracle]
-/
#guard_msgs (whitespace := lax) in
#ops_lint cheat_noWitness

open Lean Elab Command in
run_cmd liftTermElabM do
  let violations ← Lint.lintDecl (← Lint.mkCtx) ``cheat_separateWitnesses
  unless violations.map Prod.fst == #["c"] do
    throwError "expected a joint witness violation for the separate witnesses"

/--
error: ops_lint (e) `NLAlib.Ops.Tools.LintFixtures.cheat_liberalAbort`: a liberal statement
without a success statement about the same program
-/
#guard_msgs (whitespace := lax) in
#ops_lint cheat_liberalAbort

/--
error: ops_lint (e) `NLAlib.Ops.Tools.LintFixtures.cheat_liberalCertificate`: a liberal statement
without a success statement about the same program
-/
#guard_msgs (whitespace := lax) in
#ops_lint cheat_liberalCertificate

/--
error: ops_lint (f) `NLAlib.Ops.Tools.LintFixtures.cheat_xi`: the algorithm's tree calls the
ξ-taking primitive `NLAlib.Ops.Examples.SrLo.sraddXi`
-/
#guard_msgs (whitespace := lax) in
#ops_lint cheat_xi

/-! ### Headlines of the examples are accepted -/

/-- info: ops_lint: `NLAlib.Ops.Tools.LintFixtures.runs_nested` passes (a)-(f) -/
#guard_msgs in
#ops_lint runs_nested

/-- info: ops_lint: `NLAlib.Ops.Examples.runs_gemm_rounded` passes (a)-(f) -/
#guard_msgs in
#ops_lint NLAlib.Ops.Examples.runs_gemm_rounded

/-- info: ops_lint: `NLAlib.Ops.Examples.gemm_spec` passes (a)-(f) -/
#guard_msgs in
#ops_lint NLAlib.Ops.Examples.gemm_spec

/-- info: ops_lint: `NLAlib.Ops.Examples.runs_srsum` passes (a)-(f) -/
#guard_msgs in
#ops_lint NLAlib.Ops.Examples.runs_srsum

/-- info: ops_lint: `NLAlib.Ops.sumSeq_spec` passes (a)-(f) -/
#guard_msgs in
#ops_lint NLAlib.Ops.sumSeq_spec

end NLAlib.Ops.Tools.LintFixtures
