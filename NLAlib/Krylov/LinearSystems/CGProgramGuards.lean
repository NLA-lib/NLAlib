/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramBody
public import NLAlib.Krylov.LinearSystems.CGProgramCounts
public import NLAlib.Krylov.LinearSystems.CGTridiagonal

/-!
# Exact guarded CG step execution

The actual curvature and stop guards surround the checked canonical CG body. No division
by zero is used to encode termination or rejected curvature.

## Main results

* `NLAlib.CGImplementation.exec_exact_curvature_guard`: actual guarded body execution.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation
open scoped Matrix

variable {P ι : Type} [DecidableEq P]

/-- Exact inner-body charges, including the branch-dependent terminal status copy.
This is proof bookkeeping for the approved program's count bound. -/
noncomputable def positiveBodyCount (tag : P) (N : ℕ) (nextρ : ℝ) : OpCount P ι :=
  Finsupp.single (.bin tag .div) 1 +
    N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
    Finsupp.single (.un tag .neg) 1 +
    N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
    (N • (Finsupp.single (.un tag .conj) 1 + Finsupp.single (.bin tag .mul) 1 +
      Finsupp.single (.bin tag .add) 1) + Finsupp.single (.lit tag) 1) +
    Finsupp.single (.bin tag .div) 1 +
    N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
    Finsupp.single (.copy tag) 1 + Finsupp.single (.cmp tag) 1 +
    (if nextρ = 0 then Finsupp.single (.copy tag) 1 else 0)

/-- Exact charges of the stored product and curvature-dot prefix of an active step. -/
noncomputable def curvatureCount (tag : P) (N : ℕ) : OpCount P ι :=
  (N • Finsupp.single (.lit tag) 1 + (N * N) •
    (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1)) +
    (N • (Finsupp.single (.un tag .conj) 1 + Finsupp.single (.bin tag .mul) 1 +
      Finsupp.single (.bin tag .add) 1) + Finsupp.single (.lit tag) 1)

omit [DecidableEq P] in
/-- The published per-step allowance is exactly the two outer guard charges, curvature
prefix, and maximal successful-body charge. -/
theorem stepCount_eq_kernel_counts (tag : P) (N : ℕ) :
    stepCount (ι := ι) tag N = Finsupp.single (.cmp tag) 1 + curvatureCount tag N +
      Finsupp.single (.cmp tag) 1 + positiveBodyCount tag N 0 := by
  classical
  simp only [stepCount, curvatureCount, positiveBodyCount, pow_two]
  simp only [nsmul_add, Finsupp.smul_single, smul_eq_mul, mul_one,
    show 5 * N = N + N + N + N + N by omega,
    show 2 * N = N + N by omega, show (2 : ℕ) = 1 + 1 from rfl,
    show (3 : ℕ) = 1 + 1 + 1 from rfl, Finsupp.single_add]
  abel_nf
  simp only [two_nsmul]

omit [DecidableEq P] in
/-- The terminal branch can only reduce the successful-body count. -/
theorem positiveBodyCount_le (tag : P) (N : ℕ) (ρ : ℝ) :
    positiveBodyCount (ι := ι) tag N ρ ≤ positiveBodyCount tag N 0 := by
  classical
  unfold positiveBodyCount
  rw [if_pos rfl]
  gcongr
  split_ifs
  · exact le_rfl
  · exact zero_le

/-- Exact charge of the two guarded alternatives of one requested loop iteration. -/
noncomputable def guardedStepCount (tag : P) (N : ℕ) (status μ nextρ : ℝ) : OpCount P ι :=
  Finsupp.single (.cmp tag) 1 + (if status = 0 then
    curvatureCount tag N + Finsupp.single (.cmp tag) 1 +
      (if 0 < μ then positiveBodyCount tag N nextρ else Finsupp.single (.copy tag) 1)
    else 0)

omit [DecidableEq P] in
/-- Rejecting curvature charges at most the successful body, because its single status
copy is included in the latter's maximal terminal-copy charge. -/
theorem single_copy_le_positiveBodyCount (tag : P) (N : ℕ) :
    Finsupp.single (.copy tag) 1 ≤ positiveBodyCount (ι := ι) tag N 0 := by
  unfold positiveBodyCount
  rw [if_pos rfl]
  exact le_add_self

omit [DecidableEq P] in
/-- Every branch of the actual requested iteration is within the approved step allowance. -/
theorem guardedStepCount_le (tag : P) (N : ℕ) (status μ ρ : ℝ) :
    guardedStepCount (ι := ι) tag N status μ ρ ≤ stepCount tag N := by
  classical
  unfold guardedStepCount
  rw [stepCount_eq_kernel_counts]
  by_cases hactive : status = 0
  · rw [if_pos hactive]
    have hbody : (if 0 < μ then positiveBodyCount (ι := ι) tag N ρ
        else Finsupp.single (.copy tag) 1) ≤ positiveBodyCount tag N 0 := by
      split_ifs
      · exact positiveBodyCount_le tag N ρ
      · exact single_copy_le_positiveBodyCount tag N
    simp only [add_assoc]
    gcongr
  · rw [if_neg hactive, add_zero]
    simpa only [add_assoc] using
      (show Finsupp.single (.cmp tag) 1 ≤ Finsupp.single (.cmp tag) 1 +
        (curvatureCount tag N + Finsupp.single (.cmp tag) 1 +
          positiveBodyCount (ι := ι) tag N 0) from le_self_add)

/-- The actual curvature guard executes the complete mathematical CG step when positive,
and otherwise writes breakdown status while preserving every vector and cached residual. -/
theorem exec_exact_curvature_guard {storedMatrix : Bool} (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (h : StoreContext tag (fun _ x => x) N A b v (v.r ⬝ᵥ v.r) 0 1 st.store storedMatrix)
    (hμ : st.store.read tag 7 2 = some (v.p ⬝ᵥ (A *ᵥ v.p))) (hr : v.r ⬝ᵥ v.r ≠ 0)
    (hs : ∀ i : Fin N, st.store.read tag 6 i = some ((A *ᵥ v.p) i)) :
    let μ := v.p ⬝ᵥ (A *ᵥ v.p)
    let next := if 0 < μ then cgStep A v else v
    let nextρ := next.r ⬝ᵥ next.r
    ∃ out, exec I (Builder.ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
      (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b next nextρ
        (if 0 < μ then if nextρ = 0 then 1 else 0 else -1) 1 out.store storedMatrix ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + Finsupp.single (.cmp tag) 1 +
        (if 0 < μ then positiveBodyCount tag N nextρ else Finsupp.single (.copy tag) 1) ∧
      out.peak = (if 0 < μ then
        Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) else st.peak) ∧
      out.peakW = (if 0 < μ then max st.peakW (st.curW + I.width tag) else st.peakW) := by
  classical
  dsimp only
  have hz : st.store.read tag 7 6 = some 0 := by
    obtain ⟨word, hw, hword⟩ := h.zero
    simpa only [hword] using hw
  have hsem : I.sem.cmp tag .lt 0 (v.p ⬝ᵥ (A *ᵥ v.p)) =
      some (decide (0 < v.p ⬝ᵥ (A *ᵥ v.p))) := by
    rw [hI]
    exact if_pos ⟨rfl, rfl⟩
  have hcmp : cmpStep I tag .lt ⟨7, 6⟩ ⟨7, 2⟩ st =
      some (decide (0 < v.p ⬝ᵥ (A *ᵥ v.p)),
        { st with cnt := st.cnt + I.charge (.cmp tag) }) := by
    simp only [cmpStep, IExp.eval_ofNat, hz, hμ, Option.bind_some, hsem, Option.map_some]
  let mid : St P ℝ (OpCount P ι) := { st with cnt := st.cnt + I.charge (.cmp tag) }
  by_cases hpos : 0 < v.p ⬝ᵥ (A *ᵥ v.p)
  · obtain ⟨out, hrun, hctx, hpos', hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
      exec_exact_positive_body I hI hc tag mid N A b v 0 h hμ (ne_of_gt hpos) hr hs
    refine ⟨out, ?_, ?_, hpos', hcur, hcurW, ?_, ?_, ?_⟩
    · change exec I (.seq (.ite tag .lt ⟨7, 6⟩ ⟨7, 2⟩ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp, Option.bind_some]
      simpa only [hpos, decide_true, Bool.true_eq, ↓reduceIte] using hrun
    · simpa only [if_pos hpos] using hctx
    · simpa only [mid, hc.charge_eq, positiveBodyCount, if_pos hpos, add_assoc] using hcnt
    · simpa only [mid, if_pos hpos] using hpeak
    · simpa only [mid, if_pos hpos] using hpeakW
  · obtain ⟨out, hrun, hctx, hstate⟩ := exec_exact_rejection I tag mid N A b v
      (v.r ⬝ᵥ v.r) 0 h
    refine ⟨out, ?_, ?_, by simpa only [mid] using congrArg St.pos hstate,
      by simpa only [mid] using congrArg St.cur hstate,
      by simpa only [mid] using congrArg St.curW hstate, ?_, ?_, ?_⟩
    · change exec I (.seq (.ite tag .lt ⟨7, 6⟩ ⟨7, 2⟩ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp, Option.bind_some]
      simpa only [hpos, decide_false, Bool.false_eq_true, ↓reduceIte] using hrun
    · simpa only [if_neg hpos] using hctx
    · simpa only [mid, hc.charge_eq, if_neg hpos] using congrArg St.cnt hstate
    · simpa only [mid, if_neg hpos] using congrArg St.peak hstate
    · simpa only [mid, if_neg hpos] using congrArg St.peakW hstate

/-- The complete active step computes its own curvature before branching. It either
realizes the next exact CG state or records curvature rejection with unchanged vectors. -/
theorem exec_exact_active_step (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N))
    (h : StoreContext tag (fun _ x => x) N A b v (v.r ⬝ᵥ v.r) 0 1 st.store)
    (hr : v.r ⬝ᵥ v.r ≠ 0) :
    let μ := v.p ⬝ᵥ (A *ᵥ v.p)
    let next := if 0 < μ then cgStep A v else v
    let nextρ := next.r ⬝ᵥ next.r
    ∃ out, exec I (do
      gemv tag (.const N) (.const N) 5 0 3 0 6 0
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)
      (Builder.ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
      (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) : Builder P ι ℕ ℕ Unit).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b next nextρ
        (if 0 < μ then if nextρ = 0 then 1 else 0 else -1) 1 out.store ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + curvatureCount tag N + Finsupp.single (.cmp tag) 1 +
        (if 0 < μ then positiveBodyCount tag N nextρ else Finsupp.single (.copy tag) 1) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  classical
  dsimp only
  obtain ⟨mid, hrun, hctx, hs, hμ, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_exact_curvature I hI hc tag st N A b v (v.r ⬝ᵥ v.r) 0 h
  obtain ⟨out, hout, hctx', hpos', hcur', hcurW', hcnt', hpeak', hpeakW'⟩ :=
    exec_exact_curvature_guard I hI hc tag mid N A b v hctx hμ hr hs
  have hcompose : ExecutionComposable I (do
      gemv tag (.const N) (.const N) 5 0 3 0 6 0
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)) :=
    (executionComposable_single I (fun _ => rfl)).bind
      (executionComposable_single I (fun _ => rfl))
  refine ⟨out, ?_, hctx', hpos'.trans hpos, hcur'.trans hcur, hcurW'.trans hcurW, ?_, ?_, ?_⟩
  · change exec I ((do
      gemv tag (.const N) (.const N) 5 0 3 0 6 0
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)) >>= fun _ => _).run st = _
    rw [hcompose, hrun, Option.bind_some]
    exact hout
  · rw [hcnt', hcnt]
    simp only [curvatureCount, add_assoc]
  · rw [hpeak', hpeak, hcur]
    split_ifs
    · simp only [Function.update_self, max_assoc, max_self, Function.update_idem]
    · rfl
  · rw [hpeakW', hpeakW, hcurW]
    split_ifs
    · rw [max_assoc, max_self]
    · rfl

/-- One complete requested iteration executes the actual status guard. Stopped runs skip
the body, and active runs perform the stored curvature prefix and its guarded step. -/
theorem exec_exact_guarded_step (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (status : ℝ)
    (h : StoreContext tag (fun _ x => x) N A b v (v.r ⬝ᵥ v.r) status 1 st.store)
    (hr : status = 0 → v.r ⬝ᵥ v.r ≠ 0) :
    let μ := v.p ⬝ᵥ (A *ᵥ v.p)
    let next := if status = 0 then if 0 < μ then cgStep A v else v else v
    let nextρ := next.r ⬝ᵥ next.r
    ∃ out, exec I (Builder.ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
      (do
      gemv tag (.const N) (.const N) 5 0 3 0 6 0
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)
      (Builder.ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
      (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) : Builder P ι ℕ ℕ Unit)
      (pure ())).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b next nextρ
        (if status = 0 then if 0 < μ then if nextρ = 0 then 1 else 0 else -1 else status)
        1 out.store ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + guardedStepCount tag N status μ nextρ ∧
      out.peak = (if status = 0 then
        Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) else st.peak) ∧
      out.peakW = (if status = 0 then max st.peakW (st.curW + I.width tag) else st.peakW) := by
  classical
  dsimp only
  have hz : st.store.read tag 7 6 = some 0 := by
    obtain ⟨word, hw, hword⟩ := h.zero
    simpa only [hword] using hw
  have hstatus : st.store.read tag 4 0 = some status := by
    obtain ⟨word, hw, hword⟩ := h.statusValue
    simpa only [hword] using hw
  have hsem : I.sem.cmp tag .eq status 0 = some (decide (status = 0)) := by rw [hI]; rfl
  have hcmp : cmpStep I tag .eq ⟨4, 0⟩ ⟨7, 6⟩ st =
      some (decide (status = 0), { st with cnt := st.cnt + I.charge (.cmp tag) }) := by
    simp only [cmpStep, IExp.eval_ofNat, hstatus, hz, Option.bind_some,
      hsem, Option.map_some]
  let mid : St P ℝ (OpCount P ι) := { st with cnt := st.cnt + I.charge (.cmp tag) }
  by_cases hactive : status = 0
  · have hctx : StoreContext tag (fun _ x => x) N A b v (v.r ⬝ᵥ v.r) 0 1 mid.store := by
      simpa only [hactive] using h
    obtain ⟨out, hrun, hctx', hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
      exec_exact_active_step I hI hc tag mid N A b v hctx (hr hactive)
    refine ⟨out, ?_, ?_, hpos, hcur, hcurW, ?_, ?_, ?_⟩
    · change exec I (.seq (.ite tag .eq ⟨4, 0⟩ ⟨7, 6⟩ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp, Option.bind_some]
      simpa only [hactive, decide_true, Bool.true_eq, ↓reduceIte] using hrun
    · simpa only [if_pos hactive] using hctx'
    · simpa only [mid, hc.charge_eq, guardedStepCount, if_pos hactive, add_assoc] using hcnt
    · simpa only [mid, if_pos hactive] using hpeak
    · simpa only [mid, if_pos hactive] using hpeakW
  · refine ⟨mid, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · change exec I (.seq (.ite tag .eq ⟨4, 0⟩ ⟨7, 6⟩ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp, Option.bind_some]
      simpa only [hactive, decide_false, Bool.false_eq_true, ↓reduceIte, Builder.run_pure]
        using exec_skip I mid
    · simpa only [if_neg hactive] using h
    · simp only [mid, guardedStepCount, if_neg hactive, add_zero, hc.charge_eq]
    · simp only [mid, if_neg hactive]
    · simp only [mid, if_neg hactive]

/-- In an SPD exact CG trajectory a nonzero residual gives strictly positive curvature.
This justifies the actual guard without imposing a local execution or curvature premise. -/
theorem zero_lt_dotProduct_mulVec_cgState_p {N j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosDef) (b : Fin N → ℝ) (hr : (cgState A b 0 j).r ≠ 0) :
    0 < (cgState A b 0 j).p ⬝ᵥ (A *ᵥ (cgState A b 0 j).p) := by
  have h := hA.re_quadForm_pos (hA.cgState_p_ne_zero b 0 hr)
  simpa only [quadForm, star_trivial, RCLike.re_to_real] using h

end NLAlib.CGImplementation
