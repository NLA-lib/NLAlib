/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramGuards

/-!
# Exact execution of the approved CG loop

The induction invariant tracks actual initialized cells, unconditional safe statuses and
conditional SPD correspondence. It is proved from initialization and actual guarded steps.

## Main results

* `NLAlib.CGImplementation.loopInvariant_initial`: the initialized store satisfies the invariant.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation
open scoped Matrix

variable {P ι : Type} [DecidableEq P]

/-- Actual stored vectors and stop status after a loop prefix. Safety applies to every real
matrix; correspondence with the mathematical recurrence is conditional on positive definiteness. -/
def LoopInvariant (tag : P) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (j : ℕ) (store : Store P ℝ) (storedMatrix : Bool := true) : Prop :=
  ∃ (v : CGState ℝ (Fin N)) (status : ℝ),
    StoreContext tag (fun _ x => x) N A b v (v.r ⬝ᵥ v.r) status 1 store storedMatrix ∧
    (status = 0 ∨ status = 1 ∨ status = -1) ∧
    (status = 0 → v.r ≠ 0) ∧
    (A.PosDef → v = cgState A b 0 j ∧ (status = 1 ↔ v.r = 0) ∧ status ≠ -1)

/-- The actual initialized CG buffers satisfy the induction invariant, including the
zero-right-hand-side status and zero-dimensional case. -/
theorem loopInvariant_initial_of_storeContext (tag : P) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (store : Store P ℝ) (storedMatrix : Bool)
    (h : StoreContext tag (fun _ x => x) N A b ⟨0, b, b⟩ (b ⬝ᵥ b)
      (if b = 0 then 1 else 0) 1 store storedMatrix) :
    LoopInvariant tag N A b 0 store storedMatrix := by
  classical
  refine ⟨⟨0, b, b⟩, if b = 0 then 1 else 0, h, ?_, ?_, ?_⟩
  · split_ifs <;> norm_num
  · intro hs hb
    change b = 0 at hb
    rw [if_pos hb] at hs
    norm_num at hs
  · intro _
    refine ⟨?_, ?_, ?_⟩
    · simp only [cgState, Matrix.mulVec_zero, sub_zero]
    · by_cases hb : b = 0 <;> simp [hb]
    · split_ifs <;> norm_num

/-- The initialized stored-matrix CG buffers satisfy the exact loop invariant. -/
theorem loopInvariant_initial (tag : P) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (store : Store P ℝ)
    (h : StoreContext tag (fun _ x => x) N A b ⟨0, b, b⟩ (b ⬝ᵥ b)
      (if b = 0 then 1 else 0) 1 store) : LoopInvariant tag N A b 0 store :=
  loopInvariant_initial_of_storeContext tag N A b store true h

/-- The guarded mathematical step preserves legal statuses and SPD recurrence correspondence,
including exact zero-residual continuation. It does not refer to a matrix access backend. -/
theorem guarded_next_invariants {N j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {v : CGState ℝ (Fin N)} {status : ℝ}
    (hstatus : status = 0 ∨ status = 1 ∨ status = -1)
    (hactive : status = 0 → v.r ≠ 0)
    (hexact : A.PosDef → v = cgState A b 0 j ∧ (status = 1 ↔ v.r = 0) ∧ status ≠ -1) :
    let μ := v.p ⬝ᵥ (A *ᵥ v.p)
    let next := if status = 0 then if 0 < μ then cgStep A v else v else v
    let flag : ℝ := if status = 0 then
      if 0 < μ then if next.r ⬝ᵥ next.r = 0 then 1 else 0 else -1 else status
    (flag = 0 ∨ flag = 1 ∨ flag = -1) ∧ (flag = 0 → next.r ≠ 0) ∧
      (A.PosDef → next = cgState A b 0 (j + 1) ∧ (flag = 1 ↔ next.r = 0) ∧ flag ≠ -1) := by
  classical
  dsimp only
  by_cases hs : status = 0
  · simp only [if_pos hs]
    by_cases hm : 0 < v.p ⬝ᵥ (A *ᵥ v.p)
    · simp only [if_pos hm]
      refine ⟨?_, ?_, ?_⟩
      · split_ifs <;> norm_num
      · intro hflag hr
        simp only [hr, dotProduct_zero] at hflag
        norm_num at hflag
      · intro hA
        obtain ⟨hv, _, _⟩ := hexact hA
        refine ⟨?_, ?_, ?_⟩
        · rw [hv]; rfl
        · by_cases hr : (cgStep A v).r = 0 <;> simp [hr]
        · split_ifs <;> norm_num
    · simp only [if_neg hm]
      refine ⟨by norm_num, by norm_num, ?_⟩
      intro hA
      obtain ⟨hv, _, _⟩ := hexact hA
      exact (hm (by simpa only [hv] using
        zero_lt_dotProduct_mulVec_cgState_p hA b (by simpa only [← hv] using hactive hs))).elim
  · simp only [if_neg hs]
    refine ⟨hstatus, hactive, ?_⟩
    intro hA
    obtain ⟨hv, hterm, hnot⟩ := hexact hA
    have hflag : status = 1 := by
      rcases hstatus with hz | h1 | hn
      · exact (hs hz).elim
      · exact h1
      · exact (hnot hn).elim
    have hr : (cgState A b 0 j).r = 0 := by rw [← hv]; exact hterm.mp hflag
    refine ⟨?_, hterm, hnot⟩
    rw [cgState_succ_eq_of_r_eq_zero A b 0 hr]
    exact hv

private theorem le_scratchPeak (peak cur : P → ℕ) (tag : P) :
    peak ≤ Function.update peak tag (max (peak tag) (cur tag + 1)) := by
  intro p
  by_cases hp : p = tag
  · subst p
    simp only [Function.update_self]
    exact le_max_left _ _
  · rw [Function.update_of_ne hp]

/-- The actual canonical guarded step preserves the loop invariant for every real matrix,
with the approved step count and one-cell scratch-memory allowance. -/
theorem exec_exact_step (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N j : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (h : LoopInvariant tag N A b j st.store) :
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
      LoopInvariant tag N A b (j + 1) out.store ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt ≤ st.cnt + stepCount tag N ∧
      out.peak ≤ Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW ≤ max st.peakW (st.curW + I.width tag) := by
  obtain ⟨v, status, hctx, hstatus, hactive, hexact⟩ := h
  obtain ⟨out, hrun, hctx', hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_exact_guarded_step I hI hc tag st N A b v status hctx
      (fun hs hz => hactive hs (dotProduct_self_eq_zero.mp hz))
  refine ⟨out, hrun, ?_, hpos, hcur, hcurW, ?_, ?_, ?_⟩
  · exact ⟨_, _, hctx', guarded_next_invariants hstatus hactive hexact⟩
  · rw [hcnt]
    gcongr
    exact guardedStepCount_le tag N status _ _
  · rw [hpeak]
    split_ifs
    · exact le_rfl
    · exact le_scratchPeak st.peak st.cur tag
  · rw [hpeakW]
    split_ifs
    · exact le_rfl
    · exact le_max_left _ _

private def PrefixInvariant (I : Interp P ι ℝ (OpCount P ι)) (tag : P) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (st : St P ℝ (OpCount P ι))
    (j : ℕ) (out : St P ℝ (OpCount P ι)) : Prop :=
  LoopInvariant tag N A b j out.store ∧ out.pos = st.pos ∧ out.cur = st.cur ∧
    out.curW = st.curW ∧ out.cnt ≤ st.cnt + j • stepCount tag N ∧
    out.peak ≤ Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
    out.peakW ≤ max st.peakW (st.curW + I.width tag)

private theorem exec_exact_prefix_succ (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st out : St P ℝ (OpCount P ι)) (N j : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (h : PrefixInvariant I tag N A b st j out) :
    ∃ next, exec I (Builder.ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
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
      (pure ())).run out = some next ∧
      PrefixInvariant I tag N A b st (j + 1) next := by
  obtain ⟨hinv, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ := h
  obtain ⟨next, hrun, hinv', hpos', hcur', hcurW', hcnt', hpeak', hpeakW'⟩ :=
    exec_exact_step I hI hc tag out N j A b hinv
  refine ⟨next, hrun, hinv', hpos'.trans hpos, hcur'.trans hcur, hcurW'.trans hcurW,
    ?_, ?_, ?_⟩
  · calc
      next.cnt ≤ out.cnt + stepCount tag N := hcnt'
      _ ≤ (st.cnt + j • stepCount tag N) + stepCount tag N := by gcongr
      _ = st.cnt + (j + 1) • stepCount tag N := by rw [succ_nsmul, add_assoc]
  · intro p
    calc
      next.peak p ≤ Function.update out.peak tag (max (out.peak tag) (out.cur tag + 1)) p :=
        hpeak' p
      _ ≤ Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) p := by
        by_cases hp : p = tag
        · subst p
          simp only [Function.update_self]
          rw [hcur]
          exact max_le (by simpa only [Function.update_self] using hpeak tag)
            (le_max_right _ _)
        · simpa only [Function.update_of_ne hp] using hpeak p
  · calc
      next.peakW ≤ max out.peakW (out.curW + I.width tag) := hpeakW'
      _ ≤ max st.peakW (st.curW + I.width tag) := by
        rw [hcurW]
        exact max_le hpeakW (le_max_right _ _)

private theorem exec_exact_loop_prefix (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (h : LoopInvariant tag N A b 0 st.store) :
    ∃ out, exec I (Builder.forRange (.const q) fun _ => (Builder.ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
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
      (pure ()))).run st = some out ∧
      PrefixInvariant I tag N A b st q out := by
  let R := PrefixInvariant I tag N A b st
  have h0 : R 0 st := ⟨h, rfl, rfl, rfl,
    by simp only [zero_nsmul, add_zero]; exact le_rfl,
    le_scratchPeak st.peak st.cur tag, le_max_left _ _⟩
  have hstep (j : ℕ) (_hj : j < q) (out : St P ℝ (OpCount P ι)) (hout : R j out) :=
    exec_exact_prefix_succ I hI hc tag st out N j A b hout
  obtain ⟨out, hrun, hout⟩ :=
    exists_exec_loop_eq_some_of_forall I (n := .const q) R h0 hstep
  refine ⟨out, ?_, hout⟩
  change exec I (.seq (.loop (.const q) _) .skip) st = _
  rw [exec_seq_skip]
  exact hrun

/-- The full canonical exact loop succeeds for every real matrix and preserves the input.
For SPD matrices its actual vector cells equal the mathematical CG state after the requested
budget, including zero termination. Counts and memory satisfy the approved loop allowance. -/
theorem exec_exact_loop (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ)
    (h : StoreContext tag (fun _ x => x) N A b ⟨0, b, b⟩ (b ⬝ᵥ b)
      (if b = 0 then 1 else 0) 1 st.store) :
    ∃ (out : St P ℝ (OpCount P ι)) (v : CGState ℝ (Fin N)) (status : ℝ),
      exec I (Builder.forRange (.const q) fun _ => (Builder.ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
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
      (pure ()))).run st = some out ∧
      StoreContext tag (fun _ x => x) N A b v (v.r ⬝ᵥ v.r) status 1 out.store ∧
      (status = 0 ∨ status = 1 ∨ status = -1) ∧
      (A.PosDef → v = cgState A b 0 q ∧ (status = 1 ↔ v.r = 0) ∧ status ≠ -1) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt ≤ st.cnt + q • stepCount tag N ∧
      out.peak ≤ Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW ≤ max st.peakW (st.curW + I.width tag) := by
  obtain ⟨out, hrun, hinv, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_exact_loop_prefix I hI hc tag st N q A b (loopInvariant_initial tag N A b _ h)
  obtain ⟨v, status, hctx, hstatus, _, hexact⟩ := hinv
  exact ⟨out, v, status, hrun, hctx, hstatus, hexact, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩

end NLAlib.CGImplementation
