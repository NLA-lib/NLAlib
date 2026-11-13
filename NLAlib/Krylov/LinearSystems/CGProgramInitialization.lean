/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.ScalarFrames
public import NLAlib.Computation.BLAS.Frames
public import NLAlib.Krylov.LinearSystems.CGTargets

/-!
# The actual preallocated exact CG initialization block

Execution lemmas for the canonical stored-matrix CG initializer, with flat storage and
resource conclusions. These derive the initialized values from actual operations, rather
than assume a desired CG state. No additional algorithm or arithmetic interface is defined.

## Main results

* `NLAlib.CGImplementation.exec_cg_initialization`: the full canonical preallocated initializer.
* `NLAlib.CGImplementation.exec_cg_constants`: the literal, negation and status setup.
* `NLAlib.CGImplementation.exec_cg_vectors`: zero iterate and copied residual and direction.
* `NLAlib.CGImplementation.exec_cg_cache_status`: actual self-dot and initial status test.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.CGImplementation

open Computation Computation.Builder

variable {P ι : Type} [DecidableEq P]

/-- The exact constant setup in the canonical CG initializer, including its actual writes,
full outside-cell frame and exact charged state. -/
theorem exec_cg_constants (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ (OpCount P ι))
    (h7 : st.store.shape[7]? = some (tag, 9))
    (h4 : st.store.shape[4]? = some (tag, 1)) :
    ∃ out, exec I (do
        ins (.lit tag ⟨7, 6⟩ 0)
        ins (.lit tag ⟨7, 7⟩ 1)
        ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
        ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag 7 6 = some 0 ∧ out.store.read tag 7 7 = some 1 ∧
      out.store.read tag 7 8 = some (-1) ∧ out.store.read tag 4 0 = some 0 ∧
      (∀ q b i, b ≠ 4 → (b ≠ 7 ∨ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 8) →
        out.store.read q b i = st.store.read q b i) ∧
      out = { st with
        store := out.store
        cnt := st.cnt + I.charge (.lit tag) + I.charge (.lit tag) +
          I.charge (.un tag .neg) + I.charge (.copy tag) } := by
  have cap (s : Store P ℝ) (hs : s.shape = st.store.shape) (i : ℕ) (hi : i < 9) :
      ∃ len, s.shape[7]? = some (tag, len) ∧ i < len :=
    ⟨9, hs ▸ h7, hi⟩
  obtain ⟨s0, w0, e0, sh0, r0, f0⟩ := exec_scalar_lit I tag st ⟨7, 6⟩ 0 0
    (by rw [hI]; simp [exactSem]) (cap _ rfl 6 (by omega))
  let st1 := { st with store := s0, cnt := st.cnt + I.charge (.lit tag) }
  obtain ⟨s1, w1, e1, sh1, r1, f1⟩ := exec_scalar_lit I tag st1 ⟨7, 7⟩ 1 1
    (by rw [hI]; simp [exactSem]) (cap _ sh0 7 (by omega))
  let st2 := { st1 with store := s1, cnt := st1.cnt + I.charge (.lit tag) }
  obtain ⟨s2, w2, e2, sh2, r2, f2⟩ := exec_scalar_un I tag st2 .neg ⟨7, 8⟩ ⟨7, 7⟩
    1 (-1) r1 (by rw [hI]; rfl) (cap _ (sh1.trans sh0) 8 (by omega))
  let st3 := { st2 with store := s2, cnt := st2.cnt + I.charge (.un tag .neg) }
  have r03 : st3.store.read tag 7 6 = some 0 := by
    rw [f2 tag 7 6 (Or.inr (Or.inr (by norm_num))), f1 tag 7 6 (Or.inr (Or.inr (by norm_num)))]
    exact r0
  obtain ⟨s3, w3, e3, sh3, r3, f3⟩ := exec_scalar_copy I tag st3 ⟨4, 0⟩ ⟨7, 6⟩ 0 r03
    ⟨1, (sh2.trans (sh1.trans sh0)) ▸ h4, by norm_num⟩
  let out := { st3 with store := s3, cnt := st3.cnt + I.charge (.copy tag) }
  refine ⟨out, ?_, sh3.trans (sh2.trans (sh1.trans sh0)), ?_, ?_, ?_, r3, ?_, rfl⟩
  · rw [exec_run_bind I (b := ins (.lit tag ⟨7, 6⟩ 0)) (fun _ => rfl), e0,
      Option.bind_some, exec_run_bind I (b := ins (.lit tag ⟨7, 7⟩ 1)) (fun _ => rfl), e1,
      Option.bind_some, exec_run_bind I (b := ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩))
        (fun _ => rfl), e2, Option.bind_some]
    exact e3
  · rw [f3 tag 7 6 (Or.inr (Or.inl (by norm_num)))]
    exact r03
  · rw [f3 tag 7 7 (Or.inr (Or.inl (by norm_num))), f2 tag 7 7 (Or.inr (Or.inr (by norm_num)))]
    exact r1
  · rw [f3 tag 7 8 (Or.inr (Or.inl (by norm_num)))]
    exact r2
  · intro q b i hb hi
    rw [f3 q b i (Or.inr (Or.inl hb))]
    rcases hi with hi | ⟨h6, h7, h8⟩
    · rw [f2 q b i (Or.inr (Or.inl hi)), f1 q b i (Or.inr (Or.inl hi)),
        f0 q b i (Or.inr (Or.inl hi))]
    · rw [f2 q b i (Or.inr (Or.inr h8)), f1 q b i (Or.inr (Or.inr h7)),
        f0 q b i (Or.inr (Or.inr h6))]

open scoped Classical in
/-- The canonical initial status guard charges one comparison and copies positive status
only when the cached exact squared residual vanishes. All other scalar cells are retained. -/
theorem exec_cg_status_guard (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) {N : ℕ} (b : Fin N → ℝ)
    (h4 : st.store.shape[4]? = some (tag, 1))
    (hnu : st.store.read tag 7 0 = some (b ⬝ᵥ b))
    (hzero : st.store.read tag 7 6 = some 0)
    (hone : st.store.read tag 7 7 = some 1)
    (hstatus : st.store.read tag 4 0 = some 0) :
    ∃ out, exec I (ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag 4 0 = some (if b = 0 then 1 else 0) ∧
      (∀ q buf i, (buf ≠ 4 ∨ i ≠ 0) → out.store.read q buf i = st.store.read q buf i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt ≤ st.cnt + Finsupp.single (.cmp tag) 1 + Finsupp.single (.copy tag) 1 ∧
      out.peak = st.peak ∧ out.peakW = st.peakW := by
  let st₀ : St P ℝ (OpCount P ι) :=
    { st with cnt := st.cnt + Finsupp.single (OpKind.cmp tag) 1 }
  have hcmp : cmpStep I tag .eq ⟨7, 0⟩ ⟨7, 6⟩ st = some (decide (b = 0), st₀) := by
    simp only [cmpStep, hnu, hzero, IExp.eval_ofNat, hI, exactSem,
      Option.bind_some, Option.map_some, dotProduct_self_eq_zero, hc.charge_eq, st₀]
  by_cases hb : b = 0
  · obtain ⟨s, hw, he, hsh, hr, hf⟩ := exec_scalar_copy I tag st₀ ⟨4, 0⟩ ⟨7, 7⟩ 1
      hone ⟨1, h4, by norm_num⟩
    let out := { st₀ with store := s, cnt := st₀.cnt + I.charge (.copy tag) }
    refine ⟨out, ?_, hsh, ?_, ?_, rfl, rfl, rfl, ?_, rfl, rfl⟩
    · change exec I (.seq (.ite tag .eq _ _ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp]
      simpa only [hb, decide_true, Bool.true_eq, ite_true, Option.bind_some, out] using he
    · simpa only [hb, ite_true, out, IExp.eval_ofNat] using hr
    · intro q buf i hi
      exact hf q buf i (Or.inr hi)
    · change (st.cnt + _) + I.charge (.copy tag) ≤ _
      rw [hc.charge_eq]
  · refine ⟨st₀, ?_, rfl, ?_, fun _ _ _ _ => rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
    · change exec I (.seq (.ite tag .eq _ _ _ _) .skip) st = _
      rw [exec_seq_skip, exec_ite, hcmp]
      simp only [hb, decide_false, Bool.false_eq_true, ite_false, Option.bind_some]
      rfl
    · simpa only [hb, ite_false] using hstatus
    · change st.cnt + _ ≤ _
      exact le_self_add

/-- The actual vector initialization writes zero iterate and copies the input into residual
and direction. No scratch allocation occurs, and all other buffers retain their contents. -/
theorem exec_cg_vectors (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (b : Fin N → ℝ)
    (h1 : st.store.shape[1]? = some (tag, N))
    (h2 : st.store.shape[2]? = some (tag, N))
    (h3 : st.store.shape[3]? = some (tag, N))
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i)) :
    ∃ out, exec I (do
        forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
        copyv tag 0 0 2 0 (.const N)
        copyv tag 0 0 3 0 (.const N)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, out.store.read tag 1 i = some 0) ∧
      (∀ i : Fin N, out.store.read tag 2 i = some (b i)) ∧
      (∀ i : Fin N, out.store.read tag 3 i = some (b i)) ∧
      (∀ q buf i, buf ≠ 1 → buf ≠ 2 → buf ≠ 3 →
        out.store.read q buf i = st.store.read q buf i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + N • Finsupp.single (.lit tag) 1 +
        N • Finsupp.single (.copy tag) 1 + N • Finsupp.single (.copy tag) 1 ∧
      out.peak = st.peak ∧ out.peakW = st.peakW := by
  let xs : ℕ → ℝ := fun i => if hi : i < N then b ⟨i, hi⟩ else 0
  obtain ⟨s0, e0, sh0, r0, f0⟩ := Computation.exec_forRange_zero_var I hI tag st
    (.const N) 1 (fun i hi => ⟨N, h1, hi⟩)
  simp only [IExp.eval_const] at e0 r0 f0
  let st0 := { st with store := s0, cnt := st.cnt + N • I.charge (.lit tag) }
  have rb0 : ∀ i < N, st0.store.read tag 0 i = some (xs i) := by
    intro i hi
    rw [f0 tag 0 i (Or.inr (Or.inl (by norm_num)))]
    simpa only [xs, dif_pos hi] using hb ⟨i, hi⟩
  obtain ⟨st1, e1, sh1, r1, f1, pos1, cur1, curW1, cnt1, peak1, peakW1⟩ :=
    Computation.exec_copyv_frame I hc tag st0 (.const N) 0 2 0 0 xs
      (by simpa only [IExp.eval_const, IExp.eval_zero, zero_add] using rb0) (by norm_num)
      (fun i hi => ⟨N, sh0 ▸ h2,
        by simpa only [IExp.eval_const, IExp.eval_zero, zero_add] using hi⟩)
  have rb1 : ∀ i < N, st1.store.read tag 0 i = some (xs i) := by
    intro i hi
    rw [f1 tag 0 i (Or.inl (by norm_num))]
    exact rb0 i hi
  obtain ⟨out, e2, sh2, r2, f2, pos2, cur2, curW2, cnt2, peak2, peakW2⟩ :=
    Computation.exec_copyv_frame I hc tag st1 (.const N) 0 3 0 0 xs
      (by simpa only [IExp.eval_const, IExp.eval_zero, zero_add] using rb1) (by norm_num)
      (fun i hi => ⟨N, (sh1.trans sh0) ▸ h3,
        by simpa only [IExp.eval_const, IExp.eval_zero, zero_add] using hi⟩)
  refine ⟨out, ?_, sh2.trans (sh1.trans sh0), ?_, ?_, ?_, ?_, pos2.trans pos1,
    cur2.trans cur1, curW2.trans curW1, ?_, peak2.trans peak1, peakW2.trans peakW1⟩
  · rw [exec_run_bind I (b := forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0))
      (fun _ => rfl), e0, Option.bind_some,
      exec_run_bind I (b := copyv tag 0 0 2 0 (.const N)) (fun _ => rfl), e1,
      Option.bind_some]
    exact e2
  · intro i
    rw [f2 tag 1 i (Or.inl (by norm_num)), f1 tag 1 i (Or.inl (by norm_num))]
    exact r0 i i.isLt
  · intro i
    rw [f2 tag 2 i (Or.inl (by norm_num))]
    simpa only [IExp.eval_zero, zero_add, xs, dif_pos i.isLt] using r1 i i.isLt
  · intro i
    simpa only [IExp.eval_zero, zero_add, xs, dif_pos i.isLt] using r2 i i.isLt
  · intro q buf i h1 h2 h3
    rw [f2 q buf i (Or.inl h3), f1 q buf i (Or.inl h2)]
    exact f0 q buf i (Or.inr (Or.inl h1))
  · rw [cnt2, cnt1]
    simp only [st0, hc.charge_eq, IExp.eval_const]

open scoped Classical in
/-- The canonical cached self-dot followed by its actual initial status test. The dot is an
executed kernel, and the zero-input status is derived from its stored result. -/
theorem exec_cg_cache_status (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (b : Fin N → ℝ)
    (h7 : st.store.shape[7]? = some (tag, 9))
    (h4 : st.store.shape[4]? = some (tag, 1))
    (hr : ∀ i : Fin N, st.store.read tag 2 i = some (b i))
    (hzero : st.store.read tag 7 6 = some 0)
    (hone : st.store.read tag 7 7 = some 1)
    (hstatus : st.store.read tag 4 0 = some 0) :
    ∃ out, exec I (do
        dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
        ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
          (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag 7 0 = some (b ⬝ᵥ b) ∧
      out.store.read tag 4 0 = some (if b = 0 then 1 else 0) ∧
      (∀ q buf i, (buf ≠ 4 ∨ i ≠ 0) → (buf ≠ 7 ∨ i ≠ 0) →
        out.store.read q buf i = st.store.read q buf i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt ≤ st.cnt + (N • (Finsupp.single (.un tag .conj) 1 +
        Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        Finsupp.single (.lit tag) 1) + Finsupp.single (.cmp tag) 1 +
        Finsupp.single (.copy tag) 1 ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  obtain ⟨s, hs⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 0) (0 : ℝ) h7 (by norm_num)
  obtain ⟨mid, edot, sh, rnu, fr, pos, cur, curW, cnt, peak, peakW⟩ :=
    Computation.exec_dot_frame I hI hc tag st N ⟨7, 0⟩ 2 2 0 0 b b
      (by simpa only [IExp.eval_zero, zero_add] using hr)
      (by simpa only [IExp.eval_zero, zero_add] using hr) (by norm_num) (by norm_num) ⟨0, s, hs⟩
  obtain ⟨out, eguard, sh', rst, fr', pos', cur', curW', cnt', peak', peakW'⟩ :=
    exec_cg_status_guard I hI hc tag mid b (sh ▸ h4) rnu
      ((fr tag 7 6 (Or.inr (by norm_num))).trans hzero)
      ((fr tag 7 7 (Or.inr (by norm_num))).trans hone)
      ((fr tag 4 0 (Or.inl (by norm_num))).trans hstatus)
  refine ⟨out, ?_, sh'.trans sh, ?_, rst, ?_, pos'.trans pos, cur'.trans cur,
    curW'.trans curW, ?_, peak'.trans peak, peakW'.trans peakW⟩
  · rw [exec_run_bind I (b := dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)) (fun _ => rfl),
      edot, Option.bind_some]
    exact eguard
  · exact (fr' tag 7 0 (Or.inl (by norm_num))).trans rnu
  · intro q buf i h4 h7
    exact (fr' q buf i h4).trans (fr q buf i h7)
  · rwa [cnt] at cnt'

/-- ROM loading and scalar setup execute in canonical order before vector initialization. -/
theorem exec_cg_preload (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ (OpCount P ι)) (N : ℕ) (vals : ℕ → ℝ)
    (h5 : st.store.shape[5]? = some (tag, N * N))
    (h7 : st.store.shape[7]? = some (tag, 9))
    (h4 : st.store.shape[4]? = some (tag, 1))
    (hrom : ∀ i < N * N, I.rom i = some (vals i)) :
    ∃ out, exec I (do
        forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
        ins (.lit tag ⟨7, 6⟩ 0)
        ins (.lit tag ⟨7, 7⟩ 1)
        ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
        ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      Holds out.store tag 5 0 (fun (i j : Fin N) => vals (i + N * j)) ∧
      out.store.read tag 7 6 = some 0 ∧ out.store.read tag 7 7 = some 1 ∧
      out.store.read tag 7 8 = some (-1) ∧ out.store.read tag 4 0 = some 0 ∧
      (∀ q b i, b ≠ 4 → b ≠ 5 → (b ≠ 7 ∨ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 8) →
        out.store.read q b i = st.store.read q b i) ∧
      out = { st with
        store := out.store
        cnt := st.cnt + (N * N) • I.charge (.rom tag) + I.charge (.lit tag) +
          I.charge (.lit tag) + I.charge (.un tag .neg) + I.charge (.copy tag) } := by
  obtain ⟨s, erom, sh, rr, fr⟩ := exec_forRange_rom I tag st (IExp.const N * IExp.const N) 5 vals
    (by simpa only [IExp.eval_mul, IExp.eval_const] using h5)
    (by simpa only [IExp.eval_mul, IExp.eval_const] using hrom)
  simp only [IExp.eval_mul, IExp.eval_const] at erom rr
  let stR := { st with store := s, cnt := st.cnt + (N * N) • I.charge (.rom tag) }
  obtain ⟨out, ec, shc, rz, ro, rn, rs, fc, state⟩ :=
    exec_cg_constants I hI tag stR (sh ▸ h7) (sh ▸ h4)
  refine ⟨out, ?_, shc.trans sh, ?_, rz, ro, rn, rs, ?_, ?_⟩
  · rw [exec_run_bind I (b := forRange (IExp.const N * IExp.const N) fun i =>
      stmt (.rom tag ⟨5, .var i⟩ (.var i))) (fun _ => rfl)]
    have erom' : exec I (forRange (IExp.const N * IExp.const N) fun i =>
        stmt (.rom tag ⟨5, .var i⟩ (.var i))).run st = some stR := by
      change exec I (.seq (.loop _ _) .skip) st = _
      rw [exec_seq_skip]
      exact erom
    rw [erom', Option.bind_some]
    exact ec
  · intro i j
    rw [fc tag 5 (0 + i + N * j) (by norm_num) (Or.inl (by norm_num))]
    have hprod := Nat.mul_le_mul_left N (Nat.succ_le_of_lt j.isLt)
    simp only [Nat.mul_succ] at hprod
    simpa only [zero_add] using rr (i + N * j) (by omega)
  · intro q b i h4 h5 h7
    rw [fc q b i h4 h7]
    exact fr q b i h5
  · simpa only [stR] using state

private theorem composable_cg_preload (I : Interp P ι ℝ (OpCount P ι)) (tag : P) (N : ℕ) :
    ExecutionComposable I (do
      forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
      ins (.lit tag ⟨7, 6⟩ 0)
      ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
      ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)) := by
  exact (executionComposable_single I (b := forRange (IExp.const N * IExp.const N) fun i =>
    stmt (.rom tag ⟨5, .var i⟩ (.var i))) (fun _ => rfl)).bind
    ((executionComposable_single I (b := ins (.lit tag ⟨7, 6⟩ 0)) (fun _ => rfl)).bind
      ((executionComposable_single I (b := ins (.lit tag ⟨7, 7⟩ 1)) (fun _ => rfl)).bind
        ((executionComposable_single I (b := ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩))
          (fun _ => rfl)).bind
          (executionComposable_single I (b := ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)) (fun _ => rfl)))))

/-- The canonical zero-iterate and input-copy prefix composes with later execution. This
syntactic certificate is shared by the stored and oracle CG initializers. -/
theorem executionComposable_cg_vectors (I : Interp P ι ℝ (OpCount P ι)) (tag : P) (N : ℕ) :
    ExecutionComposable I (do
      forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (.const N)
      copyv tag 0 0 3 0 (.const N)) := by
  exact (executionComposable_single I (b := forRange (.const N) fun i =>
    ins (.lit tag ⟨1, .var i⟩ 0)) (fun _ => rfl)).bind
    ((executionComposable_single I (b := copyv tag 0 0 2 0 (.const N)) (fun _ => rfl)).bind
      (executionComposable_single I (b := copyv tag 0 0 3 0 (.const N)) (fun _ => rfl)))

omit [DecidableEq P] in
private theorem cg_count_zero_eq (tag : P) (N : ℕ) :
    cgCount (ι := ι) tag N 0 =
      (N * N) • Finsupp.single (.rom tag) 1 + Finsupp.single (.lit tag) 1 +
      Finsupp.single (.lit tag) 1 + Finsupp.single (.un tag .neg) 1 +
      Finsupp.single (.copy tag) 1 + N • Finsupp.single (.lit tag) 1 +
      N • Finsupp.single (.copy tag) 1 + N • Finsupp.single (.copy tag) 1 +
      (N • (Finsupp.single (.un tag .conj) 1 + Finsupp.single (.bin tag .mul) 1 +
        Finsupp.single (.bin tag .add) 1) + Finsupp.single (.lit tag) 1) +
      Finsupp.single (.cmp tag) 1 + Finsupp.single (.copy tag) 1 := by
  simp only [cgCount, Nat.zero_mul, Nat.mul_zero,
    Finsupp.single_zero, add_zero, zero_add, nsmul_add, Finsupp.smul_single,
    smul_eq_mul, Nat.mul_one, pow_two]
  rw [show N + 3 = N + 1 + 1 + 1 by omega, show 2 * N + 2 = N + N + 1 + 1 by omega]
  simp only [Finsupp.single_add]
  abel

open scoped Classical in
/-- The full preallocated initializer executes in the canonical CG operation order. It
loads the ROM matrix, retains the input, returns zero iterate and copied residual/direction,
computes the cached squared residual, and derives the initial status. Its operation bound is
the approved zero-step CG count, including the zero-input branch; the sole scratch peak is
one dot-kernel cell. No positive-dimension, nonzero-input or matrix definiteness assumption
is needed. All conclusions are flat facts about the actual returned state. -/
theorem exec_cg_initialization (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (b : Fin N → ℝ) (vals : ℕ → ℝ)
    (hshape : st.store.shape = #[(tag, N), (tag, N), (tag, N), (tag, N),
      (tag, 1), (tag, N * N), (tag, N), (tag, 9)])
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hrom : ∀ i < N * N, I.rom i = some (vals i)) :
    ∃ out, exec I (do
        forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
        ins (.lit tag ⟨7, 6⟩ 0)
        ins (.lit tag ⟨7, 7⟩ 1)
        ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
        ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
        forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
        copyv tag 0 0 2 0 (.const N)
        copyv tag 0 0 3 0 (.const N)
        dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
        ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
          (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, out.store.read tag 0 i = some (b i)) ∧
      Holds out.store tag 5 0 (fun (i j : Fin N) => vals (i + N * j)) ∧
      (∀ i : Fin N, out.store.read tag 1 i = some 0) ∧
      (∀ i : Fin N, out.store.read tag 2 i = some (b i)) ∧
      (∀ i : Fin N, out.store.read tag 3 i = some (b i)) ∧
      out.store.read tag 7 0 = some (b ⬝ᵥ b) ∧
      out.store.read tag 7 6 = some 0 ∧ out.store.read tag 7 7 = some 1 ∧
      out.store.read tag 7 8 = some (-1) ∧
      out.store.read tag 4 0 = some (if b = 0 then 1 else 0) ∧
      (∀ q buf i, buf ≠ 1 → buf ≠ 2 → buf ≠ 3 → buf ≠ 4 → buf ≠ 5 →
        (buf ≠ 7 ∨ i ≠ 0 ∧ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 8) →
        out.store.read q buf i = st.store.read q buf i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt ≤ st.cnt + cgCount tag N 0 ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  obtain ⟨pre, epre, shpre, mat, rz, ro, rn, rs, fpre, statepre⟩ :=
    exec_cg_preload I hI tag st N vals (by rw [hshape]; rfl) (by rw [hshape]; rfl)
      (by rw [hshape]; rfl) hrom
  have rbpre (i : Fin N) : pre.store.read tag 0 i = some (b i) :=
    (fpre tag 0 i (by norm_num) (by norm_num) (Or.inl (by norm_num))).trans (hb i)
  obtain ⟨vec, evec, shvec, rx, rr, rp, fvec, posvec, curvec, curWvec, cntvec,
      peakvec, peakWvec⟩ := exec_cg_vectors I hI hc tag pre N b
    (by rw [shpre, hshape]; rfl) (by rw [shpre, hshape]; rfl)
    (by rw [shpre, hshape]; rfl) rbpre
  obtain ⟨out, eout, shout, rnu, rst, fout, posout, curout, curWout, cntout,
      peakout, peakWout⟩ := exec_cg_cache_status I hI hc tag vec N b
    (by rw [shvec, shpre, hshape]; rfl) (by rw [shvec, shpre, hshape]; rfl) rr
    ((fvec tag 7 6 (by norm_num) (by norm_num) (by norm_num)).trans rz)
    ((fvec tag 7 7 (by norm_num) (by norm_num) (by norm_num)).trans ro)
    ((fvec tag 4 0 (by norm_num) (by norm_num) (by norm_num)).trans rs)
  have frame (q : P) (buf i : ℕ) (h1 : buf ≠ 1) (h2 : buf ≠ 2) (h3 : buf ≠ 3)
      (h4 : buf ≠ 4) (h5 : buf ≠ 5)
      (h7 : buf ≠ 7 ∨ i ≠ 0 ∧ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 8) :
      out.store.read q buf i = st.store.read q buf i := by
    rw [fout q buf i (Or.inl h4) (h7.elim Or.inl (fun h => Or.inr h.1)),
      fvec q buf i h1 h2 h3]
    exact fpre q buf i h4 h5 (h7.elim Or.inl (fun h => Or.inr h.2))
  have pospre := congrArg St.pos statepre
  have curpre := congrArg St.cur statepre
  have curWpre := congrArg St.curW statepre
  refine ⟨out, ?_, shout.trans (shvec.trans shpre), ?_, ?_, ?_, ?_, ?_, rnu,
    ?_, ?_, ?_, rst, frame, posout.trans (posvec.trans pospre),
    curout.trans (curvec.trans curpre),
    curWout.trans (curWvec.trans curWpre), ?_, ?_, ?_⟩
  · change exec I ((do
      forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
      ins (.lit tag ⟨7, 6⟩ 0); ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩); ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)) >>= fun _ => (do
        forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
        copyv tag 0 0 2 0 (.const N); copyv tag 0 0 3 0 (.const N)) >>= fun _ => (do
          dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
          ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
            (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))).run st = some out
    rw [composable_cg_preload I tag N, epre, Option.bind_some,
      executionComposable_cg_vectors I tag N, evec, Option.bind_some]
    exact eout
  · intro i
    exact (frame tag 0 i (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (Or.inl (by norm_num))).trans (hb i)
  · intro i j
    rw [fout tag 5 (0 + i + N * j) (Or.inl (by norm_num)) (Or.inl (by norm_num)),
      fvec tag 5 (0 + i + N * j) (by norm_num) (by norm_num) (by norm_num)]
    exact mat i j
  · intro i
    exact (fout tag 1 i (Or.inl (by norm_num)) (Or.inl (by norm_num))).trans (rx i)
  · intro i
    exact (fout tag 2 i (Or.inl (by norm_num)) (Or.inl (by norm_num))).trans (rr i)
  · intro i
    exact (fout tag 3 i (Or.inl (by norm_num)) (Or.inl (by norm_num))).trans (rp i)
  · rw [fout tag 7 6 (Or.inl (by norm_num)) (Or.inr (by norm_num)),
      fvec tag 7 6 (by norm_num) (by norm_num) (by norm_num)]
    exact rz
  · rw [fout tag 7 7 (Or.inl (by norm_num)) (Or.inr (by norm_num)),
      fvec tag 7 7 (by norm_num) (by norm_num) (by norm_num)]
    exact ro
  · rw [fout tag 7 8 (Or.inl (by norm_num)) (Or.inr (by norm_num)),
      fvec tag 7 8 (by norm_num) (by norm_num) (by norm_num)]
    exact rn
  · rw [cntvec, congrArg St.cnt statepre] at cntout
    simp only [hc.charge_eq] at cntout
    rw [cg_count_zero_eq]
    exact cntout.trans_eq (by abel)
  · rw [peakout, peakvec, congrArg St.peak statepre, curvec, congrArg St.cur statepre]
  · rw [peakWout, peakWvec, congrArg St.peakW statepre, curWvec, congrArg St.curW statepre]

/-- The actual complete initializer prefix composes with subsequent loop execution,
without changing or regrouping the canonical program tree. -/
theorem executionComposable_cg_initialization (I : Interp P ι ℝ (OpCount P ι))
    (tag : P) (N : ℕ) : ExecutionComposable I (do
      forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
      ins (.lit tag ⟨7, 6⟩ 0)
      ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
      ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
      forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (.const N)
      copyv tag 0 0 3 0 (.const N)
      dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩ (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())) := by
  exact (composable_cg_preload I tag N).bind ((executionComposable_cg_vectors I tag N).bind
    ((executionComposable_single I (b := dot tag ⟨7, 0⟩ 2 0 2 0 (.const N))
      (fun _ => rfl)).bind (executionComposable_single I (b := ifThenElse tag .eq
        ⟨7, 0⟩ ⟨7, 6⟩ (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())) (fun _ => rfl))))

end NLAlib.CGImplementation
