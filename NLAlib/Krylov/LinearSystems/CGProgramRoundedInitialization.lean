/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramRoundedRun

/-!
# Actual rounded CG initialization instructions

Supporting frames for the canonical initializer under the existing scalar arithmetic
contract. Literal one is rounded and its decoding is proved positive, rather than equated
to one. No alternate program or numerical run interface is introduced.

## Main results

* `NLAlib.CGImplementation.exec_rounded_initialization`: the actual complete initializer.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation Computation.Builder
open scoped Matrix

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {u : P → ℝ} {dec : P → K → ℝ} {storedMatrix : Bool}

omit [DecidableEq P] [AddMonoid C] in
/-- Local zero and one literal facts, together with defined exact negation, supply the
actual CG flag words. The positive flag need not decode to one: its relative literal
accuracy is retained, and its sign follows from unit roundoff below one. No arithmetic,
comparison, square-root or global range contract is needed. -/
theorem exists_cg_flag_words (I : Interp P ι K C) (tag : P)
    (hzero : ∃ zero, I.sem.lit tag 0 = some zero ∧ dec tag zero = 0)
    (hone : ∃ one, I.sem.lit tag 1 = some one ∧ RelErr (u tag) 1 (dec tag one))
    (hneg : ∀ x, ∃ z, I.sem.un tag .neg x = some z ∧ dec tag z = -dec tag x)
    (hu : u tag < 1) :
    ∃ zero one negative : K, I.sem.lit tag 0 = some zero ∧ dec tag zero = 0 ∧
      I.sem.lit tag 1 = some one ∧ 0 < dec tag one ∧ |dec tag one - 1| ≤ u tag ∧
      I.sem.un tag .neg one = some negative ∧ dec tag negative = -dec tag one := by
  obtain ⟨zero, hz, hd0⟩ := hzero
  obtain ⟨one, ho, d, hd, hdo⟩ := hone
  have hone' : dec tag one = 1 + d := by simpa only [one_mul] using hdo
  obtain ⟨negative, hn, hdn⟩ := hneg one
  refine ⟨zero, one, negative, hz, hd0, ho, ?_, ?_, hn, hdn⟩
  · rw [hone']
    linarith [(abs_le.mp hd).1]
  · simpa only [hone', add_sub_cancel_left] using hd

/-- The actual constant setup in the canonical CG initializer, including its actual writes,
full outside-cell frame and exact charged state. -/
theorem exec_cg_constant_words (I : Interp P ι K C) (tag : P)
    (zero one negative : K) (hz : I.sem.lit tag 0 = some zero)
    (ho : I.sem.lit tag 1 = some one) (hn : I.sem.un tag .neg one = some negative) (st : St P K C)
    (h7 : st.store.shape[7]? = some (tag, 9))
    (h4 : st.store.shape[4]? = some (tag, 1)) :
    ∃ out, exec I (do
        ins (.lit tag ⟨7, 6⟩ 0)
        ins (.lit tag ⟨7, 7⟩ 1)
        ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
        ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag 7 6 = some zero ∧ out.store.read tag 7 7 = some one ∧
      out.store.read tag 7 8 = some negative ∧ out.store.read tag 4 0 = some zero ∧
      (∀ q b i, b ≠ 4 → (b ≠ 7 ∨ i ≠ 6 ∧ i ≠ 7 ∧ i ≠ 8) →
        out.store.read q b i = st.store.read q b i) ∧
      out = { st with
        store := out.store
        cnt := st.cnt + I.charge (.lit tag) + I.charge (.lit tag) +
          I.charge (.un tag .neg) + I.charge (.copy tag) } := by
  have cap (s : Store P K) (hs : s.shape = st.store.shape) (i : ℕ) (hi : i < 9) :
      ∃ len, s.shape[7]? = some (tag, len) ∧ i < len :=
    ⟨9, hs ▸ h7, hi⟩
  obtain ⟨s0, w0, e0, sh0, r0, f0⟩ := exec_scalar_lit I tag st ⟨7, 6⟩ 0 zero
    hz (cap _ rfl 6 (by omega))
  let st1 := { st with store := s0, cnt := st.cnt + I.charge (.lit tag) }
  obtain ⟨s1, w1, e1, sh1, r1, f1⟩ := exec_scalar_lit I tag st1 ⟨7, 7⟩ 1 one
    ho (cap _ sh0 7 (by omega))
  let st2 := { st1 with store := s1, cnt := st1.cnt + I.charge (.lit tag) }
  obtain ⟨s2, w2, e2, sh2, r2, f2⟩ := exec_scalar_un I tag st2 .neg ⟨7, 8⟩ ⟨7, 7⟩
    one negative r1 hn (cap _ (sh1.trans sh0) 8 (by omega))
  let st3 := { st2 with store := s2, cnt := st2.cnt + I.charge (.un tag .neg) }
  have r03 : st3.store.read tag 7 6 = some zero := by
    rw [f2 tag 7 6 (Or.inr (Or.inr (by norm_num))), f1 tag 7 6 (Or.inr (Or.inr (by norm_num)))]
    exact r0
  obtain ⟨s3, w3, e3, sh3, r3, f3⟩ := exec_scalar_copy I tag st3 ⟨4, 0⟩ ⟨7, 6⟩ zero r03
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

/-- The actual vector initialization writes zero iterate and copies the input into residual
and direction. No scratch allocation occurs, and all other buffers retain their contents. -/
theorem exec_cg_vector_words (I : Interp P ι K (OpCount P ι))
    (tag : P) (zero : K) (hzero : I.sem.lit tag 0 = some zero)
    (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N : ℕ) (b : Fin N → K)
    (h1 : st.store.shape[1]? = some (tag, N))
    (h2 : st.store.shape[2]? = some (tag, N))
    (h3 : st.store.shape[3]? = some (tag, N))
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i)) :
    ∃ out, exec I (do
        forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
        copyv tag 0 0 2 0 (.const N)
        copyv tag 0 0 3 0 (.const N)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, out.store.read tag 1 i = some zero) ∧
      (∀ i : Fin N, out.store.read tag 2 i = some (b i)) ∧
      (∀ i : Fin N, out.store.read tag 3 i = some (b i)) ∧
      (∀ q buf i, buf ≠ 1 → buf ≠ 2 → buf ≠ 3 →
        out.store.read q buf i = st.store.read q buf i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + N • Finsupp.single (.lit tag) 1 +
        N • Finsupp.single (.copy tag) 1 + N • Finsupp.single (.copy tag) 1 ∧
      out.peak = st.peak ∧ out.peakW = st.peakW := by
  let xs : ℕ → K := fun i => if hi : i < N then b ⟨i, hi⟩ else zero
  obtain ⟨s0, e0, sh0, r0, f0⟩ := exec_forRange_literal_zero_var I tag zero hzero st
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

/-- ROM loading and scalar setup execute in canonical order before vector initialization. -/
theorem exec_cg_preload_words (I : Interp P ι K (OpCount P ι)) (tag : P)
    (zero one negative : K) (hz : I.sem.lit tag 0 = some zero)
    (ho : I.sem.lit tag 1 = some one) (hn : I.sem.un tag .neg one = some negative)
    (st : St P K (OpCount P ι)) (N : ℕ) (vals : ℕ → K)
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
      out.store.read tag 7 6 = some zero ∧ out.store.read tag 7 7 = some one ∧
      out.store.read tag 7 8 = some negative ∧ out.store.read tag 4 0 = some zero ∧
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
    exec_cg_constant_words I tag zero one negative hz ho hn stR
      (sh ▸ h7) (sh ▸ h4)
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

theorem executionComposable_rounded_preload (I : Interp P ι K (OpCount P ι)) (tag : P) (N : ℕ) :
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

theorem executionComposable_rounded_vectors (I : Interp P ι K (OpCount P ι)) (tag : P) (N : ℕ) :
    ExecutionComposable I (do
      forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (.const N)
      copyv tag 0 0 3 0 (.const N)) := by
  exact (executionComposable_single I (b := forRange (.const N) fun i =>
    ins (.lit tag ⟨1, .var i⟩ 0)) (fun _ => rfl)).bind
    ((executionComposable_single I (b := copyv tag 0 0 2 0 (.const N)) (fun _ => rfl)).bind
      (executionComposable_single I (b := copyv tag 0 0 3 0 (.const N)) (fun _ => rfl)))

/-- ROM loading, actual literal setup and vector initialization compose in the canonical
order from the actual flag words and their local literal/negation facts. No global scalar
arithmetic contract is needed. Input and matrix words are retained exactly; the positive
flag's supplied accuracy and sign are preserved. -/
theorem exec_rounded_setup (I : Interp P ι K (OpCount P ι)) (tag : P)
    (zero one negative : K) (hz : I.sem.lit tag 0 = some zero) (hd0 : dec tag zero = 0)
    (ho : I.sem.lit tag 1 = some one) (hpos : 0 < dec tag one)
    (herr : |dec tag one - 1| ≤ u tag) (hn : I.sem.un tag .neg one = some negative)
    (hdn : dec tag negative = -dec tag one)
    (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N : ℕ) (b : Fin N → K) (vals : ℕ → K)
    (hshape : st.store.shape = workspaceShape tag N)
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hrom : ∀ i < N * N, I.rom i = some (vals i)) :
    ∃ (out : St P K (OpCount P ι)) (zero one negative : K),
      exec I (do
        forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
        ins (.lit tag ⟨7, 6⟩ 0)
        ins (.lit tag ⟨7, 7⟩ 1)
        ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
        ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
        forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
        copyv tag 0 0 2 0 (.const N)
        copyv tag 0 0 3 0 (.const N)).run st = some out ∧
      out.store.shape = workspaceShape tag N ∧
      Holds out.store tag 5 0 (fun i j : Fin N => vals (i + N * j)) ∧
      (∀ i : Fin N, out.store.read tag 0 i = some (b i)) ∧
      (∀ i : Fin N, out.store.read tag 1 i = some zero) ∧
      (∀ i : Fin N, out.store.read tag 2 i = some (b i)) ∧
      (∀ i : Fin N, out.store.read tag 3 i = some (b i)) ∧
      out.store.read tag 7 6 = some zero ∧ out.store.read tag 7 7 = some one ∧
      out.store.read tag 7 8 = some negative ∧ out.store.read tag 4 0 = some zero ∧
      dec tag zero = 0 ∧ 0 < dec tag one ∧ |dec tag one - 1| ≤ u tag ∧
      dec tag negative = -dec tag one := by
  obtain ⟨pre, epre, shpre, mat, rz, ro, rn, rs, fpre, _⟩ :=
    exec_cg_preload_words I tag zero one negative hz ho hn st N vals
      (by simp [hshape, workspaceShape]) (by simp [hshape, workspaceShape])
      (by simp [hshape, workspaceShape]) hrom
  have rbpre (i : Fin N) : pre.store.read tag 0 i = some (b i) :=
    (fpre tag 0 i (by norm_num) (by norm_num) (Or.inl (by norm_num))).trans (hb i)
  obtain ⟨out, evec, shvec, rx, rr, rp, fvec, _⟩ := exec_cg_vector_words I tag zero hz hc
    pre N b (by simp [shpre, hshape, workspaceShape])
      (by simp [shpre, hshape, workspaceShape])
      (by simp [shpre, hshape, workspaceShape]) rbpre
  have frame (buf idx : ℕ) (h1 : buf ≠ 1) (h2 : buf ≠ 2) (h3 : buf ≠ 3) :
      out.store.read tag buf idx = pre.store.read tag buf idx := fvec tag buf idx h1 h2 h3
  refine ⟨out, zero, one, negative, ?_, shvec.trans (shpre.trans hshape), ?_, ?_,
    rx, rr, rp, ?_, ?_, ?_, ?_, hd0, hpos, herr, hdn⟩
  · change exec I ((do
      forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
      ins (.lit tag ⟨7, 6⟩ 0); ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩); ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)) >>= fun _ => (do
        forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
        copyv tag 0 0 2 0 (.const N); copyv tag 0 0 3 0 (.const N))).run st = some out
    rw [executionComposable_rounded_preload I tag N, epre, Option.bind_some]
    exact evec
  · intro i j
    rw [frame 5 _ (by norm_num) (by norm_num) (by norm_num)]
    exact mat i j
  · intro i
    rw [frame 0 _ (by norm_num) (by norm_num) (by norm_num)]
    exact rbpre i
  · exact (frame 7 6 (by norm_num) (by norm_num) (by norm_num)).trans rz
  · exact (frame 7 7 (by norm_num) (by norm_num) (by norm_num)).trans ro
  · exact (frame 7 8 (by norm_num) (by norm_num) (by norm_num)).trans rn
  · exact (frame 4 0 (by norm_num) (by norm_num) (by norm_num)).trans rs

/-- The initial executed self-dot covers empty vectors as well as positive dimension.
Only its actual input reads and writable destination are assumed. -/
theorem exec_rounded_initial_pairing (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K C) (N : ℕ) (b : Fin N → ℝ)
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hr : ∀ i : Fin N, ∃ w, st.store.read tag 2 i = some w ∧ dec tag w = b i)
    (hdst : ∃ v s, st.store.write tag 7 0 v = some s) :
    ∃ out w θ, exec I (dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)).run st = some out ∧
      st.store.write tag 7 0 w = some out.store ∧
      dec tag w = ‖WithLp.toLp 2 b‖ ^ 2 * (1 + θ) ∧
      |θ| ≤ cgImplementationRoundoffBound N (u tag) ∧ 0 ≤ dec tag w ∧
      (dec tag w = 0 ↔ b = 0) := by
  let xs : ℕ → ℝ := fun i => if hi : i < N then b ⟨i, hi⟩ else 0
  have hx (i : ℕ) (hi : i < N) :
      ∃ w, st.store.read tag 2 (0 + i) = some w ∧ dec tag w = xs i := by
    simpa only [zero_add, xs, dif_pos hi] using hr ⟨i, hi⟩
  have hu := hsem.nonneg (p := tag) trivial
  have hn : (N : ℝ) * u tag < 1 := by
    by_cases hN : 0 < N
    · exact (cgImplementationRoundoffBound_kernel_bounds hN hu hsmall).1
    · have : N = 0 := by omega
      simp [this]
  have hγ : roundingFactor N (u tag) ≤ cgImplementationRoundoffBound N (u tag) := by
    by_cases hN : 0 < N
    · exact (cgImplementationRoundoffBound_kernel_bounds hN hu hsmall).2.2
    · have : N = 0 := by omega
      simp [this, roundingFactor, cgImplementationRoundoffBound_def]
  obtain ⟨out, w, he, hw, θ, hθ, heq⟩ := hsem.exec_dot_self_relErr I tag st hz
    ⟨7, 0⟩ 2 0 (.const N) xs hn hx (by norm_num) hdst
  have hxs : (fun i : Fin N => xs i) = b := by funext i; simp only [xs, dif_pos i.isLt]
  change dec tag w = ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ ^ 2 * (1 + θ) at heq
  rw [hxs] at heq
  have hθ' := hθ.trans hγ
  have hfactor : 0 < 1 + θ := by linarith [(abs_le.mp hθ').1]
  refine ⟨out, w, θ, he, hw, heq, hθ', ?_, ?_⟩
  · rw [heq]
    exact mul_nonneg (sq_nonneg _) hfactor.le
  · rw [heq, mul_eq_zero, or_iff_left hfactor.ne', sq_eq_zero_iff, norm_eq_zero,
      WithLp.toLp_eq_zero]

/-- The actual initial cache write turns the initialized words into the existing storage
context. The right-hand side is decoded from retained input words. When `storedMatrix` is
true the matrix is decoded from the loaded words; otherwise the context imposes no
matrix-storage condition. -/
theorem storeContext_of_pairing_write (tag : P) (N : ℕ) (old next : Store P K)
    (b : Fin N → K) (A : Matrix (Fin N) (Fin N) ℝ) (zero one negative word : K)
    (hshape : old.shape = workspaceShape tag N storedMatrix)
    (hmat : if storedMatrix then HoldsDecoded old dec tag 5 0 A else True)
    (hb : ∀ i : Fin N, old.read tag 0 i = some (b i))
    (hx : ∀ i : Fin N, old.read tag 1 i = some zero)
    (hr : ∀ i : Fin N, old.read tag 2 i = some (b i))
    (hp : ∀ i : Fin N, old.read tag 3 i = some (b i))
    (hz : old.read tag 7 6 = some zero) (ho : old.read tag 7 7 = some one)
    (hn : old.read tag 7 8 = some negative) (hs : old.read tag 4 0 = some zero)
    (hdz : dec tag zero = 0) (hdn : dec tag negative = -dec tag one)
    (hw : old.write tag 7 0 word = some next) :
    StoreContext tag dec N A (fun i => dec tag (b i))
      ⟨0, fun i => dec tag (b i), fun i => dec tag (b i)⟩
      (dec tag word) 0 (dec tag one) next storedMatrix := by
  have frame (buf idx : ℕ) (h : buf ≠ 7 ∨ idx ≠ 0) :
      next.read tag buf idx = old.read tag buf idx :=
    Store.read_of_write_eq_some_of_ne hw h
  refine ⟨(Store.shape_of_write_eq_some hw).trans hshape, ?_, ?_, ?_, ?_, ?_,
    ⟨word, Store.read_of_write_eq_some hw, rfl⟩, ?_, ?_, ?_, ?_⟩
  · cases storedMatrix with
    | false => trivial
    | true =>
      intro i j
      rw [frame 5 _ (Or.inl (by norm_num))]
      exact hmat i j
  · intro i
    exact ⟨b i, (frame 0 _ (Or.inl (by norm_num))).trans (hb i), rfl⟩
  · intro i
    exact ⟨zero, (frame 1 _ (Or.inl (by norm_num))).trans (hx i), hdz⟩
  · intro i
    exact ⟨b i, (frame 2 _ (Or.inl (by norm_num))).trans (hr i), rfl⟩
  · intro i
    exact ⟨b i, (frame 3 _ (Or.inl (by norm_num))).trans (hp i), rfl⟩
  · exact ⟨zero, (frame 4 0 (Or.inl (by norm_num))).trans hs, hdz⟩
  · exact ⟨zero, (frame 7 6 (Or.inr (by norm_num))).trans hz, hdz⟩
  · exact ⟨one, (frame 7 7 (Or.inr (by norm_num))).trans ho, rfl⟩
  · exact ⟨negative, (frame 7 8 (Or.inr (by norm_num))).trans hn, hdn⟩

/-- The complete actual initializer supplies the stored header and initial cache errors.
Empty input and empty dimension are included; literal-one positivity needs unit roundoff
below one independently of the dimension-dependent budget. The decoded matrix and input
are obtained from the actual ROM/input words. No desired numerical-state premise is used. -/
theorem exec_rounded_initialization (I : Interp P ι K (OpCount P ι)) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hu : u tag < 1) (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N : ℕ) (b : Fin N → K) (vals : ℕ → K)
    (hshape : st.store.shape = workspaceShape tag N)
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hrom : ∀ i < N * N, I.rom i = some (vals i))
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (predot cached header : St P K (OpCount P ι)) (ν θ flag : ℝ),
      exec I (do
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
          (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())).run st = some header ∧
      predot.store.shape = workspaceShape tag N ∧
      (∀ i : Fin N, ∃ w, predot.store.read tag 2 i = some w ∧ dec tag w = dec tag (b i)) ∧
      exec I (dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)).run predot = some cached ∧
      header.store.read tag 7 0 = cached.store.read tag 7 0 ∧
      StoreContext tag dec N (fun i j => dec tag (vals (i + N * j))) (fun i => dec tag (b i))
        ⟨0, fun i => dec tag (b i), fun i => dec tag (b i)⟩ ν
        (if (fun i : Fin N => dec tag (b i)) = 0 then flag else 0) flag header.store ∧
      ν = ‖WithLp.toLp 2 (fun i : Fin N => dec tag (b i))‖ ^ 2 * (1 + θ) ∧
      |θ| ≤ cgImplementationRoundoffBound N (u tag) ∧ 0 ≤ ν ∧
      (ν = 0 ↔ (fun i : Fin N => dec tag (b i)) = 0) ∧
      0 < flag ∧ |flag - 1| ≤ u tag := by
  classical
  obtain ⟨zeroWord, oneWord, negativeWord, hz0, hdz, ho, hpos0, herr, hn, hdn0⟩ :=
    exists_cg_flag_words I tag ((hsem.isArithErrSem (fun _ => trivial)).lit_zero tag)
      (by
        obtain ⟨one, ho⟩ := hsem.lit_ok tag 1 trivial
        exact ⟨one, ho, by simpa only [RelErr, Rat.cast_one] using hsem.lit_err tag 1 one ho⟩)
      (hsem.neg tag) hu
  obtain ⟨predot, zero, one, negative, epre, sh, mat, rb, rx, rr, rp, rz, ro, rn,
      rs, hd0, hpos, hflag, hdn⟩ := exec_rounded_setup I tag zeroWord oneWord negativeWord
        hz0 hdz ho hpos0 herr hn hdn0 hc st N b vals hshape hb hrom
  have hread (i : Fin N) :
      ∃ w, predot.store.read tag 2 i = some w ∧ dec tag w = dec tag (b i) := ⟨b i, rr i, rfl⟩
  obtain ⟨scratch, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape zero
    (show predot.store.shape[7]? = some (tag, 9) by simp [sh, workspaceShape])
    (show 0 < 9 by norm_num)
  obtain ⟨cached, w, θ, edot, write, heq, hθ, hnonneg, hzero⟩ :=
    exec_rounded_initial_pairing I tag hsem hz predot N (fun i => dec tag (b i)) hsmall
      hread ⟨zero, scratch, hw⟩
  have ctx := storeContext_of_pairing_write tag N predot.store cached.store b
    (fun i j => dec tag (vals (i + N * j))) zero one negative w sh
    (by intro i j; exact ⟨vals (i + N * j), mat i j, rfl⟩) rb rx rr rp rz ro rn rs hd0 hdn write
  obtain ⟨header, estop, hout, frame⟩ := exec_rounded_stop_guard I tag hsem cached N
    (fun i j => dec tag (vals (i + N * j))) (fun i => dec tag (b i))
    ⟨0, fun i => dec tag (b i), fun i => dec tag (b i)⟩ (dec tag w) 0 (dec tag one) ctx
  refine ⟨predot, cached, header, dec tag w, θ, dec tag one, ?_, sh, hread,
    edot, frame tag 7 0 (by norm_num), ?_, heq, hθ, hnonneg, hzero, hpos, hflag⟩
  · change exec I ((do
      forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
      ins (.lit tag ⟨7, 6⟩ 0); ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩); ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)) >>= fun _ => (do
        forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
        copyv tag 0 0 2 0 (.const N); copyv tag 0 0 3 0 (.const N)) >>= fun _ => (do
          dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
          ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
            (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))).run st = some header
    rw [← bind_assoc]
    rw [(executionComposable_rounded_preload I tag N).bind
      (executionComposable_rounded_vectors I tag N)]
    simp only [bind_assoc]
    rw [epre, Option.bind_some, exec_run_bind I
        (b := dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)) (fun _ => rfl), edot, Option.bind_some]
    exact estop
  · simpa only [hzero] using hout

end NLAlib.CGImplementation
