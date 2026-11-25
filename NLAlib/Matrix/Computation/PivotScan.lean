/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Order.Fin.Basic
public import NLAlib.Computation.Contract
public import NLAlib.Computation.RoutineFrames

/-!
# Stored absolute-value pivot scans

Pivot searches compare absolute values of the current decoded stored entries. `copyAbs`
computes this magnitude by an exact sign test and negation, without introducing a rounded
square or square root. Its execution theorem retains the exact output write.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main definitions

* `NLAlib.Computation.copyAbs`: copy the absolute value of a real decoded scalar.
* `NLAlib.Computation.pivotScanUpdate`: retain an incumbent unless a candidate is strictly larger.
* `NLAlib.Computation.initializePivotScan`: initialize a magnitude, zero and index.
* `NLAlib.Computation.pivotScanLoop`: scan with initialized caller-owned workspace.
* `NLAlib.Computation.argmaxAbs`: the pivot scan with scoped workspace.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_copyAbs`: success, exact magnitude and one output write.
* `NLAlib.Computation.IsRelErrSem.exec_pivotScanUpdate`: a successful stable maximum update.
* `NLAlib.Computation.IsRelErrSem.exec_pivotScanLoop`: the first maximum with explicit workspace.
* `NLAlib.Computation.IsRelErrSem.exec_argmaxAbs`: the scoped scan and single output block write.
* `NLAlib.Computation.executionComposable_argmaxAbs`: composition with a following routine.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Copy a real decoded scalar's absolute value to `dst`, using a cell `zero` decoding to zero
and an exact comparison followed by either negation or a copy. No magnitude is squared. -/
def copyAbs {P ι VB VI : Type} (tag : P) (dst src zero : Cell VB VI) :
    Builder P ι VB VI Unit :=
  ifThenElse tag .lt src zero
    (ins (.un tag .neg dst src)) (ins (.copy tag dst src))

/-- Retain a stored incumbent magnitude and index unless the candidate magnitude is strictly
larger, then copy the candidate magnitude and store its exact index literal. Equal magnitudes
retain the incumbent, so a scan in increasing order selects the first maximum. -/
def pivotScanUpdate {P ι VB VI : Type} (tag : P) (best index candidate : Cell VB VI)
    (k : IExp VI) : Builder P ι VB VI Unit :=
  ifThenElse tag .lt best candidate
    (do ins (.copy tag best candidate); ins (.litIdx tag index k)) (pure ())

/-- Scan magnitudes in increasing index order using three caller-owned workspace cells:
the incumbent magnitude at offset zero, an exact zero at offset one and a candidate at offset
two. The incumbent and output index must initially describe an entry of the input vector.
Equal magnitudes retain the incumbent. -/
def pivotScanLoop {P ι VB VI : Type} (tag : P) (n : IExp VI) (x : VB) (xo : IExp VI)
    (scratch : VB) (index : Cell VB VI) : Builder P ι VB VI Unit :=
  forRange n fun k => do
    copyAbs tag ⟨scratch, 2⟩ ⟨x, xo + IExp.var k⟩ ⟨scratch, 1⟩
    pivotScanUpdate tag ⟨scratch, 0⟩ index ⟨scratch, 2⟩ (.var k)

/-- Initialize a pivot scan's incumbent to the magnitude of the first input entry, its zero
cell to zero and its output index to zero. The workspace buffer has three cells. -/
def initializePivotScan {P ι VB VI : Type} (tag : P) (x : VB) (xo : IExp VI)
    (scratch : VB) (index : Cell VB VI) : Builder P ι VB VI Unit := scope do
  ins (.lit tag ⟨scratch, 1⟩ 0)
  copyAbs tag ⟨scratch, 0⟩ ⟨x, xo⟩ ⟨scratch, 1⟩
  ins (.litIdx tag index 0)

/-- Return the first index of an entry of largest absolute value in a nonempty stored vector.
The result is an exact natural index literal; the three magnitude workspace cells are scoped.
Ties retain the first index, including index zero when every entry is zero. -/
def argmaxAbs {P ι VB VI : Type} (tag : P) (n : IExp VI) (x : VB) (xo : IExp VI)
    (index : Cell VB VI) : Builder P ι VB VI Unit := scope do
  let scratch ← alloc tag 3
  initializePivotScan tag x xo scratch index
  pivotScanLoop tag n x xo scratch index

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Under the standard scalar model, an initialized source and zero cell and a writable
destination imply successful absolute-value copying. The only net effect on the store is
one destination write, and its decoding is exactly the absolute value of the input decoding.
The destination may coincide with either input cell. -/
theorem IsRelErrSem.exec_copyAbs {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (I : Interp P ι K C) (h : IsRelErrSem u dec safe I.sem)
    (tag : P) (st : St P K C) (dst src zero : Cell ℕ ℕ)
    (v z : K) (hv : st.store.read tag src.buf src.idx.eval = some v)
    (hz : st.store.read tag zero.buf zero.idx.eval = some z) (hdz : dec tag z = 0)
    (hd : ∃ len, st.store.shape[dst.buf]? = some (tag, len) ∧ dst.idx.eval < len) :
    ∃ (out : St P K C) (w : K), exec I (copyAbs tag dst src zero).run st = some out ∧
      st.store.write tag dst.buf dst.idx.eval w = some out.store ∧
      dec tag w = |dec tag v| := by
  let tested : St P K C := { st with cnt := st.cnt + I.charge (.cmp tag) }
  have hc : cmpStep I tag .lt src zero st =
      some (decide (dec tag v < 0), tested) := by
    simp only [cmpStep, hv, hz, Option.bind_some, h.cmp_lt, hdz]
    rfl
  have hrun : (copyAbs tag dst src zero : Builder P ι ℕ ℕ Unit).run =
      .seq (.ite tag .lt src zero (ins (.un tag .neg dst src)).run
        (ins (.copy tag dst src)).run) .skip := rfl
  simp only [hrun, exec_seq_skip, exec_ite, hc, Option.bind_some]
  by_cases hneg : dec tag v < 0
  · obtain ⟨w, hw, hdw⟩ := h.neg tag v
    obtain ⟨s, hs, hr, -, -, -⟩ := exec_scalar_un I tag tested .neg dst src v w hv hw hd
    refine ⟨{ tested with store := s, cnt := tested.cnt + I.charge (.un tag .neg) },
      w, ?_, hs, ?_⟩
    · simpa only [hneg, decide_true, ↓reduceIte] using hr
    · rw [hdw, abs_of_neg hneg]
  · obtain ⟨s, hs, hr, -, -, -⟩ := exec_scalar_copy I tag tested dst src v hv hd
    refine ⟨{ tested with store := s, cnt := tested.cnt + I.charge (.copy tag) },
      v, ?_, hs, ?_⟩
    · simpa only [hneg, decide_false, Bool.false_eq_true, ↓reduceIte] using hr
    · exact (abs_of_nonneg (le_of_not_gt hneg)).symm

/-- A stable maximum update succeeds under exact decoded comparisons and exact natural
literals. Its two stored outputs decode to the larger magnitude and the associated index;
ties preserve the incumbent. Every other cell and every buffer shape is retained. -/
theorem IsRelErrSem.exec_pivotScanUpdate {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (I : Interp P ι K C) (h : IsRelErrSem u dec safe I.sem)
    {B : ℕ} (hi : IsExactIntLit dec I.sem B) (tag : P) (st : St P K C)
    (best index candidate : Cell ℕ ℕ) (k : IExp ℕ) (hk : k.eval ≤ B)
    (b i c : K) (hb : st.store.read tag best.buf best.idx.eval = some b)
    (hidx : st.store.read tag index.buf index.idx.eval = some i)
    (hc : st.store.read tag candidate.buf candidate.idx.eval = some c)
    (hbi : best.buf ≠ index.buf ∨ best.idx.eval ≠ index.idx.eval) :
    ∃ (out : St P K C) (b' i' : K),
      exec I (pivotScanUpdate tag best index candidate k).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag best.buf best.idx.eval = some b' ∧
      out.store.read tag index.buf index.idx.eval = some i' ∧
      dec tag b' = max (dec tag b) (dec tag c) ∧
      dec tag i' = (if dec tag b < dec tag c then (k.eval : ℝ) else dec tag i) ∧
      ∀ q buf j, (buf ≠ best.buf ∨ j ≠ best.idx.eval) →
        (buf ≠ index.buf ∨ j ≠ index.idx.eval) →
        out.store.read q buf j = st.store.read q buf j := by
  let tested : St P K C := { st with cnt := st.cnt + I.charge (.cmp tag) }
  have ht : cmpStep I tag .lt best candidate st =
      some (decide (dec tag b < dec tag c), tested) := by
    simp only [cmpStep, hb, hc, Option.bind_some, h.cmp_lt]
    rfl
  have hrun : (pivotScanUpdate tag best index candidate k : Builder P ι ℕ ℕ Unit).run =
      .seq (.ite tag .lt best candidate
        (.seq (.instr (.copy tag best candidate))
          (.seq (.instr (.litIdx tag index k)) .skip)) .skip) .skip := rfl
  simp only [hrun, exec_seq_skip, exec_ite, ht, Option.bind_some]
  by_cases hlt : dec tag b < dec tag c
  · obtain ⟨iw, hiw, hdi⟩ := hi tag k.eval hk
    obtain ⟨s₁, hs₁⟩ := Store.exists_write_eq_some_of_read_eq_some (v := c) hb
    have hidx₁ : s₁.read tag index.buf index.idx.eval = some i := by
      rw [Store.read_of_write_eq_some_of_ne hs₁ (hbi.imp Ne.symm Ne.symm)]
      exact hidx
    obtain ⟨s₂, hs₂⟩ := Store.exists_write_eq_some_of_read_eq_some (v := iw) hidx₁
    let out : St P K C := { tested with
      store := s₂
      cnt := (tested.cnt + I.charge (.copy tag)) + I.charge (.lit tag) }
    refine ⟨out, c, iw, ?_, (Store.shape_of_write_eq_some hs₂).trans
      (Store.shape_of_write_eq_some hs₁), ?_, Store.read_of_write_eq_some hs₂,
      (max_eq_right hlt.le).symm, by simpa only [hlt, ↓reduceIte] using hdi, ?_⟩
    · simp only [hlt, decide_true, ↓reduceIte]
      rw [exec_seq_instr_copy I (st := tested) hc hs₁,
        exec_seq_instr_litIdx I hiw hs₂, exec_skip]
    · rw [Store.read_of_write_eq_some_of_ne hs₂ hbi]
      exact Store.read_of_write_eq_some hs₁
    · intro q buf j hb' hi'
      exact (Store.read_of_write_eq_some_of_ne hs₂ hi').trans
        (Store.read_of_write_eq_some_of_ne hs₁ hb')
  · refine ⟨tested, b, i, ?_, rfl, hb, hidx, (max_eq_left (le_of_not_gt hlt)).symm,
      by simp only [hlt, ↓reduceIte], fun _ _ _ _ _ => rfl⟩
    simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact exec_skip I tested

private structure ScanState {N : ℕ} (dec : P → K → ℝ) (tag : P) (x : Fin N → ℝ)
    (scratch : ℕ) (index : Cell ℕ ℕ) (z : K) (initial : Store P K)
    (k : ℕ) (s : Store P K) : Prop where
  shape : s.shape = initial.shape
  frame : ∀ q b j, b ≠ scratch → (b ≠ index.buf ∨ j ≠ index.idx.eval) →
    s.read q b j = initial.read q b j
  zero : s.read tag scratch 1 = some z
  values : ∃ b i : K, ∃ chosen : Fin N,
    s.read tag scratch 0 = some b ∧ s.read tag index.buf index.idx.eval = some i ∧
    dec tag b = |x chosen| ∧ dec tag i = chosen.val ∧
    (∀ l : Fin N, l.val < k → |x l| ≤ |x chosen|) ∧
    (∀ l : Fin N, l < chosen → |x l| < |x chosen|)

private theorem exists_exec_scan_step {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (I : Interp P ι K C) (h : IsRelErrSem u dec safe I.sem)
    {N B : ℕ} (hi : IsExactIntLit dec I.sem B) (hB : N ≤ B)
    (tag : P) (initial : Store P K) (x : Fin N → ℝ) (xb : ℕ) (xo : IExp ℕ)
    (scratch : ℕ) (index : Cell ℕ ℕ) (z : K) (hz : dec tag z = 0)
    (hin : ReadsDecoded initial dec tag xb xo.eval x)
    (hsh : initial.shape[scratch]? = some (tag, 3))
    (hxs : xb ≠ scratch) (hxi : xb ≠ index.buf) (hsi : scratch ≠ index.buf)
    (k : ℕ) (hk : k < N) (st : St P K C)
    (hs : ScanState dec tag x scratch index z initial k st.store) :
    ∃ out, exec I (do
      copyAbs tag ⟨scratch, 2⟩ ⟨xb, xo + IExp.var k⟩ ⟨scratch, 1⟩
      pivotScanUpdate tag ⟨scratch, 0⟩ index ⟨scratch, 2⟩ (.var k)).run st = some out ∧
      ScanState dec tag x scratch index z initial (k + 1) out.store := by
  obtain ⟨bw, iw, chosen, hbw, hiw, hdb, hdi, hdom, hfirst⟩ := hs.values
  obtain ⟨v, hv, hdv⟩ := hin ⟨k, hk⟩
  have hv' : st.store.read tag xb (xo.eval + k) = some v := by
    rw [hs.frame tag xb _ hxs (Or.inl hxi)]
    exact hv
  obtain ⟨mid, cw, hr₁, hw₁, hdc⟩ := h.exec_copyAbs I tag st
    ⟨scratch, 2⟩ ⟨xb, xo + IExp.var k⟩ ⟨scratch, 1⟩ v z hv' hs.zero hz
    ⟨3, hs.shape ▸ hsh, by norm_num [IExp.eval]⟩
  have hbw' : mid.store.read tag scratch 0 = some bw := by
    rw [Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega : 0 ≠ 2))]
    exact hbw
  have hiw' : mid.store.read tag index.buf index.idx.eval = some iw := by
    rw [Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hsi.symm)]
    exact hiw
  obtain ⟨out, bw', iw', hr₂, hshape, hreadb, hreadi, hdb', hdi', hframe⟩ :=
    h.exec_pivotScanUpdate I hi tag mid ⟨scratch, 0⟩ index ⟨scratch, 2⟩ (.var k)
      (by dsimp; omega) bw iw cw hbw' hiw' (Store.read_of_write_eq_some hw₁) (Or.inl hsi)
  let candidate : Fin N := ⟨k, hk⟩
  let selected := if |x chosen| < |x candidate| then candidate else chosen
  have hc : dec tag cw = |x candidate| := by simpa only [hdv] using hdc
  obtain ⟨hmax, hdom', hfirst'⟩ :=
    Fin.max_eq_score_choose_of_prefix (fun i => |x i|) chosen candidate rfl hdom hfirst
  refine ⟨out, ?_, ⟨hshape.trans ((Store.shape_of_write_eq_some hw₁).trans hs.shape),
    ?_, ?_, bw', iw', selected, hreadb, hreadi, ?_, ?_, hdom', hfirst'⟩⟩
  · rw [exec_run_bind I
      (b := copyAbs tag ⟨scratch, 2⟩ ⟨xb, xo + IExp.var k⟩ ⟨scratch, 1⟩)
      (fun _ => rfl), hr₁, Option.bind_some]
    exact hr₂
  · intro q b j hbs hbi
    rw [hframe q b j (Or.inl hbs) hbi,
      Store.read_of_write_eq_some_of_ne hw₁ (Or.inl hbs)]
    exact hs.frame q b j hbs hbi
  · rw [hframe tag scratch 1 (Or.inr (by omega : 1 ≠ 0)) (Or.inl hsi),
      Store.read_of_write_eq_some_of_ne hw₁ (Or.inr (by omega : 1 ≠ 2))]
    exact hs.zero
  · rw [hdb', hdb, hc]
    exact hmax
  · simpa only [hdb, hc, hdi, IExp.eval_var, selected, apply_ite, candidate] using hdi'

/-- A magnitude scan with initialized workspace succeeds and returns the first index of a
largest absolute decoded input entry. Exact natural literals preserve the selected index;
the input vector, every other cell outside the output index and workspace, and all buffer
shapes are retained. The workspace holds an initial incumbent magnitude, an exact zero and
one writable candidate cell. -/
theorem IsRelErrSem.exec_pivotScanLoop {u : P → ℝ} {dec : P → K → ℝ}
    {safe : P → ℝ → Prop} (I : Interp P ι K C) (h : IsRelErrSem u dec safe I.sem)
    {N B : ℕ} (hi : IsExactIntLit dec I.sem B) (hB : N ≤ B) (hN : 0 < N)
    (tag : P) (st : St P K C) (x : Fin N → ℝ) (xb : ℕ) (xo : IExp ℕ)
    (scratch : ℕ) (index : Cell ℕ ℕ) (z bw iw : K) (hz : dec tag z = 0)
    (hin : ReadsDecoded st.store dec tag xb xo.eval x)
    (hsh : st.store.shape[scratch]? = some (tag, 3))
    (hxs : xb ≠ scratch) (hxi : xb ≠ index.buf) (hsi : scratch ≠ index.buf)
    (hzero : st.store.read tag scratch 1 = some z)
    (hbw : st.store.read tag scratch 0 = some bw) (hdb : dec tag bw = |x ⟨0, hN⟩|)
    (hiw : st.store.read tag index.buf index.idx.eval = some iw) (hdi : dec tag iw = 0) :
    ∃ (out : St P K C) (w : K) (chosen : Fin N),
      exec I (pivotScanLoop tag (.const N) xb xo scratch index).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag index.buf index.idx.eval = some w ∧ dec tag w = chosen.val ∧
      (∀ j : Fin N, |x j| ≤ |x chosen|) ∧
      (∀ j : Fin N, j < chosen → |x j| < |x chosen|) ∧
      ∀ q b j, b ≠ scratch → (b ≠ index.buf ∨ j ≠ index.idx.eval) →
        out.store.read q b j = st.store.read q b j := by
  let R := ScanState dec tag x scratch index z st.store
  have h0 : R 0 st.store := by
    refine ⟨rfl, fun _ _ _ _ _ => rfl, hzero, bw, iw, ⟨0, hN⟩,
      hbw, hiw, hdb, by simpa using hdi, ?_, ?_⟩
    · intro j hj
      omega
    · intro j hj
      exact (Nat.not_lt_zero _ hj).elim
  obtain ⟨out, hr, hs⟩ := exists_exec_loop_eq_some_of_forall I (n := .const N)
    (fun k s => R k s.store) h0 (fun k hk s hs =>
      exists_exec_scan_step I h hi hB tag st.store x xb xo scratch index z hz hin hsh
        hxs hxi hsi k hk s hs)
  obtain ⟨bw', iw', chosen, -, hread, -, hdi', hdom, hfirst⟩ := hs.values
  refine ⟨out, iw', chosen, ?_, hs.shape, hread, hdi', fun j => hdom j j.isLt,
    hfirst, hs.frame⟩
  change exec I (.seq (.loop (.const N) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

/-- The scoped absolute-value pivot scan composes with every following builder under the same
interpretation. Its workspace is released before the continuation executes. -/
theorem executionComposable_argmaxAbs (I : Interp P ι K C) (tag : P) (n : IExp ℕ)
    (x : ℕ) (xo : IExp ℕ) (index : Cell ℕ ℕ) :
    ExecutionComposable I (argmaxAbs tag n x xo index) :=
  executionComposable_single I (fun _ => rfl)

private theorem exists_exec_initializePivotScan {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    {N B : ℕ} (hi : IsExactIntLit dec I.sem B) (hN : 0 < N)
    (tag : P) (st : St P K C) (x : Fin N → ℝ) (xb : ℕ) (xo : IExp ℕ)
    (scratch : ℕ) (index : Cell ℕ ℕ) (hin : ReadsDecoded st.store dec tag xb xo.eval x)
    (hsh : st.store.shape[scratch]? = some (tag, 3))
    (hw : Writable st.store tag index.buf index.idx.eval 1)
    (hxs : xb ≠ scratch) (hsi : scratch ≠ index.buf) :
    ∃ (out : St P K C) (z : K),
      exec I (initializePivotScan tag xb xo scratch index).run st = some out ∧
      dec tag z = 0 ∧ ScanState dec tag x scratch index z st.store 0 out.store := by
  obtain ⟨z, hz, hdz⟩ := (h.isArithErrSem fun _ => trivial).lit_zero tag
  obtain ⟨iw, hiw, hdi⟩ := hi tag 0 (Nat.zero_le B)
  obtain ⟨v, hv, hdv⟩ := hin ⟨0, hN⟩
  obtain ⟨s₁, hs₁, -, hshape₁, hread₁, hframe₁⟩ := exec_scalar_lit I tag st
    ⟨scratch, 1⟩ 0 z hz ⟨3, hsh, by norm_num [IExp.eval]⟩
  let st₁ : St P K C := { st with store := s₁, cnt := st.cnt + I.charge (.lit tag) }
  have hv₁ : s₁.read tag xb xo.eval = some v := by
    rw [Store.read_of_write_eq_some_of_ne hs₁ (Or.inl hxs)]
    simpa using hv
  obtain ⟨st₂, bw, hr₂, hs₂, hdb⟩ := h.exec_copyAbs I tag st₁
    ⟨scratch, 0⟩ ⟨xb, xo⟩ ⟨scratch, 1⟩ v z hv₁ hread₁ hdz
    ⟨3, hshape₁ ▸ hsh, by norm_num [IExp.eval]⟩
  obtain ⟨len, hlen, hlt⟩ := hw 0 (by omega)
  have hshape₂ : st₂.store.shape = st.store.shape :=
    (Store.shape_of_write_eq_some hs₂).trans hshape₁
  obtain ⟨s₃, hs₃⟩ := Store.exists_write_eq_some_of_getElem?_shape iw
    (hshape₂ ▸ hlen) (by simpa using hlt)
  let out : St P K C := { st₂ with store := s₃, cnt := st₂.cnt + I.charge (.lit tag) }
  refine ⟨out, z, ?_, hdz, ⟨(Store.shape_of_write_eq_some hs₃).trans hshape₂,
    ?_, ?_, bw, iw, ⟨0, hN⟩, ?_, Store.read_of_write_eq_some hs₃,
    by simpa only [hdv] using hdb, by simpa using hdi, ?_, ?_⟩⟩
  · change exec I (.seq _ .skip) st = some out
    rw [exec_seq_skip]
    change exec I (.seq (.instr (.lit tag ⟨scratch, 1⟩ 0)) _) st = some out
    rw [exec_seq_instr_lit I hz hs₁]
    change exec I (copyAbs tag ⟨scratch, 0⟩ ⟨xb, xo⟩ ⟨scratch, 1⟩ >>= fun _ =>
      ins (.litIdx tag index 0)).run st₁ = some out
    rw [exec_run_bind I
      (b := copyAbs tag ⟨scratch, 0⟩ ⟨xb, xo⟩ ⟨scratch, 1⟩)
      (fun _ => rfl), hr₂, Option.bind_some]
    change exec I (.seq (.instr (.litIdx tag index 0)) .skip) st₂ = some out
    rw [exec_seq_instr_litIdx I (by simpa using hiw) hs₃, exec_skip]
  · intro q b j hbs hbi
    rw [Store.read_of_write_eq_some_of_ne hs₃ hbi,
      Store.read_of_write_eq_some_of_ne hs₂ (Or.inl hbs),
      Store.read_of_write_eq_some_of_ne hs₁ (Or.inl hbs)]
  · rw [Store.read_of_write_eq_some_of_ne hs₃ (Or.inl hsi),
      Store.read_of_write_eq_some_of_ne hs₂ (Or.inr (by omega : 1 ≠ 0))]
    exact hread₁
  · rw [Store.read_of_write_eq_some_of_ne hs₃ (Or.inl hsi)]
    exact Store.read_of_write_eq_some hs₂
  · intro j hj
    omega
  · intro j hj
    exact (Nat.not_lt_zero _ hj).elim

private theorem scan_pop_write (tag : P) (initial final : Store P K)
    (index : Cell ℕ ℕ) (arr : Array (Option K)) (w : K)
    (hshape : final.shape = Store.shape (initial.push (tag, arr)))
    (hw : Writable initial tag index.buf index.idx.eval 1)
    (hread : final.read tag index.buf index.idx.eval = some w)
    (hframe : ∀ q b j, b ≠ initial.size → (b ≠ index.buf ∨ j ≠ index.idx.eval) →
      final.read q b j = Store.read (initial.push (tag, arr)) q b j) :
    initial.writeBlock tag index.buf index.idx.eval #[w] = some final.pop := by
  have hsize : final.size = initial.size + 1 := by
    simpa only [Store.size_shape, Array.size_push] using congrArg Array.size hshape
  have hidx : index.buf < initial.size := hw.lt_size (by omega)
  refine Store.writeBlock_eq_some_of_read ?_ ?_ ?_
  · rw [Store.shape_pop, hshape]
    simp only [Store.shape, Array.map_push, Array.pop_push]
  · intro j hj
    have hj0 : j = 0 := by simpa using hj
    subst j
    rw [Nat.add_zero, Store.read_pop_of_lt (by omega), hread]
    rfl
  · intro q b j hj
    by_cases hb : b < initial.size
    · rw [Store.read_pop_of_lt (by omega), hframe q b j (by omega) (by
        simp only [Array.size_singleton] at hj
        omega), Store.read_push_of_lt hb]
    · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
        Store.read_eq_none_of_size_le (by omega)]

/-- An absolute-value pivot search on a nonempty vector succeeds under the standard real
scalar model and exact natural index literals through its length. It writes one exact index
word selecting the first largest absolute decoded input entry and leaves every other stored
cell unchanged. The input and output occupy different buffers; three scratch cells are scoped.
The comparisons use the current stored entries, including in rounded arithmetic. -/
theorem IsRelErrSem.exec_argmaxAbs {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    {N B : ℕ} (hi : IsExactIntLit dec I.sem B) (hB : N ≤ B) (hN : 0 < N)
    (tag : P) (st : St P K C) (x : Fin N → ℝ) (xb : ℕ) (xo : IExp ℕ)
    (index : Cell ℕ ℕ) (hin : ReadsDecoded st.store dec tag xb xo.eval x)
    (hw : Writable st.store tag index.buf index.idx.eval 1) (hxi : xb ≠ index.buf) :
    ∃ (out : St P K C) (w : K) (chosen : Fin N),
      exec I (argmaxAbs tag (.const N) xb xo index).run st = some out ∧
      st.store.writeBlock tag index.buf index.idx.eval #[w] = some out.store ∧
      dec tag w = chosen.val ∧ (∀ j : Fin N, |x j| ≤ |x chosen|) ∧
      (∀ j : Fin N, j < chosen → |x j| < |x chosen|) := by
  let Q : Store P K → Prop := fun s => ∃ (w : K) (chosen : Fin N),
    st.store.writeBlock tag index.buf index.idx.eval #[w] = some s ∧
    dec tag w = chosen.val ∧ (∀ j : Fin N, |x j| ≤ |x chosen|) ∧
    (∀ j : Fin N, j < chosen → |x j| < |x chosen|)
  have hidx : index.buf < st.store.size := hw.lt_size (by omega)
  obtain ⟨v, hv, -⟩ := hin ⟨0, hN⟩
  have hxb : xb < st.store.size := Store.lt_size_of_read_eq_some hv
  have hbody : ∀ σ : St P K C,
      σ.store = st.store.push (tag, Array.replicate 3 none) →
      ∃ out, exec I (do
        initializePivotScan tag xb xo st.store.size index
        pivotScanLoop tag (.const N) xb xo st.store.size index).run σ = some out ∧
        Q out.store.pop := by
    intro σ hσ
    have hinσ : ReadsDecoded σ.store dec tag xb xo.eval x :=
      hσ ▸ hin.push (tag, Array.replicate 3 none)
    have hwσ : Writable σ.store tag index.buf index.idx.eval 1 :=
      hσ ▸ hw.push (tag, Array.replicate 3 none)
    have hshσ : σ.store.shape[st.store.size]? = some (tag, 3) := by
      rw [hσ]
      exact Store.getElem?_shape_push_size _ _ _
    obtain ⟨mid, z, hr₁, hz, hs⟩ := exists_exec_initializePivotScan I h hi hN tag σ x xb xo
      st.store.size index hinσ hshσ hwσ (Nat.ne_of_lt hxb) (Nat.ne_of_gt hidx)
    obtain ⟨out, hr₂, hfinal⟩ := exists_exec_loop_eq_some_of_forall I (n := .const N)
      (fun k s => ScanState dec tag x st.store.size index z σ.store k s.store) hs
      (fun k hk s hs => exists_exec_scan_step I h hi hB tag σ.store x xb xo
        st.store.size index z hz hinσ hshσ (Nat.ne_of_lt hxb) hxi
        (Nat.ne_of_gt hidx) k hk s hs)
    obtain ⟨bw', iw', selected, -, hread, -, hdi', hdom', hfirst'⟩ := hfinal.values
    refine ⟨out, ?_, iw', selected, ?_, hdi', fun j => hdom' j j.isLt, hfirst'⟩
    · rw [exec_run_bind I
        (b := initializePivotScan tag xb xo st.store.size index) (fun _ => rfl),
        hr₁, Option.bind_some]
      change exec I (.seq (.loop (.const N) _) .skip) mid = some out
      rw [exec_seq_skip]
      exact hr₂
    · exact scan_pop_write tag st.store out.store index (Array.replicate 3 none) iw'
        (hfinal.shape.trans (congrArg Store.shape hσ)) hw hread
        (by simpa only [hσ] using hfinal.frame)
  obtain ⟨out, hr, w, chosen, hwrite, hdec, hmax, hfirst⟩ :=
    exists_exec_alloc I tag (.const 3) (fun scratch => ((do
      initializePivotScan tag xb xo scratch index
      pivotScanLoop tag (.const N) xb xo scratch index) : Builder P ι ℕ ℕ Unit).run) st Q hbody
  refine ⟨out, w, chosen, ?_, hwrite, hdec, hmax, hfirst⟩
  change exec I (.seq (.alloc tag 3 _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

end NLAlib.Computation
