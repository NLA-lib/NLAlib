/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyFactorization
public import NLAlib.Matrix.Factorizations.CholeskyLU
public import NLAlib.Computation.ScalarFrames
public import NLAlib.ForMathlib.Data.Fin.Embedding

/-!
# Converting stored LU factors to Cholesky

The upper pivots are square-rooted in place. Each lower column has its upper prefix explicitly
zeroed and its diagonal-inclusive suffix scaled by that root.

## Main definitions

* `NLAlib.Computation.choleskyScaleColumn`: one actual column conversion.
* `NLAlib.Computation.choleskyScaleColumns`: the full conversion loop.

## Main results

* `NLAlib.Computation.CholeskyScaling.exec_columns`: exact conversion and its complete frame.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Convert one stored LU column to a Cholesky column. Square-root the upper pivot in place,
explicitly zero the lower column's upper prefix, and scale its suffix including the diagonal. -/
def choleskyScaleColumn {P ι VB VI : Type} (p : P) (n k : IExp VI) (L U : VB)
    (lo uo : IExp VI) : Builder P ι VB VI Unit := do
  let diag : Cell VB VI := ⟨U, uo + k + n * k⟩
  ins (.un p .sqrt diag diag)
  forRange k fun i => ins (.lit p ⟨L, lo + n * k + IExp.var i⟩ 0)
  scal p diag L (lo + k + n * k) (n - k)

/-- Convert every column of stored canonical LU factors to the Cholesky factor. -/
def choleskyScaleColumns {P ι VB VI : Type} (p : P) (n : IExp VI) (L U : VB)
    (lo uo : IExp VI) : Builder P ι VB VI Unit :=
  forRange n fun k => choleskyScaleColumn p n (.var k) L U lo uo

variable {P ι : Type} [DecidableEq P]

namespace CholeskyScaling

/-- A complete output frame, the converted-column prefix, untouched remaining lower columns,
and the upper pivots that have not yet been square-rooted. -/
def State (base : Store P ℝ) (p : P) (L U lo uo : ℕ) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) (s : Store P ℝ) : Prop :=
  (∃ g, Store.BlockFrame base p U L lo (N * N) s g) ∧
    (∀ i j : Fin N, s.read p L (lo + i + N * j) =
      some (if j.val < k then choleskyLower A i j else luLower A i j)) ∧
    ∀ j : Fin N, k ≤ j.val → s.read p U (uo + j + N * j) = some (luUpper A j j)

private theorem reads_after_suffix {N k : ℕ} {s s' : Store P ℝ} {p : P}
    {L lo : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hk : k < N) (htail : N - k ≤ N)
    (h : ∀ i j : Fin N, s.read p L (lo + i + N * j) =
      some (if j.val < k then choleskyLower A i j else luLower A i j))
    (hw : s.writeBlock p L (lo + k + N * k)
      (Array.ofFn fun i : Fin (N - k) =>
        choleskyLower A (Fin.natAdd_castLEEmb (htail) i) ⟨k, hk⟩) =
        some s') :
    ∀ i j : Fin N, s'.read p L (lo + i + N * j) =
      some (if j.val < k + 1 then choleskyLower A i j else luLower A i j) := by
  intro i j
  by_cases hj : j.val = k
  · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hj
    simp only [show k < k + 1 by omega, if_pos]
    by_cases hi : k ≤ i.val
    · have hr := Store.read_of_writeBlock_eq_some_of_lt (j := i.val - k) hw
        (by simp only [Array.size_ofFn]; omega)
      have ha : lo + i.val + N * k = lo + k + N * k + (i.val - k) := by omega
      change s'.read p L (lo + i.val + N * k) = some (choleskyLower A i ⟨k, hk⟩)
      rw [ha]
      have he : Fin.natAdd_castLEEmb (htail)
          (⟨i.val - k, by omega⟩ : Fin (N - k)) = i := by
        apply Fin.ext
        rw [Fin.val_natAdd_castLEEmb_sub]
        change k + (i.val - k) = i.val
        omega
      simpa only [Array.getElem?_ofFn, show i.val - k < N - k by omega, dif_pos, he] using hr
    · rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inr (Or.inl (by omega)))]
      rw [h i ⟨k, hk⟩]
      simp only [lt_self_iff_false, if_false]
      have hij : i < (⟨k, hk⟩ : Fin N) := by exact (show i.val < k by omega)
      simp [luLower, choleskyLower, hij.not_ge, hij.not_gt, hij.ne]
  · have hout : L ≠ L ∨ lo + i.val + N * j.val < lo + k + N * k ∨
        lo + k + N * k + (Array.ofFn fun r : Fin (N - k) =>
          choleskyLower A (Fin.natAdd_castLEEmb (htail) r) ⟨k, hk⟩).size ≤
          lo + i.val + N * j.val := by
      simp only [Array.size_ofFn]
      by_cases hjk : j.val < k
      · have := Nat.add_mul_lt_mul_of_lt_of_lt i.isLt hjk
        omega
      · have hm := Nat.mul_le_mul_left N (show k + 1 ≤ j.val by omega)
        rw [Nat.mul_succ] at hm
        omega
    rw [Store.read_of_writeBlock_eq_some_of_ne hw hout, h i j]
    have hiff : (j.val < k) ↔ j.val < k + 1 := by omega
    simp only [← hiff]

private theorem suffix_array {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef)
    (k : ℕ) (hk : k < N) (htail : N - k ≤ N) :
    (List.range (N - k)).toArray.map (fun i => Real.sqrt (luUpper A ⟨k, hk⟩ ⟨k, hk⟩) *
      (if h : k + i < N then luLower A ⟨k + i, h⟩ ⟨k, hk⟩ else 0)) =
      Array.ofFn (fun i : Fin (N - k) =>
        choleskyLower A (Fin.natAdd_castLEEmb (htail) i) ⟨k, hk⟩) := by
  apply Array.ext
  · simp
  · intro i hi hi'
    have hiN : i < N - k := by simpa only [Array.size_ofFn] using hi'
    have hki : k + i < N := by omega
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_range,
      dif_pos hki, Array.getElem_ofFn]
    have he : Fin.natAdd_castLEEmb (htail) (⟨i, hiN⟩ : Fin (N - k)) =
        (⟨k + i, hki⟩ : Fin N) := Fin.ext (Fin.val_natAdd_castLEEmb_sub k _ _)
    rw [he, mul_comm]
    simpa only [RCLike.re_to_real, RCLike.ofReal_real_eq_id, id_eq] using
      hA.luLower_mul_sqrt_luUpper_apply ⟨k + i, hki⟩ ⟨k, hk⟩

private theorem exec_root (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (p : P) (st : St P ℝ (OpCount P ι)) (base : Store P ℝ) (n : IExp ℕ)
    (L U : ℕ) (lo uo : IExp ℕ) (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hA : A.PosDef) (hLU : L ≠ U) (k : ℕ) (hk : k < n.eval)
    (h : State base p L U lo.eval uo.eval A k st.store) :
    ∃ mid, exec I (ins (.un p .sqrt ⟨U, uo + .var k + n * .var k⟩
      ⟨U, uo + .var k + n * .var k⟩)).run st = some mid ∧
      (∃ g, Store.BlockFrame base p U L lo.eval (n.eval * n.eval) mid.store g) ∧
      (∀ i j : Fin n.eval, mid.store.read p L (lo.eval + i + n.eval * j) =
        some (if j.val < k then choleskyLower A i j else luLower A i j)) ∧
      mid.store.read p U (uo.eval + k + n.eval * k) =
        some (Real.sqrt (luUpper A ⟨k, hk⟩ ⟨k, hk⟩)) ∧
      ∀ j : Fin n.eval, k < j.val → mid.store.read p U (uo.eval + j + n.eval * j) =
        some (luUpper A j j) := by
  have hp : 0 < luUpper A ⟨k, hk⟩ ⟨k, hk⟩ := by
    rw [luUpper_apply_self]
    exact hA.gaussState_apply_self_pos ⟨k, hk⟩
  have hr : st.store.read p U (uo.eval + k + n.eval * k) =
      some (luUpper A ⟨k, hk⟩ ⟨k, hk⟩) := h.2.2 ⟨k, hk⟩ (Nat.le_refl k)
  obtain ⟨s, hw, he, hsh, hd, hfr⟩ := exec_scalar_un I p st .sqrt
    ⟨U, uo + IExp.var k + n * IExp.var k⟩
    ⟨U, uo + IExp.var k + n * IExp.var k⟩
    (luUpper A ⟨k, hk⟩ ⟨k, hk⟩) (Real.sqrt (luUpper A ⟨k, hk⟩ ⟨k, hk⟩)) hr
    (by rw [hI]; simp only [exactSem, hp.le, if_pos, RCLike.re_to_real,
      RCLike.ofReal_real_eq_id, id_eq])
    (Store.exists_getElem?_shape_of_read_eq_some hr)
  obtain ⟨g, hf⟩ := h.1
  refine ⟨_, he, ⟨g, hf.write_scratch (fun _ => hLU) hw⟩, ?_, hd, ?_⟩
  · intro i j
    exact (hfr p L _ (Or.inr (Or.inl hLU))).trans (h.2.1 i j)
  · intro j hj
    have haddr : uo.eval + j.val + n.eval * j.val ≠ uo.eval + k + n.eval * k := by
      have hm := Nat.mul_le_mul_left n.eval (Nat.le_of_lt hj)
      omega
    exact (hfr p U _ (Or.inr (Or.inr haddr))).trans (h.2.2 j (Nat.le_of_lt hj))

private theorem exec_suffix (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (base : Store P ℝ) (n : IExp ℕ)
    (L U : ℕ) (lo uo : IExp ℕ) (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hA : A.PosDef) (hLU : L ≠ U) (k : ℕ) (hk : k < n.eval)
    (hF : ∃ g, Store.BlockFrame base p U L lo.eval (n.eval * n.eval) st.store g)
    (hL : ∀ i j : Fin n.eval, st.store.read p L (lo.eval + i + n.eval * j) =
      some (if j.val < k then choleskyLower A i j else luLower A i j))
    (hroot : st.store.read p U (uo.eval + k + n.eval * k) =
      some (Real.sqrt (luUpper A ⟨k, hk⟩ ⟨k, hk⟩)))
    (hU : ∀ j : Fin n.eval, k < j.val → st.store.read p U (uo.eval + j + n.eval * j) =
      some (luUpper A j j)) :
    ∃ out, exec I (scal p ⟨U, uo + .var k + n * .var k⟩ L
      (lo + .var k + n * .var k) (n - .var k)).run st = some out ∧
      State base p L U lo.eval uo.eval A (k + 1) out.store := by
  let xs : ℕ → ℝ := fun i => if h : k + i < n.eval then
    luLower A ⟨k + i, h⟩ ⟨k, hk⟩ else 0
  have hx : ∀ i < (n - .var k).eval, st.store.read p L
      ((lo + .var k + n * .var k).eval + i) = some (xs i) := by
    intro i hi
    have hki : k + i < n.eval := by change i < n.eval - k at hi; omega
    simpa only [IExp.eval, xs, dif_pos hki, Fin.val_mk, lt_self_iff_false, if_false,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hL ⟨k + i, hki⟩ ⟨k, hk⟩
  let W := Array.ofFn fun i : Fin (n.eval - k) =>
    choleskyLower A (Fin.natAdd_castLEEmb (Nat.sub_le n.eval k) i) ⟨k, hk⟩
  obtain ⟨s, hw⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape
    (s := st.store) (p := p) (b := L) (off := lo.eval + k + n.eval * k) (xs := W) (by
      intro i hi
      exact Store.exists_getElem?_shape_of_read_eq_some (hx i (by simpa [W] using hi)))
  have hw' : st.store.writeBlock p L (lo + .var k + n * .var k).eval
      ((List.range (n - .var k).eval).toArray.map fun i =>
        Real.sqrt (luUpper A ⟨k, hk⟩ ⟨k, hk⟩) * xs i) = some s := by
    change st.store.writeBlock p L (lo.eval + k + n.eval * k)
      ((List.range (n.eval - k)).toArray.map fun i =>
        Real.sqrt (luUpper A ⟨k, hk⟩ ⟨k, hk⟩) * xs i) = some s
    rw [show (List.range (n.eval - k)).toArray.map (fun i =>
      Real.sqrt (luUpper A ⟨k, hk⟩ ⟨k, hk⟩) * xs i) = W from
        suffix_array A hA k hk (Nat.sub_le n.eval k)]
    exact hw
  obtain ⟨out, he, hs, _⟩ := exec_scal I hI hc p st
    ⟨U, uo + .var k + n * .var k⟩ L (lo + .var k + n * .var k) (n - .var k)
    _ xs hroot hx (fun he => (hLU he.symm).elim) s hw'
  obtain ⟨g, hf⟩ := hF
  refine ⟨out, he, ?_⟩
  rw [hs]
  refine ⟨⟨_, hf.writeBlock (off := k + n.eval * k) (by simpa [Nat.add_assoc] using hw) ?_⟩,
    reads_after_suffix hk (Nat.sub_le n.eval k) hL hw, fun j hj => ?_⟩
  · simp only [W, Array.size_ofFn]
    have hm := Nat.mul_le_mul_left n.eval (Nat.succ_le_of_lt hk)
    rw [Nat.mul_succ] at hm
    omega
  · exact (Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hLU.symm)).trans
      (hU j (by omega))

-- The actual column proof composes three continuations and transports their complete store frames.
set_option maxHeartbeats 800000 in
-- Nested continuation elaboration combines the square-root, zero-fill and suffix-scaling runs.
private theorem exec_column (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (base : Store P ℝ) (n : IExp ℕ)
    (L U : ℕ) (lo uo : IExp ℕ) (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hA : A.PosDef) (hLU : L ≠ U) (k : ℕ) (hk : k < n.eval)
    (h : State base p L U lo.eval uo.eval A k st.store) :
    ∃ out, exec I (choleskyScaleColumn p n (.var k) L U lo uo).run st = some out ∧
      State base p L U lo.eval uo.eval A (k + 1) out.store := by
  obtain ⟨mid, he, hf, hl, hr, hu⟩ := exec_root I hI p st base n L U lo uo A hA hLU k hk h
  have hz : ∀ i < (IExp.var k).eval,
      mid.store.read p L ((lo + n * .var k).eval + i) = some 0 := by
    intro i hi
    have hin : i < n.eval := by change i < k at hi; omega
    have hij : (⟨i, hin⟩ : Fin n.eval) < ⟨k, hk⟩ := hi
    simpa only [IExp.eval, Fin.val_mk, lt_self_iff_false, if_false, luLower,
      Matrix.of_apply, if_neg hij.not_gt, if_neg hij.ne, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hl ⟨i, hin⟩ ⟨k, hk⟩
  obtain ⟨cleared, hc', hstore⟩ := exec_forRange_zero_of_reads_eq_zero I p 0
    (by rw [hI]; simp only [exactSem, Rat.cast_zero]) mid (.var k) L (lo + n * .var k)
    (fun i hi => Store.exists_getElem?_shape_of_read_eq_some (hz i hi)) hz
  obtain ⟨out, hs, hout⟩ := exec_suffix I hI hc p cleared base n L U lo uo A hA hLU k hk
    (by simpa only [hstore] using hf) (by simpa only [hstore] using hl)
    (by simpa only [hstore] using hr) (by simpa only [hstore] using hu)
  refine ⟨out, ?_, hout⟩
  unfold choleskyScaleColumn
  rw [exec_run_bind I (b := ins (.un p .sqrt ⟨U, uo + .var k + n * .var k⟩
    ⟨U, uo + .var k + n * .var k⟩)) (fun _ => rfl), he, Option.bind_some]
  rw [exec_run_bind I (b := forRange (.var k) fun i =>
    ins (.lit p ⟨L, lo + n * .var k + .var i⟩ 0)) (fun _ => rfl), hc', Option.bind_some]
  exact hs

/-- The actual column-conversion loop succeeds from canonical stored factors and preserves
its complete lower-output/upper-scratch frame. Positive definiteness supplies every square root. -/
theorem exec_columns (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (base : Store P ℝ) (n : IExp ℕ)
    (L U : ℕ) (lo uo : IExp ℕ) (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hA : A.PosDef) (hLU : L ≠ U)
    (h : State base p L U lo.eval uo.eval A 0 st.store) :
    ∃ out, exec I (choleskyScaleColumns p n L U lo uo).run st = some out ∧
      (∃ g, Store.BlockFrame base p U L lo.eval (n.eval * n.eval) out.store g) ∧
      Holds out.store p L lo.eval (choleskyLower A) := by
  obtain ⟨out, he, hf, hl, _⟩ := exists_exec_loop_eq_some_of_forall I
    (fun k σ => State base p L U lo.eval uo.eval A k σ.store) h
    (fun k hk σ hσ => exec_column I hI hc p σ base n L U lo uo A hA hLU k hk hσ)
  refine ⟨out, ?_, hf, fun i j => ?_⟩
  · change exec I (.seq (.loop n _) .skip) st = some out
    rw [exec_seq_skip]
    exact he
  · simpa only [if_pos j.isLt] using hl i j

end CholeskyScaling
end NLAlib.Computation
