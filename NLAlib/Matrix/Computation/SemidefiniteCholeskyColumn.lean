/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyColumns
public import NLAlib.Matrix.Computation.GuardedElimination

/-!
# Zero-safe Cholesky columns

A stored zero pivot produces a full zero factor column without division. Positive pivots
use the existing square-root and normalization routine. This supplies columns for exact
positive semidefinite factorization, including rank-deficient inputs.

## Main results

* `NLAlib.Computation.exec_choleskyColumnTotal`: exact success with a nonnegative pivot.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Form one Cholesky column with a stored zero-pivot test. Zero pivots write a full zero
column without taking a square root or dividing. Nonzero pivots use the existing normalized
residual column. [GolubVanLoan2013, §4.2]. -/
def choleskyColumnTotal {P ι VB VI : Type} (p : P) (n : IExp VI) (R L : VB)
    (ro lo k : IExp VI) : Builder P ι VB VI Unit := scope do
  let z ← alloc p 1
  ins (.lit p ⟨z, 0⟩ 0)
  ifThenElse p .eq ⟨R, ro + k + n * k⟩ ⟨z, 0⟩
    (forRange n fun i => ins (.lit p ⟨L, lo + n * k + IExp.var i⟩ 0))
    (choleskyColumnOfResidual p n R L ro lo k)

variable {P ι : Type} [DecidableEq P]

private theorem exec_zero_column (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (p : P) (st : St P ℝ (OpCount P ι))
    (n : IExp ℕ) (L : ℕ) (off : IExp ℕ)
    (hw : Writable st.store p L off.eval n.eval) :
    ∃ out, exec I (forRange n fun i => ins (.lit p ⟨L, off + IExp.var i⟩ 0)).run st =
      some out ∧ st.store.writeBlock p L off.eval
        (Array.ofFn fun _ : Fin n.eval => (0 : ℝ)) = some out.store := by
  obtain ⟨s, hr, hs, hread, hframe⟩ := exec_forRange_literal_zero I p 0
    (by rw [hI]; simp only [exactSem, Rat.cast_zero]) st n L off hw
  refine ⟨_, hr, Store.writeBlock_eq_some_of_read hs ?_ ?_⟩
  · intro i hi
    have hi' : i < n.eval := by simpa only [Array.size_ofFn] using hi
    simpa only [Array.getElem?_ofFn, hi', dite_true] using hread i hi'
  · intro q b i hi
    exact hframe q b i (Or.inr (by simpa only [Array.size_ofFn] using hi))

private theorem exec_column_branch (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : ∀ kind, I.charge kind = Finsupp.single kind 1)
    (p : P) (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (R L : ℕ) (ro lo k : IExp ℕ)
    (B : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hB : Holds st.store p R ro.eval B) (hRL : R ≠ L)
    (hp : 0 ≤ B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)
    (hz : ∀ i : Fin n.eval, (i : ℕ) < k.eval → B i ⟨k.eval, hk⟩ = 0)
    (hL : Writable st.store p L (lo.eval + n.eval * k.eval) n.eval)
    (z : ℕ) (hzero : st.store.read p z 0 = some 0) :
    ∃ out, exec I (.ite p .eq ⟨R, ro + k + n * k⟩ ⟨z, 0⟩
      (forRange n fun i => ins (.lit p ⟨L, lo + n * k + IExp.var i⟩ 0)).run
      (choleskyColumnOfResidual p n R L ro lo k).run) st = some out ∧
      st.store.writeBlock p L (lo.eval + n.eval * k.eval)
        (Array.ofFn fun i : Fin n.eval => if (i : ℕ) < k.eval then 0
          else B i ⟨k.eval, hk⟩ / Real.sqrt (B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)) =
            some out.store := by
  let r : Fin n.eval := ⟨k.eval, hk⟩
  let tested : St P ℝ (OpCount P ι) := { st with cnt := st.cnt + I.charge (.cmp p) }
  have hpiv : st.store.read p R (ro.eval + k.eval + n.eval * k.eval) = some (B r r) :=
    hB r r
  have hcmp : cmpStep I p .eq ⟨R, ro + k + n * k⟩ ⟨z, 0⟩ st =
      some (decide (B r r = 0), tested) := by
    simp only [cmpStep, IExp.eval_add, IExp.eval_mul, IExp.eval_zero, hpiv,
      hzero, Option.bind_some, hI, exactSem, Option.map_some]
    rfl
  by_cases h : B r r = 0
  · obtain ⟨out, hr, hw⟩ := exec_zero_column I hI p tested n L (lo + n * k) hL
    refine ⟨out, ?_, ?_⟩
    · rw [exec_ite, hcmp]
      simpa only [h, decide_true, Option.bind_some, ↓reduceIte] using hr
    · simpa only [r, h, Real.sqrt_zero, div_zero, ite_self, tested, IExp.eval_add,
        IExp.eval_mul] using hw
  · obtain ⟨out, hr, hw⟩ := exec_choleskyColumnOfResidual I hI hc p tested n R L ro lo k
      B hk hB hRL (lt_of_le_of_ne hp (Ne.symm h)) hL
    refine ⟨out, ?_, ?_⟩
    · rw [exec_ite, hcmp]
      simpa only [h, decide_false, Option.bind_some, Bool.false_eq_true, ↓reduceIte] using hr
    · convert hw using 3
      funext i
      split_ifs with hi
      · exact (hz i hi).symm
      · rfl

/-- A nonnegative pivot and a zero prefix above it suffice for successful exact column
formation, including a zero pivot with arbitrary entries below it. The only net write is the
full factor column. [GolubVanLoan2013, §4.2]. -/
theorem exec_choleskyColumnTotal (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : ∀ kind, I.charge kind = Finsupp.single kind 1)
    (p : P) (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (R L : ℕ) (ro lo k : IExp ℕ)
    (B : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hB : Holds st.store p R ro.eval B) (hRL : R ≠ L)
    (hp : 0 ≤ B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)
    (hz : ∀ i : Fin n.eval, (i : ℕ) < k.eval → B i ⟨k.eval, hk⟩ = 0)
    (hL : Writable st.store p L (lo.eval + n.eval * k.eval) n.eval) :
    ∃ out, exec I (choleskyColumnTotal p n R L ro lo k).run st = some out ∧
      st.store.writeBlock p L (lo.eval + n.eval * k.eval)
        (Array.ofFn fun i : Fin n.eval => if (i : ℕ) < k.eval then 0
          else B i ⟨k.eval, hk⟩ / Real.sqrt (B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)) =
            some out.store := by
  have hLb : L < st.store.size := by
    obtain ⟨len, hh, _⟩ := hL 0 (by omega)
    have := (Array.getElem?_eq_some_iff.mp hh).1
    simpa only [Store.size_shape] using this
  have hRb := Store.lt_size_of_read_eq_some (hB ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)
  have hbody : ∀ σ : St P ℝ (OpCount P ι),
      σ.store = st.store.push (p, Array.replicate 1 none) →
      ∃ out, exec I ((do
        ins (.lit p ⟨st.store.size, 0⟩ 0)
        ifThenElse p .eq ⟨R, ro + k + n * k⟩ ⟨st.store.size, 0⟩
          (forRange n fun i => ins (.lit p ⟨L, lo + n * k + IExp.var i⟩ 0))
          (choleskyColumnOfResidual p n R L ro lo k)) : Builder P ι ℕ ℕ Unit).run σ = some out ∧
        st.store.writeBlock p L (lo.eval + n.eval * k.eval)
          (Array.ofFn fun i : Fin n.eval => if (i : ℕ) < k.eval then 0
            else B i ⟨k.eval, hk⟩ / Real.sqrt (B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)) =
              some out.store.pop := by
    intro σ hσ
    obtain ⟨s, hw⟩ := Store.exists_write_eq_some_of_getElem?_shape (0 : ℝ)
      (hσ ▸ Store.getElem?_shape_push_size st.store p 1) (by omega : 0 < 1)
    let ready : St P ℝ (OpCount P ι) :=
      { σ with store := s, cnt := σ.cnt + I.charge (.lit p) }
    have hB' : Holds s p R ro.eval B := fun i j => by
      rw [Store.read_of_write_eq_some_of_ne hw (Or.inl (Nat.ne_of_lt hRb)), hσ,
        Store.read_push_of_lt hRb]
      exact hB i j
    have hL' : Writable s p L (lo.eval + n.eval * k.eval) n.eval := by
      rw [Writable, Store.shape_of_write_eq_some hw]
      intro i hi
      obtain ⟨len, hh, ht⟩ := hL i hi
      exact ⟨len, by rw [hσ, Store.getElem?_shape_push_of_lt _ hLb]; exact hh, ht⟩
    obtain ⟨out, hr, hf⟩ := exec_column_branch I hI hc p ready n R L ro lo k B hk
      hB' hRL hp hz hL' st.store.size (Store.read_of_write_eq_some hw)
    refine ⟨out, ?_, ?_⟩
    · change exec I (.seq (.instr (.lit p ⟨st.store.size, 0⟩ 0)) (.seq _ .skip)) σ = _
      rw [exec_seq_instr_lit I (by rw [hI]; simp only [exactSem, Rat.cast_zero]) hw,
        exec_seq_skip]
      exact hr
    · have hpop : ready.store.pop = st.store := by
        rw [show ready.store = s from rfl,
          Store.pop_of_write_top hw (by simp only [hσ, Array.size_push]; omega), hσ]
        exact Array.pop_push
      have hpopwrite := Store.writeBlock_pop_of_lt hf (fun _ => by
        have hs := Store.size_of_write_eq_some hw
        simp only [hσ, Array.size_push] at hs
        change L + 1 < s.size
        omega)
      simpa only [hpop] using hpopwrite
  obtain ⟨out, hr, hw⟩ := exists_exec_alloc I p 1 (fun z => ((do
    ins (.lit p ⟨z, 0⟩ 0)
    ifThenElse p .eq ⟨R, ro + k + n * k⟩ ⟨z, 0⟩
      (forRange n fun i => ins (.lit p ⟨L, lo + n * k + IExp.var i⟩ 0))
      (choleskyColumnOfResidual p n R L ro lo k)) : Builder P ι ℕ ℕ Unit).run) st
    (fun s => st.store.writeBlock p L (lo.eval + n.eval * k.eval)
      (Array.ofFn fun i : Fin n.eval => if (i : ℕ) < k.eval then 0
        else B i ⟨k.eval, hk⟩ / Real.sqrt (B ⟨k.eval, hk⟩ ⟨k.eval, hk⟩)) = some s) hbody
  refine ⟨out, ?_, hw⟩
  change exec I (.seq (.alloc p 1 _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

/-- The zero-safe column operation writes the computed factor column of a positive
semidefinite input, even when the diagonal pivot vanishes. [GolubVanLoan2013, §4.2]. -/
theorem exec_choleskyColumnTotal_of_posSemidef (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : ∀ kind, I.charge kind = Finsupp.single kind 1)
    (p : P) (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (R L : ℕ) (ro lo k : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hA : A.PosSemidef) (hk : k.eval < n.eval)
    (hR : Holds st.store p R ro.eval (gaussState A k.eval)) (hRL : R ≠ L)
    (hL : Writable st.store p L (lo.eval + n.eval * k.eval) n.eval) :
    ∃ out, exec I (choleskyColumnTotal p n R L ro lo k).run st = some out ∧
      st.store.writeBlock p L (lo.eval + n.eval * k.eval)
        (Array.ofFn fun i => choleskyLower A i ⟨k.eval, hk⟩) = some out.store := by
  obtain ⟨out, hr, hw⟩ := exec_choleskyColumnTotal I hI hc p st n R L ro lo k
    (gaussState A k.eval) hk hR hRL (hA.gaussState _).diag_nonneg
    (fun i hi => hA.gaussState_apply_eq_zero_of_lt_left hi _) hL
  refine ⟨out, hr, ?_⟩
  convert hw using 3
  funext i
  simp only [choleskyLower, Matrix.of_apply, RCLike.re_to_real,
    RCLike.ofReal_real_eq_id, id_eq]
  by_cases hi : (i : ℕ) < k.eval
  · rw [if_neg (show ¬(⟨k.eval, hk⟩ : Fin n.eval) ≤ i by exact not_le.mpr hi),
      if_pos hi]
  · rw [if_pos (show (⟨k.eval, hk⟩ : Fin n.eval) ≤ i by exact Nat.le_of_not_gt hi),
      if_neg hi]

end NLAlib.Computation
