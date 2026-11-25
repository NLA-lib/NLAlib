/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PivotedCholeskyPrefix
public import NLAlib.Matrix.Computation.SemidefiniteCholeskyColumn

/-!
# Zero-safe symmetric pivoted Cholesky steps

One actual step selects a diagonal, exchanges both residual axes and the completed factor
rows, then materializes a zero-safe Cholesky column and eliminates its pivot.

## Main results

* `NLAlib.Computation.exec_pivotedCholeskyStep`: a stored PSD prefix advances successfully.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- One diagonal-pivoted Cholesky step, including the actual absolute history write and
symmetric residual exchange. Zero pivots skip square-root division and elimination. -/
def pivotedCholeskyStep {P ι VB VI : Type} (tag : P) (n k : IExp VI)
    (R L H : VB) (lo ho : IExp VI) : Builder P ι VB VI Unit := scope do
  PivotedCholesky.symmetricCholeskyPivot tag n k R L H lo ho
  choleskyColumnTotal tag n R L 0 lo k
  schurStepTotal tag n R 0 k

variable {P ι : Type} [DecidableEq P]

/-- One pivoted Cholesky step releases all its internal temporary storage. -/
theorem executionComposable_pivotedCholeskyStep {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (tag : P) (n k : IExp ℕ) (R L H : ℕ) (lo ho : IExp ℕ) :
    ExecutionComposable I (pivotedCholeskyStep tag n k R L H lo ho) :=
  executionComposable_single I (fun _ => rfl)

namespace PivotedCholesky

private theorem exec_column (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n k : IExp ℕ) (R L : ℕ) (lo : IExp ℕ)
    (A F : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hA : A.PosSemidef)
    (hk : k.eval < n.eval) (hR : Holds st.store tag R 0 (gaussState A k.eval))
    (hF : Holds st.store tag L lo.eval F) (hRL : R ≠ L)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval)) :
    ∃ out, exec I (choleskyColumnTotal tag n R L 0 lo k).run st = some out ∧
      st.store.writeBlock tag L lo.eval
        (flatten (F.updateCol ⟨k.eval, hk⟩ (fun i => choleskyLower A i ⟨k.eval, hk⟩))) =
          some out.store ∧
      Holds out.store tag L lo.eval
        (F.updateCol ⟨k.eval, hk⟩ (fun i => choleskyLower A i ⟨k.eval, hk⟩)) := by
  have hcap : Writable st.store tag L (lo.eval + n.eval * k.eval) n.eval := by
    intro i hi
    obtain ⟨len, hs, ht⟩ := hL (i + n.eval * k.eval)
      (Nat.add_mul_lt_mul_of_lt_of_lt hi hk)
    exact ⟨len, hs, by omega⟩
  obtain ⟨out, hr, hw⟩ := exec_choleskyColumnTotal_of_posSemidef I hI hc tag st n R L
    0 lo k A hA hk hR hRL hcap
  have hF' : Holds out.store tag L lo.eval
      (F.updateCol ⟨k.eval, hk⟩ (fun i => choleskyLower A i ⟨k.eval, hk⟩)) := by
    intro i j
    by_cases he : j = ⟨k.eval, hk⟩
    · subst j
      rw [Matrix.updateCol_self]
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Array.getElem?_ofFn,
        i.isLt, ↓reduceDIte] using
        Store.read_of_writeBlock_eq_some_of_lt hw (j := i.val)
          (by simp only [Array.size_ofFn]; exact i.isLt)
    · rw [Matrix.updateCol_ne he]
      have hj : j.val ≠ k.eval := fun h => he (Fin.ext h)
      rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inr (by
        simp only [Array.size_ofFn]
        have := i.isLt
        rcases lt_or_gt_of_ne hj with hj | hj <;> [left; right] <;> nlinarith))]
      exact hF i j
  refine ⟨out, hr, Store.writeBlock_eq_some_of_read (Store.shape_of_writeBlock_eq_some hw)
    (fun t ht => hF'.read_flatten t (by simpa only [size_flatten] using ht)) ?_, hF'⟩
  intro q b t ht
  apply Store.read_of_writeBlock_eq_some_of_ne hw
  simp only [size_flatten] at ht
  simp only [Array.size_ofFn]
  have hend : lo.eval + n.eval * k.eval + n.eval ≤ lo.eval + n.eval * n.eval := by
    nlinarith
  omega

private theorem exec_totalPhase (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n k : IExp ℕ) (R L H : ℕ) (lo ho : IExp ℕ)
    (A F : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hA : A.PosSemidef)
    (hk : k.eval < n.eval) (hR : Holds st.store tag R 0 (gaussState A k.eval))
    (hF : Holds st.store tag L lo.eval F) (hRL : R ≠ L)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval)) (base : Store P ℝ)
    (hf : PLU.Frame base n.eval R L L H lo.eval lo.eval ho.eval st.store) :
    ∃ out, exec I (do
      choleskyColumnTotal tag n R L 0 lo k
      schurStepTotal tag n R 0 k).run st = some out ∧
      PLU.Frame base n.eval R L L H lo.eval lo.eval ho.eval out.store ∧
      Holds out.store tag R 0 (gaussState A (k.eval + 1)) ∧
      Holds out.store tag L lo.eval
        (F.updateCol ⟨k.eval, hk⟩ (fun i => choleskyLower A i ⟨k.eval, hk⟩)) ∧
      ∀ q b i, b ≠ R → b ≠ L → out.store.read q b i = st.store.read q b i := by
  obtain ⟨column, he₁, hw₁, hF'⟩ := exec_column I hI hc tag st n k R L lo A F hA hk
    hR hF hRL hL
  have hR' : Holds column.store tag R 0 (gaussState A k.eval) := fun i j =>
    (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hRL)).trans (hR i j)
  obtain ⟨out, he₂, hw₂, hR''⟩ := exec_schurStepTotal I hI hc tag column n R 0 k
    (gaussState A k.eval) hk hR'
  refine ⟨out, ?_, (hf.write_lower hw₁ (size_flatten _)).write_residual hw₂ (size_flatten _),
    ?_, ?_, ?_⟩
  · rw [exec_run_bind I (b := choleskyColumnTotal tag n R L 0 lo k) (fun _ => rfl),
      he₁, Option.bind_some]
    exact he₂
  · rw [gaussState_succ A hk]
    exact hR''
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hRL.symm)]
    exact hF' i j
  · intro q b i hbR hbL
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hbR),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hbL)]

end PivotedCholesky

/-- A readable stored PSD prefix advances through actual diagonal selection, symmetric
swaps and total Cholesky/Schur kernels. The stored log, rather than an unrelated existential
permutation, determines both input axes. -/
theorem exec_pivotedCholeskyStep (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (base : Store P ℝ) (n : IExp ℕ) (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hA : A.PosSemidef) (R L H : ℕ) (lo ho : IExp ℕ)
    (hL : Writable base tag L lo.eval (n.eval * n.eval))
    (hH : Writable base tag H ho.eval n.eval) (hRL : R ≠ L) (hRH : R ≠ H) (hLH : L ≠ H)
    (k : ℕ) (hk : k < n.eval) (st : St P ℝ (OpCount P ι))
    (hs : PivotedCholesky.State base tag A R L H lo.eval ho.eval k st.store) :
    ∃ out, exec I (pivotedCholeskyStep tag n (.var k) R L H lo ho).run st = some out ∧
      PivotedCholesky.State base tag A R L H lo.eval ho.eval (k + 1) out.store := by
  obtain ⟨p, F, hR, hF, hprefix, hlog⟩ := hs.values
  let pivot : Fin n.eval := ⟨k, hk⟩
  let B := A.submatrix (luPivotPermutation p k) (luPivotPermutation p k)
  have hcap : Writable st.store tag H (ho + .var k).eval 1 := by
    intro i hi
    obtain ⟨len, hh, ht⟩ := (hH.of_shape_eq hs.frame.shape) k hk
    exact ⟨len, hh, by change ho.eval + k + i < len; omega⟩
  obtain ⟨swapped, r, he₁, hkr, hf₁, hR₁, hF₁, hr, hmax, hpast⟩ :=
    PivotedCholesky.exec_pivotPhase I hI tag st n (.var k) R L H lo ho
      (gaussState B k) F hk hR hF hcap hRL hRH hLH base hs.frame
  let q := Function.update p pivot r
  let B' := A.submatrix (luPivotPermutation q (k + 1)) (luPivotPermutation q (k + 1))
  let ρ := Equiv.swap pivot r
  have hfix : ∀ i : Fin n.eval, i.val < k → ρ i = i :=
    fun i hi => Fin.swap_apply_of_lt_of_le pivot r (Fin.le_def.mpr hkr) i (Fin.lt_def.mpr hi)
  have hsub : B' = B.submatrix ρ ρ := by
    dsimp only [B', B, q, pivot, ρ]
    rw [luPivotPermutation_update]
    rfl
  have hRB : Holds swapped.store tag R 0 (gaussState B' k) := by
    rw [hsub, gaussState_submatrix B ρ k hfix]
    exact hR₁
  obtain ⟨out, he₂, hf₂, hR₂, hF₂, hhist⟩ := PivotedCholesky.exec_totalPhase I hI hc tag
    swapped n (.var k) R L H lo ho B' (F.submatrix ρ id) (hA.submatrix _) hk hRB hF₁ hRL
      (hL.of_shape_eq hf₁.shape) base hf₁
  have hprefix' := forall_lt_choleskyLower_eq_of_update A F p pivot r
    (Fin.le_def.mpr hkr) hprefix
  refine ⟨out, ?_, hf₂, q, _, hR₂, hF₂, hprefix', ?_⟩
  · change exec I (.seq _ .skip) st = some out
    rw [exec_seq_skip]
    rw [exec_run_bind I (b := PivotedCholesky.symmetricCholeskyPivot tag n (.var k)
      R L H lo ho) (fun _ => rfl), he₁, Option.bind_some]
    exact he₂
  · intro j hj
    by_cases hjk : j = pivot
    · subst j
      simp only [q, Function.update_self]
      exact ⟨(hhist tag H _ hRH.symm hLH.symm).trans hr, Fin.le_def.mpr hkr⟩
    · have hj' : j.val < k := by
        have hne : j.val ≠ k := fun he => hjk (Fin.ext he)
        omega
      rw [show q j = p j from Function.update_of_ne hjk _ _]
      refine ⟨?_, (hlog j hj').2⟩
      rw [hhist tag H _ hRH.symm hLH.symm, hpast tag H _ hRH.symm hLH.symm
        (Or.inr (by change ho.eval + j.val ≠ ho.eval + k; omega))]
      exact (hlog j hj').1


end NLAlib.Computation
