/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyRangeState
public import NLAlib.Matrix.Computation.CholeskyRangeConditions
public import NLAlib.Matrix.Computation.SchurUnderflow

/-!
# Successful finite-range Cholesky iterations

Every exact scalar result is bounded from input numerical conditions before its backend
success law is used. The full-residual comparison includes retired rows and columns.

## Main results

* `NLAlib.Computation.CholeskyRange.exec_iteration`: actual successful finite-range execution
  advances the complete storage, structural and mixed-error invariants.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Computation.CholeskyRange

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

private theorem factor_of_column_write {dec : P → K → ℝ} {base s s' : Store P K}
    {u τ μ B e : ℝ} {p : P} {R L lo N k : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hs : State dec u τ μ B e base p R L lo A k s) (hk : k < N) (W : Fin N → K)
    (hw : s.writeBlock p L (lo + N * k) (Array.ofFn W) = some s')
    (hz : ∀ i, i.val < k → dec p (W i) = 0) (hpos : 0 < dec p (W ⟨k, hk⟩))
    (he : ∀ i, |dec p (W i) - choleskyLower A i ⟨k, hk⟩| ≤ e) :
    ∀ i j : Fin N, j.val < k + 1 → ∃ w,
      s'.read p L (lo + i.val + N * j.val) = some w ∧
      (i < j → dec p w = 0) ∧ (i = j → 0 < dec p w) ∧
      |dec p w - choleskyLower A i j| ≤ e := by
  intro i j hj
  by_cases hjk : j.val = k
  · have hjr : j = ⟨k, hk⟩ := Fin.ext hjk
    subst j
    refine ⟨W i, ?_, hz i, ?_, he i⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Store.read_of_writeBlock_eq_some_of_lt hw (j := i.val) (by simp)
    · intro hi
      subst i
      exact hpos
  · have hjk' : j.val < k := by omega
    obtain ⟨w, hr, hz', hp', he'⟩ := hs.factor i j hjk'
    refine ⟨w, ?_, hz', hp', he'⟩
    rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inr (Or.inl ?_)), hr]
    simpa only [Nat.add_assoc] using
      Nat.add_lt_add_left (Nat.add_mul_lt_mul_of_lt_of_lt i.isLt hjk') lo

private theorem residual_bounds {N : ℕ} {A M : Matrix (Fin N) (Fin N) ℝ}
    {u τ μ B Ω : ℝ} (hc : CholeskyRangeConditions N u τ B μ Ω)
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    {k : ℕ} (hk : k < N)
    (herr : ∀ i j, |M i j - gaussState A k i j| ≤ choleskyMixedSchurErrorBound u τ B μ k) :
    μ ≤ gaussState A k ⟨k, hk⟩ ⟨k, hk⟩ ∧ (∀ i j, |gaussState A k i j| ≤ B) ∧
      μ / 2 ≤ M ⟨k, hk⟩ ⟨k, hk⟩ ∧ (∀ i j, |M i j| ≤ 2 * B) ∧
      choleskyMixedSchurErrorBound u τ B μ k ≤ μ / 2 := by
  have hA : A.PosDef := by
    have h := (Matrix.PosDef.one.smul hc.margin_pos).add_posSemidef (Matrix.le_iff.mp hlo)
    simpa only [add_sub_cancel] using h
  have hB : 0 ≤ B := hc.margin_pos.le.trans hc.margin_le_scale
  have hle := choleskyMixedSchurErrorBound_le_choleskyMixedSchurErrorBound
    hc.roundoff_nonneg hc.underflow_nonneg hB hc.margin_pos (Nat.le_of_lt hk)
  have herror : choleskyMixedSchurErrorBound u τ B μ k ≤ μ / 2 := hle.trans hc.residual_error_lt.le
  have hp := le_gaussState_apply_self_of_smul_one_le hc.margin_pos hlo ⟨k, hk⟩
  have hE : ∀ i j, |gaussState A k i j| ≤ B := by
    intro i j
    simpa only [Real.norm_eq_abs] using hA.posSemidef.norm_gaussState_apply_le hscale k i j
  refine ⟨hp, hE, ?_, ?_, herror⟩
  · have he := (abs_le.mp (herr ⟨k, hk⟩ ⟨k, hk⟩)).1
    linarith
  · intro i j
    calc |M i j| ≤ |M i j - gaussState A k i j| + |gaussState A k i j| := by
           simpa only [sub_add_cancel] using
             abs_add_le (M i j - gaussState A k i j) (gaussState A k i j)
         _ ≤ choleskyMixedSchurErrorBound u τ B μ k + B := add_le_add (herr i j) (hE i j)
         _ ≤ 2 * B := by have hh := hc.margin_le_scale; linarith

/-- Explicit input numerical range conditions imply success of the actual existing Cholesky
iteration with mixed errors. The source spectral band controls the exact reference, and every
computed divisor and exact arithmetic result is justified before executing its instruction. -/
theorem exec_iteration {dec : P → K → ℝ} {u τ : P → ℝ} {safe : P → ℝ → Prop}
    (I : Interp P ι K C)
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (τ p)) dec safe I.sem) (p : P)
    (n : IExp ℕ) {μ B Ω : ℝ} (hc : CholeskyRangeConditions n.eval (u p) (τ p) B μ Ω)
    (hrange : ∀ a, |a| ≤ Ω → safe p a)
    (hminus : ∃ ell, I.sem.lit p (-1) = some ell ∧ AbsRelErr (u p) (τ p) (-1) (dec p ell))
    (hsqrt : ∀ v, 0 ≤ dec p v → |Real.sqrt (dec p v)| ≤ Ω →
      ∃ d, I.sem.un p .sqrt v = some d ∧ AbsRelErr (u p) (τ p) (Real.sqrt (dec p v)) (dec p d))
    (base : Store P K) (R L : ℕ) (lo : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hlo : μ • (1 : Matrix (Fin n.eval) (Fin n.eval) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (hRL : R ≠ L) (hL : Writable base p L lo.eval (n.eval * n.eval))
    (k : ℕ) (hk : k < n.eval) (st : St P K C)
    (hs : State dec (u p) (τ p) μ B
      (choleskyMixedColumnErrorBound (u p) (τ p) B μ
        (choleskyMixedSchurErrorBound (u p) (τ p) B μ n.eval)) base p R L lo.eval A k st.store) :
    ∃ out, exec I (do
      choleskyColumnOfResidual p n R L 0 lo (.var k)
      forRange (IExp.var k) fun i => ins (.lit p ⟨L, lo + n * IExp.var k + IExp.var i⟩ 0)
      schurStep p n R 0 (.var k)).run st = some out ∧
      State dec (u p) (τ p) μ B
        (choleskyMixedColumnErrorBound (u p) (τ p) B μ
          (choleskyMixedSchurErrorBound (u p) (τ p) B μ n.eval))
        base p R L lo.eval A (k + 1) out.store := by
  obtain ⟨g, hF⟩ := hs.frame
  obtain ⟨M, hM, herr⟩ := hs.residual
  obtain ⟨hpE, hE, hpM, hMs, herror⟩ := residual_bounds hc hlo hscale hk herr
  have hB : 0 ≤ B := hc.margin_pos.le.trans hc.margin_le_scale
  have hm : 0 < μ / 2 := by have hh := hc.margin_pos; positivity
  have hcap : Writable st.store p L (lo.eval + n.eval * k) n.eval := by
    intro i hi
    obtain ⟨len, hlen, hlt⟩ := hL (i + n.eval * k)
      (Nat.add_mul_lt_mul_of_lt_of_lt hi hk)
    exact ⟨len, hF.1 ▸ hlen, by omega⟩
  obtain ⟨s₁, W, hr₁, hw₁, hz, hrootlower, hdrel, hdiv⟩ :=
    h.exec_choleskyColumnOfResidual_zero_upper I p st n R L 0 lo (.var k) M hk hM hRL
      hc.roundoff_lt_one hm hpM hMs hrange hsqrt hc.root_le hc.root_margin_pos hc.quotient_le hcap
  have hwe := abs_column_sub_choleskyLower_le hc.margin_pos hc.margin_le_scale hlo hscale
    hc.roundoff_nonneg hc.underflow_nonneg hc.root_margin_pos hk hc.residual_error_lt herr
    (fun i => dec p (W i)) hz hrootlower hdrel hdiv
  have hprefix := factor_of_column_write hs hk W hw₁ hz (hc.root_margin_pos.trans_le hrootlower) hwe
  have hM₁ := hM.of_writeBlock hw₁ (by intro _ _; simp [blockDisjoint_iff, hRL])
  obtain ⟨out, Wr, hr₂, hWrs, hw₂, hlocal⟩ := h.exec_schurStep_abs_sub_le I p s₁ n R 0 (.var k)
    M hk hM₁ hc.roundoff_nonneg hc.underflow_nonneg (by positivity) hm hpM hMs hrange hminus
    hc.coefficient_le hc.row_product_le hc.cell_product_le hc.sum_le
  have hF₁ := hF.writeBlock hw₁ (by
    simp only [Array.size_ofFn, IExp.eval_var]
    have hm' := Nat.mul_le_mul_left n.eval (Nat.succ_le_of_lt hk)
    nlinarith)
  refine ⟨out, ?_, ⟨_, hF₁.writeBlock_scratch (fun _ => hRL.symm) hw₂⟩, ?_, ?_⟩
  · have hcomp : ExecutionComposable I (do
      choleskyColumnOfResidual p n R L 0 lo (.var k)
      forRange (IExp.var k) fun i => ins (.lit p ⟨L, lo + n * IExp.var k + IExp.var i⟩ 0)) :=
        (executionComposable_single I (fun _ => rfl)).bind
          (executionComposable_single I (fun _ => rfl))
    exact (hcomp (fun _ => schurStep p n R 0 (.var k)) st).trans (by
      rw [hr₁, Option.bind_some]
      exact hr₂)
  · refine ⟨unflatten n.eval n.eval (Wr.map (dec p)), ?_, ?_⟩
    · intro i j
      have ht : i.val + n.eval * j.val < Wr.size := by
        rw [hWrs]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt
      exact ⟨Wr[i.val + n.eval * j.val], by
        simpa only [IExp.eval_zero, Nat.zero_add, Array.getElem?_eq_getElem ht] using
          Store.read_of_writeBlock_eq_some_of_lt hw₂ ht,
        by simp [unflatten, Array.getElem?_eq_getElem ht]⟩
    · intro i j
      rw [gaussState_succ A hk]
      exact abs_sub_eliminationStep_le_choleskyMixedSchurErrorBound hc.margin_pos hc.margin_le_scale
        herror hpE hE herr hlocal i j
  · intro i j hj
    obtain ⟨w, hr, hzero, hdiag, he⟩ := hprefix i j hj
    exact ⟨w, (Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hRL.symm)).trans hr,
      hzero, hdiag, he⟩

end NLAlib.Computation.CholeskyRange
