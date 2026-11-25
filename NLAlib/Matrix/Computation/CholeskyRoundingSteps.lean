/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyRoundingState
public import NLAlib.Matrix.Computation.SchurRounding

/-!
# Successful rounded Cholesky iterations

A quantitative input spectral margin and the explicit active-entry error recurrence guarantee
that the actual square root, divisions and saved-pivot Schur update all succeed.

## Main results

* `NLAlib.Computation.CholeskyRounding.exec_iteration`: the existing full driver's iteration
  succeeds and advances its numerical and complete storage invariant.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Computation.CholeskyRounding

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

private theorem factor_of_column_write {dec : P → K → ℝ} {base s s' : Store P K}
    {u μ B e : ℝ} {p : P} {R L lo N k : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hs : State dec u μ B e base p R L lo A k s) (hk : k < N) (W : Fin N → K)
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

private theorem pivot_pos {N : ℕ} {A M : Matrix (Fin N) (Fin N) ℝ}
    {u μ B : ℝ} (hμ : 0 < μ) (hμB : μ ≤ B) (hu : 0 ≤ u)
    (hlo : μ • (1 : Matrix (Fin N) (Fin N) ℝ) ≤ A) {k : ℕ} (hk : k < N)
    (hη : choleskySchurErrorBound u B μ N < μ / 2)
    (herr : ∀ i j, k ≤ i.val → k ≤ j.val →
      |M i j - gaussState A k i j| ≤ choleskySchurErrorBound u B μ k) :
    0 < M ⟨k, hk⟩ ⟨k, hk⟩ := by
  have hp := le_gaussState_apply_self_of_smul_one_le hμ hlo ⟨k, hk⟩
  have hle := choleskySchurErrorBound_le_choleskySchurErrorBound
    hu (hμ.le.trans hμB) hμ (Nat.le_of_lt hk)
  have he := (abs_le.mp (herr ⟨k, hk⟩ ⟨k, hk⟩ le_rfl le_rfl)).1
  linarith

/-- Under a positive lower spectral input margin, an input norm bound and terminal recurrence
less than half that margin, the existing Cholesky iteration succeeds under standard rounding.
It preserves the complete output/scratch frame and advances both numerical invariants. -/
theorem exec_iteration {dec : P → K → ℝ} {u : P → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    {μ B : ℝ} (hμ : 0 < μ) (hμB : μ ≤ B) (hu1 : u p ≤ 1 / 10)
    (base : Store P K) (n : IExp ℕ) (R L : ℕ) (lo : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hlo : μ • (1 : Matrix (Fin n.eval) (Fin n.eval) ℝ) ≤ A) (hscale : specNorm A ≤ B)
    (hη : choleskySchurErrorBound (u p) B μ n.eval < μ / 2) (hRL : R ≠ L)
    (hL : Writable base p L lo.eval (n.eval * n.eval)) (k : ℕ) (hk : k < n.eval)
    (st : St P K C)
    (hs : State dec (u p) μ B
      ((2 * (1 + B / μ) * choleskySchurErrorBound (u p) B μ n.eval + 16 * u p * B) / Real.sqrt μ)
      base p R L lo.eval A k st.store) :
    ∃ out, exec I (do
      choleskyColumnOfResidual p n R L 0 lo (.var k)
      forRange (IExp.var k) fun i => ins (.lit p ⟨L, lo + n * IExp.var k + IExp.var i⟩ 0)
      schurStep p n R 0 (.var k)).run st = some out ∧
      State dec (u p) μ B
        ((2 * (1 + B / μ) * choleskySchurErrorBound (u p) B μ n.eval + 16 * u p * B) / Real.sqrt μ)
        base p R L lo.eval A (k + 1) out.store := by
  obtain ⟨g, hF⟩ := hs.frame
  obtain ⟨M, hM, herr⟩ := hs.residual
  have hu : 0 ≤ u p := h.nonneg trivial
  have hpos := pivot_pos hμ hμB hu hlo hk hη herr
  have hcap : Writable st.store p L (lo.eval + n.eval * k) n.eval := by
    intro i hi
    obtain ⟨len, hlen, hlt⟩ := hL (i + n.eval * k)
      (Nat.add_mul_lt_mul_of_lt_of_lt hi hk)
    exact ⟨len, hF.1 ▸ hlen, by omega⟩
  obtain ⟨s₁, W, hr₁, hw₁, hz, hdpos, hdrel, hdiv⟩ :=
    h.exec_choleskyColumnOfResidual_zero_upper I p st n R L 0 lo (.var k)
      M hk hM hRL hpos (by linarith) hcap
  have hwe := abs_column_sub_choleskyLower_le hμ hμB hlo hscale hu hu1 hk hη herr
    (fun i => dec p (W i)) hz hdrel hdiv
  have hprefix := factor_of_column_write hs hk W hw₁ hz hdpos hwe
  have hM₁ := hM.of_writeBlock hw₁ (by intro _ _; simp [blockDisjoint_iff, hRL])
  obtain ⟨out, Wr, hr₂, hWrs, hw₂, hlocal⟩ :=
    h.exec_schurStep_abs_sub_le I p s₁ n R 0 (.var k) M hk hM₁ hpos.ne' (by linarith)
  have hF₁ := hF.writeBlock hw₁ (by
    simp only [Array.size_ofFn, IExp.eval_var]
    have hm := Nat.mul_le_mul_left n.eval (Nat.succ_le_of_lt hk)
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
    · intro i j hi hj
      rw [gaussState_succ A hk]
      have hA : A.PosDef := by
        have hp := (Matrix.PosDef.one.smul hμ).add_posSemidef (Matrix.le_iff.mp hlo)
        simpa only [add_sub_cancel] using hp
      exact abs_sub_eliminationStep_le_choleskySchurErrorBound hμ hμB hu hu1
        (le_trans (choleskySchurErrorBound_le_choleskySchurErrorBound hu (hμ.le.trans hμB) hμ
          (Nat.le_of_lt hk)) hη.le)
        (le_gaussState_apply_self_of_smul_one_le hμ hlo ⟨k, hk⟩)
        (fun a b => by simpa only [Real.norm_eq_abs] using
          hA.posSemidef.norm_gaussState_apply_le hscale k a b)
        herr hlocal i j (by change k ≤ i.val; omega) (by change k ≤ j.val; omega)
  · intro i j hj
    obtain ⟨w, hr, hzero, hdiag, he⟩ := hprefix i j hj
    exact ⟨w, (Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hRL.symm)).trans hr,
      hzero, hdiag, he⟩

end NLAlib.Computation.CholeskyRounding
