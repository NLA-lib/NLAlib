/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveUpdates

/-!
# The Schur steps of a worklist round as tracked similarities

A round of the rounded deflation worklist in Schur mode (`NLAlib.ShiftedQR.solveRoundedWith`)
either finishes a block with a Schur leaf or decouples it and cuts it. Both steps act on one
range block of a matrix that is block upper triangular for the ranges, and both update the
couplings of the block with computed unitaries. This file shows that each step is a tracked
unitary similarity of the whole matrix (`NLAlib.IsTrackedUnitarySimilar`) with explicit errors,
and that the block structure (`NLAlib.ShiftedQR.SchurShape`) is kept: active blocks upper
Hessenberg, finished blocks upper triangular, exact zeros below the diagonal blocks. The coupling
errors of a step lie in two corners of the matrix with disjoint rows and columns, so their norm is
the larger of the two (`NLAlib.specNorm_add_le_max_of_support`).

## Main definitions

* `NLAlib.ShiftedQR.decoupleReplay`: the replays of a decoupling update before the cut.
* `NLAlib.ShiftedQR.SchurShape`: the shape of the matrix between rounds.

## Main results

* `NLAlib.specNorm_add_le_max_of_support`, `NLAlib.specNorm_couplingPart_le_max`: matrices
  supported on disjoint rows and columns.
* `NLAlib.ShiftedQR.decoupleUpdateMatrix_isPerturbedUnitarySimilarBy`: the decoupling update as
  a witnessed step.
* `NLAlib.ShiftedQR.leafUpdate_isTrackedUnitarySimilar`: the leaf update as a tracked step.
* `NLAlib.ShiftedQR.SchurShape.leaf`, `NLAlib.ShiftedQR.SchurShape.split`,
  `NLAlib.ShiftedQR.SchurShape.isUpperTriangular`, `NLAlib.ShiftedQR.SchurShape.deflationInv`:
  the shape through the rounds and at the end.
-/

@[expose] public section

namespace NLAlib

open Ops
open scoped Matrix

section Support

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- Disjoint corners: if $\mathbf{X}$ is supported on the rows of `r` and the columns of
`c`, and $\mathbf{Y}$ off both, then $\|\mathbf{X} + \mathbf{Y}\|_2 \le
\max(\|\mathbf{X}\|_2, \|\mathbf{Y}\|_2)$. -/
theorem specNorm_add_le_max_of_support {X Y : Matrix m n 𝕜} (r : m → Prop) (c : n → Prop)
    (hX : ∀ i j, ¬(r i ∧ c j) → X i j = 0) (hY : ∀ i j, ¬(¬r i ∧ ¬c j) → Y i j = 0) :
    specNorm (X + Y) ≤ max (specNorm X) (specNorm Y) := by
  classical
  set M := max (specNorm X) (specNorm Y)
  have hM : 0 ≤ M := (specNorm_nonneg X).trans (le_max_left _ _)
  refine (specNorm_le_iff hM).2 fun v => ?_
  set v₁ : n → 𝕜 := fun j => if c j then v j else 0
  set v₂ : n → 𝕜 := fun j => if c j then 0 else v j
  have hX1 : X *ᵥ v = X *ᵥ v₁ := by
    funext i; simp only [Matrix.mulVec, dotProduct, v₁]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : c j
    · simp [hj]
    · simp [hj, hX i j (fun h => hj h.2)]
  have hY2 : Y *ᵥ v = Y *ᵥ v₂ := by
    funext i; simp only [Matrix.mulVec, dotProduct, v₂]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : c j
    · simp [hj, hY i j (fun h => h.2 hj)]
    · simp [hj]
  have hXr : ∀ i, ¬r i → (X *ᵥ v) i = 0 := fun i hi => by
    simp [Matrix.mulVec, dotProduct, hX i _ (fun h => hi h.1)]
  have hYr : ∀ i, r i → (Y *ᵥ v) i = 0 := fun i hi => by
    simp [Matrix.mulVec, dotProduct, hY i _ (fun h => h.1 hi)]
  have hsq : ‖WithLp.toLp 2 ((X + Y) *ᵥ v)‖ ^ 2 =
      ‖WithLp.toLp 2 (X *ᵥ v₁)‖ ^ 2 + ‖WithLp.toLp 2 (Y *ᵥ v₂)‖ ^ 2 := by
    rw [← hX1, ← hY2]
    simp only [EuclideanSpace.norm_sq_eq, Matrix.add_mulVec, Pi.add_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : r i
    · simp [hYr i hi]
    · simp [hXr i hi]
  have hv : ‖WithLp.toLp 2 v₁‖ ^ 2 + ‖WithLp.toLp 2 v₂‖ ^ 2 = ‖WithLp.toLp 2 v‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, ← Finset.sum_add_distrib, v₁, v₂]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : c j <;> simp [hj]
  have h1 : ‖WithLp.toLp 2 (X *ᵥ v₁)‖ ≤ M * ‖WithLp.toLp 2 v₁‖ := (norm_toLp_mulVec_le X v₁).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h2 : ‖WithLp.toLp 2 (Y *ᵥ v₂)‖ ≤ M * ‖WithLp.toLp 2 v₂‖ := (norm_toLp_mulVec_le Y v₂).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [hsq, mul_pow, ← hv, mul_add]
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow] at h1' h2'
  linarith
end Support


section Embed
variable {N lo d : ℕ}

/-- The block embedding acts on the rows of the range only. -/
theorem embedBlock_mul_apply_of_not_mem (V : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) {i : Fin N} (hi : ¬(lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d))
    (j : Fin N) : (embedBlock (N := N) lo V * X) i j = X i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [embedBlock, hi]
  · intro k _ hk; simp [embedBlock, hi, Ne.symm hk]
  · simp

/-- The block embedding acts on the columns of the range only. -/
theorem mul_embedBlock_apply_of_not_mem (V : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) {j : Fin N}
    (hj : ¬(lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d)) : (X * embedBlock (N := N) lo V) i j = X i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simp [embedBlock, hj]
  · intro k _ hk
    by_cases hk' : lo ≤ (k : ℕ) ∧ (k : ℕ) < lo + d
    · simp [embedBlock, hk', hj]
    · simp [embedBlock, hk', hk]
  · simp

/-- A row of the range of $\operatorname{diag}(\mathbf{I}, \mathbf{V}, \mathbf{I})\mathbf{X}$:
the row of $\mathbf{V}$ times the rows of $\mathbf{X}$ on the range. -/
theorem embedBlock_mul_apply_of_mem (hN : lo + d ≤ N) (V : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) {i : Fin N} (hi : lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d)
    (j : Fin N) : (embedBlock (N := N) lo V * X) i j =
      ∑ a : Fin d, V ⟨(i : ℕ) - lo, by omega⟩ a * X ⟨lo + a, by omega⟩ j := by
  rw [Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (fun a : Fin d => (⟨lo + a, by omega⟩ : Fin N))
    (fun a b h => Fin.ext (by simpa using h)) _ _ (fun k hk => ?_) (fun a => ?_)
  · have hk' : ¬(lo ≤ (k : ℕ) ∧ (k : ℕ) < lo + d) := fun h =>
      hk ⟨⟨(k : ℕ) - lo, by omega⟩, Fin.ext (by simp; omega)⟩
    simp [embedBlock, hk', hi]
  · have ha := a.isLt
    simp [embedBlock, hi]

/-- A column of the range of $\mathbf{X}\operatorname{diag}(\mathbf{I}, \mathbf{V}, \mathbf{I})$:
the columns of $\mathbf{X}$ on the range times the column of $\mathbf{V}$. -/
theorem mul_embedBlock_apply_of_mem (hN : lo + d ≤ N) (V : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) {j : Fin N}
    (hj : lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d) : (X * embedBlock (N := N) lo V) i j =
      ∑ a : Fin d, X i ⟨lo + a, by omega⟩ * V a ⟨(j : ℕ) - lo, by omega⟩ := by
  rw [Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (fun a : Fin d => (⟨lo + a, by omega⟩ : Fin N))
    (fun a b h => Fin.ext (by simpa using h)) _ _ (fun k hk => ?_) (fun a => ?_)
  · have hk' : ¬(lo ≤ (k : ℕ) ∧ (k : ℕ) < lo + d) := fun h =>
      hk ⟨⟨(k : ℕ) - lo, by omega⟩, Fin.ext (by simp; omega)⟩
    have hkj : k ≠ j := fun h => hk' (h ▸ hj)
    simp [embedBlock, hk', hkj]
  · have ha := a.isLt
    simp [embedBlock, hj]

end Embed

section Rect

variable {N : ℕ}

/-- A rectangular block placed in the zero matrix keeps its spectral norm bound. -/
theorem specNorm_setRect_zero_le {m q : ℕ} {r0 c0 : ℕ} (hr : r0 + m ≤ N) (hc : c0 + q ≤ N)
    (E : Matrix (Fin m) (Fin q) ℂ) :
    specNorm (setRect (0 : Matrix (Fin N) (Fin N) ℂ) r0 c0 E) ≤ specNorm E := by
  refine (specNorm_le_iff (specNorm_nonneg E)).2 fun v => ?_
  set w : Fin q → ℂ := fun b => v ⟨c0 + b, by omega⟩
  have hrow : ∀ i : Fin N, (setRect (0 : Matrix (Fin N) (Fin N) ℂ) r0 c0 E *ᵥ v) i =
      if h : r0 ≤ (i : ℕ) ∧ (i : ℕ) < r0 + m then (E *ᵥ w) ⟨(i : ℕ) - r0, by omega⟩ else 0 := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    split_ifs with h
    · symm
      refine Fintype.sum_of_injective (fun b : Fin q => (⟨c0 + b, by omega⟩ : Fin N))
        (fun a b hab => Fin.ext (by simpa using hab)) _ _ (fun k hk => ?_) (fun b => ?_)
      · have hk' : ¬(c0 ≤ (k : ℕ) ∧ (k : ℕ) < c0 + q) := fun h' =>
          hk ⟨⟨(k : ℕ) - c0, by omega⟩, Fin.ext (by simp; omega)⟩
        simp [setRect, hk']
      · have hb := b.isLt
        simp only [setRect, Matrix.of_apply, w]
        rw [dif_pos ⟨h.1, h.2, by simp, by simp⟩]
        congr 2; ext; simp
    · refine Finset.sum_eq_zero fun k _ => ?_
      simp only [setRect, Matrix.of_apply]
      rw [dif_neg fun h' => h ⟨h'.1, h'.2.1⟩]; simp
  have hsq : ‖WithLp.toLp 2 (setRect (0 : Matrix (Fin N) (Fin N) ℂ) r0 c0 E *ᵥ v)‖ ^ 2 =
      ‖WithLp.toLp 2 (E *ᵥ w)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, hrow]
    symm
    refine Fintype.sum_of_injective (fun a : Fin m => (⟨r0 + a, by omega⟩ : Fin N))
      (fun a b hab => Fin.ext (by simpa using hab)) _ _ (fun k hk => ?_) (fun a => ?_)
    · have hk' : ¬(r0 ≤ (k : ℕ) ∧ (k : ℕ) < r0 + m) := fun h' =>
        hk ⟨⟨(k : ℕ) - r0, by omega⟩, Fin.ext (by simp; omega)⟩
      simp [hk']
    · have ha := a.isLt
      simp only
      rw [dif_pos ⟨by simp, by simp⟩]
      congr 3; ext; simp
  have hw : ‖WithLp.toLp 2 w‖ ^ 2 ≤ ‖WithLp.toLp 2 v‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, w]
    have e : ∑ b : Fin q, ‖v ⟨c0 + b, by omega⟩‖ ^ 2 =
        ∑ k ∈ Finset.univ.image (fun b : Fin q => (⟨c0 + b, by omega⟩ : Fin N)), ‖v k‖ ^ 2 :=
      (Finset.sum_image (f := fun k => ‖v k‖ ^ 2)
        fun a _ b _ hab => Fin.ext (by simpa using hab)).symm
    rw [e]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [hsq, mul_pow]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_toLp_mulVec_le E w) 2
  rw [mul_pow] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left hw (by positivity))
end Rect

section Replay

variable {M : Machine ℝ} {N : ℕ}

/-- The entries of a matrix masked on the left by `NLAlib.colMask` (a row mask). -/
theorem colMask_mul_apply (j0 nc : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (colMask N j0 nc * X) i j = if j0 ≤ (i : ℕ) ∧ (i : ℕ) < j0 + nc then X i j else 0 := by
  simp only [colMask, Matrix.diagonal_mul]; split_ifs <;> simp

/-- The entries of a matrix masked on the right by `NLAlib.colMask`. -/
theorem mul_colMask_apply (j0 nc : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (X * colMask N j0 nc) i j = if j0 ≤ (j : ℕ) ∧ (j : ℕ) < j0 + nc then X i j else 0 := by
  simp only [colMask, Matrix.mul_diagonal]; split_ifs <;> simp

/-- A row replay keeps the rows outside its two planes. -/
theorem replayRowStep_apply_row {lo j0 nc : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry)
    (r t : Fin N) (hr : (r : ℕ) ≠ lo + e.1) (hr' : (r : ℕ) ≠ lo + e.1 + 1) :
    replayRowStep M lo j0 nc X e r t = X r t := by
  unfold replayRowStep
  split_ifs
  · simp only [machineRowRotationOn, machineRowRotation, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> rfl
  · rfl

/-- A column replay keeps the columns outside its two planes. -/
theorem replayColumnStep_apply_col {lo i0 nr : ℕ} (X : Matrix (Fin N) (Fin N) ℂ)
    (e : GivensEntry) (r t : Fin N) (ht : (t : ℕ) ≠ lo + e.1) (ht' : (t : ℕ) ≠ lo + e.1 + 1) :
    replayColumnStep M lo i0 nr X e r t = X r t := by
  unfold replayColumnStep
  split_ifs
  · simp only [machineColRotationOn, machineColRotation, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> rfl
  · rfl

/-- A column replay on a row range keeps the other rows. -/
theorem replayColumnStep_apply_of_not_mem {lo i0 nr : ℕ} (X : Matrix (Fin N) (Fin N) ℂ)
    (e : GivensEntry) (r t : Fin N) (hr : ¬(i0 ≤ (r : ℕ) ∧ (r : ℕ) < i0 + nr)) :
    replayColumnStep M lo i0 nr X e r t = X r t := by
  unfold replayColumnStep
  split_ifs
  · simp [machineColRotationOn, hr]
  · rfl

/-- The row replay of a log inside the range keeps the rows outside it. -/
theorem foldl_replayRowStep_apply_row {lo d j0 nc : ℕ} (es : List GivensEntry)
    (hes : ∀ e ∈ es, e.1 + 1 < d) (X : Matrix (Fin N) (Fin N) ℂ) (r t : Fin N)
    (hr : ¬(lo ≤ (r : ℕ) ∧ (r : ℕ) < lo + d)) :
    es.foldl (replayRowStep M lo j0 nc) X r t = X r t := by
  induction es generalizing X with
  | nil => rfl
  | cons e es ih =>
    have he := hes e List.mem_cons_self
    rw [List.foldl_cons, ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he')),
      replayRowStep_apply_row _ _ _ _ (by omega) (by omega)]

/-- The column replay of a log inside the range keeps the columns outside it. -/
theorem foldl_replayColumnStep_apply_col {lo d i0 nr : ℕ} (es : List GivensEntry)
    (hes : ∀ e ∈ es, e.1 + 1 < d) (X : Matrix (Fin N) (Fin N) ℂ) (r t : Fin N)
    (ht : ¬(lo ≤ (t : ℕ) ∧ (t : ℕ) < lo + d)) :
    es.foldl (replayColumnStep M lo i0 nr) X r t = X r t := by
  induction es generalizing X with
  | nil => rfl
  | cons e es ih =>
    have he := hes e List.mem_cons_self
    rw [List.foldl_cons, ih (fun e' he' => hes e' (List.mem_cons_of_mem _ he')),
      replayColumnStep_apply_col _ _ _ _ (by omega) (by omega)]

/-- The column replay of a log on a row range keeps the other rows. -/
theorem foldl_replayColumnStep_apply_of_not_mem {lo i0 nr : ℕ} (es : List GivensEntry)
    (X : Matrix (Fin N) (Fin N) ℂ) (r t : Fin N) (hr : ¬(i0 ≤ (r : ℕ) ∧ (r : ℕ) < i0 + nr)) :
    es.foldl (replayColumnStep M lo i0 nr) X r t = X r t := by
  induction es generalizing X with
  | nil => rfl
  | cons e es ih => rw [List.foldl_cons, ih, replayColumnStep_apply_of_not_mem _ _ _ _ hr]

/-- A column replay on a row range, masked to the range, is the replay over all rows of the
masked matrix. -/
theorem colMask_mul_replayColumnStep {u : ℝ} (hM : StdModel u id M) (lo i0 nr : ℕ)
    (X : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) :
    colMask N i0 nr * replayColumnStep M lo i0 nr X e =
      replayColumnStep M lo 0 N (colMask N i0 nr * X) e := by
  ext r t
  rw [colMask_mul_apply]
  by_cases h : lo + e.1 + 1 < N
  · simp only [replayColumnStep, dif_pos h, machineColRotationOn, Matrix.of_apply,
      machineColRotation, colMask_mul_apply]
    by_cases hr : i0 ≤ (r : ℕ) ∧ (r : ℕ) < i0 + nr
    · simp [hr]
    · simp only [hr, if_false, Nat.zero_le, zero_add, r.isLt, and_self, if_true]
      split_ifs <;> simp [linearComplex_zero_zero hM]
  · simp [replayColumnStep, h, colMask_mul_apply]

/-- The masked column replay of a log is the full column replay of the masked matrix. -/
theorem colMask_mul_foldl_replayColumnStep {u : ℝ} (hM : StdModel u id M) (lo i0 nr : ℕ)
    (es : List GivensEntry) (X : Matrix (Fin N) (Fin N) ℂ) :
    colMask N i0 nr * es.foldl (replayColumnStep M lo i0 nr) X =
      es.foldl (replayColumnStep M lo 0 N) (colMask N i0 nr * X) := by
  induction es generalizing X with
  | nil => rfl
  | cons e es ih => simp only [List.foldl_cons, ih, colMask_mul_replayColumnStep hM]

end Replay

section Coupling

variable {N : ℕ}

/-- The entries of a matrix masked on both sides by `NLAlib.colMask`. -/
theorem colMask_mul_mul_colMask_apply (i0 nr j0 nc : ℕ) (X : Matrix (Fin N) (Fin N) ℂ)
    (i j : Fin N) : (colMask N i0 nr * X * colMask N j0 nc) i j =
      if (i0 ≤ (i : ℕ) ∧ (i : ℕ) < i0 + nr) ∧ (j0 ≤ (j : ℕ) ∧ (j : ℕ) < j0 + nc) then X i j
      else 0 := by
  rw [mul_colMask_apply, colMask_mul_apply]
  split_ifs <;> tauto

/-- The coupling part of a range step as two disjoint corners: if $\mathbf{D}$ vanishes on
the left and bottom couplings of the range $[lo, lo + d)$ and agrees with $\mathbf{X}$ on the
right coupling and with $\mathbf{Y}$ on the top coupling, its coupling part has spectral norm at
most $\max(\|\mathbf{X}\|_2, \|\mathbf{Y}\|_2)$ (the two corners have disjoint rows and
columns). -/
theorem specNorm_couplingPart_le_max {lo d : ℕ} (hN : lo + d ≤ N)
    {D X Y : Matrix (Fin N) (Fin N) ℂ}
    (hR : ∀ i j : Fin N, lo ≤ (i : ℕ) → (i : ℕ) < lo + d → lo + d ≤ (j : ℕ) → D i j = X i j)
    (hT : ∀ i j : Fin N, (i : ℕ) < lo → lo ≤ (j : ℕ) → (j : ℕ) < lo + d → D i j = Y i j)
    (hL : ∀ i j : Fin N, lo ≤ (i : ℕ) → (i : ℕ) < lo + d → (j : ℕ) < lo → D i j = 0)
    (hB : ∀ i j : Fin N, lo + d ≤ (i : ℕ) → lo ≤ (j : ℕ) → (j : ℕ) < lo + d → D i j = 0) :
    specNorm (couplingPart lo d D) ≤ max (specNorm X) (specNorm Y) := by
  set X' := colMask N lo d * X * colMask N (lo + d) (N - lo - d)
  set Y' := colMask N 0 lo * Y * colMask N lo d
  have e : couplingPart lo d D = X' + Y' := by
    ext i j
    have hi := i.isLt
    have hj := j.isLt
    simp only [couplingPart, Matrix.of_apply, Matrix.add_apply, X', Y',
      colMask_mul_mul_colMask_apply]
    by_cases hiR : lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d <;>
      by_cases hjR : lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d
    · rw [if_pos (iff_of_true hiR hjR), if_neg (by omega), if_neg (by omega), add_zero]
    · rw [if_neg (by tauto)]
      by_cases hjl : (j : ℕ) < lo
      · rw [if_neg (by omega), if_neg (by omega), add_zero, hL i j hiR.1 hiR.2 hjl]
      · rw [if_pos (by omega), if_neg (by omega), add_zero, hR i j hiR.1 hiR.2 (by omega)]
    · rw [if_neg (by tauto)]
      by_cases hil : (i : ℕ) < lo
      · rw [if_neg (by omega), if_pos (by omega), zero_add, hT i j hil hjR.1 hjR.2]
      · rw [if_neg (by omega), if_neg (by omega), add_zero, hB i j (by omega) hjR.1 hjR.2]
    · rw [if_pos (iff_of_false hiR hjR), if_neg (by omega), if_neg (by omega), add_zero]
  rw [e]
  refine (specNorm_add_le_max_of_support (fun i : Fin N => lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d)
    (fun j : Fin N => lo + d ≤ (j : ℕ)) (fun i j h => ?_) (fun i j h => ?_)).trans
    (max_le_max ?_ ?_)
  · simp only [X', colMask_mul_mul_colMask_apply]
    rw [if_neg (by have := j.isLt; omega)]
  · simp only [Y', colMask_mul_mul_colMask_apply]
    rw [if_neg (by omega)]
  · exact ((isStarProjection_colMask N (lo + d) (N - lo - d)).specNorm_mul_right_le _).trans
      ((isStarProjection_colMask N lo d).specNorm_mul_le _)
  · exact ((isStarProjection_colMask N lo d).specNorm_mul_right_le _).trans
      ((isStarProjection_colMask N 0 lo).specNorm_mul_le _)

end Coupling

/-- The adjoint of the block embedding acts on the rows of the range only. -/
theorem embedBlock_conjTranspose_mul_apply_of_not_mem {N lo d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) {i : Fin N} (hi : ¬(lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d))
    (j : Fin N) : ((embedBlock (N := N) lo V)ᴴ * X) i j = X i j := by
  rw [embedBlock_conjTranspose, embedBlock_mul_apply_of_not_mem _ _ hi]

/-- The entries of a range step $\widetilde{\mathbf{V}}^{\mathsf H}\mathbf{A}\widetilde{\mathbf{V}}$
off the columns of the range are those of $\widetilde{\mathbf{V}}^{\mathsf H}\mathbf{A}$. -/
theorem conjTranspose_mul_mul_embedBlock_apply_col {N lo d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) {j : Fin N}
    (hj : ¬(lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d)) :
    ((embedBlock (N := N) lo V)ᴴ * X * embedBlock (N := N) lo V) i j =
      ((embedBlock (N := N) lo V)ᴴ * X) i j :=
  mul_embedBlock_apply_of_not_mem _ _ _ hj

/-- The entries of a range step off the rows of the range are those of
$\mathbf{A}\widetilde{\mathbf{V}}$. -/
theorem conjTranspose_mul_mul_embedBlock_apply_row {N lo d : ℕ} (V : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (Fin N) (Fin N) ℂ) {i : Fin N} (hi : ¬(lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d))
    (j : Fin N) :
    ((embedBlock (N := N) lo V)ᴴ * X * embedBlock (N := N) lo V) i j =
      (X * embedBlock (N := N) lo V) i j := by
  rw [Matrix.mul_assoc, embedBlock_conjTranspose_mul_apply_of_not_mem _ _ hi]

/-- A range step of a range block triangular matrix vanishes on the left coupling. -/
theorem conjTranspose_mul_mul_embedBlock_left {N lo d : ℕ} (hN : lo + d ≤ N)
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsRangeBlockTriangular lo d A)
    (V : Matrix (Fin d) (Fin d) ℂ) {i j : Fin N} (hi : lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d)
    (hj : (j : ℕ) < lo) : ((embedBlock (N := N) lo V)ᴴ * A * embedBlock (N := N) lo V) i j = 0 := by
  rw [conjTranspose_mul_mul_embedBlock_apply_col _ _ _ (by omega), embedBlock_conjTranspose,
    embedBlock_mul_apply_of_mem hN _ _ hi]
  exact Finset.sum_eq_zero fun a _ => by rw [hA _ _ (Or.inl ⟨hj, by simp⟩), mul_zero]

/-- A range step of a range block triangular matrix vanishes on the bottom coupling. -/
theorem conjTranspose_mul_mul_embedBlock_bottom {N lo d : ℕ} (hN : lo + d ≤ N)
    {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsRangeBlockTriangular lo d A)
    (V : Matrix (Fin d) (Fin d) ℂ) {i j : Fin N} (hi : lo + d ≤ (i : ℕ))
    (hj : lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d) :
    ((embedBlock (N := N) lo V)ᴴ * A * embedBlock (N := N) lo V) i j = 0 := by
  rw [conjTranspose_mul_mul_embedBlock_apply_row _ _ (by omega),
    mul_embedBlock_apply_of_mem hN _ _ _ hj]
  exact Finset.sum_eq_zero fun a _ => by
    rw [hA _ _ (Or.inr ⟨by simp, hi⟩), zero_mul]

/-- A rectangular block inside the matrix has spectral norm at most that of the matrix. -/
theorem specNorm_subRect_le {N r0 c0 m q : ℕ} (hr : r0 + m ≤ N) (hc : c0 + q ≤ N)
    (A : Matrix (Fin N) (Fin N) ℂ) : specNorm (subRect A r0 c0 m q) ≤ specNorm A := by
  have e : subRect A r0 c0 m q = A.submatrix (fun i : Fin m => (⟨r0 + i, by omega⟩ : Fin N))
      (fun j : Fin q => (⟨c0 + j, by omega⟩ : Fin N)) := by
    ext i j
    have := i.isLt; have := j.isLt
    simp [subRect, show r0 + (i : ℕ) < N by omega, show c0 + (j : ℕ) < N by omega]
  rw [e]
  exact specNorm_submatrix_le A (fun a b h => Fin.ext (by simpa using h))
    (fun a b h => Fin.ext (by simpa using h))

namespace ShiftedQR

section DecoupleStep

variable {n : ℕ}

/-- The block of a range inside the matrix is the submatrix on the range embedding. -/
theorem subBlock_eq_submatrix_rangeEmb {lo d : ℕ} (hN : lo + d ≤ n + 1)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    subBlock A (lo, d) = A.submatrix (rangeEmb hN) (rangeEmb hN) := by
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [subBlock, blockIndex, Matrix.submatrix_apply, rangeEmb]
  congr 1 <;> ext <;> simp <;> omega

/-- The entries of `NLAlib.setSubBlock`: the block inside the range, the matrix outside. -/
theorem setSubBlock_apply {lo d : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Matrix (Fin d) (Fin d) ℂ) (i j : Fin (n + 1)) :
    setSubBlock A (lo, d) B i j =
      if h : lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d ∧ lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d then
        B ⟨i - lo, by omega⟩ ⟨j - lo, by omega⟩ else A i j := rfl

/-- The matrix after the replays of a decoupling update and before the cut: the log replayed on
the rows of the right coupling of the range $[lo, lo + d)$, then on the columns of its top
coupling. -/
noncomputable def decoupleReplay (M : Machine ℝ) {N : ℕ} (lo d : ℕ) (es : List GivensEntry)
    (A : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  es.foldl (replayColumnStep M lo 0 lo) (es.foldl (replayRowStep M lo (lo + d) (N - lo - d)) A)

/-- The decoupling update is the cut of the replays. -/
theorem decoupleUpdateMatrix_eq (M : Machine ℝ) {N : ℕ} (lo d i : ℕ) (es : List GivensEntry)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    decoupleUpdateMatrix M lo d i es A =
      cutEntry M (lo + i + 1) (lo + i) (decoupleReplay M lo d es A) :=
  rfl

/-- The replays keep the rows from `lo` on that their column fold does not reach. -/
theorem decoupleReplay_apply_of_le {M : Machine ℝ} {N lo d : ℕ} (es : List GivensEntry)
    (A : Matrix (Fin N) (Fin N) ℂ) {r : Fin N} (hr : lo ≤ (r : ℕ)) (t : Fin N) :
    decoupleReplay M lo d es A r t = es.foldl (replayRowStep M lo (lo + d) (N - lo - d)) A r t :=
  foldl_replayColumnStep_apply_of_not_mem _ _ _ _ (by omega)

/-- The replays keep the columns outside the range. -/
theorem decoupleReplay_apply_col {M : Machine ℝ} {N lo d : ℕ} {es : List GivensEntry}
    (hes : ∀ e ∈ es, e.1 + 1 < d) (A : Matrix (Fin N) (Fin N) ℂ) (r : Fin N) {t : Fin N}
    (ht : ¬(lo ≤ (t : ℕ) ∧ (t : ℕ) < lo + d)) :
    decoupleReplay M lo d es A r t = es.foldl (replayRowStep M lo (lo + d) (N - lo - d)) A r t :=
  foldl_replayColumnStep_apply_col es hes _ _ _ ht

/-- The row fold keeps the rows outside the range and the columns left of its coupling. -/
theorem foldl_replayRowStep_coupling_apply {M : Machine ℝ} {N lo d : ℕ} {es : List GivensEntry}
    (hes : ∀ e ∈ es, e.1 + 1 < d) (A : Matrix (Fin N) (Fin N) ℂ) (r t : Fin N)
    (h : ¬(lo ≤ (r : ℕ) ∧ (r : ℕ) < lo + d) ∨ (t : ℕ) < lo + d) :
    es.foldl (replayRowStep M lo (lo + d) (N - lo - d)) A r t = A r t := by
  rcases h with h | h
  · exact foldl_replayRowStep_apply_row es hes A r t h
  · exact foldl_replayRowStep_apply_of_not_mem es A r t (by omega)

/-- The replays keep every entry outside the right and top couplings of the range. -/
theorem decoupleReplay_apply_of_not_coupling {M : Machine ℝ} {N lo d : ℕ} {es : List GivensEntry}
    (hes : ∀ e ∈ es, e.1 + 1 < d) (A : Matrix (Fin N) (Fin N) ℂ) (r t : Fin N)
    (h : ¬((lo ≤ (r : ℕ) ∧ (r : ℕ) < lo + d) ∧ lo + d ≤ (t : ℕ)) ∧
      ¬((r : ℕ) < lo ∧ lo ≤ (t : ℕ) ∧ (t : ℕ) < lo + d)) :
    decoupleReplay M lo d es A r t = A r t := by
  by_cases hr : lo ≤ (r : ℕ)
  · rw [decoupleReplay_apply_of_le es A hr, foldl_replayRowStep_coupling_apply hes]
    by_cases ht : lo + d ≤ (t : ℕ)
    · exact Or.inl fun h' => h.1 ⟨h', ht⟩
    · exact Or.inr (by omega)
  · have ht : ¬(lo ≤ (t : ℕ) ∧ (t : ℕ) < lo + d) := fun h' => h.2 ⟨by omega, h'⟩
    rw [decoupleReplay_apply_col hes A r ht, foldl_replayRowStep_coupling_apply hes]
    exact Or.inl (by omega)

/-- The replays of the decoupling update of the range $[lo, lo + d)$ on a range block
triangular $\mathbf{A}$ with a new block $\mathbf{H}'$: the coupling part of the difference with
the exact step by $\widetilde{\mathbf{V}} =
\operatorname{diag}(\mathbf{I}, \mathbf{V}, \mathbf{I})$,
$\mathbf{V}$ the log's unitary, is at most $((1 + 24\boldsymbol{u})^{R} - 1)\|\mathbf{A}\|_2$,
$R$ the number of entries. -/
theorem specNorm_couplingPart_decoupleReplay_le {Mch : Machine ℝ} {u : ℝ}
    (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) {lo d : ℕ} (hN : lo + d ≤ n + 1)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : IsRangeBlockTriangular lo d A)
    (H' : Matrix (Fin d) (Fin d) ℂ) {es : List GivensEntry} (hes : ∀ e ∈ es, e.1 + 1 < d) :
    specNorm (couplingPart lo d (decoupleReplay Mch lo d es (setSubBlock A (lo, d) H') -
      (embedBlock lo (givensLog d es))ᴴ * A * embedBlock lo (givensLog d es))) ≤
        ((1 + 24 * u) ^ es.length - 1) * specNorm A := by
  set A₁ := setSubBlock A (lo, d) H'
  set W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := embedBlock lo (givensLog d es)
  set X₁ := es.foldl (replayRowStep Mch lo (lo + d) (n + 1 - lo - d)) A₁
  set Cr := colMask (n + 1) (lo + d) (n + 1 - lo - d)
  set Ct := colMask (n + 1) 0 lo
  have hes' : ∀ e ∈ es, lo + e.1 + 1 < n + 1 ∧ (e.1 + 1 < d ∨ e = (0, 0, 0)) :=
    fun e he => ⟨by have := hes e he; omega, Or.inl (hes e he)⟩
  have hA₁ : ∀ i j : Fin (n + 1), ¬((lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d) ∧
      (lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d)) → A₁ i j = A i j := fun i j h => by
    simp only [A₁, setSubBlock_apply]; rw [dif_neg (by tauto)]
  have hX₁ : ∀ i j : Fin (n + 1), (i : ℕ) < lo → X₁ i j = A i j := fun i j hi => by
    simp only [X₁]
    rw [foldl_replayRowStep_coupling_apply hes _ _ _ (Or.inl (by omega)), hA₁ _ _ (by omega)]
  have hCr : A₁ * Cr = A * Cr := by
    ext i j; simp only [Cr, mul_colMask_apply]
    split_ifs with h
    · exact hA₁ _ _ (by omega)
    · rfl
  have hCt : Ct * X₁ = Ct * A := by
    ext i j; simp only [Ct, colMask_mul_apply]
    split_ifs with h
    · exact hX₁ _ _ (by omega)
    · rfl
  refine (specNorm_couplingPart_le_max hN
    (X := es.foldl (replayRowStep Mch lo 0 (n + 1)) (A₁ * Cr) - Wᴴ * (A₁ * Cr))
    (Y := es.foldl (replayColumnStep Mch lo 0 (n + 1)) (Ct * X₁) - (Ct * X₁) * W)
    (fun i j hi1 hi2 hj => ?_) (fun i j hi hj1 hj2 => ?_) (fun i j hi1 hi2 hj => ?_)
    (fun i j hi hj1 hj2 => ?_)).trans (max_le ?_ ?_)
  · rw [Matrix.sub_apply, Matrix.sub_apply, decoupleReplay_apply_of_le es _ hi1,
      ← foldl_replayRowStep_mul_colMask hM, mul_colMask_apply, if_pos (by omega),
      conjTranspose_mul_mul_embedBlock_apply_col _ _ _ (by omega), hCr, ← Matrix.mul_assoc,
      mul_colMask_apply, if_pos (by omega)]
  · have e : decoupleReplay Mch lo d es A₁ i j = (Ct * decoupleReplay Mch lo d es A₁) i j := by
      rw [colMask_mul_apply, if_pos (by omega)]
    rw [Matrix.sub_apply, Matrix.sub_apply, e, decoupleReplay,
      colMask_mul_foldl_replayColumnStep hM, conjTranspose_mul_mul_embedBlock_apply_row _ _
      (by omega), hCt, Matrix.mul_assoc, colMask_mul_apply, if_pos (by omega)]
  · rw [Matrix.sub_apply, conjTranspose_mul_mul_embedBlock_left hN hA _ ⟨hi1, hi2⟩ hj,
      decoupleReplay_apply_of_not_coupling hes _ _ _ ⟨by omega, by omega⟩, hA₁ _ _ (by omega),
      hA _ _ (Or.inl ⟨hj, hi1⟩), sub_zero]
  · rw [Matrix.sub_apply, conjTranspose_mul_mul_embedBlock_bottom hN hA _ hi ⟨hj1, hj2⟩,
      decoupleReplay_apply_of_not_coupling hes _ _ _ ⟨by omega, by omega⟩, hA₁ _ _ (by omega),
      hA _ _ (Or.inr ⟨hj2, hi⟩), sub_zero]
  · refine (specNorm_foldl_replayRowStep_sub_le hM hu0 hu hN es hes' _).trans ?_
    rw [hCr]
    exact mul_le_mul_of_nonneg_left ((isStarProjection_colMask _ _ _).specNorm_mul_right_le A)
      (by linarith [one_le_pow₀ (n := es.length) (show (1 : ℝ) ≤ 1 + 24 * u by linarith)])
  · refine (specNorm_foldl_replayColumnStep_sub_le hM hu0 hu hN es hes' _).trans ?_
    rw [hCt]
    exact mul_le_mul_of_nonneg_left ((isStarProjection_colMask _ _ _).specNorm_mul_le A)
      (by linarith [one_le_pow₀ (n := es.length) (show (1 : ℝ) ≤ 1 + 24 * u by linarith)])

/-- The replays keep a range block triangular matrix with a new block range block triangular,
and read back the new block. -/
theorem decoupleReplay_isRangeBlockTriangular {Mch : Machine ℝ} {lo d : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : IsRangeBlockTriangular lo d A)
    (H' : Matrix (Fin d) (Fin d) ℂ) {es : List GivensEntry} (hes : ∀ e ∈ es, e.1 + 1 < d) :
    IsRangeBlockTriangular lo d (decoupleReplay Mch lo d es (setSubBlock A (lo, d) H')) := by
  intro i j h
  rw [decoupleReplay_apply_of_not_coupling hes _ _ _ ⟨by omega, by omega⟩, setSubBlock_apply,
    dif_neg (by omega), hA i j h]

/-- The decoupling update as a witnessed step: on a machine with the standard model at
$0 \le \boldsymbol{u} \le 1/100$ and the exact literal $0$, let $\mathbf{A}$ of order $n + 1$
be block upper triangular for the three ranges around $[lo, lo + d + 1)$ and let the new block
$\mathbf{H}'$ be a perturbed unitary similarity of the block of $\mathbf{A}$ with error
$\varepsilon$ by the unitary $\mathbf{V}$ of a log `es` of rotations inside the block. The
decoupling update with the cut after the block row $i < d$ with $|h'_{i+1,i}| \le c$ is a
perturbed unitary similarity of $\mathbf{A}$ by $\operatorname{diag}(\mathbf{I}, \mathbf{V},
\mathbf{I})$ with error $\varepsilon + ((1 + 24\boldsymbol{u})^{R} - 1)\|\mathbf{A}\|_2 + c$,
$R$ the number of entries. -/
theorem decoupleUpdateMatrix_isPerturbedUnitarySimilarBy {Mch : Machine ℝ} {u : ℝ}
    (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) (hz : Mch.lit 0 = 0)
    {lo d : ℕ} (hN : lo + (d + 1) ≤ n + 1) {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hA : IsRangeBlockTriangular lo (d + 1) A) {H' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    {es : List GivensEntry} (hes : ∀ e ∈ es, e.1 + 1 < d + 1) {ε c : ℝ}
    (hblk : IsPerturbedUnitarySimilarBy (givensLog (d + 1) es) (subBlock A (lo, d + 1)) H' ε)
    (i : Fin d) (hc : ‖H' i.succ i.castSucc‖ ≤ c) :
    IsPerturbedUnitarySimilarBy (embedBlock lo (givensLog (d + 1) es)) A
      (decoupleUpdateMatrix Mch lo (d + 1) i es (setSubBlock A (lo, d + 1) H'))
      (ε + ((1 + 24 * u) ^ es.length - 1) * specNorm A + c) := by
  set T := decoupleReplay Mch lo (d + 1) es (setSubBlock A (lo, d + 1) H')
  have hblkT : T.submatrix (rangeEmb hN) (rangeEmb hN) = H' := by
    ext a b
    have ha := a.isLt
    have hb := b.isLt
    simp only [T, Matrix.submatrix_apply, rangeEmb]
    rw [decoupleReplay_apply_of_not_coupling (by simpa using hes) _ _ _ (by simp; omega),
      setSubBlock_apply, dif_pos (by simp; omega)]
    congr 1 <;> ext <;> simp
  have h₁ := IsPerturbedUnitarySimilarBy.of_range_block hN hA
    (decoupleReplay_isRangeBlockTriangular hA H' hes)
    (by rw [hblkT, ← subBlock_eq_submatrix_rangeEmb hN]; exact hblk)
    (fun i' j' hi hj => by
      rw [decoupleReplay_apply_of_not_coupling hes _ _ _ ⟨by omega, by omega⟩, setSubBlock_apply,
        dif_neg (by omega)])
    (specNorm_couplingPart_decoupleReplay_le hM hu0 hu hN hA H' hes)
  have hp : lo + (i : ℕ) + 1 < n + 1 := by omega
  have hT : T ⟨lo + i + 1, hp⟩ ⟨lo + i, by omega⟩ = H' i.succ i.castSucc := by
    simp only [T]
    rw [decoupleReplay_apply_of_not_coupling hes _ _ _ ⟨by simp, by simp; omega⟩,
      setSubBlock_apply, dif_pos (by simp; omega)]
    congr 1
    · ext; simp; omega
    · ext; simp
  have h₂ : IsPerturbedUnitarySimilarBy 1 T (cutEntry Mch (lo + i + 1) (lo + i) T) c := by
    refine IsPerturbedUnitarySimilarBy.of_specNorm_sub_le hasOrthonormalCols_one ?_
    have e : cutEntry Mch (lo + i + 1) (lo + i) T - 1ᴴ * T * 1 =
        Matrix.single ⟨lo + i + 1, hp⟩ ⟨lo + i, by omega⟩
          (-T ⟨lo + i + 1, hp⟩ ⟨lo + i, by omega⟩) := by
      ext r t
      simp only [cutEntry, hz, Matrix.of_apply, Matrix.conjTranspose_one, Matrix.one_mul,
        Matrix.mul_one, Matrix.sub_apply, Matrix.single_apply, Fin.ext_iff]
      split_ifs with h1 h2 h2
      · have e1 : r = ⟨lo + i + 1, hp⟩ := Fin.ext h1.1
        have e2 : t = ⟨lo + i, by omega⟩ := Fin.ext h1.2
        rw [e1, e2]; simp; rfl
      · exfalso; omega
      · exfalso; omega
      · simp
    rw [e]
    exact (specNorm_single_le _ _ _).trans (by rw [norm_neg, hT]; exact hc)
  have := h₁.trans h₂
  rwa [Matrix.mul_one] at this

end DecoupleStep

/-- The error of a stored product with a near-unitary leaf accumulator: with
$\|\mathbf{U}_b - \mathbf{V}\|_2 \le \varepsilon_L$, $\mathbf{V}$ unitary of order $d$, and
$\mathbf{X}$ with $d$ columns, $\|\mathrm{fl}(\mathbf{X}\mathbf{U}_b) - \mathbf{X}\mathbf{V}\|_2
\le (g d(1 + \varepsilon_L) + \varepsilon_L)\|\mathbf{X}\|_2$, $g$ the growth of
`NLAlib.Ops.StdModel.specNorm_matMulWord_sub_le_growth`. -/
theorem specNorm_matMulWord_sub_mul_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu8 : u ≤ 1 / 8) {m d : ℕ} (X : Matrix (Fin m) (Fin d) ℂ)
    {Ub V : Matrix (Fin d) (Fin d) ℂ} (hV : HasOrthonormalCols V) {εL : ℝ}
    (hUb : specNorm (Ub - V) ≤ εL) :
    specNorm (matMulWord M X Ub - X * V) ≤
      ((1 + (6 * u + 5 * u ^ 2)) ^ d * (5 * u + d * (6 * u + 5 * u ^ 2)) * d * (1 + εL) + εL) *
        specNorm X := by
  set g := (1 + (6 * u + 5 * u ^ 2)) ^ d * (5 * u + d * (6 * u + 5 * u ^ 2))
  have hg0 : 0 ≤ g := by positivity
  have hUbn : specNorm Ub ≤ 1 + εL := by
    have := specNorm_add_le (Ub - V) V
    rw [sub_add_cancel] at this
    linarith [hV.specNorm_le_one]
  have hq : (0 : ℝ) ≤ √(d : ℝ) := Real.sqrt_nonneg _
  have hqq : √(d : ℝ) * √(d : ℝ) = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hXF : frobNorm X ≤ √(d : ℝ) * specNorm X := by
    simpa using frobNorm_le_sqrt_card_mul_specNorm X
  have hUbF : frobNorm Ub ≤ √(d : ℝ) * (1 + εL) :=
    (by simpa using frobNorm_le_sqrt_card_mul_specNorm Ub :
      frobNorm Ub ≤ √(d : ℝ) * specNorm Ub).trans
      (mul_le_mul_of_nonneg_left hUbn hq)
  have e : matMulWord M X Ub - X * V = (matMulWord M X Ub - X * Ub) + X * (Ub - V) := by
    rw [Matrix.mul_sub]; abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  have h1 := (hM.specNorm_matMulWord_sub_le_growth hu0 hu8 X Ub).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul hXF hUbF (frobNorm_nonneg _) (by positivity)) hg0)
  have h2 : specNorm (X * (Ub - V)) ≤ specNorm X * εL :=
    (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hUb (specNorm_nonneg _))
  have e2 : g * (√(d : ℝ) * specNorm X * (√(d : ℝ) * (1 + εL))) =
      g * (√(d : ℝ) * √(d : ℝ)) * (1 + εL) * specNorm X := by ring
  rw [e2, hqq] at h1
  nlinarith [specNorm_nonneg X]


section Shape

variable {n : ℕ}

/-- A partition into ranges stays one under a permutation of the list. -/
theorem _root_.NLAlib.IsRangePartition.perm {N : ℕ} {L L' : List (ℕ × ℕ)}
    (h : IsRangePartition N L) (hp : L.Perm L') : IsRangePartition N L' :=
  ⟨hp.nodup_iff.mp h.1, fun r hr => h.2.1 r (hp.mem_iff.mpr hr), fun i hi => by
    obtain ⟨c, ⟨hc1, hc2, hc3⟩, hcu⟩ := h.2.2 i hi
    exact ⟨c, ⟨hp.mem_iff.mp hc1, hc2, hc3⟩,
      fun y hy => hcu y ⟨hp.mem_iff.mpr hy.1, hy.2.1, hy.2.2⟩⟩⟩

/-- Splitting the first range of a partition into two consecutive ranges gives a partition. -/
theorem _root_.NLAlib.IsRangePartition.split_cons {N lo d i : ℕ} {rest : List (ℕ × ℕ)}
    (h : IsRangePartition N ((lo, d) :: rest)) (hi : i + 1 < d) :
    IsRangePartition N ((lo, i + 1) :: (lo + i + 1, d - i - 1) :: rest) := by
  obtain ⟨hnd, hval, huniq⟩ := h
  have hlo := hval (lo, d) List.mem_cons_self
  have hpar : ∀ r ∈ rest, ∀ k < N, r.1 ≤ k → k < r.1 + r.2 → ¬(lo ≤ k ∧ k < lo + d) := by
    intro r hr k hk h₁ h₂ h₃
    have := (huniq k hk).unique ⟨List.mem_cons_of_mem _ hr, h₁, h₂⟩ ⟨List.mem_cons_self, h₃⟩
    exact (List.nodup_cons.mp hnd).1 (this ▸ hr)
  simp only at hlo
  refine ⟨?_, ?_, ?_⟩
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, (List.nodup_cons.mp hnd).2⟩⟩
    · simp only [List.mem_cons, Prod.mk.injEq, not_or]
      exact ⟨by omega, fun hr => hpar _ hr lo (by omega) le_rfl (by simp) ⟨le_rfl, by omega⟩⟩
    · exact fun hr => hpar _ hr (lo + i + 1) (by omega) le_rfl (by simp; omega)
        ⟨by omega, by omega⟩
  · intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | rfl | hr
    · simp; omega
    · simp; omega
    · exact hval r (List.mem_cons_of_mem _ hr)
  · intro k hk
    by_cases hkb : lo ≤ k ∧ k < lo + d
    · by_cases hk' : k < lo + i + 1
      · refine ⟨(lo, i + 1), ⟨List.mem_cons_self, by simp; omega⟩, ?_⟩
        rintro r' ⟨hr', h₁, h₂⟩
        simp only [List.mem_cons] at hr'
        rcases hr' with rfl | rfl | hr'
        · rfl
        · simp at h₁; omega
        · exact absurd hkb (hpar r' hr' k hk h₁ h₂)
      · refine ⟨(lo + i + 1, d - i - 1), ⟨by simp, by simp; omega⟩, ?_⟩
        rintro r' ⟨hr', h₁, h₂⟩
        simp only [List.mem_cons] at hr'
        rcases hr' with rfl | rfl | hr'
        · simp at h₂; omega
        · rfl
        · exact absurd hkb (hpar r' hr' k hk h₁ h₂)
    · obtain ⟨r₀, ⟨hr₀, h₁, h₂⟩, hu⟩ := huniq k hk
      have hr₀' : r₀ ∈ rest := by
        rcases List.mem_cons.mp hr₀ with rfl | h
        · exact absurd ⟨h₁, h₂⟩ hkb
        · exact h
      refine ⟨r₀, ⟨by simp [hr₀'], h₁, h₂⟩, ?_⟩
      rintro r' ⟨hr', h₁', h₂'⟩
      simp only [List.mem_cons] at hr'
      rcases hr' with rfl | rfl | hr'
      · simp at h₁' h₂'; omega
      · simp at h₁' h₂'; omega
      · exact hu r' ⟨List.mem_cons_of_mem _ hr', h₁', h₂'⟩

/-- Splitting a range in the middle of a partition into two consecutive ranges, the right one
first, gives a partition. -/
theorem _root_.NLAlib.IsRangePartition.split_append {N lo d i : ℕ} {rs done : List (ℕ × ℕ)}
    (h : IsRangePartition N (rs ++ [(lo, d)] ++ done)) (hi : i + 1 < d) :
    IsRangePartition N (rs ++ [(lo + i + 1, d - i - 1), (lo, i + 1)] ++ done) := by
  have hp0 : (rs ++ [(lo, d)] ++ done).Perm ((lo, d) :: (rs ++ done)) := by
    simp [List.perm_middle]
  have hp1 : ((lo, i + 1) :: (lo + i + 1, d - i - 1) :: (rs ++ done)).Perm
      (rs ++ [(lo + i + 1, d - i - 1), (lo, i + 1)] ++ done) := by
    refine (List.Perm.swap _ _ _).trans ?_
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact (List.perm_middle.trans (List.Perm.cons _ List.perm_middle)).symm
  exact ((h.perm hp0).split_cons hi).perm hp1

/-- **The shape of the matrix in the Schur-mode worklist**: the active and the finished ranges
partition the indices, every nonzero entry below the diagonal lies in a diagonal block, the
active blocks are upper Hessenberg and the finished blocks upper triangular. -/
def SchurShape (n : ℕ) (active done : List (ℕ × ℕ)) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Prop :=
  IsRangePartition (n + 1) (active ++ done) ∧
    (∀ i j : Fin (n + 1), (j : ℕ) < i → A i j ≠ 0 →
      ∃ r ∈ active ++ done, r.1 ≤ (j : ℕ) ∧ (i : ℕ) < r.1 + r.2) ∧
    (∀ r ∈ active, IsUpperHessenberg (subBlock A r)) ∧
    ∀ r ∈ done, (subBlock A r).IsUpperTriangular

/-- The start: an upper Hessenberg matrix is one active range. -/
theorem SchurShape.init {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) :
    SchurShape n [(0, n + 1)] [] H := by
  refine ⟨?_, fun i j _ _ => ⟨(0, n + 1), by simp, by simp, by have := i.isLt; omega⟩, ?_,
    by simp⟩
  · refine ⟨by simp, fun r hr => ?_, fun i hi => ⟨(0, n + 1), ⟨by simp, by simp, by omega⟩, ?_⟩⟩
    · simp only [List.append_nil, List.mem_singleton] at hr; subst hr; simp
    · rintro q ⟨hq, -, -⟩; simpa using hq
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact hH.subBlock (by simp)

/-- A range of the shape: the matrix is block upper triangular for the three ranges around it. -/
theorem SchurShape.isRangeBlockTriangular {active done : List (ℕ × ℕ)}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (h : SchurShape n active done A) {r : ℕ × ℕ}
    (hr : r ∈ active ++ done) : IsRangeBlockTriangular r.1 r.2 A := by
  intro i j hij
  by_contra hne
  obtain ⟨q, hq, hq1, hq2⟩ := h.2.1 i j (by omega) hne
  have hr' := h.1.2.1 r hr
  have key : ∀ k, k < n + 1 → r.1 ≤ k → k < r.1 + r.2 → q.1 ≤ k → k < q.1 + q.2 → q = r :=
    fun k hk h1 h2 h3 h4 => by
      obtain ⟨c, -, hc⟩ := h.1.2.2 k hk
      exact (hc q ⟨hq, h3, h4⟩).trans (hc r ⟨hr, h1, h2⟩).symm
  rcases hij with hij | hij
  · have := key r.1 (by omega) le_rfl (by omega) (by omega) (by omega)
    subst this; omega
  · have := key (r.1 + r.2 - 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    subst this; omega

/-- The block of a range of a partition is read without clamping. -/
theorem _root_.NLAlib.IsRangePartition.subBlock_apply {L : List (ℕ × ℕ)}
    (hL : IsRangePartition (n + 1) L) {r : ℕ × ℕ} (hr : r ∈ L)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a b : Fin r.2) :
    subBlock A r a b = A ⟨r.1 + a, by have := (hL.2.1 r hr).2; omega⟩
      ⟨r.1 + b, by have := (hL.2.1 r hr).2; omega⟩ := by
  simp only [subBlock, Matrix.submatrix_apply]
  congr 1 <;> exact Fin.ext (hL.val_blockIndex hr _)

/-- The block of a range of the shape is read without clamping. -/
theorem SchurShape.subBlock_apply {active done : List (ℕ × ℕ)}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (h : SchurShape n active done A) {r : ℕ × ℕ}
    (hr : r ∈ active ++ done) (a b : Fin r.2) :
    subBlock A r a b = A ⟨r.1 + a, by have := (h.1.2.1 r hr).2; omega⟩
      ⟨r.1 + b, by have := (h.1.2.1 r hr).2; omega⟩ :=
  h.1.subBlock_apply hr A a b

/-- The end of the worklist: with no active range left, the matrix is upper triangular. -/
theorem SchurShape.isUpperTriangular {done : List (ℕ × ℕ)}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (h : SchurShape n [] done A) :
    A.IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  by_contra hne
  obtain ⟨r, hr, h1, h2⟩ := h.2.1 i j hij hne
  have hr' : r ∈ done := by simpa using hr
  have hb := h.2.2.2 r hr' (show (⟨(j : ℕ) - r.1, by omega⟩ : Fin r.2) < ⟨(i : ℕ) - r.1, by omega⟩
    from by simp only [Fin.mk_lt_mk]; omega)
  rw [h.subBlock_apply hr] at hb
  exact hne (by convert hb using 2 <;> ext <;> simp <;> omega)

end Shape

section LeafStep

variable {n : ℕ}

/-- The leaf update keeps every entry outside the right and top couplings of the range. -/
theorem leafUpdateMatrix_apply_of_not_coupling (M : Machine ℝ) {N lo d : ℕ}
    (Ub : Matrix (Fin d) (Fin d) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) (r t : Fin N)
    (h : ¬((lo ≤ (r : ℕ) ∧ (r : ℕ) < lo + d) ∧ lo + d ≤ (t : ℕ)) ∧
      ¬((r : ℕ) < lo ∧ lo ≤ (t : ℕ) ∧ (t : ℕ) < lo + d)) :
    leafUpdateMatrix M lo Ub A r t = A r t := by
  simp only [leafUpdateMatrix, setRect, Matrix.of_apply]
  rw [dif_neg (by omega), dif_neg (by omega)]

/-- The right coupling after the leaf update. -/
theorem leafUpdateMatrix_apply_right (M : Machine ℝ) {N lo d : ℕ}
    (Ub : Matrix (Fin d) (Fin d) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) {r t : Fin N}
    (hr : lo ≤ (r : ℕ) ∧ (r : ℕ) < lo + d) (ht : lo + d ≤ (t : ℕ)) :
    leafUpdateMatrix M lo Ub A r t = matMulWord M (machineConjTranspose M Ub)
      (subRect A lo (lo + d) d (N - lo - d)) ⟨(r : ℕ) - lo, by omega⟩
        ⟨(t : ℕ) - (lo + d), by have := t.isLt; omega⟩ := by
  simp only [leafUpdateMatrix, setRect, Matrix.of_apply]
  rw [dif_neg (by omega), dif_pos (by have := t.isLt; omega)]

/-- The top coupling after the leaf update. -/
theorem leafUpdateMatrix_apply_top (M : Machine ℝ) {N lo d : ℕ}
    (Ub : Matrix (Fin d) (Fin d) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) {r t : Fin N}
    (hr : (r : ℕ) < lo) (ht : lo ≤ (t : ℕ) ∧ (t : ℕ) < lo + d) :
    leafUpdateMatrix M lo Ub A r t = matMulWord M (subRect A 0 lo lo d) Ub ⟨r, hr⟩
      ⟨(t : ℕ) - lo, by omega⟩ := by
  simp only [leafUpdateMatrix, setRect, Matrix.of_apply]
  rw [dif_pos (by omega)]
  congr 1
  ext i j
  have := i.isLt; have := j.isLt
  simp only [subRect, Matrix.of_apply]
  split_ifs <;> first | rfl | omega

/-- The left form of `NLAlib.specNorm_matMulWord_sub_mul_le`: with
$\|\mathbf{U}_b - \mathbf{V}\|_2 \le \varepsilon_L$, $\mathbf{V}$ unitary of order $d$, and
$\mathbf{Y}$ with $d$ rows, $\|\mathrm{fl}(\mathbf{U}_b^{\mathsf H}\mathbf{Y}) -
\mathbf{V}^{\mathsf H}\mathbf{Y}\|_2 \le (g d(1 + \varepsilon_L) +
\varepsilon_L)\|\mathbf{Y}\|_2$. -/
theorem specNorm_matMulWord_conjTranspose_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu8 : u ≤ 1 / 8) {m d : ℕ} (Y : Matrix (Fin d) (Fin m) ℂ)
    {Ub V : Matrix (Fin d) (Fin d) ℂ} (hV : HasOrthonormalCols V) {εL : ℝ} (hεL : 0 ≤ εL)
    (hUb : specNorm (Ub - V) ≤ εL) :
    specNorm (matMulWord M Ubᴴ Y - Vᴴ * Y) ≤
      ((1 + (6 * u + 5 * u ^ 2)) ^ d * (5 * u + d * (6 * u + 5 * u ^ 2)) * d * (1 + εL) + εL) *
        specNorm Y := by
  set g := (1 + (6 * u + 5 * u ^ 2)) ^ d * (5 * u + d * (6 * u + 5 * u ^ 2))
  have hg0 : 0 ≤ g := by positivity
  have hUbn : specNorm Ub ≤ 1 + εL := by
    have := specNorm_add_le (Ub - V) V
    rw [sub_add_cancel] at this
    linarith [hV.specNorm_le_one]
  have hq : (0 : ℝ) ≤ √(d : ℝ) := Real.sqrt_nonneg _
  have hqq : √(d : ℝ) * √(d : ℝ) = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hYF : frobNorm Y ≤ √(d : ℝ) * specNorm Y := by
    rw [← frobNorm_conjTranspose, ← specNorm_conjTranspose Y]
    simpa using frobNorm_le_sqrt_card_mul_specNorm Yᴴ
  have hUbF : frobNorm Ubᴴ ≤ √(d : ℝ) * (1 + εL) := by
    rw [frobNorm_conjTranspose]
    exact (by simpa using frobNorm_le_sqrt_card_mul_specNorm Ub :
      frobNorm Ub ≤ √(d : ℝ) * specNorm Ub).trans (mul_le_mul_of_nonneg_left hUbn hq)
  have e : matMulWord M Ubᴴ Y - Vᴴ * Y = (matMulWord M Ubᴴ Y - Ubᴴ * Y) + (Ub - V)ᴴ * Y := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul]; abel
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  have h1 := (hM.specNorm_matMulWord_sub_le_growth hu0 hu8 Ubᴴ Y).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul hUbF hYF (frobNorm_nonneg _) (by positivity)) hg0)
  have h2 : specNorm ((Ub - V)ᴴ * Y) ≤ εL * specNorm Y :=
    (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (by rwa [specNorm_conjTranspose])
      (specNorm_nonneg _))
  have e2 : g * (√(d : ℝ) * (1 + εL) * (√(d : ℝ) * specNorm Y)) =
      g * (√(d : ℝ) * √(d : ℝ)) * (1 + εL) * specNorm Y := by ring
  rw [e2, hqq] at h1
  nlinarith [specNorm_nonneg Y]

/-- The coupling part of the leaf update: on a range block triangular $\mathbf{A}$, with
$\|\mathbf{U}_b - \mathbf{V}\|_2 \le \varepsilon_L$ and $\mathbf{V}$ unitary, the couplings
computed with $\mathbf{U}_b$ are within $(g d(1 + \varepsilon_L) + \varepsilon_L)
\|\mathbf{A}\|_2$ of those of the exact step by $\operatorname{diag}(\mathbf{I}, \mathbf{V},
\mathbf{I})$. -/
theorem leafUpdate_couplingPart_le {Mch : Machine ℝ} {u : ℝ} (hM : StdModel u id Mch)
    (hu0 : 0 ≤ u) (hu8 : u ≤ 1 / 8) {lo d : ℕ} (hN : lo + d ≤ n + 1)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : IsRangeBlockTriangular lo d A)
    {Ub V Tb : Matrix (Fin d) (Fin d) ℂ} (hV : HasOrthonormalCols V) {εL : ℝ} (hεL : 0 ≤ εL)
    (hUb : specNorm (Ub - V) ≤ εL) :
    specNorm (couplingPart lo d (leafUpdateMatrix Mch lo Ub (setSubBlock A (lo, d) Tb) -
      (embedBlock lo V)ᴴ * A * embedBlock lo V)) ≤
      ((1 + (6 * u + 5 * u ^ 2)) ^ d * (5 * u + d * (6 * u + 5 * u ^ 2)) * d * (1 + εL) + εL) *
        specNorm A := by
  set A₁ := setSubBlock A (lo, d) Tb
  set R₁ := subRect A₁ lo (lo + d) d (n + 1 - lo - d)
  set T₁ := subRect A₁ 0 lo lo d
  have hA₁ : ∀ i j : Fin (n + 1), ¬((lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d) ∧
      (lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d)) → A₁ i j = A i j := fun i j h => by
    simp only [A₁, setSubBlock_apply]; rw [dif_neg (by tauto)]
  have hR₁ : R₁ = subRect A lo (lo + d) d (n + 1 - lo - d) := by
    ext a b; have := a.isLt; have := b.isLt
    simp only [R₁, subRect, Matrix.of_apply]
    split_ifs
    · exact hA₁ _ _ (by simp)
    · rfl
  have hT₁ : T₁ = subRect A 0 lo lo d := by
    ext a b; have := a.isLt; have := b.isLt
    simp only [T₁, subRect, Matrix.of_apply]
    split_ifs
    · exact hA₁ _ _ (by simp)
    · rfl
  refine (specNorm_couplingPart_le_max hN
    (X := setRect 0 lo (lo + d) (matMulWord Mch Ubᴴ R₁ - Vᴴ * R₁))
    (Y := setRect 0 0 lo (matMulWord Mch T₁ Ub - T₁ * V))
    (fun i j hi1 hi2 hj => ?_) (fun i j hi hj1 hj2 => ?_) (fun i j hi1 hi2 hj => ?_)
    (fun i j hi hj1 hj2 => ?_)).trans (max_le ?_ ?_)
  · rw [Matrix.sub_apply, leafUpdateMatrix_apply_right _ _ _ ⟨hi1, hi2⟩ hj,
      conjTranspose_mul_mul_embedBlock_apply_col _ _ _ (by omega), embedBlock_conjTranspose,
      embedBlock_mul_apply_of_mem hN _ _ ⟨hi1, hi2⟩, machineConjTranspose_eq hM]
    simp only [setRect, Matrix.of_apply, Matrix.zero_apply]
    rw [dif_pos (by have := j.isLt; omega), Matrix.sub_apply, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    have := a.isLt; have := j.isLt
    rw [hR₁]
    simp only [subRect, Matrix.of_apply]
    rw [dif_pos (by omega)]
    congr 2; ext; simp; omega
  · rw [Matrix.sub_apply, leafUpdateMatrix_apply_top _ _ _ hi ⟨hj1, hj2⟩,
      conjTranspose_mul_mul_embedBlock_apply_row _ _ (by omega),
      mul_embedBlock_apply_of_mem hN _ _ _ ⟨hj1, hj2⟩]
    simp only [setRect, Matrix.of_apply, Matrix.zero_apply]
    rw [dif_pos (by omega), Matrix.sub_apply, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    have := a.isLt
    rw [hT₁]
    simp only [subRect, Matrix.of_apply]
    rw [dif_pos (by omega)]
    congr 2; ext; simp
  · rw [Matrix.sub_apply, conjTranspose_mul_mul_embedBlock_left hN hA _ ⟨hi1, hi2⟩ hj,
      leafUpdateMatrix_apply_of_not_coupling _ _ _ _ _ ⟨by omega, by omega⟩, hA₁ _ _ (by omega),
      hA _ _ (Or.inl ⟨hj, hi1⟩), sub_zero]
  · rw [Matrix.sub_apply, conjTranspose_mul_mul_embedBlock_bottom hN hA _ hi ⟨hj1, hj2⟩,
      leafUpdateMatrix_apply_of_not_coupling _ _ _ _ _ ⟨by omega, by omega⟩, hA₁ _ _ (by omega),
      hA _ _ (Or.inr ⟨hj2, hi⟩), sub_zero]
  · refine (specNorm_setRect_zero_le (by omega) (by omega) _).trans ?_
    refine (specNorm_matMulWord_conjTranspose_sub_le hM hu0 hu8 R₁ hV hεL hUb).trans ?_
    exact mul_le_mul_of_nonneg_left (hR₁ ▸ specNorm_subRect_le (by omega) (by omega) A)
      (add_nonneg (mul_nonneg (by positivity) (by linarith)) hεL)
  · refine (specNorm_setRect_zero_le (by omega) (by omega) _).trans ?_
    refine (specNorm_matMulWord_sub_mul_le hM hu0 hu8 T₁ hV hUb).trans ?_
    exact mul_le_mul_of_nonneg_left (hT₁ ▸ specNorm_subRect_le (by omega) (by omega) A)
      (add_nonneg (mul_nonneg (by positivity) (by linarith)) hεL)

/-- The leaf update as a tracked step: on a machine with the standard model at
$0 \le \boldsymbol{u} \le 1/8$, let $\mathbf{A}$ of order $n + 1$ be block upper triangular for
the three ranges around $[lo, lo + d)$ and let the leaf output $(\mathbf{U}_b, \mathbf{T}_b)$ be
tracked from $(\mathbf{I}, \mathbf{A}_{lo:lo+d})$ with errors $(\varepsilon_L, \beta)$,
$\varepsilon_L \ge 0$. Writing $\mathbf{T}_b$ into the block and updating the couplings and the
accumulator $\mathbf{U}$ with $\mathbf{U}_b$ is tracked from $(\mathbf{U}, \mathbf{A})$ with the
relative accumulator error $(1 + 24\boldsymbol{u})^{2d(d+2)}(1 + \varepsilon_L) - 1$ and the
backward error $\beta + (g d(1 + \varepsilon_L) + \varepsilon_L)\|\mathbf{A}\|_2$, $g$ the
growth of a stored product of inner dimension $d$. -/
theorem leafUpdate_isTrackedUnitarySimilar {Mch : Machine ℝ} {u : ℝ} (hM : StdModel u id Mch)
    (hu0 : 0 ≤ u) (hu8 : u ≤ 1 / 8) {lo d : ℕ} (hN : lo + d ≤ n + 1)
    {A U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : IsRangeBlockTriangular lo d A)
    {Ub Tb : Matrix (Fin d) (Fin d) ℂ} {εL β : ℝ} (hεL : 0 ≤ εL)
    (hleaf : IsTrackedUnitarySimilar εL β 1 (subBlock A (lo, d)) Ub Tb) :
    IsTrackedUnitarySimilar ((1 + 24 * u) ^ (2 * d * (d + 2)) * (1 + εL) - 1)
      (β + ((1 + (6 * u + 5 * u ^ 2)) ^ d * (5 * u + d * (6 * u + 5 * u ^ 2)) * d * (1 + εL) +
        εL) * specNorm A) U A (leafUpdateAccumulator Mch lo Ub U)
      (leafUpdateMatrix Mch lo Ub (setSubBlock A (lo, d) Tb)) := by
  obtain ⟨Wb, hWb, hUbW⟩ := hleaf
  have hUb : specNorm (Ub - Wb) ≤ εL := by
    rw [Matrix.one_mul] at hUbW
    exact hUbW.trans (mul_le_of_le_one_right hεL specNorm_one_le)
  set A₁ := setSubBlock A (lo, d) Tb
  set L := leafUpdateMatrix Mch lo Ub A₁
  have hA₁ : ∀ i j : Fin (n + 1), ¬((lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d) ∧
      (lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d)) → A₁ i j = A i j := fun i j h => by
    simp only [A₁, setSubBlock_apply]; rw [dif_neg (by tauto)]
  have hL : ∀ i j, _ → L i j = A₁ i j := fun i j h =>
    leafUpdateMatrix_apply_of_not_coupling Mch Ub A₁ i j h
  refine ⟨embedBlock lo Wb, ?_, ?_⟩
  · refine IsPerturbedUnitarySimilarBy.of_range_block hN hA (fun i j h => ?_) ?_
      (fun i j hi hj => by rw [hL i j ⟨by omega, by omega⟩, hA₁ _ _ (by omega)]) ?_
    · rw [hL i j ⟨by omega, by omega⟩, hA₁ _ _ (by omega), hA i j h]
    · have e : L.submatrix (rangeEmb hN) (rangeEmb hN) = Tb := by
        ext a b
        have ha := a.isLt
        have hb := b.isLt
        simp only [Matrix.submatrix_apply, rangeEmb]
        rw [hL _ _ ⟨by simp, by simp⟩]
        simp only [A₁, setSubBlock_apply]
        rw [dif_pos (by simp)]
        congr 1 <;> ext <;> simp
      rw [e, ← subBlock_eq_submatrix_rangeEmb hN]
      exact hWb
    · exact leafUpdate_couplingPart_le hM hu0 hu8 hN hA hWb.1 hεL hUb
  · exact specNorm_setRect_matMulWord_sub_le hM hu0 hu8 hN U hWb.1 hεL hUb

end LeafStep

section ShapeSteps

variable {n : ℕ}

/-- A matrix that agrees with $\mathbf{A}$ off the range $(lo, d)$ of a partition has the same
blocks on the other ranges. -/
theorem _root_.NLAlib.IsRangePartition.subBlock_eq_of_agree {L : List (ℕ × ℕ)}
    (hL : IsRangePartition (n + 1) L) {lo d : ℕ} (hr : (lo, d) ∈ L) {q : ℕ × ℕ} (hq : q ∈ L)
    (hne : q ≠ (lo, d)) {A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hag : ∀ i j : Fin (n + 1), ¬(lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d) →
      ¬(lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d) → A' i j = A i j) :
    subBlock A' q = subBlock A q := by
  have hd := hL.disjoint hq hr hne
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [subBlock, Matrix.submatrix_apply]
  apply hag <;> rw [hL.val_blockIndex hq] <;> simp only at hd <;> omega

/-- The block of the range $(lo, d)$ of a partition read from its entries. -/
theorem _root_.NLAlib.IsRangePartition.subBlock_eq_of_block {L : List (ℕ × ℕ)}
    (hL : IsRangePartition (n + 1) L) {lo d : ℕ} (hr : (lo, d) ∈ L)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : ∀ (a b : Fin d) (i j : Fin (n + 1)), (i : ℕ) = lo + a → (j : ℕ) = lo + b →
      A i j = B a b) : subBlock A (lo, d) = B := by
  ext a b
  exact hB a b _ _ (hL.val_blockIndex hr a) (hL.val_blockIndex hr b)

/-- The shape as a deflation invariant: a matrix of the shape that is a perturbed unitary
similarity of $\mathbf{H}$ with error $\varepsilon$ meets `NLAlib.DeflationInv` with its
diagonal as the output. -/
theorem SchurShape.deflationInv {active done : List (ℕ × ℕ)}
    {H A V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ε : ℝ} (h : SchurShape n active done A)
    (hV : IsPerturbedUnitarySimilarBy V H A ε) :
    DeflationInv H ε active done A fun i => A i i := by
  obtain ⟨hVo, E, hE, hA⟩ := hV
  refine ⟨A, V, E, hasOrthonormalCols_iff.mp hVo, hE, hA, h.1, fun i j hij => ?_,
    fun r hr => ⟨rfl, h.2.2.1 r hr⟩, fun r hr => ?_⟩
  · by_contra hne
    obtain ⟨ri, hri, hi⟩ := (h.1.2.2 i i.isLt).exists
    obtain ⟨rj, hrj, hj⟩ := (h.1.2.2 j j.isLt).exists
    rw [h.1.rangeLabel_eq hri hi.1 hi.2, h.1.rangeLabel_eq hrj hj.1 hj.2] at hij
    by_cases hji : (j : ℕ) < i
    · obtain ⟨q, hq, hq1, hq2⟩ := h.2.1 i j hji hne
      obtain ⟨c, -, hc⟩ := h.1.2.2 i i.isLt
      obtain ⟨c', -, hc'⟩ := h.1.2.2 j j.isLt
      have e1 := (hc q ⟨hq, by omega, hq2⟩).trans (hc ri ⟨hri, hi.1, hi.2⟩).symm
      have e2 := (hc' q ⟨hq, hq1, by omega⟩).trans (hc' rj ⟨hrj, hj.1, hj.2⟩).symm
      rw [← e1, ← e2] at hij
      exact lt_irrefl _ hij
    · have hne' : rj ≠ ri := fun e => by rw [e] at hij; exact lt_irrefl _ hij
      rcases h.1.disjoint hrj hri hne' with hd | hd <;> omega
  · have hr' : r ∈ active ++ done := List.mem_append_right _ hr
    rw [Matrix.charpoly_of_isUpperTriangular _ (h.2.2.2 r hr)]
    have e : (∏ a : Fin r.2, (Polynomial.X - Polynomial.C (subBlock A r a a))) =
        ((Finset.univ.val.map fun a => subBlock A r a a).map
          fun x => Polynomial.X - Polynomial.C x).prod := by
      rw [Multiset.map_map]; rfl
    rw [e, Polynomial.roots_multiset_prod_X_sub_C, Fin.univ_val_map]
    rfl

/-- A leaf finishes its range: writing an upper triangular block on the popped range and
updating its couplings moves the range from active to finished. -/
theorem SchurShape.leaf {rs done : List (ℕ × ℕ)} {lo d : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (h : SchurShape n (rs ++ [(lo, d)]) done A)
    (M : Machine ℝ) (Ub : Matrix (Fin d) (Fin d) ℂ) {Tb : Matrix (Fin d) (Fin d) ℂ}
    (hTb : Tb.IsUpperTriangular) :
    SchurShape n rs ((lo, d) :: done) (leafUpdateMatrix M lo Ub (setSubBlock A (lo, d) Tb)) := by
  have hL : rs ++ [(lo, d)] ++ done = rs ++ (lo, d) :: done := by simp
  have hp := h.1
  rw [hL] at hp
  have hr : (lo, d) ∈ rs ++ (lo, d) :: done := by simp
  have hrd := hp.2.1 _ hr
  simp only at hrd
  have hLe : ∀ i j : Fin (n + 1), (j : ℕ) < i →
      leafUpdateMatrix M lo Ub (setSubBlock A (lo, d) Tb) i j = setSubBlock A (lo, d) Tb i j :=
    fun i j hji => leafUpdateMatrix_apply_of_not_coupling M Ub _ i j ⟨by omega, by omega⟩
  have hag : ∀ i j : Fin (n + 1), ¬(lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d) →
      ¬(lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d) →
      leafUpdateMatrix M lo Ub (setSubBlock A (lo, d) Tb) i j = A i j := fun i j hi hj => by
    rw [leafUpdateMatrix_apply_of_not_coupling M Ub _ i j ⟨by omega, by omega⟩, setSubBlock_apply,
      dif_neg (by omega)]
  refine ⟨hp, fun i j hji hij => ?_, fun r hr' => ?_, fun r hr' => ?_⟩
  · rw [hLe i j hji, setSubBlock_apply] at hij
    split_ifs at hij with hb
    · exact ⟨(lo, d), hr, by simp; omega, by simp; omega⟩
    · obtain ⟨q, hq, h1, h2⟩ := h.2.1 i j hji hij
      exact ⟨q, by rw [hL] at hq; exact hq, h1, h2⟩
  · have hq : r ∈ rs ++ (lo, d) :: done := by simp [hr']
    have hne' : r ≠ (lo, d) := fun e => by
      have hnd := hp.1
      rw [List.nodup_append] at hnd
      exact hnd.2.2 r hr' (lo, d) (by simp) e
    rw [hp.subBlock_eq_of_agree hr hq hne' hag]
    exact h.2.2.1 r (by simp [hr'])
  · rcases List.mem_cons.mp hr' with rfl | hr'
    · rw [hp.subBlock_eq_of_block hr (B := Tb) fun a b i j hi hj => by
        rw [leafUpdateMatrix_apply_of_not_coupling M Ub _ i j ⟨by omega, by omega⟩,
          setSubBlock_apply, dif_pos (by omega)]
        congr 1 <;> ext <;> simp <;> omega]
      exact hTb
    · have hq : r ∈ rs ++ (lo, d) :: done := by simp [hr']
      have hne' : r ≠ (lo, d) := fun e => by
        have hnd := hp.1
        rw [List.nodup_append] at hnd
        exact (List.nodup_cons.mp hnd.2.1).1 (e ▸ hr')
      rw [hp.subBlock_eq_of_agree hr hq hne' hag]
      exact h.2.2.2 r hr'

/-- A cut splits its range: writing an upper Hessenberg block on the popped range
$(lo, d + 1)$, replaying its log on the couplings and cutting the entry $(lo + i + 1, lo + i)$
to the exact zero replaces the range by its two children, the right one pushed first. -/
theorem SchurShape.split {rs done : List (ℕ × ℕ)} {lo d : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (h : SchurShape n (rs ++ [(lo, d + 1)]) done A)
    {M : Machine ℝ} (hz : M.lit 0 = 0) {H' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hH' : IsUpperHessenberg H') {es : List GivensEntry} (hes : ∀ e ∈ es, e.1 + 1 < d + 1)
    (i : Fin d) :
    SchurShape n (rs ++ [(lo + i + 1, d + 1 - i - 1), (lo, i + 1)]) done
      (decoupleUpdateMatrix M lo (d + 1) i es (setSubBlock A (lo, d + 1) H')) := by
  have hi := i.isLt
  set c1 : ℕ × ℕ := (lo + i + 1, d + 1 - i - 1)
  set c2 : ℕ × ℕ := (lo, (i : ℕ) + 1)
  have hold := h.1
  have hnew : IsRangePartition (n + 1) (rs ++ [c1, c2] ++ done) := hold.split_append (by omega)
  have hr : (lo, d + 1) ∈ rs ++ [(lo, d + 1)] ++ done := by simp
  have hrd := hold.2.1 _ hr
  simp only at hrd
  set D' := decoupleUpdateMatrix M lo (d + 1) i es (setSubBlock A (lo, d + 1) H')
  have hD : ∀ r t : Fin (n + 1), ¬((r : ℕ) = lo + i + 1 ∧ (t : ℕ) = lo + i) →
      ¬((lo ≤ (r : ℕ) ∧ (r : ℕ) < lo + (d + 1)) ∧ lo + (d + 1) ≤ (t : ℕ)) →
      ¬((r : ℕ) < lo ∧ lo ≤ (t : ℕ) ∧ (t : ℕ) < lo + (d + 1)) →
      D' r t = setSubBlock A (lo, d + 1) H' r t := fun r t hc h1 h2 => by
    simp only [D', decoupleUpdateMatrix_eq, cutEntry, Matrix.of_apply]
    rw [if_neg hc, decoupleReplay_apply_of_not_coupling hes _ _ _ ⟨h1, h2⟩]
  have hcut : ∀ r t : Fin (n + 1), (r : ℕ) = lo + i + 1 → (t : ℕ) = lo + i → D' r t = 0 :=
    fun r t h1 h2 => by
      simp only [D', decoupleUpdateMatrix_eq, cutEntry, Matrix.of_apply]
      rw [if_pos ⟨h1, h2⟩, hz]; rfl
  have hag : ∀ r t : Fin (n + 1), ¬(lo ≤ (r : ℕ) ∧ (r : ℕ) < lo + (d + 1)) →
      ¬(lo ≤ (t : ℕ) ∧ (t : ℕ) < lo + (d + 1)) → D' r t = A r t := fun r t h1 h2 => by
    rw [hD r t (by omega) (by omega) (by omega), setSubBlock_apply, dif_neg (by omega)]
  have hmem : ∀ q ∈ rs ++ [(lo, d + 1)] ++ done, q ≠ (lo, d + 1) → q ∈ rs ++ [c1, c2] ++ done :=
    fun q hq hne => by simp only [List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hq ⊢; tauto
  have hHz : ∀ (r t : Fin (n + 1)) (a b : Fin (d + 1)), (r : ℕ) = lo + a → (t : ℕ) = lo + b →
      ¬((r : ℕ) = lo + i + 1 ∧ (t : ℕ) = lo + i) → (b : ℕ) + 1 < a → D' r t = 0 :=
    fun r t a b hr' ht' hc hab => by
      rw [hD r t hc (by omega) (by omega), setSubBlock_apply, dif_pos (by omega)]
      exact hH' _ _ (by simp only at *; omega)
  refine ⟨hnew, fun r t htr hne => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · by_cases hb : (lo ≤ (r : ℕ) ∧ (r : ℕ) < lo + (d + 1)) ∧
        (lo ≤ (t : ℕ) ∧ (t : ℕ) < lo + (d + 1))
    · have hc : ¬((r : ℕ) = lo + i + 1 ∧ (t : ℕ) = lo + i) := fun hc => hne (hcut r t hc.1 hc.2)
      have hrt : (r : ℕ) = t + 1 := by
        by_contra hrt
        exact hne (hHz r t ⟨r - lo, by omega⟩ ⟨t - lo, by omega⟩ (by simp; omega)
          (by simp; omega) hc (by simp; omega))
      by_cases ht : (t : ℕ) < lo + i
      · exact ⟨c2, by simp [c2], by simp [c2]; omega, by simp [c2]; omega⟩
      · exact ⟨c1, by simp [c1], by simp [c1]; omega, by simp [c1]; omega⟩
    · have hne' := hne
      rw [hD r t (by omega) (by omega) (by omega), setSubBlock_apply, dif_neg (by tauto)] at hne'
      obtain ⟨q, hq, h1, h2⟩ := h.2.1 r t htr hne'
      refine ⟨q, hmem q hq fun e => ?_, h1, h2⟩
      subst e; simp only at h1 h2; omega
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hq
    rcases hq with hq | rfl | rfl
    · have hq' : q ∈ rs ++ [(lo, d + 1)] ++ done := by simp [hq]
      have hne : q ≠ (lo, d + 1) := fun e => by
        have hnd := hold.1
        simp only [List.append_assoc, List.singleton_append] at hnd
        rw [List.nodup_append] at hnd
        exact hnd.2.2 q hq (lo, d + 1) (by simp) e
      rw [hold.subBlock_eq_of_agree hr hq' hne hag]
      exact h.2.2.1 q (by simp [hq])
    · intro a b hab
      rw [hnew.subBlock_apply (by simp [c1]) D' a b]
      have ha := a.isLt; have hb := b.isLt
      simp only [c1] at ha hb
      exact hHz _ _ ⟨i + 1 + a, by omega⟩ ⟨i + 1 + b, by omega⟩ (by simp [c1]; omega)
        (by simp [c1]; omega) (by simp [c1]; omega) (by simp; omega)
    · intro a b hab
      rw [hnew.subBlock_apply (by simp [c2]) D' a b]
      have ha := a.isLt; have hb := b.isLt
      simp only [c2] at ha hb
      exact hHz _ _ ⟨a, by omega⟩ ⟨b, by omega⟩ (by simp [c2]) (by simp [c2])
        (by simp [c2]; omega) (by simpa using hab)
  · have hq' : q ∈ rs ++ [(lo, d + 1)] ++ done := by simp [hq]
    have hne : q ≠ (lo, d + 1) := fun e => by
      have hnd := hold.1
      rw [List.nodup_append] at hnd
      exact hnd.2.2 (lo, d + 1) (by simp) q hq e.symm
    rw [hold.subBlock_eq_of_agree hr hq' hne hag]
    exact h.2.2.2 q hq

end ShapeSteps

end ShiftedQR

end NLAlib
