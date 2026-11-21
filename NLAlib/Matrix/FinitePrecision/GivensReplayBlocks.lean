/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.GivensReplay
public import NLAlib.Matrix.FinitePrecision.StoredBlocks

/-!
# Givens replays and embedded blocks on a range

Facts about matrices that act on one range $[lo, lo + d)$ of the indices: the block embedding
$\operatorname{diag}(\mathbf{I}, \mathbf{V}, \mathbf{I})$ (`NLAlib.embedBlock`), the row and column
masks (`NLAlib.colMask`), the replay steps of a Givens log on a range of rows or columns
(`NLAlib.replayRowStep`, `NLAlib.replayColumnStep`), the couplings of a range block
(`NLAlib.couplingPart`) and rectangular blocks (`NLAlib.subRect`, `NLAlib.setRect`). Matrices
supported on disjoint rows and columns have norm the larger of the two
(`NLAlib.specNorm_add_le_max_of_support`).

## Main results

* `NLAlib.specNorm_add_le_max_of_support`, `NLAlib.specNorm_couplingPart_le_max`: matrices
  supported on disjoint rows and columns.
* `NLAlib.embedBlock_mul_apply_of_mem`, `NLAlib.conjTranspose_mul_mul_embedBlock_left`,
  `NLAlib.conjTranspose_mul_mul_embedBlock_bottom`: the entries of a range step.
* `NLAlib.colMask_mul_foldl_replayColumnStep`, `NLAlib.foldl_replayRowStep_apply_row`: the
  replay steps on a range.
* `NLAlib.specNorm_setRect_zero_le`, `NLAlib.specNorm_subRect_le`: rectangular blocks.
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

end NLAlib
