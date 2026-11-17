/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Diagonalizable
public import NLAlib.Matrix.Spectral.SingularValueInequalities

/-!
# Eigenvalue clusters and small singular values

Two eigenvalues of a diagonalized matrix close to a shift force its second-smallest shifted
singular value to be small, with the loss given by the diagonalizer condition number.

## Main results

* `NLAlib.singularValues_le_mul_pseudoConditionNumber_of_mul_eq_mul_diagonal`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Two eigenvalues in a disk force a small second singular value.** If a diagonalizer has
two distinct columns whose eigenvalues are within $r\ge0$ of $z$, then the second-smallest
singular value of $z\mathbf{I}-\mathbf{A}$ is at most $r$ times its condition number.
[BanksGarzaVargasKulkarniSrivastava2023, Lemma 3.5], with the same argument over `RCLike`. -/
theorem singularValues_le_mul_pseudoConditionNumber_of_mul_eq_mul_diagonal
    {𝕜 : Type*} [RCLike 𝕜] {A V : Matrix n n 𝕜} {d : n → 𝕜} (hV : IsUnit V)
    (hAV : A * V = V * Matrix.diagonal d) {k : ℕ} (hk : k + 2 = Fintype.card n)
    {i j : n} (hij : i ≠ j) (z : 𝕜) {r : ℝ} (hr : 0 ≤ r)
    (hi : ‖z - d i‖ ≤ r) (hj : ‖z - d j‖ ≤ r) :
    singularValues (z • 1 - A) k ≤ r * pseudoConditionNumber V := by
  classical
  let e : n → 𝕜 := fun l => if l = i ∨ l = j then 0 else z - d l
  let f : n → 𝕜 := fun l => if l = i ∨ l = j then z - d l else 0
  let T := V * Matrix.diagonal e * V⁻¹
  have he : (Matrix.diagonal e).rank ≤ k := by
    rw [Matrix.rank_diagonal, Fintype.card_subtype]
    have hs : (Finset.univ.filter fun l => e l ≠ 0) ⊆ Finset.univ \ {i,j} := by
      intro l hl
      have hzero : ¬ (l = i ∨ l = j) := by
        intro h
        exact (Finset.mem_filter.mp hl).2 (by simp only [e, if_pos h])
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hzero⟩
    have hc : (Finset.univ \ {i,j}).card = k := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      rw [Finset.card_univ, Finset.card_pair_eq_two_iff.mpr hij]
      omega
    exact (Finset.card_le_card hs).trans_eq hc
  have hT : T.rank ≤ k := (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_right _ _).trans he)
  have hA : A = V * Matrix.diagonal d * V⁻¹ := by
    rw [← hAV, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hV),
      Matrix.mul_one]
  have hconst : Matrix.diagonal (fun _ : n => z) = z • (1 : Matrix n n 𝕜) := by
    ext a b
    by_cases hab : a = b <;> simp [Matrix.smul_apply, hab]
  have hId : z • (1 : Matrix n n 𝕜) = V * Matrix.diagonal (fun _ => z) * V⁻¹ := by
    rw [hconst, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hV)]
  have hres : z • 1 - A - T = V * Matrix.diagonal f * V⁻¹ := by
    rw [hId, hA]
    change _ - _ - (V * Matrix.diagonal e * V⁻¹) = _
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub,
      ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
    apply congrArg (fun v : n → 𝕜 => V * Matrix.diagonal v * V⁻¹)
    funext l
    change z - d l - (if l = i ∨ l = j then 0 else z - d l) =
      (if l = i ∨ l = j then z - d l else 0)
    split_ifs <;> simp
  have hf : specNorm (Matrix.diagonal f) ≤ r := specNorm_diagonal_le hr (fun l => by
    dsimp [f]
    split_ifs with h
    · rcases h with rfl | rfl
      · exact hi
      · exact hj
    · simpa using hr)
  calc singularValues (z • 1 - A) k ≤ specNorm (z • 1 - A - T) :=
      by simpa only [Nat.add_zero, singularValues_zero_eq_specNorm] using
        singularValues_add_le_singularValues_sub_of_rank_le (z • 1 - A) hT 0
    _ ≤ specNorm V * r * specNorm V⁻¹ := by
      rw [hres]
      exact (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hf (specNorm_nonneg V)))
        (specNorm_nonneg _))
    _ = _ := by rw [pseudoConditionNumber_of_isUnit hV]; ring

/-- A net of a spectral disk detects a close eigenvalue pair whenever a diagonalizer has
condition number at most $B$. Two net-near eigenvalues give a second singular value at most
$2rB$. This is the deterministic net step of
[BanksGarzaVargasKulkarniSrivastava2023, proof of Theorem 3.6]. -/
theorem exists_mem_singularValues_le_of_not_exists_isEigenvalueListing
    {𝕜 : Type*} [RCLike 𝕜] {A V : Matrix n n 𝕜} {d : n → 𝕜}
    (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d)
    {k : ℕ} (hk : k + 2 = Fintype.card n) {r R B : ℝ} (hr : 0 < r)
    (hR : specNorm A < R) (hB : pseudoConditionNumber V ≤ B)
    (Z : Finset 𝕜) (hZ : ∀ z : 𝕜, ‖z‖ ≤ R → ∃ y ∈ Z, ‖z - y‖ ≤ r / 2)
    (hbad : ¬ ∃ e : n → 𝕜, IsEigenvalueListing A e ∧
      ∀ i j, i ≠ j → r < ‖e i - e j‖) :
    ∃ y ∈ Z, singularValues (y • 1 - A) k ≤ 2 * r * B := by
  classical
  have hd := isEigenvalueListing_of_mul_eq_mul_diagonal
    ((Matrix.isUnit_iff_isUnit_det _).mp hV) hAV
  have hclose : ¬ ∀ i j, i ≠ j → r < ‖d i - d j‖ := fun h => hbad ⟨d, hd, h⟩
  push Not at hclose
  obtain ⟨i, j, hij, hdij⟩ := hclose
  obtain ⟨y, hy, hiy⟩ := hZ (d i)
    ((norm_le_specNorm_of_mul_eq_mul_diagonal hV hAV i).trans hR.le)
  have hyi : ‖y - d i‖ ≤ 2 * r := by rw [norm_sub_rev]; linarith
  have hyj : ‖y - d j‖ ≤ 2 * r := by
    have hh := norm_sub_le_norm_sub_add_norm_sub y (d i) (d j)
    rw [norm_sub_rev y (d i)] at hh
    linarith
  exact ⟨y, hy, (singularValues_le_mul_pseudoConditionNumber_of_mul_eq_mul_diagonal
    hV hAV hk hij y (by positivity) hyi hyj).trans
      (mul_le_mul_of_nonneg_left hB (by positivity))⟩

end NLAlib
