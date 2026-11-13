/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Subspaces.Frames
public import NLAlib.Matrix.Pseudoinverse.Pinv
public import NLAlib.Matrix.Subspaces.ProjectorPair

/-!
# Unitary canonical form of an idempotent

An orthonormal basis in the range and its orthogonal complement splits an idempotent into
oblique planes and scalar identity and zero blocks. Its singular values give the entries of
the oblique planes, over either the real or the complex field.

## Main results

* `IsIdempotentElem.one_le_singularValues`: the positive singular values are at least one.
* `IsIdempotentElem.exists_conjTranspose_mul_mul_eq_fromBlocks`: a basis for the canonical form.
* `IsIdempotentElem.exists_fromBlocks_of_rank_add_eq`: the form with its number of oblique planes.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

private theorem gram_mul_add_gram_mul {r s : ℕ} (A : Matrix (Fin r) n 𝕜)
    {U : Matrix n (Fin r) 𝕜} {Q : Matrix n (Fin s) 𝕜}
    (h : HasOrthonormalCols (Matrix.fromCols U Q)) (hc : r + s = Fintype.card n)
    (hAU : A * U = 1) :
    (A * Q) * (A * Q)ᴴ + 1 = A * Aᴴ := by
  classical
  have he := h.mul_conjTranspose_add_mul_conjTranspose (by simpa using hc)
  have gram {p : ℕ} (B : Matrix n (Fin p) 𝕜) :
      A * (B * Bᴴ) * Aᴴ = (A * B) * (A * B)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hm := congrArg (fun M => A * M * Aᴴ) he
  simpa only [Matrix.mul_add, Matrix.add_mul, gram, hAU, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one, add_comm] using hm

private theorem exists_frames (P : Matrix n n 𝕜) (hP : IsIdempotentElem P) {s : ℕ}
    (hc : P.rank + s = Fintype.card n) :
    ∃ (U : Matrix n (Fin P.rank) 𝕜) (Q : Matrix n (Fin s) 𝕜),
      HasOrthonormalCols (Matrix.fromCols U Q) ∧ Uᴴ * P * U = 1 ∧ Qᴴ * P = 0 ∧
      (Uᴴ * P * Q) * (Uᴴ * P * Q)ᴴ + 1 =
        Matrix.diagonal (fun i : Fin P.rank => ((singularValues P i ^ 2 : ℝ) : 𝕜)) := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD P le_rfl P.rank_le_card_height P.rank_le_card_width
  obtain ⟨Q, hQ⟩ := h.hasOrthonormalCols_left.exists_fromCols (p := Fin s) (by simpa using hc)
  have hR : rangeProjector P = U * Uᴴ := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      h.conjTranspose.rangeProjector_conjTranspose_eq (fun i => (singularValues_pos_iff P).2 i.isLt)
  have hfix : P * rangeProjector P = rangeProjector P := by
    rw [← mul_pinv, ← Matrix.mul_assoc, hP.eq]
  have hPU : P * U = U := by
    have he := congrArg (fun M => M * U) hfix
    simpa only [hR, Matrix.mul_assoc, h.hasOrthonormalCols_left.conjTranspose_mul_self,
      Matrix.mul_one] using he
  have hAU : Uᴴ * P * U = 1 := by
    rw [Matrix.mul_assoc, hPU, h.hasOrthonormalCols_left.conjTranspose_mul_self]
  have hQU : Qᴴ * U = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using
      congrArg Matrix.conjTranspose (hasOrthonormalCols_fromCols_iff.mp hQ).2.2
  refine ⟨U, Q, hQ, hAU, ?_, ?_⟩
  · rw [h.eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQU, Matrix.zero_mul, Matrix.zero_mul]
  · rw [gram_mul_add_gram_mul _ hQ hc hAU, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc Uᴴ, ← Matrix.mul_assoc P,
      h.mul_conjTranspose_self_eq, h.hasOrthonormalCols_left.mul_conjTranspose_mul_cancel_right,
      h.hasOrthonormalCols_left.conjTranspose_mul_cancel_left]

private def planeCoeffs {r s : ℕ} (t : ℕ → ℝ) : Matrix (Fin r) (Fin s) 𝕜 :=
  Matrix.of fun i j => if i.val = j.val then ((t i : ℝ) : 𝕜) else 0

private theorem planeCoeffs_gram {r s : ℕ} (t : ℕ → ℝ) (hz : ∀ k, s ≤ k → t k = 0) :
    (planeCoeffs t : Matrix (Fin r) (Fin s) 𝕜) * (planeCoeffs t)ᴴ =
      Matrix.diagonal (fun i : Fin r => ((t i ^ 2 : ℝ) : 𝕜)) := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i.val < s
  · let k : Fin s := ⟨i.val, hi⟩
    rw [Finset.sum_eq_single k]
    · by_cases hij : i = j
      · subst j
        simp [planeCoeffs, k, sq]
      · have hji : j.val ≠ i.val := fun he => hij (Fin.ext he.symm)
        simp [planeCoeffs, k, hji, Matrix.diagonal_apply_ne _ hij]
    · intro l _ hl
      have hil : i.val ≠ l.val := fun he => hl (Fin.ext he.symm)
      simp [planeCoeffs, hil]
    · simp
  · have hi0 := hz i (Nat.le_of_not_gt hi)
    simp [planeCoeffs, hi0, Matrix.diagonal_apply, apply_ite]

private theorem exists_rotation {r s : ℕ} (T : Matrix (Fin r) (Fin s) 𝕜) (σ : ℕ → ℝ)
    (hσ : Antitone σ) (hσ0 : ∀ i, 0 ≤ σ i)
    (h : T * Tᴴ + 1 = Matrix.diagonal (fun i : Fin r => ((σ i ^ 2 : ℝ) : 𝕜))) :
    ∃ W : Matrix (Fin s) (Fin s) 𝕜, HasOrthonormalCols W ∧
      T * W = planeCoeffs (fun i => Real.sqrt (σ i ^ 2 - 1)) ∧
      ∀ i : Fin r, σ i ^ 2 = singularValues T i ^ 2 + 1 := by
  classical
  have hd : Antitone fun i : Fin r => σ i ^ 2 := fun i j hij =>
    pow_le_pow_left₀ (hσ0 j) (hσ hij) 2
  have hσT (i : Fin r) : σ i ^ 2 = singularValues T i ^ 2 + 1 := by
    rw [← eigenvalue_diagonal (𝕜 := 𝕜) hd i, ← h,
      singularValues_sq_eq_eigenvalue_mul_conjTranspose_self]
    simpa only [one_smul] using
      (Matrix.isHermitian_mul_conjTranspose_self T).eigenvalue_add_smul_one 1 (by simp)
  let D : Matrix (Fin r) (Fin s) 𝕜 := planeCoeffs (singularValues T)
  have hgram : T * Tᴴ = D * Dᴴ := by
    rw [eq_sub_of_add_eq h, planeCoeffs_gram _ (fun k hk => singularValues_of_card_cols_le T
      (by simpa using hk))]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
        hσT, RCLike.ofReal_add, RCLike.ofReal_one, add_sub_cancel_right]
    · simp [Matrix.sub_apply, hij]
  obtain ⟨W, hW, he⟩ := (conjTranspose_mul_self_eq_iff_exists_mul (A := Tᴴ) (B := Dᴴ)
    le_rfl).mp (by simpa only [Matrix.conjTranspose_conjTranspose] using hgram)
  refine ⟨W, hW, ?_, hσT⟩
  have ht : T = D * Wᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose he
  rw [ht, hW.mul_conjTranspose_mul_cancel_right]
  ext i j
  simp only [D, planeCoeffs, Matrix.of_apply, hσT, add_sub_cancel_right,
    Real.sqrt_sq (singularValues_nonneg T i)]

/-- Every positive singular value of an idempotent matrix is at least one.
[HornJohnson2013, Corollary 3.4.3.3]. -/
theorem _root_.IsIdempotentElem.one_le_singularValues {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {i : ℕ} (hi : i < P.rank) : 1 ≤ singularValues P i := by
  classical
  have hR := isStarProjection_rangeProjector P
  have hfix : P * rangeProjector P = rangeProjector P := by
    rw [← mul_pinv, ← Matrix.mul_assoc, hP.eq]
  calc
    1 = singularValues (rangeProjector P) i :=
      (hR.singularValues_of_lt_rank (by rwa [rank_rangeProjector])).symm
    _ = singularValues (P * rangeProjector P) i := by rw [hfix]
    _ ≤ singularValues P i * specNorm (rangeProjector P) := singularValues_mul_le_mul_specNorm _ _ _
    _ ≤ singularValues P i := mul_le_of_le_one_right (singularValues_nonneg P i) hR.specNorm_le_one

/-- **Unitary canonical form of an idempotent.** For an idempotent $\mathbf{P}$ of rank $r$ and
nullity $s$, there is an orthonormal basis in which $\mathbf{P}$ consists of $g$ oblique planes
with blocks
$$\begin{bmatrix}1 & \sqrt{\sigma_i(\mathbf{P})^2-1} \\ 0 & 0\end{bmatrix},$$
and scalar identity and zero blocks. Exactly the first $g$ singular values exceed one, and each
positive singular value is at least one. This includes empty matrices and ranks zero and full.
[HornJohnson2013, Corollary 3.4.3.3]. -/
theorem _root_.IsIdempotentElem.exists_fromBlocks_of_rank_add_eq {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {s : ℕ} (hc : P.rank + s = Fintype.card n) :
    ∃ g ≤ min P.rank s, (∀ i, 1 < singularValues P i ↔ i < g) ∧
      (∀ i < P.rank, 1 ≤ singularValues P i) ∧
      ∃ H : Matrix n (Fin P.rank ⊕ Fin s) 𝕜, HasOrthonormalCols H ∧
        Hᴴ * P * H = Matrix.fromBlocks 1
          (Matrix.of fun (i : Fin P.rank) (j : Fin s) =>
            if i.val = j.val then ((Real.sqrt (singularValues P i ^ 2 - 1) : ℝ) : 𝕜) else 0)
          0 0 := by
  classical
  obtain ⟨U, Q, hH, hU, hQ, hG⟩ := exists_frames P hP hc
  let T := Uᴴ * P * Q
  obtain ⟨W, hW, hTW, hσ⟩ := exists_rotation T (singularValues P) (singularValues_antitone P)
    (singularValues_nonneg P) hG
  have hr : T.rank ≤ min P.rank s := le_min (by simpa [T] using T.rank_le_card_height)
    (by simpa using T.rank_le_card_width)
  refine ⟨T.rank, hr, ?_, fun _ hi => hP.one_le_singularValues hi,
    Matrix.fromCols U (Q * W), ?_, ?_⟩
  · intro i
    by_cases hi : i < P.rank
    · have hs := hσ ⟨i, hi⟩
      change singularValues P i ^ 2 = singularValues T i ^ 2 + 1 at hs
      rw [← singularValues_pos_iff T]
      constructor <;> intro hlt <;>
        nlinarith [singularValues_nonneg T i, singularValues_nonneg P i]
    · rw [(singularValues_eq_zero_iff P).mpr (Nat.le_of_not_gt hi)]
      have := hr.trans (min_le_left _ _)
      simp only [not_lt.mpr (by omega : T.rank ≤ i), iff_false]
      norm_num
  · obtain ⟨h₁, h₂, h₁₂⟩ := hasOrthonormalCols_fromCols_iff.mp hH
    exact hasOrthonormalCols_fromCols_iff.mpr ⟨h₁, h₂.mul hW, by
      rw [← Matrix.mul_assoc, h₁₂, Matrix.zero_mul]⟩
  · rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols, Matrix.conjTranspose_mul, Matrix.mul_assoc Wᴴ Qᴴ,
      hQ, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, hU,
      ← Matrix.mul_assoc (Uᴴ * P) Q W, hTW]
    rfl

/-- **Unitary canonical form of an idempotent.** In an orthonormal basis of the range and its
orthogonal complement, the diagonal blocks are the identity and zero. The rectangular upper-right
block is diagonal with entries $\sqrt{\sigma_i(\mathbf{P})^2-1}$.
[HornJohnson2013, Corollary 3.4.3.3].
Result: oblique-projector-canonical-form -/
theorem _root_.IsIdempotentElem.exists_conjTranspose_mul_mul_eq_fromBlocks {P : Matrix n n 𝕜}
    (hP : IsIdempotentElem P) {s : ℕ} (hc : P.rank + s = Fintype.card n) :
    ∃ H : Matrix n (Fin P.rank ⊕ Fin s) 𝕜, HasOrthonormalCols H ∧
      Hᴴ * P * H = Matrix.fromBlocks 1
        (Matrix.of fun (i : Fin P.rank) (j : Fin s) =>
          if i.val = j.val then ((Real.sqrt (singularValues P i ^ 2 - 1) : ℝ) : 𝕜) else 0)
        0 0 := by
  obtain ⟨_, _, _, _, h⟩ := hP.exists_fromBlocks_of_rank_add_eq hc
  exact h

end NLAlib
