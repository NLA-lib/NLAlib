/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.UnitarilyInvariant
public import NLAlib.Matrix.Subspaces.Frames

/-!
# Representing a fixed-shape unitarily invariant norm

A norm supplied on a fixed rectangular matrix space is determined by its values on real diagonal
matrices between two orthonormal frames. This restriction is invariant under permutations and
signs. It extends to a symmetric gauge on finitely supported sequences, which represents the
original norm at every matrix of that shape.

## Main results

* `NLAlib.IsUnitarilyInvariant.exists_forall_matrixNorm_eq`: the symmetric gauge representation.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 m n r : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq r]

namespace IsUnitarilyInvariant

/-- Changing the two orthonormal frames of a rectangular compression preserves an invariant
function, because each change of frame extends to a square unitary. -/
theorem apply_mul_mul_conjTranspose_eq {f : Matrix m n 𝕜 → ℝ} (hf : IsUnitarilyInvariant f)
    {U U' : Matrix m r 𝕜} {V V' : Matrix n r 𝕜} (hU : HasOrthonormalCols U)
    (hU' : HasOrthonormalCols U') (hV : HasOrthonormalCols V) (hV' : HasOrthonormalCols V')
    (D : Matrix r r 𝕜) : f (U * D * Vᴴ) = f (U' * D * V'ᴴ) := by
  obtain ⟨P, hP, rfl⟩ := (conjTranspose_mul_self_eq_iff_exists_mul le_rfl).mp
    (hU.conjTranspose_mul_self.trans hU'.conjTranspose_mul_self.symm)
  obtain ⟨Q, hQ, rfl⟩ := (conjTranspose_mul_self_eq_iff_exists_mul le_rfl).mp
    (hV.conjTranspose_mul_self.trans hV'.conjTranspose_mul_self.symm)
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using hf P hP Q hQ (U' * D * V'ᴴ)

end IsUnitarilyInvariant

/-- Insert real coefficients into a pair of thin orthonormal frames. -/
private noncomputable def frameDiagonal (U : Matrix m r 𝕜) (V : Matrix n r 𝕜) :
    (r → ℝ) →ₗ[ℝ] Matrix m n 𝕜 where
  toFun x := U * Matrix.diagonal (fun i => ((x i : ℝ) : 𝕜)) * Vᴴ
  map_add' x y := by
    simp only [Pi.add_apply, RCLike.ofReal_add, ← Matrix.diagonal_add, Matrix.mul_add,
      Matrix.add_mul]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have h : (fun i => ((c * x i : ℝ) : 𝕜)) = c • (fun i => ((x i : ℝ) : 𝕜)) := by
      ext i
      simp [RCLike.real_smul_eq_coe_mul]
    rw [h, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq m] [DecidableEq n] in
private theorem frameDiagonal_eq_zero {U : Matrix m r 𝕜} {V : Matrix n r 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) {x : r → ℝ}
    (hx : frameDiagonal U V x = 0) : x = 0 := by
  change U * Matrix.diagonal (fun i => ((x i : ℝ) : 𝕜)) * Vᴴ = (0 : Matrix m n 𝕜) at hx
  have h := congrArg (fun M => Uᴴ * M * V) hx
  simp only [Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.mul_one,
    hU.conjTranspose_mul_cancel_left, Matrix.mul_zero, Matrix.zero_mul] at h
  ext i
  have hi := congrFun (congrFun h i) i
  simpa using hi

private theorem apply_frameDiagonal_comp_perm {f : Matrix m n 𝕜 → ℝ} (hf : IsUnitarilyInvariant f)
    {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (σ : Equiv.Perm r) (x : r → ℝ) :
    f (frameDiagonal U V (x ∘ σ)) = f (frameDiagonal U V x) := by
  let D := Matrix.diagonal (fun i => ((x (σ i) : ℝ) : 𝕜))
  calc
    _ = f (U.submatrix (Equiv.refl m) σ * D * (V.submatrix (Equiv.refl n) σ)ᴴ) :=
      hf.apply_mul_mul_conjTranspose_eq hU (hU.submatrix _ σ.injective)
        hV (hV.submatrix _ σ.injective) D
    _ = _ := by
      have hd : D = (Matrix.diagonal fun i => ((x i : ℝ) : 𝕜)).submatrix σ σ :=
        (Matrix.submatrix_diagonal_equiv (fun i => ((x i : ℝ) : 𝕜)) σ).symm
      rw [hd, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
        Matrix.submatrix_mul_equiv]
      rfl

private theorem apply_frameDiagonal_abs {f : Matrix m n 𝕜 → ℝ} (hf : IsUnitarilyInvariant f)
    {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} (hU : HasOrthonormalCols U) (x : r → ℝ) :
    f (frameDiagonal U V (fun i => |x i|)) = f (frameDiagonal U V x) := by
  have hGram : (frameDiagonal U V (fun i => |x i|))ᴴ * frameDiagonal U V (fun i => |x i|) =
      (frameDiagonal U V x)ᴴ * frameDiagonal U V x := by
    change (U * Matrix.diagonal _ * Vᴴ)ᴴ * (U * Matrix.diagonal _ * Vᴴ) =
      (U * Matrix.diagonal _ * Vᴴ)ᴴ * (U * Matrix.diagonal _ * Vᴴ)
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      hU.conjTranspose_mul_cancel_left, Matrix.conjTranspose_diagonal_ofReal]
    congr 1
    simp only [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, ← RCLike.ofReal_mul,
      abs_mul_abs_self]
  obtain ⟨P, hP, h⟩ := (conjTranspose_mul_self_eq_iff_exists_mul le_rfl).mp hGram
  rw [h]
  simpa only [Matrix.conjTranspose_one, Matrix.mul_one] using
    hf P hP 1 hasOrthonormalCols_one (frameDiagonal U V x)

/-- **Von Neumann's symmetric gauge representation.** Let $p$ be a definite seminorm on a
fixed real or complex rectangular matrix space, invariant under arbitrary unitary factors on
the left and right. A single symmetric gauge $\Phi$ on finitely supported sequences satisfies
$\|\mathbf{A}\|_{\Phi}=p(\mathbf{A})$ for every matrix of that shape. If either index type
is empty, every input is zero. This extends the normalized square complex case of
[Bhatia1997, Theorem IV.2.1] to arbitrary norm scalings and rectangular shapes.
Result: unitarily-invariant-norm -/
theorem IsUnitarilyInvariant.exists_forall_matrixNorm_eq {p : Seminorm 𝕜 (Matrix m n 𝕜)}
    (hp : IsUnitarilyInvariant (p : Matrix m n 𝕜 → ℝ)) (hdef : ∀ A, p A = 0 → A = 0) :
    ∃ Φ : SymmetricGauge, ∀ A : Matrix m n 𝕜, Φ.matrixNorm A = p A := by
  classical
  let d := min (Fintype.card m) (Fintype.card n)
  obtain hd | hd := Nat.eq_zero_or_pos d
  · refine ⟨kyFanGauge 1 one_ne_zero, fun A => ?_⟩
    have hr : A.rank ≤ d := le_min A.rank_le_card_height A.rank_le_card_width
    have hA := Matrix.rank_eq_zero.mp (le_zero_iff.mp (hd ▸ hr))
    rw [hA, SymmetricGauge.matrixNorm_zero, map_zero]
  obtain ⟨U, hU⟩ := exists_hasOrthonormalCols_of_card_le (n := m) (p := Fin d) 𝕜
    (by rw [Fintype.card_fin]; exact min_le_left _ _)
  obtain ⟨V, hV⟩ := exists_hasOrthonormalCols_of_card_le (n := n) (p := Fin d) 𝕜
    (by rw [Fintype.card_fin]; exact min_le_right _ _)
  let q := (p.restrictScalars ℝ).comp (frameDiagonal U V)
  obtain ⟨Φ, hΦ⟩ := SymmetricGauge.exists_eq_restrict hd q
    (fun x hx => frameDiagonal_eq_zero hU hV (hdef _ hx))
    (apply_frameDiagonal_comp_perm hp hU hV) (apply_frameDiagonal_abs hp hU)
  refine ⟨Φ, fun A => ?_⟩
  have hs := isSVD_svdU_svdV A
  have hr : A.rank ≤ d := le_min A.rank_le_card_height A.rank_le_card_width
  rw [SymmetricGauge.matrixNorm_def, hΦ (singularValuesFinsupp A) fun i hi =>
    (singularValues_eq_zero_iff A).mpr (hr.trans hi)]
  exact (hp.apply_mul_mul_conjTranspose_eq hU hs.hasOrthonormalCols_left hV
    hs.hasOrthonormalCols_right _).trans (congrArg p hs.eq.symm)

end NLAlib
