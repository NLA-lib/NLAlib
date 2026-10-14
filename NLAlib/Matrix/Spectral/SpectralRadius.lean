/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import NLAlib.Matrix.Spectral.Normal
public import NLAlib.Matrix.Spectral.Gershgorin

/-!
# The spectral radius of a matrix

The spectral radius of a square matrix over `𝕜` is the largest modulus of a complex eigenvalue,
`NLAlib.specRadius A`, defined through Mathlib's `spectralRadius` of the complexification. It is
at most the spectral norm, with equality for normal matrices; it is invariant under similarity;
it is at most the largest row sum; and it is sub-additive and sub-multiplicative on commuting
matrices. The powers of a matrix are in `NLAlib.Matrix.Spectral.PowerBounds`.

## Main definitions

* `NLAlib.specRadius`: the spectral radius, a real number.

## Main results

* `NLAlib.specRadius_le_iff_of_charpoly_eq`: the spectral radius through an eigenvalue listing.
* `NLAlib.specRadius_le_specNorm`, `IsStarNormal.specNorm_eq_specRadius`.
* `NLAlib.specRadius_inv_mul_mul`, `NLAlib.specRadius_mul_comm`.
* `NLAlib.specRadius_add_le_of_commute`, `NLAlib.specRadius_mul_le_of_commute`.
* `NLAlib.specRadius_one_sub_inv_diagonal_mul_lt_one`: convergence of the Jacobi iteration.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial Filter Topology

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **spectral radius** of a square matrix: the largest modulus of a complex eigenvalue, zero
for a matrix of size zero. [HornJohnson2013, Definition 1.2.9]. -/
noncomputable def specRadius (A : Matrix n n 𝕜) : ℝ :=
  (spectralRadius ℂ (complexify A)).toReal

/-- The spectral radius is nonnegative. -/
theorem specRadius_nonneg (A : Matrix n n 𝕜) : 0 ≤ specRadius A :=
  ENNReal.toReal_nonneg

omit [Fintype n] [DecidableEq n] in
private theorem complexify_complex (A : Matrix n n ℂ) : complexify A = A := by
  ext i j
  rw [complexify_apply, RCLike.toComplex_complex]

private theorem spectralRadius_complexify_eq_iSup {A : Matrix n n 𝕜} {d : n → ℂ}
    (hd : IsEigenvalueListing (complexify A) d) :
    spectralRadius ℂ (complexify A) = ⨆ i, (‖d i‖₊ : ENNReal) := by
  rw [spectralRadius, hd.spectrum_eq_range]
  exact iSup_range

/-- The spectral radius of the complexification, as an extended nonnegative real, is finite:
the bridge from Mathlib's `spectralRadius` to `specRadius`. -/
theorem spectralRadius_complexify_ne_top (A : Matrix n n 𝕜) :
    spectralRadius ℂ (complexify A) ≠ ⊤ := by
  obtain ⟨d, hd⟩ := exists_isEigenvalueListing (complexify A)
  rw [spectralRadius_complexify_eq_iSup hd]
  refine ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := Finset.univ.sup fun i => ‖d i‖₊)) ?_
  exact iSup_le fun i => ENNReal.coe_le_coe.mpr (Finset.le_sup (f := fun i => ‖d i‖₊)
    (Finset.mem_univ i))

private theorem charpoly_complexify (A : Matrix n n 𝕜) :
    (complexify A).charpoly = A.charpoly.map (RCLike.toComplex : 𝕜 →⋆ₐ[ℝ] ℂ).toRingHom :=
  Matrix.charpoly_map A (RCLike.toComplex : 𝕜 →⋆ₐ[ℝ] ℂ).toRingHom

private theorem specRadius_eq_of_charpoly_eq {A B : Matrix n n 𝕜}
    (h : A.charpoly = B.charpoly) : specRadius A = specRadius B := by
  have hs : spectrum ℂ (complexify A) = spectrum ℂ (complexify B) := by
    ext μ
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.mem_spectrum_iff_isRoot_charpoly,
      charpoly_complexify, charpoly_complexify, h]
  rw [specRadius, specRadius, spectralRadius, spectralRadius, hs]

private theorem toComplex_mem_spectrum_complexify {A : Matrix n n 𝕜} {μ : 𝕜}
    (hμ : μ ∈ spectrum 𝕜 A) : RCLike.toComplex μ ∈ spectrum ℂ (complexify A) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, IsRoot.def] at hμ ⊢
  rw [charpoly_complexify,
    show RCLike.toComplex μ = (RCLike.toComplex : 𝕜 →⋆ₐ[ℝ] ℂ).toRingHom μ from rfl,
    Polynomial.eval_map_apply, hμ, map_zero]

/-- Every complex eigenvalue is at most the spectral radius in modulus. -/
theorem norm_le_specRadius_of_mem_spectrum_complexify {A : Matrix n n 𝕜} {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (complexify A)) : ‖μ‖ ≤ specRadius A := by
  have h2 := ENNReal.toReal_mono (spectralRadius_complexify_ne_top A)
    (le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (complexify A)) => (‖k‖₊ : ENNReal)) μ hμ)
  rwa [ENNReal.coe_toReal, coe_nnnorm] at h2

/-- Over `ℂ` the spectral radius is Mathlib's `spectralRadius`. -/
theorem specRadius_eq_toReal_spectralRadius (A : Matrix n n ℂ) :
    specRadius A = (spectralRadius ℂ A).toReal := by
  rw [specRadius, complexify_complex]

/-- The spectral radius of the complexification. -/
@[simp]
theorem specRadius_complexify (A : Matrix n n 𝕜) : specRadius (complexify A) = specRadius A := by
  rw [specRadius, complexify_complex, specRadius]

/-- The spectral radius of the identity of positive size is one. -/
@[simp]
theorem specRadius_one [Nonempty n] : specRadius (1 : Matrix n n 𝕜) = 1 := by
  rw [specRadius, complexify_one, spectrum.spectralRadius_one, ENNReal.toReal_one]

/-- Every eigenvalue is at most the spectral radius in modulus. -/
theorem norm_le_specRadius_of_mem_spectrum {A : Matrix n n 𝕜} {μ : 𝕜} (hμ : μ ∈ spectrum 𝕜 A) :
    ‖μ‖ ≤ specRadius A := by
  rw [← RCLike.norm_toComplex]
  exact norm_le_specRadius_of_mem_spectrum_complexify (toComplex_mem_spectrum_complexify hμ)

/-- **The spectral radius through a listing of the eigenvalues.** -/
theorem specRadius_le_iff_of_charpoly_eq {A : Matrix n n 𝕜} {d : n → ℂ}
    (hd : IsEigenvalueListing (complexify A) d) {c : ℝ} (hc : 0 ≤ c) :
    specRadius A ≤ c ↔ ∀ i, ‖d i‖ ≤ c := by
  rw [specRadius, ← ENNReal.le_ofReal_iff_toReal_le (spectralRadius_complexify_ne_top A) hc,
    spectralRadius_complexify_eq_iSup hd, iSup_le_iff]
  refine forall_congr' fun i => ?_
  rw [ENNReal.le_ofReal_iff_toReal_le ENNReal.coe_ne_top hc, ENNReal.coe_toReal, coe_nnnorm]

private theorem norm_le_specRadius_of_isEigenvalueListing {A : Matrix n n 𝕜} {d : n → ℂ}
    (hd : IsEigenvalueListing (complexify A) d) (i : n) : ‖d i‖ ≤ specRadius A :=
  (specRadius_le_iff_of_charpoly_eq hd (specRadius_nonneg A)).mp le_rfl i

/-- The spectral radius is attained at an eigenvalue of the complexification. -/
theorem exists_mem_spectrum_norm_eq_specRadius [Nonempty n] (A : Matrix n n 𝕜) :
    ∃ μ ∈ spectrum ℂ (complexify A), ‖μ‖ = specRadius A := by
  obtain ⟨d, hd⟩ := exists_isEigenvalueListing (complexify A)
  obtain ⟨i, hi⟩ := Finite.exists_max fun i => ‖d i‖
  have hmem : d i ∈ spectrum ℂ (complexify A) := hd.spectrum_eq_range ▸ Set.mem_range_self i
  exact ⟨d i, hmem, le_antisymm (norm_le_specRadius_of_mem_spectrum_complexify hmem)
    ((specRadius_le_iff_of_charpoly_eq hd (norm_nonneg _)).mpr hi)⟩

/-- **The spectral radius is at most the spectral norm.** [HornJohnson2013, Theorem 5.6.9]. -/
theorem specRadius_le_specNorm (A : Matrix n n 𝕜) : specRadius A ≤ specNorm A := by
  have h := spectralRadius_complexify_ne_top A
  open scoped Matrix.Norms.L2Operator in
  have hle := spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ (complexify A) 0
  simp only [Nat.cast_zero, zero_add, one_div_one, ENNReal.rpow_one, pow_one] at hle
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hle
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal, coe_nnnorm, coe_nnnorm,
    ← specNorm_eq_norm, ← specNorm_eq_norm, specNorm_complexify] at h2
  exact h2.trans (mul_le_of_le_one_right (specNorm_nonneg A) specNorm_one_le)

/-- The spectral radius of a matrix of size zero is zero. -/
@[simp]
theorem specRadius_of_isEmpty [IsEmpty n] (A : Matrix n n 𝕜) : specRadius A = 0 := by
  refine le_antisymm ?_ (specRadius_nonneg A)
  rw [← specNorm_zero (m := n) (n := n) (𝕜 := 𝕜), Subsingleton.elim 0 A]
  exact specRadius_le_specNorm A

/-- The spectral radius of a power. -/
theorem specRadius_pow [Nonempty n] (A : Matrix n n 𝕜) (k : ℕ) :
    specRadius (A ^ k) = specRadius A ^ k := by
  obtain ⟨d, hd⟩ := exists_isEigenvalueListing (complexify A)
  have hk : IsEigenvalueListing (complexify (A ^ k)) fun i => d i ^ k := by
    rw [complexify_pow]
    exact hd.pow k
  refine le_antisymm ?_ ?_
  · refine (specRadius_le_iff_of_charpoly_eq hk (pow_nonneg (specRadius_nonneg A) k)).mpr
      fun i => ?_
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_specRadius_of_isEigenvalueListing hd i) k
  · obtain ⟨i, hi⟩ := Finite.exists_max fun i => ‖d i‖
    have hρ : specRadius A = ‖d i‖ :=
      le_antisymm ((specRadius_le_iff_of_charpoly_eq hd (norm_nonneg _)).mpr hi)
        (norm_le_specRadius_of_isEigenvalueListing hd i)
    rw [hρ, ← norm_pow]
    exact norm_le_specRadius_of_isEigenvalueListing hk i

/-- The spectral radius is invariant under similarity. -/
theorem specRadius_inv_mul_mul (A : Matrix n n 𝕜) {S : Matrix n n 𝕜} (hS : IsUnit S.det) :
    specRadius (S⁻¹ * A * S) = specRadius A := by
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det S).mpr hS
  exact specRadius_eq_of_charpoly_eq (Matrix.charpoly_units_conj' u A)

/-- `A B` and `B A` have the same spectral radius. -/
theorem specRadius_mul_comm (A B : Matrix n n 𝕜) : specRadius (A * B) = specRadius (B * A) :=
  specRadius_eq_of_charpoly_eq (Matrix.charpoly_mul_comm A B)

/-- **The spectral norm of a normal matrix is its spectral radius.**
[HornJohnson2013, §5.6]. -/
theorem _root_.IsStarNormal.specNorm_eq_specRadius {A : Matrix n n 𝕜} (hA : IsStarNormal A) :
    specNorm A = specRadius A := by
  obtain ⟨d, hd⟩ := exists_isEigenvalueListing (complexify A)
  have hN : IsStarNormal (complexify A) := by
    rw [isStarNormal_iff, Matrix.star_eq_conjTranspose] at hA ⊢
    rw [commute_iff_eq, ← complexify_conjTranspose, ← complexify_mul, ← complexify_mul, hA.eq]
  refine le_antisymm ?_ (specRadius_le_specNorm A)
  rw [← specNorm_complexify]
  exact (hN.specNorm_le_iff hd (specRadius_nonneg A)).mpr
    (norm_le_specRadius_of_isEigenvalueListing hd)

/-- The spectral radius is at most the largest row sum.
Port of `NLAlib.spectralRadius_le_max_row_sum`. -/
theorem specRadius_le_of_forall_sum_le {A : Matrix n n 𝕜} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ∑ j, ‖A i j‖ ≤ c) : specRadius A ≤ c := by
  obtain ⟨d, hd⟩ := exists_isEigenvalueListing (complexify A)
  refine (specRadius_le_iff_of_charpoly_eq hd hc).mpr fun i => ?_
  have hmem : d i ∈ spectrum ℂ (complexify A) := hd.spectrum_eq_range ▸ Set.mem_range_self i
  obtain ⟨j, hj⟩ := exists_norm_le_sum_of_mem_spectrum hmem
  refine hj.trans ((Finset.sum_congr rfl fun l _ => ?_).trans_le (h j))
  rw [complexify_apply, RCLike.norm_toComplex]

omit [DecidableEq n] in
private theorem commute_complexify {A B : Matrix n n 𝕜} (h : Commute A B) :
    Commute (complexify A) (complexify B) := by
  rw [commute_iff_eq, ← complexify_mul, ← complexify_mul, h.eq]

/-- The spectral radius of a sum of commuting matrices is at most the sum. -/
theorem specRadius_add_le_of_commute {A B : Matrix n n 𝕜} (h : Commute A B) :
    specRadius (A + B) ≤ specRadius A + specRadius B := by
  obtain ⟨a, b, ha, hb, hab, -⟩ :=
    exists_isEigenvalueListing_add_mul_of_commute (commute_complexify h)
  rw [← complexify_add] at hab
  refine (specRadius_le_iff_of_charpoly_eq hab
    (add_nonneg (specRadius_nonneg A) (specRadius_nonneg B))).mpr fun i => ?_
  exact (norm_add_le _ _).trans (add_le_add (norm_le_specRadius_of_isEigenvalueListing ha i)
    (norm_le_specRadius_of_isEigenvalueListing hb i))

/-- The spectral radius of a product of commuting matrices is at most the product. -/
theorem specRadius_mul_le_of_commute {A B : Matrix n n 𝕜} (h : Commute A B) :
    specRadius (A * B) ≤ specRadius A * specRadius B := by
  obtain ⟨a, b, ha, hb, -, hab⟩ :=
    exists_isEigenvalueListing_add_mul_of_commute (commute_complexify h)
  rw [← complexify_mul] at hab
  refine (specRadius_le_iff_of_charpoly_eq hab
    (mul_nonneg (specRadius_nonneg A) (specRadius_nonneg B))).mpr fun i => ?_
  rw [norm_mul]
  exact mul_le_mul (norm_le_specRadius_of_isEigenvalueListing ha i)
    (norm_le_specRadius_of_isEigenvalueListing hb i) (norm_nonneg _) (specRadius_nonneg A)

/-! ### Diagonal dominance -/

private theorem specRadius_lt_of_forall_sum_lt {A : Matrix n n 𝕜} {c : ℝ} (hc : 0 < c)
    (h : ∀ i, ∑ j, ‖A i j‖ < c) : specRadius A < c := by
  cases isEmpty_or_nonempty n with
  | inl hn => rw [specRadius_of_isEmpty]; exact hc
  | inr hn =>
    obtain ⟨μ, hμ, hρ⟩ := exists_mem_spectrum_norm_eq_specRadius A
    obtain ⟨i, hi⟩ := exists_norm_le_sum_of_mem_spectrum hμ
    rw [← hρ]
    refine hi.trans_lt ((Finset.sum_congr rfl fun l _ => ?_).trans_lt (h i))
    rw [complexify_apply, RCLike.norm_toComplex]

/-- **The Jacobi iteration converges for strictly diagonally dominant matrices**: the iteration
matrix `1 - D⁻¹ A`, with `D` the diagonal of `A`, has spectral radius less than one.
[GolubVanLoan2013, Theorem 11.2.2]; [Saad2003, Theorem 4.9].
Result: jacobi-convergence -/
theorem specRadius_one_sub_inv_diagonal_mul_lt_one {A : Matrix n n 𝕜}
    (h : ∀ i, gershgorinRadius A i < ‖A i i‖) :
    specRadius (1 - (Matrix.diagonal fun i => A i i)⁻¹ * A) < 1 := by
  have hne : ∀ i, A i i ≠ 0 := fun i =>
    norm_pos_iff.mp ((gershgorinRadius_nonneg A i).trans_lt (h i))
  have hD : (Matrix.diagonal fun i => A i i)⁻¹ = Matrix.diagonal fun i => (A i i)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg Matrix.diagonal (funext fun i => mul_inv_cancel₀ (hne i))
  refine specRadius_lt_of_forall_sum_lt zero_lt_one fun i => ?_
  have hentry : ∀ j, ‖(1 - (Matrix.diagonal fun i => (A i i)⁻¹) * A) i j‖ =
      if j = i then 0 else ‖A i i‖⁻¹ * ‖A i j‖ := by
    intro j
    rw [Matrix.sub_apply, Matrix.diagonal_mul]
    split_ifs with hji
    · subst hji
      rw [Matrix.one_apply_eq, inv_mul_cancel₀ (hne j), sub_self, norm_zero]
    · rw [Matrix.one_apply_ne (Ne.symm hji), zero_sub, norm_neg, norm_mul, norm_inv]
  have hsum : ∑ j, (if j = i then 0 else ‖A i i‖⁻¹ * ‖A i j‖) =
      ∑ j ∈ Finset.univ.erase i, ‖A i i‖⁻¹ * ‖A i j‖ :=
    (Finset.sum_erase Finset.univ (f := fun j => if j = i then (0 : ℝ) else ‖A i i‖⁻¹ * ‖A i j‖)
      (a := i) (if_pos rfl)).symm.trans
      (Finset.sum_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj))
  rw [hD, Finset.sum_congr rfl fun j _ => hentry j, hsum, ← Finset.mul_sum,
    ← gershgorinRadius_def]
  exact (inv_mul_lt_one₀ (norm_pos_iff.mpr (hne i))).mpr (h i)

end NLAlib
