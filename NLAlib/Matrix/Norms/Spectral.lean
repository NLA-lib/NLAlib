/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Tactic.Positivity.Core
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2

/-!
# The spectral norm

`NLAlib.specNorm A` is the spectral norm of a matrix: the operator norm of `x ↦ A *ᵥ x` between
Euclidean spaces, equal to the largest singular value. It is a named function because Mathlib's
matrix norms are scoped instances; `NLAlib.specNorm_eq_norm` is the bridge, by `rfl`, to the norm
of the `Matrix.Norms.L2Operator` scope. Unlike that norm, `specNorm` needs no `DecidableEq`.

## Main definitions

* `NLAlib.specNorm`: the spectral norm.

## Main results

* `NLAlib.norm_toLp_mulVec_le`: `‖A x‖ ≤ specNorm A * ‖x‖`.
* `NLAlib.specNorm_le_iff`: the characterisation as the least such constant.
* `NLAlib.specNorm_mul_le`, `NLAlib.specNorm_pow_le`: submultiplicativity, for rectangular
  factors and for powers.
* `NLAlib.specNorm_conjTranspose_mul_self`: the C*-identity `specNorm (Aᴴ * A) = specNorm A ^ 2`.
* `NLAlib.exists_norm_eq_one_and_norm_mulVec_eq_specNorm`: the norm is attained.
* `NLAlib.specNorm_eq_norm`: the bridge to Mathlib.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-- The **spectral norm** of a matrix: the operator norm of `x ↦ A *ᵥ x` from
`EuclideanSpace 𝕜 n` to `EuclideanSpace 𝕜 m`. It equals the largest singular value and is `0` when
either index type is empty. [GolubVanLoan2013, §2.3.1]. -/
noncomputable def specNorm (A : Matrix m n 𝕜) : ℝ :=
  ‖LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 𝕜 (m → 𝕜)).symm.toLinearMap ∘ₗ A.mulVecLin ∘ₗ
      (WithLp.linearEquiv 2 𝕜 (n → 𝕜)).toLinearMap)‖

open scoped Matrix.Norms.L2Operator in
/-- **Bridge to Mathlib.** `specNorm A` is the norm of `A` in the `Matrix.Norms.L2Operator`
scope. Port of `NLAlib.specNorm_eq_norm`. -/
theorem specNorm_eq_norm [DecidableEq n] (A : Matrix m n 𝕜) : specNorm A = ‖A‖ :=
  rfl

/-! ### Norm axioms -/

/-- The spectral norm is nonnegative. -/
theorem specNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ specNorm A :=
  norm_nonneg _

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm of the zero matrix is zero. -/
@[simp]
theorem specNorm_zero : specNorm (0 : Matrix m n 𝕜) = 0 := by
  classical
  rw [specNorm_eq_norm, norm_zero]

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm vanishes only at the zero matrix. -/
@[simp]
theorem specNorm_eq_zero_iff {A : Matrix m n 𝕜} : specNorm A = 0 ↔ A = 0 := by
  classical
  rw [specNorm_eq_norm, norm_eq_zero]

open scoped Matrix.Norms.L2Operator in
/-- The triangle inequality for the spectral norm. -/
theorem specNorm_add_le (A B : Matrix m n 𝕜) : specNorm (A + B) ≤ specNorm A + specNorm B := by
  classical
  simp only [specNorm_eq_norm]
  exact norm_add_le A B

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm is invariant under negation. -/
@[simp]
theorem specNorm_neg (A : Matrix m n 𝕜) : specNorm (-A) = specNorm A := by
  classical
  rw [specNorm_eq_norm, specNorm_eq_norm, norm_neg]

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm of a difference is symmetric. -/
theorem specNorm_sub_comm (A B : Matrix m n 𝕜) : specNorm (A - B) = specNorm (B - A) := by
  classical
  rw [specNorm_eq_norm, specNorm_eq_norm, norm_sub_rev]

open scoped Matrix.Norms.L2Operator in
/-- The triangle inequality for a difference. -/
theorem specNorm_sub_le (A B : Matrix m n 𝕜) : specNorm (A - B) ≤ specNorm A + specNorm B := by
  classical
  simp only [specNorm_eq_norm]
  exact norm_sub_le A B

open scoped Matrix.Norms.L2Operator in
/-- The reverse triangle inequality: the spectral norm is `1`-Lipschitz for itself.
Port of `NLAlib.abs_specNorm_sub_specNorm_le`. -/
theorem abs_specNorm_sub_specNorm_le (A B : Matrix m n 𝕜) :
    |specNorm A - specNorm B| ≤ specNorm (A - B) := by
  classical
  simp only [specNorm_eq_norm]
  exact abs_norm_sub_norm_le A B

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm is absolutely homogeneous. -/
theorem specNorm_smul (c : 𝕜) (A : Matrix m n 𝕜) : specNorm (c • A) = ‖c‖ * specNorm A := by
  classical
  rw [specNorm_eq_norm, specNorm_eq_norm, norm_smul]

/-- The spectral norm is absolutely homogeneous for the real scalar action on a `𝕜`-matrix. -/
theorem specNorm_real_smul (a : ℝ) (A : Matrix m n 𝕜) : specNorm (a • A) = |a| * specNorm A := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), specNorm_smul, RCLike.norm_ofReal]

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm of a finite sum is at most the sum of the spectral norms. -/
theorem specNorm_sum_le {ι : Type*} (s : Finset ι) (A : ι → Matrix m n 𝕜) :
    specNorm (∑ i ∈ s, A i) ≤ ∑ i ∈ s, specNorm (A i) := by
  classical
  simp only [specNorm_eq_norm]
  exact norm_sum_le s A

/-! ### Action on vectors -/

open scoped Matrix.Norms.L2Operator in
/-- The defining bound of the spectral norm: `‖A x‖ ≤ specNorm A * ‖x‖`.
Port of `NLAlib.sum_norm_sq_mulVec_le_specNorm_sq`. -/
theorem norm_toLp_mulVec_le (A : Matrix m n 𝕜) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ specNorm A * ‖WithLp.toLp 2 x‖ := by
  classical
  exact A.l2_opNorm_mulVec (WithLp.toLp 2 x)

/-- The spectral norm is the least constant `c ≥ 0` with `‖A x‖ ≤ c * ‖x‖` for all `x`. -/
theorem specNorm_le_iff {A : Matrix m n 𝕜} {c : ℝ} (hc : 0 ≤ c) :
    specNorm A ≤ c ↔ ∀ x, ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ c * ‖WithLp.toLp 2 x‖ := by
  unfold specNorm
  rw [ContinuousLinearMap.opNorm_le_iff hc]
  exact ⟨fun h x => h (WithLp.toLp 2 x), fun h x => h x.ofLp⟩

/-- To bound the spectral norm by `c ≥ 0` it is enough to bound `‖A x‖` on unit vectors.
Port of `NLAlib.specNorm_le_of_forall_sqrt_le`. -/
theorem specNorm_le_of_forall_norm_eq_one {A : Matrix m n 𝕜} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, ‖WithLp.toLp 2 x‖ = 1 → ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ c) : specNorm A ≤ c :=
  ContinuousLinearMap.opNorm_le_of_unit_norm hc fun x hx => h x.ofLp hx

/-- The spectral norm is attained at a unit vector, when there is one. -/
theorem exists_norm_eq_one_and_norm_mulVec_eq_specNorm [Nonempty n] (A : Matrix m n 𝕜) :
    ∃ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 ∧ ‖WithLp.toLp 2 (A *ᵥ x)‖ = specNorm A := by
  classical
  obtain ⟨i⟩ := ‹Nonempty n›
  have hne : (Metric.sphere (0 : EuclideanSpace 𝕜 n) 1).Nonempty :=
    ⟨EuclideanSpace.single i 1, by simp⟩
  have hcont : Continuous fun x : EuclideanSpace 𝕜 n => ‖WithLp.toLp 2 (A *ᵥ x.ofLp)‖ :=
    (Matrix.toEuclideanLin A).continuous_of_finiteDimensional.norm
  obtain ⟨x, hx, hmax⟩ :=
    (isCompact_sphere (0 : EuclideanSpace 𝕜 n) 1).exists_isMaxOn hne hcont.continuousOn
  rw [mem_sphere_zero_iff_norm] at hx
  refine ⟨x.ofLp, hx, le_antisymm ?_ ?_⟩
  · have h := norm_toLp_mulVec_le A x.ofLp
    rwa [show ‖WithLp.toLp 2 x.ofLp‖ = 1 from hx, mul_one] at h
  · exact specNorm_le_of_forall_norm_eq_one (norm_nonneg _) fun y hy =>
      hmax (mem_sphere_zero_iff_norm.2 hy)

/-- The bilinear form bound: `|uᴴ A x| ≤ ‖u‖ * specNorm A * ‖x‖`.
Port of `NLAlib.abs_dotProduct_mulVec_le`. -/
theorem norm_star_dotProduct_mulVec_le (A : Matrix m n 𝕜) (u : m → 𝕜) (x : n → 𝕜) :
    ‖star u ⬝ᵥ (A *ᵥ x)‖ ≤ ‖WithLp.toLp 2 u‖ * specNorm A * ‖WithLp.toLp 2 x‖ := by
  have hin : star u ⬝ᵥ (A *ᵥ x) = inner 𝕜 (WithLp.toLp 2 u) (WithLp.toLp 2 (A *ᵥ x)) := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [hin, mul_assoc]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (norm_toLp_mulVec_le A x) (norm_nonneg _))

/-- To bound the spectral norm by `c ≥ 0` it is enough to bound the bilinear form `uᴴ A x` by `c`
on unit vectors `u` and `x`. -/
theorem specNorm_le_of_forall_norm_star_dotProduct_mulVec_le {A : Matrix m n 𝕜} {c : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ (u : m → 𝕜) (x : n → 𝕜), ‖WithLp.toLp 2 u‖ = 1 → ‖WithLp.toLp 2 x‖ = 1 →
      ‖star u ⬝ᵥ (A *ᵥ x)‖ ≤ c) : specNorm A ≤ c := by
  refine specNorm_le_of_forall_norm_eq_one hc fun x hx => ?_
  set r : ℝ := ‖WithLp.toLp 2 (A *ᵥ x)‖ with hr
  rcases eq_or_lt_of_le (norm_nonneg (WithLp.toLp 2 (A *ᵥ x))) with h0 | h0
  · rw [hr, ← h0]
    exact hc
  have hu : ‖WithLp.toLp 2 (r⁻¹ • (A *ᵥ x))‖ = 1 := by
    rw [WithLp.toLp_smul, norm_smul, ← hr, norm_inv, Real.norm_eq_abs, abs_of_pos h0,
      inv_mul_cancel₀ h0.ne']
  have hself : ‖star (A *ᵥ x) ⬝ᵥ (A *ᵥ x)‖ = r ^ 2 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp, inner_self_eq_norm_sq_to_K, norm_pow,
      RCLike.norm_ofReal, abs_norm]
  have key := h _ x hu hx
  rw [star_smul, star_trivial, smul_dotProduct, norm_smul, hself, Real.norm_eq_abs, abs_inv,
    abs_of_pos h0] at key
  have hrr : r⁻¹ * r ^ 2 = r := by
    field_simp
  rwa [hrr] at key

/-! ### Products and adjoints -/

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm is submultiplicative, for rectangular factors.
[GolubVanLoan2013, §2.3.3]. Port of `NLAlib.specNorm_mul_le`. -/
theorem specNorm_mul_le (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    specNorm (A * B) ≤ specNorm A * specNorm B := by
  classical
  simp only [specNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm is invariant under the conjugate transpose.
Port of `NLAlib.specNorm_conjTranspose`. -/
@[simp]
theorem specNorm_conjTranspose (A : Matrix m n 𝕜) : specNorm Aᴴ = specNorm A := by
  classical
  rw [specNorm_eq_norm, specNorm_eq_norm, Matrix.l2_opNorm_conjTranspose]

private theorem specNorm_map_star_le (A : Matrix m n 𝕜) : specNorm (A.map star) ≤ specNorm A := by
  refine (specNorm_le_iff (specNorm_nonneg A)).2 fun x => ?_
  have hv : A.map star *ᵥ x = star (A *ᵥ star x) := by
    ext i
    simp [Matrix.mulVec, dotProduct, star_sum]
  rw [hv, EuclideanSpace.norm_toLp_star, ← EuclideanSpace.norm_toLp_star x]
  exact norm_toLp_mulVec_le A (star x)

/-- The spectral norm is invariant under entrywise conjugation. -/
theorem specNorm_map_star (A : Matrix m n 𝕜) : specNorm (A.map star) = specNorm A := by
  refine le_antisymm (specNorm_map_star_le A) ?_
  have h := specNorm_map_star_le (A.map star)
  have hA : (A.map star).map star = A := by
    ext i j
    simp
  rwa [hA] at h

/-- The spectral norm is invariant under the transpose, also over `ℂ`.
Port of `NLAlib.specNorm_transpose`. -/
@[simp]
theorem specNorm_transpose (A : Matrix m n 𝕜) : specNorm Aᵀ = specNorm A := by
  have h : Aᵀ = Aᴴ.map star := by
    ext i j
    simp
  rw [h, specNorm_map_star, specNorm_conjTranspose]

open scoped Matrix.Norms.L2Operator in
/-- The **C*-identity**: `specNorm (Aᴴ * A) = specNorm A ^ 2`.
Port of `NLAlib.specNorm_sq_eq_specNorm_conjTranspose_mul_self`. -/
theorem specNorm_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    specNorm (Aᴴ * A) = specNorm A ^ 2 := by
  classical
  rw [specNorm_eq_norm, specNorm_eq_norm, Matrix.l2_opNorm_conjTranspose_mul_self, sq]

/-- The C*-identity for `A * Aᴴ`. Port of `NLAlib.specNorm_mul_conjTranspose_self`. -/
theorem specNorm_mul_conjTranspose_self (A : Matrix m n 𝕜) :
    specNorm (A * Aᴴ) = specNorm A ^ 2 := by
  have h := specNorm_conjTranspose_mul_self Aᴴ
  rwa [Matrix.conjTranspose_conjTranspose, specNorm_conjTranspose] at h

/-! ### Reindexing and special matrices -/

private theorem specNorm_submatrix_equiv_le (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    specNorm (A.submatrix e₁ e₂) ≤ specNorm A := by
  refine (specNorm_le_iff (specNorm_nonneg A)).2 fun x => ?_
  rw [Matrix.submatrix_mulVec_equiv, EuclideanSpace.norm_toLp_comp_equiv,
    ← EuclideanSpace.norm_toLp_comp_equiv x e₂.symm]
  exact norm_toLp_mulVec_le A _

/-- The spectral norm is invariant under relabelling rows and columns by bijections.
Port of `NLAlib.specNorm_reindex`. -/
@[simp]
theorem specNorm_submatrix_equiv (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    specNorm (A.submatrix e₁ e₂) = specNorm A := by
  refine le_antisymm (specNorm_submatrix_equiv_le A e₁ e₂) ?_
  have h := specNorm_submatrix_equiv_le (A.submatrix e₁ e₂) e₁.symm e₂.symm
  rwa [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Equiv.self_comp_symm,
    Matrix.submatrix_id_id] at h

/-- The spectral norm of the identity is at most one. It is zero on an empty index type. -/
theorem specNorm_one_le [DecidableEq n] : specNorm (1 : Matrix n n 𝕜) ≤ 1 :=
  (specNorm_le_iff zero_le_one).2 fun x => by rw [Matrix.one_mulVec, one_mul]

/-- The spectral norm of the identity on a nonempty index type is one. -/
@[simp]
theorem specNorm_one [DecidableEq n] [Nonempty n] : specNorm (1 : Matrix n n 𝕜) = 1 := by
  refine le_antisymm specNorm_one_le ?_
  obtain ⟨i⟩ := ‹Nonempty n›
  have h := norm_toLp_mulVec_le (1 : Matrix n n 𝕜) (Pi.single i 1)
  rwa [Matrix.one_mulVec, PiLp.toLp_single, PiLp.norm_single, norm_one, mul_one] at h

/-- The spectral norm of a power is at most the power of the spectral norm. -/
theorem specNorm_pow_le [DecidableEq n] (A : Matrix n n 𝕜) (k : ℕ) :
    specNorm (A ^ k) ≤ specNorm A ^ k := by
  induction k with
  | zero => simpa only [pow_zero] using specNorm_one_le (n := n) (𝕜 := 𝕜)
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (specNorm_nonneg A))

open scoped Matrix.Norms.L2Operator in
/-- The spectral norm of a diagonal matrix is the largest modulus of a diagonal entry, that is,
the supremum norm of the diagonal. -/
theorem specNorm_diagonal [DecidableEq n] (d : n → 𝕜) : specNorm (Matrix.diagonal d) = ‖d‖ := by
  rw [specNorm_eq_norm, Matrix.l2_opNorm_diagonal]

/-- A diagonal matrix with entries bounded by `c ≥ 0` has spectral norm at most `c`.
Port of `NLAlib.specNorm_diagonal_le`. -/
theorem specNorm_diagonal_le [DecidableEq n] {d : n → 𝕜} {c : ℝ} (hc : 0 ≤ c)
    (hd : ∀ i, ‖d i‖ ≤ c) : specNorm (Matrix.diagonal d) ≤ c := by
  rw [specNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hc).2 hd

/-- The spectral norm of a rank-one matrix `u vᵀ` is the product of the Euclidean norms. -/
theorem specNorm_vecMulVec (u : m → 𝕜) (v : n → 𝕜) :
    specNorm (Matrix.vecMulVec u v) = ‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 v‖ := by
  have hmv (x : n → 𝕜) : ‖WithLp.toLp 2 (Matrix.vecMulVec u v *ᵥ x)‖ =
      ‖v ⬝ᵥ x‖ * ‖WithLp.toLp 2 u‖ := by
    rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul, WithLp.toLp_smul, norm_smul]
  refine le_antisymm ((specNorm_le_iff (by positivity)).2 fun x => ?_) ?_
  · have hcs : ‖v ⬝ᵥ x‖ ≤ ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 x‖ := by
      have h := norm_inner_le_norm (𝕜 := 𝕜) (WithLp.toLp 2 (star v)) (WithLp.toLp 2 x)
      rwa [EuclideanSpace.inner_toLp_toLp, star_star, dotProduct_comm,
        EuclideanSpace.norm_toLp_star] at h
    rw [hmv]
    calc ‖v ⬝ᵥ x‖ * ‖WithLp.toLp 2 u‖
        ≤ ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 u‖ := by gcongr
      _ = ‖WithLp.toLp 2 u‖ * ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 x‖ := by ring
  · have h := norm_toLp_mulVec_le (Matrix.vecMulVec u v) (star v)
    have hvv : ‖v ⬝ᵥ star v‖ = ‖WithLp.toLp 2 v‖ ^ 2 := by
      rw [← EuclideanSpace.inner_toLp_toLp, inner_self_eq_norm_sq_to_K, norm_pow,
        RCLike.norm_ofReal, abs_norm]
    rw [hmv, EuclideanSpace.norm_toLp_star, hvv] at h
    rcases eq_or_lt_of_le (norm_nonneg (WithLp.toLp 2 v)) with h0 | h0
    · rw [← h0, mul_zero]
      exact specNorm_nonneg _
    · exact le_of_mul_le_mul_right (le_of_eq_of_le (by ring) h) h0

/-- Every column has Euclidean norm at most the spectral norm. -/
theorem norm_toLp_col_le_specNorm (A : Matrix m n 𝕜) (j : n) :
    ‖WithLp.toLp 2 (A.col j)‖ ≤ specNorm A := by
  classical
  have h := norm_toLp_mulVec_le A (Pi.single j 1)
  rwa [Matrix.mulVec_single_one, PiLp.toLp_single, PiLp.norm_single, norm_one, mul_one] at h

/-- Every entry is bounded by the spectral norm. Port of `NLAlib.abs_apply_le_specNorm`. -/
theorem norm_apply_le_specNorm (A : Matrix m n 𝕜) (i : m) (j : n) : ‖A i j‖ ≤ specNorm A :=
  (PiLp.norm_apply_le (WithLp.toLp 2 (A.col j)) i).trans (norm_toLp_col_le_specNorm A j)

/-- The spectral norm is continuous for the entrywise topology on matrices. -/
theorem continuous_specNorm : Continuous (specNorm : Matrix m n 𝕜 → ℝ) := by
  classical
  open scoped Matrix.Norms.L2Operator in
  exact continuous_norm (E := Matrix m n 𝕜)

end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `NLAlib.specNorm A` is nonnegative. -/
@[positivity NLAlib.specNorm _]
meta def evalSpecNorm : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    let pf ← mkAppM ``NLAlib.specNorm_nonneg #[e.appArg!]
    pure (.nonnegative pf)

end Mathlib.Meta.Positivity
