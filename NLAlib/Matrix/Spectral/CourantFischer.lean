/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Spectral.EigenvalueTransform

/-!
# The Courant–Fischer variational characterisation of eigenvalues

The `k`-th eigenvalue of a Hermitian matrix is a max–min and a min–max of its quadratic form
over subspaces. The two one-sided subspace statements are the forms proofs use: a lower bound on
the quadratic form over a subspace of dimension `k + 1` bounds `eigenvalue A k` from below, and
an upper bound over a subspace of codimension `k` bounds it from above. Hypotheses are written
homogeneously, `c * ‖x‖ ^ 2 ≤ re (quadForm A x)`, with no restriction to nonzero or unit vectors.

The extreme eigenvalues are also characterised in the Loewner order, which is how bounds on the
largest and smallest eigenvalue of a random matrix are stated and used.

## Main results

* `Matrix.IsHermitian.le_eigenvalue_of_forall_mem`,
  `Matrix.IsHermitian.eigenvalue_le_of_forall_mem`: the one-sided Courant–Fischer bounds.
* `Matrix.IsHermitian.eigenvalue_eq_iSup_iInf`, `Matrix.IsHermitian.eigenvalue_eq_iInf_iSup`:
  the Courant–Fischer theorem as equations.
* `Matrix.IsHermitian.le_smul_one_iff`, `Matrix.IsHermitian.smul_one_le_iff`: the largest and
  smallest eigenvalue in the Loewner order.
* `Matrix.IsHermitian.specNorm_eq_max`, `Matrix.PosSemidef.specNorm_eq_eigenvalue_zero`: the
  spectral norm of a Hermitian matrix.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### Coordinates in an eigenbasis -/

/-- Coordinates in an orthonormal eigenbasis of a Hermitian matrix: a linear map `T` to
`Fin (Fintype.card n) → 𝕜` that preserves the Euclidean norm, diagonalises the quadratic form
with the sorted eigenvalues as weights, and for every set `s` of coordinates has a subspace of
dimension `s.card` on which the coordinates outside `s` vanish. -/
private theorem exists_eigencoordinates {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ T : (n → 𝕜) →ₗ[𝕜] (Fin (Fintype.card n) → 𝕜),
      (∀ x, ‖WithLp.toLp 2 x‖ ^ 2 = ∑ j, ‖T x j‖ ^ 2) ∧
      (∀ x, RCLike.re (quadForm A x) = ∑ j : Fin (Fintype.card n), eigenvalue A j * ‖T x j‖ ^ 2) ∧
      ∀ s : Finset (Fin (Fintype.card n)), ∃ S : Submodule 𝕜 (n → 𝕜),
        Module.finrank 𝕜 S = s.card ∧ ∀ x ∈ S, ∀ j ∉ s, T x j = 0 := by
  classical
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hU' : HasOrthonormalCols Uᴴ := hU.conjTranspose_of_card_eq (Fintype.card_fin _).symm
  refine ⟨Uᴴ.mulVecLin, fun x => ?_, fun x => ?_, fun s => ?_⟩
  · rw [Matrix.mulVecLin_apply, ← hU'.norm_toLp_mulVec x, EuclideanSpace.norm_sq_eq]
  · have hq : quadForm A x = quadForm
        (Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜))
        (Uᴴ *ᵥ x) := by
      rw [← quadForm_conjTranspose_mul_mul, Matrix.conjTranspose_conjTranspose, ← hAU]
    rw [hq, quadForm_diagonal, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← RCLike.ofReal_mul, RCLike.ofReal_re, Matrix.mulVecLin_apply]
  · refine ⟨LinearMap.range
      (U.submatrix id (Subtype.val : s → Fin (Fintype.card n))).mulVecLin, ?_, ?_⟩
    · exact (hU.submatrix (Equiv.refl n) Subtype.val_injective).rank_eq.trans
        (Fintype.card_coe s)
    · rintro _ ⟨y, rfl⟩ j hj
      have hUs : Uᴴ * U.submatrix id (Subtype.val : s → Fin (Fintype.card n)) =
          (1 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) 𝕜).submatrix id
            Subtype.val := by
        rw [← hU.conjTranspose_mul_self]
        rfl
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hUs]
      refine Finset.sum_eq_zero fun t _ => ?_
      change (1 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) 𝕜) j t.1 * y t = 0
      rw [Matrix.one_apply_ne fun h : j = t.1 => hj (h ▸ t.2), zero_mul]

/-- If the coordinates before `k` vanish, the weighted sum is at most `eigenvalue A k` times the
plain sum. -/
private theorem sum_eigenvalue_mul_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    {y : Fin (Fintype.card n) → 𝕜} (hy : ∀ j : Fin (Fintype.card n), (j : ℕ) < k → y j = 0) :
    ∑ j : Fin (Fintype.card n), eigenvalue A j * ‖y j‖ ^ 2 ≤
      eigenvalue A k * ∑ j, ‖y j‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases lt_or_ge (j : ℕ) k with hjk | hjk
  · rw [hy j hjk, norm_zero, zero_pow two_ne_zero, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalue_le_eigenvalue hjk j.isLt) (sq_nonneg _)

/-- If the coordinates after `k` vanish, the weighted sum is at least `eigenvalue A k` times the
plain sum. -/
private theorem le_sum_eigenvalue_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    (hk : k < Fintype.card n) {y : Fin (Fintype.card n) → 𝕜}
    (hy : ∀ j : Fin (Fintype.card n), k < (j : ℕ) → y j = 0) :
    eigenvalue A k * ∑ j, ‖y j‖ ^ 2 ≤
      ∑ j : Fin (Fintype.card n), eigenvalue A j * ‖y j‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases lt_or_ge k (j : ℕ) with hjk | hjk
  · rw [hy j hjk, norm_zero, zero_pow two_ne_zero, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalue_le_eigenvalue hjk hk) (sq_nonneg _)

omit [Fintype n] in
/-- A subspace of dimension larger than `s.card` has a nonzero vector whose coordinates in `s`
vanish. -/
private theorem exists_mem_ne_zero_forall_eq_zero [Finite n] {N : ℕ} (T : (n → 𝕜) →ₗ[𝕜] (Fin N → 𝕜))
    (s : Finset (Fin N)) (S : Submodule 𝕜 (n → 𝕜)) (hS : s.card < Module.finrank 𝕜 S) :
    ∃ x ∈ S, x ≠ 0 ∧ ∀ j ∈ s, T x j = 0 := by
  have hker : LinearMap.ker
      ((LinearMap.funLeft 𝕜 𝕜 (Subtype.val : s → Fin N) ∘ₗ T).domRestrict S) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt
      (by rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe])
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨y, y.2, fun h => hy0 (Subtype.ext h),
    fun j hj => congrFun (LinearMap.mem_ker.mp hy) ⟨j, hj⟩⟩

private theorem norm_toLp_sq_pos {x : n → 𝕜} (hx : x ≠ 0) : 0 < ‖WithLp.toLp 2 x‖ ^ 2 :=
  pow_pos (norm_pos_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hx)) 2

/-! ### Unit vectors -/

/-- A nonzero vector has a unit multiple, and the quadratic form scales with the squared norm. -/
private theorem exists_smul_norm_eq_one {x : n → 𝕜} (hx : x ≠ 0) :
    ∃ a : 𝕜, ‖WithLp.toLp 2 (a • x)‖ = 1 ∧ ∀ A : Matrix n n 𝕜,
      RCLike.re (quadForm A x) = RCLike.re (quadForm A (a • x)) * ‖WithLp.toLp 2 x‖ ^ 2 := by
  have hx' : ‖WithLp.toLp 2 x‖ ≠ 0 := norm_ne_zero_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hx)
  have ha : ((‖WithLp.toLp 2 x‖⁻¹ : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (inv_ne_zero hx')
  have h1 : ‖WithLp.toLp 2 (((‖WithLp.toLp 2 x‖⁻¹ : ℝ) : 𝕜) • x)‖ = 1 := by
    rw [WithLp.toLp_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hx']
  refine ⟨_, h1, fun A => ?_⟩
  rw [re_quadForm_eq_rayleighQuotient_mul A x, ← rayleighQuotient_smul A ha x,
    rayleighQuotient_of_norm_eq_one A h1]

/-- A lower bound on the quadratic form over the unit vectors of a subspace is a homogeneous
lower bound on the subspace. -/
private theorem mul_norm_sq_le_re_quadForm_of_forall_unit {A : Matrix n n 𝕜}
    {S : Submodule 𝕜 (n → 𝕜)} {c : ℝ}
    (h : ∀ x ∈ S, ‖WithLp.toLp 2 x‖ = 1 → c ≤ RCLike.re (quadForm A x)) (x : n → 𝕜)
    (hx : x ∈ S) : c * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [quadForm_zero_right, WithLp.toLp_zero, norm_zero, zero_pow two_ne_zero, mul_zero,
      map_zero]
  · obtain ⟨a, ha, hq⟩ := exists_smul_norm_eq_one hx0
    rw [hq A]
    exact mul_le_mul_of_nonneg_right (h _ (S.smul_mem a hx) ha) (sq_nonneg _)

/-- An upper bound on the quadratic form over the unit vectors of a subspace is a homogeneous
upper bound on the subspace. -/
private theorem re_quadForm_le_mul_norm_sq_of_forall_unit {A : Matrix n n 𝕜}
    {S : Submodule 𝕜 (n → 𝕜)} {c : ℝ}
    (h : ∀ x ∈ S, ‖WithLp.toLp 2 x‖ = 1 → RCLike.re (quadForm A x) ≤ c) (x : n → 𝕜)
    (hx : x ∈ S) : RCLike.re (quadForm A x) ≤ c * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [quadForm_zero_right, WithLp.toLp_zero, norm_zero, zero_pow two_ne_zero, mul_zero,
      map_zero]
  · obtain ⟨a, ha, hq⟩ := exists_smul_norm_eq_one hx0
    rw [hq A]
    exact mul_le_mul_of_nonneg_right (h _ (S.smul_mem a hx) ha) (sq_nonneg _)

/-- A subspace of positive dimension has a unit vector. -/
private theorem exists_mem_norm_eq_one {S : Submodule 𝕜 (n → 𝕜)}
    (hS : 0 < Module.finrank 𝕜 S) : ∃ x ∈ S, ‖WithLp.toLp 2 x‖ = 1 := by
  obtain ⟨x, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hS
  obtain ⟨a, ha, -⟩ := exists_smul_norm_eq_one (x := (x : n → 𝕜)) fun h => hx0 (Subtype.ext h)
  exact ⟨_, S.smul_mem a x.2, ha⟩

/-- On unit vectors the quadratic form is bounded by the spectral norm. -/
private theorem abs_re_quadForm_le_specNorm (A : Matrix n n 𝕜) {x : n → 𝕜}
    (hx : ‖WithLp.toLp 2 x‖ = 1) : |RCLike.re (quadForm A x)| ≤ specNorm A := by
  have h := abs_re_quadForm_le A x
  rwa [hx, one_pow, mul_one] at h

private theorem bddBelow_range_re_quadForm (A : Matrix n n 𝕜) (p : (n → 𝕜) → Prop) :
    BddBelow (Set.range fun x : {x : n → 𝕜 // p x ∧ ‖WithLp.toLp 2 x‖ = 1} =>
      RCLike.re (quadForm A x.1)) := by
  refine ⟨-specNorm A, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (abs_le.mp (abs_re_quadForm_le_specNorm A x.2.2)).1

private theorem bddAbove_range_re_quadForm (A : Matrix n n 𝕜) (p : (n → 𝕜) → Prop) :
    BddAbove (Set.range fun x : {x : n → 𝕜 // p x ∧ ‖WithLp.toLp 2 x‖ = 1} =>
      RCLike.re (quadForm A x.1)) := by
  refine ⟨specNorm A, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (abs_le.mp (abs_re_quadForm_le_specNorm A x.2.2)).2

/-- The quadratic form at a unit eigenvector is the eigenvalue. -/
private theorem re_quadForm_of_mulVec_eq_smul {A : Matrix n n 𝕜} {u : n → 𝕜} {c : ℝ}
    (hu : ‖WithLp.toLp 2 u‖ = 1) (h : A *ᵥ u = c • u) : RCLike.re (quadForm A u) = c := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)] at h
  rw [quadForm, h, dotProduct_smul, smul_eq_mul,
    EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, hu, one_pow, RCLike.ofReal_one, mul_one,
    RCLike.ofReal_re]

/-! ### One-sided subspace bounds -/

/-- **Courant–Fischer, lower bound.** If the quadratic form of a Hermitian `A` is at least
`c * ‖x‖ ^ 2` on a subspace of dimension at least `k + 1`, then `c ≤ eigenvalue A k`.
[HornJohnson2013, Theorem 4.2.6]; stated there as an equation over `ℂ` with eigenvalues in
increasing order, here as the inequality a proof applies, over any `RCLike` field, non-increasing.
Port of `Matrix.IsHermitian.le_eigenvalues₀_of_forall_mem`.
Result: courant-fischer -/
theorem _root_.Matrix.IsHermitian.le_eigenvalue_of_forall_mem {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (S : Submodule 𝕜 (n → 𝕜)) (hS : k + 1 ≤ Module.finrank 𝕜 S)
    {c : ℝ} (h : ∀ x ∈ S, c * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x)) :
    c ≤ eigenvalue A k := by
  have hk : k < Fintype.card n := by
    have h1 := S.finrank_le
    rw [Module.finrank_fintype_fun_eq_card] at h1
    omega
  obtain ⟨T, hT₁, hT₂, -⟩ := exists_eigencoordinates hA
  obtain ⟨x, hxS, hx0, hx⟩ := exists_mem_ne_zero_forall_eq_zero T (Finset.Iio ⟨k, hk⟩) S
    (by rw [Fin.card_Iio]; exact hS)
  have h1 : RCLike.re (quadForm A x) ≤ eigenvalue A k * ‖WithLp.toLp 2 x‖ ^ 2 := by
    rw [hT₁, hT₂]
    exact sum_eigenvalue_mul_le hA fun j hj => hx j (Finset.mem_Iio.mpr hj)
  exact le_of_mul_le_mul_right ((h x hxS).trans h1) (norm_toLp_sq_pos hx0)

/-- **Courant–Fischer, upper bound.** If the quadratic form of a Hermitian `A` is at most
`c * ‖x‖ ^ 2` on a subspace of codimension at most `k`, for a valid index `k`, then
`eigenvalue A k ≤ c`. The index must be valid: beyond the size of `A` the eigenvalue is `0` by
convention while the zero subspace satisfies the hypothesis for negative `c`.
[HornJohnson2013, Theorem 4.2.6].
Port of `Matrix.IsHermitian.eigenvalues₀_le_of_forall_mem`.
Result: courant-fischer -/
theorem _root_.Matrix.IsHermitian.eigenvalue_le_of_forall_mem {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) (W : Submodule 𝕜 (n → 𝕜))
    (hW : Fintype.card n ≤ Module.finrank 𝕜 W + k) {c : ℝ}
    (h : ∀ x ∈ W, RCLike.re (quadForm A x) ≤ c * ‖WithLp.toLp 2 x‖ ^ 2) :
    eigenvalue A k ≤ c := by
  obtain ⟨T, hT₁, hT₂, -⟩ := exists_eigencoordinates hA
  obtain ⟨x, hxW, hx0, hx⟩ := exists_mem_ne_zero_forall_eq_zero T (Finset.Ioi ⟨k, hk⟩) W
    (by rw [Fin.card_Ioi]; dsimp only; omega)
  have h1 : eigenvalue A k * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x) := by
    rw [hT₁, hT₂]
    exact le_sum_eigenvalue_mul hA hk fun j hj => hx j (Finset.mem_Ioi.mpr hj)
  exact le_of_mul_le_mul_right (h1.trans (h x hxW)) (norm_toLp_sq_pos hx0)

/-- The lower bound is attained: there is a subspace of dimension `k + 1` on which the quadratic
form is at least `eigenvalue A k * ‖x‖ ^ 2` (the span of the first `k + 1` eigenvectors).
Port of `Matrix.IsHermitian.exists_submodule_eigenvalues₀_mul_le`. -/
theorem _root_.Matrix.IsHermitian.exists_submodule_eigenvalue_mul_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    ∃ S : Submodule 𝕜 (n → 𝕜), Module.finrank 𝕜 S = k + 1 ∧
      ∀ x ∈ S, eigenvalue A k * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x) := by
  obtain ⟨T, hT₁, hT₂, hT₃⟩ := exists_eigencoordinates hA
  obtain ⟨S, hS, hST⟩ := hT₃ (Finset.Iic ⟨k, hk⟩)
  refine ⟨S, by rw [hS, Fin.card_Iic], fun x hx => ?_⟩
  rw [hT₁, hT₂]
  exact le_sum_eigenvalue_mul hA hk fun j hj =>
    hST x hx j fun hmem => absurd (Finset.mem_Iic.mp hmem) (not_le.mpr hj)

/-- The upper bound is attained: there is a subspace of codimension `k` on which the quadratic
form is at most `eigenvalue A k * ‖x‖ ^ 2` (the span of the eigenvectors from the `k`-th on).
Port of `Matrix.IsHermitian.exists_submodule_le_eigenvalues₀_mul`. -/
theorem _root_.Matrix.IsHermitian.exists_submodule_le_eigenvalue_mul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    ∃ W : Submodule 𝕜 (n → 𝕜), Module.finrank 𝕜 W + k = Fintype.card n ∧
      ∀ x ∈ W, RCLike.re (quadForm A x) ≤ eigenvalue A k * ‖WithLp.toLp 2 x‖ ^ 2 := by
  obtain ⟨T, hT₁, hT₂, hT₃⟩ := exists_eigencoordinates hA
  obtain ⟨W, hW, hWT⟩ := hT₃ (Finset.Ici ⟨k, hk⟩)
  refine ⟨W, by rw [hW, Fin.card_Ici]; dsimp only; omega, fun x hx => ?_⟩
  rw [hT₁, hT₂]
  exact sum_eigenvalue_mul_le hA fun j hj =>
    hWT x hx j fun hmem => absurd (Finset.mem_Ici.mp hmem) (not_le.mpr hj)

/-! ### The Courant–Fischer equations -/

/-- **Courant–Fischer, max–min form.** `eigenvalue A k` is the supremum, over subspaces `S` of
dimension `k + 1`, of the infimum of the quadratic form over the unit vectors of `S`.
[HornJohnson2013, Theorem 4.2.6].
Port of `Matrix.IsHermitian.eigenvalues₀_eq_iSup_iInf`.
Result: courant-fischer -/
theorem _root_.Matrix.IsHermitian.eigenvalue_eq_iSup_iInf {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue A k =
      ⨆ S : {S : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 S = k + 1},
        ⨅ x : {x : n → 𝕜 // x ∈ S.1 ∧ ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) := by
  have hinner : ∀ S : {S : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 S = k + 1},
      (⨅ x : {x : n → 𝕜 // x ∈ S.1 ∧ ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1)) ≤
        eigenvalue A k := fun S =>
    hA.le_eigenvalue_of_forall_mem S.1 S.2.ge <|
      mul_norm_sq_le_re_quadForm_of_forall_unit fun x hx hx1 =>
        ciInf_le (bddBelow_range_re_quadForm A (· ∈ S.1)) ⟨x, hx, hx1⟩
  obtain ⟨S, hS, hAS⟩ := hA.exists_submodule_eigenvalue_mul_le hk
  have : Nonempty {S : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 S = k + 1} := ⟨⟨S, hS⟩⟩
  refine le_antisymm ?_ (ciSup_le hinner)
  obtain ⟨u, huS, hu⟩ := exists_mem_norm_eq_one (S := S) (by omega)
  have : Nonempty {x : n → 𝕜 // x ∈ S ∧ ‖WithLp.toLp 2 x‖ = 1} := ⟨⟨u, huS, hu⟩⟩
  refine le_ciSup_of_le ⟨eigenvalue A k, ?_⟩ ⟨S, hS⟩ (le_ciInf fun x => ?_)
  · rintro _ ⟨S', rfl⟩
    exact hinner S'
  · have h := hAS x.1 x.2.1
    rwa [x.2.2, one_pow, mul_one] at h

/-- **Courant–Fischer, min–max form.** `eigenvalue A k` is the infimum, over subspaces `W` of
codimension `k`, of the supremum of the quadratic form over the unit vectors of `W`.
[HornJohnson2013, Theorem 4.2.6].
Port of `Matrix.IsHermitian.eigenvalues₀_eq_iInf_iSup`.
Result: courant-fischer -/
theorem _root_.Matrix.IsHermitian.eigenvalue_eq_iInf_iSup {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue A k =
      ⨅ W : {W : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 W + k = Fintype.card n},
        ⨆ x : {x : n → 𝕜 // x ∈ W.1 ∧ ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) := by
  have hinner : ∀ W : {W : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 W + k = Fintype.card n},
      eigenvalue A k ≤
        ⨆ x : {x : n → 𝕜 // x ∈ W.1 ∧ ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) :=
    fun W => hA.eigenvalue_le_of_forall_mem hk W.1 W.2.ge <|
      re_quadForm_le_mul_norm_sq_of_forall_unit fun x hx hx1 =>
        le_ciSup (bddAbove_range_re_quadForm A (· ∈ W.1)) ⟨x, hx, hx1⟩
  obtain ⟨W, hW, hAW⟩ := hA.exists_submodule_le_eigenvalue_mul hk
  have : Nonempty {W : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 W + k = Fintype.card n} :=
    ⟨⟨W, hW⟩⟩
  refine le_antisymm (le_ciInf hinner) ?_
  obtain ⟨u, huW, hu⟩ := exists_mem_norm_eq_one (S := W) (by omega)
  have : Nonempty {x : n → 𝕜 // x ∈ W ∧ ‖WithLp.toLp 2 x‖ = 1} := ⟨⟨u, huW, hu⟩⟩
  refine ciInf_le_of_le ⟨eigenvalue A k, ?_⟩ ⟨W, hW⟩ (ciSup_le fun x => ?_)
  · rintro _ ⟨W', rfl⟩
    exact hinner W'
  · have h := hAW x.1 x.2.1
    rwa [x.2.2, one_pow, mul_one] at h

/-! ### Extreme eigenvalues -/

/-- **Rayleigh bound, upper.** The quadratic form of a Hermitian matrix is at most its largest
eigenvalue times `‖x‖ ^ 2`. [HornJohnson2013, Theorem 4.2.2]. -/
theorem _root_.Matrix.IsHermitian.re_quadForm_le_eigenvalue_zero_mul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (quadForm A x) ≤ eigenvalue A 0 * ‖WithLp.toLp 2 x‖ ^ 2 := by
  obtain ⟨T, hT₁, hT₂, -⟩ := exists_eigencoordinates hA
  rw [hT₁, hT₂]
  exact sum_eigenvalue_mul_le hA fun j hj => absurd hj (Nat.not_lt_zero _)

/-- **Rayleigh bound, lower.** The quadratic form of a Hermitian matrix is at least its smallest
eigenvalue times `‖x‖ ^ 2`. The last index is given by the equation `k + 1 = Fintype.card n`.
[HornJohnson2013, Theorem 4.2.2].
Port of `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf`, there as an infimum. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_last_mul_le_re_quadForm {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k + 1 = Fintype.card n) (x : n → 𝕜) :
    eigenvalue A k * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x) := by
  obtain ⟨T, hT₁, hT₂, -⟩ := exists_eigencoordinates hA
  rw [hT₁, hT₂]
  exact le_sum_eigenvalue_mul hA (by omega) fun j hj => absurd j.isLt (by omega)

/-- A Hermitian matrix is below its largest eigenvalue times the identity. -/
theorem _root_.Matrix.IsHermitian.le_eigenvalue_zero_smul_one [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) : A ≤ eigenvalue A 0 • (1 : Matrix n n 𝕜) := by
  rw [hA.le_iff_re_quadForm_le (isHermitian_real_smul_one _)]
  intro x
  rw [re_quadForm_real_smul_one]
  exact hA.re_quadForm_le_eigenvalue_zero_mul x

/-- A Hermitian matrix is above its smallest eigenvalue times the identity. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_last_smul_one_le [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ} (hk : k + 1 = Fintype.card n) :
    eigenvalue A k • (1 : Matrix n n 𝕜) ≤ A := by
  rw [(isHermitian_real_smul_one _).le_iff_re_quadForm_le hA]
  intro x
  rw [re_quadForm_real_smul_one]
  exact hA.eigenvalue_last_mul_le_re_quadForm hk x

/-- **The largest eigenvalue in the Loewner order.** For a Hermitian matrix on a nonempty index
type, `A ≤ c • 1` exactly when the largest eigenvalue is at most `c`. This is the form in which
an upper bound on `λ_max` is used. -/
theorem _root_.Matrix.IsHermitian.le_smul_one_iff [DecidableEq n] [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c : ℝ} :
    A ≤ c • (1 : Matrix n n 𝕜) ↔ eigenvalue A 0 ≤ c := by
  rw [hA.le_iff_re_quadForm_le (isHermitian_real_smul_one c)]
  simp only [re_quadForm_real_smul_one]
  refine ⟨fun h => ?_, fun h x => ?_⟩
  · refine hA.eigenvalue_le_of_forall_mem Fintype.card_pos ⊤ ?_ fun x _ => h x
    rw [finrank_top, Module.finrank_fintype_fun_eq_card, add_zero]
  · exact (hA.re_quadForm_le_eigenvalue_zero_mul x).trans
      (mul_le_mul_of_nonneg_right h (sq_nonneg _))

/-- **The smallest eigenvalue in the Loewner order.** For a Hermitian matrix, `c • 1 ≤ A` exactly
when the smallest eigenvalue is at least `c`. This is the form in which a lower bound on `λ_min`
is used. -/
theorem _root_.Matrix.IsHermitian.smul_one_le_iff [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k + 1 = Fintype.card n) {c : ℝ} :
    c • (1 : Matrix n n 𝕜) ≤ A ↔ c ≤ eigenvalue A k := by
  rw [(isHermitian_real_smul_one c).le_iff_re_quadForm_le hA]
  simp only [re_quadForm_real_smul_one]
  refine ⟨fun h => ?_, fun h x => ?_⟩
  · refine hA.le_eigenvalue_of_forall_mem ⊤ ?_ fun x _ => h x
    rw [finrank_top, Module.finrank_fintype_fun_eq_card, hk]
  · exact (mul_le_mul_of_nonneg_right h (sq_nonneg _)).trans
      (hA.eigenvalue_last_mul_le_re_quadForm hk x)

/-- The largest eigenvalue of a Hermitian matrix is the supremum of its quadratic form over
unit vectors. [HornJohnson2013, Theorem 4.2.2].
Result: rayleigh-ritz -/
theorem _root_.Matrix.IsHermitian.eigenvalue_zero_eq_iSup [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    eigenvalue A 0 = ⨆ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) := by
  obtain ⟨u, hu, hAu⟩ := hA.exists_norm_eq_one_and_mulVec_eq (k := 0) Fintype.card_pos
  have : Nonempty {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} := ⟨⟨u, hu⟩⟩
  have hle : ∀ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1},
      RCLike.re (quadForm A x.1) ≤ eigenvalue A 0 := fun x => by
    have h := hA.re_quadForm_le_eigenvalue_zero_mul x.1
    rwa [x.2, one_pow, mul_one] at h
  refine le_antisymm ?_ (ciSup_le hle)
  rw [← re_quadForm_of_mulVec_eq_smul hu hAu]
  exact le_ciSup (f := fun x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} =>
    RCLike.re (quadForm A x.1)) ⟨eigenvalue A 0, by rintro _ ⟨x, rfl⟩; exact hle x⟩ ⟨u, hu⟩

/-- The smallest eigenvalue of a Hermitian matrix is the infimum of its quadratic form over
unit vectors. [HornJohnson2013, Theorem 4.2.2].
Port of `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf`.
Result: rayleigh-ritz -/
theorem _root_.Matrix.IsHermitian.eigenvalue_last_eq_iInf {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k + 1 = Fintype.card n) :
    eigenvalue A k = ⨅ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) := by
  obtain ⟨u, hu, hAu⟩ := hA.exists_norm_eq_one_and_mulVec_eq (k := k) (by omega)
  have : Nonempty {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} := ⟨⟨u, hu⟩⟩
  have hle : ∀ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1},
      eigenvalue A k ≤ RCLike.re (quadForm A x.1) := fun x => by
    have h := hA.eigenvalue_last_mul_le_re_quadForm hk x.1
    rwa [x.2, one_pow, mul_one] at h
  refine le_antisymm (le_ciInf hle) ?_
  rw [← re_quadForm_of_mulVec_eq_smul hu hAu]
  exact ciInf_le (f := fun x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} =>
    RCLike.re (quadForm A x.1)) ⟨eigenvalue A k, by rintro _ ⟨x, rfl⟩; exact hle x⟩ ⟨u, hu⟩

/-! ### The spectral norm of a Hermitian matrix -/

/-- Every eigenvalue of a Hermitian matrix is bounded in absolute value by the spectral norm. -/
theorem _root_.Matrix.IsHermitian.abs_eigenvalue_le_specNorm {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : ℕ) : |eigenvalue A k| ≤ specNorm A := by
  rcases lt_or_ge k (Fintype.card n) with hk | hk
  · obtain ⟨u, hu, hAu⟩ := hA.exists_norm_eq_one_and_mulVec_eq hk
    rw [← re_quadForm_of_mulVec_eq_smul hu hAu]
    exact abs_re_quadForm_le_specNorm A hu
  · rw [eigenvalue_of_card_le A hk, abs_zero]
    exact specNorm_nonneg A

/-- The spectral norm of a Hermitian matrix is the larger of the absolute values of its extreme
eigenvalues. Port of `NLAlib.specNorm_eq_norm_eigenvalue`, there over `ℝ` as a supremum over the
unsorted eigenvalues. -/
theorem _root_.Matrix.IsHermitian.specNorm_eq_max {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    specNorm A = max |eigenvalue A 0| |eigenvalue A k| := by
  refine le_antisymm ?_
    (max_le (hA.abs_eigenvalue_le_specNorm 0) (hA.abs_eigenvalue_le_specNorm k))
  rw [hA.specNorm_le_iff_abs_re_quadForm_le (le_max_of_le_left (abs_nonneg _))]
  intro x
  have h0 := hA.re_quadForm_le_eigenvalue_zero_mul x
  have hk' := hA.eigenvalue_last_mul_le_re_quadForm hk x
  have hx := sq_nonneg ‖WithLp.toLp 2 x‖
  rw [abs_le]
  constructor
  · refine le_trans ?_ hk'
    rw [← neg_mul]
    exact mul_le_mul_of_nonneg_right
      ((neg_le_neg (le_max_right _ _)).trans (neg_abs_le _)) hx
  · exact h0.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_max_left _ _)) hx)

/-- The spectral norm of a positive semidefinite matrix is its largest eigenvalue. -/
theorem _root_.Matrix.PosSemidef.specNorm_eq_eigenvalue_zero {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : specNorm A = eigenvalue A 0 := by
  classical
  refine le_antisymm ?_
    ((le_abs_self _).trans (hA.isHermitian.abs_eigenvalue_le_specNorm 0))
  rw [hA.specNorm_le_iff (hA.eigenvalue_nonneg 0)]
  exact hA.isHermitian.le_eigenvalue_zero_smul_one

/-- A positive semidefinite matrix has a unit eigenvector for its spectral norm.
Port of `NLAlib.exists_unit_mulVec_eq_specNorm_smul`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.exists_norm_eq_one_and_mulVec_eq_specNorm_smul [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    ∃ u : n → 𝕜, ‖WithLp.toLp 2 u‖ = 1 ∧ A *ᵥ u = specNorm A • u := by
  rw [hA.specNorm_eq_eigenvalue_zero]
  exact hA.isHermitian.exists_norm_eq_one_and_mulVec_eq Fintype.card_pos

end NLAlib
