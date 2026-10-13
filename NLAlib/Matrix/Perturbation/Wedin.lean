/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.DavisKahan
public import NLAlib.Matrix.Spectral.LowRank

/-!
# Wedin's theorem for singular subspaces

The analogue of the `sin Θ` theorem for the singular subspaces of a rectangular matrix. The left
and right subspaces are coupled, so the Sylvester equation is replaced by a coupled pair.

The basic statement is in residual form. Let `U`, `V` be frames of left and right singular
vectors of `A` for its `j + 1` largest singular values, and let `(U', V', S)` be any approximate
singular triple with `S` bounded below by `α`. Then
`(α - σ_{j+1}(A)) max (‖(1 - U Uᴴ) U'‖, ‖(1 - V Vᴴ) V'‖) ≤ max (‖A V' - U' S‖, ‖Aᴴ U' - V' Sᴴ‖)`.
The perturbation theorem is the case where `(U', V', S)` is exact for `A + E`.

## Main results

* `NLAlib.SymmetricGauge.sub_mul_max_matrixNorm_le_max`: the coupled separation bound.
* `NLAlib.SymmetricGauge.sub_mul_max_matrixNorm_one_sub_mul_le_max`: Wedin's theorem in residual
  form, every unitarily invariant norm.
* `NLAlib.SymmetricGauge.mul_max_matrixNorm_one_sub_mul_le_of_singularValues_sub`: the leading
  singular subspaces of `A` and `A + E`.
* `NLAlib.sub_sq_mul_frobNorm_one_sub_mul_sq_add_le`,
  `NLAlib.sq_mul_frobNorm_one_sub_mul_sq_add_le_of_singularValues_sub`: the Frobenius forms.
* `NLAlib.max_specNorm_one_sub_mul_le_two_mul_specNorm_div_singularGap`: the bound with the gap of
  the unperturbed matrix only.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-! ### Coupled separation bounds -/

omit [DecidableEq m] [DecidableEq n] in
/-- One of the two inequalities behind the coupled bound: `α ‖X‖ ≤ β ‖Y‖ + ‖D Y - X T‖`. -/
private theorem mul_matrixNorm_le_mul_matrixNorm_add (Φ : SymmetricGauge) {D : Matrix m n 𝕜}
    {T : Matrix p p 𝕜} {α β : ℝ} (hT : (α ^ 2) • (1 : Matrix p p 𝕜) ≤ T * Tᴴ)
    (hD : specNorm D ≤ β) (X : Matrix m p 𝕜) (Y : Matrix n p 𝕜) :
    α * Φ.matrixNorm X ≤ β * Φ.matrixNorm Y + Φ.matrixNorm (D * Y - X * T) := by
  have h₁ := Φ.mul_matrixNorm_le_matrixNorm_mul_sub_mul (L := Tᴴ) (M := (0 : Matrix m m 𝕜))
    (r := 0) (δ := α) (by rw [specNorm_zero])
    (by rwa [zero_add, Matrix.conjTranspose_conjTranspose]) Xᴴ
  rw [Matrix.mul_zero, sub_zero, ← Matrix.conjTranspose_mul, Φ.matrixNorm_conjTranspose,
    Φ.matrixNorm_conjTranspose] at h₁
  have h₂ : Φ.matrixNorm (X * T) ≤ Φ.matrixNorm (D * Y) + Φ.matrixNorm (D * Y - X * T) := by
    have h := Φ.matrixNorm_add_le (D * Y) (-(D * Y - X * T))
    rwa [Φ.matrixNorm_neg, ← sub_eq_add_neg, sub_sub_cancel] at h
  have h₃ : Φ.matrixNorm (D * Y) ≤ β * Φ.matrixNorm Y :=
    (Φ.matrixNorm_mul_le_specNorm_mul D Y).trans
      (mul_le_mul_of_nonneg_right hD (Φ.matrixNorm_nonneg Y))
  linarith

/-- The scalar step of the Frobenius coupled bound: the triangle inequality in the plane. -/
private theorem sub_sq_mul_add_sq_le_add_sq {α β x y a b : ℝ} (hβ : 0 ≤ β) (hαβ : β ≤ α)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h₁ : α * x ≤ β * y + a) (h₂ : α * y ≤ β * x + b) :
    (α - β) ^ 2 * (x ^ 2 + y ^ 2) ≤ a ^ 2 + b ^ 2 := by
  have hα : 0 ≤ α := hβ.trans hαβ
  have hr : √(x ^ 2 + y ^ 2) ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  have hs : √(a ^ 2 + b ^ 2) ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hr₀ := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  have hs₀ := Real.sqrt_nonneg (a ^ 2 + b ^ 2)
  generalize √(x ^ 2 + y ^ 2) = r at hr hr₀
  generalize √(a ^ 2 + b ^ 2) = s at hs hs₀
  have hcs : y * a + x * b ≤ r * s := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hr₀ hs₀) ?_
    rw [mul_pow, hr, hs]
    nlinarith [sq_nonneg (y * b - x * a)]
  have h₃ : (α * r) ^ 2 ≤ (β * r + s) ^ 2 := by
    have e₁ : (α * x) ^ 2 ≤ (β * y + a) ^ 2 := pow_le_pow_left₀ (mul_nonneg hα hx) h₁ 2
    have e₂ : (α * y) ^ 2 ≤ (β * x + b) ^ 2 := pow_le_pow_left₀ (mul_nonneg hα hy) h₂ 2
    have e₃ := mul_le_mul_of_nonneg_left hcs hβ
    have e₄ : (α * r) ^ 2 = (α * x) ^ 2 + (α * y) ^ 2 := by
      rw [mul_pow, hr]
      ring
    have e₅ : (β * r + s) ^ 2 =
        β ^ 2 * (x ^ 2 + y ^ 2) + 2 * (β * (r * s)) + (a ^ 2 + b ^ 2) := by
      rw [← hr, ← hs]
      ring
    rw [e₄, e₅]
    linarith
  have h₄ : α * r ≤ β * r + s :=
    le_of_pow_le_pow_left₀ two_ne_zero (add_nonneg (mul_nonneg hβ hr₀) hs₀) h₃
  have h₅ : (α - β) * r ≤ s := by linarith
  have h₆ := pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr hαβ) hr₀) h₅ 2
  rwa [mul_pow, hr, hs] at h₆

omit [DecidableEq m] [DecidableEq n] in
/-- **Coupled separation bound.** If the square matrix `T` is bounded below by `α`
(`α² • 1 ≤ Tᴴ T`) and `‖D‖₂ ≤ β`, then for every pair `X`, `Y`, in every unitarily invariant
norm, `(α - β) max (‖X‖, ‖Y‖) ≤ max (‖D Y - X T‖, ‖Dᴴ X - Y Tᴴ‖)`. No sign condition on `α` is
needed: the bound is trivial for `α < β`.
[Wedin1972]; [StewartSun1990, §V.4].
Port of `NLAlib.sub_mul_max_specNorm_le_max_coupled_residual`, there over `ℝ` in the spectral
norm with diagonal `T`. -/
theorem SymmetricGauge.sub_mul_max_matrixNorm_le_max (Φ : SymmetricGauge) {D : Matrix m n 𝕜}
    {T : Matrix p p 𝕜} {α β : ℝ} (hT : (α ^ 2) • (1 : Matrix p p 𝕜) ≤ Tᴴ * T)
    (hD : specNorm D ≤ β) (X : Matrix m p 𝕜) (Y : Matrix n p 𝕜) :
    (α - β) * max (Φ.matrixNorm X) (Φ.matrixNorm Y) ≤
      max (Φ.matrixNorm (D * Y - X * T)) (Φ.matrixNorm (Dᴴ * X - Y * Tᴴ)) := by
  have hβ : 0 ≤ β := (specNorm_nonneg D).trans hD
  have h₁ := mul_matrixNorm_le_mul_matrixNorm_add Φ
    (smul_one_le_mul_conjTranspose_self_of_smul_one_le hT) hD X Y
  have h₂ := mul_matrixNorm_le_mul_matrixNorm_add Φ (D := Dᴴ) (T := Tᴴ) (β := β)
    (by rwa [Matrix.conjTranspose_conjTranspose]) (by rwa [specNorm_conjTranspose]) Y X
  rcases le_total (Φ.matrixNorm X) (Φ.matrixNorm Y) with h | h
  · rw [max_eq_right h]
    refine le_trans ?_ (le_max_right _ _)
    linarith [mul_le_mul_of_nonneg_left h hβ]
  · rw [max_eq_left h]
    refine le_trans ?_ (le_max_left _ _)
    linarith [mul_le_mul_of_nonneg_left h hβ]

omit [DecidableEq m] [DecidableEq n] in
/-- The coupled separation bound in the Frobenius norm, for the sum of squares:
`(α - β)² (‖X‖_F² + ‖Y‖_F²) ≤ ‖D Y - X T‖_F² + ‖Dᴴ X - Y Tᴴ‖_F²` when `β ≤ α`.
[Wedin1972].
Port of `NLAlib.sub_sq_mul_add_sq_frobNorm_le_add_sq_coupled_residual`. -/
theorem sub_sq_mul_frobNorm_sq_add_frobNorm_sq_le {D : Matrix m n 𝕜} {T : Matrix p p 𝕜}
    {α β : ℝ} (hαβ : β ≤ α) (hT : (α ^ 2) • (1 : Matrix p p 𝕜) ≤ Tᴴ * T)
    (hD : specNorm D ≤ β) (X : Matrix m p 𝕜) (Y : Matrix n p 𝕜) :
    (α - β) ^ 2 * (frobNorm X ^ 2 + frobNorm Y ^ 2) ≤
      frobNorm (D * Y - X * T) ^ 2 + frobNorm (Dᴴ * X - Y * Tᴴ) ^ 2 := by
  have h₁ := mul_matrixNorm_le_mul_matrixNorm_add (lpGauge 2 one_le_two)
    (smul_one_le_mul_conjTranspose_self_of_smul_one_le hT) hD X Y
  have h₂ := mul_matrixNorm_le_mul_matrixNorm_add (lpGauge 2 one_le_two) (D := Dᴴ) (T := Tᴴ)
    (β := β) (by rwa [Matrix.conjTranspose_conjTranspose]) (by rwa [specNorm_conjTranspose]) Y X
  simp only [lpGauge_two_matrixNorm] at h₁ h₂
  exact sub_sq_mul_add_sq_le_add_sq ((specNorm_nonneg D).trans hD) hαβ (frobNorm_nonneg X)
    (frobNorm_nonneg Y) h₁ h₂

/-! ### The part of a matrix outside its leading singular subspaces -/

omit [Fintype p] in
private theorem conjTranspose_diagonal_ofReal (σ : p → ℝ) :
    (Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜))ᴴ = Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜) := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  exact RCLike.conj_ofReal _

omit [Fintype n] [DecidableEq m] [DecidableEq n] in
/-- The second singular vector equation in the form `Uᴴ * A = Σ * Vᴴ`. -/
private theorem conjTranspose_mul_eq_diagonal_mul {A : Matrix m n 𝕜} {U : Matrix m p 𝕜}
    {V : Matrix n p 𝕜} {σ : p → ℝ}
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) :
    Uᴴ * A = (Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) * Vᴴ := by
  have h := congrArg Matrix.conjTranspose hAU
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    conjTranspose_diagonal_ofReal] at h

/-- The right complement alone already removes the leading part:
`(1 - U Uᴴ) A (1 - V Vᴴ) = A (1 - V Vᴴ)`. -/
private theorem one_sub_mul_mul_one_sub_eq_mul_one_sub {A : Matrix m n 𝕜} {U : Matrix m p 𝕜}
    {V : Matrix n p 𝕜} {σ : p → ℝ} (hV : HasOrthonormalCols V)
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) :
    (1 - U * Uᴴ) * A * (1 - V * Vᴴ) = A * (1 - V * Vᴴ) := by
  have h : Uᴴ * A * (1 - V * Vᴴ) = 0 := by
    rw [conjTranspose_mul_eq_diagonal_mul hAU, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
      ← Matrix.mul_assoc Vᴴ, hV.conjTranspose_mul_self, Matrix.one_mul, sub_self, Matrix.mul_zero]
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc U, Matrix.mul_assoc U, h,
    Matrix.mul_zero, sub_zero]

/-- The left complement alone already removes the leading part:
`(1 - U Uᴴ) A (1 - V Vᴴ) = (1 - U Uᴴ) A`. -/
private theorem one_sub_mul_mul_one_sub_eq_one_sub_mul {A : Matrix m n 𝕜} {U : Matrix m p 𝕜}
    {V : Matrix n p 𝕜} {σ : p → ℝ} (hU : HasOrthonormalCols U)
    (hAV : A * V = U * Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) :
    (1 - U * Uᴴ) * A * (1 - V * Vᴴ) = (1 - U * Uᴴ) * A := by
  have h : (1 - U * Uᴴ) * A * V = 0 := by
    rw [Matrix.mul_assoc, hAV, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc U, hU.conjTranspose_mul_self, Matrix.mul_one, sub_self, Matrix.zero_mul]
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h, Matrix.zero_mul, sub_zero]

/-- The first residual of Wedin's coupled pair, for the compression `D = (1 - U Uᴴ) A (1 - V Vᴴ)`
and the components of `U'`, `V'` outside the leading subspaces. -/
private theorem one_sub_mul_mul_one_sub_mul_sub {A : Matrix m n 𝕜} {U : Matrix m p 𝕜}
    {V : Matrix n p 𝕜} {σ : p → ℝ} {q : Type*} [Fintype q] (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) (hAV : A * V = U * Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) (U' : Matrix m q 𝕜)
    (V' : Matrix n q 𝕜) (S : Matrix q q 𝕜) :
    (1 - U * Uᴴ) * A * (1 - V * Vᴴ) * ((1 - V * Vᴴ) * V') - (1 - U * Uᴴ) * U' * S =
      (1 - U * Uᴴ) * (A * V' - U' * S) := by
  have hPV : IsStarProjection (1 - V * Vᴴ) := hV.isStarProjection_mul_conjTranspose.one_sub
  rw [one_sub_mul_mul_one_sub_eq_mul_one_sub hV hAU, Matrix.mul_assoc A, ← Matrix.mul_assoc _ _ V',
    hPV.mul_self, ← Matrix.mul_assoc, ← one_sub_mul_mul_one_sub_eq_mul_one_sub hV hAU,
    one_sub_mul_mul_one_sub_eq_one_sub_mul hU hAV, Matrix.mul_sub, Matrix.mul_assoc,
    Matrix.mul_assoc]

/-- The second residual of Wedin's coupled pair. -/
private theorem conjTranspose_one_sub_mul_mul_one_sub_mul_sub {A : Matrix m n 𝕜}
    {U : Matrix m p 𝕜} {V : Matrix n p 𝕜} {σ : p → ℝ} {q : Type*} [Fintype q]
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hAV : A * V = U * Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜)) (U' : Matrix m q 𝕜)
    (V' : Matrix n q 𝕜) (S : Matrix q q 𝕜) :
    ((1 - U * Uᴴ) * A * (1 - V * Vᴴ))ᴴ * ((1 - U * Uᴴ) * U') - (1 - V * Vᴴ) * V' * S =
      (1 - V * Vᴴ) * (Aᴴ * U' - V' * S) := by
  have hPU : IsStarProjection (1 - U * Uᴴ) := hU.isStarProjection_mul_conjTranspose.one_sub
  have hPV : IsStarProjection (1 - V * Vᴴ) := hV.isStarProjection_mul_conjTranspose.one_sub
  have e : ((1 - U * Uᴴ) * A * (1 - V * Vᴴ))ᴴ * ((1 - U * Uᴴ) * U') =
      ((1 - U * Uᴴ) * A * (1 - V * Vᴴ))ᴴ * U' := by
    rw [one_sub_mul_mul_one_sub_eq_one_sub_mul hU hAV, Matrix.conjTranspose_mul,
      hPU.conjTranspose_eq, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ U', hPU.mul_self,
      Matrix.mul_assoc]
  rw [e, one_sub_mul_mul_one_sub_eq_mul_one_sub hV hAU, Matrix.conjTranspose_mul,
    hPV.conjTranspose_eq, Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc]

/-- A real diagonal matrix with entries at least `α ≥ 0` is bounded below by `α`. -/
private theorem sq_smul_one_le_conjTranspose_diagonal_mul_self {σ : p → ℝ} {α : ℝ} (hα : 0 ≤ α)
    (h : ∀ i, α ≤ σ i) :
    (α ^ 2) • (1 : Matrix p p 𝕜) ≤
      (Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜))ᴴ * Matrix.diagonal fun i => ((σ i : ℝ) : 𝕜) := by
  rw [smul_one_le_conjTranspose_mul_self_iff]
  intro x
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Matrix.mulVec_diagonal, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hα (h i) 2) (sq_nonneg _)

/-- If `A * V = U * Σ` and `Aᴴ * U = V * Σ` for a frame `V` and `Σ` the diagonal matrix of the
`j + 1` largest singular values, then the remainder is the compression of `A` to the
complements: `A - U Σ Vᴴ = (1 - U Uᴴ) A (1 - V Vᴴ)`. Orthonormality of the columns of `U` is not
needed. -/
theorem sub_mul_diagonal_mul_conjTranspose_eq {A : Matrix m n 𝕜} {j : ℕ}
    {U : Matrix m (Fin (j + 1)) 𝕜} {V : Matrix n (Fin (j + 1)) 𝕜} (hV : HasOrthonormalCols V)
    (hAV : A * V = U * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜)) :
    A - U * (Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜)) * Vᴴ =
      (1 - U * Uᴴ) * A * (1 - V * Vᴴ) := by
  rw [one_sub_mul_mul_one_sub_eq_mul_one_sub hV hAU, Matrix.mul_sub, Matrix.mul_one,
    ← Matrix.mul_assoc, hAV]

/-- **The complement of leading singular frames.** Under the same hypotheses the compression of
`A` to the complements has spectral norm `σ_{j+1}(A)`. This holds with repeated singular
values. -/
theorem specNorm_one_sub_mul_mul_one_sub_of_mul_eq_mul_diagonal {A : Matrix m n 𝕜} {j : ℕ}
    {U : Matrix m (Fin (j + 1)) 𝕜} {V : Matrix n (Fin (j + 1)) 𝕜} (hV : HasOrthonormalCols V)
    (hAV : A * V = U * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜)) :
    specNorm ((1 - U * Uᴴ) * A * (1 - V * Vᴴ)) = singularValues A (j + 1) := by
  refine le_antisymm ?_ ?_
  · have hAAV : Aᴴ * A * V =
        V * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue (Aᴴ * A) i : ℝ) : 𝕜) := by
      rw [Matrix.mul_assoc, hAV, ← Matrix.mul_assoc, hAU, Matrix.mul_assoc,
        Matrix.diagonal_mul_diagonal]
      congr 2
      ext i
      rw [← sq_singularValues, RCLike.ofReal_pow, sq]
    have hP : IsStarProjection (1 - V * Vᴴ) := hV.isStarProjection_mul_conjTranspose.one_sub
    have h₁ := one_sub_mul_mul_one_sub_le_of_mul_eq_mul_diagonal
      (Matrix.isHermitian_conjTranspose_mul_self A) hV hAAV
    have h₂ : eigenvalue (Aᴴ * A) (j + 1) • (1 - V * Vᴴ) ≤
        eigenvalue (Aᴴ * A) (j + 1) • (1 : Matrix n n 𝕜) := by
      rw [Matrix.le_iff, ← smul_sub, sub_sub_cancel]
      refine (Matrix.posSemidef_self_mul_conjTranspose V).smul ?_
      rw [← sq_singularValues]
      exact sq_nonneg _
    have h₃ := h₁.trans h₂
    rw [← sq_singularValues, ← Matrix.mul_assoc] at h₃
    nth_rewrite 1 [← hP.isHermitian.eq] at h₃
    rw [Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      ← specNorm_sq_le_iff_conjTranspose_mul_self_le (sq_nonneg _)] at h₃
    rw [one_sub_mul_mul_one_sub_eq_mul_one_sub hV hAU]
    exact le_of_pow_le_pow_left₀ two_ne_zero (singularValues_nonneg A (j + 1)) h₃
  · rw [← sub_mul_diagonal_mul_conjTranspose_eq hV hAV hAU]
    refine singularValues_le_specNorm_sub_of_rank_le A ?_
    rw [Matrix.mul_assoc]
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_le_card_width U).trans_eq (Fintype.card_fin _))

/-! ### Wedin's theorem -/

omit [Fintype m] [DecidableEq m] [DecidableEq n] [Fintype p] [DecidableEq p] in
/-- The residual of an exact pair for `A + E`, seen from `A`, is `-(E * V)`. -/
private theorem sub_eq_neg_mul_of_add_mul_eq {A E : Matrix m n 𝕜} {V : Matrix n p 𝕜}
    {B : Matrix m p 𝕜} (h : (A + E) * V = B) : A * V - B = -(E * V) := by
  rw [← h, Matrix.add_mul]
  abel

/-- **Wedin's `sin Θ` theorem, residual form.** Let `U`, `V` be frames of left and right
singular vectors of `A` for its `j + 1` largest singular values. For any triple `(U', V', S)`
with `S` bounded below by `α` (`α² • 1 ≤ Sᴴ S`), in every unitarily invariant norm
`(α - σ_{j+1}(A)) max (‖(1 - U Uᴴ) U'‖, ‖(1 - V Vᴴ) V'‖) ≤ max (‖A V' - U' S‖, ‖Aᴴ U' - V' Sᴴ‖)`.
[Wedin1972]; [StewartSun1990, Theorem V.4.1].
Port of `NLAlib.max_specNorm_sinePrincipalAngles_le_max_residual_div`, there over `ℝ` in the
spectral norm with square SVD factors.
Result: wedin -/
theorem SymmetricGauge.sub_mul_max_matrixNorm_one_sub_mul_le_max (Φ : SymmetricGauge)
    {A : Matrix m n 𝕜} {j : ℕ} {U : Matrix m (Fin (j + 1)) 𝕜} {V : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hAV : A * V = U * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    {S : Matrix p p 𝕜} {α : ℝ} (hS : (α ^ 2) • (1 : Matrix p p 𝕜) ≤ Sᴴ * S)
    (U' : Matrix m p 𝕜) (V' : Matrix n p 𝕜) :
    (α - singularValues A (j + 1)) *
        max (Φ.matrixNorm ((1 - U * Uᴴ) * U')) (Φ.matrixNorm ((1 - V * Vᴴ) * V')) ≤
      max (Φ.matrixNorm (A * V' - U' * S)) (Φ.matrixNorm (Aᴴ * U' - V' * Sᴴ)) := by
  have hPU : IsStarProjection (1 - U * Uᴴ) := hU.isStarProjection_mul_conjTranspose.one_sub
  have hPV : IsStarProjection (1 - V * Vᴴ) := hV.isStarProjection_mul_conjTranspose.one_sub
  have h := Φ.sub_mul_max_matrixNorm_le_max hS
    (specNorm_one_sub_mul_mul_one_sub_of_mul_eq_mul_diagonal hV hAV hAU).le
    ((1 - U * Uᴴ) * U') ((1 - V * Vᴴ) * V')
  rw [one_sub_mul_mul_one_sub_mul_sub hU hV hAV hAU,
    conjTranspose_one_sub_mul_mul_one_sub_mul_sub hU hV hAV hAU] at h
  exact h.trans (max_le_max (Φ.matrixNorm_mul_le_of_isStarProjection hPU _)
    (Φ.matrixNorm_mul_le_of_isStarProjection hPV _))

/-- **Wedin's `sin Θ` theorem, residual form, Frobenius norm.** Let `U`, `V` be frames of left
and right singular vectors of `A` for its `j + 1` largest singular values. For any triple
`(U', V', S)` with `S` bounded below by `α ≥ σ_{j+1}(A)` (`α² • 1 ≤ Sᴴ S`),
`(α - σ_{j+1}(A))² (‖(1 - U Uᴴ) U'‖_F² + ‖(1 - V Vᴴ) V'‖_F²) ≤
‖A V' - U' S‖_F² + ‖Aᴴ U' - V' Sᴴ‖_F²`.
[Wedin1972]; [StewartSun1990, Theorem V.4.1].
Result: wedin -/
theorem sub_sq_mul_frobNorm_one_sub_mul_sq_add_le {A : Matrix m n 𝕜} {j : ℕ}
    {U : Matrix m (Fin (j + 1)) 𝕜} {V : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hAV : A * V = U * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    {S : Matrix p p 𝕜} {α : ℝ} (hα : singularValues A (j + 1) ≤ α)
    (hS : (α ^ 2) • (1 : Matrix p p 𝕜) ≤ Sᴴ * S) (U' : Matrix m p 𝕜) (V' : Matrix n p 𝕜) :
    (α - singularValues A (j + 1)) ^ 2 *
        (frobNorm ((1 - U * Uᴴ) * U') ^ 2 + frobNorm ((1 - V * Vᴴ) * V') ^ 2) ≤
      frobNorm (A * V' - U' * S) ^ 2 + frobNorm (Aᴴ * U' - V' * Sᴴ) ^ 2 := by
  have hPU : IsStarProjection (1 - U * Uᴴ) := hU.isStarProjection_mul_conjTranspose.one_sub
  have hPV : IsStarProjection (1 - V * Vᴴ) := hV.isStarProjection_mul_conjTranspose.one_sub
  have h := sub_sq_mul_frobNorm_sq_add_frobNorm_sq_le hα hS
    (specNorm_one_sub_mul_mul_one_sub_of_mul_eq_mul_diagonal hV hAV hAU).le
    ((1 - U * Uᴴ) * U') ((1 - V * Vᴴ) * V')
  rw [one_sub_mul_mul_one_sub_mul_sub hU hV hAV hAU,
    conjTranspose_one_sub_mul_mul_one_sub_mul_sub hU hV hAV hAU] at h
  exact h.trans (add_le_add (pow_le_pow_left₀ (frobNorm_nonneg _) (hPU.frobNorm_mul_le _) 2)
    (pow_le_pow_left₀ (frobNorm_nonneg _) (hPV.frobNorm_mul_le _) 2))

/-- **Wedin's `sin Θ` theorem.** Let `U`, `V` be frames of left and right singular vectors of `A`
for its `j + 1` largest singular values, and `U'`, `V'` the same for `A + E`. If
`δ ≤ σ_j(A + E) - σ_{j+1}(A)`, then in every unitarily invariant norm
`δ max (‖(1 - U Uᴴ) U'‖, ‖(1 - V Vᴴ) V'‖) ≤ max (‖E V'‖, ‖Eᴴ U'‖)`.
[Wedin1972]; [StewartSun1990, Theorem V.4.1].
Port of `NLAlib.max_specNorm_sinePrincipalAngles_le_max_perturbation_frame_div`, there over `ℝ`
in the spectral norm with square SVD factors.
Result: wedin -/
theorem SymmetricGauge.mul_max_matrixNorm_one_sub_mul_le_of_singularValues_sub
    (Φ : SymmetricGauge) {A E : Matrix m n 𝕜} {j : ℕ} {U U' : Matrix m (Fin (j + 1)) 𝕜}
    {V V' : Matrix n (Fin (j + 1)) 𝕜} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hAV : A * V = U * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAV' : (A + E) * V' =
      U' * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues (A + E) i : ℝ) : 𝕜))
    (hAU' : (A + E)ᴴ * U' =
      V' * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues (A + E) i : ℝ) : 𝕜))
    {δ : ℝ} (hδ : δ ≤ singularValues (A + E) j - singularValues A (j + 1)) :
    δ * max (Φ.matrixNorm ((1 - U * Uᴴ) * U')) (Φ.matrixNorm ((1 - V * Vᴴ) * V')) ≤
      max (Φ.matrixNorm (E * V')) (Φ.matrixNorm (Eᴴ * U')) := by
  have hS := sq_smul_one_le_conjTranspose_diagonal_mul_self (𝕜 := 𝕜)
    (σ := fun i : Fin (j + 1) => singularValues (A + E) i) (singularValues_nonneg (A + E) j)
    fun i => singularValues_antitone (A + E) (Nat.lt_succ_iff.mp i.2)
  have h := Φ.sub_mul_max_matrixNorm_one_sub_mul_le_max hU hV hAV hAU hS U' V'
  rw [conjTranspose_diagonal_ofReal, sub_eq_neg_mul_of_add_mul_eq hAV',
    sub_eq_neg_mul_of_add_mul_eq (by rwa [Matrix.conjTranspose_add] at hAU'), Φ.matrixNorm_neg,
    Φ.matrixNorm_neg] at h
  exact (mul_le_mul_of_nonneg_right hδ (le_max_of_le_left (Φ.matrixNorm_nonneg _))).trans h

/-- **Wedin's theorem in the Frobenius norm**:
`δ² (‖(1 - U Uᴴ) U'‖_F² + ‖(1 - V Vᴴ) V'‖_F²) ≤ ‖E V'‖_F² + ‖Eᴴ U'‖_F²` for
`0 ≤ δ ≤ σ_j(A + E) - σ_{j+1}(A)`.
[Wedin1972]; [StewartSun1990, Theorem V.4.1].
Port of `NLAlib.sqrt_add_sq_frobNorm_sinePrincipalAngles_le_sqrt_add_sq_perturbation_frame_div`.
Result: wedin -/
theorem sq_mul_frobNorm_one_sub_mul_sq_add_le_of_singularValues_sub {A E : Matrix m n 𝕜}
    {j : ℕ} {U U' : Matrix m (Fin (j + 1)) 𝕜} {V V' : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hAV : A * V = U * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAV' : (A + E) * V' =
      U' * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues (A + E) i : ℝ) : 𝕜))
    (hAU' : (A + E)ᴴ * U' =
      V' * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues (A + E) i : ℝ) : 𝕜))
    {δ : ℝ} (hδ₀ : 0 ≤ δ) (hδ : δ ≤ singularValues (A + E) j - singularValues A (j + 1)) :
    δ ^ 2 * (frobNorm ((1 - U * Uᴴ) * U') ^ 2 + frobNorm ((1 - V * Vᴴ) * V') ^ 2) ≤
      frobNorm (E * V') ^ 2 + frobNorm (Eᴴ * U') ^ 2 := by
  have hS := sq_smul_one_le_conjTranspose_diagonal_mul_self (𝕜 := 𝕜)
    (σ := fun i : Fin (j + 1) => singularValues (A + E) i) (singularValues_nonneg (A + E) j)
    fun i => singularValues_antitone (A + E) (Nat.lt_succ_iff.mp i.2)
  have h := sub_sq_mul_frobNorm_one_sub_mul_sq_add_le hU hV hAV hAU (by linarith) hS U' V'
  rw [conjTranspose_diagonal_ofReal, sub_eq_neg_mul_of_add_mul_eq hAV',
    sub_eq_neg_mul_of_add_mul_eq (by rwa [Matrix.conjTranspose_add] at hAU'), frobNorm_neg,
    frobNorm_neg] at h
  have h₃ : δ ^ 2 ≤ (singularValues (A + E) j - singularValues A (j + 1)) ^ 2 :=
    pow_le_pow_left₀ hδ₀ hδ 2
  exact (mul_le_mul_of_nonneg_right h₃ (by positivity)).trans h

/-- **Wedin's theorem with the gap of the unperturbed matrix**, spectral norm:
`max (‖(1 - U Uᴴ) U'‖₂, ‖(1 - V Vᴴ) V'‖₂) ≤ 2 ‖E‖₂ / (σ_j(A) - σ_{j+1}(A))`, for frames with
orthonormal columns on both sides.
Port of `NLAlib.max_specNorm_sinePrincipalAngles_le_two_mul_specNorm_div_population_gap`.
Result: wedin -/
theorem max_specNorm_one_sub_mul_le_two_mul_specNorm_div_singularGap {A E : Matrix m n 𝕜}
    {j : ℕ} {U U' : Matrix m (Fin (j + 1)) 𝕜} {V V' : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (hU' : HasOrthonormalCols U')
    (hV' : HasOrthonormalCols V')
    (hAV : A * V = U * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAU : Aᴴ * U = V * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues A i : ℝ) : 𝕜))
    (hAV' : (A + E) * V' =
      U' * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues (A + E) i : ℝ) : 𝕜))
    (hAU' : (A + E)ᴴ * U' =
      V' * Matrix.diagonal fun i : Fin (j + 1) => ((singularValues (A + E) i : ℝ) : 𝕜))
    (hgap : 0 < singularGap A (j + 1)) :
    max (specNorm ((1 - U * Uᴴ) * U')) (specNorm ((1 - V * Vᴴ) * V')) ≤
      2 * specNorm E / singularGap A (j + 1) := by
  rw [singularGap_succ] at hgap ⊢
  rw [le_div_iff₀ hgap]
  have hM₀ : 0 ≤ max (specNorm ((1 - U * Uᴴ) * U')) (specNorm ((1 - V * Vᴴ) * V')) :=
    le_max_of_le_left (specNorm_nonneg _)
  have hM₁ : max (specNorm ((1 - U * Uᴴ) * U')) (specNorm ((1 - V * Vᴴ) * V')) ≤ 1 := max_le
    ((hU.isStarProjection_mul_conjTranspose.one_sub.specNorm_mul_le U').trans hU'.specNorm_le_one)
    ((hV.isStarProjection_mul_conjTranspose.one_sub.specNorm_mul_le V').trans hV'.specNorm_le_one)
  have hweyl := abs_singularValues_sub_le_specNorm (A + E) A j
  rw [add_sub_cancel_left] at hweyl
  have h := (lpGauge ⊤ le_top).mul_max_matrixNorm_one_sub_mul_le_of_singularValues_sub hU hV hAV
    hAU hAV' hAU' le_rfl
  simp only [lpGauge_top_matrixNorm] at h
  have hE : max (specNorm (E * V')) (specNorm (Eᴴ * U')) ≤ specNorm E := max_le
    (hV'.specNorm_mul_right_le E)
    ((hU'.specNorm_mul_right_le Eᴴ).trans_eq (specNorm_conjTranspose E))
  generalize max (specNorm ((1 - U * Uᴴ) * U')) (specNorm ((1 - V * Vᴴ) * V')) = M at *
  have h₁ := mul_le_mul_of_nonneg_right (sub_le_of_abs_sub_le_left hweyl) hM₀
  have h₂ := mul_le_mul_of_nonneg_left hM₁ (specNorm_nonneg E)
  linarith

end NLAlib
