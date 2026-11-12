/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean norms of coordinate vectors

Bridges between the Euclidean norm $\|\mathbf{x}\|$ (`‖WithLp.toLp 2 x‖`) of a vector
`x : n → 𝕜` and the pairing $\mathbf{x}^{\mathsf{H}}\mathbf{x}$ (`star x ⬝ᵥ x`), the
Cauchy–Schwarz inequality for the dot product, the behaviour of that norm under conjugation,
reindexing, extension by zero, concatenation and scaling by $\lvert k \rvert^{-1/2}$, and the
Lipschitz condition for the Euclidean norm read on coordinate vectors. Componentwise arithmetic
envelopes give normwise update, dot-product and normalization error bounds. Upstream candidates for
`Mathlib.Analysis.InnerProductSpace.PiL2`.

## Main results

* `EuclideanSpace.norm_le_norm_toLp`: the sup norm is at most the Euclidean norm.
* `EuclideanSpace.norm_toLp_add_le`, `EuclideanSpace.norm_toLp_sub_le`: triangle inequalities
  on coordinate vectors.
* `EuclideanSpace.inner_toLp_toLp_eq_star_dotProduct`: the inner product is
  $\langle \mathbf{x}, \mathbf{y} \rangle = \mathbf{x}^{\mathsf{H}}\mathbf{y}$.
* `EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct`:
  $\|\mathbf{x}\|^2 = \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{x})$.
* `EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq`:
  $\mathbf{x}^{\mathsf{H}}\mathbf{x} = \|\mathbf{x}\|^2$ in $\Bbbk$.
* `EuclideanSpace.abs_dotProduct_le_norm`: Cauchy–Schwarz over $\mathbb{R}$.
* `EuclideanSpace.norm_toLp_star`: $\|\overline{\mathbf{x}}\| = \|\mathbf{x}\|$.
* `EuclideanSpace.norm_toLp_comp_equiv`: $\|(\mathbf{x}_{e(i)})_i\| = \|\mathbf{x}\|$ for a
  bijection $e$.
* `EuclideanSpace.norm_toLp_comp_le_of_injective`: $\|(\mathbf{y}_{e(i)})_i\| \le \|\mathbf{y}\|$
  for an injection $e$.
* `EuclideanSpace.norm_toLp_extend_zero`: extending by zero along an injection keeps the norm.
* `EuclideanSpace.norm_toLp_sumElim_sq`:
  $\left\|\begin{bmatrix} \mathbf{x} \\ \mathbf{y} \end{bmatrix}\right\|^2
  = \|\mathbf{x}\|^2 + \|\mathbf{y}\|^2$.
* `EuclideanSpace.norm_toLp_sq_eq_sum_sq`: $\|\mathbf{x}\|^2 = \sum_i \mathbf{x}_i^2$ over
  $\mathbb{R}$.
* `EuclideanSpace.norm_toLp_inv_sqrt_card_smul_sq`:
  $\|\lvert k \rvert^{-1/2} \mathbf{v}\|^2 = \|\mathbf{v}\|^2 / \lvert k \rvert$.
* `EuclideanSpace.lipschitzWith_ofLp_iff`: Lipschitz on `EuclideanSpace ℝ n` as an inequality on
  `n → ℝ`.
* `EuclideanSpace.norm_sub_add_smul_le_of_componentwise`: a componentwise update envelope.
* `EuclideanSpace.abs_dotProduct_sub_le_of_componentwise`: a dot-product error envelope.
* `EuclideanSpace.normalization_bounds_of_self_dot_sqrt_div`: norm and normalization errors
  from self-dot, square-root and component-division envelopes, including a zero norm.
-/

@[expose] public section

namespace EuclideanSpace

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- The sup norm of a coordinate vector is at most its Euclidean norm:
$\max_i \lvert x_i \rvert \le \|\mathbf{x}\|$. -/
theorem norm_le_norm_toLp (x : n → 𝕜) : ‖x‖ ≤ ‖WithLp.toLp 2 x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => PiLp.norm_apply_le (WithLp.toLp 2 x) i

/-- The triangle inequality for the Euclidean norm of coordinate vectors. This is
`norm_add_le` transported through `WithLp.toLp_add`. -/
theorem norm_toLp_add_le (x y : n → 𝕜) :
    ‖WithLp.toLp 2 (x + y)‖ ≤ ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖ := by
  simpa only [WithLp.toLp_add] using norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

/-- The Euclidean norm of a difference is at most the sum of the norms. This is
`norm_sub_le` transported through `WithLp.toLp_sub`. -/
theorem norm_toLp_sub_le (x y : n → 𝕜) :
    ‖WithLp.toLp 2 (x - y)‖ ≤ ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖ := by
  simpa only [WithLp.toLp_sub] using norm_sub_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

/-- Coordinatewise domination of norms implies domination of Euclidean norms. -/
theorem norm_toLp_le_norm_toLp {x y : n → 𝕜} (h : ∀ i, ‖x i‖ ≤ ‖y i‖) :
    ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 y‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2

/-- The inner product of two coordinate vectors in Euclidean space is
$\langle \mathbf{x}, \mathbf{y} \rangle = \mathbf{x}^{\mathsf{H}}\mathbf{y}$ (`star x ⬝ᵥ y`). -/
theorem inner_toLp_toLp_eq_star_dotProduct (x y : n → 𝕜) :
    inner 𝕜 (WithLp.toLp 2 x) (WithLp.toLp 2 y) = star x ⬝ᵥ y := by
  rw [inner_toLp_toLp, dotProduct_comm]

/-- The squared Euclidean norm of a coordinate vector is the real part of
$\mathbf{x}^{\mathsf{H}}\mathbf{x}$: $\|\mathbf{x}\|^2
= \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{x})$. -/
theorem norm_toLp_sq_eq_re_star_dotProduct (x : n → 𝕜) :
    ‖WithLp.toLp 2 x‖ ^ 2 = RCLike.re (star x ⬝ᵥ x) := by
  rw [← inner_toLp_toLp_eq_star_dotProduct, inner_self_eq_norm_sq]

/-- The pairing of a coordinate vector with itself is its squared Euclidean norm, as an element
of $\Bbbk$: $\mathbf{x}^{\mathsf{H}}\mathbf{x} = \|\mathbf{x}\|^2$. -/
theorem star_dotProduct_self_eq_coe_norm_sq (x : n → 𝕜) :
    star x ⬝ᵥ x = ((‖WithLp.toLp 2 x‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← inner_toLp_toLp_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]

/-- Over $\mathbb{R}$, the squared Euclidean norm of a coordinate vector is
$\|\mathbf{x}\|^2 = \mathbf{x}^{\mathsf{T}}\mathbf{x}$. -/
theorem norm_toLp_sq_eq_dotProduct_self (x : n → ℝ) : ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
  rw [norm_toLp_sq_eq_re_star_dotProduct, star_trivial, RCLike.re_to_real]

/-- **Cauchy–Schwarz for the dot product**: over $\mathbb{R}$,
$\lvert \mathbf{x}^{\mathsf{T}}\mathbf{y} \rvert \le \|\mathbf{x}\| \|\mathbf{y}\|$ with Euclidean
norms. The coordinate form of `abs_real_inner_le_norm`.
[HornJohnson2013, Theorem 5.1.4] (locator to check). -/
theorem abs_dotProduct_le_norm (x y : n → ℝ) :
    |x ⬝ᵥ y| ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
  have h := abs_real_inner_le_norm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  rwa [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm] at h

/-! ### Conjugation, reindexing, extension by zero and concatenation -/

/-- Entrywise conjugation does not change the Euclidean norm of a coordinate vector. -/
theorem norm_toLp_star (x : n → 𝕜) : ‖WithLp.toLp 2 (star x)‖ = ‖WithLp.toLp 2 x‖ := by
  simp [EuclideanSpace.norm_eq]

/-- Relabelling the coordinates by a bijection does not change the Euclidean norm. -/
theorem norm_toLp_comp_equiv {p : Type*} [Fintype p] (x : n → 𝕜) (e : p ≃ n) :
    ‖WithLp.toLp 2 (x ∘ e)‖ = ‖WithLp.toLp 2 x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  exact congrArg Real.sqrt (e.sum_comp fun i => ‖x i‖ ^ 2)

/-- Selecting coordinates along an injection does not increase the Euclidean norm. -/
theorem norm_toLp_comp_le_of_injective {p : Type*} [Fintype p] {e : p → n}
    (he : Function.Injective e) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (y ∘ e)‖ ≤ ‖WithLp.toLp 2 y‖ := by
  classical
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Function.comp_apply]
  rw [← Finset.sum_image (s := Finset.univ) (g := e) (f := fun k => ‖y k‖ ^ 2) he.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => sq_nonneg _

/-- Extending a coordinate vector by zero along an injection does not change its Euclidean
norm. -/
theorem norm_toLp_extend_zero {p : Type*} [Fintype p] {e : p → n} (he : Function.Injective e)
    (x : p → 𝕜) : ‖WithLp.toLp 2 (Function.extend e x 0)‖ = ‖WithLp.toLp 2 x‖ := by
  have h : ∑ i, ‖x i‖ ^ 2 = ∑ k, ‖Function.extend e x 0 k‖ ^ 2 := by
    refine Fintype.sum_of_injective e he _ _ (fun k hk => ?_) fun i => ?_
    · rw [Function.extend_apply' _ _ _ hk, Pi.zero_apply, norm_zero, zero_pow two_ne_zero]
    · rw [he.extend_apply]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  exact congrArg Real.sqrt h.symm

/-- **Pythagoras for concatenated coordinate vectors**: the squared Euclidean norm of the
concatenation of $\mathbf{x}$ and $\mathbf{y}$ (`Sum.elim x y`) is the sum of their squared
Euclidean norms,
$\left\|\begin{bmatrix} \mathbf{x} \\ \mathbf{y} \end{bmatrix}\right\|^2
= \|\mathbf{x}\|^2 + \|\mathbf{y}\|^2$. [HornJohnson2013, §5.1] (locator to check). -/
theorem norm_toLp_sumElim_sq {m : Type*} [Fintype m] (x : m → 𝕜) (y : n → 𝕜) :
    ‖WithLp.toLp 2 (Sum.elim x y)‖ ^ 2 = ‖WithLp.toLp 2 x‖ ^ 2 + ‖WithLp.toLp 2 y‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]


/-- The squared Euclidean norm of a real coordinate vector is the sum of the squared coordinates,
$\|\mathbf{x}\|^2 = \sum_i \mathbf{x}_i^2$: `EuclideanSpace.real_norm_sq_eq` stated for
`x : n → ℝ`. -/
theorem norm_toLp_sq_eq_sum_sq (x : n → ℝ) : ‖WithLp.toLp 2 x‖ ^ 2 = ∑ i, x i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

/-- The normalisation of a sketch with $\lvert k \rvert$ rows: scaling a vector of
$\Bbbk^k$ by $\lvert k \rvert^{-1/2}$ divides its squared norm by $\lvert k \rvert$,
$\|\lvert k \rvert^{-1/2} \mathbf{v}\|^2 = \|\mathbf{v}\|^2 / \lvert k \rvert$. -/
theorem norm_toLp_inv_sqrt_card_smul_sq {k : Type*} [Fintype k] (v : k → 𝕜) :
    ‖WithLp.toLp 2 ((√(Fintype.card k : ℝ))⁻¹ • v)‖ ^ 2 =
      ‖WithLp.toLp 2 v‖ ^ 2 / Fintype.card k := by
  rw [WithLp.toLp_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg _), inv_mul_eq_div]

open scoped NNReal in
/-- Lipschitz for the Euclidean norm, as an inequality on `n → ℝ`: $f$ is $L$-Lipschitz on
`EuclideanSpace ℝ n` if and only if
$\lvert f(\mathbf{x}) - f(\mathbf{y})\rvert \le L \|\mathbf{x} - \mathbf{y}\|$ for all
$\mathbf{x}, \mathbf{y}$. -/
theorem lipschitzWith_ofLp_iff {f : (n → ℝ) → ℝ} {L : ℝ≥0} :
    LipschitzWith L (fun x : EuclideanSpace ℝ n => f (WithLp.ofLp x)) ↔
      ∀ x y, |f x - f y| ≤ L * ‖WithLp.toLp 2 (x - y)‖ := by
  simp only [lipschitzWith_iff_dist_le_mul, dist_eq_norm, Real.norm_eq_abs]
  constructor
  · intro h x y
    simpa only [WithLp.toLp_sub] using h (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  · intro h x y
    simpa only [WithLp.toLp_sub, WithLp.toLp_ofLp] using h (WithLp.ofLp x) (WithLp.ofLp y)

/-- Taking the real norm of each coordinate preserves the Euclidean norm. -/
theorem norm_toLp_norm (x : n → 𝕜) :
    ‖WithLp.toLp 2 (fun i => ‖x i‖)‖ = ‖WithLp.toLp 2 x‖ := by
  simp [EuclideanSpace.norm_eq]

/-- A constant coordinate vector has norm equal to the coordinate norm times the square root
of the dimension, including dimension zero. This is the Euclidean specialization of
`PiLp.norm_toLp_const`. -/
theorem norm_toLp_const (c : 𝕜) :
    ‖WithLp.toLp 2 (fun _ : n => c)‖ = Real.sqrt (Fintype.card n) * ‖c‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- A coordinatewise relative and absolute envelope gives a Euclidean envelope. The absolute
term grows with the square root of the dimension; both coefficients are nonnegative. -/
theorem norm_toLp_le_mul_add_of_forall_abs_le {u η : ℝ} {x e : n → ℝ}
    (hu : 0 ≤ u) (hη : 0 ≤ η) (h : ∀ i, |e i| ≤ u * |x i| + η) :
    ‖WithLp.toLp 2 e‖ ≤ u * ‖WithLp.toLp 2 x‖ + Real.sqrt (Fintype.card n) * η := by
  have hdom := norm_toLp_le_norm_toLp (x := e)
    (y := u • (fun i => |x i|) + fun _ => η) fun i => by
      change |e i| ≤ |u * |x i| + η|
      rw [abs_of_nonneg (add_nonneg (mul_nonneg hu (abs_nonneg (x i))) hη)]
      exact h i
  refine hdom.trans ?_
  rw [WithLp.toLp_add]
  refine (norm_add_le _ _).trans_eq ?_
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu,
    norm_toLp_const, Real.norm_eq_abs, abs_of_nonneg hη]
  congr 2
  simpa only [Real.norm_eq_abs] using norm_toLp_norm x

/-! ### Componentwise arithmetic envelopes and normalization -/

private theorem norm_abs (x : n → ℝ) :
    ‖WithLp.toLp 2 (fun i => |x i|)‖ = ‖WithLp.toLp 2 x‖ := by
  simpa only [Real.norm_eq_abs] using EuclideanSpace.norm_toLp_norm x

/-- A componentwise relative error envelope for a scaled vector update gives a Euclidean
error bound, including zero-dimensional vectors. [Higham2002, §3.1]. -/
theorem norm_sub_add_smul_le_of_componentwise {e a : ℝ} {x y z : n → ℝ}
    (he : 0 ≤ e)
    (h : ∀ i, |(y + a • x - z) i| ≤ e * (|y i| + |a * x i|)) :
    ‖WithLp.toLp 2 (y + a • x - z)‖ ≤
      e * (‖WithLp.toLp 2 y‖ + |a| * ‖WithLp.toLp 2 x‖) := by
  have hd := EuclideanSpace.norm_toLp_le_norm_toLp (x := y + a • x - z)
    (y := e • (fun i => |y i| + |a * x i|)) fun i => by
      change |(y + a • x - z) i| ≤ |e * (|y i| + |a * x i|)|
      rw [abs_of_nonneg (mul_nonneg he (add_nonneg (abs_nonneg _) (abs_nonneg _)))]
      exact h i
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg he] at hd
  have heq : (fun i => |y i| + |a * x i|) =
      (fun i => |y i|) + (fun i => |(a • x) i|) := rfl
  rw [heq, WithLp.toLp_add] at hd
  refine hd.trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) he) |>.trans_eq ?_
  rw [norm_abs, norm_abs, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

/-- The componentwise dot-product bound gives the norm-relative projection defect, with
no assumption on the norms of its two operands. [Higham2002, §3.1]. -/
theorem abs_dotProduct_sub_le_of_componentwise {e α : ℝ} {x y : n → ℝ}
    (he : 0 ≤ e) (h : |x ⬝ᵥ y - α| ≤ e * ∑ i, |x i * y i|) :
    |x ⬝ᵥ y - α| ≤ e * ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
  have hs : ∑ i, |x i * y i| ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
    calc
      _ = (fun i => |x i|) ⬝ᵥ (fun i => |y i|) := by simp [dotProduct, abs_mul]
      _ ≤ |(fun i => |x i|) ⬝ᵥ (fun i => |y i|)| := le_abs_self _
      _ ≤ _ := by
        simpa only [norm_abs] using
          EuclideanSpace.abs_dotProduct_le_norm (fun i => |x i|) (fun i => |y i|)
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hs he])

/-- Componentwise division errors bound the normalization residual after multiplication by
the actual nonzero divisor. The divisor may have either sign. [Higham2002, §3.1]. -/
theorem norm_sub_smul_le_of_div_error {e β : ℝ} {z q : n → ℝ} (he : 0 ≤ e) (hβ : β ≠ 0)
    (h : ∀ i, |z i / β - q i| ≤ e * |z i / β|) :
    ‖WithLp.toLp 2 (z - β • q)‖ ≤ e * ‖WithLp.toLp 2 z‖ := by
  have hp (i : n) : |(z - β • q) i| ≤ e * |z i| + 0 := by
    have heq : (z i / β - q i) * β = z i - β * q i := by field_simp
    change |z i - β * q i| ≤ _
    calc
      _ = |(z i / β - q i) * β| := congrArg abs heq.symm
      _ ≤ (e * |z i / β|) * |β| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (h i) (abs_nonneg _)
      _ = _ := by rw [mul_assoc, ← abs_mul, div_mul_cancel₀ _ hβ, add_zero]
  simpa only [mul_zero, add_zero] using
    EuclideanSpace.norm_toLp_le_mul_add_of_forall_abs_le he le_rfl hp

private theorem abs_sub_sqrt_le_of_relative_sq {r σ e : ℝ} (hr : 0 ≤ r) (hσ : 0 ≤ σ)
    (h : |σ - r ^ 2| ≤ e * r ^ 2) : |r - Real.sqrt σ| ≤ e * r := by
  rcases hr.eq_or_lt with hr | hr
  · have hr0 : r = 0 := hr.symm
    have hσ0 : σ = 0 := by
      have hz : |σ| ≤ 0 := by simpa only [hr0, zero_pow (by omega : 2 ≠ 0),
        sub_zero, mul_zero] using h
      exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg σ))
    simp only [hr0, hσ0, Real.sqrt_zero, sub_self, abs_zero, mul_zero, le_refl]
  · have hprod : |r - Real.sqrt σ| * (r + Real.sqrt σ) = |r ^ 2 - σ| := by
      rw [← abs_of_nonneg (add_nonneg hr.le (Real.sqrt_nonneg σ)), ← abs_mul]
      congr 1
      nlinarith [Real.sq_sqrt hσ]
    have hm : |r - Real.sqrt σ| * r ≤ e * r ^ 2 := by
      have hb : |r ^ 2 - σ| ≤ e * r ^ 2 := by simpa only [abs_sub_comm] using h
      have hl := mul_le_mul_of_nonneg_left
        (show r ≤ r + Real.sqrt σ from le_add_of_nonneg_right (Real.sqrt_nonneg σ))
        (abs_nonneg (r - Real.sqrt σ))
      exact hl.trans (hprod.le.trans hb)
    exact (mul_le_mul_iff_right₀ hr).mp
      (by simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using hm)

/-- Self-dot error followed by square-root error gives a relative norm error with coefficient
$e_d+e_s(1+e_d)$. The computed squared norm is nonnegative. [Higham2002, §3.1]. -/
theorem abs_norm_sub_le_of_self_dot_sqrt {ed es σ β : ℝ} {z : n → ℝ}
    (hes : 0 ≤ es) (hσ : 0 ≤ σ)
    (hdot : |σ - ‖WithLp.toLp 2 z‖ ^ 2| ≤ ed * ‖WithLp.toLp 2 z‖ ^ 2)
    (hsqrt : |β - Real.sqrt σ| ≤ es * Real.sqrt σ) :
    |‖WithLp.toLp 2 z‖ - β| ≤ (ed + es * (1 + ed)) * ‖WithLp.toLp 2 z‖ := by
  have hr := abs_sub_sqrt_le_of_relative_sq (norm_nonneg _) hσ hdot
  have hup : Real.sqrt σ ≤ (1 + ed) * ‖WithLp.toLp 2 z‖ := by
    linarith [(abs_le.mp hr).1]
  have hsqrt' : |Real.sqrt σ - β| ≤ es * Real.sqrt σ := by
    simpa only [abs_sub_comm] using hsqrt
  calc
    _ ≤ |‖WithLp.toLp 2 z‖ - Real.sqrt σ| + |Real.sqrt σ - β| := abs_sub_le _ _ _
    _ ≤ ed * ‖WithLp.toLp 2 z‖ + es * ((1 + ed) * ‖WithLp.toLp 2 z‖) :=
      add_le_add hr (hsqrt'.trans (mul_le_mul_of_nonneg_left hup hes))
    _ = _ := by ring

private theorem abs_norm_sq_sub_one_le_of_normalization {e g β : ℝ} {z q : n → ℝ}
    (hg : g < 1) (hβ : 0 < β)
    (hscale : |‖WithLp.toLp 2 z‖ - β| ≤ g * ‖WithLp.toLp 2 z‖)
    (hres : ‖WithLp.toLp 2 (z - β • q)‖ ≤ e * ‖WithLp.toLp 2 z‖) :
    let t := (e + g) / (1 - g)
    |‖WithLp.toLp 2 q‖ ^ 2 - 1| ≤ t * (2 + t) := by
  intro t
  have hr : 0 < ‖WithLp.toLp 2 z‖ := by
    apply lt_of_le_of_ne (norm_nonneg _)
    intro hz
    have hzero := hscale
    rw [← hz, zero_sub, abs_neg, abs_of_pos hβ, mul_zero] at hzero
    linarith
  have hd : |‖WithLp.toLp 2 z‖ - β * ‖WithLp.toLp 2 q‖| ≤ e * ‖WithLp.toLp 2 z‖ := by
    have hh := abs_norm_sub_norm_le (WithLp.toLp 2 z) (WithLp.toLp 2 (β • q))
    rw [← WithLp.toLp_sub, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hβ] at hh
    exact hh.trans hres
  have hl : (1 - g) * ‖WithLp.toLp 2 z‖ ≤ β := by linarith [(abs_le.mp hscale).2]
  have hm : β * |‖WithLp.toLp 2 q‖ - 1| ≤ (e + g) * ‖WithLp.toLp 2 z‖ := by
    have hh := abs_sub_le (β * ‖WithLp.toLp 2 q‖) ‖WithLp.toLp 2 z‖ β
    rw [show β * ‖WithLp.toLp 2 q‖ - β = β * (‖WithLp.toLp 2 q‖ - 1) by ring,
      abs_mul, abs_of_pos hβ, abs_sub_comm (β * ‖WithLp.toLp 2 q‖)] at hh
    linarith
  have hunit : |‖WithLp.toLp 2 q‖ - 1| ≤ t := by
    apply (le_div_iff₀ (by linarith : 0 < 1 - g)).mpr
    have hh := mul_le_mul_of_nonneg_right hl (abs_nonneg (‖WithLp.toLp 2 q‖ - 1))
    exact (mul_le_mul_iff_right₀ hr).mp (by nlinarith [hm, hh])
  have ht : 0 ≤ t := (abs_nonneg _).trans hunit
  have hp : |‖WithLp.toLp 2 q‖ + 1| ≤ 2 + t := by
    rw [abs_of_nonneg (by positivity)]
    linarith [(abs_le.mp hunit).2]
  rw [show ‖WithLp.toLp 2 q‖ ^ 2 - 1 =
    (‖WithLp.toLp 2 q‖ - 1) * (‖WithLp.toLp 2 q‖ + 1) by ring, abs_mul]
  exact mul_le_mul hunit hp (abs_nonneg _) ht

/-- Actual self-dot, square-root and guarded component-division bounds imply a nonnegative
computed norm, a normalization residual bound, and a squared near-unit bound whenever
the stored norm is nonzero. The terminal zero-norm case is included.
[Higham2002, §3.1]. -/
theorem normalization_bounds_of_self_dot_sqrt_div {ed es eq σ β : ℝ} {z q : n → ℝ}
    (hed : 0 ≤ ed) (hes : 0 ≤ es) (heq : 0 ≤ eq) (hσ : 0 ≤ σ)
    (hdot : |σ - ‖WithLp.toLp 2 z‖ ^ 2| ≤ ed * ‖WithLp.toLp 2 z‖ ^ 2)
    (hsqrt : |β - Real.sqrt σ| ≤ es * Real.sqrt σ)
    (hdiv : β ≠ 0 → ∀ i, |z i / β - q i| ≤ eq * |z i / β|)
    (hg : ed + es * (1 + ed) < 1) :
    0 ≤ β ∧ ‖WithLp.toLp 2 (z - β • q)‖ ≤ eq * ‖WithLp.toLp 2 z‖ ∧
      (β ≠ 0 → let t := (eq + (ed + es * (1 + ed))) / (1 - (ed + es * (1 + ed)))
        |‖WithLp.toLp 2 q‖ ^ 2 - 1| ≤ t * (2 + t)) := by
  have hscale := abs_norm_sub_le_of_self_dot_sqrt hes hσ hdot hsqrt
  have hes1 : es < 1 := by nlinarith [mul_nonneg hed hes]
  have hβ : 0 ≤ β := by
    have hl := (abs_le.mp hsqrt).1
    have hp := mul_nonneg (by linarith : 0 ≤ 1 - es) (Real.sqrt_nonneg σ)
    nlinarith
  have hres : ‖WithLp.toLp 2 (z - β • q)‖ ≤ eq * ‖WithLp.toLp 2 z‖ := by
    by_cases hb : β = 0
    · have hz : ‖WithLp.toLp 2 z‖ = 0 := by
        rw [hb, sub_zero, abs_of_nonneg (norm_nonneg _)] at hscale
        nlinarith [norm_nonneg (WithLp.toLp 2 z)]
      simp only [hb, zero_smul, sub_zero, hz, mul_zero, le_refl]
    · exact norm_sub_smul_le_of_div_error heq hb (hdiv hb)
  exact ⟨hβ, hres, fun hb =>
    abs_norm_sq_sub_one_le_of_normalization hg (lt_of_le_of_ne hβ hb.symm) hscale hres⟩

end EuclideanSpace
