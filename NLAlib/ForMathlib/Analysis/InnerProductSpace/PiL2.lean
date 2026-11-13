/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Euclidean norm of a coordinate vector as a dot product

Bridges between the Euclidean norm $\|\mathbf{x}\|$ (`‖WithLp.toLp 2 x‖`) of a vector
`x : n → 𝕜` and the pairing $\mathbf{x}^{\mathsf{H}}\mathbf{x}$ (`star x ⬝ᵥ x`), the
Cauchy–Schwarz inequality for the dot product, the behaviour of that norm under conjugation,
reindexing, extension by zero, concatenation and scaling by $\lvert k \rvert^{-1/2}$, and the
Lipschitz condition for the Euclidean norm read on coordinate vectors. Upstream candidates for
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
[HornJohnson2013, Theorem 5.1.4]. -/
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
= \|\mathbf{x}\|^2 + \|\mathbf{y}\|^2$. [HornJohnson2013, §5.1]. -/
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

/-- The sum of absolute coordinate products is bounded by the product of Euclidean norms.
This is Cauchy–Schwarz applied to the coordinate magnitudes. -/
theorem sum_abs_mul_le_norm (x y : n → ℝ) :
    (∑ i, |x i * y i|) ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
  have h := abs_dotProduct_le_norm (fun i => |x i|) (fun i => |y i|)
  have hn (z : n → ℝ) : ‖WithLp.toLp 2 (fun i => |z i|)‖ = ‖WithLp.toLp 2 z‖ := by
    simpa only [Real.norm_eq_abs] using norm_toLp_norm z
  rw [hn x, hn y, dotProduct,
    abs_of_nonneg (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)))] at h
  simpa only [abs_mul] using h

/-- Approximating the second vector of a real dot product changes the pairing by at most
the first vector's Euclidean norm times the vector error. A further scalar error adds to it. -/
theorem abs_dotProduct_sub_le_of_norm_sub_le {x y z : n → ℝ} {a B E : ℝ}
    (hyz : ‖WithLp.toLp 2 (y - z)‖ ≤ E) (hz : |x ⬝ᵥ z - a| ≤ B) :
    |x ⬝ᵥ y - a| ≤ B + ‖WithLp.toLp 2 x‖ * E := by
  have hg := abs_dotProduct_le_norm x (y - z)
  rw [dotProduct_sub] at hg
  have hgap := hg.trans (mul_le_mul_of_nonneg_left hyz (norm_nonneg _))
  calc
    _ ≤ |x ⬝ᵥ y - x ⬝ᵥ z| + |x ⬝ᵥ z - a| := abs_sub_le _ _ _
    _ ≤ ‖WithLp.toLp 2 x‖ * E + B := add_le_add hgap hz
    _ = _ := add_comm _ _

/-- A constant coordinate vector has norm equal to the coordinate norm times the square root
of the dimension, including dimension zero. This is the Euclidean specialization of
`PiLp.norm_toLp_const`. -/
theorem norm_toLp_const (c : 𝕜) :
    ‖WithLp.toLp 2 (fun _ : n => c)‖ = Real.sqrt (Fintype.card n) * ‖c‖ := by
  convert (PiLp.norm_toLp_const (p := 2) (ι := n) (by norm_num) c) using 1 <;>
    simp [Real.sqrt_eq_rpow, Function.const_def]

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

end EuclideanSpace
