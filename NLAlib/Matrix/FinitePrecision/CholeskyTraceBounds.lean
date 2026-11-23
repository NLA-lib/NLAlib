/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Traces
public import NLAlib.Matrix.Perturbation.Inverse

/-!
# Bounds behind the rounding error analysis of Cholesky factorization

The steps of the analysis of a Cholesky trace that do not depend on the trace: a running
difference with rounding errors, the quadratic form argument for the positivity of the next
pivot, and Frobenius bounds for a product with entrywise errors [Higham2002, §10.1].

## Main results

* `NLAlib.Computation.one_add_pos_of_isRoundingProduct`: a product of rounding factors is
  positive.
* `NLAlib.Computation.exists_eq_one_add_mul_sub_sum_of_relErr`,
  `NLAlib.Computation.exists_eq_mul_one_add_sub_sum_of_relErr`: a running difference.
* `NLAlib.Computation.dotProduct_self_le_specNorm_inv_mul`: a positive definite form from below.
* `NLAlib.Computation.pos_of_mul_dotProduct_self_le_of_abs_sub_le`: the next pivot is positive.
* `NLAlib.Computation.frobNorm_sub_mul_transpose_le`,
  `NLAlib.Computation.frobNorm_add_mul_add_sub_le`: products with entrywise errors.
-/

@[expose] public section

open Finset
open scoped Matrix

namespace NLAlib.Computation

/-- A product $1 + \theta$ of rounding factors with unit roundoff $0 \le u < 1$ is positive. -/
theorem one_add_pos_of_isRoundingProduct {u θ : ℝ} {k : ℕ} (h : IsRoundingProduct u k θ)
    (hu : 0 ≤ u) (hu1 : u < 1) : 0 < 1 + θ :=
  lt_of_lt_of_le (pow_pos (by linarith) k) ((isRoundingProduct_iff hu hu1).mp h).1

/-- **A running difference, with the errors on the terms.** Let $0 \le u < 1$ and let
$s_{k+1}$ be $s_k - q_k$ with relative error $u$, for $q_k$ the number $c_k$ with relative error
$u$, $k < K$. Then $s_K = (1 + \varepsilon)(s_0 - \sum_{k<K} c_k(1 + \eta_k))$, with
$1 + \varepsilon$ a product of $K$ rounding factors and each $1 + \eta_k$ a product of $k + 1$.
[Higham2002, §10.1]. -/
theorem exists_eq_one_add_mul_sub_sum_of_relErr {u : ℝ} {c s : ℕ → ℝ} (hu : 0 ≤ u)
    (hu1 : u < 1) (K : ℕ)
    (h : ∀ k < K, ∃ q, RelErr u (c k) q ∧ RelErr u (s k - q) (s (k + 1))) :
    ∃ (ε : ℝ) (η : ℕ → ℝ), IsRoundingProduct u K ε ∧
      (∀ k < K, IsRoundingProduct u (k + 1) (η k)) ∧
      s K = (1 + ε) * (s 0 - ∑ k ∈ range K, c k * (1 + η k)) := by
  induction K with
  | zero => exact ⟨0, 0, isRoundingProduct_zero, by simp, by simp⟩
  | succ K ih =>
    obtain ⟨ε, η, hε, hη, hs⟩ := ih fun k hk => h k (by omega)
    obtain ⟨q, ⟨δ, hδ, rfl⟩, ⟨δ', hδ', hs'⟩⟩ := h K (by omega)
    have hpos := one_add_pos_of_isRoundingProduct hε hu hu1
    refine ⟨(1 + ε) * (1 + δ') - 1, fun k => if k < K then η k else (1 + δ) / (1 + ε) - 1,
      hε.mul (isRoundingProduct_one_of_abs_le hδ'), fun k hk => ?_, ?_⟩
    · by_cases hkK : k < K
      · simpa only [if_pos hkK] using hη k hkK
      · obtain rfl : k = K := by omega
        simp only [lt_irrefl, if_false]
        exact ((isRoundingProduct_one_of_abs_le hδ).div hε).mono hu (by omega)
    · have hsum : ∑ k ∈ range K, c k * (1 + if k < K then η k else (1 + δ) / (1 + ε) - 1) =
          ∑ k ∈ range K, c k * (1 + η k) :=
        sum_congr rfl fun k hk => by rw [if_pos (mem_range.mp hk)]
      beta_reduce
      rw [hs', hs, sum_range_succ, hsum]
      simp only [lt_irrefl, if_false]
      field_simp
      ring

/-- **A running difference, with the errors carried forward.** Let $0 \le u$ and let
$s_{k+1}$ be $s_k - q_k$ with relative error $u$, for $q_k$ the number $c_k$ with relative error
$u$, $k < K$. Then $s_K = s_0(1 + \alpha) - \sum_{k<K} c_k(1 + \eta_k)$, with $1 + \alpha$ a product
of $K$ rounding factors and each $1 + \eta_k$ a product of $K + 1$. [Higham2002, §3.1]. -/
theorem exists_eq_mul_one_add_sub_sum_of_relErr {u : ℝ} {c s : ℕ → ℝ} (hu : 0 ≤ u) (K : ℕ)
    (h : ∀ k < K, ∃ q, RelErr u (c k) q ∧ RelErr u (s k - q) (s (k + 1))) :
    ∃ (α : ℝ) (η : ℕ → ℝ), IsRoundingProduct u K α ∧
      (∀ k < K, IsRoundingProduct u (K + 1) (η k)) ∧
      s K = s 0 * (1 + α) - ∑ k ∈ range K, c k * (1 + η k) := by
  induction K with
  | zero => exact ⟨0, 0, isRoundingProduct_zero, by simp, by simp⟩
  | succ K ih =>
    obtain ⟨α, η, hα, hη, hs⟩ := ih fun k hk => h k (by omega)
    obtain ⟨q, ⟨δ, hδ, rfl⟩, ⟨δ', hδ', hs'⟩⟩ := h K (by omega)
    have h1 := isRoundingProduct_one_of_abs_le hδ'
    refine ⟨(1 + α) * (1 + δ') - 1,
      fun k => if k < K then (1 + η k) * (1 + δ') - 1 else (1 + δ) * (1 + δ') - 1,
      hα.mul h1, fun k hk => ?_, ?_⟩
    · by_cases hkK : k < K
      · simpa only [if_pos hkK] using (hη k hkK).mul h1
      · simp only [if_neg hkK]
        exact ((isRoundingProduct_one_of_abs_le hδ).mul h1).mono hu (by omega)
    · have hsum : ∑ k ∈ range K, c k * (1 + if k < K then (1 + η k) * (1 + δ') - 1 else
          (1 + δ) * (1 + δ') - 1) = (∑ k ∈ range K, c k * (1 + η k)) * (1 + δ') := by
        rw [sum_mul]
        exact sum_congr rfl fun k hk => by rw [if_pos (mem_range.mp hk)]; ring
      beta_reduce
      rw [hs', hs, sum_range_succ, hsum]
      simp only [lt_irrefl, if_false]
      ring

/-- For positive definite $\mathbf{A}$,
$\mathbf{z}^{\mathsf{T}}\mathbf{z} \le
\|\mathbf{A}^{-1}\|_2\,\mathbf{z}^{\mathsf{T}}\mathbf{A}\mathbf{z}$. -/
theorem dotProduct_self_le_specNorm_inv_mul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (z : Fin n → ℝ) : z ⬝ᵥ z ≤ specNorm A⁻¹ * (z ⬝ᵥ (A *ᵥ z)) := by
  have hU : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hT : Aᵀ = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  set c := specNorm A⁻¹ with hc
  set y := A⁻¹ *ᵥ z with hy
  have hAy : A *ᵥ y = z := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hU, Matrix.one_mulVec]
  have hyA : y ⬝ᵥ (A *ᵥ z) = z ⬝ᵥ z := by
    rw [Matrix.dotProduct_mulVec]
    nth_rewrite 1 [← hT]
    rw [Matrix.vecMul_transpose, hAy]
  have hnorm : ∀ w : Fin n → ℝ, w ⬝ᵥ w = ‖WithLp.toLp 2 w‖ ^ 2 := fun w => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  have hyn : ‖WithLp.toLp 2 y‖ ≤ c * ‖WithLp.toLp 2 z‖ := norm_toLp_mulVec_le _ _
  have hyz : y ⬝ᵥ z ≤ c * (z ⬝ᵥ z) := by
    have hcs : y ⬝ᵥ z ≤ ‖WithLp.toLp 2 y‖ * ‖WithLp.toLp 2 z‖ := by
      have := real_inner_le_norm (WithLp.toLp 2 y) (WithLp.toLp 2 z)
      simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using this
    rw [hnorm z, sq, ← mul_assoc]
    exact hcs.trans (mul_le_mul_of_nonneg_right hyn (norm_nonneg _))
  rcases (specNorm_nonneg A⁻¹).eq_or_lt with h0 | hpos
  · have hy0 : y = 0 := by
      have : ‖WithLp.toLp 2 y‖ ≤ 0 := by simpa [hc, ← h0] using hyn
      have h2 : WithLp.toLp 2 y = 0 := norm_le_zero_iff.mp this
      simpa using h2
    have hz0 : z = 0 := by rw [← hAy, hy0, Matrix.mulVec_zero]
    simp [hz0]
  · have hq : 0 ≤ (c • z - y) ⬝ᵥ (A *ᵥ (c • z - y)) := by
      simpa using hA.posSemidef.dotProduct_mulVec_nonneg (c • z - y)
    have hexp : (c • z - y) ⬝ᵥ (A *ᵥ (c • z - y)) =
        c * c * (z ⬝ᵥ (A *ᵥ z)) - 2 * c * (z ⬝ᵥ z) + y ⬝ᵥ z := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hAy, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hyA]
      ring
    rw [hexp] at hq
    have hfin : c * (z ⬝ᵥ z) ≤ c * (c * (z ⬝ᵥ (A *ᵥ z))) := by nlinarith
    exact le_of_mul_le_mul_left hfin hpos

/-- The quadratic form of $\mathbf{A}$ at a null vector of the computed rows is the running
value, up to the entrywise errors. -/
private theorem abs_quad_sub_le {n : ℕ} {A M : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    {j : Fin n} {t v γ Λ : ℝ} (hxj : x j = 1) (hx0 : ∀ i, j < i → x i = 0) (hMx : Mᵀ *ᵥ x = 0)
    (he : ∀ i k, i ≤ j → k ≤ j → |A i k - (M * Mᵀ) i k - (if i = j ∧ k = j then t else 0)| ≤
      v * Λ + γ * ∑ m, |M i m| * |M k m|) :
    |x ⬝ᵥ (A *ᵥ x) - t| ≤
      v * Λ * (∑ i, |x i|) ^ 2 + γ * ∑ m, (∑ i, |x i| * |M i m|) ^ 2 := by
  have h0 : x ⬝ᵥ ((M * Mᵀ) *ᵥ x) = 0 := by
    rw [← Matrix.mulVec_mulVec, hMx, Matrix.mulVec_zero, dotProduct_zero]
  have hform : ∀ B : Matrix (Fin n) (Fin n) ℝ,
      x ⬝ᵥ (B *ᵥ x) = ∑ i, ∑ k, x i * x k * B i k := fun B => by
    simp only [dotProduct, Matrix.mulVec, mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by ring
  have ht : ∑ i, ∑ k, x i * x k * (if i = j ∧ k = j then t else 0) = t := by
    rw [sum_eq_single j, sum_eq_single j]
    · simp [hxj]
    · intro k _ hk
      simp [hk]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  have hid : x ⬝ᵥ (A *ᵥ x) - t =
      ∑ i, ∑ k, x i * x k * (A i k - (M * Mᵀ) i k - if i = j ∧ k = j then t else 0) := by
    simp only [mul_sub, sum_sub_distrib]
    rw [← hform A, ← hform (M * Mᵀ), h0, ht, sub_zero]
  have h1 : (∑ i, |x i|) ^ 2 = ∑ i, ∑ k, |x i| * |x k| := by
    rw [sq, sum_mul_sum]
  have h2 : ∑ m, (∑ i, |x i| * |M i m|) ^ 2 =
      ∑ i, ∑ k, |x i| * |x k| * ∑ m, |M i m| * |M k m| := by
    simp only [sq, sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have hR : v * Λ * (∑ i, |x i|) ^ 2 + γ * ∑ m, (∑ i, |x i| * |M i m|) ^ 2 =
      ∑ i, ∑ k, |x i| * |x k| * (v * Λ + γ * ∑ m, |M i m| * |M k m|) := by
    rw [h1, h2, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [hid, hR]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
  by_cases hi : j < i
  · simp [hx0 i hi]
  by_cases hk : j < k
  · simp [hx0 k hk]
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (he i k (not_lt.mp hi) (not_lt.mp hk)) (by positivity)

/-- The computed rows at a vector supported up to `j`, with a unit entry at `j`. -/
private theorem sum_sq_sum_abs_le {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ}
    {j : Fin n} (hxj : x j = 1) (hx0 : ∀ i, j < i → x i = 0) :
    ∑ m, (∑ i, |x i| * |M i m|) ^ 2 ≤
      2 * (x ⬝ᵥ x - 1) * (∑ m, ∑ i, (if i < j then M i m else 0) ^ 2) +
        2 * ∑ m, M j m ^ 2 := by
  set y : Fin n → ℝ := fun i => if i < j then x i else 0 with hy
  have hY : ∑ i, y i ^ 2 ≤ x ⬝ᵥ x - 1 := by
    have hsum : ∑ i, (y i ^ 2 + if i = j then (1 : ℝ) else 0) ≤ ∑ i, x i * x i := by
      refine sum_le_sum fun i _ => ?_
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · simp [hy, hlt, hlt.ne, sq]
      · simp [hy, hxj]
      · simp [hy, not_lt.mpr hgt.le, hgt.ne', hx0 i hgt]
    rw [sum_add_distrib, sum_ite_eq' univ j] at hsum
    simp only [mem_univ, if_true] at hsum
    change _ ≤ ∑ i, x i * x i - 1
    linarith
  have hm : ∀ m, (∑ i, |x i| * |M i m|) ^ 2 ≤
      2 * (x ⬝ᵥ x - 1) * (∑ i, (if i < j then M i m else 0) ^ 2) + 2 * M j m ^ 2 := by
    intro m
    have hsplit : ∑ i, |x i| * |M i m| =
        ∑ i, |y i| * |if i < j then M i m else 0| + |M j m| := by
      have hpt : ∀ i, |x i| * |M i m| =
          |y i| * |if i < j then M i m else 0| + if i = j then |M j m| else 0 := by
        intro i
        rcases lt_trichotomy i j with hlt | rfl | hgt
        · simp [hy, hlt, hlt.ne]
        · simp [hy, hxj]
        · simp [hy, not_lt.mpr hgt.le, hgt.ne', hx0 i hgt]
      rw [sum_congr rfl fun i _ => hpt i, sum_add_distrib, sum_ite_eq' univ j]
      simp
    have hcs := sum_mul_sq_le_sq_mul_sq univ (fun i => |y i|)
      (fun i => |if i < j then M i m else 0|)
    simp only [sq_abs] at hcs
    have hS : 0 ≤ ∑ i, (if i < j then M i m else 0) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    have hcs' := hcs.trans (mul_le_mul_of_nonneg_right hY hS)
    rw [hsplit]
    nlinarith [sq_nonneg ((∑ i, |y i| * |if i < j then M i m else 0|) - |M j m|), sq_abs (M j m)]
  calc _ ≤ ∑ m, (2 * (x ⬝ᵥ x - 1) * (∑ i, (if i < j then M i m else 0) ^ 2) + 2 * M j m ^ 2) :=
        sum_le_sum fun m _ => hm m
    _ = _ := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]

/-- The running value of the next Cholesky pivot is positive. Let $\mathbf{x}$ have $x_j = 1$
and $x_i = 0$ for $i > j$, with $\mathbf{M}^{\mathsf{T}}\mathbf{x} = \mathbf{0}$ and
$\mu\,\mathbf{x}^{\mathsf{T}}\mathbf{x} \le \mathbf{x}^{\mathsf{T}}\mathbf{A}\mathbf{x}$.
Suppose that for $i, k \le j$ the entry $(i, k)$ of
$\mathbf{A} - \mathbf{M}\mathbf{M}^{\mathsf{T}} -
t\,\mathbf{e}_j\mathbf{e}_j^{\mathsf{T}}$ is at most
$v\Lambda + \gamma\sum_m \lvert M_{im}\rvert\lvert M_{km}\rvert$, with
$v, \gamma, \Lambda \ge 0$, that
$t \le (1 + v)\Lambda - (1 - \gamma)w$ for the squared norm $w$ of row $j$ of $\mathbf{M}$,
and, with
$\Phi$ the sum of the squares of the rows before $j$, that $vn\Lambda + 2\gamma\Phi \le \mu$,
$\gamma \le 1/7$, $v(n + 1) \le 1/7$ and $vn\Lambda + 4\gamma\Lambda < \mu$. Then $t > 0$. -/
theorem pos_of_mul_dotProduct_self_le_of_abs_sub_le {n : ℕ} {A M : Matrix (Fin n) (Fin n) ℝ}
    {x : Fin n → ℝ} {j : Fin n}
    {t v γ Λ μ : ℝ} (hΛ : 0 ≤ Λ) (hv : 0 ≤ v) (hγ0 : 0 ≤ γ)
    (hμA : μ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)) (hxj : x j = 1) (hx0 : ∀ i, j < i → x i = 0)
    (hMx : Mᵀ *ᵥ x = 0)
    (he : ∀ i k, i ≤ j → k ≤ j → |A i k - (M * Mᵀ) i k - (if i = j ∧ k = j then t else 0)| ≤
      v * Λ + γ * ∑ m, |M i m| * |M k m|)
    (ht : t ≤ (1 + v) * Λ - (1 - γ) * ∑ m, M j m ^ 2)
    (hC : v * Λ * n + 2 * γ * (∑ m, ∑ i, (if i < j then M i m else 0) ^ 2) ≤ μ)
    (hγ : γ ≤ 1 / 7) (hvn : v * ((n : ℝ) + 1) ≤ 1 / 7)
    (hfin : v * Λ * n + 4 * γ * Λ < μ) : 0 < t := by
  set Φ := ∑ m, ∑ i, (if i < j then M i m else 0) ^ 2 with hΦ
  set w := ∑ m, M j m ^ 2 with hw
  set X := x ⬝ᵥ x with hX
  have hw0 : 0 ≤ w := sum_nonneg fun _ _ => sq_nonneg _
  have hX1 : 1 ≤ X := by
    have h1 : x j * x j ≤ ∑ i, x i * x i :=
      single_le_sum (f := fun i => x i * x i) (fun i _ => mul_self_nonneg _) (mem_univ j)
    rw [hxj] at h1
    simpa [hX, dotProduct] using h1
  have hsumx : (∑ i, |x i|) ^ 2 ≤ n * X := by
    have h := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun i : Fin n => |x i|)
    simpa [hX, dotProduct, sq] using h
  have hq := abs_quad_sub_le hxj hx0 hMx he
  have hsq := sum_sq_sum_abs_le (M := M) hxj hx0
  have hupper : x ⬝ᵥ (A *ᵥ x) ≤ t + v * Λ * (n * X) + γ * (2 * (X - 1) * Φ + 2 * w) := by
    have h1 := (le_abs_self _).trans hq
    have h2 := mul_le_mul_of_nonneg_left hsumx (mul_nonneg hv hΛ)
    have h3 := mul_le_mul_of_nonneg_left hsq hγ0
    linarith
  have hD : 0 ≤ (X - 1) * (μ - v * Λ * n - 2 * γ * Φ) :=
    mul_nonneg (by linarith) (by linarith)
  have hkey : μ - v * Λ * n ≤ t + 2 * γ * w := by nlinarith
  have hw2 : w ≤ 2 * Λ := by nlinarith [mul_nonneg hγ0 hw0, mul_nonneg hv hΛ]
  have hγw : γ * w ≤ γ * (2 * Λ) := mul_le_mul_of_nonneg_left hw2 hγ0
  linarith

/-- If $\lvert (\mathbf{A} - \mathbf{M}\mathbf{M}^{\mathsf{T}})_{ik}\rvert \le
v\lvert A_{ik}\rvert +
\gamma\sum_m \lvert M_{im}\rvert\lvert M_{km}\rvert$ with $v, \gamma \ge 0$, for
$n \times n$ matrices, then
$\|\mathbf{A} - \mathbf{M}\mathbf{M}^{\mathsf{T}}\|_{\mathsf{F}} \le
vn\|\mathbf{A}\|_2 + \gamma\|\mathbf{M}\|_{\mathsf{F}}^2$. -/
theorem frobNorm_sub_mul_transpose_le {n : ℕ} {A M : Matrix (Fin n) (Fin n) ℝ} {v γ : ℝ}
    (hv : 0 ≤ v) (hγ : 0 ≤ γ)
    (h : ∀ i k, |A i k - (M * Mᵀ) i k| ≤ v * |A i k| + γ * ∑ m, |M i m| * |M k m|) :
    frobNorm (A - M * Mᵀ) ≤ v * (n * specNorm A) + γ * frobNorm M ^ 2 := by
  set B : Matrix (Fin n) (Fin n) ℝ := v • A.map abs + γ • (M.map abs * (M.map abs)ᵀ) with hB
  have hBij : ∀ i k, B i k = v * |A i k| + γ * ∑ m, |M i m| * |M k m| := fun i k => by
    simp [hB, Matrix.mul_apply]
  have h1 : frobNorm (A - M * Mᵀ) ≤ frobNorm B := by
    refine frobNorm_le_of_norm_apply_le fun i k => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hBij]
    exact (h i k).trans (le_abs_self _)
  have hAF : frobNorm (A.map abs) = frobNorm A := by simp [frobNorm]
  have hMF : frobNorm (M.map abs) = frobNorm M := by simp [frobNorm]
  have hAn : frobNorm A ≤ n * specNorm A := by
    have := frobNorm_le_card_mul_of_forall_abs_le (M := A) (specNorm_nonneg A)
      fun i k => by simpa using norm_apply_le_specNorm A i k
    simpa using this
  have hprod : frobNorm (M.map abs * (M.map abs)ᵀ) ≤ frobNorm M ^ 2 := by
    refine (frobNorm_mul_le _ _).trans_eq ?_
    rw [frobNorm_transpose, hMF, sq]
  refine h1.trans ((frobNorm_add_le _ _).trans (add_le_add ?_ ?_))
  · rw [frobNorm_smul, Real.norm_of_nonneg hv, hAF]
    exact mul_le_mul_of_nonneg_left hAn hv
  · rw [frobNorm_smul, Real.norm_of_nonneg hγ]
    exact mul_le_mul_of_nonneg_left hprod hγ

/-- If $\lvert \mathbf{D}_1\rvert \le g\lvert\mathbf{T}\rvert$ and
$\lvert \mathbf{D}_2\rvert \le g\lvert\mathbf{T}^{\mathsf{T}}\rvert$ entrywise, with
$g \ge 0$, then
$\|(\mathbf{T} + \mathbf{D}_1)(\mathbf{T}^{\mathsf{T}} + \mathbf{D}_2) -
\mathbf{T}\mathbf{T}^{\mathsf{T}}\|_{\mathsf{F}} \le
(2g + g^2)\|\mathbf{T}\|_{\mathsf{F}}^2$. -/
theorem frobNorm_add_mul_add_sub_le {n : ℕ} {T D₁ D₂ : Matrix (Fin n) (Fin n) ℝ} {g : ℝ}
    (hg : 0 ≤ g) (h₁ : ∀ i k, |D₁ i k| ≤ g * |T i k|) (h₂ : ∀ i k, |D₂ i k| ≤ g * |Tᵀ i k|) :
    frobNorm ((T + D₁) * (Tᵀ + D₂) - T * Tᵀ) ≤ (2 * g + g ^ 2) * frobNorm T ^ 2 := by
  have hD : ∀ {D S : Matrix (Fin n) (Fin n) ℝ}, (∀ i k, |D i k| ≤ g * |S i k|) →
      frobNorm D ≤ g * frobNorm S := fun {D S} hDS => by
    have h1 : frobNorm D ≤ frobNorm (g • S) := frobNorm_le_of_norm_apply_le fun i k => by
      simpa [abs_mul, abs_of_nonneg hg] using hDS i k
    rwa [frobNorm_smul, Real.norm_of_nonneg hg] at h1
  have h1 := hD h₁
  have h2 : frobNorm D₂ ≤ g * frobNorm T := by
    simpa only [frobNorm_transpose] using hD h₂
  have hF := frobNorm_nonneg T
  have hexp : (T + D₁) * (Tᵀ + D₂) - T * Tᵀ = D₁ * Tᵀ + T * D₂ + D₁ * D₂ := by
    simp only [Matrix.add_mul, Matrix.mul_add]
    abel
  rw [hexp]
  have ha := frobNorm_mul_le D₁ Tᵀ
  have hb := frobNorm_mul_le T D₂
  have hc := frobNorm_mul_le D₁ D₂
  rw [frobNorm_transpose] at ha
  have ha' : frobNorm D₁ * frobNorm T ≤ g * frobNorm T * frobNorm T :=
    mul_le_mul_of_nonneg_right h1 hF
  have hb' : frobNorm T * frobNorm D₂ ≤ frobNorm T * (g * frobNorm T) :=
    mul_le_mul_of_nonneg_left h2 hF
  have hc' : frobNorm D₁ * frobNorm D₂ ≤ g * frobNorm T * (g * frobNorm T) :=
    mul_le_mul h1 h2 (frobNorm_nonneg _) (mul_nonneg hg hF)
  have htri := (frobNorm_add_le (D₁ * Tᵀ + T * D₂) (D₁ * D₂)).trans
    (add_le_add_left (frobNorm_add_le (D₁ * Tᵀ) (T * D₂)) _)
  nlinarith

end NLAlib.Computation
