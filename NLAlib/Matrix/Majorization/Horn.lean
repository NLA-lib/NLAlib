/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import NLAlib.Matrix.Majorization.DoublyStochastic
public import NLAlib.Matrix.Spectral.SVD
public import NLAlib.Matrix.Spectral.SingularValueInequalities

/-!
# Horn's product inequality and log-majorization

The singular values of a product are log-majorized by the products of the singular values:
`∏ i < k, σ_i(A B) ≤ ∏ i < k, σ_i(A) σ_i(B)`. Weyl's lemma turns such product inequalities
between non-increasing nonnegative sequences into inequalities between sums of powers, which is
how Hölder's inequality for Schatten norms is obtained.

## Main results

* `NLAlib.prod_range_singularValues_mul_le`: Horn's product inequality.
* `NLAlib.sum_range_rpow_le_of_forall_prod_range_le`: Weyl's lemma, log-majorization implies
  weak majorization of powers.
* `NLAlib.sum_range_singularValues_mul_rpow_le`: power sums of the singular values of a product.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-! ### Horn's product inequality -/

/-- For a matrix `Y` with `k` columns, the product of the `k` squared singular values of `A * Y`
is at most that of `A` times that of `Y`: the Gram determinant of `A * Y` factors through an
orthonormal basis of a `k`-dimensional space containing the range of `Y`. -/
private theorem prod_sq_singularValues_mul_le (A : Matrix m p 𝕜) {k : ℕ}
    (Y : Matrix p (Fin k) 𝕜) (hk : k ≤ Fintype.card p) :
    ∏ i ∈ Finset.range k, singularValues (A * Y) i ^ 2 ≤
      (∏ i ∈ Finset.range k, singularValues A i ^ 2) *
        ∏ i ∈ Finset.range k, singularValues Y i ^ 2 := by
  obtain ⟨U, V, h⟩ := exists_isSVD Y (k := k)
    (Y.rank_le_card_width.trans (Fintype.card_fin k).le) hk (Fintype.card_fin k).ge
  set R : Matrix (Fin k) (Fin k) 𝕜 :=
    Matrix.diagonal (fun i : Fin k => ((singularValues Y i : ℝ) : 𝕜)) * Vᴴ with hR
  have hY : Y = U * R := by rw [hR, ← Matrix.mul_assoc]; exact h.eq
  have h1 : (A * Y)ᴴ * (A * Y) = Rᴴ * ((A * U)ᴴ * (A * U)) * R := by
    rw [hY]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have h2 : Yᴴ * Y = Rᴴ * R := by
    rw [hY, h.hasOrthonormalCols_left.conjTranspose_mul_mul]
  have hdet : ((A * Y)ᴴ * (A * Y)).det = ((A * U)ᴴ * (A * U)).det * (Yᴴ * Y).det := by
    rw [h1, h2]
    simp only [Matrix.det_mul]
    ring
  simp only [det_conjTranspose_mul_self_eq_prod_sq_singularValues, Fintype.card_fin] at hdet
  have hdet' : ∏ i ∈ Finset.range k, singularValues (A * Y) i ^ 2 =
      (∏ i ∈ Finset.range k, singularValues (A * U) i ^ 2) *
        ∏ i ∈ Finset.range k, singularValues Y i ^ 2 := by
    exact_mod_cast hdet
  rw [hdet']
  gcongr with i hi
  · exact singularValues_nonneg _ _
  · exact (singularValues_mul_le_mul_specNorm A U i).trans
      (mul_le_of_le_one_right (singularValues_nonneg A i)
        h.hasOrthonormalCols_left.specNorm_le_one)

/-- The leading `k` right singular vectors: an `X` with `k` orthonormal columns such that the
singular values of `M * X` are the `k` largest singular values of `M`. -/
private theorem exists_hasOrthonormalCols_singularValues_mul_eq (M : Matrix m n 𝕜) {k : ℕ}
    (hkm : k ≤ Fintype.card m) (hkn : k ≤ Fintype.card n) :
    ∃ X : Matrix n (Fin k) 𝕜, HasOrthonormalCols X ∧
      ∀ i < k, singularValues (M * X) i = singularValues M i := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (le_min hkm hkn)
  obtain ⟨U₁, U₂, V₁, V₂, h⟩ := exists_isSVD_fromCols M (k := k) (d := d)
    (hd ▸ le_min M.rank_le_card_height M.rank_le_card_width) (hd ▸ min_le_left _ _)
    (hd ▸ min_le_right _ _)
  have hV₁ := (hasOrthonormalCols_fromCols_iff.mp h.hasOrthonormalCols_right).1
  have hU₁ := (hasOrthonormalCols_fromCols_iff.mp h.hasOrthonormalCols_left).1
  have hMV : M * V₁ = U₁ * Matrix.diagonal (fun i : Fin k => ((singularValues M i : ℝ) : 𝕜)) := by
    ext a i
    have := congrFun (congrFun h.mul_right_eq a) (Sum.inl i)
    rw [Matrix.mul_diagonal, Matrix.fromCols_apply_inl, Sum.elim_inl] at this
    rw [Matrix.mul_diagonal, ← this]
    simp only [Matrix.mul_apply, Matrix.fromCols_apply_inl]
  have hsvd : IsSVD (M * V₁) U₁ (fun i : Fin k => singularValues M i) 1 :=
    ⟨hU₁, hasOrthonormalCols_one, fun i => singularValues_nonneg M i, by
      rw [Matrix.conjTranspose_one, Matrix.mul_one, hMV]⟩
  refine ⟨V₁, hV₁, fun i hi => ?_⟩
  exact hsvd.singularValues_eq (fun a b hab => singularValues_antitone M (Fin.le_def.mp hab))
    ⟨i, hi⟩

/-- **Horn's product inequality.** For every `k`,
`∏ i < k, σ_i(A * B) ≤ ∏ i < k, σ_i(A) σ_i(B)`.
[HornJohnson1991, Theorem 3.3.4].
Port of `NLAlib.prod_singularValues_mul_le`, there over `ℝ`.
Result: horn-product-inequality -/
theorem prod_range_singularValues_mul_le (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) (k : ℕ) :
    ∏ i ∈ Finset.range k, singularValues (A * B) i ≤
      ∏ i ∈ Finset.range k, singularValues A i * singularValues B i := by
  have hnn : 0 ≤ ∏ i ∈ Finset.range k, singularValues A i * singularValues B i :=
    Finset.prod_nonneg fun i _ => mul_nonneg (singularValues_nonneg A i) (singularValues_nonneg B i)
  by_cases hk : k ≤ (A * B).rank
  · have hkm : k ≤ Fintype.card m := hk.trans (A * B).rank_le_card_height
    have hkn : k ≤ Fintype.card n := hk.trans (A * B).rank_le_card_width
    have hkp : k ≤ Fintype.card p :=
      hk.trans ((Matrix.rank_mul_le_left A B).trans A.rank_le_card_width)
    obtain ⟨X, hX, hXs⟩ := exists_hasOrthonormalCols_singularValues_mul_eq (A * B) hkm hkn
    have hBX (i : ℕ) : singularValues (B * X) i ≤ singularValues B i :=
      (singularValues_mul_le_mul_specNorm B X i).trans
        (mul_le_of_le_one_right (singularValues_nonneg B i) hX.specNorm_le_one)
    refine le_of_sq_le_sq ?_ hnn
    rw [← Finset.prod_pow, ← Finset.prod_pow]
    calc ∏ i ∈ Finset.range k, singularValues (A * B) i ^ 2
        = ∏ i ∈ Finset.range k, singularValues (A * (B * X)) i ^ 2 :=
          Finset.prod_congr rfl fun i hi => by
            rw [← Matrix.mul_assoc, hXs i (Finset.mem_range.mp hi)]
      _ ≤ (∏ i ∈ Finset.range k, singularValues A i ^ 2) *
            ∏ i ∈ Finset.range k, singularValues (B * X) i ^ 2 :=
          prod_sq_singularValues_mul_le A (B * X) hkp
      _ ≤ (∏ i ∈ Finset.range k, singularValues A i ^ 2) *
            ∏ i ∈ Finset.range k, singularValues B i ^ 2 := by
          gcongr with i hi
          · exact singularValues_nonneg _ _
          · exact hBX i
      _ = ∏ i ∈ Finset.range k, (singularValues A i * singularValues B i) ^ 2 := by
          rw [← Finset.prod_mul_distrib]
          simp only [mul_pow]
  · rw [Finset.prod_eq_zero (Finset.mem_range.mpr (not_le.mp hk))
      ((singularValues_eq_zero_iff (A * B)).mpr le_rfl)]
    exact hnn

/-! ### Weyl's lemma -/

/-- Weyl's lemma for positive sequences: logarithms turn the product inequalities into a weak
majorization, to which the monotone convex function `t ↦ exp (r * t)` is applied. -/
private theorem sum_range_rpow_le_of_forall_prod_range_le_of_pos {x y : ℕ → ℝ} {N : ℕ}
    (hx0 : ∀ i < N, 0 < x i) (hy0 : ∀ i < N, 0 < y i) (hx : Antitone x) (hy : Antitone y)
    (h : ∀ k ≤ N, ∏ i ∈ Finset.range k, x i ≤ ∏ i ∈ Finset.range k, y i) {r : ℝ} (hr : 0 < r) :
    ∑ i ∈ Finset.range N, x i ^ r ≤ ∑ i ∈ Finset.range N, y i ^ r := by
  have hlx : AntitoneOn (fun i => Real.log (x i)) (Set.Iio N) := fun i _ j hj hij =>
    Real.log_le_log (hx0 j hj) (hx hij)
  have hly : AntitoneOn (fun i => Real.log (y i)) (Set.Iio N) := fun i _ j hj hij =>
    Real.log_le_log (hy0 j hj) (hy hij)
  have hmaj : WeaklyMajorized (fun i : Fin N => Real.log (x i))
      fun i : Fin N => Real.log (y i) := by
    refine (weaklyMajorized_fin_iff_sum_range_le hlx hly).mpr fun k hk => ?_
    have hxk : ∀ i ∈ Finset.range k, 0 < x i := fun i hi =>
      hx0 i ((Finset.mem_range.mp hi).trans_le hk)
    have hyk : ∀ i ∈ Finset.range k, 0 < y i := fun i hi =>
      hy0 i ((Finset.mem_range.mp hi).trans_le hk)
    rw [← Real.log_prod fun i hi => (hxk i hi).ne', ← Real.log_prod fun i hi => (hyk i hi).ne']
    exact Real.log_le_log (Finset.prod_pos hxk) (h k hk)
  have hmono : Monotone fun t : ℝ => Real.exp (r * t) := fun s t hst =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hr.le)
  have hconv : ConvexOn ℝ Set.univ fun t : ℝ => Real.exp (r * t) :=
    convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ r)
  have key := hmaj.sum_monotone_convex_le hmono hconv
  have hexp {z : ℝ} (hz : 0 < z) : Real.exp (r * Real.log z) = z ^ r := by
    rw [Real.rpow_def_of_pos hz, mul_comm]
  rw [← Fin.sum_univ_eq_sum_range (fun i => x i ^ r) N,
    ← Fin.sum_univ_eq_sum_range (fun i => y i ^ r) N]
  calc ∑ i : Fin N, x i ^ r = ∑ i : Fin N, Real.exp (r * Real.log (x i)) :=
        Finset.sum_congr rfl fun i _ => (hexp (hx0 i i.isLt)).symm
    _ ≤ ∑ i : Fin N, Real.exp (r * Real.log (y i)) := key
    _ = ∑ i : Fin N, y i ^ r := Finset.sum_congr rfl fun i _ => hexp (hy0 i i.isLt)

/-- **Weyl's lemma: log-majorization implies weak majorization of powers.** For nonnegative
non-increasing sequences `x`, `y` with `∏ i < k, x i ≤ ∏ i < k, y i` for all `k ≤ N`, and any
`r > 0`, `∑ i < N, x i ^ r ≤ ∑ i < N, y i ^ r`.
[HornJohnson1991, Theorem 3.3.13 and Corollary 3.3.10].
Port of `NLAlib.sum_range_rpow_le_of_nonneg_of_prod_le`. -/
theorem sum_range_rpow_le_of_forall_prod_range_le {x y : ℕ → ℝ} {N : ℕ} (hx0 : ∀ i, 0 ≤ x i)
    (hy0 : ∀ i, 0 ≤ y i) (hx : Antitone x) (hy : Antitone y)
    (h : ∀ k ≤ N, ∏ i ∈ Finset.range k, x i ≤ ∏ i ∈ Finset.range k, y i) {r : ℝ} (hr : 0 < r) :
    ∑ i ∈ Finset.range N, x i ^ r ≤ ∑ i ∈ Finset.range N, y i ^ r := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases (hx0 N).eq_or_lt with hxN | hxN
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, ← hxN, Real.zero_rpow hr.ne', add_zero]
      exact (ih fun k hk => h k (hk.trans N.le_succ)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (hy0 N) r))
    · have hxpos : ∀ i < N + 1, 0 < x i := fun i hi => hxN.trans_le (hx (Nat.lt_succ_iff.mp hi))
      have hprod : 0 < ∏ i ∈ Finset.range (N + 1), y i :=
        (Finset.prod_pos fun i hi => hxpos i (Finset.mem_range.mp hi)).trans_le (h _ le_rfl)
      have hypos : ∀ i < N + 1, 0 < y i := fun i hi =>
        (hy0 i).lt_of_ne' fun hi0 =>
          hprod.ne' (Finset.prod_eq_zero (Finset.mem_range.mpr hi) hi0)
      exact sum_range_rpow_le_of_forall_prod_range_le_of_pos hxpos hypos hx hy h hr

/-- Power sums of the singular values of a product: for `r > 0` and every `N`,
`∑ i < N, σ_i(A B) ^ r ≤ ∑ i < N, (σ_i(A) σ_i(B)) ^ r`.
[HornJohnson1991, Theorem 3.3.14].
Port of `NLAlib.sum_range_singularValues_mul_rpow_le`, there over `ℝ`. -/
theorem sum_range_singularValues_mul_rpow_le (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) (N : ℕ)
    {r : ℝ} (hr : 0 < r) :
    ∑ i ∈ Finset.range N, singularValues (A * B) i ^ r ≤
      ∑ i ∈ Finset.range N, (singularValues A i * singularValues B i) ^ r :=
  sum_range_rpow_le_of_forall_prod_range_le (singularValues_nonneg (A * B))
    (fun i => mul_nonneg (singularValues_nonneg A i) (singularValues_nonneg B i))
    (singularValues_antitone (A * B))
    (fun i j hij => mul_le_mul (singularValues_antitone A hij) (singularValues_antitone B hij)
      (singularValues_nonneg B j) (singularValues_nonneg A i))
    (fun k _ => prod_range_singularValues_mul_le A B k) hr

end NLAlib
