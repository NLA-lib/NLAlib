/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.CholeskyTraceBounds
public import NLAlib.Matrix.Factorizations.Cholesky
public import NLAlib.Matrix.Perturbation.Inverse

/-!
# Rounding errors of Cholesky factorization and of the solve with its factors

A run of left-looking Cholesky factorization in the standard model, as a trace of computed values
(`NLAlib.Computation.IsCholTrace`). For a positive definite $\mathbf{A}$ with
$4(n + 1)^2(u + v)\kappa(\mathbf{A}) \le 1$, read with relative error $v$ and factored at unit
roundoff $u$, every computed pivot is positive and the factor has a small backward error
[Higham2002, Theorem 10.3, Theorem 10.7]. The solve with the computed factors then has a small
relative error.

## Main definitions

* `NLAlib.Computation.IsCholEntryTrace`, `NLAlib.Computation.IsCholTrace`: the computed values.
* `NLAlib.Computation.lowerOf`: the lower triangular matrix of stored entries.
* `NLAlib.Computation.IsBackSubstTrace`: back substitution with the transpose of a lower factor.

## Main results

* `NLAlib.Computation.IsCholTrace.pos_and_specNorm_sub_le`: no breakdown, and the backward error.
* `NLAlib.Computation.norm_inv_mulVec_sub_le_of_isCholTrace`: the relative error of the solve.
-/

@[expose] public section

open Finset
open scoped Matrix

namespace NLAlib.Computation

/-- The running values of entry $(i, j)$ of left-looking Cholesky: $s_0 = a_{ij}$, and for $k < j$
a product $q$ with relative error $u$ of $l_{ik}l_{jk}$ and $s_{k+1}$ with relative error $u$ of
$s_k - q$. -/
def IsCholEntryTrace (u : ℝ) (a L : ℕ → ℕ → ℝ) (i j : ℕ) (s : ℕ → ℝ) : Prop :=
  s 0 = a i j ∧ ∀ k < j, ∃ q : ℝ, RelErr u (L i k * L j k) q ∧ RelErr u (s k - q) (s (k + 1))

/-- **A trace of left-looking Cholesky factorization** of order $n$ at unit roundoff $u$. The
diagonal entry is a rounded square root of its running value when that is nonnegative, and an
entry below it a rounded quotient when the diagonal entry is nonzero; a machine returns some
word otherwise, so the trace of a run exists before any pivot is known to be positive. -/
structure IsCholTrace (u : ℝ) (a L : ℕ → ℕ → ℝ) (n : ℕ) : Prop where
  /-- The diagonal entries. -/
  diag : ∀ j < n, ∃ s, IsCholEntryTrace u a L j j s ∧
    (0 ≤ s j → RelErr u (Real.sqrt (s j)) (L j j))
  /-- The entries below the diagonal. -/
  below : ∀ j < n, ∀ i, j < i → i < n → ∃ s, IsCholEntryTrace u a L i j s ∧
    (L j j ≠ 0 → RelErr u (s j / L j j) (L i j))

/-- The lower triangular matrix of the entries $l_{ij}$, $j \le i$. -/
def lowerOf (L : ℕ → ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if j ≤ i then L i j else 0

/-- **A trace of back substitution** with the transpose of a lower triangular factor: forward
substitution in reversed indices, as an in-place solve computes it. -/
def IsBackSubstTrace (u : ℝ) (L : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (n : ℕ) (x : ℕ → ℝ) : Prop :=
  IsSubstTrace (fun _ => RelErr u) (fun i j => L (n - 1 - j) (n - 1 - i))
    (fun i => b (n - 1 - i)) n (fun i => x (n - 1 - i))

/-! ### The entries of a trace -/

/-- An entry below the diagonal, with the errors on the products. -/
private theorem IsCholTrace.exists_below_eq {u : ℝ} {a L : ℕ → ℕ → ℝ} {n : ℕ}
    (h : IsCholTrace u a L n) (hu : 0 ≤ u) (hu1 : u < 1) {i j : ℕ} (hj : j < i) (hi : i < n)
    (hd : L j j ≠ 0) :
    ∃ θ : ℕ → ℝ, (∀ k ≤ j, |θ k| ≤ roundingFactor (n + 1) u) ∧
      a i j = ∑ k ∈ range (j + 1), L i k * L j k * (1 + θ k) := by
  obtain ⟨s, ⟨hs0, hsk⟩, hdiv⟩ := h.below j (by omega) i hj hi
  obtain ⟨ε, η, hε, hη, hs⟩ :=
    exists_eq_one_add_mul_sub_sum_of_relErr (c := fun k => L i k * L j k) hu hu1 j hsk
  obtain ⟨δ, hδ, hL⟩ := hdiv hd
  have hδ1 := isRoundingProduct_one_of_abs_le hδ
  have hδpos := one_add_pos_of_isRoundingProduct hδ1 hu hu1
  have hεpos := one_add_pos_of_isRoundingProduct hε hu hu1
  have hlast := hδ1.inv.div hε
  refine ⟨fun k => if k < j then η k else (1 + ((1 + δ)⁻¹ - 1)) / (1 + ε) - 1,
    fun k hk => ?_, ?_⟩
  · by_cases hkj : k < j
    · simp only [if_pos hkj]
      exact ((hη k hkj).mono hu (by omega)).abs_le hu1
    · simp only [if_neg hkj]
      exact (hlast.mono hu (by omega)).abs_le hu1
  · rw [sum_range_succ]
    simp only [lt_irrefl, if_false]
    rw [sum_congr rfl fun k hk => by rw [if_pos (mem_range.mp hk)]]
    rw [hs0] at hs
    have hsj : s j = L i j * L j j / (1 + δ) := by
      rw [hL]
      field_simp
    have hdiff : a i j - ∑ k ∈ range j, L i k * L j k * (1 + η k) =
        L i j * L j j * (1 + ((1 + δ)⁻¹ - 1)) / (1 + ε) := by
      have h2 : (1 + ε) * (a i j - ∑ k ∈ range j, L i k * L j k * (1 + η k)) =
          L i j * L j j / (1 + δ) := by rw [← hs, hsj]
      rw [eq_div_iff hεpos.ne']
      rw [mul_comm, h2]
      field_simp
      ring
    have h3 : L i j * L j j * (1 + ((1 + ((1 + δ)⁻¹ - 1)) / (1 + ε) - 1)) =
        L i j * L j j * (1 + ((1 + δ)⁻¹ - 1)) / (1 + ε) := by ring
    linarith

/-- A diagonal entry: if its running value is positive, the pivot is positive and the entry is
a sum of perturbed squares. -/
private theorem IsCholTrace.exists_diag_eq {u : ℝ} {a L : ℕ → ℕ → ℝ} {n : ℕ}
    (h : IsCholTrace u a L n) (hu : 0 ≤ u) (hu1 : u < 1) {j : ℕ} (hj : j < n) :
    ∃ θ : ℕ → ℝ, (∀ k ≤ j, |θ k| ≤ roundingFactor (n + 1) u) ∧
      (0 < a j j - ∑ k ∈ range j, L j k * L j k * (1 + θ k) →
        0 < L j j ∧ a j j = ∑ k ∈ range (j + 1), L j k * L j k * (1 + θ k)) := by
  obtain ⟨s, ⟨hs0, hsk⟩, hroot⟩ := h.diag j hj
  obtain ⟨ε, η, hε, hη, hs⟩ :=
    exists_eq_one_add_mul_sub_sum_of_relErr (c := fun k => L j k * L j k) hu hu1 j hsk
  rw [hs0] at hs
  have hεpos := one_add_pos_of_isRoundingProduct hε hu hu1
  obtain ⟨θj, hθj, himp⟩ : ∃ θj : ℝ, |θj| ≤ roundingFactor (n + 1) u ∧
      (0 < a j j - ∑ k ∈ range j, L j k * L j k * (1 + η k) →
        0 < L j j ∧ a j j - ∑ k ∈ range j, L j k * L j k * (1 + η k) =
          L j j * L j j * (1 + θj)) := by
    by_cases ht : 0 < a j j - ∑ k ∈ range j, L j k * L j k * (1 + η k)
    · have hsj : 0 < s j := by rw [hs]; positivity
      obtain ⟨δ, hδ, hL⟩ := hroot hsj.le
      have hδ1 := isRoundingProduct_one_of_abs_le hδ
      have hδpos := one_add_pos_of_isRoundingProduct hδ1 hu hu1
      have hp := (hδ1.inv.mul hδ1.inv).div hε
      refine ⟨_, (hp.mono hu (by omega)).abs_le hu1, fun _ => ⟨?_, ?_⟩⟩
      · rw [hL]
        exact mul_pos (Real.sqrt_pos.mpr hsj) hδpos
      · have hsq : L j j * L j j = s j * (1 + δ) ^ 2 := by
          rw [hL]
          nlinarith [Real.mul_self_sqrt hsj.le]
        rw [hsq, hs]
        field_simp
        ring
    · exact ⟨0, by simpa using roundingFactor_nonneg hu hu1, fun h' => absurd h' ht⟩
  refine ⟨fun k => if k < j then η k else θj, fun k hk => ?_, ?_⟩
  · by_cases hkj : k < j
    · simp only [if_pos hkj]
      exact ((hη k hkj).mono hu (by omega)).abs_le hu1
    · simpa only [if_neg hkj] using hθj
  · beta_reduce
    have hs1 : ∑ k ∈ range j, L j k * L j k * (1 + if k < j then η k else θj) =
        ∑ k ∈ range j, L j k * L j k * (1 + η k) :=
      sum_congr rfl fun k hk => by rw [if_pos (mem_range.mp hk)]
    rw [sum_range_succ, hs1]
    simp only [lt_irrefl, if_false]
    intro ht
    obtain ⟨hp, he⟩ := himp ht
    exact ⟨hp, by linarith⟩

/-- A pivot whose entry is a sum of perturbed squares. -/
private def IsGoodPivot (u : ℝ) (a L : ℕ → ℕ → ℝ) (n j : ℕ) : Prop :=
  0 < L j j ∧ ∃ θ : ℕ → ℝ, (∀ k ≤ j, |θ k| ≤ roundingFactor (n + 1) u) ∧
    a j j = ∑ k ∈ range (j + 1), L j k * L j k * (1 + θ k)

/-- The entries of the columns before `J`, on and below the diagonal. -/
private def truncOf (L : ℕ → ℕ → ℝ) (n J : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i m => if (m : ℕ) < J ∧ m ≤ i then L i m else 0

private theorem sum_range_eq_sum_fin {n K : ℕ} (hK : K ≤ n) (f : ℕ → ℝ) :
    ∑ m ∈ range K, f m = ∑ m : Fin n, if (m : ℕ) < K then f m else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun m => if m < K then f m else 0) n, ← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext m
  simp only [mem_range, mem_filter]
  omega

/-- An entry of a truncated product, from its expression with errors on the products. -/
private theorem abs_sub_mul_apply_le {n : ℕ} {A M : Matrix (Fin n) (Fin n) ℝ} {a L : ℕ → ℕ → ℝ}
    {θ : ℕ → ℝ} {γ v t : ℝ} {K : ℕ} {i k : Fin n} (hK : K ≤ n)
    (hM : ∀ m : Fin n, M i m * M k m = if (m : ℕ) < K then L i m * L k m else 0)
    (hθ : ∀ m < K, |θ m| ≤ γ) (ha : |a i k - A i k| ≤ v * |A i k|)
    (he : a i k = t + ∑ m ∈ range K, L i m * L k m * (1 + θ m)) :
    |A i k - (M * Mᵀ) i k - t| ≤ v * |A i k| + γ * ∑ m, |M i m| * |M k m| := by
  have hprod : (M * Mᵀ) i k = ∑ m ∈ range K, L i m * L k m := by
    rw [Matrix.mul_apply, sum_range_eq_sum_fin hK]
    exact sum_congr rfl fun m _ => hM m
  have hsum : |∑ m ∈ range K, L i m * L k m * θ m| ≤ γ * ∑ m, |M i m| * |M k m| := by
    have hto : ∑ m, |M i m| * |M k m| = ∑ m ∈ range K, |L i m * L k m| := by
      rw [sum_range_eq_sum_fin hK]
      refine sum_congr rfl fun m _ => ?_
      rw [← abs_mul, hM]
      split_ifs <;> simp
    rw [hto, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hθ m (mem_range.mp hm)) (abs_nonneg _)
  have heq : A i k - (M * Mᵀ) i k - t =
      -(a i k - A i k) + ∑ m ∈ range K, L i m * L k m * θ m := by
    rw [hprod, he]
    simp only [mul_add, mul_one, sum_add_distrib]
    ring
  rw [heq]
  refine (abs_add_le _ _).trans (add_le_add ?_ hsum)
  rwa [abs_neg]

/-- The entries of a truncated product for the columns before `J`, once these have good
pivots. -/
private theorem IsCholTrace.abs_sub_truncOf_apply_le {n J : ℕ} {u v : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {a L : ℕ → ℕ → ℝ} (h : IsCholTrace u a L n) (hu : 0 ≤ u)
    (hu1 : u < 1) (ha : ∀ i j : Fin n, j ≤ i → |a i j - A i j| ≤ v * |A i j|)
    (hgood : ∀ k < J, IsGoodPivot u a L n k) {i k : Fin n} (hki : k ≤ i) (hk : (k : ℕ) < J) :
    |A i k - (truncOf L n J * (truncOf L n J)ᵀ) i k - 0| ≤ v * |A i k| +
      roundingFactor (n + 1) u * ∑ m, |truncOf L n J i m| * |truncOf L n J k m| := by
  have hM : ∀ m : Fin n, truncOf L n J i m * truncOf L n J k m =
      if (m : ℕ) < (k : ℕ) + 1 then L i m * L k m else 0 := by
    intro m
    have hki' : (k : ℕ) ≤ i := hki
    simp only [truncOf, Matrix.of_apply, Fin.le_def]
    by_cases hm : (m : ℕ) < (k : ℕ) + 1
    · rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, if_pos hm]
    · rw [if_neg hm, if_neg (fun hc : (m : ℕ) < J ∧ (m : ℕ) ≤ k => hm (by omega)), mul_zero]
  obtain ⟨θ, hθ, he⟩ : ∃ θ : ℕ → ℝ, (∀ m ≤ (k : ℕ), |θ m| ≤ roundingFactor (n + 1) u) ∧
      a i k = ∑ m ∈ range ((k : ℕ) + 1), L i m * L k m * (1 + θ m) := by
    rcases eq_or_lt_of_le hki with heq | hlt
    · obtain ⟨_, θ, hθ, he⟩ := hgood k hk
      subst heq
      exact ⟨θ, hθ, he⟩
    · exact h.exists_below_eq hu hu1 hlt i.isLt (hgood k hk).1.ne'
  exact abs_sub_mul_apply_le (t := 0) (by omega) hM (fun m hm => hθ m (by omega)) (ha i k hki)
    (by rw [zero_add]; exact he)

/-- A vector with unit entry `j`, zero after it, in the null space of the computed rows. -/
private theorem exists_null_vector {n : ℕ} (L : ℕ → ℕ → ℝ) (j : Fin n)
    (hpos : ∀ k : Fin n, k < j → 0 < L k k) :
    ∃ x : Fin n → ℝ, x j = 1 ∧ (∀ i, j < i → x i = 0) ∧ (truncOf L n j)ᵀ *ᵥ x = 0 := by
  classical
  set T : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i k =>
    if k < j ∧ k ≤ i ∧ i ≤ j then L i k else if i = k then 1 else 0 with hTdef
  have hlow : T.BlockTriangular OrderDual.toDual := fun i k hik => by
    have hik' : i < k := hik
    simp [hTdef, not_le.mpr hik', hik'.ne]
  have hdet : T.det ≠ 0 := by
    rw [Matrix.det_of_isLowerTriangular T hlow]
    refine prod_ne_zero_iff.mpr fun i _ => ?_
    by_cases hi : i < j
    · simpa [hTdef, hi, hi.le] using (hpos i hi).ne'
    · simp [hTdef, hi]
  have hU : IsUnit Tᵀ.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hdet
  set x := Tᵀ⁻¹ *ᵥ Pi.single j (1 : ℝ) with hx
  have hTx : Tᵀ *ᵥ x = Pi.single j 1 := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
  have hcoord : ∀ i, ∑ k, T k i * x k = (Pi.single j (1 : ℝ) : Fin n → ℝ) i := fun i => by
    have := congrFun hTx i
    simpa [Matrix.mulVec, dotProduct] using this
  have hcol : ∀ i, j ≤ i → x i = (Pi.single j (1 : ℝ) : Fin n → ℝ) i := by
    intro i hi
    rw [← hcoord i]
    have hTk : ∀ k, T k i * x k = if k = i then x k else 0 := by
      intro k
      by_cases hk : k = i <;> simp [hTdef, not_lt.mpr hi, hk]
    rw [sum_congr rfl fun k _ => hTk k, sum_ite_eq' univ i]
    simp
  refine ⟨x, by simpa using hcol j le_rfl, fun i hi => ?_, ?_⟩
  · simpa [hi.ne'] using hcol i hi.le
  funext m
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply]
  by_cases hm : m < j
  · have h := hcoord m
    rw [Pi.single_eq_of_ne hm.ne] at h
    rw [← h]
    refine sum_congr rfl fun i _ => ?_
    by_cases hi : j < i
    · have hxi : x i = 0 := by simpa [hi.ne'] using hcol i hi.le
      simp [hxi]
    · by_cases hmi : m ≤ i
      · simp [truncOf, hTdef, hm, hmi, not_lt.mp hi]
      · have hne : i ≠ m := fun e => hmi e.ge
        simp [truncOf, hTdef, hm, hmi, hne]
  · refine sum_eq_zero fun i _ => ?_
    simp [truncOf, hm]

/-! ### No breakdown and the backward error -/

/-- The sizes that the smallness hypothesis gives to the rounding factor and to the errors. -/
private theorem chol_constants {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u v : ℝ} (hn : 0 < n)
    (hA : A.PosDef) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hsmall : 4 * ((n : ℝ) + 1) ^ 2 * (u + v) * pseudoConditionNumber A ≤ 1) :
    u < 1 ∧ roundingFactor (n + 1) u ≤ 8 / 7 * ((n : ℝ) + 1) * u ∧
      roundingFactor (n + 1) u ≤ 1 / 7 ∧ v * ((n : ℝ) + 1) ≤ 1 / 8 ∧ v ≤ 1 / 16 ∧
      0 < specNorm A⁻¹ ∧ 4 * ((n : ℝ) + 1) ^ 2 * (u + v) * specNorm A ≤ (specNorm A⁻¹)⁻¹ := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hκ := one_le_pseudoConditionNumber hA.isUnit.ne_zero
  rw [pseudoConditionNumber_of_isUnit hA.isUnit] at hκ hsmall
  have hN : (2 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set N : ℝ := (n : ℝ) + 1 with hNdef
  have hc : 0 < specNorm A⁻¹ := by
    refine lt_of_le_of_ne (specNorm_nonneg _) fun h0 => ?_
    rw [← h0, mul_zero] at hκ
    linarith
  have hx0 : 0 ≤ N ^ 2 * (u + v) := by positivity
  have hx : 4 * (N ^ 2 * (u + v)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hκ (by positivity : 0 ≤ 4 * (N ^ 2 * (u + v)))
    nlinarith
  have hNN : 2 * N ≤ N ^ 2 := by nlinarith
  have hNu : N * u ≤ 1 / 8 := by
    have h1 := mul_le_mul_of_nonneg_right hNN hu
    nlinarith [mul_nonneg (sq_nonneg N) hv]
  have hNv : v * N ≤ 1 / 8 := by
    have h1 := mul_le_mul_of_nonneg_right hNN hv
    nlinarith [mul_nonneg (sq_nonneg N) hu]
  have hu1 : u < 1 := by nlinarith
  have hNu0 : 0 ≤ N * u := by positivity
  have hγ : roundingFactor (n + 1) u ≤ 8 / 7 * N * u := by
    have hg := roundingFactor_le (n := n + 1) hu (by push_cast; linarith)
    push_cast at hg
    refine hg.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨hu1, hγ, by linarith, hNv, by nlinarith, hc, ?_⟩
  calc 4 * N ^ 2 * (u + v) * specNorm A
      = 4 * N ^ 2 * (u + v) * (specNorm A * specNorm A⁻¹) * (specNorm A⁻¹)⁻¹ := by
        field_simp
    _ ≤ 1 * (specNorm A⁻¹)⁻¹ := by gcongr
    _ = (specNorm A⁻¹)⁻¹ := one_mul _

/-- The two inequalities that the positivity of the next pivot uses. -/
private theorem chol_numeric {N u v γ Λ μ Φ : ℝ} (hN : 2 ≤ N) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hΛ : 0 ≤ Λ) (hγN : γ ≤ 8 / 7 * N * u) (hμ : 4 * N ^ 2 * (u + v) * Λ ≤ μ)
    (hμ0 : 0 < μ) (hΦ0 : 0 ≤ Φ) (hΦ : Φ ≤ 5 / 4 * (N - 1) * Λ) :
    v * Λ * (N - 1) + 2 * γ * Φ ≤ μ ∧ v * Λ * (N - 1) + 4 * γ * Λ < μ := by
  have hN0 : 0 ≤ N := by linarith
  have hP : 0 ≤ N * N * u * Λ := by positivity
  have hQ : 0 ≤ N * N * v * Λ := by positivity
  have hR : 2 * (N * u * Λ) ≤ N * N * u * Λ := by
    have := mul_le_mul_of_nonneg_right hN (by positivity : 0 ≤ N * u * Λ)
    nlinarith
  have ha1 : γ * Φ ≤ 8 / 7 * N * u * (5 / 4 * (N - 1) * Λ) :=
    mul_le_mul hγN hΦ hΦ0 (by positivity)
  have ha2 : 8 / 7 * N * u * (5 / 4 * (N - 1) * Λ) ≤ 10 / 7 * (N * N * u * Λ) := by
    nlinarith [mul_nonneg hN0 (mul_nonneg hu hΛ)]
  have hb : γ * Λ ≤ 8 / 7 * (N * u * Λ) := by
    have := mul_le_mul_of_nonneg_right hγN hΛ
    linarith
  have hc : v * Λ * (N - 1) ≤ N * N * v * Λ := by
    have h1 : N - 1 ≤ N * N := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hv hΛ)
    linarith
  have hμ' : 4 * (N * N * u * Λ + N * N * v * Λ) ≤ μ := by nlinarith
  constructor <;> nlinarith

private theorem IsGoodPivot.sum_sq_le {n j : ℕ} {u v : ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    {a L : ℕ → ℕ → ℝ} (hj : j < n) (hg : IsGoodPivot u a L n j)
    (ha : ∀ i j : Fin n, j ≤ i → |a i j - A i j| ≤ v * |A i j|) (hv0 : 0 ≤ v) (hv : v ≤ 1 / 16)
    (hγ : roundingFactor (n + 1) u ≤ 1 / 7) :
    ∑ m ∈ range (j + 1), L j m ^ 2 ≤ 5 / 4 * specNorm A := by
  obtain ⟨_, θ, hθ, he⟩ := hg
  have hA1 := ha ⟨j, hj⟩ ⟨j, hj⟩ le_rfl
  have hAΛ : |A ⟨j, hj⟩ ⟨j, hj⟩| ≤ specNorm A := by
    simpa using norm_apply_le_specNorm A ⟨j, hj⟩ ⟨j, hj⟩
  simp only at hA1
  have hup : a j j ≤ (1 + v) * specNorm A := by
    have h1 := (abs_le.mp hA1).2
    have h2 := le_abs_self (A ⟨j, hj⟩ ⟨j, hj⟩)
    have h3 := mul_le_mul_of_nonneg_left hAΛ hv0
    linarith
  have hlow : (1 - roundingFactor (n + 1) u) * ∑ m ∈ range (j + 1), L j m ^ 2 ≤ a j j := by
    rw [he, mul_sum]
    refine sum_le_sum fun m hm => ?_
    have h1 := (abs_le.mp (hθ m (by have := mem_range.mp hm; omega))).1
    nlinarith [mul_self_nonneg (L j m)]
  have hR : 0 ≤ ∑ m ∈ range (j + 1), L j m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hΛ := specNorm_nonneg A
  nlinarith

private theorem sum_truncOf_sq_le {n : ℕ} (L : ℕ → ℕ → ℝ) (J : ℕ) (i : Fin n) :
    ∑ m, truncOf L n J i m ^ 2 ≤ ∑ m ∈ range ((i : ℕ) + 1), L i m ^ 2 := by
  rw [sum_range_eq_sum_fin (K := (i : ℕ) + 1) i.isLt]
  refine sum_le_sum fun m _ => ?_
  simp only [truncOf, Matrix.of_apply, Fin.le_def]
  by_cases hmi : (m : ℕ) ≤ i
  · rw [if_pos (by omega : (m : ℕ) < (i : ℕ) + 1)]
    split_ifs
    · exact le_rfl
    · simpa using sq_nonneg (L i m)
  · rw [if_neg (by omega : ¬ (m : ℕ) < (i : ℕ) + 1), if_neg (fun hc => hmi hc.2)]
    simp

/-- The entries up to `j` of the error of the truncated product, with the running value `t` of
the next pivot in place of its square. -/
private theorem IsCholTrace.abs_sub_step_le {n j : ℕ} {u v t : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {a L : ℕ → ℕ → ℝ} {θ : ℕ → ℝ} (h : IsCholTrace u a L n)
    (hA : A.PosDef) (hu : 0 ≤ u) (hu1 : u < 1) (hv : 0 ≤ v) (hj : j < n)
    (ha : ∀ i j : Fin n, j ≤ i → |a i j - A i j| ≤ v * |A i j|)
    (hgood : ∀ k < j, IsGoodPivot u a L n k)
    (hθ : ∀ k ≤ j, |θ k| ≤ roundingFactor (n + 1) u)
    (ht : a j j = t + ∑ m ∈ range j, L j m * L j m * (1 + θ m)) (i k : Fin n)
    (hi : i ≤ ⟨j, hj⟩) (hk : k ≤ ⟨j, hj⟩) :
    |A i k - (truncOf L n j * (truncOf L n j)ᵀ) i k -
        (if i = ⟨j, hj⟩ ∧ k = ⟨j, hj⟩ then t else 0)| ≤
      v * specNorm A + roundingFactor (n + 1) u *
        ∑ m, |truncOf L n j i m| * |truncOf L n j k m| := by
  have hvA : ∀ p q : Fin n, v * |A p q| ≤ v * specNorm A := fun p q =>
    mul_le_mul_of_nonneg_left (by simpa using norm_apply_le_specNorm A p q) hv
  have hlo : ∀ p q : Fin n, q ≤ p → p ≤ ⟨j, hj⟩ →
      |A p q - (truncOf L n j * (truncOf L n j)ᵀ) p q -
          (if p = ⟨j, hj⟩ ∧ q = ⟨j, hj⟩ then t else 0)| ≤
        v * specNorm A + roundingFactor (n + 1) u *
          ∑ m, |truncOf L n j p m| * |truncOf L n j q m| := by
    intro p q hqp hp
    rcases eq_or_lt_of_le (hqp.trans hp) with hq | hq
    · obtain rfl : p = ⟨j, hj⟩ := le_antisymm hp (hq ▸ hqp)
      subst hq
      rw [if_pos ⟨rfl, rfl⟩]
      refine (abs_sub_mul_apply_le (a := a) (L := L) (θ := θ) (K := j) hj.le (fun m => ?_)
        (fun m hm => hθ m hm.le) (ha _ _ le_rfl) ht).trans (add_le_add_left (hvA _ _) _)
      simp only [truncOf, Matrix.of_apply, Fin.le_def]
      by_cases hm : (m : ℕ) < j
      · rw [if_pos ⟨hm, hm.le⟩, if_pos hm]
      · rw [if_neg (fun hc => hm hc.1), if_neg hm, mul_zero]
    · rw [if_neg (fun hc => hq.ne hc.2)]
      exact (h.abs_sub_truncOf_apply_le hu hu1 ha hgood hqp hq).trans
        (add_le_add_left (hvA _ _) _)
  rcases le_total k i with hki | hik
  · exact hlo i k hki hi
  · have hsym : A k i = A i k := by simpa using (hA.isHermitian.apply k i).symm
    have hM : (truncOf L n j * (truncOf L n j)ᵀ) k i =
        (truncOf L n j * (truncOf L n j)ᵀ) i k := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      exact sum_congr rfl fun m _ => mul_comm _ _
    have := hlo k i hik hk
    rw [hsym, hM] at this
    simpa only [and_comm, mul_comm] using this

/-- A pivot is good when those before it are. -/
private theorem IsCholTrace.isGoodPivot_of_forall_lt {n j : ℕ} {u v : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {a L : ℕ → ℕ → ℝ} (h : IsCholTrace u a L n) (hA : A.PosDef)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : ∀ i j : Fin n, j ≤ i → |a i j - A i j| ≤ v * |A i j|)
    (hsmall : 4 * ((n : ℝ) + 1) ^ 2 * (u + v) * pseudoConditionNumber A ≤ 1) (hj : j < n)
    (hgood : ∀ k < j, IsGoodPivot u a L n k) : IsGoodPivot u a L n j := by
  obtain ⟨hu1, hγN, hγ7, hvN, hv16, hc, hμ⟩ := chol_constants (by omega) hA hu hv hsmall
  have hγ0 := roundingFactor_nonneg (n := n + 1) hu hu1
  have hΛ := specNorm_nonneg A
  obtain ⟨θ, hθ, himp⟩ := h.exists_diag_eq hu hu1 hj
  suffices ht : 0 < a j j - ∑ k ∈ range j, L j k * L j k * (1 + θ k) from
    ⟨(himp ht).1, θ, hθ, (himp ht).2⟩
  obtain ⟨x, hxj, hx0, hMx⟩ := exists_null_vector L ⟨j, hj⟩ fun k hk => (hgood k hk).1
  have hμA : (specNorm A⁻¹)⁻¹ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
    rw [inv_mul_le_iff₀ hc]
    exact dotProduct_self_le_specNorm_inv_mul hA x
  have hΦ0 : 0 ≤ ∑ m, ∑ i, (if i < (⟨j, hj⟩ : Fin n) then truncOf L n j i m else 0) ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have hΦ : ∑ m, ∑ i, (if i < (⟨j, hj⟩ : Fin n) then truncOf L n j i m else 0) ^ 2 ≤
      5 / 4 * (((n : ℝ) + 1) - 1) * specNorm A := by
    rw [sum_comm]
    have hrow : ∀ i : Fin n,
        ∑ m, (if i < (⟨j, hj⟩ : Fin n) then truncOf L n j i m else 0) ^ 2 ≤
          5 / 4 * specNorm A := fun i => by
      by_cases hi : i < (⟨j, hj⟩ : Fin n)
      · simp only [if_pos hi]
        exact (sum_truncOf_sq_le L j i).trans
          ((hgood i hi).sum_sq_le i.isLt ha hv hv16 hγ7)
      · simp only [if_neg hi]
        simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4) hΛ
    refine (sum_le_sum fun i _ => hrow i).trans_eq ?_
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hN : (2 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    linarith
  obtain ⟨hC, hfin⟩ := chol_numeric hN hu hv hΛ hγN hμ (inv_pos.mpr hc) hΦ0 hΦ
  rw [add_sub_cancel_right] at hC hfin
  refine pos_of_mul_dotProduct_self_le_of_abs_sub_le (M := truncOf L n j) (j := ⟨j, hj⟩) hΛ hv
    hγ0 hμA hxj hx0 hMx
    (fun i k hi hk => h.abs_sub_step_le hA hu hu1 hv hj ha hgood hθ (by ring) i k hi hk)
    ?_ hC hγ7 (by linarith) hfin
  have hw : ∑ m, truncOf L n j (⟨j, hj⟩ : Fin n) m ^ 2 = ∑ m ∈ range j, L j m ^ 2 := by
    rw [sum_range_eq_sum_fin hj.le]
    refine sum_congr rfl fun m _ => ?_
    simp only [truncOf, Matrix.of_apply, Fin.le_def]
    by_cases hm : (m : ℕ) < j
    · rw [if_pos ⟨hm, hm.le⟩, if_pos hm]
    · rw [if_neg (fun hc => hm hc.1), if_neg hm]
      simp
  rw [hw, mul_sum]
  have hA1 := ha ⟨j, hj⟩ ⟨j, hj⟩ le_rfl
  have hAΛ : |A ⟨j, hj⟩ ⟨j, hj⟩| ≤ specNorm A := by
    simpa using norm_apply_le_specNorm A ⟨j, hj⟩ ⟨j, hj⟩
  simp only at hA1
  have hup : a j j ≤ (1 + v) * specNorm A := by
    have h1 := (abs_le.mp hA1).2
    have h2 := le_abs_self (A ⟨j, hj⟩ ⟨j, hj⟩)
    have h3 := mul_le_mul_of_nonneg_left hAΛ hv
    linarith
  have hsum : ∑ m ∈ range j, (1 - roundingFactor (n + 1) u) * L j m ^ 2 ≤
      ∑ k ∈ range j, L j k * L j k * (1 + θ k) := by
    refine sum_le_sum fun m hm => ?_
    have h1 := (abs_le.mp (hθ m (mem_range.mp hm).le)).1
    nlinarith [mul_self_nonneg (L j m)]
  linarith

private theorem IsCholTrace.forall_isGoodPivot {n : ℕ} {u v : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {a L : ℕ → ℕ → ℝ} (h : IsCholTrace u a L n) (hA : A.PosDef)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : ∀ i j : Fin n, j ≤ i → |a i j - A i j| ≤ v * |A i j|)
    (hsmall : 4 * ((n : ℝ) + 1) ^ 2 * (u + v) * pseudoConditionNumber A ≤ 1) :
    ∀ j < n, IsGoodPivot u a L n j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    exact h.isGoodPivot_of_forall_lt hA hu hv ha hsmall hj fun k hk => ih k hk (by omega)

private theorem truncOf_self (L : ℕ → ℕ → ℝ) (n : ℕ) : truncOf L n n = lowerOf L n := by
  ext i m
  simp [truncOf, lowerOf]

/-- The bounds on the computed factor, from a trace. -/
private theorem IsCholTrace.frobNorm_bounds {n : ℕ} {u v : ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    {a L : ℕ → ℕ → ℝ} (h : IsCholTrace u a L n) (hA : A.PosDef) (hu : 0 ≤ u) (hu1 : u < 1)
    (hv : 0 ≤ v) (ha : ∀ i j : Fin n, j ≤ i → |a i j - A i j| ≤ v * |A i j|)
    (hgood : ∀ j < n, IsGoodPivot u a L n j) (hv16 : v ≤ 1 / 16)
    (hγ7 : roundingFactor (n + 1) u ≤ 1 / 7) :
    frobNorm (lowerOf L n) ^ 2 ≤ 5 / 4 * n * specNorm A ∧
      frobNorm (A - lowerOf L n * (lowerOf L n)ᵀ) ≤
        v * (n * specNorm A) + roundingFactor (n + 1) u * frobNorm (lowerOf L n) ^ 2 := by
  have hγ0 := roundingFactor_nonneg (n := n + 1) hu hu1
  constructor
  · rw [frobNorm_sq_eq_sum_sq, ← truncOf_self]
    refine (sum_le_sum fun i _ => (sum_truncOf_sq_le L n i).trans
      ((hgood i i.isLt).sum_sq_le i.isLt ha hv hv16 hγ7)).trans_eq ?_
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · refine frobNorm_sub_mul_transpose_le hv hγ0 fun i k => ?_
    rw [← truncOf_self]
    have hlo : ∀ p q : Fin n, q ≤ p → |A p q - (truncOf L n n * (truncOf L n n)ᵀ) p q| ≤
        v * |A p q| + roundingFactor (n + 1) u *
          ∑ m, |truncOf L n n p m| * |truncOf L n n q m| := fun p q hqp => by
      simpa using h.abs_sub_truncOf_apply_le hu hu1 ha hgood hqp q.isLt
    rcases le_total k i with hki | hik
    · exact hlo i k hki
    · have hsym : A k i = A i k := by simpa using (hA.isHermitian.apply k i).symm
      have hM : (truncOf L n n * (truncOf L n n)ᵀ) k i =
          (truncOf L n n * (truncOf L n n)ᵀ) i k := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
        exact sum_congr rfl fun m _ => mul_comm _ _
      have := hlo k i hik
      rw [hsym, hM] at this
      simpa only [mul_comm] using this

/-! ### The solve with the computed factor -/

/-- Forward substitution as an exact solve with a perturbed lower factor. -/
private theorem exists_lower_mulVec_eq {n : ℕ} {u : ℝ} {L : ℕ → ℕ → ℝ} {rh y : ℕ → ℝ}
    (hy : IsSubstTrace (fun _ => RelErr u) L rh n y) (hd : ∀ i < n, L i i ≠ 0) (hu : 0 ≤ u)
    (hu1 : u < 1) :
    ∃ D : Matrix (Fin n) (Fin n) ℝ, (∀ i k, |D i k| ≤ roundingFactor n u * |lowerOf L n i k|) ∧
      (lowerOf L n + D) *ᵥ (fun i : Fin n => y i) = fun i : Fin n => rh i := by
  obtain ⟨Δ, hΔ, hsum⟩ := hy.exists_sum_add_mul_eq hd hu hu1
  have hγ0 := roundingFactor_nonneg (n := n) hu hu1
  refine ⟨Matrix.of fun i k => if k ≤ i then Δ i k else 0, fun i k => ?_, ?_⟩
  · by_cases hki : k ≤ i
    · simpa [lowerOf, hki] using hΔ i i.isLt k hki
    · simp [lowerOf, hki]
  · funext i
    rw [← hsum i i.isLt, sum_range_eq_sum_fin (K := (i : ℕ) + 1) i.isLt]
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, lowerOf, Matrix.of_apply]
    refine sum_congr rfl fun k _ => ?_
    by_cases hki : k ≤ i
    · have : (k : ℕ) < (i : ℕ) + 1 := Nat.lt_succ_of_le hki
      simp [hki, this]
    · have : ¬ (k : ℕ) < (i : ℕ) + 1 := fun hc => hki (Nat.le_of_lt_succ hc)
      simp [hki, this]

/-- Back substitution as an exact solve with a perturbed transposed factor. -/
private theorem exists_upper_mulVec_eq {n : ℕ} {u : ℝ} {L : ℕ → ℕ → ℝ} {y d : ℕ → ℝ}
    (hd : IsBackSubstTrace u L y n d) (hdiag : ∀ i < n, L i i ≠ 0) (hu : 0 ≤ u) (hu1 : u < 1) :
    ∃ D : Matrix (Fin n) (Fin n) ℝ,
      (∀ k l, |D k l| ≤ roundingFactor n u * |(lowerOf L n)ᵀ k l|) ∧
      ((lowerOf L n)ᵀ + D) *ᵥ (fun i : Fin n => d i) = fun i : Fin n => y i := by
  have hdiag' : ∀ i < n, (fun i j => L (n - 1 - j) (n - 1 - i)) i i ≠ 0 :=
    fun i _ => hdiag (n - 1 - i) (by omega)
  obtain ⟨Δ, hΔ, hsum⟩ := IsSubstTrace.exists_sum_add_mul_eq hd hdiag' hu hu1
  refine ⟨Matrix.of fun k l => if k ≤ l then Δ (n - 1 - k) (n - 1 - l) else 0,
    fun k l => ?_, ?_⟩
  · by_cases hkl : k ≤ l
    · have hkl' : (k : ℕ) ≤ l := hkl
      have hl := l.isLt
      have hk := k.isLt
      have := hΔ (n - 1 - k) (by omega) (n - 1 - l) (by omega)
      rw [show n - 1 - (n - 1 - (l : ℕ)) = l by omega,
        show n - 1 - (n - 1 - (k : ℕ)) = k by omega] at this
      simpa [lowerOf, hkl] using this
    · have hγ0 := roundingFactor_nonneg (n := n) hu hu1
      simp only [Matrix.of_apply, if_neg hkl, abs_zero]
      positivity
  · funext k
    have hk := k.isLt
    have hs := hsum (n - 1 - k) (by omega)
    rw [show n - 1 - (n - 1 - (k : ℕ)) = k by omega,
      sum_range_eq_sum_fin (n := n) (K := n - 1 - (k : ℕ) + 1) (by omega)] at hs
    rw [← hs, ← Equiv.sum_comp Fin.revPerm]
    simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.transpose_apply, lowerOf,
      Matrix.of_apply]
    refine sum_congr rfl fun j _ => ?_
    have hj := j.isLt
    have hrev : ((Fin.revPerm j : Fin n) : ℕ) = n - 1 - j := by
      simp only [Fin.revPerm_apply, Fin.val_rev]
      omega
    by_cases hc : k ≤ j
    · have hkj : (k : ℕ) ≤ j := hc
      have h1 : ((Fin.revPerm j : Fin n) : ℕ) < n - 1 - (k : ℕ) + 1 := by omega
      rw [if_pos hc, if_pos hc, if_pos h1, hrev, show n - 1 - (n - 1 - (j : ℕ)) = j by omega]
    · have hkj : ¬ (k : ℕ) ≤ j := hc
      have h1 : ¬ ((Fin.revPerm j : Fin n) : ℕ) < n - 1 - (k : ℕ) + 1 := by omega
      rw [if_neg hc, if_neg hc, if_neg h1]
      ring

/-- The scaling of the right side read with relative error $v$. -/
private theorem exists_scaling {n : ℕ} {v : ℝ} {r : Fin n → ℝ} {rh : ℕ → ℝ} (hv : 0 ≤ v)
    (hv16 : v ≤ 1 / 16) (hr : ∀ i : Fin n, |rh i - r i| ≤ v * |r i|) :
    ∃ w : Fin n → ℝ, (∀ i, |w i - 1| ≤ 2 * v) ∧ ∀ i, w i * rh i = r i := by
  refine ⟨fun i => if r i = 0 then 1 else r i / rh i, fun i => ?_, fun i => ?_⟩ <;>
    by_cases h0 : r i = 0
  · simpa [h0] using hv
  · have hlow : (1 - v) * |r i| ≤ |rh i| := by
      have := abs_sub_abs_le_abs_sub (r i) (rh i)
      rw [abs_sub_comm] at this
      linarith [hr i]
    have hrpos : 0 < |r i| := abs_pos.mpr h0
    have hrh : 0 < |rh i| := lt_of_lt_of_le (by nlinarith) hlow
    have hrh0 : rh i ≠ 0 := abs_pos.mp hrh
    simp only [if_neg h0]
    rw [show r i / rh i - 1 = -(rh i - r i) / rh i by field_simp; ring, abs_div, abs_neg,
      div_le_iff₀ hrh]
    nlinarith [hr i, mul_nonneg hv hrpos.le]
  · have : rh i = 0 := by
      have := hr i
      simp only [h0, abs_zero, mul_zero, sub_zero] at this
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    simp [h0, this]
  · have hlow : (1 - v) * |r i| ≤ |rh i| := by
      have := abs_sub_abs_le_abs_sub (r i) (rh i)
      rw [abs_sub_comm] at this
      linarith [hr i]
    have hrpos : 0 < |r i| := abs_pos.mpr h0
    have hrh : 0 < |rh i| := lt_of_lt_of_le (by nlinarith) hlow
    have hrh0 : rh i ≠ 0 := abs_pos.mp hrh
    simp only [if_neg h0]
    field_simp

/-- The size of the perturbation of the solve. -/
private theorem solve_numeric {N u v γ F2 Λ e h p : ℝ} (hN : 2 ≤ N) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hΛ : 0 ≤ Λ) (hγ0 : 0 ≤ γ) (hγN : γ ≤ 8 / 7 * N * u) (hγ7 : γ ≤ 1 / 7) (hF0 : 0 ≤ F2)
    (hF : F2 ≤ 5 / 4 * (N - 1) * Λ) (hsm : 24 * (N ^ 2 * (u + v)) ≤ 1)
    (he : e ≤ 2 * N ^ 2 * (u + v) * Λ) (hh : h ≤ (2 * γ + γ ^ 2) * F2) (hh0 : 0 ≤ h)
    (hp : p ≤ Λ + e + h) :
    e + h + (N - 1) * (2 * v) * p ≤ 6 * (N ^ 2 * (u + v)) * Λ := by
  have hN0 : 0 ≤ N := by linarith
  have hc0 : 0 ≤ N ^ 2 * (u + v) := by positivity
  have h1 : (2 * γ + γ ^ 2) * F2 ≤ 15 / 7 * γ * F2 := by
    have : γ ^ 2 ≤ 1 / 7 * γ := by nlinarith
    exact mul_le_mul_of_nonneg_right (by linarith) hF0
  have h2 : γ * F2 ≤ 8 / 7 * N * u * (5 / 4 * (N - 1) * Λ) :=
    mul_le_mul hγN hF hF0 (by positivity)
  have h3 : N * u * ((N - 1) * Λ) ≤ N ^ 2 * u * Λ := by
    nlinarith [mul_nonneg (mul_nonneg hN0 hu) hΛ]
  have hhb : h ≤ 7 / 2 * (N ^ 2 * u * Λ) := by nlinarith
  have hu2 : N ^ 2 * u * Λ ≤ N ^ 2 * (u + v) * Λ := by
    have : N ^ 2 * u ≤ N ^ 2 * (u + v) := by nlinarith [mul_nonneg (sq_nonneg N) hv]
    exact mul_le_mul_of_nonneg_right this hΛ
  have hcΛ : N ^ 2 * (u + v) * Λ ≤ 1 / 24 * Λ := mul_le_mul_of_nonneg_right (by linarith) hΛ
  have hpb : p ≤ 5 / 4 * Λ := by nlinarith
  have hvp : (N - 1) * (2 * v) * p ≤ (N - 1) * (2 * v) * (5 / 4 * Λ) :=
    mul_le_mul_of_nonneg_left hpb (mul_nonneg (by linarith) (by positivity))
  have hv2 : (N - 1) * v * Λ ≤ N ^ 2 * v * Λ := by
    have : (N - 1) * v ≤ N ^ 2 * v := mul_le_mul_of_nonneg_right (by nlinarith) hv
    exact mul_le_mul_of_nonneg_right this hΛ
  have hsplit : N ^ 2 * (u + v) * Λ = N ^ 2 * u * Λ + N ^ 2 * v * Λ := by ring
  have hu0 : 0 ≤ N ^ 2 * u * Λ := by positivity
  have hv0 : 0 ≤ N ^ 2 * v * Λ := by positivity
  nlinarith

/-- The computed solve is an exact solve with a nearby matrix. -/
private theorem exists_add_mulVec_eq_of_isCholTrace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {a L : ℕ → ℕ → ℝ} {u v : ℝ} (h : IsCholTrace u a L n) (hA : A.PosDef) (hu : 0 ≤ u)
    (hv : 0 ≤ v) (ha : ∀ i j : Fin n, j ≤ i → |a i j - A i j| ≤ v * |A i j|) (hn : 0 < n)
    (hsmall4 : 4 * ((n : ℝ) + 1) ^ 2 * (u + v) * pseudoConditionNumber A ≤ 1)
    (hc24 : 24 * (((n : ℝ) + 1) ^ 2 * (u + v)) ≤ 1)
    (hE : specNorm (A - lowerOf L n * (lowerOf L n)ᵀ) ≤
      2 * ((n : ℝ) + 1) ^ 2 * (u + v) * specNorm A)
    {r : Fin n → ℝ} {rh y d : ℕ → ℝ} (hr : ∀ i : Fin n, |rh i - r i| ≤ v * |r i|)
    (hy : IsSubstTrace (fun _ => RelErr u) L rh n y) (hd : IsBackSubstTrace u L y n d) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, specNorm E ≤ 6 * (((n : ℝ) + 1) ^ 2 * (u + v)) * specNorm A ∧
      (A + E) *ᵥ (fun i : Fin n => d i) = r := by
  obtain ⟨hu1, hγN, hγ7, -, hv16, -, -⟩ := chol_constants hn hA hu hv hsmall4
  have hgood := h.forall_isGoodPivot hA hu hv ha hsmall4
  have hdiag : ∀ i < n, L i i ≠ 0 := fun i hi => (hgood i hi).1.ne'
  obtain ⟨D₁, hD₁, hP⟩ := exists_lower_mulVec_eq hy hdiag hu hu1
  obtain ⟨D₂, hD₂, hQ⟩ := exists_upper_mulVec_eq hd hdiag hu hu1
  obtain ⟨w, hw, hwr⟩ := exists_scaling hv hv16 hr
  set T := lowerOf L n with hT
  set PQ := (T + D₁) * (Tᵀ + D₂) with hPQ
  have hγ0' := roundingFactor_nonneg (n := n) hu hu1
  have hγle : roundingFactor n u ≤ roundingFactor (n + 1) u :=
    roundingFactor_le_roundingFactor hu hu1 (by omega)
  have hH := frobNorm_add_mul_add_sub_le hγ0' hD₁ hD₂
  have hF := (h.frobNorm_bounds hA hu hu1 hv ha hgood hv16 hγ7).1
  have hW : specNorm (Matrix.diagonal w - 1) ≤ n * (2 * v) := by
    refine (specNorm_le_frobNorm _).trans ?_
    have := frobNorm_le_card_mul_of_forall_abs_le (M := Matrix.diagonal w - 1)
      (by positivity : 0 ≤ 2 * v) fun i k => by
        by_cases hik : i = k
        · subst hik
          simpa using hw i
        · simpa [Matrix.diagonal_apply_ne _ hik, Matrix.one_apply_ne hik] using by positivity
    simpa using this
  refine ⟨A⁻¹ * 0 + (Matrix.diagonal w * PQ - A), ?_, ?_⟩
  · have hdecomp : A⁻¹ * 0 + (Matrix.diagonal w * PQ - A) =
        -(A - T * Tᵀ) + (PQ - T * Tᵀ) + (Matrix.diagonal w - 1) * PQ := by
      simp only [Matrix.mul_zero, zero_add, Matrix.sub_mul, Matrix.one_mul]
      abel
    have hh := specNorm_le_frobNorm (PQ - T * Tᵀ)
    have hPQn : specNorm PQ ≤ specNorm A + specNorm (A - T * Tᵀ) + specNorm (PQ - T * Tᵀ) := by
      have heq : PQ = A - (A - T * Tᵀ) + (PQ - T * Tᵀ) := by abel
      calc specNorm PQ = specNorm (A - (A - T * Tᵀ) + (PQ - T * Tᵀ)) := by rw [← heq]
        _ ≤ specNorm (A - (A - T * Tᵀ)) + specNorm (PQ - T * Tᵀ) := specNorm_add_le _ _
        _ ≤ _ := add_le_add_left (specNorm_sub_le _ _) _
    have hmono : (2 * roundingFactor n u + roundingFactor n u ^ 2) * frobNorm T ^ 2 ≤
        (2 * roundingFactor (n + 1) u + roundingFactor (n + 1) u ^ 2) * frobNorm T ^ 2 := by
      gcongr
    have hN : (2 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hnum := solve_numeric hN hu hv (specNorm_nonneg A)
      (roundingFactor_nonneg hu hu1) hγN hγ7 (sq_nonneg (frobNorm T))
      (by simpa using hF) hc24 hE (hh.trans (hH.trans hmono)) (specNorm_nonneg _) hPQn
    rw [hdecomp]
    have hprod := (specNorm_mul_le (Matrix.diagonal w - 1) PQ).trans
      (mul_le_mul_of_nonneg_right hW (specNorm_nonneg PQ))
    have htri := (specNorm_add_le (-(A - T * Tᵀ) + (PQ - T * Tᵀ))
      ((Matrix.diagonal w - 1) * PQ)).trans (add_le_add_left
        ((specNorm_add_le (-(A - T * Tᵀ)) (PQ - T * Tᵀ)).trans
          (add_le_add_left (specNorm_neg _).le _)) _)
    have hn' : (n : ℝ) = (n : ℝ) + 1 - 1 := by ring
    rw [← hn'] at hnum
    linarith
  · have hcoe : (A + (A⁻¹ * 0 + (Matrix.diagonal w * PQ - A))) = Matrix.diagonal w * PQ := by
      simp
    rw [hcoe, ← Matrix.mulVec_mulVec, hPQ, ← Matrix.mulVec_mulVec, hQ, hP]
    funext i
    simpa [Matrix.mulVec_diagonal] using hwr i

/-! ### The rounded residual -/

/-- One row of the rounded residual. -/
private theorem abs_residual_row_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b x rh : Fin n → ℝ}
    {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) {i : Fin n}
    (h : ∃ s : ℕ → ℝ, IsSubstRowTrace (fun _ => RelErr u)
      (fun i j => if hi : i < n then if hj : j < n then A ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0)
      (fun i => if hi : i < n then b ⟨i, hi⟩ else 0)
      (fun j => if hj : j < n then x ⟨j, hj⟩ else 0) i n s ∧ s n = rh i) :
    |(b - A *ᵥ x - rh) i| ≤ roundingFactor (n + 1) u *
      (|b i| + (A.map abs *ᵥ fun j => |x j|) i) := by
  obtain ⟨s, ⟨hs0, hstep⟩, hsn⟩ := h
  set c : ℕ → ℝ := fun j => (if hi : (i : ℕ) < n then if hj : j < n then
    A ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0) * (if hj : j < n then x ⟨j, hj⟩ else 0) with hc
  obtain ⟨α, η, hα, hη, hs⟩ :=
    exists_eq_mul_one_add_sub_sum_of_relErr (c := c) (s := s) hu n hstep
  have hγ0 := roundingFactor_nonneg (n := n + 1) hu hu1
  have hαb : |α| ≤ roundingFactor (n + 1) u := (hα.mono hu (by omega)).abs_le hu1
  have hηb : ∀ k < n, |η k| ≤ roundingFactor (n + 1) u := fun k hk => (hη k hk).abs_le hu1
  have hb0 : s 0 = b i := by simpa [i.isLt] using hs0
  have hcF : ∀ k : Fin n, c k = A i k * x k := fun k => by simp [hc, i.isLt, k.isLt]
  have hAx : (A *ᵥ x) i = ∑ k ∈ range n, c k := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [Matrix.mulVec, dotProduct]
    exact sum_congr rfl fun k _ => (hcF k).symm
  have hAabs : (A.map abs *ᵥ fun j => |x j|) i = ∑ k ∈ range n, |c k| := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => |c k|)]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    exact sum_congr rfl fun k _ => by rw [hcF k, abs_mul]
  have heq : (b - A *ᵥ x - rh) i = -(b i * α) + ∑ k ∈ range n, c k * η k := by
    simp only [Pi.sub_apply]
    rw [hAx, ← hsn, hs, hb0]
    simp only [mul_add, mul_one, sum_add_distrib]
    ring
  have hsum : |∑ k ∈ range n, c k * η k| ≤
      roundingFactor (n + 1) u * ∑ k ∈ range n, |c k| := by
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hηb k (mem_range.mp hk)) (abs_nonneg _)
  have hfirst : |-(b i * α)| ≤ roundingFactor (n + 1) u * |b i| := by
    rw [abs_neg, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hαb (abs_nonneg _)
  rw [heq, hAabs, mul_add]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsum)

/-- **Cholesky in the standard model does not break down and is backward stable.** Let
$\mathbf{A}$ be positive definite of order $n$, read as $a_{ij}$, $j \le i$, with relative error
$v \ge 0$, and let $l$ be a trace of left-looking Cholesky on $a$ at unit roundoff $u \ge 0$, with
$4(n + 1)^2(u + v)\kappa(\mathbf{A}) \le 1$. Then every computed pivot is positive and
$$\|\mathbf{A} - \mathbf{L}\mathbf{L}^{\mathsf{T}}\|_2 \le 2(n + 1)^2(u + v)\|\mathbf{A}\|_2 .$$
[Higham2002, Theorem 10.3, Theorem 10.7]; normwise, with these constants.
Result: cholesky-backward-error -/
theorem IsCholTrace.pos_and_specNorm_sub_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {a L : ℕ → ℕ → ℝ}
    {u v : ℝ} (h : IsCholTrace u a L n) (hA : A.PosDef) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ha : ∀ i j : Fin n, j ≤ i → |a i j - A i j| ≤ v * |A i j|)
    (hsmall : 4 * ((n : ℝ) + 1) ^ 2 * (u + v) * pseudoConditionNumber A ≤ 1) :
    (∀ j < n, 0 < L j j) ∧
      specNorm (A - lowerOf L n * (lowerOf L n)ᵀ) ≤
        2 * ((n : ℝ) + 1) ^ 2 * (u + v) * specNorm A := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), ?_⟩
    have h0 : A - lowerOf L 0 * (lowerOf L 0)ᵀ = 0 := by
      ext i
      exact i.elim0
    rw [h0, specNorm_zero]
    have := specNorm_nonneg A
    positivity
  obtain ⟨hu1, hγN, hγ7, -, hv16, -, -⟩ := chol_constants hn hA hu hv hsmall
  have hgood := h.forall_isGoodPivot hA hu hv ha hsmall
  refine ⟨fun j hj => (hgood j hj).1, ?_⟩
  obtain ⟨hF, hE⟩ := h.frobNorm_bounds hA hu hu1 hv ha hgood hv16 hγ7
  have hγ0 := roundingFactor_nonneg (n := n + 1) hu hu1
  have hΛ := specNorm_nonneg A
  refine (specNorm_le_frobNorm _).trans (hE.trans ?_)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : roundingFactor (n + 1) u * frobNorm (lowerOf L n) ^ 2 ≤
      8 / 7 * ((n : ℝ) + 1) * u * (5 / 4 * n * specNorm A) :=
    mul_le_mul hγN hF (sq_nonneg _) (by positivity)
  have h2 : (n : ℝ) * (u * specNorm A) ≤ ((n : ℝ) + 1) * (u * specNorm A) := by
    nlinarith [mul_nonneg hu hΛ]
  have h3 : (n : ℝ) * (v * specNorm A) ≤ ((n : ℝ) + 1) ^ 2 * (v * specNorm A) := by
    have : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (mul_nonneg hv hΛ)
  have h4 : ((n : ℝ) + 1) * ((n : ℝ) * (u * specNorm A)) ≤
      ((n : ℝ) + 1) * (((n : ℝ) + 1) * (u * specNorm A)) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h5 : 0 ≤ ((n : ℝ) + 1) ^ 2 * (u * specNorm A) := by positivity
  have h6 : 0 ≤ ((n : ℝ) + 1) ^ 2 * (v * specNorm A) := by positivity
  nlinarith

/-- **The solve with computed Cholesky factors has a small relative error.** Let $\mathbf{A}$ be
positive definite of order $n$, with a Cholesky trace as in
`NLAlib.Computation.IsCholTrace.pos_and_specNorm_sub_le` and
$24(n + 1)^2(u + v)\kappa(\mathbf{A}) \le 1$. Let $\hat{\mathbf{r}}$ be $\mathbf{r}$ with relative
error $v$ in each entry, $\mathbf{y}$ a forward substitution trace with $\mathbf{L}$ from
$\hat{\mathbf{r}}$ and $\mathbf{d}$ a back substitution trace with $\mathbf{L}^{\mathsf{T}}$ from
$\mathbf{y}$, at unit roundoff $u$. Then
$$\|\mathbf{A}^{-1}\mathbf{r} - \mathbf{d}\| \le 24(n + 1)^2(u + v)\kappa(\mathbf{A})
\|\mathbf{A}^{-1}\mathbf{r}\| .$$
[CarsonHigham2018, (2.3)]; the assumption there on the solver, proved here for Cholesky. -/
theorem norm_inv_mulVec_sub_le_of_isCholTrace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {a L : ℕ → ℕ → ℝ} {u v : ℝ} (h : IsCholTrace u a L n) (hA : A.PosDef) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ha : ∀ i j : Fin n, j ≤ i → |a i j - A i j| ≤ v * |A i j|)
    (hsmall : 24 * ((n : ℝ) + 1) ^ 2 * (u + v) * pseudoConditionNumber A ≤ 1)
    {r : Fin n → ℝ} {rh y d : ℕ → ℝ} (hr : ∀ i : Fin n, |rh i - r i| ≤ v * |r i|)
    (hy : IsSubstTrace (fun _ => RelErr u) L rh n y) (hd : IsBackSubstTrace u L y n d) :
    ‖WithLp.toLp 2 (A⁻¹ *ᵥ r - fun i : Fin n => d i)‖ ≤
      24 * ((n : ℝ) + 1) ^ 2 * (u + v) * pseudoConditionNumber A * ‖WithLp.toLp 2 (A⁻¹ *ᵥ r)‖ := by
  have hκ0 : 0 ≤ pseudoConditionNumber A := by
    rw [pseudoConditionNumber_of_isUnit hA.isUnit]
    exact mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (A⁻¹ *ᵥ r - fun i : Fin 0 => d i) = 0 := by
      funext i
      exact i.elim0
    rw [h0, WithLp.toLp_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hκ0) (norm_nonneg _)
  have hκ1 : 1 ≤ pseudoConditionNumber A := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact one_le_pseudoConditionNumber hA.isUnit.ne_zero
  set c := ((n : ℝ) + 1) ^ 2 * (u + v) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcκ : 0 ≤ c * pseudoConditionNumber A := mul_nonneg hc0 hκ0
  have hsmall' : 24 * (c * pseudoConditionNumber A) ≤ 1 := by
    simpa only [hc, mul_assoc] using hsmall
  have hsmall4 : 4 * ((n : ℝ) + 1) ^ 2 * (u + v) * pseudoConditionNumber A ≤ 1 := by
    have : 4 * ((n : ℝ) + 1) ^ 2 * (u + v) * pseudoConditionNumber A =
        4 * (c * pseudoConditionNumber A) := by rw [hc]; ring
    rw [this]
    linarith
  have hc24 : 24 * c ≤ 1 := by nlinarith
  have hE := (h.pos_and_specNorm_sub_le hA hu hv ha hsmall4).2
  obtain ⟨E, hEn, hEd⟩ := exists_add_mulVec_eq_of_isCholTrace h hA hu hv ha hn hsmall4 hc24 hE
    hr hy hd
  have hbound : specNorm (A⁻¹ * E) ≤ 12 * (c * pseudoConditionNumber A) := by
    have h1 := specNorm_mul_le A⁻¹ E
    have h2 := mul_le_mul_of_nonneg_left hEn (specNorm_nonneg A⁻¹)
    have h3 : specNorm A⁻¹ * (6 * c * specNorm A) = 6 * (c * pseudoConditionNumber A) := by
      rw [pseudoConditionNumber_of_isUnit hA.isUnit]
      ring
    linarith
  have hω : 12 * (c * pseudoConditionNumber A) ≤ 1 / 2 := by linarith
  have hsol := norm_inv_mulVec_sub_le_of_add_mulVec_eq hA.isUnit hbound (by linarith) hEd
  refine hsol.trans ?_
  have hratio : 12 * (c * pseudoConditionNumber A) / (1 - 12 * (c * pseudoConditionNumber A)) ≤
      24 * ((n : ℝ) + 1) ^ 2 * (u + v) * pseudoConditionNumber A := by
    rw [div_le_iff₀ (by linarith)]
    have : 24 * ((n : ℝ) + 1) ^ 2 * (u + v) * pseudoConditionNumber A =
        24 * (c * pseudoConditionNumber A) := by rw [hc]; ring
    rw [this]
    nlinarith
  exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)

/-- **The rounded residual.** If $s$ runs through $s_0 = b_i$ and $s_{j+1}$, $j < n$, a rounded
$s_j - q_j$ for a rounded $q_j$ of $a_{ij}x_j$ at unit roundoff $u$ with $(n + 1)u < 1$, in every
row $i$, then the final values $\hat{\mathbf{r}}$ satisfy
$$\|\mathbf{b} - \mathbf{A}\mathbf{x} - \hat{\mathbf{r}}\| \le (n + 1)\,\gamma_{n+1}
\bigl(\|\mathbf{b}\| + \|\mathbf{A}\|_2\|\mathbf{x}\|\bigr),\qquad
\gamma_{n+1} = (1 - u)^{-(n+1)} - 1.$$
[Higham2002, §12.1]; normwise. -/
theorem norm_sub_mulVec_sub_le_of_isSubstRowTrace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {b x rh : Fin n → ℝ} {u : ℝ} (hu : 0 ≤ u) (hu1 : ((n : ℝ) + 1) * u < 1)
    (h : ∀ i : Fin n, ∃ s : ℕ → ℝ, IsSubstRowTrace (fun _ => RelErr u)
      (fun i j => if hi : i < n then if hj : j < n then A ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0)
      (fun i => if hi : i < n then b ⟨i, hi⟩ else 0)
      (fun j => if hj : j < n then x ⟨j, hj⟩ else 0) i n s ∧ s n = rh i) :
    ‖WithLp.toLp 2 (b - A *ᵥ x - rh)‖ ≤ ((n : ℝ) + 1) * roundingFactor (n + 1) u *
      (‖WithLp.toLp 2 b‖ + specNorm A * ‖WithLp.toLp 2 x‖) := by
  have hu1 : u < 1 := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hγ0 := roundingFactor_nonneg (n := n + 1) hu hu1
  set e : Fin n → ℝ := b - A *ᵥ x - rh with he
  have hrow : ∀ i, |e i| ≤ roundingFactor (n + 1) u *
      (|b i| + (A.map abs *ᵥ fun j => |x j|) i) := fun i => abs_residual_row_le hu hu1 (h i)
  have hdom := EuclideanSpace.norm_toLp_le_norm_toLp (x := e)
    (y := roundingFactor (n + 1) u •
      ((fun i => |b i|) + A.map abs *ᵥ fun j => |x j|)) fun i => by
      have hnn : 0 ≤ (A.map abs *ᵥ fun j => |x j|) i := by
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
        exact sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      rw [abs_of_nonneg (mul_nonneg hγ0 (add_nonneg (abs_nonneg _) hnn))]
      exact hrow i
  have hb : ‖WithLp.toLp 2 (fun i => |b i|)‖ = ‖WithLp.toLp 2 b‖ := by
    simp [EuclideanSpace.norm_eq]
  have hAx := norm_toLp_map_abs_mulVec_abs_le A x
  rw [Fintype.card_fin] at hAx
  have hsqrt : √(n : ℝ) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hP : 0 ≤ specNorm A * ‖WithLp.toLp 2 x‖ :=
    mul_nonneg (specNorm_nonneg A) (norm_nonneg _)
  have hAx' : ‖WithLp.toLp 2 (A.map abs *ᵥ fun j => |x j|)‖ ≤
      ((n : ℝ) + 1) * (specNorm A * ‖WithLp.toLp 2 x‖) := by
    refine hAx.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hsqrt hP
  refine hdom.trans ?_
  rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hγ0]
  have hbn := norm_nonneg (WithLp.toLp 2 b)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsumn : ‖WithLp.toLp 2 ((fun i => |b i|) + A.map abs *ᵥ fun j => |x j|)‖ ≤
      ((n : ℝ) + 1) * (‖WithLp.toLp 2 b‖ + specNorm A * ‖WithLp.toLp 2 x‖) := by
    rw [WithLp.toLp_add]
    refine (norm_add_le _ _).trans ?_
    rw [hb]
    nlinarith
  calc _ ≤ roundingFactor (n + 1) u *
        (((n : ℝ) + 1) * (‖WithLp.toLp 2 b‖ + specNorm A * ‖WithLp.toLp 2 x‖)) :=
        mul_le_mul_of_nonneg_left hsumn hγ0
    _ = _ := by ring

end NLAlib.Computation
