/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.LowRank.FiniteSpectrum
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Exp

/-!
# Minimax lower bounds for low-rank approximation

Frobenius minimax lower bounds for any fixed natural batch count. A level spectrum has a head
$L$ on $k$ and $r+1$ tail levels $\nu_j \in [0,\tau]$, and an extrapolation constant $C$
controls degree-$r$ polynomials at the head by their tail values. Gaussian overlap estimates
and the general Krylov coupling give a distributional failure bound and a randomized
worst-case hard input for every such spectrum. Two explicit query lower bounds follow: the
equispaced spectrum (head $r+2$, levels $1,\ldots,r+1$, $C = 4^{r+1}$) and the Chebyshev
spectrum (head $1+1/(8(r+1)^2)$, Chebyshev levels in $[1/2,1]$, $C = 4$).

## Main definitions

* `NLAlib.equispacedQueryFactor`, `NLAlib.equispacedAccuracyBound`: the equispaced query
  denominator and admissible squared-error accuracy.
* `NLAlib.chebyshevQueryFactor`, `NLAlib.chebyshevAccuracyBound`: the Chebyshev ones.

Their explicit values are the one-sided comparisons `NLAlib.equispacedQueryFactor_le`,
`NLAlib.le_equispacedAccuracyBound`, `NLAlib.chebyshevQueryFactor_le` and
`NLAlib.le_chebyshevAccuracyBound`, with `NLAlib.equispacedQueryFactor_pos` and
`NLAlib.chebyshevQueryFactor_pos`.

For natural $r$, the equispaced query factor is <!-- value equispacedQueryFactor r -->
$256\cdot4^{r+1}(r+1)(r+2)$, and the accuracy cutoff is
set to <!-- value equispacedAccuracyBound r -->
$1/(512\cdot4^{r+1}(r+1)(r+2)^2)$. The Chebyshev query factor is
$r \mapsto$ <!-- value chebyshevQueryFactor r --> $12544(r+1)^3$, with the cutoff
$r \mapsto$ <!-- value chebyshevAccuracyBound r --> $1/(25088(r+1)^3(r+2))$.

## Main results

* In `QueryAlgorithm.IsPassStructured`,
  `measureReal_frobNorm_sub_mul_sq_lt_le_of_pass_lt_of_hasLaw_haarFrame` bounds success on Haar
  rotations of a level spectrum.
* `NLAlib.exists_le_measureReal_frobNorm_sub_mul_sq_ge_of_pass_lt`: a randomized worst-case bound.
* `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt`: the equispaced
  fixed-batch query lower bound.
* `div_chebyshevQueryFactor_mul_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt`:
  the Chebyshev fixed-batch query lower bound, $q = \Omega(k/(\varepsilon(r+1)^3))$.
* The same bound with natural-number sizes:
`natCast_div_chebyshevQueryFactor_mul_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt`
-/

@[expose] public section

namespace NLAlib

/-- **Query factor for fixed-batch Frobenius approximation**: for natural $r$, the
query lower bound uses <!-- value equispacedQueryFactor r -->
$$256\cdot4^{r+1}(r+1)(r+2) \,.$$
Its reciprocal is a conservative fixed-$r$ coefficient of $k/\varepsilon$. -/
noncomputable irreducible_def equispacedQueryFactor (r : ℕ) : ℝ :=
  256 * 4 ^ (r + 1) * ((r : ℝ) + 1) * (r + 2)

/-- **Accuracy cutoff for fixed-batch Frobenius approximation**: natural $r$ permits squared
relative-error accuracy at most <!-- value equispacedAccuracyBound r -->
$$1/(512\cdot4^{r+1}(r+1)(r+2)^2) \,.$$
This suffices for the floor and Gaussian dimension conditions for every positive target rank. -/
noncomputable irreducible_def equispacedAccuracyBound (r : ℕ) : ℝ :=
  1 / (512 * 4 ^ (r + 1) * ((r : ℝ) + 1) * (r + 2) ^ 2)

/-- **Query factor for the Chebyshev fixed-batch bounds**: for natural $r$, the query lower
bound uses <!-- value chebyshevQueryFactor r -->
$$12544(r+1)^3 \,.$$
It is $16\cdot4\cdot196$ times $(r+1)^3$: the tail multiplicity $k/(16\varepsilon(r+1)^3)$, a
quarter of it for the queries, and the Gaussian width $14^2$. -/
noncomputable irreducible_def chebyshevQueryFactor (r : ℕ) : ℝ := 12544 * ((r : ℝ) + 1) ^ 3

/-- **Accuracy cutoff for the Chebyshev fixed-batch bounds**: natural $r$ permits accuracy at
most <!-- value chebyshevAccuracyBound r -->
$$1/(25088(r+1)^3(r+2)) \,.$$
This makes the tail multiplicity large enough for the Gaussian width and the exceptional
probability, for every positive target rank. -/
noncomputable irreducible_def chebyshevAccuracyBound (r : ℕ) : ℝ :=
  1 / (25088 * ((r : ℝ) + 1) ^ 3 * (r + 2))

/-- The equispaced query factor is positive: `equispacedQueryFactor r`, whose value
is <!-- value equispacedQueryFactor r -->$256\cdot4^{r+1}(r+1)(r+2)$, is $> 0$ for every natural
$r$. -/
theorem equispacedQueryFactor_pos (r : ℕ) : 0 < equispacedQueryFactor r := by
  rw [equispacedQueryFactor_def]
  positivity

/-- An explicit upper bound, $256\cdot4^{r+1}(r+1)(r+2)$, on `equispacedQueryFactor r`, whose
value is <!-- value equispacedQueryFactor r -->$256\cdot4^{r+1}(r+1)(r+2)$. A smaller factor is a
better query lower bound. -/
theorem equispacedQueryFactor_le (r : ℕ) :
    equispacedQueryFactor r ≤ 256 * 4 ^ (r + 1) * ((r : ℝ) + 1) * (r + 2) := by
  rw [equispacedQueryFactor_def]

/-- An explicit lower bound, $1/(512\cdot4^{r+1}(r+1)(r+2)^2)$, on `equispacedAccuracyBound r`,
whose value is <!-- value equispacedAccuracyBound r -->$1/(512\cdot4^{r+1}(r+1)(r+2)^2)$. A
larger cutoff admits more accuracies $\varepsilon$. -/
theorem le_equispacedAccuracyBound (r : ℕ) :
    1 / (512 * 4 ^ (r + 1) * ((r : ℝ) + 1) * (r + 2) ^ 2) ≤ equispacedAccuracyBound r := by
  rw [equispacedAccuracyBound_def]

/-- The Chebyshev query factor is positive: `chebyshevQueryFactor r`, whose value
is <!-- value chebyshevQueryFactor r -->$12544(r+1)^3$, is $> 0$ for every natural $r$. -/
theorem chebyshevQueryFactor_pos (r : ℕ) : 0 < chebyshevQueryFactor r := by
  rw [chebyshevQueryFactor_def]
  positivity

/-- An explicit upper bound, $12544(r+1)^3$, on `chebyshevQueryFactor r`, whose value
is <!-- value chebyshevQueryFactor r -->$12544(r+1)^3$. A smaller factor is a better query lower
bound. -/
theorem chebyshevQueryFactor_le (r : ℕ) :
    chebyshevQueryFactor r ≤ 12544 * ((r : ℝ) + 1) ^ 3 := by
  rw [chebyshevQueryFactor_def]

/-- An explicit lower bound, $1/(25088(r+1)^3(r+2))$, on `chebyshevAccuracyBound r`, whose value
is <!-- value chebyshevAccuracyBound r -->$1/(25088(r+1)^3(r+2))$. A larger cutoff admits more
accuracies $\varepsilon$. -/
theorem le_chebyshevAccuracyBound (r : ℕ) :
    1 / (25088 * ((r : ℝ) + 1) ^ 3 * (r + 2)) ≤ chebyshevAccuracyBound r := by
  rw [chebyshevAccuracyBound_def]

end NLAlib

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]

section GaussianCapture

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Scalar comparison used after the interpolation estimate and Gaussian norm bounds. -/
private theorem false_of_interpolation_lt {C γ t s N sumH : ℝ} (hC : 0 ≤ C) (hγ : 2 < γ)
    (ht : 0 < t) (hs : (γ - 2) * t ≤ s) (hN : 0 ≤ N)
    (key : s ^ 2 * sumH ≤ C * (3 * t) ^ 2 * N)
    (hlt : 9 * C / (γ - 2) ^ 2 * N < sumH) : False := by
  have hγ2 : 0 < γ - 2 := by linarith
  have hsp : 0 < s := lt_of_lt_of_le (mul_pos hγ2 ht) hs
  have h1 := mul_lt_mul_of_pos_left hlt (pow_pos hsp 2)
  have hs2 := pow_le_pow_left₀ (mul_nonneg hγ2.le ht.le) hs 2
  have h3 : t ^ 2 ≤ s ^ 2 / (γ - 2) ^ 2 := by
    rw [le_div_iff₀ (pow_pos hγ2 2)]; rw [mul_pow] at hs2; linarith [hs2]
  have h2 : 9 * C * t ^ 2 * N ≤ s ^ 2 * (9 * C / (γ - 2) ^ 2 * N) := by
    calc 9 * C * t ^ 2 * N = 9 * C * N * t ^ 2 := by ring
      _ ≤ 9 * C * N * (s ^ 2 / (γ - 2) ^ 2) := by gcongr
      _ = s ^ 2 * (9 * C / (γ - 2) ^ 2 * N) := by ring
  have key' : C * (3 * t) ^ 2 * N = 9 * C * t ^ 2 * N := by ring
  linarith [h1, key, h2, key']

omit [DecidableEq k] [DecidableEq m] in
/-- Lower Gram bound for an arbitrary tail block. -/
private theorem measureReal_not_gram_tail_le_of_pass_lt {r : ℕ}
    {b : Type*} [Fintype b] [DecidableEq b]
    {G : Ω → Matrix (k ⊕ (Fin (r + 1) × m)) b ℝ}
    (hG : HasLaw G (gaussianMatrix (k ⊕ (Fin (r + 1) × m)) b) μ)
    (j : Fin (r + 1)) {t : ℝ} (ht : 0 ≤ t)
    (htn : t ≤ √(Fintype.card m : ℝ) - √(Fintype.card b : ℝ)) :
    μ.real {ω | ¬ (√(Fintype.card m : ℝ) - √(Fintype.card b : ℝ) - t) ^ 2 •
      (1 : Matrix b b ℝ) ≤ ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        (G ω).submatrix (fun i : m => Sum.inr (j, i)) id} ≤ Real.exp (-t ^ 2 / 2) :=
  measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix
    (hasLaw_submatrix_of_hasLaw_gaussianMatrix hG (fun i i' h => by simpa using h)
      Function.injective_id) ht htn

/-- Gaussian head-capture estimate with a free deviation parameter. -/
private theorem
measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_pass_lt_of_hasLaw_gaussianMatrix
    {r : ℕ} {L C : ℝ} {ν : Fin (r + 1) → ℝ} (hI : IsExtrapolationControl L ν C)
    {b : Type*} [Fintype b] {G : Ω → Matrix (k ⊕ (Fin (r + 1) × m)) b ℝ}
    (hG : HasLaw G (gaussianMatrix (k ⊕ (Fin (r + 1) × m)) b) μ)
    {γ : ℝ} (hγ : 2 < γ)
    (hkb : Fintype.card k ≤ Fintype.card b) (hbm : γ ^ 2 * Fintype.card b ≤ Fintype.card m) :
    μ.real {ω | ∃ z ∈ blockKrylovSpace
      (Matrix.diagonal (levelSpectrum k m L ν)) (G ω) (r + 1),
        9 * C / (γ - 2) ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2} ≤
      (r + 2) * Real.exp (-(Fintype.card m / (2 * γ ^ 2))) := by
  classical
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hC : 0 ≤ C := hI.pos.le
  have hγ0 : 0 < γ := by linarith
  set a : ℝ := √(Fintype.card m : ℝ) with ha_def
  set c : ℝ := √(Fintype.card b : ℝ) with hc_def
  set d : ℝ := √(Fintype.card k : ℝ) with hd_def
  set t : ℝ := a / γ with ht_def
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = Fintype.card m := Real.sq_sqrt (Nat.cast_nonneg _)
  have hc2 : c ^ 2 = Fintype.card b := Real.sq_sqrt (Nat.cast_nonneg _)
  have ht0 : 0 ≤ t := div_nonneg ha0 hγ0.le
  have hat : a = γ * t := by rw [ht_def]; field_simp
  have hct : c ≤ t := by
    have h1 : (c * γ) ^ 2 ≤ a ^ 2 := by
      rw [mul_pow, ha2, hc2]; linarith [hbm]
    rw [ht_def, le_div_iff₀ hγ0]
    nlinarith [mul_nonneg hc0 hγ0.le]
  have htn : t ≤ a - c := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ γ - 2) ht0]
  have hdc : d ≤ c := Real.sqrt_le_sqrt (Nat.cast_le.mpr hkb)
  have hexp : Real.exp (-t ^ 2 / 2) = Real.exp (-(Fintype.card m / (2 * γ ^ 2))) := by
    congr 1
    rw [ht_def, div_pow, ha2]
    ring
  -- tail blocks: the lower Gram bound fails with probability at most `exp (-t^2/2)` each
  have hA : μ.real (⋃ j : Fin (r + 1), {ω | ¬ (a - c - t) ^ 2 • (1 : Matrix b b ℝ) ≤
      ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        (G ω).submatrix (fun i : m => Sum.inr (j, i)) id}) ≤ (r + 1) * Real.exp (-t ^ 2 / 2) := by
    refine (measureReal_iUnion_fintype_le _).trans ((Finset.sum_le_sum fun j _ =>
      measureReal_not_gram_tail_le_of_pass_lt hG j ht0 htn).trans ?_)
    simp
  -- head block: the spectral norm is large with probability at most `exp (-t^2/2)`
  have hB : μ.real {ω | d + c + t ≤ specNorm ((G ω).submatrix Sum.inl id)} ≤
      Real.exp (-t ^ 2 / 2) :=
    measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix
      (hasLaw_submatrix_of_hasLaw_gaussianMatrix hG Sum.inl_injective Function.injective_id) ht0
  refine le_trans (measureReal_mono (s₂ := (⋃ j : Fin (r + 1), {ω | ¬ (a - c - t) ^ 2 •
      (1 : Matrix b b ℝ) ≤ ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        (G ω).submatrix (fun i : m => Sum.inr (j, i)) id}) ∪
      {ω | d + c + t ≤ specNorm ((G ω).submatrix Sum.inl id)}) (fun ω hω => ?_))
    ((measureReal_union_le _ _).trans ?_)
  · obtain ⟨z, hz, hlt⟩ := hω
    by_contra hnot
    have hs : ∀ j : Fin (r + 1), (a - c - t) ^ 2 • (1 : Matrix b b ℝ) ≤
        ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
          (G ω).submatrix (fun i : m => Sum.inr (j, i)) id := by
      intro j
      by_contra h
      exact hnot (Or.inl (Set.mem_iUnion.2 ⟨j, h⟩))
    have hS : specNorm ((G ω).submatrix Sum.inl id) ≤ 3 * t := by
      by_contra h
      have hB' : d + c + t ≤ specNorm ((G ω).submatrix Sum.inl id) := by
        linarith [not_le.1 h]
      exact hnot (Or.inr hB')
    have key :=
      mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace_of_isExtrapolationControl hI hs hS hz
    have hsum : 0 < ∑ a : k, z (Sum.inl a) ^ 2 :=
      lt_of_le_of_lt (by positivity) hlt
    have hne : Nonempty k := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hsum
    have hb1 : 1 ≤ Fintype.card b := le_trans (Fintype.card_pos (α := k)) hkb
    have hb1' : (1 : ℝ) ≤ Fintype.card b := by exact_mod_cast hb1
    have hm : (0 : ℝ) < Fintype.card m :=
      lt_of_lt_of_le (pow_pos hγ0 2) ((le_mul_of_one_le_right (sq_nonneg γ) hb1').trans hbm)
    have ha_pos : 0 < a := Real.sqrt_pos.2 hm
    have ht_pos : 0 < t := div_pos ha_pos hγ0
    have hs_lb : (γ - 2) * t ≤ a - c - t := by linarith [hat, hct]
    exact false_of_interpolation_lt hC hγ ht_pos hs_lb (sq_nonneg _) key hlt
  · rw [← hexp]
    linarith [hA, hB]

/-- The numerical Gaussian deviation used in the equispaced fixed-batch theorem. -/
private theorem equispaced_deviation (r : ℕ) :
    2 < 8 * (2 : ℝ) ^ (r + 1) ∧
      (8 * (2 : ℝ) ^ (r + 1)) ^ 2 = equispacedGaussianFactor r ∧
      36 * equispacedInterpolationFactor r ≤ (8 * (2 : ℝ) ^ (r + 1) - 2) ^ 2 := by
  have hp : (1 : ℝ) ≤ 2 ^ (r + 1) := one_le_pow₀ (by norm_num)
  have hpow : ((2 : ℝ) ^ (r + 1)) ^ 2 = 4 ^ (r + 1) := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hγ : 2 < 8 * (2 : ℝ) ^ (r + 1) := by linarith
  refine ⟨hγ, ?_, ?_⟩
  · rw [equispacedGaussianFactor_def, mul_pow, hpow]
    norm_num
  · rw [equispacedInterpolationFactor_def, ← hpow]
    nlinarith [sq_nonneg (2 * (2 : ℝ) ^ (r + 1) - 2)]

/-- Under a width condition $\gamma^2\lvert b\rvert \le \lvert m\rvert$ with
$36C \le (\gamma-2)^2$, a Gaussian Krylov space of a level spectrum with extrapolation constant
$C$ rarely captures a quarter of its norm in the head eigenspace. -/
theorem measureReal_exists_mem_blockKrylovSpace_gt_quarter_le_of_hasLaw_gaussianMatrix
    {r : ℕ} {L C : ℝ} {ν : Fin (r + 1) → ℝ} (hI : IsExtrapolationControl L ν C)
    {γ : ℝ} (hγ : 2 < γ) (hγC : 36 * C ≤ (γ - 2) ^ 2) {b : Type*} [Fintype b]
    {G : Ω → Matrix (k ⊕ (Fin (r + 1) × m)) b ℝ}
    (hG : HasLaw G (gaussianMatrix (k ⊕ (Fin (r + 1) × m)) b) μ)
    (hkb : Fintype.card k ≤ Fintype.card b)
    (hbm : γ ^ 2 * Fintype.card b ≤ Fintype.card m) :
    μ.real {ω | ∃ z ∈ blockKrylovSpace
      (Matrix.diagonal (levelSpectrum k m L ν)) (G ω) (r + 1),
      1 / 4 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2} ≤
      (r + 2) * Real.exp (-(Fintype.card m / (2 * γ ^ 2))) := by
  have := hG.isProbabilityMeasure
  have hcoeff : 9 * C / (γ - 2) ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hγ))]
    linarith
  have hbad :=
    measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_pass_lt_of_hasLaw_gaussianMatrix
      hI hG hγ hkb hbm
  refine (measureReal_mono fun ω hω => ?_).trans hbad
  obtain ⟨z, hz, hlt⟩ := hω
  exact ⟨z, hz, (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)).trans_lt hlt⟩

end GaussianCapture

/-- Orthogonal change of coordinates and small head capture force excess Frobenius loss. -/
private theorem le_frobNorm_of_orthonormal_range_of_pass_lt {r : ℕ} {L τ : ℝ}
    {ν : Fin (r + 1) → ℝ} (hν0 : ∀ j, 0 ≤ ν j) (hντ : ∀ j, ν j ≤ τ) (hτL : τ ≤ L)
    {b : Type*} [Fintype b]
    {U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ}
    {W : Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ}
    {M : Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ}
    {G : Matrix (k ⊕ (Fin (r + 1) × m)) b ℝ} (hU : HasOrthonormalCols U)
    (hr : LinearMap.range (Uᴴ * W).mulVecLin ≤
      blockKrylovSpace (Matrix.diagonal (levelSpectrum k m L ν)) G (r + 1))
    (hgood : ∀ z ∈ blockKrylovSpace (Matrix.diagonal (levelSpectrum k m L ν)) G (r + 1),
      ¬ (1 / 4 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2)) :
    Fintype.card m * ∑ j, ν j ^ 2 + (L ^ 2 - τ ^ 2) * Fintype.card k / 2 ≤
      frobNorm (U * Matrix.diagonal (levelSpectrum k m L ν) * Uᴴ - W * M) ^ 2 := by
  classical
  set D := Matrix.diagonal (levelSpectrum k m L ν)
  have heq : U * D * Uᴴ - W * M = U * (D - (Uᴴ * W) * (M * U)) * Uᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc U (Uᴴ * W),
      ← Matrix.mul_assoc U Uᴴ, hU.mul_conjTranspose_self, Matrix.one_mul,
      Matrix.mul_assoc W, Matrix.mul_assoc M, hU.mul_conjTranspose_self,
      Matrix.mul_one, Matrix.mul_assoc]
  rw [heq, hU.conjTranspose.frobNorm_mul_right, hU.frobNorm_mul_left]
  have hle := le_frobNorm_diagonal_levelSpectrum_sub_mul_sq (L := L) hν0 hντ (Uᴴ * W) (M * U)
  have ht : ∑ a : k, ‖WithLp.toLp 2 (rangeProjector (Uᴴ * W) *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2
      ≤ 1 / 4 * Fintype.card k := by
    let P := rangeProjector (Uᴴ * W)
    have hP : IsStarProjection P := isStarProjection_rangeProjector _
    have hsum := hP.sum_head_mass_sq_le (c := 1 / 4) (by norm_num) (fun a => by
      have hz : P *ᵥ Pi.single (Sum.inl a) 1 ∈ LinearMap.range (Uᴴ * W).mulVecLin := by
        rw [← range_rangeProjector]
        exact ⟨_, rfl⟩
      have h1 := hgood _ (hr hz)
      rw [not_lt, EuclideanSpace.norm_toLp_sq_eq_sum_sq] at h1
      simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h1)
    simpa only [EuclideanSpace.norm_toLp_sq_eq_sum_sq, Matrix.mulVec_single_one,
      Matrix.col_apply, P] using hsum
  have hkn : (0 : ℝ) ≤ Fintype.card k := Nat.cast_nonneg _
  have hτ : 0 ≤ τ := (hν0 0).trans (hντ 0)
  have hgap : 0 ≤ L ^ 2 - τ ^ 2 := sub_nonneg.mpr (pow_le_pow_left₀ hτ hτL 2)
  have hnon := mul_nonneg hgap (sub_nonneg.mpr ht)
  dsimp only [D] at *
  nlinarith

/-- A deterministic measurable algorithm using at most $r$ batches cannot attain the optimum
plus $(L^2-\tau^2)\lvert k\rvert/2$ on most Haar rotations of a level spectrum with levels in
$[0,\tau]$, $\tau \le L$, and extrapolation constant $C$. For a deviation $\gamma > 2$ with
$36C \le (\gamma-2)^2$, the width condition is $\gamma^2(q+\lvert k\rvert)\le\lvert m\rvert$, and
the success probability is at most $(r+2)\exp(-\lvert m\rvert/(2\gamma^2))$. -/
theorem
QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_pass_lt_of_hasLaw_haarFrame
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {r q : ℕ} {L τ C γ : ℝ}
    {ν : Fin (r + 1) → ℝ} (hI : IsExtrapolationControl L ν C) (hν0 : ∀ j, 0 ≤ ν j)
    (hντ : ∀ j, ν j ≤ τ) (hτL : τ ≤ L) (hγ : 2 < γ) (hγC : 36 * C ≤ (γ - 2) ^ 2)
    {alg : QueryAlgorithm (k ⊕ (Fin (r + 1) × m) → ℝ)
      ((k ⊕ (Fin (r + 1) × m) → ℝ) × (k ⊕ (Fin (r + 1) × m) → ℝ)) q
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)}
    {pass : ℕ → ℕ} (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < r)
    (halg : alg.IsMeasurable)
    {U : Ω → Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ}
    (hU : HasLaw U (haarFrame (k ⊕ (Fin (r + 1) × m))
      (k ⊕ (Fin (r + 1) × m))) μ)
    (hwidth : γ ^ 2 * (q + Fintype.card k) ≤ Fintype.card m) :
    μ.real {ω | frobNorm
      (U ω * Matrix.diagonal (levelSpectrum k m L ν) * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (levelSpectrum k m L ν)))).1 *
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (levelSpectrum k m L ν)))).2) ^ 2 <
      Fintype.card m * ∑ j, ν j ^ 2 + (L ^ 2 - τ ^ 2) * Fintype.card k / 2} ≤
      (r + 2) * Real.exp (-(Fintype.card m / (2 * γ ^ 2))) := by
  have := hU.isProbabilityMeasure
  set D := Matrix.diagonal (levelSpectrum k m L ν)
  set μ' := μ.prod (gaussianMatrix (k ⊕ (Fin (r + 1) × m)) (Fin q ⊕ k))
  have hU₁ : HasLaw (fun p : Ω × Matrix (k ⊕ (Fin (r + 1) × m)) (Fin q ⊕ k) ℝ => U p.1)
      (haarFrame (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m))) μ' :=
    hU.comp measurePreserving_fst.hasLaw
  obtain ⟨G, hG⟩ := (hpass.mapOutput Prod.fst).exists_isKrylovCoupling_of_hasLaw_haarFrame
    hp (halg.mapOutput measurable_fst) D
    (0 : Matrix (k ⊕ (Fin (r + 1) × m)) (Fin 0) ℝ) hU₁
    measurePreserving_snd.hasLaw (indepFun_prod₀ hU.aemeasurable aemeasurable_id)
  have hbad :=
    measureReal_exists_mem_blockKrylovSpace_gt_quarter_le_of_hasLaw_gaussianMatrix
      hI hγ hγC hG.hasLaw_gaussianMatrix
    (by simp) (by simpa only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add] using hwidth)
  calc _ = μ'.real (Prod.fst ⁻¹' {ω | frobNorm (U ω * D * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω) D)).1 * (alg.run (hiddenRotationOracle (U ω) D)).2)
          ^ 2 < Fintype.card m * ∑ j, ν j ^ 2 + (L ^ 2 - τ ^ 2) * Fintype.card k / 2}) := by
        rw [← Set.prod_univ, measureReal_def, measureReal_def, Measure.prod_prod, measure_univ,
          mul_one]
    _ ≤ _ := measureReal_mono_ae ?_
    _ ≤ _ := hbad
  filter_upwards [hG.ae_range_le_of_isEmpty, ae_hasOrthonormalCols_of_hasLaw_haarFrame hU₁ le_rfl]
    with ω hω hUω hlt
  change frobNorm _ ^ 2 < _ at hlt
  change ∃ z ∈ _, _ < _
  by_contra hne
  push Not at hne
  rw [QueryAlgorithm.run_mapOutput] at hω
  exact absurd hlt (not_lt.2 (le_frobNorm_of_orthonormal_range_of_pass_lt hν0 hντ hτL hUω hω
    (fun z hz => not_lt.mpr (hne z hz))))


-- Indexed query families require extra elaboration work when transferred through Yao.
set_option maxHeartbeats 800000 in
-- The indexed seed family and its stronger-oracle reduction require extra elaboration work.
/-- A measurable randomized algorithm using at most $r$ batches has an orthogonal hard rotation
of a level spectrum (levels in $[0,\tau]$, $\tau \le L$, extrapolation constant $C$) on which
its squared Frobenius error is at least the optimum plus $(L^2-\tau^2)\lvert k\rvert/2$ with
probability at least one minus the distributional exceptional probability
$(r+2)\exp(-\lvert m\rvert/(2\gamma^2))$. -/
theorem exists_le_measureReal_frobNorm_sub_mul_sq_ge_of_pass_lt
    {r q : ℕ} {L τ C γ : ℝ} {ν : Fin (r + 1) → ℝ} (hI : IsExtrapolationControl L ν C)
    (hν0 : ∀ j, 0 ≤ ν j) (hντ : ∀ j, ν j ≤ τ) (hτL : τ ≤ L) (hγ : 2 < γ)
    (hγC : 36 * C ≤ (γ - 2) ^ 2)
    (hwidth : γ ^ 2 * (q + Fintype.card k) ≤ Fintype.card m)
    {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin (r + 1) × m) → ℝ)
      (k ⊕ (Fin (r + 1) × m) → ℝ) q
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < r)
    (ρ : Measure S) [IsProbabilityMeasure ρ] :
    ∃ U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ,
      HasOrthonormalCols U ∧
      1 - ((r : ℝ) + 2) * Real.exp (-(Fintype.card m / (2 * γ ^ 2))) ≤
      ρ.real {s | let A := U * Matrix.diagonal (levelSpectrum k m L ν) * Uᴴ
        let output := (alg s).run A.mulVec
        Fintype.card m * ∑ j, ν j ^ 2 + (L ^ 2 - τ ^ 2) * Fintype.card k / 2 ≤
            frobNorm (A - output.1 * output.2) ^ 2} := by
  let D := Matrix.diagonal (levelSpectrum k m L ν)
  let threshold := Fintype.card m * ∑ j, ν j ^ 2 + (L ^ 2 - τ ^ 2) * Fintype.card k / 2
  let δ := ((r : ℝ) + 2) * Real.exp (-(Fintype.card m / (2 * γ ^ 2)))
  let B : Set (Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ ×
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)) :=
    {p | HasOrthonormalCols p.1 ∧ threshold ≤ frobNorm (p.1 * D * p.1ᴴ - p.2.1 * p.2.2) ^ 2}
  have hF : Measurable fun p : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ ×
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ) =>
      frobNorm (p.1 * D * p.1ᴴ - p.2.1 * p.2.2) ^ 2 := by
    exact ((measurable_frobNorm).comp (by fun_prop)).pow_const 2
  have hB : MeasurableSet B :=
    (measurable_fst isClosed_setOf_hasOrthonormalCols.measurableSet).inter
      (measurableSet_le measurable_const hF)
  have hO : Measurable (Function.uncurry fun
      (U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ)
      (x : k ⊕ (Fin (r + 1) × m) → ℝ) => hiddenRotationOracle U D x) :=
    Measurable.hiddenRotationOracle measurable_fst measurable_snd _
  have hA : QueryAlgorithm.IsMeasurableFamily fun s => (alg s).comapResponse
      (R' := (k ⊕ (Fin (r + 1) × m) → ℝ) × (k ⊕ (Fin (r + 1) × m) → ℝ)) Prod.fst :=
    halg.comapResponse measurable_fst
  have hsucc : ∀ s, 1 - δ ≤
      (haarFrame (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m))).real
        {U | (U, ((alg s).comapResponse Prod.fst).run (hiddenRotationOracle U D)) ∈ B} := by
    intro s
    let A' := (alg s).comapResponse
      (R' := (k ⊕ (Fin (r + 1) × m) → ℝ) × (k ⊕ (Fin (r + 1) × m) → ℝ)) Prod.fst
    have hrun : Measurable fun U => A'.run (hiddenRotationOracle U D) :=
      ((halg.isMeasurable s).comapResponse measurable_fst).measurable_run hO
    have hpass' := (hpass s).comapResponse
      (R' := (k ⊕ (Fin (r + 1) × m) → ℝ) × (k ⊕ (Fin (r + 1) × m) → ℝ)) Prod.fst
    have hbad := hpass'.measureReal_frobNorm_sub_mul_sq_lt_le_of_pass_lt_of_hasLaw_haarFrame
      hI hν0 hντ hτL hγ hγC (hp s)
      ((halg.isMeasurable s).comapResponse measurable_fst)
      (HasLaw.id (μ := haarFrame (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)))) hwidth
    change 1 - δ ≤ (haarFrame (k ⊕ (Fin (r + 1) × m))
      (k ⊕ (Fin (r + 1) × m))).real {U | HasOrthonormalCols U ∧
        threshold ≤ frobNorm (U * D * Uᴴ - (A'.run (hiddenRotationOracle U D)).1 *
          (A'.run (hiddenRotationOracle U D)).2) ^ 2}
    have hErr : Measurable fun U :
        Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ =>
        frobNorm (U * D * Uᴴ - (A'.run (hiddenRotationOracle U D)).1 *
          (A'.run (hiddenRotationOracle U D)).2) ^ 2 := by
      refine (measurable_frobNorm.comp ?_).pow_const 2
      exact ((measurable_id.matrix_mul measurable_const).matrix_mul
        (Measurable.matrix_conjTranspose (by fun_prop) measurable_id)).sub
        ((measurable_fst.comp hrun).matrix_mul (measurable_snd.comp hrun))
    exact le_measureReal_hasOrthonormalCols_and_ge _ hErr threshold δ hbad
  obtain ⟨U, hU⟩ := hA.exists_le_measureReal_run_mem_of_forall (ρ := ρ)
    (ν := haarFrame (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m))) hO hB hsucc
  by_cases hUo : HasOrthonormalCols U
  · refine ⟨U, hUo, hU.trans (measureReal_mono fun s hs => ?_)⟩
    have h := hs.2
    rw [QueryAlgorithm.run_comapResponse] at h
    exact h
  · exact ⟨1, hasOrthonormalCols_one, hU.trans (measureReal_mono fun s hs => absurd hs.1 hUo)⟩

omit [DecidableEq k] [DecidableEq m] in
/-- The common last step of the fixed-batch Frobenius query lower bounds: on a level spectrum
with a positive head, a width condition, a small exceptional probability and an admissible
excess below the threshold, no algorithm succeeds with probability one half on every PSD
input. -/
private theorem false_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt
    {r q : ℕ} {L τ C γ ε : ℝ} {ν : Fin (r + 1) → ℝ} (hI : IsExtrapolationControl L ν C)
    (hν0 : ∀ j, 0 ≤ ν j) (hντ : ∀ j, ν j ≤ τ) (hτL : τ ≤ L) (hL : 0 < L) (hγ : 2 < γ)
    (hγC : 36 * C ≤ (γ - 2) ^ 2)
    (hwidth : γ ^ 2 * (q + Fintype.card k) ≤ Fintype.card m)
    (hsmall : ((r : ℝ) + 2) * Real.exp (-(Fintype.card m / (2 * γ ^ 2))) < 1 / 2)
    (hexcess : ε * (Fintype.card m * ∑ j, ν j ^ 2) < (L ^ 2 - τ ^ 2) * Fintype.card k / 2)
    {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin (r + 1) × m) → ℝ)
      (k ⊕ (Fin (r + 1) × m) → ℝ) q
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < r)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ,
      A.PosSemidef → 1 / 2 ≤ ρ.real {s |
        frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
          (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) : False := by
  classical
  have hνL : ∀ j, ν j ≤ L := fun j => (hντ j).trans hτL
  obtain ⟨U, hU, hfail⟩ := exists_le_measureReal_frobNorm_sub_mul_sq_ge_of_pass_lt
    hI hν0 hντ hτL hγ hγC hwidth halg hpass hp ρ
  set A := U * Matrix.diagonal (levelSpectrum k m L ν) * Uᴴ
  have hApsd : A.PosSemidef := posSemidef_mul_diagonal_levelSpectrum_mul_conjTranspose hL.le hν0 U
  have hopt : frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2 =
      Fintype.card m * ∑ j, ν j ^ 2 :=
    hU.frobNorm_sub_truncatedSVD_sq_eq_mul_sum_sq hL hν0 hνL
  have hsuccess := hsucc A hApsd
  rw [hopt] at hsuccess
  have hrun : Measurable fun s => (alg s).run A.mulVec := by
    have hO : Measurable fun p :
        Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ ×
          (k ⊕ (Fin (r + 1) × m) → ℝ) => p.1.mulVec p.2 := by fun_prop
    exact (halg.measurable_run
      (O := fun B : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ => B.mulVec)
      hO).comp (measurable_id.prodMk measurable_const)
  let F : Set S := {s | Fintype.card m * ∑ j, ν j ^ 2 + (L ^ 2 - τ ^ 2) * Fintype.card k / 2 ≤
        frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2}
  have hFm : MeasurableSet F := by
    exact measurableSet_le measurable_const
      ((measurable_frobNorm.comp (measurable_const.sub
        ((measurable_fst.comp hrun).matrix_mul (measurable_snd.comp hrun)))).pow_const 2)
  have hsub : {s : S | frobNorm (A - ((alg s).run A.mulVec).1 *
      ((alg s).run A.mulVec).2) ^ 2 ≤ (1 + ε) * (Fintype.card m * ∑ j, ν j ^ 2)} ⊆ Fᶜ := by
    intro s hs hc
    change frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
      (1 + ε) * (Fintype.card m * ∑ j, ν j ^ 2) at hs
    change Fintype.card m * ∑ j, ν j ^ 2 + (L ^ 2 - τ ^ 2) * Fintype.card k / 2 ≤
        frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 at hc
    nlinarith
  have hcompl := probReal_compl_eq_one_sub (μ := ρ) hFm
  have hmono := measureReal_mono (μ := ρ) hsub
  have hfail' : 1 - ((r : ℝ) + 2) * Real.exp (-(Fintype.card m / (2 * γ ^ 2))) ≤ ρ.real F :=
    hfail
  linarith

/-- Numerical floor conditions forced by the selected accuracy cutoff. -/
theorem equispacedGaussianFactor_mul_add_le_and_mul_le_of_floor {r : ℕ} {ε K : ℝ} {q m : ℕ}
    (hK : 1 ≤ K) (hε : 0 < ε) (hεr : ε ≤ equispacedAccuracyBound r)
    (hm : m = ⌊K / (ε * ((r : ℝ) + 1) * (r + 2))⌋₊)
    (hq : (q : ℝ) ≤ K / (equispacedQueryFactor r * ε)) :
    equispacedGaussianFactor r * (q + K) ≤ m ∧
      4 * equispacedGaussianFactor r * (r + 2) ≤ m := by
  let A := equispacedGaussianFactor r
  let T := ((r : ℝ) + 1) * (r + 2)
  let x := K / (ε * T)
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hC : (0 : ℝ) < 4 ^ (r + 1) := pow_pos (by norm_num) _
  have hA : 0 < A := by dsimp [A]; rw [equispacedGaussianFactor_def]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hcut : ε * T * (8 * A * (r + 2)) ≤ 1 := by
    rw [equispacedAccuracyBound_def, le_div_iff₀ (by positivity)] at hεr
    dsimp [T, A]
    rw [equispacedGaussianFactor_def]
    nlinarith [hεr]
  have hx : 8 * A * (r + 2) * K ≤ x := by
    rw [le_div_iff₀ (mul_pos hε hT)]
    calc 8 * A * (r + 2) * K * (ε * T) = K * (ε * T * (8 * A * (r + 2))) := by ring
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hcut (by linarith)
      _ = K := mul_one _
  have hA1 : 1 ≤ A := by
    dsimp [A]
    rw [equispacedGaussianFactor_def]
    have h4 : (1 : ℝ) ≤ 4 ^ (r + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hx8 : 8 * A * (r + 2) ≤ x :=
    (le_mul_of_one_le_right (by positivity) hK).trans hx
  have hx2 : 2 ≤ x := by nlinarith
  have hmx : x / 2 ≤ (m : ℝ) := by
    have hf : x - 1 < (m : ℝ) := by
      rw [hm]
      simpa [x, T, mul_assoc] using Nat.sub_one_lt_floor x
    linarith
  have hqx : (q : ℝ) ≤ x / (4 * A) := by
    convert hq using 1
    dsimp [x, A, T]
    rw [div_div]
    congr 1
    rw [equispacedQueryFactor_def, equispacedGaussianFactor_def]
    ring
  have hqmul : A * q ≤ x / 4 := by
    rw [le_div_iff₀ (by positivity : 0 < 4 * A)] at hqx
    nlinarith
  have hKmul : A * K ≤ x / 4 := by
    have hpos : 0 ≤ (8 * A * (r + 2) - 4 * A) * K :=
      mul_nonneg (by nlinarith [mul_nonneg hA.le hR]) (by linarith)
    nlinarith
  exact ⟨by nlinarith, by nlinarith⟩

/-- The chosen tail multiplicity makes the admissible excess strictly smaller than the hard
instance's lower-error threshold. -/
private theorem mul_equispacedTailFactor_lt {r : ℕ} {ε K : ℝ} {m : ℕ}
    (hK : 0 < K) (hε : 0 < ε)
    (hm : m = ⌊K / (ε * ((r : ℝ) + 1) * (r + 2))⌋₊) :
    ε * (m * equispacedTailFactor r) < (2 * (r : ℝ) + 3) * K / 2 := by
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hT : 0 < ((r : ℝ) + 1) * (r + 2) := by positivity
  have hmle : (m : ℝ) ≤ K / (ε * ((r : ℝ) + 1) * (r + 2)) := by
    rw [hm]
    exact Nat.floor_le (by positivity)
  have htail : 0 ≤ equispacedTailFactor r := by rw [equispacedTailFactor_def]; positivity
  calc ε * (m * equispacedTailFactor r) ≤
      ε * ((K / (ε * ((r : ℝ) + 1) * (r + 2))) * equispacedTailFactor r) := by gcongr
    _ = K * (2 * (r : ℝ) + 3) / 6 := by
      rw [equispacedTailFactor_def]
      field_simp
    _ < (2 * (r : ℝ) + 3) * K / 2 := by nlinarith

omit [DecidableEq k] [DecidableEq m] in
/-- **Fixed-batch Frobenius query lower bound**: for every natural $r$, positive target rank,
$0<\varepsilon$ at most <!-- value equispacedAccuracyBound r -->
$$1/(512\cdot4^{r+1}(r+1)(r+2)^2) \,,$$
and $\lvert m\rvert=\lfloor \lvert k\rvert/(\varepsilon(r+1)(r+2))\rfloor$, every measurable
randomized algorithm
using at most $r$ batches and attaining squared relative Frobenius error $1+\varepsilon$ with
probability at least $1/2$ on every PSD input of dimension $\lvert k\rvert+(r+1)\lvert m\rvert$.
The query lower bound is <!-- value equispacedQueryFactor r -->
$$q>\frac{\lvert k\rvert}{256\cdot4^{r+1}(r+1)(r+2)\varepsilon} \,.$$
Constants are conservative; for $r \ge 3$ the Chebyshev bound
`div_chebyshevQueryFactor_mul_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt`
has the smaller query factor. No printed source.
Result: fixed-batch-low-rank-lower-bound -/
theorem div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt
    [Nonempty k] {r : ℕ} {ε : ℝ} {q : ℕ} (hε : 0 < ε)
    (hεr : ε ≤ equispacedAccuracyBound r)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) /
      (ε * ((r : ℝ) + 1) * (r + 2))⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin (r + 1) × m) → ℝ)
      (k ⊕ (Fin (r + 1) × m) → ℝ) q
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < r)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ,
      A.PosSemidef → 1 / 2 ≤ ρ.real {s |
        frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
          (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (equispacedQueryFactor r * ε) < q := by
  have hk1 : (1 : ℝ) ≤ Fintype.card k := Nat.one_le_cast.mpr Fintype.card_pos
  have hkpos : (0 : ℝ) < Fintype.card k := Nat.cast_pos.mpr Fintype.card_pos
  by_contra hcon
  obtain ⟨hwidth, hmLarge⟩ := equispacedGaussianFactor_mul_add_le_and_mul_le_of_floor
    hk1 hε hεr hm (not_lt.mp hcon)
  obtain ⟨hγ, hγsq, hγC⟩ := equispaced_deviation r
  have hG : 0 < equispacedGaussianFactor r := by rw [equispacedGaussianFactor_def]; positivity
  have hsmall := Real.mul_exp_neg_div_lt_half hG hmLarge
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hexcess := mul_equispacedTailFactor_lt hkpos hε hm
  rw [← sum_sq_eq_equispacedTailFactor] at hexcess
  rw [← hγsq] at hwidth hsmall
  exact false_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt
    (L := (r : ℝ) + 2) (τ := (r : ℝ) + 1) (isExtrapolationControl_equispacedInterpolationFactor r)
    (fun j => by positivity)
    (fun j => by have := (Nat.cast_le (α := ℝ)).2 (Nat.lt_succ_iff.mp j.is_lt); linarith)
    (by linarith) (by positivity) hγ hγC hwidth hsmall
    (by convert hexcess using 1; ring) halg hpass hp ρ hsucc

/-- Numerical conditions forced by the Chebyshev accuracy cutoff and the tail multiplicity
$\lfloor K/(16\varepsilon(r+1)^3)\rfloor$: the width $196(q+K)$ and the tail $784(r+2)$ fit. -/
theorem mul_add_le_and_mul_le_of_floor_of_le_chebyshevAccuracyBound {r : ℕ} {ε K : ℝ}
    {q m : ℕ} (hK : 1 ≤ K) (hε : 0 < ε) (hεr : ε ≤ chebyshevAccuracyBound r)
    (hm : m = ⌊K / (16 * ε * ((r : ℝ) + 1) ^ 3)⌋₊)
    (hq : (q : ℝ) ≤ K / (chebyshevQueryFactor r * ε)) :
    (14 : ℝ) ^ 2 * (q + K) ≤ m ∧ 4 * (14 : ℝ) ^ 2 * (r + 2) ≤ m := by
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  set T : ℝ := ((r : ℝ) + 1) ^ 3 with hT_def
  have hT1 : 1 ≤ T := one_le_pow₀ (by linarith)
  set x := K / (16 * ε * T) with hx_def
  have hden : 0 < 16 * ε * T := by positivity
  have hcut : ε * T * (25088 * (r + 2)) ≤ 1 := by
    rw [chebyshevAccuracyBound_def, le_div_iff₀ (by positivity)] at hεr
    nlinarith [hεr]
  have hx : 1568 * (r + 2) * K ≤ x := by
    rw [hx_def, le_div_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left hcut (by linarith : (0 : ℝ) ≤ K)]
  have hx1568 : 1568 * ((r : ℝ) + 2) ≤ x := by nlinarith
  have hmx : x / 2 ≤ (m : ℝ) := by
    have hf : x - 1 < (m : ℝ) := by
      rw [hm]
      exact Nat.sub_one_lt_floor x
    linarith
  have hqx : 784 * (q : ℝ) ≤ x := by
    have hq' : (q : ℝ) ≤ K / (12544 * T * ε) := by
      rw [chebyshevQueryFactor_def] at hq
      exact hq
    rw [hx_def, le_div_iff₀ hden]
    rw [le_div_iff₀ (by positivity)] at hq'
    nlinarith [hq']
  constructor <;> nlinarith

/-- The Chebyshev tail multiplicity makes the admissible squared-error excess smaller than the
Frobenius threshold. -/
private theorem mul_sum_chebyshevTailLevel_sq_lt {r : ℕ} {ε K : ℝ} {m : ℕ}
    (hK : 0 < K) (hε : 0 < ε) (hm : m = ⌊K / (16 * ε * ((r : ℝ) + 1) ^ 3)⌋₊) :
    ε * (m * ∑ j, chebyshevTailLevel r j ^ 2) <
      ((1 + chebyshevHeadGap r) ^ 2 - 1 ^ 2) * K / 2 := by
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hmle : (m : ℝ) ≤ K / (16 * ε * ((r : ℝ) + 1) ^ 3) := by
    rw [hm]
    exact Nat.floor_le (by positivity)
  have hsum : ∑ j, chebyshevTailLevel r j ^ 2 ≤ (r : ℝ) + 1 := by
    calc ∑ j, chebyshevTailLevel r j ^ 2 ≤ ∑ _j : Fin (r + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => by
            have h0 := le_chebyshevTailLevel r j
            have h1 := chebyshevTailLevel_le r j
            nlinarith
      _ = (r : ℝ) + 1 := by simp
  have hsum0 : 0 ≤ ∑ j, chebyshevTailLevel r j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hδ : chebyshevHeadGap r = 1 / (8 * ((r : ℝ) + 1) ^ 2) := rfl
  have hδ0 : 0 < chebyshevHeadGap r := chebyshevHeadGap_pos r
  have hgap : 2 * chebyshevHeadGap r ≤ (1 + chebyshevHeadGap r) ^ 2 - 1 ^ 2 := by nlinarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc ε * (m * ∑ j, chebyshevTailLevel r j ^ 2) ≤ ε * (m * ((r : ℝ) + 1)) := by gcongr
    _ ≤ ε * (K / (16 * ε * ((r : ℝ) + 1) ^ 3) * ((r : ℝ) + 1)) := by gcongr
    _ = K / (16 * ((r : ℝ) + 1) ^ 2) := by field_simp
    _ < 2 * chebyshevHeadGap r * K / 2 := by
      rw [hδ]
      rw [div_lt_iff₀ (by positivity)]
      field_simp
      nlinarith
    _ ≤ ((1 + chebyshevHeadGap r) ^ 2 - 1 ^ 2) * K / 2 := by gcongr

omit [DecidableEq k] [DecidableEq m] in
/-- **Chebyshev fixed-batch Frobenius query lower bound**: for every natural $r$, positive target
rank, $0<\varepsilon$ at most <!-- value chebyshevAccuracyBound r -->
$$1/(25088(r+1)^3(r+2)) \,,$$
and $\lvert m\rvert=\lfloor \lvert k\rvert/(16\varepsilon(r+1)^3)\rfloor$, every measurable
randomized algorithm using at most $r$ batches and attaining squared relative Frobenius error
$1+\varepsilon$ with probability at least $1/2$ on every PSD input of dimension
$\lvert k\rvert+(r+1)\lvert m\rvert$ uses <!-- value chebyshevQueryFactor r -->
$$q>\frac{\lvert k\rvert}{12544(r+1)^3\varepsilon}$$
queries. No printed source.

Note: the hard spectrum has its head at $1+1/(8(r+1)^2)$ and Chebyshev tail levels in
$[1/2,1]$ (`chebyshevLevelSpectrum`). The dependence on the batch count is polynomial; its
optimal exponent is not asserted. The integer-size form is
`natCast_div_chebyshevQueryFactor_mul_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt`
Result: fixed-batch-low-rank-lower-bound -/
theorem div_chebyshevQueryFactor_mul_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt
    [Nonempty k] {r : ℕ} {ε : ℝ} {q : ℕ} (hε : 0 < ε)
    (hεr : ε ≤ chebyshevAccuracyBound r)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) / (16 * ε * ((r : ℝ) + 1) ^ 3)⌋₊)
    {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin (r + 1) × m) → ℝ)
      (k ⊕ (Fin (r + 1) × m) → ℝ) q
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < r)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ,
      A.PosSemidef → 1 / 2 ≤ ρ.real {s |
        frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
          (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (chebyshevQueryFactor r * ε) < q := by
  have hk1 : (1 : ℝ) ≤ Fintype.card k := Nat.one_le_cast.mpr Fintype.card_pos
  have hkpos : (0 : ℝ) < Fintype.card k := Nat.cast_pos.mpr Fintype.card_pos
  by_contra hcon
  obtain ⟨hwidth, hmLarge⟩ := mul_add_le_and_mul_le_of_floor_of_le_chebyshevAccuracyBound
    hk1 hε hεr hm (not_lt.mp hcon)
  have hsmall := Real.mul_exp_neg_div_lt_half (by norm_num : (0 : ℝ) < 14 ^ 2) hmLarge
  have hδ := chebyshevHeadGap_pos r
  exact false_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt
    (τ := 1) (γ := 14) (isExtrapolationControl_chebyshevTailLevel r)
    (fun j => by linarith [le_chebyshevTailLevel r j]) (chebyshevTailLevel_le r)
    (by linarith) (by linarith) (by norm_num) (by norm_num) hwidth hsmall
    (mul_sum_chebyshevTailLevel_sq_lt hkpos hε hm) halg hpass hp ρ hsucc

-- The theorem's name exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Chebyshev fixed-batch Frobenius query lower bound**, integer sizes: let
$k \ge 1$, $m$, $r$ and $q$ be natural numbers and $n = k + (r + 1)m$, with
$0 < \varepsilon \le \varepsilon_r$ and $m = \lfloor k/(16\varepsilon(r+1)^3) \rfloor$. Let
$(\mathcal{A}_s)$ be a randomized algorithm, that is, a measurable family of algorithms with seed
$s$ drawn from a probability measure $\rho$, where every $\mathcal{A}_s$ makes $q$ matrix–vector
products with its input $\mathbf{A}$ in at most $r$ batches (the products of a batch are chosen
before any response of that batch is seen) and returns $\mathbf{W} \in \mathbb{R}^{n \times k}$
and $\mathbf{M} \in \mathbb{R}^{k \times n}$. If for every symmetric positive semidefinite
$\mathbf{A} \in \mathbb{R}^{n \times n}$
$$\mathbb{P}_{s \sim \rho}\bigl[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2\bigr]
\ge \frac{1}{2} \,,$$
then
$$q > \frac{k}{C_r\,\varepsilon} \,.$$
Here <!-- value chebyshevQueryFactor r -->
$C_r = 12544(r+1)^3$ and <!-- value chebyshevAccuracyBound r -->
$\varepsilon_r = 1/(25088(r+1)^3(r+2))$.
No printed source.

Note: $C_r$ is `chebyshevQueryFactor r` (`chebyshevQueryFactor_le`) and $\varepsilon_r$ is
`chebyshevAccuracyBound r` (`le_chebyshevAccuracyBound`). The $n$ coordinates are indexed by
`Fin k ⊕ (Fin (r + 1) × Fin m)`: a head of $k$ coordinates and $r + 1$ tail levels of $m$ each.
General form, with finite index types in place of $k$ and $m$:
`div_chebyshevQueryFactor_mul_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt`.
The hard spectrum has its head at $1+1/(8(r+1)^2)$ and Chebyshev tail levels in $[1/2,1]$
(`chebyshevLevelSpectrum`). The dependence on the batch count is polynomial; its optimal exponent
is not asserted.
Result: fixed-batch-low-rank-lower-bound -/
theorem
    natCast_div_chebyshevQueryFactor_mul_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt
    {k m r q : ℕ} {ε : ℝ} (hk : 0 < k) (hε : 0 < ε) (hεr : ε ≤ chebyshevAccuracyBound r)
    (hm : m = ⌊(k : ℝ) / (16 * ε * ((r : ℝ) + 1) ^ 3)⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (Fin k ⊕ (Fin (r + 1) × Fin m) → ℝ)
      (Fin k ⊕ (Fin (r + 1) × Fin m) → ℝ) q
      (Matrix (Fin k ⊕ (Fin (r + 1) × Fin m)) (Fin k) ℝ ×
        Matrix (Fin k) (Fin k ⊕ (Fin (r + 1) × Fin m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < r)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (Fin k ⊕ (Fin (r + 1) × Fin m)) (Fin k ⊕ (Fin (r + 1) × Fin m)) ℝ,
      A.PosSemidef → 1 / 2 ≤ ρ.real {s |
        frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
          (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2}) :
    (k : ℝ) / (chebyshevQueryFactor r * ε) < q := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h :=
    div_chebyshevQueryFactor_mul_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt
    (k := Fin k) (m := Fin m) (r := r) (ε := ε) (alg := alg)
  simp only [Fintype.card_fin] at h
  exact h hε hεr hm halg hpass hp ρ hsucc

end NLAlib
