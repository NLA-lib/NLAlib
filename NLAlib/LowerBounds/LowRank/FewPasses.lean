/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Real.Basic
public import NLAlib.ForMathlib.MeasureTheory.Measure.Prod
public import NLAlib.Matrix.Basic.Gram
public import NLAlib.LowerBounds.QueryModel.HiddenRotation
public import NLAlib.LowerBounds.QueryModel.Yao
public import NLAlib.Matrix.Spectral.LowRank
public import NLAlib.Polynomial.Interpolation.DividedDifference
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues

/-!
# Lower bounds for few-pass low-rank approximation

The hard instances of the pass lower bounds for rank-$k$ approximation are
$\mathbf{A} = \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$ with $\mathbf{U}$
Haar and $\mathbf{d}$ = `equispacedLevelSpectrum k m p`: a head of $k$ eigenvalues $p + 2$ and a
tail of $p + 1$ equispaced levels $1, \dots, p + 1$ with $m$ eigenvalues each. A $p$-pass
algorithm sees $\mathbf{U}$ only through polynomials of degree at most $p$ in
$\operatorname{diag}(\mathbf{d})$, and such a polynomial is fixed at the head by its values on the
tail levels (finite differences), so the head cannot be captured unless the number of products is
of the order of $m$. This file has the deterministic and Gaussian steps; the two-pass
algorithmic lower bounds ($p = 2$), which go through the Krylov coupling, are proved below.

## Main definitions

* `NLAlib.equispacedLevelSpectrum`.

## Main results

* `NLAlib.HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq`,
  `NLAlib.HasOrthonormalCols.singularValues_mul_diagonal_mul_card`: the optimum.
* `NLAlib.le_frobNorm_diagonal_sub_mul_sq`, `NLAlib.le_specNorm_diagonal_sub_mul_sq`: error from
  head capture.
* `NLAlib.mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace`: the interpolation bound.
* `NLAlib.measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix`: Gaussian
  head capture.
* In `QueryAlgorithm.IsPassStructured`,
  `measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame` and
  `measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`: deterministic two-pass lower bounds.
* `NLAlib.exists_le_measureReal_frobNorm_sub_mul_sq_ge`: randomized worst-case error.
* `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le`,
  `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one`,
  `NLAlib.lt_of_forall_le_measureReal_specNorm_sub_mul_le`: query-count lower bounds.
* `NLAlib.natCast_div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le`,
  `NLAlib.natCast_div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one`: the two-pass
  and one-pass Frobenius query lower bounds with natural-number sizes.
-/

@[expose] public section

namespace NLAlib

/-- The **equispaced-level spectrum** with head $k$ and tail $m$ for $p$ passes, on
$k \oplus (\{0, \dots, p\} \times m)$: the value $p + 2$ on the head coordinates and $j + 1$ on
the tail level $j$. For $p = 2$ it is
$\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m, 3\mathbf{I}_m)$, whose best
rank-$\lvert k \rvert$ Frobenius error is $14\lvert m \rvert$. -/
def equispacedLevelSpectrum (k m : Type*) (p : ℕ) : k ⊕ (Fin (p + 1) × m) → ℝ :=
  Sum.elim (fun _ => (p : ℝ) + 2) fun x => (x.1 : ℝ) + 1

end NLAlib

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k m : Type*} [Fintype k]
  [Fintype m] [DecidableEq k] [DecidableEq m]

/-- The optimum of the two-pass hard instance: for orthogonal $\mathbf{U}$ and
$\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m,
3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$,
$\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2 = 14\lvert m \rvert$. -/
theorem HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq
    {U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ} (hU : HasOrthonormalCols U) :
    frobNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ -
        truncatedSVD (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ)
          (Fintype.card k)) ^ 2 = 14 * Fintype.card m := by
  set d := equispacedLevelSpectrum k m 2
  set A := U * Matrix.diagonal d * Uᴴ
  set h : k ⊕ (Fin 3 × m) → ℝ := Sum.elim (fun _ => 4) 0
  have hcard : Fintype.card (k ⊕ (Fin 3 × m)) = Fintype.card k + 3 * Fintype.card m := by
    simp
  -- the squared Frobenius norm of the diagonal pieces
  have hD : frobNorm (Matrix.diagonal d) ^ 2 = 16 * Fintype.card k + 14 * Fintype.card m := by
    rw [frobNorm_diagonal_sq]
    simp [d, equispacedLevelSpectrum, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fin.sum_univ_three]
    ring
  have hT : frobNorm (Matrix.diagonal (d - h)) ^ 2 = 14 * Fintype.card m := by
    rw [frobNorm_diagonal_sq]
    simp [d, h, equispacedLevelSpectrum, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fin.sum_univ_three]
    ring
  have hrank : (U * Matrix.diagonal h * Uᴴ).rank ≤ Fintype.card k := by
    refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans ?_)
    rw [Matrix.rank_diagonal]
    refine Fintype.card_le_of_surjective (fun a : k => ⟨Sum.inl a, by norm_num [h]⟩) ?_
    rintro ⟨a | x, hx⟩
    · exact ⟨a, rfl⟩
    · exact (hx rfl).elim
  have hσ : ∀ i, singularValues A i ≤ 4 := by
    intro i
    refine (singularValues_le_specNorm A i).trans ?_
    rw [hU.specNorm_mul_conjTranspose_right, hU.specNorm_mul_left]
    refine specNorm_diagonal_le (by norm_num) fun i => ?_
    rcases i with a | ⟨j, b⟩
    · norm_num [d, equispacedLevelSpectrum]
    · fin_cases j <;> norm_num [d, equispacedLevelSpectrum]
  refine le_antisymm ?_ ?_
  · -- Eckart–Young against the head part `U diag(h) Uᴴ`
    rw [← hT]
    refine pow_le_pow_left₀ (frobNorm_nonneg _)
      ((frobNorm_sub_truncatedSVD_le_of_rank_le A hrank).trans_eq ?_) 2
    rw [show A - U * Matrix.diagonal h * Uᴴ = U * Matrix.diagonal (d - h) * Uᴴ by
      rw [show d - h = fun i => d i - h i from rfl, ← Matrix.diagonal_sub, Matrix.mul_sub,
        Matrix.sub_mul],
      hU.frobNorm_mul_conjTranspose_right, hU.frobNorm_mul_left]
  · -- the head singular values are at most `4`, so the tail carries at least `14 |m|`
    have hA : frobNorm A ^ 2 = 16 * Fintype.card k + 14 * Fintype.card m := by
      rw [hU.frobNorm_mul_conjTranspose_right, hU.frobNorm_mul_left, hD]
    have hhead : ∑ i ∈ Finset.range (Fintype.card k), singularValues A i ^ 2 ≤
        16 * Fintype.card k := by
      calc _ ≤ ∑ i ∈ Finset.range (Fintype.card k), (4 : ℝ) ^ 2 :=
            Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (singularValues_nonneg A i) (hσ i) 2
        _ = _ := by simp; ring
    rw [frobNorm_sub_truncatedSVD_sq, min_self]
    rw [frobNorm_sq_eq_sum_singularValues_sq, ← Finset.sum_range_add_sum_Ico _
      (hcard ▸ Nat.le_add_right _ _ : Fintype.card k ≤ _)] at hA
    linarith

/-- The kernel of a coordinate restriction has dimension at least the number of the other
coordinates. -/
private theorem card_le_finrank_ker_funLeft {ι τ : Type*} [Fintype ι] [Fintype τ] (f : τ → ι) :
    Fintype.card ι ≤
      Module.finrank ℝ (LinearMap.ker (LinearMap.funLeft ℝ ℝ f)) + Fintype.card τ := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.funLeft ℝ ℝ f)
  have h2 := Submodule.finrank_le (LinearMap.range (LinearMap.funLeft ℝ ℝ f))
  rw [Module.finrank_fintype_fun_eq_card] at h1 h2
  omega

/-- The squared norm of a diagonal action is a weighted sum of squares. -/
private theorem sq_norm_diagonal_mulVec {n : Type*} [Fintype n] [DecidableEq n] (d x : n → ℝ) :
    ‖WithLp.toLp 2 (Matrix.diagonal d *ᵥ x)‖ ^ 2 = ∑ i, (d i * x i) ^ 2 := by
  rw [EuclideanSpace.norm_toLp_sq_eq_sum_sq]
  simp only [Matrix.mulVec_diagonal]

/-- The $(k + 1)$-st singular value of the two-pass hard instance is $3$: for orthogonal
$\mathbf{U}$ and $m$ nonempty, $\sigma_k(\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}) = 3$
(indices from $0$). -/
theorem HasOrthonormalCols.singularValues_mul_diagonal_mul_card [Nonempty m]
    {U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ} (hU : HasOrthonormalCols U) :
    singularValues (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ) (Fintype.card k) =
      3 := by
  rw [Matrix.mul_assoc, hU.singularValues_mul_left, hU.singularValues_mul_conjTranspose_right]
  apply le_antisymm
  · -- upper bound: the codimension-`k` subspace of tail coordinates
    refine singularValues_le_of_forall_mem _
      (LinearMap.ker (LinearMap.funLeft ℝ ℝ (Sum.inl : k → k ⊕ (Fin 3 × m)))) ?_ (by norm_num) ?_
    · exact card_le_finrank_ker_funLeft (Sum.inl : k → k ⊕ (Fin 3 × m))
    intro x hx
    have hx' : ∀ a, x (Sum.inl a) = 0 := fun a => congrFun (LinearMap.mem_ker.mp hx) a
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
    rw [mul_pow, sq_norm_diagonal_mulVec, EuclideanSpace.norm_toLp_sq_eq_sum_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rcases i with a | ⟨l, j⟩
    · simp [hx' a]
    · have hl : ((l : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by have := l.isLt; omega : (l : ℕ) ≤ 2)
      have h0 : (0 : ℝ) ≤ (l : ℕ) + 1 := by positivity
      have h3 : ((l : ℕ) : ℝ) + 1 ≤ 3 := by linarith
      simp only [equispacedLevelSpectrum, Sum.elim_inr]
      nlinarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h3 2)
        (sq_nonneg (x (Sum.inr (l, j))))]
  · -- lower bound: the subspace killing the levels 0 and 1 has dimension above `k`
    refine le_singularValues_of_forall_mem _ (LinearMap.ker (LinearMap.funLeft ℝ ℝ
      (fun p : Fin 2 × m => (Sum.inr (Fin.castSucc p.1, p.2) : k ⊕ (Fin 3 × m))))) ?_ ?_
    · have := card_le_finrank_ker_funLeft
        (fun p : Fin 2 × m => (Sum.inr (Fin.castSucc p.1, p.2) : k ⊕ (Fin 3 × m)))
      have hm : 0 < Fintype.card m := Fintype.card_pos
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at this ⊢
      omega
    intro x hx
    have hx' : ∀ (a : Fin 2) (j : m), x (Sum.inr (Fin.castSucc a, j)) = 0 :=
      fun a j => congrFun (LinearMap.mem_ker.mp hx) (a, j)
    apply (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp
    rw [mul_pow, sq_norm_diagonal_mulVec, EuclideanSpace.norm_toLp_sq_eq_sum_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rcases i with a | ⟨l, j⟩
    · have hd : equispacedLevelSpectrum k m 2 (Sum.inl a) = 4 := by
        simp [equispacedLevelSpectrum]; norm_num
      rw [hd]
      nlinarith [sq_nonneg (x (Sum.inl a))]
    · by_cases hl : (l : ℕ) < 2
      · have h0 : x (Sum.inr (l, j)) = 0 := by
          have := hx' ⟨l, hl⟩ j
          rwa [show Fin.castSucc (⟨l, hl⟩ : Fin 2) = l from Fin.ext rfl] at this
        simp [h0]
      · have hl2 : ((l : ℕ) : ℝ) = 2 := by
          have := l.isLt
          exact_mod_cast (by omega : (l : ℕ) = 2)
        simp only [equispacedLevelSpectrum, Sum.elim_inr, hl2]
        nlinarith [sq_nonneg (x (Sum.inr (l, j)))]

/-- A real star projection is symmetric. -/
private lemma isStarProjection_entry_symm {n : Type*} [Fintype n]
    {P : Matrix n n ℝ} (hP : IsStarProjection P) (i j : n) : P i j = P j i := by
  have h := congrFun (congrFun hP.isSelfAdjoint j) i
  simpa [Matrix.star_apply] using h

/-- Frobenius error from head capture: for every $\mathbf{W} \in \mathbb{R}^{n \times k}$ and
$\mathbf{M} \in \mathbb{R}^{k \times n}$, $n = k \oplus (\{0, 1, 2\} \times m)$ and
$\mathbf{D} = \operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m, 3\mathbf{I}_m)$,
$$\|\mathbf{D} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \ge 14\lvert m \rvert + 7\bigl(\lvert k
\rvert - t\bigr) \,, \qquad t = \sum_{a \in k}\|\mathbf{P}_{\mathbf{W}}\mathbf{e}_a\|^2 \,,$$
$t$ the head mass captured by the range of $\mathbf{W}$. -/
theorem le_frobNorm_diagonal_sub_mul_sq (W : Matrix (k ⊕ (Fin 3 × m)) k ℝ)
    (M : Matrix k (k ⊕ (Fin 3 × m)) ℝ) :
    14 * Fintype.card m + 7 * (Fintype.card k -
        ∑ a : k, ‖WithLp.toLp 2 (rangeProjector W *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2) ≤
      frobNorm (Matrix.diagonal (equispacedLevelSpectrum k m 2) - W * M) ^ 2 := by
  set P := rangeProjector W with hPdef
  set Q : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ := 1 - P with hQdef
  set d := equispacedLevelSpectrum k m 2 with hd
  have hP : IsStarProjection P := isStarProjection_rangeProjector W
  have hQ : IsStarProjection Q := isStarProjection_one_sub_rangeProjector W
  -- Step 1: `Q (D - W M) = Q D` since `Q W = 0`, and `Q` contracts.
  have hcontr : frobNorm (Q * Matrix.diagonal d) ^ 2 ≤
      frobNorm (Matrix.diagonal d - W * M) ^ 2 := by
    have h : Q * Matrix.diagonal d = Q * (Matrix.diagonal d - W * M) := by
      have hQW : Q * W = 0 := by
        rw [hQdef, Matrix.sub_mul, Matrix.one_mul, rangeProjector_mul_self, sub_self]
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hQW, Matrix.zero_mul, sub_zero]
    rw [h]
    exact pow_le_pow_left₀ (frobNorm_nonneg _) (hQ.frobNorm_mul_le _) 2
  -- Step 2: `‖Q D‖_F² = ∑ d_j² Q_jj`, as `∑ᵢ Q_ij² = Q_jj`.
  have hcol : ∀ j, ∑ i, Q i j ^ 2 = Q j j := by
    intro j
    refine Eq.trans ?_ (congrFun (congrFun hQ.mul_self j) j)
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [isStarProjection_entry_symm hQ j i]
    ring
  have hfrob : frobNorm (Q * Matrix.diagonal d) ^ 2 = ∑ j, d j ^ 2 * Q j j := by
    rw [frobNorm_sq_eq_sum_sq, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hcol j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_diagonal]
    ring
  have hQjj : ∀ j, Q j j = 1 - P j j := fun j => by rw [hQdef]; simp
  -- Step 3: `P_jj = ‖P e_j‖²` is nonnegative, and `∑ P_jj = rank P ≤ k`.
  have hPnn : ∀ j, 0 ≤ P j j := fun j => by
    rw [← hP.norm_toLp_mulVec_single_sq j]; positivity
  have ht : ∑ a : k, ‖WithLp.toLp 2 (P *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2 =
      ∑ a : k, P (Sum.inl a) (Sum.inl a) :=
    Finset.sum_congr rfl fun a _ => hP.norm_toLp_mulVec_single_sq _
  have htr : ∑ j, P j j ≤ Fintype.card k := by
    have h1 : ∑ j, P j j = P.trace := rfl
    have h2 : P.trace = (W.rank : ℝ) := trace_rangeProjector W
    have h3 : (W.rank : ℝ) ≤ Fintype.card k := by exact_mod_cast Matrix.rank_le_card_width W
    linarith
  rw [Fintype.sum_sum_type] at htr
  -- Step 4: split the head (`d = 4`) from the tail (`d = 1, 2, 3`, where `d² ≤ 9`).
  have hd_inl : ∀ a : k, d (Sum.inl a) = 4 := fun a => by
    simp [hd, equispacedLevelSpectrum]; norm_num
  have hd_inr : ∀ x : Fin 3 × m, d (Sum.inr x) = ((x.1 : ℕ) : ℝ) + 1 := fun x => by
    simp [hd, equispacedLevelSpectrum]
  have hB : ∑ x : Fin 3 × m, (((x.1 : ℕ) : ℝ) + 1) ^ 2 * P (Sum.inr x) (Sum.inr x) ≤
      9 * ∑ x : Fin 3 × m, P (Sum.inr x) (Sum.inr x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have h3 : ((x.1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast Fin.is_le x.1
    have h0 : (0 : ℝ) ≤ ((x.1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h9 : (0 : ℝ) ≤ 9 - (((x.1 : ℕ) : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [mul_nonneg h9 (hPnn (Sum.inr x))]
  have hA : ∑ a : k, d (Sum.inl a) ^ 2 * Q (Sum.inl a) (Sum.inl a) =
      16 * Fintype.card k - 16 * ∑ a : k, P (Sum.inl a) (Sum.inl a) := by
    have h16 : ∀ a : k, d (Sum.inl a) ^ 2 * Q (Sum.inl a) (Sum.inl a) =
        16 - 16 * P (Sum.inl a) (Sum.inl a) := fun a => by
      rw [hd_inl, hQjj]; ring
    rw [Finset.sum_congr rfl fun a _ => h16 a, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hX : ∑ x : Fin 3 × m, (((x.1 : ℕ) : ℝ) + 1) ^ 2 = 14 * (Fintype.card m : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp [Fin.sum_univ_three, Finset.sum_const, Finset.card_univ]
    ring
  have hBt : ∑ x : Fin 3 × m, d (Sum.inr x) ^ 2 * Q (Sum.inr x) (Sum.inr x) =
      14 * (Fintype.card m : ℝ) -
        ∑ x : Fin 3 × m, (((x.1 : ℕ) : ℝ) + 1) ^ 2 * P (Sum.inr x) (Sum.inr x) := by
    rw [← hX, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hd_inr, hQjj]
    ring
  have hmain : 14 * (Fintype.card m : ℝ) + 7 * (Fintype.card k -
      ∑ a : k, P (Sum.inl a) (Sum.inl a)) ≤ ∑ j, d j ^ 2 * Q j j := by
    rw [Fintype.sum_sum_type, hA, hBt]
    linarith
  rw [ht]
  linarith [hcontr, hfrob, hmain]

/-- Spectral error from head capture: for every $\mathbf{W} \in \mathbb{R}^{n \times k}$ and
$\mathbf{M} \in \mathbb{R}^{k \times n}$, $k$ nonempty, $n = k \oplus (\{0, 1, 2\} \times m)$ and
$\mathbf{D} = \operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m, 3\mathbf{I}_m)$,
$$\|\mathbf{D} - \mathbf{W}\mathbf{M}\|_2^2 \ge
\frac{16(\lvert k \rvert - t)}{\lvert k \rvert} \,, \qquad
t = \sum_{a \in k}\|\mathbf{P}_{\mathbf{W}}\mathbf{e}_a\|^2 \,.$$ -/
theorem le_specNorm_diagonal_sub_mul_sq [Nonempty k] (W : Matrix (k ⊕ (Fin 3 × m)) k ℝ)
    (M : Matrix k (k ⊕ (Fin 3 × m)) ℝ) :
    16 * (Fintype.card k -
        ∑ a : k, ‖WithLp.toLp 2 (rangeProjector W *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2) /
        Fintype.card k ≤
      specNorm (Matrix.diagonal (equispacedLevelSpectrum k m 2) - W * M) ^ 2 := by
  classical
  set P := rangeProjector W with hPdef
  have hP : IsStarProjection P := isStarProjection_rangeProjector W
  set X := Matrix.diagonal (equispacedLevelSpectrum k m 2) - W * M with hXdef
  set e : k → (k ⊕ (Fin 3 × m) → ℝ) := fun a => Pi.single (Sum.inl a) 1 with he
  have hnorm1 : ∀ a : k, ‖WithLp.toLp 2 (e a)‖ = 1 := by
    intro a
    simp [he]
  have hpy : ∀ a : k,
      ‖WithLp.toLp 2 ((1 - P) *ᵥ e a)‖ ^ 2 = 1 - ‖WithLp.toLp 2 (P *ᵥ e a)‖ ^ 2 := by
    intro a
    have h := hP.norm_toLp_sq_eq_add (e a)
    rw [hnorm1 a] at h
    linarith
  have hDe : ∀ a : k, Matrix.diagonal (equispacedLevelSpectrum k m 2) *ᵥ e a = (4 : ℝ) • e a := by
    intro a
    ext i
    rcases i with i | ⟨j, i⟩
    · by_cases h : i = a
      · subst h
        simp [he, equispacedLevelSpectrum, Matrix.mulVec_diagonal]
        norm_num
      · simp [he, equispacedLevelSpectrum, Matrix.mulVec_diagonal, h]
    · simp [he, equispacedLevelSpectrum, Matrix.mulVec_diagonal]
  have hPW : (1 - P) * W = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPdef, rangeProjector_mul_self, sub_self]
  have hWM : (1 - P) * (W * M) = 0 := by rw [← Matrix.mul_assoc, hPW, Matrix.zero_mul]
  have hsq : ∀ a : k, 16 * ‖WithLp.toLp 2 ((1 - P) *ᵥ e a)‖ ^ 2 ≤ specNorm X ^ 2 := by
    intro a
    have hXe : X *ᵥ e a = Matrix.diagonal (equispacedLevelSpectrum k m 2) *ᵥ e a -
        (W * M) *ᵥ e a := by
      rw [hXdef, Matrix.sub_mulVec]
    have hw : (1 - P) *ᵥ (X *ᵥ e a) = (4 : ℝ) • ((1 - P) *ᵥ e a) := by
      have hWMv : (1 - P) *ᵥ ((W * M) *ᵥ e a) = 0 := by
        rw [Matrix.mulVec_mulVec, hWM, Matrix.zero_mulVec]
      rw [hXe, Matrix.mulVec_sub, hWMv, sub_zero, hDe, Matrix.mulVec_smul]
    have hA := hP.norm_toLp_sq_eq_add (X *ᵥ e a)
    have hB := norm_toLp_mulVec_le X (e a)
    rw [hnorm1 a, mul_one] at hB
    have hC : ‖WithLp.toLp 2 ((1 - P) *ᵥ (X *ᵥ e a))‖ = 4 * ‖WithLp.toLp 2 ((1 - P) *ᵥ e a)‖ := by
      rw [hw, WithLp.toLp_smul, norm_smul]
      norm_num
    rw [hC, mul_pow] at hA
    nlinarith [sq_nonneg ‖WithLp.toLp 2 (P *ᵥ (X *ᵥ e a))‖, pow_le_pow_left₀ (norm_nonneg _) hB 2]
  have hsum : ∑ a : k, 16 * ‖WithLp.toLp 2 ((1 - P) *ᵥ e a)‖ ^ 2 ≤
      ∑ a : k, specNorm X ^ 2 := Finset.sum_le_sum fun a _ => hsq a
  rw [← Finset.mul_sum] at hsum
  simp only [hpy, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hsum
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.mpr Fintype.card_pos
  rw [div_le_iff₀ hk]
  nlinarith [hsum]

/-- A real polynomial of degree below $3$ satisfies $P(4) = P(1) - 3P(2) + 3P(3)$. -/
private lemma eval_four_eq_of_natDegree_lt {P : Polynomial ℝ} (hP : P.natDegree < 3) :
    P.eval 4 = P.eval 1 - 3 * P.eval 2 + 3 * P.eval 3 := by
  have h := sum_neg_one_pow_mul_choose_mul_eval_eq_zero hP 1 1
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Summed over the columns, $P(4)^2 \le 19\bigl(P(1)^2 + P(2)^2 + P(3)^2\bigr)$ for polynomials
of degree below $3$ (Cauchy–Schwarz on the coefficients $(1, -3, 3)$). -/
private lemma sum_eval_four_sq_le_of_natDegree_lt {b : Type*} [Fintype b] {f : b → Polynomial ℝ}
    (hdeg : ∀ c, (f c).natDegree < 3) :
    ∑ c, (f c).eval 4 ^ 2 ≤
      19 * (∑ c, (f c).eval 1 ^ 2 + ∑ c, (f c).eval 2 ^ 2 + ∑ c, (f c).eval 3 ^ 2) := by
  have hN1 : ∀ c, (f c).eval 4 ^ 2 ≤
      19 * ((f c).eval 1 ^ 2 + (f c).eval 2 ^ 2 + (f c).eval 3 ^ 2) := by
    intro c
    rw [eval_four_eq_of_natDegree_lt (hdeg c)]
    nlinarith [sq_nonneg (3 * (f c).eval 1 + (f c).eval 2),
      sq_nonneg (3 * (f c).eval 1 - (f c).eval 3),
      sq_nonneg (3 * (f c).eval 2 + 3 * (f c).eval 3)]
  have := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hN1 c
  simpa only [← Finset.mul_sum, Finset.sum_add_distrib] using this


/-- Interpolation bound for depth-3 Krylov vectors: let
$\mathbf{G} \in \mathbb{R}^{n \times b}$ with tail blocks $\mathbf{G}_j$ (rows of level $j + 1$)
and head block $\mathbf{G}_h$, $s^2\mathbf{I} \preceq \mathbf{G}_j^{\mathsf{H}}\mathbf{G}_j$ for
$j = 0, 1, 2$ and $\|\mathbf{G}_h\|_2 \le S$. Every $\mathbf{z} \in \mathcal{K}_3(\mathbf{D},
\mathbf{G})$ has
$$s^2\sum_{a \in k} z_a^2 \le 19\,S^2\,\|\mathbf{z}\|^2 \,.$$ -/
theorem mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace {b : Type*} [Fintype b]
    [DecidableEq b] {G : Matrix (k ⊕ (Fin 3 × m)) b ℝ} {s S : ℝ}
    (hs : ∀ j : Fin 3, s ^ 2 • (1 : Matrix b b ℝ) ≤
      (G.submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        G.submatrix (fun i : m => Sum.inr (j, i)) id)
    (hS : specNorm (G.submatrix Sum.inl id) ≤ S) {z : k ⊕ (Fin 3 × m) → ℝ}
    (hz : z ∈ blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m 2)) G 3) :
    s ^ 2 * ∑ a : k, z (Sum.inl a) ^ 2 ≤ 19 * S ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 := by
  obtain ⟨f, hf, hz'⟩ := mem_blockKrylovSpace_iff.1 hz
  have hzi : ∀ x, z x = ∑ c, (f c).eval (equispacedLevelSpectrum k m 2 x) * G x c := by
    intro x
    rw [← hz']
    simp [Finset.sum_apply, aeval_diagonal_self, Matrix.mulVec_diagonal]
  have hdeg : ∀ c, (f c).natDegree < 3 := by
    intro c
    by_cases h0 : f c = 0
    · simp [h0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 (by exact_mod_cast hf c)
  -- head block: `‖G_h v‖ ≤ S ‖v‖` with `v = P(4)`
  have hH : ∑ a : k, z (Sum.inl a) ^ 2 ≤ S ^ 2 * ∑ c, (f c).eval 4 ^ 2 := by
    have hw : ∀ a : k, z (Sum.inl a) =
        (G.submatrix (fun a : k => Sum.inl a) id *ᵥ fun c => (f c).eval 4) a := by
      intro a
      rw [hzi]
      norm_num [equispacedLevelSpectrum, Matrix.mulVec, dotProduct, mul_comm]
    have h1 : ‖WithLp.toLp 2 (G.submatrix (fun a : k => Sum.inl a) id *ᵥ fun c => (f c).eval 4)‖ ≤
        S * ‖WithLp.toLp 2 (fun c => (f c).eval 4)‖ :=
      (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, EuclideanSpace.norm_toLp_sq_eq_sum_sq, EuclideanSpace.norm_toLp_sq_eq_sum_sq] at h2
    simp only [hw]
    exact h2
  -- the three tail levels
  have hL0 : s ^ 2 * ∑ c, (f c).eval 1 ^ 2 ≤ ∑ i, z (Sum.inr ((0 : Fin 3), i)) ^ 2 := by
    have hw : ∀ i : m, z (Sum.inr ((0 : Fin 3), i)) =
        (G.submatrix (fun i : m => Sum.inr ((0 : Fin 3), i)) id *ᵥ fun c => (f c).eval 1) i := by
      intro i
      rw [hzi]
      norm_num [equispacedLevelSpectrum, Matrix.mulVec, dotProduct, mul_comm]
    simp only [hw]
    exact sq_mul_sum_sq_le_sum_sq_mulVec _ (hs 0) _
  have hL1 : s ^ 2 * ∑ c, (f c).eval 2 ^ 2 ≤ ∑ i, z (Sum.inr ((1 : Fin 3), i)) ^ 2 := by
    have hw : ∀ i : m, z (Sum.inr ((1 : Fin 3), i)) =
        (G.submatrix (fun i : m => Sum.inr ((1 : Fin 3), i)) id *ᵥ fun c => (f c).eval 2) i := by
      intro i
      rw [hzi]
      norm_num [equispacedLevelSpectrum, Matrix.mulVec, dotProduct, mul_comm]
    simp only [hw]
    exact sq_mul_sum_sq_le_sum_sq_mulVec _ (hs 1) _
  have hL2 : s ^ 2 * ∑ c, (f c).eval 3 ^ 2 ≤ ∑ i, z (Sum.inr ((2 : Fin 3), i)) ^ 2 := by
    have hw : ∀ i : m, z (Sum.inr ((2 : Fin 3), i)) =
        (G.submatrix (fun i : m => Sum.inr ((2 : Fin 3), i)) id *ᵥ fun c => (f c).eval 3) i := by
      intro i
      rw [hzi]
      norm_num [equispacedLevelSpectrum, Matrix.mulVec, dotProduct, mul_comm]
    simp only [hw]
    exact sq_mul_sum_sq_le_sum_sq_mulVec _ (hs 2) _
  have hN := sum_eval_four_sq_le_of_natDegree_lt hdeg
  -- the norm of `z` splits into head and tails
  have hnorm : ‖WithLp.toLp 2 z‖ ^ 2 = ∑ a : k, z (Sum.inl a) ^ 2 +
      (∑ i, z (Sum.inr ((0 : Fin 3), i)) ^ 2 + ∑ i, z (Sum.inr ((1 : Fin 3), i)) ^ 2 +
        ∑ i, z (Sum.inr ((2 : Fin 3), i)) ^ 2) := by
    rw [EuclideanSpace.norm_toLp_sq_eq_sum_sq, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fin.sum_univ_three]
  have hHnn : 0 ≤ ∑ a : k, z (Sum.inl a) ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  rw [hnorm]
  have h1 := mul_le_mul_of_nonneg_left hH (sq_nonneg s)
  have h2 := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ s ^ 2 * S ^ 2)
  have h3 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hL0 hL1) hL2)
    (by positivity : (0 : ℝ) ≤ 19 * S ^ 2)
  have h4 := mul_nonneg (by positivity : (0 : ℝ) ≤ 19 * S ^ 2) hHnn
  nlinarith [h1, h2, h3, h4]

/-- Algebra of the final step: a Krylov vector with head mass $\Sigma > 171 N/(\gamma - 2)^2$ is
impossible when $s \ge (\gamma - 2)t > 0$ and $s^2\Sigma \le 19(3t)^2 N$. -/
private theorem false_of_mul_sum_sq_le_of_lt {γ t s N sumH : ℝ} (hγ : 2 < γ) (ht : 0 < t)
    (hs : (γ - 2) * t ≤ s) (hN : 0 ≤ N) (key : s ^ 2 * sumH ≤ 19 * (3 * t) ^ 2 * N)
    (hlt : 171 / (γ - 2) ^ 2 * N < sumH) : False := by
  have hγ2 : 0 < γ - 2 := by linarith
  have hsp : 0 < s := lt_of_lt_of_le (mul_pos hγ2 ht) hs
  have h1 := mul_lt_mul_of_pos_left hlt (pow_pos hsp 2)
  have hs2 := pow_le_pow_left₀ (mul_nonneg hγ2.le ht.le) hs 2
  have h3 : t ^ 2 ≤ s ^ 2 / (γ - 2) ^ 2 := by
    rw [le_div_iff₀ (pow_pos hγ2 2)]; rw [mul_pow] at hs2; linarith [hs2]
  have h2 : 171 * t ^ 2 * N ≤ s ^ 2 * (171 / (γ - 2) ^ 2 * N) := by
    calc 171 * t ^ 2 * N = 171 * N * t ^ 2 := by ring
      _ ≤ 171 * N * (s ^ 2 / (γ - 2) ^ 2) := by gcongr
      _ = s ^ 2 * (171 / (γ - 2) ^ 2 * N) := by ring
  have key' : 19 * (3 * t) ^ 2 * N = 171 * t ^ 2 * N := by ring
  linarith [h1, key, h2, key']

omit [DecidableEq k] [DecidableEq m] in
/-- Lower Gram bound for one tail block of a Gaussian matrix (rows of level `j + 1`). -/
private theorem measureReal_not_gram_tail_le {b : Type*} [Fintype b] [DecidableEq b]
    {G : Ω → Matrix (k ⊕ (Fin 3 × m)) b ℝ} (hG : HasLaw G (gaussianMatrix (k ⊕ (Fin 3 × m)) b) μ)
    (j : Fin 3) {t : ℝ} (ht : 0 ≤ t)
    (htn : t ≤ √(Fintype.card m : ℝ) - √(Fintype.card b : ℝ)) :
    μ.real {ω | ¬ (√(Fintype.card m : ℝ) - √(Fintype.card b : ℝ) - t) ^ 2 • (1 : Matrix b b ℝ) ≤
      ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        (G ω).submatrix (fun i : m => Sum.inr (j, i)) id} ≤ Real.exp (-t ^ 2 / 2) :=
  measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix
    (hasLaw_submatrix_of_hasLaw_gaussianMatrix hG (fun i i' h => by simpa using h)
      Function.injective_id) ht htn

/-- Gaussian head capture of a depth-3 Krylov space: let $\mathbf{G}$ be a standard Gaussian
$n \times b$ matrix, $n = k \oplus (\{0, 1, 2\} \times m)$, $\gamma > 2$, $\lvert k \rvert \le
\lvert b \rvert$ and $\gamma^2\lvert b \rvert \le \lvert m \rvert$. Then
$$\mathbb{P}\Bigl[\exists\,\mathbf{z} \in \mathcal{K}_3(\mathbf{D}, \mathbf{G}):\
\sum_{a \in k} z_a^2 > \frac{171}{(\gamma - 2)^2}\|\mathbf{z}\|^2\Bigr] \le
4\exp\Bigl(-\frac{\lvert m \rvert}{2\gamma^2}\Bigr) \,.$$ -/
theorem measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix
    {b : Type*} [Fintype b] {G : Ω → Matrix (k ⊕ (Fin 3 × m)) b ℝ}
    (hG : HasLaw G (gaussianMatrix (k ⊕ (Fin 3 × m)) b) μ) {γ : ℝ} (hγ : 2 < γ)
    (hkb : Fintype.card k ≤ Fintype.card b) (hbm : γ ^ 2 * Fintype.card b ≤ Fintype.card m) :
    μ.real {ω | ∃ z ∈ blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m 2)) (G ω) 3,
        171 / (γ - 2) ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2} ≤
      4 * Real.exp (-(Fintype.card m / (2 * γ ^ 2))) := by
  classical
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
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
  have hA : μ.real (⋃ j : Fin 3, {ω | ¬ (a - c - t) ^ 2 • (1 : Matrix b b ℝ) ≤
      ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        (G ω).submatrix (fun i : m => Sum.inr (j, i)) id}) ≤ 3 * Real.exp (-t ^ 2 / 2) := by
    refine (measureReal_iUnion_fintype_le _).trans ((Finset.sum_le_sum fun j _ =>
      measureReal_not_gram_tail_le hG j ht0 htn).trans ?_)
    simp
  -- head block: the spectral norm is large with probability at most `exp (-t^2/2)`
  have hB : μ.real {ω | d + c + t ≤ specNorm ((G ω).submatrix Sum.inl id)} ≤
      Real.exp (-t ^ 2 / 2) :=
    measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix
      (hasLaw_submatrix_of_hasLaw_gaussianMatrix hG Sum.inl_injective Function.injective_id) ht0
  refine le_trans (measureReal_mono (s₂ := (⋃ j : Fin 3, {ω | ¬ (a - c - t) ^ 2 •
      (1 : Matrix b b ℝ) ≤ ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        (G ω).submatrix (fun i : m => Sum.inr (j, i)) id}) ∪
      {ω | d + c + t ≤ specNorm ((G ω).submatrix Sum.inl id)}) (fun ω hω => ?_))
    ((measureReal_union_le _ _).trans ?_)
  · obtain ⟨z, hz, hlt⟩ := hω
    by_contra hnot
    have hs : ∀ j : Fin 3, (a - c - t) ^ 2 • (1 : Matrix b b ℝ) ≤
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
    have key := mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace hs hS hz
    have hsum : 0 < ∑ a : k, z (Sum.inl a) ^ 2 := lt_of_le_of_lt (by positivity) hlt
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
    exact false_of_mul_sum_sq_le_of_lt hγ ht_pos hs_lb (sq_nonneg _) key hlt
  · rw [← hexp]
    linarith [hA, hB]

/-- Deterministic error bound: for orthogonal $\mathbf{U}$, if the range of $\mathbf{U}^{\mathsf{H}}
\mathbf{W}$ lies in $\mathcal{K}_3(\mathbf{D}, \mathbf{G})$ and no vector of that space has head
mass above $19/36$ of its squared norm, then $\|\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}} -
\mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \ge 14\lvert m \rvert + \tfrac{33}{10}\lvert k \rvert$. -/
private lemma le_frobNorm_of_orthonormal_range {b : Type*} [Fintype b]
    {U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ}
    {W : Matrix (k ⊕ (Fin 3 × m)) k ℝ} {M : Matrix k (k ⊕ (Fin 3 × m)) ℝ}
    {G : Matrix (k ⊕ (Fin 3 × m)) b ℝ} (hU : HasOrthonormalCols U)
    (hr : LinearMap.range (Uᴴ * W).mulVecLin ≤
      blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m 2)) G 3)
    (hgood : ∀ z ∈ blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m 2)) G 3,
      ¬ (171 / (20 - 2 : ℝ) ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2)) :
    14 * (Fintype.card m : ℝ) + 33 / 10 * Fintype.card k ≤
      frobNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ - W * M) ^ 2 := by
  classical
  set D := Matrix.diagonal (equispacedLevelSpectrum k m 2) with hD
  have hfrob : frobNorm (U * D * Uᴴ - W * M) = frobNorm (D - (Uᴴ * W) * (M * U)) := by
    have hU1 : Uᴴ * U = 1 := hU
    have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU1
    have hUh : HasOrthonormalCols Uᴴ := by
      unfold HasOrthonormalCols
      rw [Matrix.conjTranspose_conjTranspose]
      exact hUU
    have hkey : U * (D - (Uᴴ * W) * (M * U)) * Uᴴ = U * D * Uᴴ - W * M := by
      have h2 : U * (D - (Uᴴ * W) * (M * U)) * Uᴴ
          = U * D * Uᴴ - (U * Uᴴ) * W * (M * (U * Uᴴ)) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      rw [h2, hUU]
      simp only [Matrix.one_mul, Matrix.mul_one]
    rw [← hkey, hUh.frobNorm_mul_right, hU.frobNorm_mul_left]
  have hle := le_frobNorm_diagonal_sub_mul_sq (Uᴴ * W) (M * U)
  have ht : ∑ a : k, ‖WithLp.toLp 2 (rangeProjector (Uᴴ * W) *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2
      ≤ 19 / 36 * Fintype.card k := by
    set P := rangeProjector (Uᴴ * W) with hPdef
    have hP : IsStarProjection P := isStarProjection_rangeProjector _
    have hnorm : ∀ z : k ⊕ (Fin 3 × m) → ℝ, ‖WithLp.toLp 2 z‖ ^ 2 = ∑ i, z i ^ 2 := by
      intro z
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    have hsum := hP.sum_head_mass_sq_le (c := 19 / 36) (by norm_num) (fun a => by
      have hz : P *ᵥ Pi.single (Sum.inl a) 1 ∈ LinearMap.range (Uᴴ * W).mulVecLin := by
        rw [← range_rangeProjector]
        exact ⟨_, rfl⟩
      have h1 := hgood _ (hr hz)
      rw [hnorm, not_lt] at h1
      simp only [Matrix.mulVec_single_one] at h1
      rw [show (171 : ℝ) / (20 - 2) ^ 2 = 19 / 36 by norm_num] at h1
      exact h1)
    simp only [hnorm, Matrix.mulVec_single_one]
    exact hsum
  rw [hfrob]
  linarith [hle, ht, (Nat.cast_nonneg (Fintype.card k) : (0 : ℝ) ≤ Fintype.card k)]

/-- Two-pass Frobenius lower bound for one deterministic algorithm: let $\mathbf{U}$ be Haar,
$\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m,
3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$, and let a measurable algorithm make $q$ queries in at most
two passes to $\mathbf{x} \mapsto (\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$ and
output $\mathbf{W} \in \mathbb{R}^{n \times k}$, $\mathbf{M} \in \mathbb{R}^{k \times n}$. If
$400(q + \lvert k \rvert) \le \lvert m \rvert$, then
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 < 14\lvert m \rvert +
3.3\lvert k \rvert\Bigr] \le 4e^{-\lvert m \rvert/800} \,,$$
and $14\lvert m \rvert = \|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2$. -/
theorem QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame
    {q : ℕ} {alg : QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ)
      ((k ⊕ (Fin 3 × m) → ℝ) × (k ⊕ (Fin 3 × m) → ℝ)) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)} {pass : ℕ → ℕ}
    (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < 2) (halg : alg.IsMeasurable)
    (hm : 400 * (q + Fintype.card k) ≤ Fintype.card m)
    {U : Ω → Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ}
    (hU : HasLaw U (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) μ) :
    μ.real {ω | frobNorm (U ω * Matrix.diagonal (equispacedLevelSpectrum k m 2) * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω) (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).1 *
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).2) ^ 2 <
        14 * Fintype.card m + 33 / 10 * Fintype.card k} ≤
      4 * Real.exp (-(Fintype.card m / 800)) := by
  classical
  have := hU.isProbabilityMeasure
  set D := Matrix.diagonal (equispacedLevelSpectrum k m 2) with hD
  set ν := gaussianMatrix (k ⊕ (Fin 3 × m)) (Fin q ⊕ k) with hν
  have : IsProbabilityMeasure ν := isProbabilityMeasure_gaussianMatrix
  -- extend the space by an independent Gaussian block Z
  have hZ : HasLaw (fun p : Ω × Matrix (k ⊕ (Fin 3 × m)) (Fin q ⊕ k) ℝ => p.2) ν (μ.prod ν) :=
    measurePreserving_snd.hasLaw
  have hUp : HasLaw (fun p : Ω × Matrix (k ⊕ (Fin 3 × m)) (Fin q ⊕ k) ℝ => U p.1)
      (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) (μ.prod ν) :=
    hU.comp (measurePreserving_fst.hasLaw)
  have hUZ : IndepFun (fun p : Ω × Matrix (k ⊕ (Fin 3 × m)) (Fin q ⊕ k) ℝ => U p.1)
      (fun p => p.2) (μ.prod ν) :=
    ProbabilityTheory.indepFun_prod₀ hU.aemeasurable aemeasurable_id
  -- Krylov coupling for the output, with no initial block
  obtain ⟨G, hG⟩ :=
    QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_of_hasLaw_haarFrame
      (alg := alg.mapOutput Prod.fst) (hpass.mapOutput Prod.fst) hp
      (halg.mapOutput measurable_fst) D
      (0 : Matrix (k ⊕ (Fin 3 × m)) (Fin 0) ℝ) hUp hZ hUZ
  have hae : ∀ᵐ p ∂(μ.prod ν), HasOrthonormalCols (U p.1) :=
    (Measure.quasiMeasurePreserving_fst).ae
      (ae_hasOrthonormalCols_of_hasLaw_haarFrame hU (by
        simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; omega))
  have hrange := hG.ae_range_le_of_isEmpty
  simp only [QueryAlgorithm.run_mapOutput] at hrange
  -- Gaussian head capture
  have hkb : Fintype.card k ≤ Fintype.card (Fin q ⊕ k) := by
    rw [Fintype.card_sum, Fintype.card_fin]; omega
  have hbm : (20 : ℝ) ^ 2 * Fintype.card (Fin q ⊕ k) ≤ Fintype.card m := by
    rw [Fintype.card_sum, Fintype.card_fin]
    have h400 : (400 : ℝ) * ((q : ℝ) + Fintype.card k) ≤ Fintype.card m := by
      exact_mod_cast hm
    push_cast
    linarith
  have hL3 := measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix
    hG.hasLaw_gaussianMatrix (γ := 20) (by norm_num) hkb hbm
  have hN : (μ.prod ν).real {p | ¬ (HasOrthonormalCols (U p.1) ∧
      LinearMap.range ((U p.1)ᴴ * (alg.run (hiddenRotationOracle (U p.1) D)).1).mulVecLin ≤
        blockKrylovSpace D (G p) 3)} = 0 := by
    have h0 : (μ.prod ν) {p | ¬ (HasOrthonormalCols (U p.1) ∧
        LinearMap.range ((U p.1)ᴴ * (alg.run (hiddenRotationOracle (U p.1) D)).1).mulVecLin ≤
          blockKrylovSpace D (G p) 3)} = 0 :=
      ae_iff.mp (hae.and hrange)
    rw [measureReal_def, h0]
    simp
  refine (MeasureTheory.measureReal_le_prod_fst ν _).trans ?_
  calc (μ.prod ν).real _ ≤ (μ.prod ν).real
        ({p | ∃ z ∈ blockKrylovSpace D (G p) 3,
          171 / (20 - 2) ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2} ∪
          {p | ¬ (HasOrthonormalCols (U p.1) ∧
            LinearMap.range ((U p.1)ᴴ * (alg.run (hiddenRotationOracle (U p.1) D)).1).mulVecLin ≤
              blockKrylovSpace D (G p) 3)}) := by
        refine measureReal_mono fun p hpS => ?_
        by_cases hgo : HasOrthonormalCols (U p.1) ∧
            LinearMap.range ((U p.1)ᴴ * (alg.run (hiddenRotationOracle (U p.1) D)).1).mulVecLin ≤
              blockKrylovSpace D (G p) 3
        · left
          by_contra hE
          have hb := le_frobNorm_of_orthonormal_range
            (M := (alg.run (hiddenRotationOracle (U p.1) D)).2) hgo.1 hgo.2
            (fun z hz hlt => hE ⟨z, hz, hlt⟩)
          exact (not_lt.mpr hb) hpS
        · exact Or.inr hgo
    _ ≤ (μ.prod ν).real {p | ∃ z ∈ blockKrylovSpace D (G p) 3,
          171 / (20 - 2) ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2} +
        (μ.prod ν).real {p | ¬ (HasOrthonormalCols (U p.1) ∧
            LinearMap.range ((U p.1)ᴴ * (alg.run (hiddenRotationOracle (U p.1) D)).1).mulVecLin ≤
              blockKrylovSpace D (G p) 3)} := measureReal_union_le _ _
    _ = _ := by rw [hN, add_zero]
    _ ≤ 4 * Real.exp (-(Fintype.card m / (2 * 20 ^ 2))) := hL3
    _ = _ := by norm_num

/-- Head mass of a range inside a subspace with small head mass: if every $\mathbf{z} \in S$ has
$\sum_{a \in k} z_a^2 \le c\|\mathbf{z}\|^2$ and the range of $\mathbf{W}$ lies in $S$, then
$\sum_{a \in k}\|\mathbf{P}_{\mathbf{W}}\mathbf{e}_a\|^2 \le c\lvert k \rvert$. -/
private theorem sum_norm_rangeProjector_mulVec_single_sq_le {W : Matrix (k ⊕ (Fin 3 × m)) k ℝ}
    {S : Submodule ℝ (k ⊕ (Fin 3 × m) → ℝ)} {c : ℝ} (hc : 0 ≤ c)
    (hW : LinearMap.range W.mulVecLin ≤ S)
    (hS : ∀ z ∈ S, ∑ a : k, z (Sum.inl a) ^ 2 ≤ c * ‖WithLp.toLp 2 z‖ ^ 2) :
    ∑ a : k, ‖WithLp.toLp 2 (rangeProjector W *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2 ≤
      c * Fintype.card k := by
  set P := rangeProjector W
  have hsymm : ∀ i j, P i j = P j i := fun i j => by
    simpa using congrFun (congrFun (conjTranspose_rangeProjector W) j) i
  have hcol : ∀ j, P.col j ∈ S := fun j => hW <| (range_rangeProjector W) ▸
    ⟨Pi.single j 1, by simp [P]⟩
  calc ∑ a : k, ‖WithLp.toLp 2 (P *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2
      = ∑ i, ∑ a : k, P.col i (Sum.inl a) ^ 2 := by
        simp only [Matrix.mulVec_single_one, EuclideanSpace.norm_toLp_sq_eq_sum_sq,
          Matrix.col_apply]
        rw [Finset.sum_comm]
        simp only [hsymm]
    _ ≤ ∑ i, c * ‖WithLp.toLp 2 (P.col i)‖ ^ 2 := Finset.sum_le_sum fun i _ => hS _ (hcol i)
    _ = c * frobNorm P ^ 2 := by rw [frobNorm_sq_eq_sum_col, Finset.mul_sum]
    _ ≤ c * (P.rank * specNorm P ^ 2) := by gcongr; exact frobNorm_sq_le_rank_mul_specNorm_sq P
    _ ≤ c * (Fintype.card k * 1 ^ 2) := by
        gcongr
        · rw [rank_rangeProjector]; exact_mod_cast W.rank_le_card_width
        · exact (isStarProjection_rangeProjector W).specNorm_le_one
    _ = c * Fintype.card k := by ring

/-- The deterministic step of the spectral two-pass bound: for orthogonal $\mathbf{U}$, if the
range of $\mathbf{U}^{\mathsf{H}}\mathbf{W}$ lies in a subspace whose vectors have head mass at
most $\tfrac{19}{64}\|\mathbf{z}\|^2$, then
$\|\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}} - \mathbf{W}\mathbf{M}\|_2^2 \ge \tfrac{45}{4}$. -/
private theorem le_specNorm_mul_diagonal_mul_sub_mul_sq [Nonempty k]
    {U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ} (hU : HasOrthonormalCols U)
    {W : Matrix (k ⊕ (Fin 3 × m)) k ℝ} {M : Matrix k (k ⊕ (Fin 3 × m)) ℝ}
    {S : Submodule ℝ (k ⊕ (Fin 3 × m) → ℝ)} (hW : LinearMap.range (Uᴴ * W).mulVecLin ≤ S)
    (hS : ∀ z ∈ S, ∑ a : k, z (Sum.inl a) ^ 2 ≤ 19 / 64 * ‖WithLp.toLp 2 z‖ ^ 2) :
    45 / 4 ≤ specNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ - W * M) ^ 2 := by
  have heq : U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ - W * M =
      U * (Matrix.diagonal (equispacedLevelSpectrum k m 2) - (Uᴴ * W) * (M * U)) * Uᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc U (Uᴴ * W), ← Matrix.mul_assoc U Uᴴ,
      hU.mul_conjTranspose_self, Matrix.one_mul, Matrix.mul_assoc W, Matrix.mul_assoc M,
      hU.mul_conjTranspose_self, Matrix.mul_one, Matrix.mul_assoc]
  rw [heq, hU.conjTranspose.specNorm_mul_right, hU.specNorm_mul_left]
  refine le_trans ?_ (le_specNorm_diagonal_sub_mul_sq _ _)
  have ht := sum_norm_rangeProjector_mulVec_single_sq_le (by norm_num) hW hS
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.mpr Fintype.card_pos
  rw [le_div_iff₀ hk]
  nlinarith

/-- Two-pass spectral lower bound for one deterministic algorithm: in the setting of
`NLAlib.QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`
($\mathbf{U}$ Haar, $\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m,
2\mathbf{I}_m, 3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$, a measurable algorithm with $q$ queries in at
most two passes to the hidden-rotation oracle, output $\mathbf{W}\mathbf{M}$ of rank at most
$\lvert k \rvert$), with $k$ nonempty and $676(q + \lvert k \rvert) \le \lvert m \rvert$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_2^2 < \tfrac{45}{4}\Bigr] \le
4e^{-\lvert m \rvert/1352} \,,$$
while $\sigma_{k+1}(\mathbf{A})^2 = 9$: no $(1 + \varepsilon)\sigma_{k+1}$ approximation for
$\varepsilon \le 0.1$. -/
theorem QueryAlgorithm.IsPassStructured.measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame
    [Nonempty k] {q : ℕ} {alg : QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ)
      ((k ⊕ (Fin 3 × m) → ℝ) × (k ⊕ (Fin 3 × m) → ℝ)) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)} {pass : ℕ → ℕ}
    (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < 2) (halg : alg.IsMeasurable)
    (hm : 676 * (q + Fintype.card k) ≤ Fintype.card m)
    {U : Ω → Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ}
    (hU : HasLaw U (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) μ) :
    μ.real {ω | specNorm (U ω * Matrix.diagonal (equispacedLevelSpectrum k m 2) * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω) (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).1 *
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).2) ^ 2 < 45 / 4} ≤
      4 * Real.exp (-(Fintype.card m / 1352)) := by
  have := hU.isProbabilityMeasure
  set D := Matrix.diagonal (equispacedLevelSpectrum k m 2)
  -- extend by an independent Gaussian matrix
  set μ' := μ.prod (gaussianMatrix (k ⊕ (Fin 3 × m)) (Fin q ⊕ k))
  have hU₁ : HasLaw (fun p : Ω × Matrix (k ⊕ (Fin 3 × m)) (Fin q ⊕ k) ℝ => U p.1)
      (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) μ' :=
    hU.comp measurePreserving_fst.hasLaw
  obtain ⟨G, hG⟩ := (hpass.mapOutput Prod.fst).exists_isKrylovCoupling_of_hasLaw_haarFrame
    (p := 2) hp (halg.mapOutput measurable_fst) D (0 : Matrix (k ⊕ (Fin 3 × m)) (Fin 0) ℝ) hU₁
    measurePreserving_snd.hasLaw (indepFun_prod₀ hU.aemeasurable aemeasurable_id)
  have hbad := measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix
    hG.hasLaw_gaussianMatrix (γ := 26) (by norm_num) (by simp) (by
      simp only [Fintype.card_sum, Fintype.card_fin]; push_cast; norm_num; exact_mod_cast hm)
  calc _ = μ'.real (Prod.fst ⁻¹' {ω | specNorm (U ω * D * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω) D)).1 * (alg.run (hiddenRotationOracle (U ω) D)).2)
          ^ 2 < 45 / 4}) := by
        rw [← Set.prod_univ, measureReal_def, measureReal_def, Measure.prod_prod, measure_univ,
          mul_one]
    _ ≤ _ := measureReal_mono_ae ?_
    _ ≤ _ := hbad.trans_eq (by norm_num)
  filter_upwards [hG.ae_range_le_of_isEmpty, ae_hasOrthonormalCols_of_hasLaw_haarFrame hU₁ le_rfl]
    with ω hω hUω hlt
  change specNorm _ ^ 2 < 45 / 4 at hlt
  change ∃ z ∈ _, _ < _
  by_contra hne
  push Not at hne
  rw [QueryAlgorithm.run_mapOutput] at hω
  refine absurd hlt (not_lt.2 (le_specNorm_mul_diagonal_mul_sub_mul_sq hUω hω fun z hz => ?_))
  have := hne z hz
  norm_num at this ⊢
  linarith

/-- Two-pass Frobenius lower bound, randomized worst case: for every randomized algorithm (a
measurable seeded family, seed law $\rho$) making $q$ matrix–vector products in at most two passes
(per seed) with output $\mathbf{W}\mathbf{M}$, $\mathbf{W} \in \mathbb{R}^{n \times k}$, and
$400(q + \lvert k \rvert) \le \lvert m \rvert$, there is an orthogonal $\mathbf{U}$ such that for
$\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m,
3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$
$$\mathbb{P}_s\Bigl[\|\mathbf{A} - \mathbf{W}_s\mathbf{M}_s\|_{\mathsf{F}}^2 \ge
14\lvert m \rvert + 3.3\lvert k \rvert\Bigr] \ge 1 - 4e^{-\lvert m \rvert/800} \,.$$ -/
theorem exists_le_measureReal_frobNorm_sub_mul_sq_ge {q : ℕ}
    (hm : 400 * (q + Fintype.card k) ≤ Fintype.card m) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ] :
    ∃ U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, HasOrthonormalCols U ∧
      1 - 4 * Real.exp (-(Fintype.card m / 800)) ≤
        ρ.real {s | 14 * Fintype.card m + 33 / 10 * Fintype.card k ≤
          frobNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ -
            ((alg s).run (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ).mulVec).1 *
            ((alg s).run (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ).mulVec).2) ^ 2}
    := by
  -- the good set of (input, output) pairs
  let B : Set (Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ ×
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)) :=
    {p | HasOrthonormalCols p.1 ∧ 14 * (Fintype.card m : ℝ) + 33 / 10 * Fintype.card k ≤
      frobNorm (p.1 * Matrix.diagonal (equispacedLevelSpectrum k m 2) * p.1ᴴ -
        p.2.1 * p.2.2) ^ 2}
  have hC : MeasurableSet {Q : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ |
      HasOrthonormalCols Q} :=
    isClosed_setOf_hasOrthonormalCols.measurableSet
  have hF : Measurable fun p : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ ×
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ) =>
      frobNorm (p.1 * Matrix.diagonal (equispacedLevelSpectrum k m 2) * p.1ᴴ -
        p.2.1 * p.2.2) ^ 2 := by
    refine ((measurable_frobNorm).comp ?_).pow_const 2
    fun_prop
  have hB : MeasurableSet B := (measurable_fst hC).inter (measurableSet_le measurable_const hF)
  have hO : Measurable (Function.uncurry fun (U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ)
      (x : k ⊕ (Fin 3 × m) → ℝ) => hiddenRotationOracle U
        (Matrix.diagonal (equispacedLevelSpectrum k m 2)) x) :=
    Measurable.hiddenRotationOracle measurable_fst measurable_snd _
  have hA : QueryAlgorithm.IsMeasurableFamily fun s => (alg s).comapResponse
      (R' := (k ⊕ (Fin 3 × m) → ℝ) × (k ⊕ (Fin 3 × m) → ℝ)) Prod.fst :=
    halg.comapResponse measurable_fst
  have hsucc : ∀ s, 1 - 4 * Real.exp (-(Fintype.card m / 800 : ℝ)) ≤
      (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))).real
        {x | (x, ((alg s).comapResponse Prod.fst).run
          (hiddenRotationOracle x (Matrix.diagonal (equispacedLevelSpectrum k m 2)))) ∈ B} := by
    intro s
    set A' := (alg s).comapResponse (R' := (k ⊕ (Fin 3 × m) → ℝ) × (k ⊕ (Fin 3 × m) → ℝ))
      Prod.fst with hA'
    set D := Matrix.diagonal (equispacedLevelSpectrum k m 2) with hD
    set G := {x : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ |
      (x, A'.run (hiddenRotationOracle x D)) ∈ B} with hG
    set B1 := {x : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ |
      frobNorm (x * D * xᴴ - (A'.run (hiddenRotationOracle x D)).1 *
        (A'.run (hiddenRotationOracle x D)).2) ^ 2 <
        14 * Fintype.card m + 33 / 10 * Fintype.card k} with hB1
    set B2 := {x : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ | ¬HasOrthonormalCols x}
      with hB2
    have h203 : (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))).real B1 ≤
        4 * Real.exp (-(Fintype.card m / 800)) :=
      QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame
        ((hpass s).comapResponse Prod.fst) (hp s)
        ((halg.isMeasurable s).comapResponse measurable_fst) hm
        (HasLaw.id (μ := haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))))
    have hortho : ∀ᵐ x ∂haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)),
        HasOrthonormalCols x :=
      ae_hasOrthonormalCols_of_hasLaw_haarFrame HasLaw.id le_rfl
    have hB20 : (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))).real B2 = 0 := by
      rw [measureReal_def, hB2, ae_iff.1 hortho]
      simp
    have hcover : (Set.univ : Set (Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ)) ⊆
        G ∪ (B1 ∪ B2) := by
      intro x _
      by_cases h1 : HasOrthonormalCols x
      · by_cases h2 : 14 * (Fintype.card m : ℝ) + 33 / 10 * Fintype.card k ≤
            frobNorm (x * D * xᴴ - (A'.run (hiddenRotationOracle x D)).1 *
              (A'.run (hiddenRotationOracle x D)).2) ^ 2
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inl (not_le.1 h2))
      · exact Or.inr (Or.inr h1)
    have h1 := measureReal_mono (μ := haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) hcover
    have h2 := measureReal_union_le (μ := haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) G
      (B1 ∪ B2)
    have h3 := measureReal_union_le (μ := haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) B1 B2
    rw [probReal_univ] at h1
    linarith
  obtain ⟨U, hU⟩ := hA.exists_le_measureReal_run_mem_of_forall (ρ := ρ)
    (ν := haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) hO hB hsucc
  by_cases hUo : HasOrthonormalCols U
  · refine ⟨U, hUo, hU.trans (measureReal_mono fun s hs => ?_)⟩
    have h := hs.2
    rw [QueryAlgorithm.run_comapResponse] at h
    exact h
  · exact ⟨1, hasOrthonormalCols_one, hU.trans (measureReal_mono fun s hs => absurd hs.1 hUo)⟩

omit [DecidableEq k] [DecidableEq m] in
/-- **Two-pass low-rank approximation needs $\Omega(k/\varepsilon)$ matrix–vector products**: let
$k$ be nonempty, $0 < \varepsilon \le \min\{1/6500, \lvert k \rvert/14000\}$ and
$\lvert m \rvert = \lfloor \lvert k \rvert/(8\varepsilon) \rfloor$, so the dimension is
$n = \lvert k \rvert + 3\lvert m \rvert < \lvert k \rvert/(2\varepsilon)$. If a randomized
algorithm (a measurable seeded family, seed law $\rho$) making $q$ matrix–vector products in at
most two passes (per seed) returns $\mathbf{W}\mathbf{M}$ ($\mathbf{W} \in \mathbb{R}^{n \times
k}$) with
$\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2$ with probability at least
$\tfrac12$ for every symmetric $\mathbf{A}$, then
$$q > \frac{\lvert k \rvert}{6400\,\varepsilon} \,.$$
No printed source.

Note: two passes of randomized SVD with $O(k/\varepsilon)$ products achieve this accuracy in
expectation, so the rate $k/\varepsilon$ is optimal for two-pass algorithms. Integer-size form:
`NLAlib.natCast_div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le`.
Result: two-pass-low-rank-lower-bound -/
theorem div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le [Nonempty k] {ε : ℝ} {q : ℕ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 6500) (hεk : ε ≤ Fintype.card k / 14000)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) / (8 * ε)⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, A.IsHermitian →
      1 / 2 ≤ ρ.real {s | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (6400 * ε) < q := by
  classical
  have hk1 : (1 : ℝ) ≤ Fintype.card k := Nat.one_le_cast.mpr Fintype.card_pos
  have hk0 : (0 : ℝ) ≤ Fintype.card k := by positivity
  have hxpos : (0 : ℝ) < (Fintype.card k : ℝ) / (8 * ε) := by positivity
  have hx1750 : (1750 : ℝ) ≤ (Fintype.card k : ℝ) / (8 * ε) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hmx : (Fintype.card k : ℝ) / (8 * ε) - 1 < (Fintype.card m : ℝ) := by
    rw [hm]; exact Nat.sub_one_lt_floor _
  have hm1750 : (1750 : ℝ) ≤ Fintype.card m := by
    rw [hm]
    exact_mod_cast Nat.le_floor (show ((1750 : ℕ) : ℝ) ≤ (Fintype.card k : ℝ) / (8 * ε) by
      exact_mod_cast hx1750)
  by_contra hcon
  replace hcon := not_lt.mp hcon
  have hq : (400 : ℝ) * (q + Fintype.card k) ≤ Fintype.card m := by
    have h1 : (q : ℝ) * (6400 * ε) ≤ Fintype.card k := by
      rwa [le_div_iff₀ (by positivity)] at hcon
    have h2 : (400 : ℝ) * (q + Fintype.card k) * (8 * ε) + 8 * ε ≤ Fintype.card k := by
      nlinarith [mul_le_mul_of_nonneg_left hε₁ hk0]
    have h3 : (400 : ℝ) * (q + Fintype.card k) + 1 ≤ (Fintype.card k : ℝ) / (8 * ε) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hq' : 400 * (q + Fintype.card k) ≤ Fintype.card m := by exact_mod_cast hq
  obtain ⟨U, hU, hfail⟩ := exists_le_measureReal_frobNorm_sub_mul_sq_ge hq' halg hpass hp ρ
  have hexp : (8 : ℝ) < Real.exp (Fintype.card m / 800) := by
    have hy : (2.1875 : ℝ) ≤ Fintype.card m / 800 := by linarith
    have e1 := Real.exp_one_gt_d9
    have e2 := Real.add_one_le_exp (0.1875 : ℝ)
    have e3 : Real.exp 2.1875 = Real.exp 1 * Real.exp 1 * Real.exp 0.1875 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    have e4 := Real.exp_le_exp.mpr hy
    nlinarith [mul_lt_mul'' e1 e1 (by norm_num) (by norm_num)]
  have hinv : Real.exp (-(Fintype.card m / 800)) * Real.exp (Fintype.card m / 800) = 1 := by
    rw [← Real.exp_add]; simp
  have hsmall : 4 * Real.exp (-(Fintype.card m / 800)) < 1 / 2 := by
    nlinarith [mul_pos (Real.exp_pos (-(Fintype.card m / 800 : ℝ))) (sub_pos.mpr hexp)]
  set A := U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ with hA
  have hAherm : A.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose _ (Matrix.isHermitian_diagonal _)
  have hopt : frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2 = 14 * Fintype.card m :=
    HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq hU
  have hsub := hsucc A hAherm
  rw [hopt] at hsub
  have hmle : (Fintype.card m : ℝ) ≤ (Fintype.card k : ℝ) / (8 * ε) := by
    rw [hm]; exact Nat.floor_le hxpos.le
  have hεm : ε * Fintype.card m ≤ (Fintype.card k : ℝ) / 8 := by
    calc ε * Fintype.card m ≤ ε * ((Fintype.card k : ℝ) / (8 * ε)) :=
          mul_le_mul_of_nonneg_left hmle hε.le
      _ = (Fintype.card k : ℝ) / 8 := by field_simp
  have hrun : Measurable fun s => (alg s).run A.mulVec := by
    have hO : Measurable fun p : Matrix (k ⊕ Fin 3 × m) (k ⊕ Fin 3 × m) ℝ ×
        (k ⊕ Fin 3 × m → ℝ) => p.1.mulVec p.2 :=
      (by fun_prop : Continuous fun p : Matrix (k ⊕ Fin 3 × m) (k ⊕ Fin 3 × m) ℝ ×
        (k ⊕ Fin 3 × m → ℝ) => p.1.mulVec p.2).measurable
    exact (halg.measurable_run
      (O := fun B : Matrix (k ⊕ Fin 3 × m) (k ⊕ Fin 3 × m) ℝ => B.mulVec) hO).comp
      (measurable_id.prodMk measurable_const)
  have hmeas : MeasurableSet {s : S | 14 * (Fintype.card m : ℝ) + 33 / 10 * Fintype.card k ≤
      frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2} := by
    refine measurableSet_le measurable_const ?_
    refine Measurable.pow_const ?_ 2
    refine measurable_frobNorm.comp (Measurable.sub measurable_const ?_)
    exact (measurable_fst.comp hrun).matrix_mul (measurable_snd.comp hrun)
  have hsubset : {s : S | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
      (1 + ε) * (14 * (Fintype.card m : ℝ))} ⊆
      {s : S | 14 * (Fintype.card m : ℝ) + 33 / 10 * Fintype.card k ≤
        frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2}ᶜ := by
    intro s hs hc
    simp only [Set.mem_ofPred_eq] at hs hc
    nlinarith
  have hcompl := MeasureTheory.probReal_compl_eq_one_sub (μ := ρ) hmeas
  have hmono := MeasureTheory.measureReal_mono (μ := ρ) hsubset
  linarith

/-- **Two-pass low-rank approximation needs $\Omega(k/\varepsilon)$ matrix–vector products**,
integer sizes: let $k$, $m$ and $q$ be natural numbers and $n = k + 3m$, with
$0 < \varepsilon \le \varepsilon_0$, $\varepsilon \le k/C_1$ and
$m = \lfloor k/(8\varepsilon) \rfloor$. Let $(\mathcal{A}_s)$ be a randomized algorithm, that is,
a measurable family of algorithms with seed $s$ drawn from a probability measure $\rho$, where
every $\mathcal{A}_s$ makes $q$ matrix–vector products with its input $\mathbf{A}$ in at most two
passes (the products of a pass are chosen before any response of that pass is seen) and returns
$\mathbf{W} \in \mathbb{R}^{n \times k}$ and $\mathbf{M} \in \mathbb{R}^{k \times n}$. If for
every symmetric $\mathbf{A} \in \mathbb{R}^{n \times n}$
$$\mathbb{P}_{s \sim \rho}\bigl[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2\bigr]
\ge \frac{1}{2} \,,$$
then
$$q > \frac{k}{C\varepsilon} \,.$$
Here $C = 6400$, $\varepsilon_0 = 1/6500$ and $C_1 = 14000$.
No printed source.

Note: the hypotheses force $k \ge 1$. The $n$ coordinates are indexed by
`Fin k ⊕ (Fin 3 × Fin m)`: a head of $k$ coordinates and three tail levels of $m$ each. General
form, with finite index types in place of $k$ and $m$:
`NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le`. Two passes of randomized SVD
with $O(k/\varepsilon)$ products achieve this accuracy in expectation, so the rate
$k/\varepsilon$ is optimal for two-pass algorithms.
Result: two-pass-low-rank-lower-bound -/
theorem natCast_div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le {k m q : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 6500) (hεk : ε ≤ k / 14000)
    (hm : m = ⌊(k : ℝ) / (8 * ε)⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (Fin k ⊕ (Fin 3 × Fin m) → ℝ) (Fin k ⊕ (Fin 3 × Fin m) → ℝ) q
      (Matrix (Fin k ⊕ (Fin 3 × Fin m)) (Fin k) ℝ × Matrix (Fin k) (Fin k ⊕ (Fin 3 × Fin m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (Fin k ⊕ (Fin 3 × Fin m)) (Fin k ⊕ (Fin 3 × Fin m)) ℝ,
      A.IsHermitian →
      1 / 2 ≤ ρ.real {s | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2}) :
    (k : ℝ) / (6400 * ε) < q := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.cast_zero, zero_div] at hεk
    exact absurd hε (not_lt.mpr hεk)
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h := div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le (k := Fin k) (m := Fin m)
    (ε := ε) (alg := alg)
  simp only [Fintype.card_fin] at h
  exact h hε hε₁ hεk hm halg hpass hp ρ hsucc

omit [DecidableEq k] [DecidableEq m] in
/-- **One-pass low-rank approximation needs $\Omega(k/\varepsilon)$ matrix–vector products**: for
algorithms whose products are all chosen in advance (one pass), with $k$ nonempty,
$0 < \varepsilon \le \min\{1/6500, \lvert k \rvert/14000\}$ and
$\lvert m \rvert = \lfloor \lvert k \rvert/(8\varepsilon) \rfloor$, an algorithm that is within
$(1 + \varepsilon)$ of the best rank-$k$ Frobenius error with probability at least $\tfrac12$ on
every symmetric input makes $q > \lvert k \rvert/(6400\varepsilon)$ products.
No printed source.

Note: this is `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le` restricted to one
pass. Truncated generalized Nyström attains the error in expectation with $O(k/\varepsilon)$
one-pass products (`LowRank/Gaussian/TruncatedGeneralizedNystromRate`), so the bound is tight up
to constants. Integer-size form:
`NLAlib.natCast_div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one`.
Result: one-pass-low-rank-lower-bound -/
theorem div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one [Nonempty k] {ε : ℝ}
    {q : ℕ} (hε : 0 < ε) (hε₁ : ε ≤ 1 / 6500) (hεk : ε ≤ Fintype.card k / 14000)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) / (8 * ε)⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 1)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, A.IsHermitian →
      1 / 2 ≤ ρ.real {s | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (6400 * ε) < q :=
  div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le hε hε₁ hεk hm halg hpass
    (fun s i hi => (hp s i hi).trans one_lt_two) ρ hsucc

/-- **One-pass low-rank approximation needs $\Omega(k/\varepsilon)$ matrix–vector products**,
integer sizes: let $k$, $m$ and $q$ be natural numbers and $n = k + 3m$, with
$0 < \varepsilon \le \varepsilon_0$, $\varepsilon \le k/C_1$ and
$m = \lfloor k/(8\varepsilon) \rfloor$. Let $(\mathcal{A}_s)$ be a randomized algorithm, that is,
a measurable family of algorithms with seed $s$ drawn from a probability measure $\rho$, where
every $\mathcal{A}_s$ makes $q$ matrix–vector products with its input $\mathbf{A}$ in one pass
(all products are chosen before any response is seen) and returns
$\mathbf{W} \in \mathbb{R}^{n \times k}$ and $\mathbf{M} \in \mathbb{R}^{k \times n}$. If for
every symmetric $\mathbf{A} \in \mathbb{R}^{n \times n}$
$$\mathbb{P}_{s \sim \rho}\bigl[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2\bigr]
\ge \frac{1}{2} \,,$$
then
$$q > \frac{k}{C\varepsilon} \,.$$
Here $C = 6400$, $\varepsilon_0 = 1/6500$ and $C_1 = 14000$.
No printed source.

Note: the hypotheses force $k \ge 1$. The $n$ coordinates are indexed by
`Fin k ⊕ (Fin 3 × Fin m)`: a head of $k$ coordinates and three tail levels of $m$ each. General
form, with finite index types in place of $k$ and $m$:
`NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one`. Truncated generalized
Nyström attains the error in expectation with $O(k/\varepsilon)$ one-pass products
(`LowRank/Gaussian/TruncatedGeneralizedNystromRate`), so the bound is tight up to constants.
Result: one-pass-low-rank-lower-bound -/
theorem natCast_div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one {k m q : ℕ}
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1 / 6500) (hεk : ε ≤ k / 14000)
    (hm : m = ⌊(k : ℝ) / (8 * ε)⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (Fin k ⊕ (Fin 3 × Fin m) → ℝ) (Fin k ⊕ (Fin 3 × Fin m) → ℝ) q
      (Matrix (Fin k ⊕ (Fin 3 × Fin m)) (Fin k) ℝ × Matrix (Fin k) (Fin k ⊕ (Fin 3 × Fin m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 1)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (Fin k ⊕ (Fin 3 × Fin m)) (Fin k ⊕ (Fin 3 × Fin m)) ℝ,
      A.IsHermitian →
      1 / 2 ≤ ρ.real {s | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2}) :
    (k : ℝ) / (6400 * ε) < q := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by
    rw [h, Nat.cast_zero, zero_div] at hεk
    exact absurd hε (not_lt.mpr hεk)
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h := div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one (k := Fin k)
    (m := Fin m) (ε := ε) (alg := alg)
  simp only [Fintype.card_fin] at h
  exact h hε hε₁ hεk hm halg hpass hp ρ hsucc

omit [DecidableEq k] [DecidableEq m] in
/-- Two-pass spectral low-rank approximation needs products proportional to the dimension:
let $k$ be nonempty, $\lvert m \rvert \ge 2812$ and $0 \le \varepsilon \le 1/10$. If a randomized
algorithm (a measurable seeded family, seed law $\rho$) making $q$ matrix–vector products in at
most two passes (per seed) returns $\mathbf{W}\mathbf{M}$ ($\mathbf{W} \in \mathbb{R}^{n \times
k}$) with $\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_2 \le (1 + \varepsilon)\sigma_{k+1}(\mathbf{A})$
with probability at least $\tfrac12$ for every symmetric $\mathbf{A} \in \mathbb{R}^{n \times n}$,
$n = \lvert k \rvert + 3\lvert m \rvert$, then
$$\lvert m \rvert < 676\,(q + \lvert k \rvert) \,,$$
i.e. $q > (n - \lvert k \rvert)/2028 - \lvert k \rvert$, whatever $\varepsilon \le 0.1$. -/
theorem lt_of_forall_le_measureReal_specNorm_sub_mul_le [Nonempty k] {ε : ℝ} {q : ℕ}
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1 / 10) (hm : 2812 ≤ Fintype.card m) {S : Type*}
    [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, A.IsHermitian →
      1 / 2 ≤ ρ.real {s | specNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ≤
        (1 + ε) * singularValues A (Fintype.card k)}) :
    Fintype.card m < 676 * (q + Fintype.card k) := by
  classical
  by_contra hcon
  replace hcon := not_lt.mp hcon
  set D := Matrix.diagonal (equispacedLevelSpectrum k m 2)
  set δ : ℝ := 1 - 4 * Real.exp (-(Fintype.card m / 1352))
  have hO : Measurable (Function.uncurry fun (U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ)
      (x : k ⊕ (Fin 3 × m) → ℝ) => (U * D * Uᴴ) *ᵥ x) :=
    (Measurable.hiddenRotationOracle measurable_fst measurable_snd D).fst
  set B : Set (Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ ×
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)) :=
    {p | HasOrthonormalCols p.1 ∧ 45 / 4 ≤ specNorm (p.1 * D * p.1ᴴ - p.2.1 * p.2.2) ^ 2}
  have hB : MeasurableSet B :=
    (isClosed_setOf_hasOrthonormalCols.measurableSet.preimage measurable_fst).inter
      (measurableSet_le measurable_const ((measurable_specNorm.comp
        (((measurable_fst.matrix_mul measurable_const).matrix_mul
          (continuous_star.measurable.matrix_conjTranspose measurable_fst)).matrix_sub
          (measurable_snd.fst.matrix_mul measurable_snd.snd))).pow_const 2))
  have hfail : ∀ s, δ ≤ (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))).real
      {U | (U, (alg s).run ((U * D * Uᴴ) *ᵥ ·)) ∈ B} := by
    intro s
    set ν := haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))
    have hL :=
      QueryAlgorithm.IsPassStructured.measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame
      ((hpass s).comapResponse Prod.fst) (hp s) ((halg.isMeasurable s).comapResponse measurable_fst)
      hcon (U := id) HasLaw.id
    simp only [QueryAlgorithm.run_comapResponse] at hL
    have hNO : ν.real {U | ¬HasOrthonormalCols U} = 0 := by
      have h := ae_iff.mp (ae_hasOrthonormalCols_of_hasLaw_haarFrame (HasLaw.id (μ := ν)) le_rfl)
      exact (congrArg ENNReal.toReal h).trans ENNReal.toReal_zero
    have hT : MeasurableSet {U | (U, (alg s).run ((U * D * Uᴴ) *ᵥ ·)) ∈ B} :=
      hB.preimage (measurable_id.prodMk ((halg.measurable_run hO).comp measurable_prodMk_left))
    have hsub : {U | (U, (alg s).run ((U * D * Uᴴ) *ᵥ ·)) ∈ B}ᶜ ⊆
        {ω | specNorm (id ω * D * (id ω)ᴴ -
          ((alg s).run (Prod.fst ∘ hiddenRotationOracle (id ω) D)).1 *
          ((alg s).run (Prod.fst ∘ hiddenRotationOracle (id ω) D)).2) ^ 2 < 45 / 4} ∪
        {U | ¬HasOrthonormalCols U} := by
      intro U hU
      by_cases hUo : HasOrthonormalCols U
      · exact Or.inl (lt_of_not_ge fun h => hU ⟨hUo, h⟩)
      · exact Or.inr hUo
    have := (measureReal_mono (μ := ν) hsub).trans (measureReal_union_le _ _)
    rw [probReal_compl_eq_one_sub hT] at this
    linarith
  obtain ⟨U, hU⟩ := halg.exists_le_measureReal_run_mem_of_forall hO ρ _ hB hfail
  have hA : (U * D * Uᴴ).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose U (Matrix.isHermitian_diagonal _)
  set succ := {s | specNorm (U * D * Uᴴ - ((alg s).run (U * D * Uᴴ).mulVec).1 *
      ((alg s).run (U * D * Uᴴ).mulVec).2) ≤
      (1 + ε) * singularValues (U * D * Uᴴ) (Fintype.card k)}
  have hsucc' : 1 / 2 ≤ ρ.real succ := hsucc _ hA
  have hmeas : MeasurableSet succ := by
    have hf : Measurable fun s => (alg s).run (U * D * Uᴴ).mulVec :=
      (halg.measurable_run (O := fun (_ : Unit) => (U * D * Uᴴ).mulVec)
        (measurable_const.matrix_mulVec measurable_snd)).comp
        (measurable_id.prodMk (measurable_const (a := ())))
    exact measurableSet_le (measurable_specNorm.comp
      (measurable_const.matrix_sub (hf.fst.matrix_mul hf.snd))) measurable_const
  have hsub : {s | (U, (alg s).run ((U * D * Uᴴ) *ᵥ ·)) ∈ B} ⊆ succᶜ := by
    rintro s ⟨hUo, hs⟩ h
    have : Nonempty m := Fintype.card_pos_iff.mp (by omega)
    have h3 : singularValues (U * D * Uᴴ) (Fintype.card k) = 3 :=
      HasOrthonormalCols.singularValues_mul_diagonal_mul_card hUo
    set E := U * D * Uᴴ - ((alg s).run (U * D * Uᴴ).mulVec).1 *
      ((alg s).run (U * D * Uᴴ).mulVec).2
    replace h : specNorm E ≤ (1 + ε) * 3 := h3 ▸ h
    replace hs : 45 / 4 ≤ specNorm E ^ 2 := hs
    nlinarith [specNorm_nonneg E]
  have hexp : Real.exp (-(Fintype.card m / 1352)) < 1 / 8 := by
    have hm' : (2812 : ℝ) ≤ Fintype.card m := by exact_mod_cast hm
    calc Real.exp (-(Fintype.card m / 1352)) ≤ Real.exp (-(2812 / 1352)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ < 1 / 8 := by
          rw [← Real.exp_log (by norm_num : (0:ℝ) < 1 / 8), one_div, Real.log_inv,
            show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
          exact Real.exp_lt_exp.mpr (by push_cast; linarith [Real.log_two_lt_d9])
  have := (hU.trans (measureReal_mono hsub)).trans_eq (probReal_compl_eq_one_sub hmeas)
  linarith

end NLAlib
