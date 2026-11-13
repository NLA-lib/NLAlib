/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CG
public import NLAlib.Krylov.LinearSystems.MINRES
public import NLAlib.Polynomial.Chebyshev.ResidualMinimax
public import NLAlib.ForMathlib.Algebra.Polynomial.Expand

/-!
# Spectra on which the Chebyshev bounds are attained

For every $q$ and $0 < a < a'$ there are a positive definite matrix with spectrum in $[a, a']$
and a right-hand side for which the CG error and the MINRES residual after $q$ steps are exactly
$T_q\bigl((a' + a)/(a' - a)\bigr)^{-1} = 2\rho^q/(1 + \rho^{2q})$ times their initial
values, $\rho = (\sqrt{a'/a} - 1)/(\sqrt{a'/a} + 1)$. So the bounds $2\rho^q$ (and $4\rho^{2q}$
squared) of `NLAlib.Krylov.LinearSystems.CG` and `NLAlib.Krylov.LinearSystems.MINRES` are tight
up to the factor $1 + \rho^{2q}$ (squared: $(1 + \rho^{2q})^2$), which tends to $1$.

The matrix is diagonal with the $q + 1$ Chebyshev extrema $\xi_0 < \dots < \xi_q$ of $[a, a']$
(`NLAlib.chebyshevExtremum`), and the right-hand side carries the dual weights
$\omega_k = \lvert\ell_k(0)\rvert$ (`NLAlib.chebyshevWeight`): for these weights the weighted
least-squares problem over residual polynomials, which CG and MINRES solve, has the Chebyshev
minimax polynomial as its solution. Reflecting the extrema of $[a^2, a'^2]$ through
$\pm\sqrt{\cdot}$
gives the same for MINRES on $[-a', -a] \cup [a, a']$ at the rate of
`Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_pow_div_two`.

On every spectrum (Greenbaum's theorem): for every positive definite $\mathbf{A}$ and start
some right-hand side makes the CG error exactly `NLAlib.residualMinimax` of the spectrum times
the initial error, and for every Hermitian $\mathbf{A}$ the same holds for the MINRES residual.
So the spectrum-optimal bounds
`Matrix.PosDef.re_quadForm_sub_cgIterate_le_residualMinimax_sq_mul` and
`Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_residualMinimax_mul` are the worst cases.
The right-hand side carries the dual weights of the minimax problem on the spectrum
(`NLAlib.exists_residualMinimax_sq_le_sum_mul_norm_sq`) as its spectral weights.

## Main definitions

* `NLAlib.chebyshevExtremaMatrix`, `NLAlib.chebyshevErrorVector`, `NLAlib.chebyshevWeightVector`.
* `NLAlib.chebyshevTwoIntervalMatrix`, `NLAlib.chebyshevTwoIntervalVector`.

## Main results

* `NLAlib.re_quadForm_sub_cgIterate_chebyshevExtremaMatrix`: CG attains the Chebyshev value.
* `NLAlib.re_quadForm_sub_cgIterate_chebyshevExtremaMatrix_eq_four_mul_pow_div`: in $\rho$.
* `NLAlib.norm_sub_mulVec_gmresIterate_chebyshevExtremaMatrix`: so does MINRES.
* `NLAlib.norm_sub_mulVec_gmresIterate_chebyshevTwoIntervalMatrix`: two symmetric intervals.
* `Matrix.PosDef.exists_re_quadForm_sub_cgIterate_eq_residualMinimax_sq_mul`,
  `Matrix.PosDef.isGreatest_re_quadForm_sub_cgIterate_div`: Greenbaum's theorem for CG.
* `Matrix.IsHermitian.exists_norm_sub_mulVec_gmresIterate_eq_residualMinimax_mul`,
  `Matrix.IsHermitian.isGreatest_norm_sub_mulVec_gmresIterate_div`: the same for MINRES.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial Polynomial.Chebyshev

namespace NLAlib

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The **Chebyshev extrema matrix**: diagonal with the $q + 1$ Chebyshev extrema of $[a, a']$. -/
noncomputable def chebyshevExtremaMatrix (a a' : ℝ) (q : ℕ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) 𝕜 :=
  Matrix.diagonal fun k => (chebyshevExtremum a a' q k : 𝕜)

/-- The CG worst-case initial error: entries $\sqrt{\omega_k/\xi_k}$, so that its
$\mathbf{A}$-norm weights are the dual weights. -/
noncomputable def chebyshevErrorVector (a a' : ℝ) (q : ℕ) : Fin (q + 1) → 𝕜 :=
  fun k => (Real.sqrt (chebyshevWeight a a' q k / chebyshevExtremum a a' q k) : 𝕜)

/-- The MINRES worst-case right-hand side: entries $\sqrt{\omega_k}$. -/
noncomputable def chebyshevWeightVector (a a' : ℝ) (q : ℕ) : Fin (q + 1) → 𝕜 :=
  fun k => (Real.sqrt (chebyshevWeight a a' q k) : 𝕜)

/-- The **symmetric two-interval matrix**: diagonal with $\pm\sqrt{\xi_j}$ for the $k + 1$
Chebyshev extrema $\xi_j$ of $[a^2, a'^2]$. -/
noncomputable def chebyshevTwoIntervalMatrix (a a' : ℝ) (k : ℕ) :
    Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) 𝕜 :=
  Matrix.diagonal fun i => Sum.elim
    (fun j : Fin (k + 1) => (Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) k j) : 𝕜))
    (fun j : Fin (k + 1) => (-Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) k j) : 𝕜)) i

/-- The two-interval right-hand side: $\sqrt{\omega_j/2}$ on both copies. -/
noncomputable def chebyshevTwoIntervalVector (a a' : ℝ) (k : ℕ) :
    Fin (k + 1) ⊕ Fin (k + 1) → 𝕜 :=
  fun i => Sum.elim (fun j => (Real.sqrt (chebyshevWeight (a ^ 2) (a' ^ 2) k j / 2) : 𝕜))
    (fun j => (Real.sqrt (chebyshevWeight (a ^ 2) (a' ^ 2) k j / 2) : 𝕜)) i

variable {𝕜}

/-- The Chebyshev extrema matrix is positive definite for $0 < a \le a'$. -/
theorem posDef_chebyshevExtremaMatrix {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a') (q : ℕ) :
    (chebyshevExtremaMatrix 𝕜 a a' q).PosDef := by
  rw [chebyshevExtremaMatrix, Matrix.posDef_diagonal_iff]
  exact fun k => RCLike.ofReal_pos.mpr (ha.trans_le (chebyshevExtremum_mem_Icc haa q k).1)

/-- Its spectrum lies in $[a, a']$. -/
theorem spectrum_chebyshevExtremaMatrix_subset_Icc {a a' : ℝ} (haa : a ≤ a') (q : ℕ) :
    spectrum ℝ (chebyshevExtremaMatrix 𝕜 a a' q) ⊆ Set.Icc a a' := by
  rw [← spectrum.preimage_algebraMap 𝕜, chebyshevExtremaMatrix, spectrum_diagonal]
  rintro r ⟨k, hk⟩
  rw [RCLike.algebraMap_eq_ofReal, RCLike.ofReal_inj] at hk
  exact hk ▸ chebyshevExtremum_mem_Icc haa q k

/-- The $\mathbf{A}$-norm on the Chebyshev extrema matrix: $\sum_k \xi_k \lvert z_k \rvert^2$. -/
private lemma re_quadForm_chebyshevExtremaMatrix (a a' : ℝ) (q : ℕ) (z : Fin (q + 1) → 𝕜) :
    RCLike.re (quadForm (chebyshevExtremaMatrix 𝕜 a a' q) z) =
      ∑ k : Fin (q + 1), chebyshevExtremum a a' q k * ‖z k‖ ^ 2 := by
  rw [chebyshevExtremaMatrix, quadForm_diagonal, map_sum]
  simp only [← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- The squared $\mathbf{A}$-norm of `chebyshevErrorVector` scaled entrywise by $f$ is
$\sum_k\omega_k\lvert f_k \rvert^2$. -/
private lemma re_quadForm_chebyshevErrorVector {a a' : ℝ} (ha : 0 < a) (haa : a < a') (q : ℕ)
    (f : Fin (q + 1) → 𝕜) :
    RCLike.re (quadForm (chebyshevExtremaMatrix 𝕜 a a' q)
        (fun k => f k * chebyshevErrorVector 𝕜 a a' q k)) =
      ∑ k : Fin (q + 1), chebyshevWeight a a' q k * ‖f k‖ ^ 2 := by
  rw [re_quadForm_chebyshevExtremaMatrix]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hξ : 0 < chebyshevExtremum a a' q k :=
    ha.trans_le (chebyshevExtremum_mem_Icc haa.le q k).1
  have hω := (chebyshevWeight_pos ha haa q k).le
  rw [norm_mul, mul_pow, chebyshevErrorVector, RCLike.norm_ofReal,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (div_nonneg hω hξ.le)]
  field_simp

/-- **CG attains the Chebyshev value**: for $0 < a < a'$, on the Chebyshev extrema matrix
$\mathbf{A}$ with solution $\mathbf{x}_\star$ = `chebyshevErrorVector` and the zero start,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{A}\mathbf{x}_\star, \mathbf{0},
q)\|_{\mathbf{A}}^2
= T_q\Bigl(\frac{a' + a}{a' - a}\Bigr)^{-2}\|\mathbf{x}_\star\|_{\mathbf{A}}^2 \,.$$
The error is $p(\mathbf{A})\mathbf{x}_\star$ for a residual polynomial $p$, of squared
$\mathbf{A}$-norm $\sum_k\omega_k\lvert p(\xi_k)\rvert^2 \ge 1/\sum_k\omega_k$ by Cauchy–Schwarz
against $\sum_k(-1)^k\omega_k p(\xi_k) = 1$; `chebyshevResidual` attains it.
[Greenbaum1997, §3.1, pp. 51–52].
Result: cg-chebyshev-sharp -/
theorem re_quadForm_sub_cgIterate_chebyshevExtremaMatrix {a a' : ℝ} (ha : 0 < a) (haa : a < a')
    (q : ℕ) :
    RCLike.re (quadForm (chebyshevExtremaMatrix 𝕜 a a' q) (chebyshevErrorVector 𝕜 a a' q -
        cgIterate (chebyshevExtremaMatrix 𝕜 a a' q)
          (chebyshevExtremaMatrix 𝕜 a a' q *ᵥ chebyshevErrorVector 𝕜 a a' q) 0 q)) =
      ((T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)))⁻¹ ^ 2 *
        RCLike.re (quadForm (chebyshevExtremaMatrix 𝕜 a a' q) (chebyshevErrorVector 𝕜 a a' q)) := by
  set A := chebyshevExtremaMatrix 𝕜 a a' q
  set e := chebyshevErrorVector 𝕜 a a' q
  set τ := (T ℝ (q : ℤ)).eval ((a' + a) / (a' - a))
  have hτ : 0 < τ := zero_lt_one.trans_le (one_le_eval_T_real (q : ℤ) (by
    rw [le_div_iff₀ (by linarith)]
    linarith))
  have hA := posDef_chebyshevExtremaMatrix (𝕜 := 𝕜) ha haa.le q
  have he : RCLike.re (quadForm A e) = τ := by
    have h := re_quadForm_chebyshevErrorVector ha haa q (fun _ => (1 : 𝕜))
    simp only [one_mul, norm_one, one_pow, mul_one] at h
    exact h.trans (sum_chebyshevWeight ha haa q)
  rw [he, inv_pow, sq, mul_inv, mul_assoc, inv_mul_cancel₀ hτ.ne', mul_one]
  refine le_antisymm ?_ ?_
  · -- the Chebyshev residual attains the value
    have h := hA.re_quadForm_sub_cgIterate_le (spectrum_chebyshevExtremaMatrix_subset_Icc haa.le q)
      (rfl : A *ᵥ e = A *ᵥ e) 0 (degree_chebyshevResidual_le a a' q)
      (eval_chebyshevResidual_zero q ha haa) (η := τ⁻¹) fun x hx => by
        have h := isUniformApproxOn_chebyshevResidual q ha haa x hx
        rwa [Real.dist_eq, sub_zero] at h
    rwa [sub_zero, he, inv_pow, sq, mul_inv, mul_assoc, inv_mul_cancel₀ hτ.ne', mul_one] at h
  · -- every residual polynomial does at least as badly
    obtain ⟨p, hp, hp₀, hpe⟩ := exists_sub_cgIterate_eq_aeval (rfl : A *ᵥ e = A *ᵥ e) 0 q
    have hpA : aeval A p =
        Matrix.diagonal (fun k : Fin (q + 1) => p.eval (chebyshevExtremum a a' q k : 𝕜)) :=
      aeval_diagonal_self _ p
    rw [hpe, sub_zero, hpA]
    have hv : Matrix.diagonal (fun k : Fin (q + 1) => p.eval (chebyshevExtremum a a' q k : 𝕜))
        *ᵥ e = fun k : Fin (q + 1) => p.eval (chebyshevExtremum a a' q k : 𝕜) * e k := by
      ext k
      rw [Matrix.mulVec_diagonal]
    rw [hv, re_quadForm_chebyshevErrorVector ha haa q]
    exact inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq ha haa hp hp₀

/-- **The CG bound is tight up to $(1 + \rho^{2q})^2$**: for $0 < a < a'$, on the Chebyshev
extrema matrix $\mathbf{A}$ (`chebyshevExtremaMatrix`) with solution $\mathbf{x}_\star$ =
`chebyshevErrorVector` and the zero start, with $\rho = (\sqrt{a'/a} - 1)/(\sqrt{a'/a} + 1)$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{A}\mathbf{x}_\star, \mathbf{0},
q)\|_{\mathbf{A}}^2 = \frac{4\rho^{2q}}{(1 + \rho^{2q})^2}\|\mathbf{x}_\star\|_{\mathbf{A}}^2 \,,$$
against the bound $4\rho^{2q}$ of
`Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow`.
Result: cg-chebyshev-sharp -/
theorem re_quadForm_sub_cgIterate_chebyshevExtremaMatrix_eq_four_mul_pow_div {a a' : ℝ}
    (ha : 0 < a) (haa : a < a') (q : ℕ) :
    RCLike.re (quadForm (chebyshevExtremaMatrix 𝕜 a a' q) (chebyshevErrorVector 𝕜 a a' q -
        cgIterate (chebyshevExtremaMatrix 𝕜 a a' q)
          (chebyshevExtremaMatrix 𝕜 a a' q *ᵥ chebyshevErrorVector 𝕜 a a' q) 0 q)) =
      4 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * q) /
          (1 + ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * q)) ^ 2 *
        RCLike.re (quadForm (chebyshevExtremaMatrix 𝕜 a a' q) (chebyshevErrorVector 𝕜 a a' q)) := by
  rw [re_quadForm_sub_cgIterate_chebyshevExtremaMatrix ha haa,
    inv_eval_T_real_eq_two_mul_pow_div q ha haa, div_pow, mul_pow, ← pow_mul, mul_comm q 2]
  norm_num

/-- **MINRES attains the Chebyshev value**: for $0 < a < a'$, on the Chebyshev extrema matrix
with right-hand side $\mathbf{w}$ = `chebyshevWeightVector` and the zero start,
$$\|\mathbf{w} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{w}, \mathbf{0}, q)\| =
T_q\Bigl(\frac{a' + a}{a' - a}\Bigr)^{-1}\|\mathbf{w}\| = \frac{2\rho^q}{1 +
\rho^{2q}}\|\mathbf{w}\| \,.$$
As for CG, with residual weights $\lvert\mathbf{w}_k\rvert^2 = \omega_k$.
[Greenbaum1997, §3.1, pp. 51–52].
Result: minres-chebyshev-sharp -/
theorem norm_sub_mulVec_gmresIterate_chebyshevExtremaMatrix {a a' : ℝ} (ha : 0 < a)
    (haa : a < a') (q : ℕ) :
    ‖WithLp.toLp 2 (chebyshevWeightVector 𝕜 a a' q - chebyshevExtremaMatrix 𝕜 a a' q *ᵥ
        gmresIterate (chebyshevExtremaMatrix 𝕜 a a' q) (chebyshevWeightVector 𝕜 a a' q) 0 q)‖ =
      ((T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)))⁻¹ *
        ‖WithLp.toLp 2 (chebyshevWeightVector 𝕜 a a' q)‖ := by
  set A := chebyshevExtremaMatrix 𝕜 a a' q
  set w := chebyshevWeightVector 𝕜 a a' q
  set τ := (T ℝ (q : ℤ)).eval ((a' + a) / (a' - a))
  have hτ : 0 < τ := zero_lt_one.trans_le (one_le_eval_T_real (q : ℤ) (by
    rw [le_div_iff₀ (by linarith)]
    linarith))
  have hA := posDef_chebyshevExtremaMatrix (𝕜 := 𝕜) ha haa.le q
  have hnorm : ∀ f : Fin (q + 1) → 𝕜, ‖WithLp.toLp 2 (fun k => f k * w k)‖ ^ 2 =
      ∑ k, chebyshevWeight a a' q k * ‖f k‖ ^ 2 := fun f => by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [w, chebyshevWeightVector]
    rw [norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs,
      Real.sq_sqrt (chebyshevWeight_pos ha haa q k).le, mul_comm]
  have hw : ‖WithLp.toLp 2 w‖ ^ 2 = τ := by
    have h := hnorm fun _ => 1
    simp only [one_mul, norm_one, one_pow, mul_one] at h
    exact h.trans (sum_chebyshevWeight ha haa q)
  refine le_antisymm ?_ ?_
  · have h := hA.isHermitian.norm_sub_mulVec_gmresIterate_le
      (spectrum_chebyshevExtremaMatrix_subset_Icc haa.le q) w 0 (degree_chebyshevResidual_le a a' q)
      (eval_chebyshevResidual_zero q ha haa) (η := τ⁻¹) fun x hx => by
        have h := isUniformApproxOn_chebyshevResidual q ha haa x hx
        rwa [Real.dist_eq, sub_zero] at h
    rwa [Matrix.mulVec_zero, sub_zero] at h
  · obtain ⟨p, hp, hp₀, hpe⟩ := exists_sub_mulVec_gmresIterate_eq_aeval A w 0 q
    rw [Matrix.mulVec_zero, sub_zero] at hpe
    have hpA : aeval A p =
        Matrix.diagonal (fun k : Fin (q + 1) => p.eval (chebyshevExtremum a a' q k : 𝕜)) :=
      aeval_diagonal_self _ p
    have hv : aeval A p *ᵥ w =
        fun k : Fin (q + 1) => p.eval (chebyshevExtremum a a' q k : 𝕜) * w k := by
      ext k
      rw [hpA, Matrix.mulVec_diagonal]
    rw [hpe, hv]
    have hsq : (τ⁻¹ * ‖WithLp.toLp 2 w‖) ^ 2 ≤
        ‖WithLp.toLp 2 (fun k : Fin (q + 1) =>
          p.eval (chebyshevExtremum a a' q k : 𝕜) * w k)‖ ^ 2 := by
      rw [hnorm, mul_pow, hw, sq, mul_assoc, inv_mul_cancel₀ hτ.ne', mul_one]
      exact inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq ha haa hp hp₀
    exact (pow_le_pow_iff_left₀ (mul_nonneg (inv_nonneg.mpr hτ.le) (norm_nonneg _))
      (norm_nonneg _) two_ne_zero).mp hsq

/-- The spectrum of the two-interval matrix lies in $[-a', -a] \cup [a, a']$. -/
theorem spectrum_chebyshevTwoIntervalMatrix_subset {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a')
    (k : ℕ) :
    spectrum ℝ (chebyshevTwoIntervalMatrix 𝕜 a a' k) ⊆ Set.Icc (-a') (-a) ∪ Set.Icc a a' := by
  have hξ : ∀ j : Fin (k + 1), a ≤ Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) k j) ∧
      Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) k j) ≤ a' := fun j => by
    have h := chebyshevExtremum_mem_Icc (pow_le_pow_left₀ ha.le haa 2) k j
    exact ⟨(Real.sqrt_sq ha.le).symm.trans_le (Real.sqrt_le_sqrt h.1),
      (Real.sqrt_le_sqrt h.2).trans_eq (Real.sqrt_sq (ha.le.trans haa))⟩
  rw [← spectrum.preimage_algebraMap 𝕜, chebyshevTwoIntervalMatrix, spectrum_diagonal]
  rintro r ⟨i, hi⟩
  rcases i with j | j
  · simp only [Sum.elim_inl] at hi
    rw [RCLike.algebraMap_eq_ofReal, RCLike.ofReal_inj] at hi
    rw [← hi]
    exact Or.inr (hξ j)
  · simp only [Sum.elim_inr] at hi
    rw [RCLike.algebraMap_eq_ofReal, ← RCLike.ofReal_neg, RCLike.ofReal_inj] at hi
    rw [← hi]
    exact Or.inl ⟨neg_le_neg (hξ j).2, neg_le_neg (hξ j).1⟩

/-- **MINRES attains the two-interval value**: for $0 < a < a'$ and every $q$, with
$k = \lfloor q/2 \rfloor$, the two-interval matrix and right-hand side give
$$\|\mathbf{w} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{w}, \mathbf{0}, q)\| =
T_k\Bigl(\frac{a'^2 + a^2}{a'^2 - a^2}\Bigr)^{-1}\|\mathbf{w}\| \,,$$
which is $2\rho_2^k/(1 + \rho_2^{2k})$ with $\rho_2 = (a'/a - 1)/(a'/a + 1)$, against the
bound $2\rho_2^k$. Odd steps gain nothing: the data are symmetric, so the least-squares residual
polynomial is even. For a residual $p$ of degree at most $q$ and $u = p(\sqrt{\xi_j})$,
$v = p(-\sqrt{\xi_j})$, $\lvert u \rvert^2 + \lvert v \rvert^2 \ge 2\lvert (u + v)/2 \rvert^2$, and
$(u + v)/2 = P(\xi_j)$ for the even part $P(x^2)$ of $p$, of degree at most $\lfloor q/2 \rfloor$;
so the residual is at least the interval value on $[a^2, a'^2]$, which the even Chebyshev residual
attains. [Greenbaum1997, §3.1, pp. 53–54].
Result: minres-two-interval-sharp -/
theorem norm_sub_mulVec_gmresIterate_chebyshevTwoIntervalMatrix {a a' : ℝ} (ha : 0 < a)
    (haa : a < a') (q : ℕ) :
    ‖WithLp.toLp 2 (chebyshevTwoIntervalVector 𝕜 a a' (q / 2) -
        chebyshevTwoIntervalMatrix 𝕜 a a' (q / 2) *ᵥ gmresIterate
          (chebyshevTwoIntervalMatrix 𝕜 a a' (q / 2)) (chebyshevTwoIntervalVector 𝕜 a a' (q / 2))
          0 q)‖ =
      ((T ℝ ((q / 2 : ℕ) : ℤ)).eval ((a' ^ 2 + a ^ 2) / (a' ^ 2 - a ^ 2)))⁻¹ *
        ‖WithLp.toLp 2 (chebyshevTwoIntervalVector 𝕜 a a' (q / 2))‖ := by
  set k := q / 2 with hk
  set A := chebyshevTwoIntervalMatrix 𝕜 a a' k
  set w := chebyshevTwoIntervalVector 𝕜 a a' k
  set ξ := chebyshevExtremum (a ^ 2) (a' ^ 2) k
  set ω := chebyshevWeight (a ^ 2) (a' ^ 2) k
  set τ := (T ℝ (k : ℤ)).eval ((a' ^ 2 + a ^ 2) / (a' ^ 2 - a ^ 2))
  have ha2 : 0 < a ^ 2 := pow_pos ha 2
  have haa2 : a ^ 2 < a' ^ 2 := pow_lt_pow_left₀ haa ha.le two_ne_zero
  have hτ : 0 < τ := zero_lt_one.trans_le (one_le_eval_T_real (k : ℤ) (by
    rw [le_div_iff₀ (by linarith)]
    linarith))
  have hω : ∀ j, 0 < ω j := chebyshevWeight_pos ha2 haa2 k
  have hξ0 : ∀ j : Fin (k + 1), 0 ≤ ξ j := fun j =>
    ha2.le.trans (chebyshevExtremum_mem_Icc haa2.le k j).1
  have hH : A.IsHermitian := by
    change (Matrix.diagonal _).IsHermitian
    rw [Matrix.isHermitian_diagonal_iff]
    rintro (j | j)
    · exact RCLike.conj_ofReal _
    · exact IsSelfAdjoint.neg (show IsSelfAdjoint ((Real.sqrt (ξ j) : ℝ) : 𝕜) from
        RCLike.conj_ofReal _)
  have hnormS : ∀ v : Fin (k + 1) ⊕ Fin (k + 1) → 𝕜, ‖WithLp.toLp 2 v‖ ^ 2 =
      ∑ j, (‖v (Sum.inl j)‖ ^ 2 + ‖v (Sum.inr j)‖ ^ 2) := fun v => by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Finset.sum_add_distrib]
  have hwl : ∀ j, ‖w (Sum.inl j)‖ ^ 2 = ω j / 2 := fun j => by
    simp only [w, chebyshevTwoIntervalVector, Sum.elim_inl]
    rw [RCLike.norm_ofReal, sq_abs, Real.sq_sqrt (by linarith [hω j])]
  have hwr : ∀ j, ‖w (Sum.inr j)‖ ^ 2 = ω j / 2 := fun j => by
    simp only [w, chebyshevTwoIntervalVector, Sum.elim_inr]
    rw [RCLike.norm_ofReal, sq_abs, Real.sq_sqrt (by linarith [hω j])]
  have hw : ‖WithLp.toLp 2 w‖ ^ 2 = τ := by
    rw [hnormS]
    refine (Finset.sum_congr rfl fun j _ => ?_).trans (sum_chebyshevWeight ha2 haa2 k)
    rw [hwl, hwr]
    ring
  refine le_antisymm ?_ ?_
  · -- the even Chebyshev residual attains the value
    have hP : ((chebyshevResidual (a ^ 2) (a' ^ 2) k).comp (X ^ 2)).degree ≤ q :=
      (degree_chebyshevResidual_comp_X_sq_le _ _ k).trans (by exact_mod_cast (by omega : 2 * k ≤ q))
    have h := hH.norm_sub_mulVec_gmresIterate_le (spectrum_chebyshevTwoIntervalMatrix_subset ha
      haa.le k) w 0 hP (eval_chebyshevResidual_comp_X_sq_zero k ha2 haa2) (η := τ⁻¹)
      (abs_eval_chebyshevResidual_comp_X_sq_le k ha haa)
    rwa [Matrix.mulVec_zero, sub_zero] at h
  · -- every residual polynomial does at least as badly, through its even part
    obtain ⟨p, hp, hp₀, hpe⟩ := exists_sub_mulVec_gmresIterate_eq_aeval A w 0 q
    rw [Matrix.mulVec_zero, sub_zero] at hpe
    have hpA : aeval A p = Matrix.diagonal (fun i => p.eval (Sum.elim
        (fun j : Fin (k + 1) => ((Real.sqrt (ξ j) : ℝ) : 𝕜))
        (fun j : Fin (k + 1) => -((Real.sqrt (ξ j) : ℝ) : 𝕜)) i)) :=
      aeval_diagonal_self _ p
    have hPd := degree_contract_le_of_degree_le two_ne_zero hp
    have hP₀ : (contract 2 p).eval 0 = 1 := by rw [eval_zero_contract two_ne_zero, hp₀]
    have hterm : ∀ j, ω j * ‖(contract 2 p).eval (ξ j : 𝕜)‖ ^ 2 ≤
        ‖(aeval A p *ᵥ w) (Sum.inl j)‖ ^ 2 + ‖(aeval A p *ᵥ w) (Sum.inr j)‖ ^ 2 := fun j => by
      have hx2 : ((Real.sqrt (ξ j) : ℝ) : 𝕜) ^ 2 = (ξ j : 𝕜) := by
        rw [← RCLike.ofReal_pow, Real.sq_sqrt (hξ0 j)]
      rw [← hx2, hpA, Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [norm_mul, norm_mul, mul_pow, mul_pow, hwl, hwr]
      have h := mul_norm_eval_contract_two_sq_le p ((Real.sqrt (ξ j) : ℝ) : 𝕜) (hω j).le
      linarith
    have hres : τ⁻¹ ≤ ‖WithLp.toLp 2 (aeval A p *ᵥ w)‖ ^ 2 := by
      rw [hnormS]
      exact (inv_eval_T_real_le_sum_chebyshevWeight_mul_norm_sq ha2 haa2 hPd hP₀).trans
        (Finset.sum_le_sum fun j _ => hterm j)
    rw [hpe]
    have hsq : (τ⁻¹ * ‖WithLp.toLp 2 w‖) ^ 2 ≤ ‖WithLp.toLp 2 (aeval A p *ᵥ w)‖ ^ 2 := by
      rw [mul_pow, hw, sq, mul_assoc, inv_mul_cancel₀ hτ.ne', mul_one]
      exact hres
    exact (pow_le_pow_iff_left₀ (mul_nonneg (inv_nonneg.mpr hτ.le) (norm_nonneg _))
      (norm_nonneg _) two_ne_zero).mp hsq

/-! ### Every spectrum: Greenbaum's theorem -/

section Greenbaum

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real part of a spectral sum with $p = r$:
$\operatorname{Re}\sum_x a_x\,\overline{z_x}\,z_x = \sum_x a_x\lvert z_x \rvert^2$. -/
private lemma re_sum_ofReal_mul_star_mul_self {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (z : ι → 𝕜) :
    RCLike.re (∑ x ∈ s, ((a x : ℝ) : 𝕜) * (star (z x) * z x)) = ∑ x ∈ s, a x * ‖z x‖ ^ 2 := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    RCLike.ofReal_re]

/-- The spectrum of a Hermitian matrix on a nonempty index type is a nonempty finite set. -/
private lemma exists_finset_spectrum_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) [Nonempty n] :
    ∃ S : Finset ℝ, spectrum ℝ A = ↑S ∧ S.Nonempty := by
  obtain ⟨S, hS⟩ := A.finite_real_spectrum.exists_finset_coe
  have h := hA.eigenvalue_mem_spectrum (k := 0) Fintype.card_pos
  rw [← hS] at h
  exact ⟨S, hS.symm, _, h⟩

/-- **The spectrum-minimax bound for CG is attained** (Greenbaum): for $n$ nonempty and positive
definite $\mathbf{A}$, every start $\mathbf{x}_0$ and every $q$ there is a solution
$\mathbf{x}_\star \ne \mathbf{x}_0$ with, for $\mathbf{b} = \mathbf{A}\mathbf{x}_\star$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}^2
= \mathsf{residualMinimax}(\sigma(\mathbf{A}), q)^2
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,,$$
where $\mathsf{residualMinimax}(\sigma(\mathbf{A}), q) =
\min_{p}\max_{\lambda \in \sigma(\mathbf{A})}\lvert p(\lambda) \rvert$, the minimum over real
$p$ with $\deg p \le q$, $p(0) = 1$. So
`Matrix.PosDef.re_quadForm_sub_cgIterate_le_residualMinimax_sq_mul` cannot be improved for any
spectrum. The interval case with an explicit instance is
`re_quadForm_sub_cgIterate_chebyshevExtremaMatrix`. The initial error carries the dual weights
$w_\lambda$ of `exists_residualMinimax_sq_le_sum_mul_norm_sq`, divided by $\lambda$, as its
spectral weights. [Greenbaum1979, Theorems 1–2, pp. 184–186]; [Greenbaum1997, §3.1, pp. 49–51].
Result: cg-spectrum-minimax-sharp -/
theorem _root_.Matrix.PosDef.exists_re_quadForm_sub_cgIterate_eq_residualMinimax_sq_mul
    {A : Matrix n n 𝕜} (hA : A.PosDef) [Nonempty n] (x₀ : n → 𝕜) (q : ℕ) :
    ∃ xs : n → 𝕜, xs ≠ x₀ ∧
      RCLike.re (quadForm A (xs - cgIterate A (A *ᵥ xs) x₀ q)) =
        residualMinimax (spectrum ℝ A) q ^ 2 * RCLike.re (quadForm A (xs - x₀)) := by
  obtain ⟨S, hS, hSne⟩ := exists_finset_spectrum_eq hA.isHermitian
  obtain ⟨w, hw, hw1, hmin⟩ := exists_residualMinimax_sq_le_sum_mul_norm_sq 𝕜 hSne q
  have hpos : ∀ x ∈ S, 0 < x := fun x hx =>
    hA.spectrum_subset_Ioi (show x ∈ spectrum ℝ A by rw [hS]; exact hx)
  obtain ⟨e, he⟩ := hA.isHermitian.exists_star_aeval_mulVec_dotProduct_cfc_mulVec_eq_sum hS
    (w := fun x => w x / x) fun x hx => div_nonneg (hw x hx) (hpos x hx).le
  -- the squared `A`-norm of `p(A) e` in the dual weights
  have hnorm : ∀ p : 𝕜[X], RCLike.re (quadForm A (aeval A p *ᵥ e)) =
      ∑ x ∈ S, w x * ‖p.eval (x : 𝕜)‖ ^ 2 := by
    intro p
    have hA' : IsSelfAdjoint A := hA.isHermitian
    have h := he (fun x => x) p p
    rw [cfc_id' ℝ A hA'] at h
    rw [quadForm_def, h, re_sum_ofReal_mul_star_mul_self]
    exact Finset.sum_congr rfl fun x hx => by rw [div_mul_cancel₀ _ (hpos x hx).ne']
  have he1 : RCLike.re (quadForm A e) = 1 := by
    have h := hnorm 1
    simp only [map_one, Matrix.one_mulVec, eval_one, norm_one, one_pow, mul_one, hw1] at h
    exact h
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [quadForm_def, Matrix.mulVec_zero, dotProduct_zero, map_zero] at he1
    exact zero_ne_one he1
  refine ⟨x₀ + e, fun h => he0 (add_eq_left.mp h), ?_⟩
  obtain ⟨p, hp, hp₀, hpe⟩ := exists_sub_cgIterate_eq_aeval (A := A) (b := A *ᵥ (x₀ + e))
    (xs := x₀ + e) rfl x₀ q
  refine le_antisymm (hA.re_quadForm_sub_cgIterate_le_residualMinimax_sq_mul rfl x₀ q) ?_
  rw [hpe, add_sub_cancel_left, he1, mul_one, hnorm, hS]
  exact hmin p hp hp₀

/-- **The worst case of CG is the spectrum minimax value**: for $n$ nonempty and positive
definite $\mathbf{A}$, a start $\mathbf{x}_0$ and $q$, the largest ratio
$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{A}\mathbf{x}_\star, \mathbf{x}_0,
q)\|_{\mathbf{A}}^2 / \|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2$ over
$\mathbf{x}_\star \ne \mathbf{x}_0$ is $\mathsf{residualMinimax}(\sigma(\mathbf{A}), q)^2$: the
equation of `Matrix.PosDef.exists_re_quadForm_sub_cgIterate_eq_residualMinimax_sq_mul` with
the bound `Matrix.PosDef.re_quadForm_sub_cgIterate_le_residualMinimax_sq_mul`.
[Greenbaum1979, Theorems 1–2, pp. 184–186].
Result: cg-spectrum-minimax-sharp -/
theorem _root_.Matrix.PosDef.isGreatest_re_quadForm_sub_cgIterate_div {A : Matrix n n 𝕜}
    (hA : A.PosDef) [Nonempty n] (x₀ : n → 𝕜) (q : ℕ) :
    IsGreatest ((fun xs => RCLike.re (quadForm A (xs - cgIterate A (A *ᵥ xs) x₀ q)) /
        RCLike.re (quadForm A (xs - x₀))) '' {xs | xs ≠ x₀})
      (residualMinimax (spectrum ℝ A) q ^ 2) := by
  have hD : ∀ xs : n → 𝕜, xs ≠ x₀ → 0 < RCLike.re (quadForm A (xs - x₀)) :=
    fun xs h => hA.re_quadForm_pos (sub_ne_zero.mpr h)
  obtain ⟨xs, hne, heq⟩ := hA.exists_re_quadForm_sub_cgIterate_eq_residualMinimax_sq_mul x₀ q
  refine ⟨⟨xs, hne, ?_⟩, ?_⟩
  · simp only
    rw [heq, mul_div_cancel_right₀ _ (hD xs hne).ne']
  · rintro _ ⟨y, hy, rfl⟩
    exact (div_le_iff₀ (hD y hy)).mpr
      (hA.re_quadForm_sub_cgIterate_le_residualMinimax_sq_mul rfl x₀ q)

/-- **The spectrum-minimax bound for MINRES is attained**: for $n$ nonempty and Hermitian
$\mathbf{A}$ (indefinite or singular allowed), every start $\mathbf{x}_0$ and every $q$ there is a
$\mathbf{b}$ with $\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0 \ne \mathbf{0}$ and
$$\|\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|
= \mathsf{residualMinimax}(\sigma(\mathbf{A}), q)\,\|\mathbf{r}_0\| \,.$$
So `Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_residualMinimax_mul` cannot be improved
for any spectrum. For singular $\mathbf{A}$ the value is $1$ ($p(0) = 1$ on the eigenvalue $0$).
The initial residual carries the dual weights of
`exists_residualMinimax_sq_le_sum_mul_norm_sq` as its spectral weights.
[GreenbaumGurvits1994]; [Greenbaum1997, §3.1, pp. 49–51].
Result: minres-spectrum-minimax-sharp -/
theorem _root_.Matrix.IsHermitian.exists_norm_sub_mulVec_gmresIterate_eq_residualMinimax_mul
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) [Nonempty n] (x₀ : n → 𝕜) (q : ℕ) :
    ∃ b : n → 𝕜, b ≠ A *ᵥ x₀ ∧
      ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ =
        residualMinimax (spectrum ℝ A) q * ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ := by
  obtain ⟨S, hS, hSne⟩ := exists_finset_spectrum_eq hA
  obtain ⟨w, hw, hw1, hmin⟩ := exists_residualMinimax_sq_le_sum_mul_norm_sq 𝕜 hSne q
  obtain ⟨r, hr⟩ := hA.exists_star_aeval_mulVec_dotProduct_cfc_mulVec_eq_sum hS hw
  -- the squared norm of `p(A) r` in the dual weights
  have hnorm : ∀ p : 𝕜[X], ‖WithLp.toLp 2 (aeval A p *ᵥ r)‖ ^ 2 =
      ∑ x ∈ S, w x * ‖p.eval (x : 𝕜)‖ ^ 2 := by
    intro p
    have h := hr (fun _ => 1) p p
    rw [cfc_const_one ℝ A, Matrix.one_mulVec] at h
    rw [EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct, h, re_sum_ofReal_mul_star_mul_self]
    simp only [mul_one]
  have hr1 : ‖WithLp.toLp 2 r‖ = 1 := by
    have h := hnorm 1
    simp only [map_one, Matrix.one_mulVec, eval_one, norm_one, one_pow, mul_one, hw1] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
  refine ⟨A *ᵥ x₀ + r, fun h => ?_, ?_⟩
  · rw [add_eq_left.mp h, WithLp.toLp_zero, norm_zero] at hr1
    exact zero_ne_one hr1
  obtain ⟨p, hp, hp₀, hpe⟩ := exists_sub_mulVec_gmresIterate_eq_aeval A (A *ᵥ x₀ + r) x₀ q
  have hup := hA.norm_sub_mulVec_gmresIterate_le_residualMinimax_mul (A *ᵥ x₀ + r) x₀ q
  rw [add_sub_cancel_left] at hpe hup ⊢
  rw [hr1, mul_one] at hup ⊢
  refine le_antisymm hup ?_
  rw [hpe]
  refine (pow_le_pow_iff_left₀ (residualMinimax_nonneg _ q) (norm_nonneg _) two_ne_zero).mp ?_
  rw [hnorm, hS]
  exact hmin p hp hp₀

/-- **The worst case of MINRES is the spectrum minimax value**: for $n$ nonempty and Hermitian
$\mathbf{A}$, a start $\mathbf{x}_0$ and $q$,
$$\max_{\mathbf{b} \ne \mathbf{A}\mathbf{x}_0}
\frac{\|\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|}
{\|\mathbf{b} - \mathbf{A}\mathbf{x}_0\|} = \mathsf{residualMinimax}(\sigma(\mathbf{A}), q)\,,$$
the maximum being attained: it combines the equation
`Matrix.IsHermitian.exists_norm_sub_mulVec_gmresIterate_eq_residualMinimax_mul` with the bound
`Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_residualMinimax_mul`.
[GreenbaumGurvits1994]; [Greenbaum1997, §3.1, pp. 49–51].
Result: minres-spectrum-minimax-sharp -/
theorem _root_.Matrix.IsHermitian.isGreatest_norm_sub_mulVec_gmresIterate_div
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) [Nonempty n] (x₀ : n → 𝕜) (q : ℕ) :
    IsGreatest ((fun b => ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ /
        ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖) '' {b | b ≠ A *ᵥ x₀})
      (residualMinimax (spectrum ℝ A) q) := by
  have hD : ∀ b : n → 𝕜, b ≠ A *ᵥ x₀ → 0 < ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ := fun b h =>
    norm_pos_iff.mpr fun h0 => h (sub_eq_zero.mp (by rwa [WithLp.toLp_eq_zero] at h0))
  obtain ⟨b, hne, heq⟩ := hA.exists_norm_sub_mulVec_gmresIterate_eq_residualMinimax_mul x₀ q
  refine ⟨⟨b, hne, ?_⟩, ?_⟩
  · simp only
    rw [heq, mul_div_cancel_right₀ _ (hD b hne).ne']
  · rintro _ ⟨c, hc, rfl⟩
    exact (div_le_iff₀ (hD c hc)).mpr
      (hA.norm_sub_mulVec_gmresIterate_le_residualMinimax_mul c x₀ q)

end Greenbaum

end NLAlib
