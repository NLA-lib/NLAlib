/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Complex.Basic
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber

/-!
# Last-row weights of an eigenvector matrix

For an invertible eigenvector matrix $\mathbf{V}$ of a diagonalizable $\mathbf{H}$, the weights
$$w_i = \frac{\lvert\mathbf{V}_{n,i}\rvert^2}{\|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|^2}$$
form a probability vector on the eigenvalues. Sums against them are the "approximate functional
calculus" of [BanksGarzaVargasSrivastava2021]: the law of the random variable $Z_{\mathbf{H}}$
there, written as finite weighted sums here. For every $\mathbf{g}$, the last row of
$\mathbf{V}\operatorname{diag}(\mathbf{g})\mathbf{V}^{-1}$ and the weighted second moment of
$\mathbf{g}$ agree up to the factor $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$ in each direction.
For normal $\mathbf{H}$ and unitary $\mathbf{V}$ the weights are the spectral measure of
$\mathbf{H}$ at $\mathbf{e}_n$.

## Main definitions

* `NLAlib.lastRowWeights`.

## Main results

* `NLAlib.lastRowWeights_nonneg`, `NLAlib.sum_lastRowWeights`: a probability vector.
* `NLAlib.sum_lastRowWeights_mul_sq_le`, `NLAlib.norm_mul_diagonal_mul_inv_last_sq_le`: the two
  sides of the approximate functional calculus.
* `NLAlib.sqrt_lastRowWeights_le_mul_one_add`: the weights after a right factor
  $\mathbf{I} + \mathbf{Z}$.
* `NLAlib.lastRowWeights_conjTranspose_mul`, `NLAlib.le_lastRowWeights_conjTranspose_mul`: the
  weights after a unitary similarity with a prescribed last column
  [BanksGarzaVargasSrivastava2025].
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- The **last-row weights** of a square matrix $\mathbf{V}$:
$w_i = \lvert\mathbf{V}_{n,i}\rvert^2 / \|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|^2$, the squared
moduli of the last row normalised to sum to $1$ (all $0$ if the last row vanishes, which an
invertible $\mathbf{V}$ excludes). With $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(
\mathbf{d})$, the weight $w_i$ sits on the eigenvalue $\mathbf{d}_i$: this is the distribution of
$Z_{\mathbf{H}}$ in [BanksGarzaVargasSrivastava2021, Definition 4.1], where $\mathbf{V}$ is
normalised by $\|\mathbf{V}\|_2 = \|\mathbf{V}^{-1}\|_2$, which no statement here needs. -/
noncomputable def lastRowWeights (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    ℝ :=
  ‖V (Fin.last n) i‖ ^ 2 / ‖WithLp.toLp 2 (V (Fin.last n))‖ ^ 2

/-- The last-row weights are nonnegative. -/
theorem lastRowWeights_nonneg (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    0 ≤ lastRowWeights V i := by
  unfold lastRowWeights
  positivity

/-- The last row of an invertible matrix is not zero. -/
private theorem norm_toLp_last_ne_zero {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hV : IsUnit V) : ‖WithLp.toLp 2 (V (Fin.last n))‖ ≠ 0 := by
  refine norm_ne_zero_iff.mpr fun h => not_isUnit_zero (M₀ := ℂ) ?_
  rw [← Matrix.det_eq_zero_of_row_eq_zero (Fin.last n)
    (fun j => by simpa using congrFun (congrArg WithLp.ofLp h) j)]
  exact (Matrix.isUnit_iff_isUnit_det V).mp hV

/-- The last-row weights of an invertible matrix sum to one: for invertible $\mathbf{V}$,
$\sum_i \lvert\mathbf{V}_{n,i}\rvert^2 / \|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|^2 = 1$. -/
theorem sum_lastRowWeights {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hV : IsUnit V) :
    ∑ i, lastRowWeights V i = 1 := by
  unfold lastRowWeights
  rw [← Finset.sum_div, div_eq_one_iff_eq (pow_ne_zero 2 (norm_toLp_last_ne_zero hV)),
    EuclideanSpace.norm_sq_eq]

/-- The last row of $\mathbf{V}\operatorname{diag}(\mathbf{g})\mathbf{V}^{-1}$ is
$\mathbf{y}^{\mathsf{T}}\mathbf{V}^{-1}$ with $\mathbf{y}_k = \mathbf{V}_{n,k}\mathbf{g}_k$,
and $\|\mathbf{y}\|^2 =
\|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|^2\sum_i w_i\lvert\mathbf{g}_i\rvert^2$. -/
private theorem lastRow_mul_diagonal_mul_inv {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hV : IsUnit V) (g : Fin (n + 1) → ℂ) :
    (V * Matrix.diagonal g * V⁻¹) (Fin.last n) = (fun k => V (Fin.last n) k * g k) ᵥ* V⁻¹ ∧
      ‖WithLp.toLp 2 (fun k => V (Fin.last n) k * g k)‖ ^ 2 =
        ‖WithLp.toLp 2 (V (Fin.last n))‖ ^ 2 * ∑ i, lastRowWeights V i * ‖g i‖ ^ 2 := by
  refine ⟨by
    ext j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.diagonal_apply, mul_assoc], ?_⟩
  have hn := norm_toLp_last_ne_zero hV
  rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold lastRowWeights
  simp only [norm_mul, mul_pow]
  field_simp

/-- **Approximate functional calculus, upper bound on the moment**: for invertible $\mathbf{V}$
with last-row weights $w$ and every $\mathbf{g}$,
$$\sum_i w_i\lvert\mathbf{g}_i\rvert^2 \le \bigl(\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2\bigr)^2\,
\|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\operatorname{diag}(\mathbf{g})\mathbf{V}^{-1}\|^2\,.$$
With $\mathbf{H} = \mathbf{V}\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}$ and
$\mathbf{g} = f(\mathbf{d})$: $\mathbb{E}\lvert f(Z_{\mathbf{H}})\rvert^2 \le
\kappa_V^2\|\mathbf{e}_n^{\mathsf{H}}f(\mathbf{H})\|^2$. [BanksGarzaVargasSrivastava2021,
Lemma 4.2], the right inequality; there $\mathbf{V}$ is normalised and $f$ arbitrary. -/
theorem sum_lastRowWeights_mul_sq_le {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hV : IsUnit V)
    (g : Fin (n + 1) → ℂ) :
    ∑ i, lastRowWeights V i * ‖g i‖ ^ 2 ≤
      pseudoConditionNumber V ^ 2 *
        ‖WithLp.toLp 2 ((V * Matrix.diagonal g * V⁻¹) (Fin.last n))‖ ^ 2 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  obtain ⟨hrow, hS⟩ := lastRow_mul_diagonal_mul_inv hV g
  set y : Fin (n + 1) → ℂ := fun k => V (Fin.last n) k * g k
  have hT : 0 ≤ ∑ i, lastRowWeights V i * ‖g i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (lastRowWeights_nonneg V i) (sq_nonneg _)
  -- `‖y‖ ≤ ‖V‖₂ ‖yᵀV⁻¹‖`, and `1 = ‖e_nᴴ V V⁻¹‖ ≤ ‖V⁻¹‖₂ ‖e_nᴴ V‖`
  have hsq : ‖WithLp.toLp 2 y‖ ^ 2 ≤
      specNorm V ^ 2 * ‖WithLp.toLp 2 ((V * Matrix.diagonal g * V⁻¹) (Fin.last n))‖ ^ 2 := by
    rw [hrow, ← mul_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul V hdet] using
      norm_toLp_vecMul_le V (y ᵥ* V⁻¹)
  have hone : (1 : ℝ) ≤ specNorm V⁻¹ ^ 2 * ‖WithLp.toLp 2 (V (Fin.last n))‖ ^ 2 := by
    have h := norm_toLp_vecMul_le V⁻¹ (V (Fin.last n))
    have hr : V (Fin.last n) ᵥ* V⁻¹ = Pi.single (Fin.last n) 1 := by
      rw [show V (Fin.last n) = Pi.single (Fin.last n) 1 ᵥ* V from
          (Matrix.single_one_vecMul (Fin.last n) V).symm, Matrix.vecMul_vecMul,
        Matrix.mul_nonsing_inv V hdet, Matrix.vecMul_one]
    rw [hr, PiLp.toLp_single, PiLp.norm_single, norm_one] at h
    simpa [mul_pow] using pow_le_pow_left₀ zero_le_one h 2
  rw [pseudoConditionNumber_of_isUnit hV, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left hone hT,
    mul_le_mul_of_nonneg_left hsq (sq_nonneg (specNorm V⁻¹))]

/-- **Approximate functional calculus, lower bound on the moment**: for invertible $\mathbf{V}$
with last-row weights $w$ and every $\mathbf{g}$,
$$\|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\operatorname{diag}(\mathbf{g})\mathbf{V}^{-1}\|^2 \le
\bigl(\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2\bigr)^2 \sum_i w_i\lvert\mathbf{g}_i\rvert^2\,.$$
[BanksGarzaVargasSrivastava2021, Lemma 4.2], the left inequality. -/
theorem norm_mul_diagonal_mul_inv_last_sq_le {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hV : IsUnit V) (g : Fin (n + 1) → ℂ) :
    ‖WithLp.toLp 2 ((V * Matrix.diagonal g * V⁻¹) (Fin.last n))‖ ^ 2 ≤
      pseudoConditionNumber V ^ 2 * ∑ i, lastRowWeights V i * ‖g i‖ ^ 2 := by
  obtain ⟨hrow, hS⟩ := lastRow_mul_diagonal_mul_inv hV g
  have hT : 0 ≤ ∑ i, lastRowWeights V i * ‖g i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (lastRowWeights_nonneg V i) (sq_nonneg _)
  -- `‖e_nᴴ V‖ ≤ ‖V‖₂`
  have hDle : ‖WithLp.toLp 2 (V (Fin.last n))‖ ^ 2 ≤ specNorm V ^ 2 := by
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have h := norm_toLp_vecMul_le V (Pi.single (Fin.last n) 1)
    rw [Matrix.single_one_vecMul, PiLp.toLp_single, PiLp.norm_single, norm_one, mul_one] at h
    exact h
  have hL := pow_le_pow_left₀ (norm_nonneg _)
    (norm_toLp_vecMul_le V⁻¹ (fun k => V (Fin.last n) k * g k)) 2
  rw [← hrow, mul_pow, hS] at hL
  rw [pseudoConditionNumber_of_isUnit hV, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hDle hT)
    (sq_nonneg (specNorm V⁻¹))]

/-! ### Weights under a perturbation of the columns -/

/-- The square root of a last-row weight is a ratio of moduli:
$\sqrt{w_i} = \lvert\mathbf{V}_{n,i}\rvert / \|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|$. -/
theorem sqrt_lastRowWeights (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    √(lastRowWeights V i) = ‖V (Fin.last n) i‖ / ‖WithLp.toLp 2 (V (Fin.last n))‖ := by
  unfold lastRowWeights
  rw [Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The weights after a right factor near the identity: for every $\mathbf{W}$, $\mathbf{Z}$
and $i$, the last-row weights of $\mathbf{W}$ and $\mathbf{W}(\mathbf{I} + \mathbf{Z})$ satisfy
$$\sqrt{w_i(\mathbf{W})} \le (1 + \|\mathbf{Z}\|_2)\sqrt{w_i(\mathbf{W}(\mathbf{I} +
  \mathbf{Z}))} + \|\mathbf{Z}\|_2.$$
With $\mathbf{W} = \mathbf{Q}^{\mathsf{H}}\mathbf{V}$ and $\mathbf{V}(\mathbf{I} + \mathbf{Z})$ the
eigenvectors of a perturbed matrix, this transfers weights to the perturbed eigenvectors.
No printed source. -/
theorem sqrt_lastRowWeights_le_mul_one_add (W Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) :
    √(lastRowWeights W i) ≤
      (1 + specNorm Z) * √(lastRowWeights (W * (1 + Z)) i) + specNorm Z := by
  set r := W (Fin.last n)
  set ζ := specNorm Z
  have hζ : 0 ≤ ζ := specNorm_nonneg Z
  have hrow : (W * (1 + Z)) (Fin.last n) = r + r ᵥ* Z := by
    rw [Matrix.mul_add, Matrix.mul_one]
    ext j
    simp [r, Matrix.vecMul, dotProduct, Matrix.mul_apply]
  rw [sqrt_lastRowWeights, sqrt_lastRowWeights, hrow]
  set r' := r + r ᵥ* Z
  have hS : 0 ≤ (1 + ζ) * (‖r' i‖ / ‖WithLp.toLp 2 r'‖) := by positivity
  rcases eq_or_lt_of_le (norm_nonneg (WithLp.toLp 2 r)) with h0 | hpos
  · rw [← h0, div_zero]
    linarith
  -- `|r_i| ≤ |r'_i| + ‖Z‖₂‖r‖` and `‖r'‖ ≤ (1 + ‖Z‖₂)‖r‖`
  have hZr : ‖WithLp.toLp 2 (r ᵥ* Z)‖ ≤ ζ * ‖WithLp.toLp 2 r‖ := norm_toLp_vecMul_le Z r
  have hri : ‖r i‖ ≤ ‖r' i‖ + ζ * ‖WithLp.toLp 2 r‖ := by
    have h := norm_sub_le (r' i) ((r ᵥ* Z) i)
    rw [show r' i - (r ᵥ* Z) i = r i by simp [r']] at h
    have h2 : ‖(r ᵥ* Z) i‖ ≤ ζ * ‖WithLp.toLp 2 r‖ :=
      (PiLp.norm_apply_le (WithLp.toLp 2 (r ᵥ* Z)) i).trans hZr
    linarith
  have hr' : ‖WithLp.toLp 2 r'‖ ≤ (1 + ζ) * ‖WithLp.toLp 2 r‖ := by
    rw [WithLp.toLp_add]
    exact (norm_add_le _ _).trans (by linarith)
  have hfirst : ‖r' i‖ / ‖WithLp.toLp 2 r‖ ≤ (1 + ζ) * (‖r' i‖ / ‖WithLp.toLp 2 r'‖) := by
    rcases eq_or_lt_of_le (norm_nonneg (WithLp.toLp 2 r')) with h0' | hpos'
    · have : ‖r' i‖ = 0 := le_antisymm
        ((PiLp.norm_apply_le (WithLp.toLp 2 r') i).trans h0'.symm.le) (norm_nonneg _)
      rw [this]
      simp
    · rw [mul_div_assoc', div_le_div_iff₀ hpos hpos', mul_assoc]
      nlinarith [mul_le_mul_of_nonneg_left hr' (norm_nonneg (r' i))]
  calc ‖r i‖ / ‖WithLp.toLp 2 r‖ ≤ ‖r' i‖ / ‖WithLp.toLp 2 r‖ + ζ := by
        rw [div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne']
        exact hri
    _ ≤ (1 + ζ) * (‖r' i‖ / ‖WithLp.toLp 2 r'‖) + ζ := by linarith

/-! ### Weights after a unitary similarity -/

/-- **The last-row weights of $\mathbf{Q}^{\mathsf{H}}\mathbf{V}$ are the squared overlaps with
the last column of $\mathbf{Q}$** ([BanksGarzaVargasSrivastava2025, Proposition 5.3],
deterministic part): if the last column of $\mathbf{Q}$ is $c\,\mathbf{x}$ with
$\lvert c\rvert = 1$, the weight of $i$ is
$$\frac{\lvert\langle \mathbf{x}, \mathbf{v}_i\rangle\rvert^2}
  {\|\mathbf{V}^{\mathsf{H}}\mathbf{x}\|^2}\,,$$
$\mathbf{v}_i$ the $i$-th column of $\mathbf{V}$. The phase $c$ of a rotation to $\mathbf{x}$
cancels, which the paper's reflector does not make explicit (its erratum P3). -/
theorem lastRowWeights_conjTranspose_mul {Q V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {x : Fin (n + 1) → ℂ} {c : ℂ} (hc : ‖c‖ = 1) (hQx : ∀ k, Q k (Fin.last n) = c * x k)
    (i : Fin (n + 1)) :
    lastRowWeights (Qᴴ * V) i =
      ‖star x ⬝ᵥ (fun k => V k i)‖ ^ 2 / ‖WithLp.toLp 2 (Vᴴ *ᵥ x)‖ ^ 2 := by
  have hrow : ∀ j, (Qᴴ * V) (Fin.last n) j = star c * (star x ⬝ᵥ (fun k => V k j)) := by
    intro j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hQx, star_mul', dotProduct,
      Pi.star_apply, Finset.mul_sum, mul_assoc]
  have hcol : ∀ j, (Vᴴ *ᵥ x) j = star (star x ⬝ᵥ (fun k => V k j)) := by
    intro j
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, star_mul',
      Pi.star_apply, star_star, mul_comm]
  have hsq : ‖WithLp.toLp 2 ((Qᴴ * V) (Fin.last n))‖ ^ 2 = ‖WithLp.toLp 2 (Vᴴ *ᵥ x)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hrow, hcol, norm_mul, norm_star, hc, one_mul]
  unfold lastRowWeights
  rw [hsq, hrow, norm_mul, norm_star, hc, one_mul]

/-- **A large overlap gives a large weight** ([BanksGarzaVargasSrivastava2025, Proposition 5.3],
deterministic part): let $\mathbf{V}$ be invertible, the last column of $\mathbf{Q}$ be
$c\,\mathbf{g}/\|\mathbf{g}\|$ with $\lvert c\rvert = 1$, $\|\mathbf{g}\| \le R$, $s \ge 0$, and
$\lvert\langle \mathbf{g}, \mathbf{v}_i\rangle\rvert \ge s\,\|\mathbf{v}_i\|$ for the $i$-th
column $\mathbf{v}_i$ of $\mathbf{V}$. Then
$$\frac{s^2}{R^2\,(\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2)^2} \le
  w_i(\mathbf{Q}^{\mathsf{H}}\mathbf{V})\,,$$
for any scaling of the columns of $\mathbf{V}$. -/
theorem le_lastRowWeights_conjTranspose_mul {Q V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {g : Fin (n + 1) → ℂ} {c : ℂ} {R s : ℝ} (hV : IsUnit V) (hc : ‖c‖ = 1)
    (hQx : ∀ k, Q k (Fin.last n) = c * ((‖WithLp.toLp 2 g‖⁻¹ : ℝ) : ℂ) * g k)
    (hg : ‖WithLp.toLp 2 g‖ ≤ R) (hs : 0 ≤ s) {i : Fin (n + 1)}
    (hgi : s * ‖WithLp.toLp 2 (fun k => V k i)‖ ≤ ‖star g ⬝ᵥ (fun k => V k i)‖) :
    s ^ 2 / (R ^ 2 * pseudoConditionNumber V ^ 2) ≤ lastRowWeights (Qᴴ * V) i := by
  rcases hs.eq_or_lt with rfl | hs
  · simpa using lastRowWeights_nonneg (Qᴴ * V) i
  set v : Fin (n + 1) → ℂ := fun k => V k i
  set γ := ‖WithLp.toLp 2 g‖
  have hdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  -- `1 ≤ ‖V⁻¹‖₂ ‖vᵢ‖`
  have hv1 : 1 ≤ specNorm V⁻¹ * ‖WithLp.toLp 2 v‖ := by
    have h := norm_toLp_mulVec_le V⁻¹ v
    have he : V⁻¹ *ᵥ v = Pi.single i 1 := by
      rw [show v = V *ᵥ Pi.single i 1 by ext k; simp [v],
        Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul V hdet, Matrix.one_mulVec]
    rwa [he, PiLp.toLp_single, PiLp.norm_single, norm_one] at h
  have hvpos : 0 < ‖WithLp.toLp 2 v‖ := by
    by_contra h0
    have h0 : ‖WithLp.toLp 2 v‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
    rw [h0, mul_zero] at hv1; exact absurd hv1 (by norm_num)
  have hγ : 0 < γ := by
    by_contra h0
    replace h0 := not_lt.mp h0
    have hg0 : g = 0 := by
      have : WithLp.toLp 2 g = 0 := norm_le_zero_iff.mp h0
      simpa using congrArg WithLp.ofLp this
    rw [hg0, star_zero, zero_dotProduct, norm_zero] at hgi
    nlinarith [mul_pos hs hvpos]
  set x : Fin (n + 1) → ℂ := fun k => ((γ⁻¹ : ℝ) : ℂ) * g k
  have hw := lastRowWeights_conjTranspose_mul (Q := Q) (V := V) (x := x) hc
    (fun k => by rw [hQx, mul_assoc]) i
  set a := ‖star x ⬝ᵥ v‖
  set b := ‖WithLp.toLp 2 (Vᴴ *ᵥ x)‖
  have hx1 : ‖WithLp.toLp 2 x‖ = 1 := by
    rw [show x = ((γ⁻¹ : ℝ) : ℂ) • g from rfl, WithLp.toLp_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hγ), inv_mul_cancel₀ hγ.ne']
  have ha : a = γ⁻¹ * ‖star g ⬝ᵥ v‖ := by
    change ‖star x ⬝ᵥ v‖ = _
    rw [show star x = ((γ⁻¹ : ℝ) : ℂ) • star g by ext k; simp [x],
      smul_dotProduct, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hγ)]
  have hab : a ≤ b := by
    have hcol : (Vᴴ *ᵥ x) i = star (star x ⬝ᵥ v) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_sum, star_mul',
        Pi.star_apply, star_star, mul_comm, v]
    have h := PiLp.norm_apply_le (WithLp.toLp 2 (Vᴴ *ᵥ x)) i
    rwa [WithLp.ofLp_toLp, hcol, norm_star] at h
  have hbV : b ≤ specNorm V := by
    have h := norm_toLp_mulVec_le Vᴴ x
    rwa [specNorm_conjTranspose, hx1, mul_one] at h
  -- `s ‖vᵢ‖ / γ ≤ a`
  have hsa : s * ‖WithLp.toLp 2 v‖ / γ ≤ a := by
    rw [ha, div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left hgi (inv_nonneg.mpr hγ.le)
  have hapos : 0 < a := lt_of_lt_of_le (div_pos (mul_pos hs hvpos) hγ) hsa
  have hbpos : 0 < b := hapos.trans_le hab
  have hVpos : 0 < specNorm V := hbpos.trans_le hbV
  rw [hw, pseudoConditionNumber_of_isUnit hV]
  -- `s² / (R² ‖V‖² ‖V⁻¹‖²) ≤ (s ‖vᵢ‖ / γ)² / ‖V‖² ≤ a² / b²`
  have hR : γ ≤ R := hg
  have hstep1 : s ^ 2 / (R ^ 2 * (specNorm V * specNorm V⁻¹) ^ 2) ≤
      (s * ‖WithLp.toLp 2 v‖ / γ) ^ 2 / specNorm V ^ 2 := by
    have hRpos : 0 < R := hγ.trans_le hR
    have hVi : 0 < specNorm V⁻¹ := by
      by_contra h0
      rw [le_antisymm (not_lt.mp h0) (specNorm_nonneg _), zero_mul] at hv1
      exact absurd hv1 (by norm_num)
    rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 1 ≤ (specNorm V⁻¹ * ‖WithLp.toLp 2 v‖) ^ 2 := one_le_pow₀ hv1
    have h2 : γ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hγ.le hR 2
    have hs2 : 0 < s ^ 2 := by positivity
    calc s ^ 2 * (γ ^ 2 * specNorm V ^ 2)
        ≤ s ^ 2 * (R ^ 2 * specNorm V ^ 2) * (specNorm V⁻¹ * ‖WithLp.toLp 2 v‖) ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg (specNorm V)),
            mul_nonneg (mul_nonneg hs2.le (mul_nonneg (sq_nonneg R) (sq_nonneg (specNorm V))))
              (sub_nonneg.mpr h1)]
      _ = (s * ‖WithLp.toLp 2 v‖) ^ 2 * (R ^ 2 * (specNorm V * specNorm V⁻¹) ^ 2) := by ring
  refine hstep1.trans ?_
  calc (s * ‖WithLp.toLp 2 v‖ / γ) ^ 2 / specNorm V ^ 2 ≤ a ^ 2 / specNorm V ^ 2 := by
        gcongr
    _ ≤ a ^ 2 / b ^ 2 := by gcongr

end NLAlib
