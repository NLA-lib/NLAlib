/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import NLAlib.ForMathlib.Analysis.MeanInequalities
public import NLAlib.Matrix.QRIteration.EigenvectorWeights
public import NLAlib.Matrix.QRIteration.ShiftedQR
public import NLAlib.Matrix.Spectral.EigenvalueListing
public import NLAlib.Matrix.Spectral.Diagonalizable

/-!
# Optimal and promising Ritz values

The two notions of approximate Ritz value that drive the shifting strategy of
[BanksGarzaVargasSrivastava2021]:

* `NLAlib.IsOptimalRitzValues θ H ss`: the shift polynomial of `ss` nearly minimises
  $\|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})\|$ over monic $p$ of its degree, whose minimum is
  $\psi_k(\mathbf{H})^k$ ($\theta$-optimal Ritz values, Definition 1.5 there);
* `NLAlib.IsPromisingRitzValue α V d ss r`: the single shift $r$ captures, up to $\alpha^k$, the
  inverse moment of the whole shift polynomial against the last-row weights (Definition 4.3
  there);

and the binary search `NLAlib.findRitz` (the subroutine $\mathrm{Find}$ of §4.3 there), which
halves the list $\log_2 k$ times, keeping the half whose inverse shift polynomial has the larger
last row. All are mathematical objects: norms and inverses are exact, and `NLAlib.findRitz` is a
specification without a cost.

The results: exact Ritz values are $1$-optimal and bounded by the norm; the moment comparison
and almost-monotonicity for a promising Ritz value (Lemma 4.4 there); the binary search returns a
$\kappa_V^{4\log_2 k/k}$-promising Ritz value (Lemma 4.5 there).

## Main definitions

* `NLAlib.IsOptimalRitzValues`, `NLAlib.IsPromisingRitzValue`, `NLAlib.findRitz`.

## Main results

* `NLAlib.length_ritzValues`, `NLAlib.shiftPoly_ritzValues`,
  `NLAlib.IsUpperHessenberg.isOptimalRitzValues_one_ritzValues`,
  `NLAlib.norm_le_specNorm_of_mem_ritzValues`: exact Ritz values.
* `NLAlib.IsOptimalRitzValues.one_le_mul_sum_lastRowWeights_div`: the moment comparison.
* `NLAlib.sum_lastRowWeights_div_pow_two_mul_le`: the second moment of an inverse shift.
* `NLAlib.IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_replicate_le`:
  almost-monotonicity.
* `NLAlib.sum_lastRowWeights_div_norm_eval_shiftPoly_le`, `NLAlib.findRitz_mem`,
  `NLAlib.isPromisingRitzValue_findRitz`: the binary search.
* `NLAlib.exists_perm_forall₂_ritzValues`: a forward-accurate listing of the eigenvalues of the
  trailing block, reordered, is entrywise within $\beta$ of the Ritz values.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- A list `ss` of $k$ shifts is a set of **$\theta$-optimal Ritz values** of $\mathbf{H}$ if
$$\|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})\| \le (\theta\,\psi_k(\mathbf{H}))^k,\qquad
p(z) = \prod_{s \in \mathrm{ss}} (z - s)\,.$$
For upper Hessenberg $\mathbf{H}$ and $k \le n$, $\psi_k(\mathbf{H})^k$ is the minimum of
$\|\mathbf{e}_n^{\mathsf{H}}q(\mathbf{H})\|$ over monic $q$ of degree $k$, attained by the
characteristic polynomial of the trailing block, so this is
[BanksGarzaVargasSrivastava2021, Definition 1.5] with the minimum written out. -/
def IsOptimalRitzValues (θ : ℝ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) :
    Prop :=
  ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss)) (Fin.last n))‖ ≤
    (θ * hessenbergPotential ss.length H) ^ ss.length

/-- A member $r$ of a list `ss` of $k$ shifts is **$\alpha$-promising** for the eigenvector
matrix $\mathbf{V}$ and eigenvalues $\mathbf{d}$ if, with $w$ the last-row weights of
$\mathbf{V}$ and $p(z) = \prod_{s \in \mathrm{ss}} (z - s)$,
$$\sum_i \frac{w_i}{\lvert p(\mathbf{d}_i)\rvert} \le
\alpha^k \sum_i \frac{w_i}{\lvert\mathbf{d}_i - r\rvert^k}\,.$$
It is meaningful when no shift is an eigenvalue (division by zero gives $0$ in Lean); the
theorems assume so. [BanksGarzaVargasSrivastava2021, Definition 4.3], with
$\mathbb{E}\,f(Z_{\mathbf{H}}) = \sum_i w_i f(\mathbf{d}_i)$. -/
def IsPromisingRitzValue (α : ℝ) (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (d : Fin (n + 1) → ℂ) (ss : List ℂ) (r : ℂ) : Prop :=
  r ∈ ss ∧ ∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖ ≤
    α ^ ss.length * ∑ i, lastRowWeights V i / ‖d i - r‖ ^ ss.length

/-- The **binary search for a promising Ritz value** ($\mathrm{Find}$ of
[BanksGarzaVargasSrivastava2021, §4.3]). `findRitz H m e ss` with `ss` of length $2^m$ splits
`ss` into its first and second halves $a$, $b$, keeps the half $h$ with the larger
$\|\mathbf{e}_n^{\mathsf{H}}p_h(\mathbf{H})^{-e}\|$ (the first on a tie), and recurses with
exponent $2e$; after $m$ halvings one shift is left. The strategy calls it with $e = 1$, so
that level $j$ compares degree $2^{m-1}$ polynomials $p_h^{2^{j-1}}$, as in the paper. With
$p_h(\mathbf{H})$ singular the inverse is Lean's junk value; the analysis assumes that no shift
is an eigenvalue.
Algorithm: shifted-qr (specification) -/
noncomputable def findRitz (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ℕ → ℕ → List ℂ → ℂ
  | 0, _, ss => ss.headD 0
  | m + 1, e, ss =>
    if ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly (ss.drop (ss.length / 2))))⁻¹ ^ e)
          (Fin.last n))‖ ≤
        ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly (ss.take (ss.length / 2))))⁻¹ ^ e)
          (Fin.last n))‖ then
      findRitz H m (2 * e) (ss.take (ss.length / 2))
    else
      findRitz H m (2 * e) (ss.drop (ss.length / 2))

/-! ### Exact Ritz values -/

/-- There are $k$ Ritz values: the trailing block is $k \times k$ and its characteristic
polynomial splits over $\mathbb{C}$, so `NLAlib.ritzValues` $k$ $\mathbf{H}$ has length $k$. -/
theorem length_ritzValues (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (ritzValues k H).length = k := by
  unfold ritzValues
  rw [Multiset.length_toList, Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _),
    Matrix.charpoly_natDegree_eq_dim]
  simp

/-- The shift polynomial of the Ritz values is the characteristic polynomial $\chi_k$ of the
trailing block. -/
theorem shiftPoly_ritzValues (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    shiftPoly (ritzValues k H) = (trailingBlock k H).charpoly := by
  rw [shiftPoly, ritzValues, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
  exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Matrix.charpoly_monic _)
    IsAlgClosed.card_roots_eq_natDegree

/-- **Exact Ritz values are $1$-optimal**: for upper Hessenberg $\mathbf{H}$ and $1 \le k \le n$,
the eigenvalues of the trailing block $\mathbf{H}_{(k)}$ satisfy
$\|\mathbf{e}_n^{\mathsf{H}}\chi_k(\mathbf{H})\| \le \psi_k(\mathbf{H})^k$.
[BanksGarzaVargasSrivastava2021, §1.1]: the true Ritz values are $1$-optimal. -/
theorem IsUpperHessenberg.isOptimalRitzValues_one_ritzValues
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) : IsOptimalRitzValues 1 H (ritzValues k H) := by
  rw [IsOptimalRitzValues, shiftPoly_ritzValues, length_ritzValues,
    hH.norm_aeval_charpoly_trailingBlock_eq hk hkn, one_mul]

/-- Ritz values are bounded by the norm: every Ritz value $s$ of order $k \le n + 1$ has
$\lvert s\rvert \le \|\mathbf{H}\|_2$. -/
theorem norm_le_specNorm_of_mem_ritzValues {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ}
    (hkn : k ≤ n + 1) {s : ℂ} (hs : s ∈ ritzValues k H) : ‖s‖ ≤ specNorm H := by
  have hroot : (trailingBlock k H).charpoly.IsRoot s := by
    unfold ritzValues at hs
    exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp (Multiset.mem_toList.mp hs)
  have hspec : s ∈ spectrum ℂ (trailingBlock k H) := Matrix.mem_spectrum_of_isRoot_charpoly hroot
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] at hspec
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hspec
  have hBv : trailingBlock k H *ᵥ v = s • v := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec] at hv
    exact (sub_eq_zero.mp hv).symm
  have hN : 0 < ‖WithLp.toLp 2 v‖ := by
    refine norm_pos_iff.mpr fun h => hv0 ?_
    simpa using h
  have hle : ‖s‖ * ‖WithLp.toLp 2 v‖ ≤ specNorm (trailingBlock k H) * ‖WithLp.toLp 2 v‖ := by
    have h1 := norm_toLp_mulVec_le (trailingBlock k H) v
    rw [hBv] at h1
    simpa [norm_smul] using h1
  have hsub : specNorm (trailingBlock k H) ≤ specNorm H := by
    unfold trailingBlock
    refine specNorm_submatrix_le H (fun a b hab => ?_) (fun a b hab => ?_) <;>
    · simp only [Fin.mk.injEq] at hab
      have ha := a.isLt
      have hb := b.isLt
      exact Fin.ext (by omega)
  exact (le_of_mul_le_mul_right hle hN).trans hsub

/-! ### Promising Ritz values -/

/-- **Moment comparison for a promising Ritz value**: let $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$, $\mathbf{V}$ invertible with
$\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$ and last-row weights $w$, let the $k$ shifts
`ss` be $\theta$-optimal Ritz values of $\mathbf{H}$, none an eigenvalue, and $r$ an
$\alpha$-promising one, $\theta \ge 0$. Then
$$1 \le \kappa\,(\alpha\theta\psi_k(\mathbf{H}))^k\sum_i\frac{w_i}{\lvert\mathbf{d}_i -
r\rvert^k}\,,$$
i.e. $\mathbb{E}\lvert Z_{\mathbf{H}} - r\rvert^{-k} \ge
\kappa^{-1}(\alpha\theta\psi_k(\mathbf{H}))^{-k}$. [BanksGarzaVargasSrivastava2021, Lemma 4.4],
(4.2) there. -/
theorem IsOptimalRitzValues.one_le_mul_sum_lastRowWeights_div {θ α : ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {ss : List ℂ} {r : ℂ}
    (hss : IsOptimalRitzValues θ H ss) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hd : ∀ i, ∀ s ∈ ss, d i ≠ s) (hr : IsPromisingRitzValue α V d ss r) (hθ : 0 ≤ θ) :
    1 ≤ pseudoConditionNumber V * (α * θ * hessenbergPotential ss.length H) ^ ss.length *
      ∑ i, lastRowWeights V i / ‖d i - r‖ ^ ss.length := by
  obtain ⟨-, hr2⟩ := hr
  have hW : ∑ i, lastRowWeights V i = 1 := sum_lastRowWeights hV
  have hκ0 : 0 ≤ pseudoConditionNumber V := pseudoConditionNumber_nonneg V
  have hψ0 : 0 ≤ hessenbergPotential ss.length H :=
    hessenbergPotential_nonneg _ _
  have hne : ∀ i, (shiftPoly ss).eval (d i) ≠ 0 := fun i => eval_shiftPoly_ne_zero (hd i)
  -- the second moment of `p(d)` is at most `(κ (θ ψ)^k)^2`
  have hA := hss
  unfold IsOptimalRitzValues at hA
  rw [aeval_eq_mul_diagonal_mul_inv hV hHV] at hA
  have hm2 : ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ^ 2 ≤
      (pseudoConditionNumber V * (θ * hessenbergPotential ss.length H) ^ ss.length) ^ 2 := by
    have h1 := sum_lastRowWeights_mul_sq_le hV (fun i => (shiftPoly ss).eval (d i))
    calc ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ^ 2
        ≤ _ := h1
      _ ≤ pseudoConditionNumber V ^ 2 *
          ((θ * hessenbergPotential ss.length H) ^ ss.length) ^ 2 := by
        gcongr
      _ = _ := by ring
  -- first moment, by Cauchy–Schwarz
  have hm1 : ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ≤
      pseudoConditionNumber V * (θ * hessenbergPotential ss.length H) ^ ss.length := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun i => lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖)
      (f := fun i => lastRowWeights V i)
      (g := fun i => lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ^ 2)
      (fun i _ => lastRowWeights_nonneg V i)
      (fun i _ => mul_nonneg (lastRowWeights_nonneg V i) (sq_nonneg _))
      (fun i _ => le_of_eq (by ring))
    rw [hW, one_mul] at hcs
    have hnn : 0 ≤ pseudoConditionNumber V * (θ * hessenbergPotential ss.length H) ^ ss.length :=
      mul_nonneg hκ0 (pow_nonneg (mul_nonneg hθ hψ0) _)
    exact le_of_pow_le_pow_left₀ two_ne_zero hnn (hcs.trans hm2)
  -- reciprocal moment, by Cauchy–Schwarz again
  have hrec : 1 ≤ (∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖) *
      ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun i => lastRowWeights V i)
      (f := fun i => lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖)
      (g := fun i => lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖)
      (fun i _ => div_nonneg (lastRowWeights_nonneg V i) (norm_nonneg _))
      (fun i _ => mul_nonneg (lastRowWeights_nonneg V i) (norm_nonneg _))
      (fun i _ => le_of_eq (by
        have : ‖(shiftPoly ss).eval (d i)‖ ≠ 0 := norm_ne_zero_iff.mpr (hne i)
        field_simp))
    rw [hW, one_pow] at hcs
    exact hcs
  have hS0 : 0 ≤ ∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖ :=
    Finset.sum_nonneg fun i _ => div_nonneg (lastRowWeights_nonneg V i) (norm_nonneg _)
  have hK0 : 0 ≤ pseudoConditionNumber V * (θ * hessenbergPotential ss.length H) ^ ss.length :=
    mul_nonneg hκ0 (pow_nonneg (mul_nonneg hθ hψ0) _)
  calc (1 : ℝ)
      ≤ (∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖) *
          ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ := hrec
    _ ≤ (∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖) *
          (pseudoConditionNumber V * (θ * hessenbergPotential ss.length H) ^ ss.length) :=
        mul_le_mul_of_nonneg_left hm1 hS0
    _ ≤ (α ^ ss.length * ∑ i, lastRowWeights V i / ‖d i - r‖ ^ ss.length) *
          (pseudoConditionNumber V * (θ * hessenbergPotential ss.length H) ^ ss.length) :=
        mul_le_mul_of_nonneg_right hr2 hK0
    _ = _ := by simp only [mul_pow]; ring

/-- **The second moment of an inverse shift**: let $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$, $\mathbf{V}$ invertible with
$\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$ and last-row weights $w$, and $r$ no
eigenvalue. Then
$$\sum_i\frac{w_i}{\lvert\mathbf{d}_i - r\rvert^{2k}} \le
\kappa^2\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - r\mathbf{I})^{-k}\|^2\,,$$
i.e. $\mathbb{E}\lvert Z_{\mathbf{H}} - r\rvert^{-2k} \le
\kappa^2\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - r\mathbf{I})^{-k}\|^2$.
[BanksGarzaVargasSrivastava2021, Lemma 4.2], with $f(z) = (z - r)^{-k}$; the paper's
first-moment form $\mathbb{E}\lvert Z_{\mathbf{H}} - r\rvert^{-k} \le
\kappa\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - r\mathbf{I})^{-k}\|$ follows by Jensen. -/
theorem sum_lastRowWeights_div_pow_two_mul_le {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {r : ℂ}
    (hr : ∀ i, d i ≠ r) (k : ℕ) :
    ∑ i, lastRowWeights V i / ‖d i - r‖ ^ (2 * k) ≤ pseudoConditionNumber V ^ 2 *
        ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ k)
          (Fin.last n))‖ ^ 2 := by
  have h := sum_lastRowWeights_mul_sq_le hV (fun i => (d i - r)⁻¹ ^ k)
  rw [← inv_sub_smul_one_pow_eq_mul_diagonal_mul_inv hV hHV hr k] at h
  refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_) h
  rw [norm_pow, norm_inv, inv_pow, inv_pow, ← pow_mul, mul_comm k, div_eq_mul_inv]

/-- The first moment of an inverse shift, by Jensen from the second
(`NLAlib.sum_lastRowWeights_div_pow_two_mul_le`): with $r$ no eigenvalue,
$\sum_i w_i/\lvert\mathbf{d}_i - r\rvert^k \le
\kappa\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - r\mathbf{I})^{-k}\|$. Used by
almost-monotonicity. -/
private theorem sum_lastRowWeights_div_pow_le {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {r : ℂ}
    (hr : ∀ i, d i ≠ r) (k : ℕ) :
    ∑ i, lastRowWeights V i / ‖d i - r‖ ^ k ≤ pseudoConditionNumber V *
        ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ k)
          (Fin.last n))‖ := by
  refine (sq_le_sq₀ (Finset.sum_nonneg fun i _ =>
    div_nonneg (lastRowWeights_nonneg V i) (by positivity))
    (mul_nonneg (pseudoConditionNumber_nonneg V) (norm_nonneg _))).mp ?_
  -- Jensen for `x ↦ x²` against the probability vector `w`
  have hjen := (convexOn_pow 2).map_sum_le (t := Finset.univ) (w := lastRowWeights V)
    (p := fun i => 1 / ‖d i - r‖ ^ k) (fun i _ => lastRowWeights_nonneg V i)
    (sum_lastRowWeights hV) (fun i _ => Set.mem_Ici.mpr (by positivity))
  simp only [smul_eq_mul, div_pow, one_pow, ← pow_mul, mul_comm k 2, mul_one_div] at hjen
  rw [mul_pow]
  exact hjen.trans (sum_lastRowWeights_div_pow_two_mul_le hV hHV hr k)

/-- **Almost-monotonicity of the potential**: in the setting of the moment comparison
(upper Hessenberg $\mathbf{H}$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$
with $\mathbf{V}$ invertible and $\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$; $k$ shifts `ss`,
$1 \le k \le n$, $\theta$-optimal, none an eigenvalue; $r$ an $\alpha$-promising member;
$\alpha, \theta \ge 0$), the degree $k$ step with shift polynomial $(z - r)^k$ satisfies
$$\psi_k(\widehat{\mathbf{H}}) \le \kappa^{2/k}\alpha\theta\,\psi_k(\mathbf{H})\,.$$
[BanksGarzaVargasSrivastava2021, Lemma 4.4]. Not used by the convergence theorem. -/
theorem IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_replicate_le {θ α : ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {d : Fin (n + 1) → ℂ}
    {ss : List ℂ} {r : ℂ} (hss : IsOptimalRitzValues θ H ss) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hd : ∀ i, ∀ s ∈ ss, d i ≠ s)
    (hr : IsPromisingRitzValue α V d ss r) (hk : 0 < ss.length) (hkn : ss.length ≤ n)
    (hα : 0 ≤ α) (hθ : 0 ≤ θ) :
    hessenbergPotential ss.length (multiShiftedQRStep H (List.replicate ss.length r)) ≤
      pseudoConditionNumber V ^ ((2 : ℝ) / ss.length) * α * θ *
        hessenbergPotential ss.length H := by
  set k := ss.length
  set κ := pseudoConditionNumber V
  set ψ := hessenbergPotential k H
  have hdr : ∀ i, d i ≠ r := fun i => hd i r hr.1
  have hκ0 : 0 ≤ κ := pseudoConditionNumber_nonneg V
  have hN := hH.hessenbergPotential_multiShiftedQRStep_replicate_pow_mul_le hk hkn
    (det_sub_smul_one_ne_zero_of_forall_ne hV hHV hdr)
  set N := ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ k)
    (Fin.last n))‖
  have hkey : 1 ≤ κ * (α * θ * ψ) ^ k * (κ * N) :=
    (hss.one_le_mul_sum_lastRowWeights_div hV hHV hd hr hθ).trans
      (mul_le_mul_of_nonneg_left (sum_lastRowWeights_div_pow_le hV hHV hdr k)
        (mul_nonneg hκ0 (pow_nonneg (mul_nonneg (mul_nonneg hα hθ)
          (hessenbergPotential_nonneg _ _)) _)))
  have hN0 : 0 < N := (norm_nonneg _).lt_of_ne fun h => by
    rw [show N = 0 from h.symm, mul_zero, mul_zero] at hkey; linarith
  have hmain : hessenbergPotential k (multiShiftedQRStep H (List.replicate k r)) ^ k ≤
      κ ^ 2 * (α * θ * ψ) ^ k :=
    le_of_mul_le_mul_right (by nlinarith [hN, hkey]) hN0
  have hψ0 : 0 ≤ ψ := hessenbergPotential_nonneg _ _
  have hψ'0 : 0 ≤ hessenbergPotential k (multiShiftedQRStep H (List.replicate k r)) :=
    hessenbergPotential_nonneg _ _
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hκk : (κ ^ ((2 : ℝ) / k)) ^ k = κ ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hκ0]
    have h2 : (2 : ℝ) / k * (k : ℝ) = 2 := by field_simp
    rw [h2]; norm_num
  have hb : 0 ≤ κ ^ ((2 : ℝ) / k) * (α * θ * ψ) :=
    mul_nonneg (Real.rpow_nonneg hκ0 _) (mul_nonneg (mul_nonneg hα hθ) hψ0)
  have hfin : hessenbergPotential k (multiShiftedQRStep H (List.replicate k r)) ^ k ≤
      (κ ^ ((2 : ℝ) / k) * (α * θ * ψ)) ^ k := by
    rw [mul_pow, hκk]; exact hmain
  have hle := (pow_le_pow_iff_left₀ hψ'0 hb hk.ne').mp hfin
  calc _ ≤ κ ^ ((2 : ℝ) / k) * (α * θ * ψ) := hle
    _ = κ ^ ((2 : ℝ) / k) * α * θ * ψ := by ring

/-! ### The binary search -/

/-- The two-sided moment bound for the inverse power `(p(H))⁻¹ ^ q` of a shift polynomial, from
`NLAlib.norm_mul_diagonal_mul_inv_last_sq_le` and `NLAlib.sum_lastRowWeights_mul_sq_le`. -/
private theorem moment_sandwich_shiftPoly {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) (q : ℕ)
    {l : List ℂ} (hl : ∀ i, (shiftPoly l).eval (d i) ≠ 0) :
    ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly l))⁻¹ ^ q) (Fin.last n))‖ ^ 2 ≤
        pseudoConditionNumber V ^ 2 *
          ∑ i, lastRowWeights V i * ‖((shiftPoly l).eval (d i))⁻¹ ^ q‖ ^ 2 ∧
      ∑ i, lastRowWeights V i * ‖((shiftPoly l).eval (d i))⁻¹ ^ q‖ ^ 2 ≤
        pseudoConditionNumber V ^ 2 *
          ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly l))⁻¹ ^ q) (Fin.last n))‖ ^ 2 := by
  have hA : (Polynomial.aeval H (shiftPoly l))⁻¹ ^ q =
      V * Matrix.diagonal (fun i => ((shiftPoly l).eval (d i))⁻¹ ^ q) * V⁻¹ := by
    rw [inv_aeval_eq_mul_diagonal_mul_inv hV hHV hl, mul_diagonal_mul_inv_pow hV]
    rfl
  rw [hA]
  exact ⟨norm_mul_diagonal_mul_inv_last_sq_le hV _, sum_lastRowWeights_mul_sq_le hV _⟩

/-- Reciprocals of a product of powers: $w/(xy)^q$ is at most $w$ times the mean of the squared
inverse powers $(x^{-1})^q$ and $(y^{-1})^q$, for $w \ge 0$. -/
private theorem inv_pow_mul_le (x y w : ℝ) (q : ℕ) (hw : 0 ≤ w) :
    w / (x * y) ^ q ≤ w * (((x⁻¹) ^ q) ^ 2 + ((y⁻¹) ^ q) ^ 2) / 2 := by
  have huv : ((x * y) ^ q)⁻¹ = (x⁻¹) ^ q * (y⁻¹) ^ q := by
    rw [mul_pow, mul_inv, inv_pow, inv_pow]
  have ham : (x⁻¹) ^ q * (y⁻¹) ^ q ≤ (((x⁻¹) ^ q) ^ 2 + ((y⁻¹) ^ q) ^ 2) / 2 := by
    nlinarith [sq_nonneg ((x⁻¹) ^ q - (y⁻¹) ^ q)]
  rw [div_eq_mul_inv, huv]
  nlinarith [mul_le_mul_of_nonneg_left ham hw]

/-- A two-sided moment bound transfers along a maximum: $X_g \le \kappa^2K_g^2$,
$K_g \le K_h$ and $K_h^2 \le \kappa^2X_h$ give $X_g \le \kappa^4X_h$. -/
private theorem moment_le_of_sandwich {κ Kg Kh Xg Xh : ℝ} (hKg0 : 0 ≤ Kg) (hKg : Kg ≤ Kh)
    (hg : Xg ≤ κ ^ 2 * Kg ^ 2) (hh : Kh ^ 2 ≤ κ ^ 2 * Xh) : Xg ≤ κ ^ 4 * Xh :=
  calc Xg ≤ κ ^ 2 * Kg ^ 2 := hg
    _ ≤ κ ^ 2 * Kh ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hKg0 hKg 2) (sq_nonneg _)
    _ ≤ κ ^ 2 * (κ ^ 2 * Xh) := mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = κ ^ 4 * Xh := by ring

/-- **One halving step of the binary search loses at most $\kappa^4$**: let $\mathbf{H}\mathbf{V}
= \mathbf{V}\operatorname{diag}(\mathbf{d})$, $\mathbf{V}$ invertible with
$\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$ and last-row weights $w$; let $a$, $b$ be lists of
shifts, none an eigenvalue, $h \in \{a, b\}$ the one with the larger
$\|\mathbf{e}_n^{\mathsf{H}}p_h(\mathbf{H})^{-q}\|$, and $p_c = p_ap_b$ for $c = a \mathbin{+\!+}
b$. Then
$$\sum_i\frac{w_i}{\lvert p_c(\mathbf{d}_i)\rvert^q} \le \kappa^4\sum_i\frac{w_i}{\lvert
p_h(\mathbf{d}_i)\rvert^{2q}}\,.$$
[BanksGarzaVargasSrivastava2021, proof of Lemma 4.5], one step of the induction (with the squares
the printed chain omits; gap G5 of the design note). -/
theorem sum_lastRowWeights_div_norm_eval_shiftPoly_le
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) {a b h : List ℂ} (hd : ∀ i, ∀ s ∈ a ++ b, d i ≠ s)
    (hh : h = a ∨ h = b) (q : ℕ)
    (hmax : ∀ g ∈ [a, b],
      ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly g))⁻¹ ^ q) (Fin.last n))‖ ≤
        ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ q) (Fin.last n))‖) :
    ∑ i, lastRowWeights V i / ‖(shiftPoly (a ++ b)).eval (d i)‖ ^ q ≤
      pseudoConditionNumber V ^ 4 *
        ∑ i, lastRowWeights V i / ‖(shiftPoly h).eval (d i)‖ ^ (2 * q) := by
  have hne : ∀ l : List ℂ, (∀ i, ∀ s ∈ l, d i ≠ s) → ∀ i, (shiftPoly l).eval (d i) ≠ 0 :=
    fun _ hl i => eval_shiftPoly_ne_zero (hl i)
  have hna : ∀ i, (shiftPoly a).eval (d i) ≠ 0 :=
    hne a fun i s hs => hd i s (List.mem_append_left _ hs)
  have hnb : ∀ i, (shiftPoly b).eval (d i) ≠ 0 :=
    hne b fun i s hs => hd i s (List.mem_append_right _ hs)
  have hnh : ∀ i, (shiftPoly h).eval (d i) ≠ 0 := by
    rcases hh with rfl | rfl
    · exact hna
    · exact hnb
  have hsa := moment_sandwich_shiftPoly hV hHV q hna
  have hsb := moment_sandwich_shiftPoly hV hHV q hnb
  have hsh := moment_sandwich_shiftPoly hV hHV q hnh
  -- pointwise: the reciprocal of `|p_a p_b|^q` is at most the mean of the squared inverse powers
  have hpt : ∀ i, lastRowWeights V i / ‖(shiftPoly (a ++ b)).eval (d i)‖ ^ q ≤
      lastRowWeights V i * (‖((shiftPoly a).eval (d i))⁻¹ ^ q‖ ^ 2 +
        ‖((shiftPoly b).eval (d i))⁻¹ ^ q‖ ^ 2) / 2 := by
    intro i
    rw [shiftPoly_append, Polynomial.eval_mul, norm_mul]
    simp only [norm_pow, norm_inv]
    exact inv_pow_mul_le _ _ _ _ (lastRowWeights_nonneg V i)
  have hsumh : ∑ i, lastRowWeights V i / ‖(shiftPoly h).eval (d i)‖ ^ (2 * q) =
      ∑ i, lastRowWeights V i * ‖((shiftPoly h).eval (d i))⁻¹ ^ q‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_pow, norm_inv, ← pow_mul, inv_pow, div_eq_mul_inv, mul_comm 2 q]
  rw [hsumh]
  obtain ⟨hKa, hXa⟩ := hsa
  obtain ⟨hKb, hXb⟩ := hsb
  obtain ⟨hKh, hXh⟩ := hsh
  have hmaxa : ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly a))⁻¹ ^ q) (Fin.last n))‖ ≤
      ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ q) (Fin.last n))‖ :=
    hmax a (by simp)
  have hmaxb : ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly b))⁻¹ ^ q) (Fin.last n))‖ ≤
      ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ q) (Fin.last n))‖ :=
    hmax b (by simp)
  -- the moment of `a` and `b` is at most `κ⁴` times the moment of `h`
  have hXa' := moment_le_of_sandwich (norm_nonneg _) hmaxa hXa hKh
  have hXb' := moment_le_of_sandwich (norm_nonneg _) hmaxb hXb hKh
  calc ∑ i, lastRowWeights V i / ‖(shiftPoly (a ++ b)).eval (d i)‖ ^ q
      ≤ ∑ i, lastRowWeights V i * (‖((shiftPoly a).eval (d i))⁻¹ ^ q‖ ^ 2 +
          ‖((shiftPoly b).eval (d i))⁻¹ ^ q‖ ^ 2) / 2 := Finset.sum_le_sum fun i _ => hpt i
    _ = (∑ i, lastRowWeights V i * ‖((shiftPoly a).eval (d i))⁻¹ ^ q‖ ^ 2 +
          ∑ i, lastRowWeights V i * ‖((shiftPoly b).eval (d i))⁻¹ ^ q‖ ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ pseudoConditionNumber V ^ 4 *
          ∑ i, lastRowWeights V i * ‖((shiftPoly h).eval (d i))⁻¹ ^ q‖ ^ 2 := by
        linarith

/-- The binary search returns a member: for a list of length $2^m$,
`NLAlib.findRitz` $\mathbf{H}$ $m$ $e$ `ss` is in `ss`. -/
theorem findRitz_mem (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) {m e : ℕ} {ss : List ℂ}
    (hss : ss.length = 2 ^ m) : findRitz H m e ss ∈ ss := by
  induction m generalizing e ss with
  | zero =>
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hss)
    simp [findRitz]
  | succ m ih =>
    have hlen : ss.length / 2 = 2 ^ m := by rw [hss, pow_succ]; omega
    rw [findRitz]
    split_ifs
    · exact List.mem_of_mem_take (ih (by rw [List.length_take, hlen, hss, pow_succ]; omega))
    · exact List.mem_of_mem_drop (ih (by rw [List.length_drop, hss, pow_succ]; omega))

/-- The binary search keeps the moment bound: for a list of length $2^m$ and exponent $e$, the
weighted sum of $\lvert p_{\mathrm{ss}}(\mathbf{d}_i)\rvert^{-e}$ is at most $\kappa^{4m}$ times
the one at the Ritz value `findRitz H m e ss`, with exponent $e2^m$. -/
private theorem sum_lastRowWeights_div_le_findRitz {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) (m : ℕ) :
    ∀ (e : ℕ) (ss : List ℂ), ss.length = 2 ^ m → (∀ i, ∀ s ∈ ss, d i ≠ s) →
      ∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖ ^ e ≤
        pseudoConditionNumber V ^ (4 * m) *
          ∑ i, lastRowWeights V i / ‖d i - findRitz H m e ss‖ ^ (e * 2 ^ m) := by
  induction m with
  | zero =>
    intro e ss hlen hd
    obtain ⟨s, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hlen)
    simp [shiftPoly, findRitz]
  | succ j ih =>
    intro e ss hlen hd
    set a := ss.take (ss.length / 2)
    set b := ss.drop (ss.length / 2)
    have hhalf : ss.length / 2 = 2 ^ j := by
      rw [hlen, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have ha : a.length = 2 ^ j := by
      rw [List.length_take, hhalf, hlen]
      exact Nat.min_eq_left (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hb : b.length = 2 ^ j := by
      rw [List.length_drop, hhalf, hlen, pow_succ]
      omega
    have hdis : ∀ i, ∀ s ∈ a ++ b, d i ≠ s := by simpa only [a, b, List.take_append_drop] using hd
    -- the half `h` that the search keeps
    obtain ⟨h, hh, hlh, hfr, hmax⟩ : ∃ h : List ℂ, (h = a ∨ h = b) ∧ h.length = 2 ^ j ∧
        findRitz H (j + 1) e ss = findRitz H j (2 * e) h ∧ ∀ g ∈ [a, b],
          ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly g))⁻¹ ^ e) (Fin.last n))‖ ≤
            ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly h))⁻¹ ^ e) (Fin.last n))‖ := by
      by_cases hc : ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly b))⁻¹ ^ e) (Fin.last n))‖ ≤
          ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly a))⁻¹ ^ e) (Fin.last n))‖
      · refine ⟨a, Or.inl rfl, ha, by rw [findRitz, if_pos hc], fun g hg => ?_⟩
        rcases List.mem_pair.mp hg with rfl | rfl
        exacts [le_rfl, hc]
      · refine ⟨b, Or.inr rfl, hb, by rw [findRitz, if_neg hc], fun g hg => ?_⟩
        rcases List.mem_pair.mp hg with rfl | rfl
        exacts [(not_le.mp hc).le, le_rfl]
    have hih := ih (2 * e) h hlh fun i s hs =>
      hdis i s (by rcases hh with rfl | rfl <;> simp [hs])
    rw [show ∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖ ^ e =
        ∑ i, lastRowWeights V i / ‖(shiftPoly (a ++ b)).eval (d i)‖ ^ e by
      rw [List.take_append_drop], hfr, show e * 2 ^ (j + 1) = 2 * e * 2 ^ j by ring]
    calc _ ≤ _ := sum_lastRowWeights_div_norm_eval_shiftPoly_le hV hHV hdis hh e hmax
      _ ≤ pseudoConditionNumber V ^ 4 * (pseudoConditionNumber V ^ (4 * j) *
          ∑ i, lastRowWeights V i / ‖d i - findRitz H j (2 * e) h‖ ^ (2 * e * 2 ^ j)) :=
        mul_le_mul_of_nonneg_left hih (by positivity)
      _ = _ := by ring

/-- **The binary search finds a promising Ritz value**: let $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$, $\mathbf{V}$ invertible with
$\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$, and `ss` a list of $k = 2^m$ shifts, none an
eigenvalue. If $\kappa^{4m} \le \alpha^k$, then `NLAlib.findRitz` $\mathbf{H}$ $m$ $1$ `ss` is an
$\alpha$-promising member of `ss`: $\sum_i w_i/\lvert p(\mathbf{d}_i)\rvert \le
\alpha^k\sum_i w_i/\lvert\mathbf{d}_i - r\rvert^k$. In particular
$\alpha = \kappa^{4\log_2 k/k}$ works. [BanksGarzaVargasSrivastava2021, Lemma 4.5]. -/
theorem isPromisingRitzValue_findRitz {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {m : ℕ}
    {ss : List ℂ} (hlen : ss.length = 2 ^ m) (hd : ∀ i, ∀ s ∈ ss, d i ≠ s) {α : ℝ}
    (hα : pseudoConditionNumber V ^ (4 * m) ≤ α ^ 2 ^ m) :
    IsPromisingRitzValue α V d ss (findRitz H m 1 ss) := by
  have hcard := sum_lastRowWeights_div_le_findRitz hV hHV m 1 ss hlen hd
  simp only [pow_one, one_mul] at hcard
  have hS0 : 0 ≤ ∑ i, lastRowWeights V i / ‖d i - findRitz H m 1 ss‖ ^ 2 ^ m :=
    Finset.sum_nonneg fun i _ => div_nonneg (lastRowWeights_nonneg V i) (by positivity)
  unfold IsPromisingRitzValue
  refine ⟨findRitz_mem H hlen, ?_⟩
  rw [hlen]
  calc _ ≤ _ := hcard
    _ ≤ α ^ 2 ^ m * ∑ i, lastRowWeights V i / ‖d i - findRitz H m 1 ss‖ ^ 2 ^ m :=
        mul_le_mul_of_nonneg_right hα hS0

/-! ### Approximate Ritz values in the order of `NLAlib.ritzValues`

An eigenvalue routine with forward error $\beta$ returns the Ritz values in its own order; the
strategy lemmas take them matched entry by entry with `NLAlib.ritzValues`. -/

/-- **Forward-approximate Ritz values in the order of `NLAlib.ritzValues`**: if `ev` is within
$\beta$ of a listing `lam` of the eigenvalues (with multiplicity) of the trailing $k \times k$ block
of $\mathbf{H}$, some reordering of `ev` is entrywise within $\beta$ of the Ritz values of order
$k$. -/
theorem exists_perm_forall₂_ritzValues {k : ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {ev lam : Fin k → ℂ} {β : ℝ} (hlam : IsEigenvalueListing (trailingBlock k H) lam)
    (hev : ∀ i, ‖ev i - lam i‖ ≤ β) :
    ∃ ss : List ℂ, ss.Perm (List.ofFn ev) ∧
      List.Forall₂ (fun r ρ => ‖r - ρ‖ ≤ β) ss (ritzValues k H) := by
  have hroots : (trailingBlock k H).charpoly.roots = (List.ofFn lam : Multiset ℂ) := by
    rw [isEigenvalueListing_iff.mp hlam]
    simpa only [Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
      List.prod_ofFn, Function.comp_def] using
      Polynomial.roots_multiset_prod_X_sub_C (List.ofFn lam : Multiset ℂ)
  have hperm : (ritzValues k H).Perm (List.ofFn lam) := by
    rw [← Multiset.coe_eq_coe, ritzValues, Multiset.coe_toList, hroots]
  have hpair : List.Forall₂ (flip fun r ρ : ℂ => ‖r - ρ‖ ≤ β) (List.ofFn lam) (List.ofFn ev) :=
    List.forall₂_iff_get.mpr
      ⟨by simp, fun i h1 _ => by simpa [flip] using hev ⟨i, by simpa using h1⟩⟩
  obtain ⟨ss, hss, hssp⟩ := List.perm_comp_forall₂ hperm hpair
  exact ⟨ss, hssp, hss.flip⟩

/-- An eigenvalue of the trailing $k \times k$ block, $k \le n + 1$, is at most
$\|\mathbf{H}\|_2$. -/
theorem IsEigenvalueListing.norm_le_specNorm_of_trailingBlock {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {lam : Fin k → ℂ}
    (hlam : IsEigenvalueListing (trailingBlock k H) lam) (hkn : k ≤ n + 1) (j : Fin k) :
    ‖lam j‖ ≤ specNorm H := by
  have hroots := hlam.charpoly_roots_eq_ofFn
  refine norm_le_specNorm_of_mem_ritzValues hkn ?_
  rw [ritzValues, Multiset.mem_toList, hroots, Multiset.mem_coe]
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

/-- The trailing $k \times k$ block, $k \le n + 1$, has spectral norm at most
$\|\mathbf{H}\|_2$. -/
theorem specNorm_trailingBlock_le {k : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hkn : k ≤ n + 1) : specNorm (trailingBlock k H) ≤ specNorm H := by
  have hinj : Function.Injective fun i : Fin k =>
      (⟨min (n + 1 - k + i) n, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (n + 1)) := by
    intro i j h
    simp only [Fin.mk.injEq] at h
    ext
    omega
  exact specNorm_submatrix_le H hinj hinj

end NLAlib
