/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.EigenvalueBackward
public import NLAlib.Matrix.Spectral.EigenvalueListing

/-!
# Matchings of the eigenvalues of nearby matrices

For any two complex matrices of order $N = n + 1$ there is a matching of their eigenvalues, with
multiplicity, at distance at most $(2N - 1)(\|\mathbf{A}\|_2 + \|\mathbf{A}'\|_2)^{1 - 1/N}
\|\mathbf{A}' - \mathbf{A}\|_2^{1/N}$ (the Ostrowski–Elsner theorem, with the constant of the
component argument; [BhatiaElsnerKrause1990] has $4$). The proof is by compactness: eigenvalue
listings move continuously up to a permutation along a converging sequence of matrices, every
eigenvalue of $\mathbf{A}'$ is close to one of $\mathbf{A}$ (Elsner's bound), and along the segment
from $\mathbf{A}$ to $\mathbf{A}'$ the count of eigenvalues in each connected component of the
union of the disks is constant. Through a diagonalizable matrix with a conditioned eigenvector
matrix and separated eigenvalues the matching is linear in the perturbation
(`NLAlib.norm_sub_le_of_matching`), which gives the forward error of an eigenvalue solver with a
backward guarantee: the root of the order is paid only on the part of the perturbation that
leaves the class. [BanksGarzaVargasSrivastava2025]

## Main results

* `NLAlib.exists_tendsto_isEigenvalueListing`: continuity of listings up to a permutation.
* `NLAlib.norm_det_smul_one_sub_le_of_mem_spectrum`,
  `NLAlib.exists_norm_sub_le_rpow_of_mem_spectrum`: Elsner's bound for one eigenvalue.
* `NLAlib.exists_isEigenvalueListing_norm_sub_le_rpow`: the Ostrowski–Elsner matching.
* `NLAlib.exists_isEigenvalueListing_norm_sub_le_of_class`: the matching through a
  diagonalizable matrix.
-/

@[expose] public section

open Filter Topology
open scoped Matrix

namespace NLAlib

/-- Eigenvalue listings are continuous up to a permutation: if the complex matrices
$\mathbf{A}_j$ of order $n$ tend to $\mathbf{A}$ and $\boldsymbol{\lambda}_j$ lists the
eigenvalues of $\mathbf{A}_j$ with multiplicity, then along a subsequence and after permuting each
listing they converge to a listing of the eigenvalues of $\mathbf{A}$. No printed source. -/
theorem exists_tendsto_isEigenvalueListing {n : ℕ} {A : ℕ → Matrix (Fin n) (Fin n) ℂ}
    {A₀ : Matrix (Fin n) (Fin n) ℂ} (hA : Tendsto A atTop (𝓝 A₀)) {ev : ℕ → Fin n → ℂ}
    (hev : ∀ j, IsEigenvalueListing (A j) (ev j)) :
    ∃ (φ : ℕ → ℕ) (σ : ℕ → Equiv.Perm (Fin n)) (e : Fin n → ℂ), StrictMono φ ∧
      IsEigenvalueListing A₀ e ∧ Tendsto (fun j => ev (φ j) ∘ σ j) atTop (𝓝 e) := by
  -- the listings lie in a compact box, since `‖ev j i‖ ≤ ‖A j‖₂` and `‖A j‖₂` is bounded
  obtain ⟨M, hM⟩ := ((continuous_specNorm.tendsto A₀).comp hA).bddAbove_range
  have hmem : ∀ j, ev j ∈ Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) M :=
    fun j i _ => mem_closedBall_zero_iff.mpr <| (norm_le_specNorm_of_mem_spectrum
      ((hev j).spectrum_eq_range ▸ Set.mem_range_self i)).trans (hM ⟨j, rfl⟩)
  obtain ⟨e, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) M).tendsto_subseq hmem
  -- no relabelling is needed; the limit is a listing because listings form a closed relation
  refine ⟨φ, fun _ => Equiv.refl _, e, hφ, ?_, hlim⟩
  exact isClosed_setOf_isEigenvalueListing.mem_of_tendsto
    ((hA.comp hφ.tendsto_atTop).prodMk_nhds hlim) (Eventually.of_forall fun j => hev (φ j))

/-- The determinant step of Elsner's bound: if $\mu$ is an eigenvalue of the complex matrix
$\mathbf{A}'$ of order $n + 1$, then for every $\mathbf{A}$ of the same order
$$\lvert\det(\mu\mathbf{I} - \mathbf{A})\rvert \le \|\mathbf{A}' - \mathbf{A}\|_2\,
  (\|\mathbf{A}\|_2 + \|\mathbf{A}'\|_2)^n.$$ -/
theorem norm_det_smul_one_sub_le_of_mem_spectrum {n : ℕ}
    {A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ A') :
    ‖(μ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - A).det‖ ≤
      specNorm (A' - A) * (specNorm A + specNorm A') ^ n := by
  -- a Schur form of `A'` with `μ` first: `Uᴴ A' U = T` upper triangular, `T₀₀ = μ`
  obtain ⟨d, hd⟩ := exists_isEigenvalueListing A'
  obtain ⟨k, hk⟩ : μ ∈ Set.range d := hd.spectrum_eq_range ▸ hμ
  obtain ⟨U, hU, hT, hdiag⟩ :=
    (hd.comp_equiv (Equiv.swap 0 k)).exists_hasOrthonormalCols_isUpperTriangular
  set T := Uᴴ * A' * U
  set M := Uᴴ * (μ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - A) * U
  have hUU : Uᴴ * U = 1 := hU
  have hdet : M.det = (μ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - A).det := by
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm (Uᴴ.det), mul_assoc, ← Matrix.det_mul, hUU,
      Matrix.det_one, mul_one]
  have hM : M = (μ • 1 - T) + Uᴴ * (A' - A) * U := by
    simp only [M, T, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hUU]
    abel
  -- the first column of `M` is that of `Uᴴ (A' - A) U`
  have hcol0 : M.col 0 = (Uᴴ * (A' - A) * U).col 0 := by
    ext i
    rw [hM]
    simp only [Matrix.col_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, add_eq_right, sub_eq_zero]
    rcases eq_or_ne i 0 with rfl | hi
    · rw [hdiag, Function.comp_apply, Equiv.swap_apply_left, hk, if_pos rfl, mul_one]
    · rw [if_neg hi, mul_zero, hT (Fin.pos_iff_ne_zero.mpr hi)]
  have hS : specNorm M ≤ specNorm A + specNorm A' := by
    have hμT : ‖μ‖ ≤ specNorm A' := by
      have h := norm_apply_le_specNorm T 0 0
      rwa [hdiag, Function.comp_apply, Equiv.swap_apply_left, hk,
        hU.specNorm_conjTranspose_mul_mul] at h
    rw [hU.specNorm_conjTranspose_mul_mul]
    refine (specNorm_sub_le _ _).trans ?_
    rw [specNorm_smul, specNorm_one, mul_one]
    linarith
  rw [← hdet]
  refine (norm_det_le_prod_norm_col M).trans ?_
  rw [Fin.prod_univ_succ, hcol0]
  refine mul_le_mul ((norm_toLp_col_le_specNorm _ 0).trans
    (hU.specNorm_conjTranspose_mul_mul _).le) ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (specNorm_nonneg _)
  calc ∏ i : Fin n, ‖WithLp.toLp 2 (M.col i.succ)‖
      ≤ ∏ _i : Fin n, (specNorm A + specNorm A') :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          fun i _ => (norm_toLp_col_le_specNorm M i.succ).trans hS
    _ = (specNorm A + specNorm A') ^ n := by rw [Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

/-- Every eigenvalue $\mu$ of a complex matrix $\mathbf{A}'$ of order $n + 1$ is within
$$(\|\mathbf{A}\|_2 + \|\mathbf{A}'\|_2)^{1 - 1/(n + 1)}\,
  \|\mathbf{A}' - \mathbf{A}\|_2^{1/(n + 1)}$$
of an eigenvalue of $\mathbf{A}$ (Elsner's bound): the step of the Ostrowski–Elsner matching for
one eigenvalue. -/
theorem exists_norm_sub_le_rpow_of_mem_spectrum {n : ℕ}
    {A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ A') :
    ∃ ν ∈ spectrum ℂ A, ‖μ - ν‖ ≤ (specNorm A + specNorm A') ^ (1 - 1 / ((n : ℝ) + 1)) *
      specNorm (A' - A) ^ (1 / ((n : ℝ) + 1)) := by
  obtain ⟨ev, hev⟩ := exists_isEigenvalueListing A
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => ‖μ - ev i‖)
    Finset.univ_nonempty
  refine ⟨ev i, hev.spectrum_eq_range ▸ Set.mem_range_self i, ?_⟩
  set S := specNorm A + specNorm A'
  set δ := ‖μ - ev i‖
  have hS : 0 ≤ S := add_nonneg (specNorm_nonneg _) (specNorm_nonneg _)
  have hE : 0 ≤ specNorm (A' - A) := specNorm_nonneg _
  -- `δ^(n+1) ≤ ∏ ‖μ - ev j‖ = ‖det(μ I - A)‖ ≤ ‖A' - A‖ S^n`
  have hpow : δ ^ (n + 1) ≤ specNorm (A' - A) * S ^ n := by
    have hdet : (μ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - A).det = ∏ j, (μ - ev j) := by
      have h := congrArg (Polynomial.eval μ) hev
      rw [Matrix.eval_charpoly, Polynomial.eval_prod, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal] at h
      simpa only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using h
    refine le_trans ?_ (norm_det_smul_one_sub_le_of_mem_spectrum (A := A) hμ)
    rw [hdet, norm_prod]
    calc δ ^ (n + 1) = ∏ _j : Fin (n + 1), δ := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ j, ‖μ - ev j‖ :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => hi j (Finset.mem_univ j)
  have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
  calc δ = (δ ^ (n + 1)) ^ (1 / ((n : ℝ) + 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        push_cast
        rw [mul_one_div_cancel hN, Real.rpow_one]
    _ ≤ (specNorm (A' - A) * S ^ n) ^ (1 / ((n : ℝ) + 1)) :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = S ^ (1 - 1 / ((n : ℝ) + 1)) * specNorm (A' - A) ^ (1 / ((n : ℝ) + 1)) := by
        rw [Real.mul_rpow hE (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hS, mul_comm]
        congr 2
        field_simp
        ring

/-- **The Ostrowski–Elsner matching** ([BanksGarzaVargasSrivastava2025, Lemma 1.2]; the constant
$2N - 1$ of the component argument at the order $N = n + 1$, where Bhatia, Elsner and Krause
have $4$): for complex matrices $\mathbf{A}, \mathbf{A}'$ of order $n + 1$ and every listing
$\boldsymbol{\lambda}$ of the eigenvalues of $\mathbf{A}$ there is a listing
$\boldsymbol{\lambda}'$ of those of $\mathbf{A}'$ with, for every $i$,
$$\lvert\lambda'_i - \lambda_i\rvert \le
  (2n + 1)(\|\mathbf{A}\|_2 + \|\mathbf{A}'\|_2)^{1 - 1/(n + 1)}
  \|\mathbf{A}' - \mathbf{A}\|_2^{1/(n + 1)}.$$ -/
theorem exists_isEigenvalueListing_norm_sub_le_rpow {n : ℕ}
    {A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {ev : Fin (n + 1) → ℂ}
    (hev : IsEigenvalueListing A ev) :
    ∃ ev' : Fin (n + 1) → ℂ, IsEigenvalueListing A' ev' ∧ ∀ i,
      ‖ev' i - ev i‖ ≤ (2 * n + 1) * (specNorm A + specNorm A') ^ (1 - 1 / ((n : ℝ) + 1)) *
        specNorm (A' - A) ^ (1 / ((n : ℝ) + 1)) := by
  sorry

/-- **The forward error through a diagonalizable matrix** ([BanksGarzaVargasSrivastava2025,
Corollary 1.3], the matching step): let $\mathbf{A} + \mathbf{E}_1 = \mathbf{V}
\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}$ with $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$
and eigenvalues separated by $g > 0$, and $\|\mathbf{E}_2\|_2 \le g/(16(n + 1)B)$. Then every
listing $\mathbf{r}$ of the eigenvalues of $\mathbf{A} + \mathbf{E}_1 + \mathbf{E}_2$ is matched
to a listing $\boldsymbol{\lambda}$ of those of $\mathbf{A}$ with, for every $i$,
$$\lvert r_i - \lambda_i\rvert \le B\|\mathbf{E}_2\|_2 + (2n + 1)(2\|\mathbf{A}\|_2 +
  \|\mathbf{E}_1\|_2)^{1 - 1/(n + 1)}\|\mathbf{E}_1\|_2^{1/(n + 1)}.$$ -/
theorem exists_isEigenvalueListing_norm_sub_le_of_class {n : ℕ}
    {A E₁ E₂ V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {B g : ℝ}
    (hV : IsUnit V) (hAV : (A + E₁) * V = V * Matrix.diagonal d)
    (hB : pseudoConditionNumber V ≤ B) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hE₂ : specNorm E₂ ≤ g / (16 * (n + 1) * B)) {roots : Fin (n + 1) → ℂ}
    (hroots : IsEigenvalueListing (A + E₁ + E₂) roots) :
    ∃ ev : Fin (n + 1) → ℂ, IsEigenvalueListing A ev ∧ ∀ i,
      ‖roots i - ev i‖ ≤ B * specNorm E₂ + (2 * n + 1) *
        (2 * specNorm A + specNorm E₁) ^ (1 - 1 / ((n : ℝ) + 1)) *
          specNorm E₁ ^ (1 / ((n : ℝ) + 1)) := by
  sorry

end NLAlib
