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
* `NLAlib.exists_norm_sub_le_rpow_of_mem_spectrum`: Elsner's bound for one eigenvalue.
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
  sorry

/-- Every eigenvalue $\mu$ of a complex matrix $\mathbf{A}'$ of order $n + 1$ is within
$$(\|\mathbf{A}\|_2 + \|\mathbf{A}'\|_2)^{1 - 1/(n + 1)}\,
  \|\mathbf{A}' - \mathbf{A}\|_2^{1/(n + 1)}$$
of an eigenvalue of $\mathbf{A}$ (Elsner's bound): the step of the Ostrowski–Elsner matching for
one eigenvalue. -/
theorem exists_norm_sub_le_rpow_of_mem_spectrum {n : ℕ}
    {A A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {μ : ℂ} (hμ : μ ∈ spectrum ℂ A') :
    ∃ ν ∈ spectrum ℂ A, ‖μ - ν‖ ≤ (specNorm A + specNorm A') ^ (1 - 1 / ((n : ℝ) + 1)) *
      specNorm (A' - A) ^ (1 / ((n : ℝ) + 1)) := by
  sorry

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
