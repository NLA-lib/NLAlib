/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Schur
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber

/-!
# Forward and backward eigenvalue errors

**Forward error implies backward error**: if every computed value is within $\beta$ of the
eigenvalue it lists, the computed values are exactly the eigenvalues of a matrix within $\beta$
in the spectral norm. Schur triangularization with the listing in its order puts the eigenvalues
on the diagonal of a triangular matrix; replacing that diagonal moves the matrix by a diagonal
matrix of norm at most $\beta$. This is how a small-eigenvalue solver with a forward guarantee
[BanksGarzaVargasSrivastava2022, Definition 1.2] enters a backward-error statement (proof of
Theorem 6.3 there). [HornJohnson2013, Theorem 2.3.1].

**Separation after a perturbation**: for a diagonalizable matrix with eigenvector condition number
at most $B$ and eigenvalues at mutual distance at least $g$, a perturbation of norm at most
$g / (16 N B)$ ($N$ the order) keeps a diagonalization with condition number at most $2B$
(`NLAlib.exists_pseudoConditionNumber_add_le`) and eigenvalues at mutual distance at least
$g - 2B\|\mathbf{E}\|_2$ (Bauer–Fike, with the disks of radius $B\|\mathbf{E}\|_2$ disjoint).
This replaces [BanksGarzaVargasSrivastava2022, Lemma 6.1], whose hypothesis
$\|\mathbf{E}\|_2 \le \mathrm{gap}/(8n^2\kappa_V^3)$ the algorithm's working accuracy violates for
$B > 32$ (G18).

## Main results

* `NLAlib.IsEigenvalueListing.exists_specNorm_sub_le`: forward implies backward.
* `NLAlib.exists_pseudoConditionNumber_le_and_le_norm_sub`: conditioning and separation after a
  perturbation.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **Forward eigenvalue error implies backward error**: if $\mathbf{d}$ lists the eigenvalues of
$\mathbf{L}$, $\beta \ge 0$ and $\lvert\mu_i - d_i\rvert \le \beta$ for every $i$, then $\mu$ lists
the eigenvalues of some $\mathbf{L}'$ with $\|\mathbf{L}' - \mathbf{L}\|_2 \le \beta$.
[HornJohnson2013, Theorem 2.3.1]; [BanksGarzaVargasSrivastava2022, proof of Theorem 6.3].

Proof: Schur with the listing order, $\mathbf{U}^{\mathsf{H}}\mathbf{L}\mathbf{U}$ upper triangular
with diagonal $\mathbf{d}$; take $\mathbf{L}' = \mathbf{L} +
\mathbf{U}\operatorname{diag}(\mu - \mathbf{d})\mathbf{U}^{\mathsf{H}}$. The hypothesis
$\beta \ge 0$ matters only for $m = 0$. -/
theorem IsEigenvalueListing.exists_specNorm_sub_le {m : ℕ} {L : Matrix (Fin m) (Fin m) ℂ}
    {d μ : Fin m → ℂ} {β : ℝ} (hd : IsEigenvalueListing L d) (hβ0 : 0 ≤ β)
    (hβ : ∀ i, ‖μ i - d i‖ ≤ β) :
    ∃ L' : Matrix (Fin m) (Fin m) ℂ, specNorm (L' - L) ≤ β ∧ IsEigenvalueListing L' μ := by
  obtain ⟨U, hU, hT, hdiag⟩ := hd.exists_hasOrthonormalCols_isUpperTriangular
  set D := Matrix.diagonal (μ - d)
  have hUU : Uᴴ * U = 1 := hU.conjTranspose_mul_self
  have hconj : Uᴴ * (L + U * D * Uᴴ) * U = Uᴴ * L * U + D := by
    simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    rw [Matrix.mul_assoc _ Uᴴ U, hUU, Matrix.mul_one]
  refine ⟨L + U * D * Uᴴ, ?_, ?_⟩
  · rw [add_sub_cancel_left, hU.specNorm_mul_conjTranspose_right, hU.specNorm_mul_left]
    exact specNorm_diagonal_le hβ0 hβ
  · have hT' : (Uᴴ * (L + U * D * Uᴴ) * U).IsUpperTriangular := by
      rw [hconj]
      intro i j hij
      have hij' : j < i := hij
      simp only [Matrix.add_apply, hT hij, D, zero_add]
      exact Matrix.diagonal_apply_ne _ (ne_of_gt hij')
    have h := hU.isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul hT'
    have hfun : (fun i => (Uᴴ * (L + U * D * Uᴴ) * U) i i) = μ := by
      funext i
      rw [hconj]
      simp [D, hdiag i]
    rwa [hfun] at h

/-- **Eigenvalue separation after a perturbation** (Bauer–Fike with disjoint disks): for
$\mathbf{A}\mathbf{V} = \mathbf{V}\mathbf{D}$, $\kappa(\mathbf{V}) \le B$, eigenvalues at mutual
distance at least $g > 0$ and $\|\mathbf{E}\|_2 \le g / (16(n + 1)B)$, the perturbed matrix has a
diagonalization $\mathbf{V}'$, $\mathbf{d}'$ with $\kappa(\mathbf{V}') \le 2B$ and eigenvalues at
mutual distance at least $g - 2B\|\mathbf{E}\|_2$. [BauerFike1960, Theorem IIIa];
[BanksGarzaVargasSrivastava2022, Lemma 6.1]. -/
theorem exists_pseudoConditionNumber_le_and_le_norm_sub {n : ℕ}
    {A V E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {B g : ℝ}
    (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d) (hB : pseudoConditionNumber V ≤ B)
    (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hE : specNorm E ≤ g / (16 * (n + 1) * B)) :
    ∃ (V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d' : Fin (n + 1) → ℂ), IsUnit V' ∧
      (A + E) * V' = V' * Matrix.diagonal d' ∧ pseudoConditionNumber V' ≤ 2 * B ∧
      ∀ i j, i ≠ j → g - 2 * B * specNorm E ≤ ‖d' i - d' j‖ := by
  sorry

end NLAlib
