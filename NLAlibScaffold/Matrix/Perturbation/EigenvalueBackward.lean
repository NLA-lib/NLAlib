/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Schur
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Perturbation.Residual
public import NLAlib.Matrix.QRIteration.DeflationConditioning

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
* `NLAlib.norm_sub_le_of_matching`: Bauer–Fike refines a matching within $g/16$ to one within
  $B\|\mathbf{E}\|_2$.
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

/-- **Bauer–Fike with a matching**: under the hypotheses of
`NLAlib.exists_pseudoConditionNumber_le_and_le_norm_sub`, a diagonalization $\mathbf{V}'$,
$\mathbf{d}'$ of $\mathbf{A} + \mathbf{E}$ with $\lvert d'_i - d_i\rvert \le g/16$ has
$\lvert d'_i - d_i\rvert \le B\|\mathbf{E}\|_2$: Bauer–Fike puts $d'_i$ within
$B\|\mathbf{E}\|_2 \le g/16$ of some $d_k$, and $k = i$ since $\lvert d_k - d_i\rvert < g$. -/
theorem norm_sub_le_of_matching {n : ℕ}
    {A V E V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d d' : Fin (n + 1) → ℂ} {B g : ℝ}
    (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d) (hB : pseudoConditionNumber V ≤ B)
    (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hE : specNorm E ≤ g / (16 * (n + 1) * B)) (hV' : IsUnit V')
    (hAV' : (A + E) * V' = V' * Matrix.diagonal d') (hm : ∀ i, ‖d' i - d i‖ ≤ g / 16)
    (i : Fin (n + 1)) :
    ‖d' i - d i‖ ≤ B * specNorm E := by
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hB
  have hN : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hBE : B * specNorm E ≤ g / 16 := by
    calc B * specNorm E ≤ B * (g / (16 * (n + 1) * B)) := by gcongr
      _ = g / (16 * (n + 1)) := by field_simp
      _ ≤ g / 16 := by gcongr; linarith
  have hcol : V'.col i ≠ 0 := (Matrix.linearIndependent_cols_iff_isUnit.mpr hV').ne_zero i
  have hAi : (A + E) *ᵥ V'.col i = d' i • V'.col i := by
    funext j
    have h := congrFun (congrFun hAV' j) i
    rw [Matrix.mul_diagonal] at h
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    exact h
  obtain ⟨k, hk⟩ := exists_norm_sub_le_pseudoConditionNumber_mul_specNorm hV hAV hcol hAi
  have hk' : ‖d k - d' i‖ ≤ B * specNorm E :=
    hk.trans (mul_le_mul_of_nonneg_right hB (specNorm_nonneg _))
  by_cases hki : k = i
  · rw [hki, norm_sub_rev] at hk'
    exact hk'
  · have h3 : ‖d k - d i‖ ≤ ‖d k - d' i‖ + ‖d' i - d i‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    linarith [hgap k i hki, hm i]

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
  obtain ⟨V', d', hV', hAV', -, hκ, hm⟩ :=
    exists_pseudoConditionNumber_add_le_and_norm_sub_le hV hAV hB hg hgap hE
  refine ⟨V', d', hV', hAV', hκ, fun i j hij => ?_⟩
  have hi := norm_sub_le_of_matching hV hAV hB hg hgap hE hV' hAV' hm i
  have hj := norm_sub_le_of_matching hV hAV hB hg hgap hE hV' hAV' hm j
  have h3 : ‖d i - d j‖ ≤ ‖d' i - d' j‖ + ‖d' i - d i‖ + ‖d' j - d j‖ := by
    calc ‖d i - d j‖ = ‖(d' i - d' j) - (d' i - d i) + (d' j - d j)‖ := by ring_nf
      _ ≤ _ := (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
  linarith [hgap i j hij]

end NLAlib
