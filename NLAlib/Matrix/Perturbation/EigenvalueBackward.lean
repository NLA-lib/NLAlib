/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Schur
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Perturbation.Residual
public import NLAlib.Matrix.Perturbation.UnitarySimilarity
public import NLAlib.Matrix.QRIteration.DeflationConditioning
public import NLAlib.Matrix.QRIteration.EigenvectorWeights

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
This is a form of [BanksGarzaVargasSrivastava2022, Lemma 6.1], whose hypothesis is
$\|\mathbf{E}\|_2 \le \mathrm{gap}/(8n^2\kappa_V^3)$; the working accuracy of that paper's
algorithm does not meet it for $B > 32$, and its proof needs only $\kappa_V^2$.

## Main results

* `NLAlib.IsEigenvalueListing.exists_specNorm_sub_le`: forward implies backward.
* `NLAlib.exists_pseudoConditionNumber_le_and_le_norm_sub`: conditioning and separation after a
  perturbation.
* `NLAlib.IsPerturbedUnitarySimilar.exists_pseudoConditionNumber_le_and_le_norm_sub`: the same
  along a perturbed unitary similarity, with the class constants doubled once.
* `NLAlib.norm_sub_le_of_matching`: Bauer–Fike refines a matching within $g/16$ to one within
  $B\|\mathbf{E}\|_2$.
* `NLAlib.exists_lastRowWeights_ge_of_norm_sub_le`: the last-row weights after a perturbation
  [BanksGarzaVargasSrivastava2025].
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **Forward eigenvalue error implies backward error**: if $\mathbf{d}$ lists the eigenvalues of
$\mathbf{L}$, $\beta \ge 0$ and $\lvert\mu_i - d_i\rvert \le \beta$ for every $i$, then $\mu$ lists
the eigenvalues of some $\mathbf{L}'$ with $\|\mathbf{L}' - \mathbf{L}\|_2 \le \beta$.
The hypothesis $\beta \ge 0$ matters only for $m = 0$.
[HornJohnson2013, Theorem 2.3.1]; [BanksGarzaVargasSrivastava2022, proof of Theorem 6.3]. -/
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

/-- Bauer–Fike with a matching: let $\mathbf{A}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$, eigenvalues at mutual distance at least $g > 0$ and
$\|\mathbf{E}\|_2 \le g/(16(n + 1)B)$ for order $n + 1$. A diagonalization $(\mathbf{A} +
\mathbf{E})\mathbf{V}' = \mathbf{V}'\operatorname{diag}(\mathbf{d}')$, $\mathbf{V}'$ invertible,
with $\lvert d'_i - d_i\rvert \le g/16$ for every $i$ has $\lvert d'_i - d_i\rvert \le
B\|\mathbf{E}\|_2$ for every $i$: Bauer–Fike puts $d'_i$ within $B\|\mathbf{E}\|_2 \le g/16$ of some
$d_k$, and $k = i$ since $\lvert d_k - d_i\rvert < g$. -/
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

/-- **Condition and separation along a perturbed unitary similarity**: let
$\mathbf{A}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
$\kappa(\mathbf{V}) = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$ and eigenvalues at mutual
distance at least $g > 0$. If $\mathbf{A}' = \mathbf{U}^{\mathsf H}(\mathbf{A} +
\mathbf{E})\mathbf{U}$ with $\mathbf{U}$ unitary and $\|\mathbf{E}\|_2 \le e \le g/(16(n + 1)B)$,
then $\mathbf{A}'$ has a diagonalization $\mathbf{V}'$, $\mathbf{d}'$ with
$\kappa(\mathbf{V}') \le 2B$ and eigenvalues at mutual distance at least $g/2$: one doubling of
the class constants per perturbation. [BanksGarzaVargasSrivastava2022, Lemma 6.1], with the
separation of `NLAlib.exists_pseudoConditionNumber_le_and_le_norm_sub`. -/
theorem IsPerturbedUnitarySimilar.exists_pseudoConditionNumber_le_and_le_norm_sub {n : ℕ}
    {A A' V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e : ℝ} (hA : IsPerturbedUnitarySimilar A A' e)
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d) {B g : ℝ}
    (hB : pseudoConditionNumber V ≤ B) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (he : e ≤ g / (16 * (n + 1) * B)) :
    ∃ (V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d' : Fin (n + 1) → ℂ), IsUnit V' ∧
      A' * V' = V' * Matrix.diagonal d' ∧ pseudoConditionNumber V' ≤ 2 * B ∧
      ∀ i j, i ≠ j → g / 2 ≤ ‖d' i - d' j‖ := by
  obtain ⟨U, E, hU, hE, rfl⟩ := hA
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hB
  have hE' := hE.trans he
  obtain ⟨V', d', hV', hAV', hκ, hsep⟩ :=
    NLAlib.exists_pseudoConditionNumber_le_and_le_norm_sub hV hAV hB hg hgap hE'
  have hBE : B * specNorm E ≤ g / 16 := by
    calc B * specNorm E ≤ B * (g / (16 * (n + 1) * B)) :=
          mul_le_mul_of_nonneg_left hE' (by linarith)
      _ = g / (16 * (n + 1)) := by field_simp
      _ ≤ g / 16 := by gcongr; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hUU : U * Uᴴ = 1 := hU.mul_conjTranspose_self
  have hQ : HasOrthonormalCols Uᴴ := by
    rw [hasOrthonormalCols_iff, Matrix.conjTranspose_conjTranspose, hUU]
  have hUu : IsUnit Uᴴ := ⟨⟨Uᴴ, U, hU.conjTranspose_mul_self, hUU⟩, rfl⟩
  refine ⟨Uᴴ * V', d', hUu.mul hV', ?_, by rw [hQ.pseudoConditionNumber_mul_left]; exact hκ,
    fun i j hij => (by linarith : g / 2 ≤ g - 2 * B * specNorm E).trans (hsep i j hij)⟩
  calc Uᴴ * (A + E) * U * (Uᴴ * V') = Uᴴ * ((A + E) * V') := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc U, hUU, Matrix.one_mul, Matrix.mul_assoc]
    _ = _ := by rw [hAV', Matrix.mul_assoc]

/-- **Eigenvector weights survive a perturbation** ([BanksGarzaVargasSrivastava2025,
Proposition 5.3], the eigenvector-perturbation step corrected for its erratum P4): let
$\mathbf{A}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$, eigenvalues separated by $g > 0$, and
$\|\mathbf{E}\|_2 \le g/(16(n + 1)B)$. Then $\mathbf{A} + \mathbf{E}$ has a diagonalization
$\mathbf{V}'$, $\mathbf{d}'$ with $\|\mathbf{V}'\|_2\|\mathbf{V}'^{-1}\|_2 \le 2B$,
$\lvert d'_i - d_i\rvert \le g/16$, and for every matrix $\mathbf{Q}$ and every $i$ the last-row
weights $w$ satisfy
$$\sqrt{w_i(\mathbf{Q}^{\mathsf{H}}\mathbf{V})} \le
  (1 + \sqrt{n + 1}\,\theta)\sqrt{w_i(\mathbf{Q}^{\mathsf{H}}\mathbf{V}')} + \theta,
  \qquad \theta = \frac{64(n + 1)B^2\|\mathbf{E}\|_2}{g}\,.$$
The paper transfers the anti-concentration of a random direction to eigenvectors that depend on
it; here the weights of the fixed $\mathbf{V}$ are transferred to $\mathbf{V}'$ for every
$\mathbf{Q}$ at once. -/
theorem exists_lastRowWeights_ge_of_norm_sub_le {n : ℕ}
    {A V E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {B g : ℝ}
    (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d) (hB : pseudoConditionNumber V ≤ B)
    (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hE : specNorm E ≤ g / (16 * (n + 1) * B)) :
    ∃ (V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d' : Fin (n + 1) → ℂ), IsUnit V' ∧
      (A + E) * V' = V' * Matrix.diagonal d' ∧ pseudoConditionNumber V' ≤ 2 * B ∧
      (∀ i, ‖d' i - d i‖ ≤ g / 16) ∧
      ∀ (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)),
        √(lastRowWeights (Qᴴ * V) i) ≤
          (1 + √(n + 1) * (64 * (n + 1) * B ^ 2 * specNorm E / g)) *
              √(lastRowWeights (Qᴴ * V') i) +
            64 * (n + 1) * B ^ 2 * specNorm E / g := by
  obtain ⟨Z, d', hU, hAV', -, hκZ, hm, hZ⟩ :=
    exists_add_mul_mul_one_add_eq_mul_diagonal hV hAV hB hg hgap hE
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hB
  refine ⟨V * (1 + Z), d', hV.mul hU, hAV', ?_, hm, fun Q i => ?_⟩
  · calc pseudoConditionNumber (V * (1 + Z))
        ≤ pseudoConditionNumber V * pseudoConditionNumber (1 + Z) :=
          pseudoConditionNumber_mul_le hV hU
      _ ≤ 2 * B := by nlinarith [pseudoConditionNumber_nonneg (1 + Z)]
  -- `‖Z‖₂ ≤ 2√(n+1) B‖E‖₂/g` is at most `θ` and at most `√(n+1) θ`
  set θ := 64 * (n + 1) * B ^ 2 * specNorm E / g
  have hE0 : 0 ≤ specNorm E := specNorm_nonneg E
  have hN : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hsN : √((n : ℝ) + 1) ≤ n + 1 := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hs0 : 0 ≤ √((n : ℝ) + 1) := Real.sqrt_nonneg _
  have hBB : 2 * B ≤ 64 * (n + 1) * B ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hN (sq_nonneg B)]
  have h2θ : 2 * B * specNorm E / g ≤ θ :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBB hE0) hg.le
  have hZθ : specNorm Z ≤ θ := hZ.trans (div_le_div_of_nonneg_right (by
    nlinarith [mul_le_mul hsN (by nlinarith : B ≤ 32 * B ^ 2) (by linarith) (by linarith)])
    hg.le)
  have hZθ' : specNorm Z ≤ √(n + 1) * θ := hZ.trans (by
    rw [show 2 * √((n : ℝ) + 1) * B * specNorm E / g = √(n + 1) * (2 * B * specNorm E / g) by
      ring]
    exact mul_le_mul_of_nonneg_left h2θ hs0)
  have h := sqrt_lastRowWeights_le_mul_one_add (Qᴴ * V) Z i
  rw [← Matrix.mul_assoc]
  refine h.trans ?_
  gcongr

/-- A perturbed unitary similarity carries an eigenvalue listing back: if $\mathbf{B}$ is a
perturbed unitary similarity of $\mathbf{A}$ with backward error $\varepsilon$ and `rts` lists the
eigenvalues of $\mathbf{B}$, then `rts` lists those of $\mathbf{A} + \mathbf{G}$ for some
$\|\mathbf{G}\|_2 \le \varepsilon$. -/
theorem IsPerturbedUnitarySimilar.exists_isEigenvalueListing {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℂ} {ε : ℝ} (h : IsPerturbedUnitarySimilar A B ε)
    {rts : Fin n → ℂ} (hB : IsEigenvalueListing B rts) :
    ∃ G : Matrix (Fin n) (Fin n) ℂ, specNorm G ≤ ε ∧ IsEigenvalueListing (A + G) rts := by
  obtain ⟨U, E, hU, hE, rfl⟩ := h
  refine ⟨E, hE, ?_⟩
  rw [isEigenvalueListing_iff] at hB ⊢
  rwa [charpoly_mul_mul_of_mul_eq_one hU.conjTranspose_mul_self] at hB

/-! ### The conditioned diagonalizable class -/

/-- **The class $(B, \Gamma)$**: $\mathbf{A}$ is diagonalizable by $\mathbf{V}$ with
$\kappa(\mathbf{V}) \le B$ (`NLAlib.pseudoConditionNumber`) and eigenvalues at mutual distance at
least $\Gamma$. The hypothesis of the shifted QR analysis
[BanksGarzaVargasSrivastava2022, Theorem 1.2], named; a diagonalizable matrix in Mathlib's sense
(`NLAlib.IsConditionedDiagonalizable.isDiagonalizable`). -/
def IsConditionedDiagonalizable {n : Type*} [Fintype n] [DecidableEq n] (B Γ : ℝ)
    (A : Matrix n n ℂ) : Prop :=
  ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧ A * V = V * Matrix.diagonal d ∧
    pseudoConditionNumber V ≤ B ∧ ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖

/-- A matrix of the class is diagonalizable. -/
theorem IsConditionedDiagonalizable.isDiagonalizable {n : Type*} [Fintype n] [DecidableEq n]
    {B Γ : ℝ} {A : Matrix n n ℂ} (h : IsConditionedDiagonalizable B Γ A) :
    IsDiagonalizable A := sorry

/-- **The class through a perturbed unitary similarity**: a step by any unitary with backward
error at most $\Gamma/(16(n+1)B)$ keeps the matrix in the class $(2B, \Gamma/2)$ (from
`NLAlib.exists_pseudoConditionNumber_le_and_le_norm_sub`; the condition number and the gaps are
unitarily invariant). -/
theorem IsConditionedDiagonalizable.of_isPerturbedUnitarySimilarBy {n : ℕ} {B Γ ε : ℝ}
    {A H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : IsConditionedDiagonalizable B Γ A)
    (hΓ : 0 < Γ) (h : IsPerturbedUnitarySimilarBy V A H ε) (hε : ε ≤ Γ / (16 * (n + 1) * B)) :
    IsConditionedDiagonalizable (2 * B) (Γ / 2) H := sorry

end NLAlib
