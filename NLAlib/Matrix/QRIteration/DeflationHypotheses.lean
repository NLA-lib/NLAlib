/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.ShiftSearch
public import NLAlib.Matrix.QRIteration.DeflationConditioning

/-!
# Quantitative hypotheses for shifted QR deflation

Explicit diagonalization, conditioning, separation and contraction assumptions bound the
number of shift-strategy iterations. The hypotheses concern the mathematical input and
parameters. They do not assert that a program executes or that an output has been obtained.

## Main results

* `NLAlib.RapidDecouplingHyps`: quantitative assumptions for one active block.
* `NLAlib.ShiftedQRHyps`: input assumptions for the full deflation algorithm.
* `NLAlib.RapidDecouplingHyps.step`: preservation and potential contraction.
* `NLAlib.RapidDecouplingHyps.iteration_lt`: continuing iterates leave iteration budget.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **The hypotheses of rapid decoupling on a block** $\mathbf{H}$ with $F$ iterations allowed:
$\mathbf{H}$ diagonalizable with $\kappa(\mathbf{V}) \le B$, $1 \le m$, $\theta, \alpha \ge 1$,
$B^{4m} \le \alpha^{2^m}$, $0 < \gamma < 1$, $\delta > 0$ with $\delta\|\mathbf{H}\|_2 \le \tau$,
and $F \ge \lceil\log(1/\delta)/\log(1/(1 - \gamma))\rceil$
([BanksGarzaVargasSrivastava2021, Theorem 1.6],
`NLAlib.IsUpperHessenberg.exists_le_isDecoupled_shqrIterate`). -/
def RapidDecouplingHyps {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (τ B θ α γ δ : ℝ)
    (m F : ℕ) : Prop :=
  (∃ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ), IsUnit V ∧
    H * V = V * Matrix.diagonal d ∧ pseudoConditionNumber V ≤ B) ∧
  1 ≤ m ∧ 1 ≤ θ ∧ 1 ≤ α ∧ B ^ (4 * m) ≤ α ^ 2 ^ m ∧ 0 < γ ∧ γ < 1 ∧ 0 < δ ∧
  δ * specNorm H ≤ τ ∧ ⌈Real.log (1 / δ) / Real.log (1 / (1 - γ))⌉₊ ≤ F


/-- A matrix that fails the decoupling test at a threshold $\tau \ge 0$ has a positive potential:
the last $k$ subdiagonal moduli are all positive. -/
theorem hessenbergPotential_pos_of_not_isDecoupledAbs {n : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (k : ℕ)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hdec : ¬IsDecoupledAbs τ H) :
    0 < hessenbergPotential k H :=
  Real.rpow_pos_of_pos (Finset.prod_pos fun i _ => by
    by_contra h
    exact hdec ⟨i, by linarith [not_lt.mp h]⟩) _

/-- One iteration is a unitary similarity without additional numerical hypotheses: the
step `NLAlib.shqrAcceptStep` of $\mathbf{H} = \mathbf{U}^{\mathsf H}\mathbf{H}_0
\mathbf{U}$ is $\mathbf{U}'^{\mathsf H}\mathbf{H}_0\mathbf{U}'$ for a unitary $\mathbf{U}'$. -/
theorem shqrAcceptStep_exists_unitary {n : ℕ} {H₀ H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (τ B θ α γ : ℝ) (m : ℕ) (ss : List ℂ) (hU : HasOrthonormalCols U) (hHU : H = Uᴴ * H₀ * U) :
    ∃ U' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HasOrthonormalCols U' ∧
      shqrAcceptStep τ B θ α γ m H ss = U'ᴴ * H₀ * U' := by
  obtain ⟨W, hW, hstep⟩ := exists_unitary_multiShiftedQRStep H
    (List.replicate (2 ^ m) (shqrAcceptShift τ B θ α γ m H ss))
  refine ⟨U * W, ?_, ?_⟩
  · exact hU.mul hW
  · rw [shqrAcceptStep, hstep, hHU, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

/-- One iteration preserves contraction: from $\mathbf{H}$ upper Hessenberg that fails
the test, with a
diagonalization of $\kappa \le B$ and $\psi_k(\mathbf{H}) \le (1 - \gamma)^j\psi_k(\mathbf{H}_0)$,
and $k$ $\theta$-optimal Ritz values `ss` (when $\psi_k(\mathbf{H}) > 0$), the step
`NLAlib.shqrAcceptStep` keeps a diagonalization of $\kappa \le B$ and, if it fails the test, has
$\psi_k \le (1 - \gamma)^{j + 1}\psi_k(\mathbf{H}_0)$. -/
theorem RapidDecouplingHyps.step {n : ℕ} {H₀ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {τ B θ α γ δ : ℝ} {m F j : ℕ} {ss : List ℂ}
    (hyp : RapidDecouplingHyps H₀ τ B θ α γ δ m F) (hkn : 2 ^ m ≤ n) (hτ : 0 ≤ τ)
    (hH : IsUpperHessenberg H) (hdec : ¬IsDecoupledAbs τ H)
    (hκ : ∃ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ), IsUnit V ∧
      H * V = V * Matrix.diagonal d ∧ pseudoConditionNumber V ≤ B)
    (hψ : hessenbergPotential (2 ^ m) H ≤ (1 - γ) ^ j * hessenbergPotential (2 ^ m) H₀)
    (hlen : ss.length = 2 ^ m)
    (hss : 0 < hessenbergPotential (2 ^ m) H → IsOptimalRitzValues θ H ss) :
    (∃ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d : Fin (n + 1) → ℂ), IsUnit V ∧
        shqrAcceptStep τ B θ α γ m H ss * V = V * Matrix.diagonal d ∧
        pseudoConditionNumber V ≤ B) ∧
      (¬IsDecoupledAbs τ (shqrAcceptStep τ B θ α γ m H ss) →
        hessenbergPotential (2 ^ m) (shqrAcceptStep τ B θ α γ m H ss) ≤
          (1 - γ) ^ (j + 1) * hessenbergPotential (2 ^ m) H₀) := by
  obtain ⟨-, hm1, hθ, hα, hBα, hγ0, hγ1, hδ, hδτ, hT⟩ := hyp
  obtain ⟨V, d, hV, hHV, hVB⟩ := hκ
  have hopt := hss (hessenbergPotential_pos_of_not_isDecoupledAbs hτ (2 ^ m) hdec)
  refine ⟨?_, fun hn => ?_⟩
  · obtain ⟨V', hV', hHV', hκ'⟩ := exists_isUnit_mul_eq_mul_diagonal_multiShiftedQRStep
      (H := H) hV hHV (List.replicate (2 ^ m) (shqrAcceptShift τ B θ α γ m H ss))
    exact ⟨V', d, hV', hHV', hκ'.trans_le hVB⟩
  · rcases hH.isDecoupledAbs_or_hessenbergPotential_shqrAcceptStep_le hV hHV hVB hm1 hkn hlen
      hopt hθ hα hBα hγ0 hγ1 hτ with h | h
    · exact absurd h hn
    · calc _ ≤ (1 - γ) * hessenbergPotential (2 ^ m) H := h
        _ ≤ (1 - γ) * ((1 - γ) ^ j * hessenbergPotential (2 ^ m) H₀) :=
          mul_le_mul_of_nonneg_left hψ (by linarith)
        _ = _ := by ring

/-- The budget for one more iteration: an iterate that fails the test while
$\psi_k(\mathbf{H}) \le (1 - \gamma)^j\psi_k(\mathbf{H}_0)$ leaves fuel for the next test of a
loop with fuel $F + 1$ (`NLAlib.lt_of_not_isDecoupledAbs_of_hessenbergPotential_le_pow`). -/
theorem RapidDecouplingHyps.iteration_lt {n : ℕ} {H₀ H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {τ B θ α γ δ : ℝ} {m F j : ℕ} (hyp : RapidDecouplingHyps H₀ τ B θ α γ δ m F) (hkn : 2 ^ m ≤ n)
    (hdec : ¬IsDecoupledAbs τ H)
    (hψ : hessenbergPotential (2 ^ m) H ≤ (1 - γ) ^ j * hessenbergPotential (2 ^ m) H₀) :
    j + 1 < F + 1 := by
  obtain ⟨-, -, -, -, -, hγ0, hγ1, hδ, hδτ, hT⟩ := hyp
  have := lt_of_not_isDecoupledAbs_of_hessenbergPotential_le_pow (k := 2 ^ m) (by positivity)
    hkn hγ0 hγ1 hδ hψ hδτ hdec
  omega

/-- The condition bound of a block meeting the rapid-decoupling hypotheses is at least $1$. -/
theorem RapidDecouplingHyps.one_le {n : ℕ} {H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {τ B θ α γ δ : ℝ} {m F : ℕ} (hyp : RapidDecouplingHyps H₀ τ B θ α γ δ m F) : 1 ≤ B := by
  obtain ⟨⟨V, d, hV, -, hVB⟩, -⟩ := hyp
  refine le_trans (one_le_pseudoConditionNumber ?_) hVB
  rintro rfl
  have := (Matrix.isUnit_iff_isUnit_det _).mp hV
  rw [Matrix.det_zero] at this
  exact not_isUnit_zero this


/-- **The quantitative input hypotheses for shifted QR deflation**, for the $N \times N$ input
$\mathbf{H}$ with $\tau = \delta\|\mathbf{H}\|_{\mathsf{F}}$ and the strategy's parameter $B$:
$\mathbf{H}$ diagonalizable with $\kappa(\mathbf{V}) \le B/2$ and eigenvalues at mutual distance
at least $g > 0$ (the blocks then have $\kappa \le B$,
`NLAlib.DeflationInv.exists_pseudoConditionNumber_subBlock_le`); $1 \le m$,
$\theta, \alpha \ge 1$, $B^{4m} \le \alpha^{2^m}$, $0 < \gamma < 1$; $\delta > 0$ small enough
that the accumulated perturbation, at most $(N - 1)\tau$, keeps the blocks' condition,
$(N - 1)\tau \le g/(8NB)$, and that $(N - 1)\tau \le \|\mathbf{H}\|_2$ (each block's norm is
then at most $2\|\mathbf{H}\|_2$); and $F \ge \lceil\log(2/\delta)/\log(1/(1 - \gamma))\rceil$. -/
def ShiftedQRHyps {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (B θ α γ δ g : ℝ) (m F : ℕ) :
    Prop :=
  (∃ (V : Matrix (Fin N) (Fin N) ℂ) (d : Fin N → ℂ), IsUnit V ∧
    H * V = V * Matrix.diagonal d ∧ 2 * pseudoConditionNumber V ≤ B ∧
    ∀ i j, i ≠ j → g ≤ ‖d i - d j‖) ∧
  0 < g ∧ 1 ≤ m ∧ 1 ≤ θ ∧ 1 ≤ α ∧ B ^ (4 * m) ≤ α ^ 2 ^ m ∧ 0 < γ ∧ γ < 1 ∧ 0 < δ ∧
  ((N - 1 : ℕ) : ℝ) * (δ * frobNorm H) ≤ g / (8 * N * B) ∧
  ((N - 1 : ℕ) : ℝ) * (δ * frobNorm H) ≤ specNorm H ∧
  ⌈Real.log (2 / δ) / Real.log (1 / (1 - γ))⌉₊ ≤ F


end NLAlib
