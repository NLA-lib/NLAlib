/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.CholeskySchurError
public import NLAlib.Matrix.Perturbation.SchurMixedError

/-!
# Full-residual Cholesky error with gradual underflow

A full-entry comparison controls both the active block and retired rows and columns of the
actual saved-pivot residual, so that its finite range can be established before every update.

## Main results

* `NLAlib.choleskyMixedSchurErrorBound_nonneg`: nonnegative allowances give nonnegative budgets.
* `NLAlib.abs_sub_eliminationStep_le_choleskyMixedSchurErrorBound`: a local mixed update advances
  the full-residual error recurrence.
-/

@[expose] public section

namespace NLAlib

/-- The full-entry saved-pivot residual error sequence with relative allowance $u$, absolute
allowance $\tau$, input scale $B$, and positive lower spectral margin $\mu$. The forcing term
has the following value: <!-- value schurMixedErrorBound u \tau (2B) (\mu/2) -->
$$\ell=1+u+\tau,\quad
C=(1+u)\ell/(\mu/2)+\tau,\quad
T=(1+u)C\cdot(2B)+\tau,\quad
Q=(1+u)(2B)\cdot T+\tau,\quad
E_c=(u+\tau)/(\mu/2)+u\ell/(\mu/2)+\tau,\quad
E_t=(2B)\cdot E_c+u C\cdot(2B)+\tau,\quad
E_q=(2B)\cdot E_t+u(2B)\cdot T+\tau,\quad
D=E_q+u((2B)+Q)+\tau$$
The propagated sequence is given by <!-- value choleskyMixedSchurErrorBound u \tau B \mu -->
$$\zeta_0=0,\quad\zeta_{k+1}=(1+6(B/\mu)+2(B/\mu)^2)\zeta_k+D$$
The input spectral band and terminal margin control every residual entry, including
retired rows and columns. -/
noncomputable def choleskyMixedSchurErrorBound (u τ B μ : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (1 + 6 * (B / μ) + 2 * (B / μ) ^ 2) * choleskyMixedSchurErrorBound u τ B μ k +
      schurMixedErrorBound u τ (2 * B) (μ / 2)

/-- Nonnegative rounding allowances and input scale with positive margin give nonnegative
full-residual mixed error budgets. -/
theorem choleskyMixedSchurErrorBound_nonneg {u τ B μ : ℝ} (hu : 0 ≤ u) (hτ : 0 ≤ τ)
    (hB : 0 ≤ B) (hμ : 0 < μ) (k : ℕ) : 0 ≤ choleskyMixedSchurErrorBound u τ B μ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hD := schurMixedErrorBound_nonneg hu hτ (by positivity : 0 ≤ 2 * B)
      (by positivity : 0 < μ / 2)
    dsimp only [choleskyMixedSchurErrorBound]
    positivity

/-- Another step cannot decrease the propagated full-residual mixed-error budget. -/
theorem choleskyMixedSchurErrorBound_le_succ {u τ B μ : ℝ} (hu : 0 ≤ u) (hτ : 0 ≤ τ)
    (hB : 0 ≤ B) (hμ : 0 < μ) (k : ℕ) :
    choleskyMixedSchurErrorBound u τ B μ k ≤ choleskyMixedSchurErrorBound u τ B μ (k + 1) := by
  have he := choleskyMixedSchurErrorBound_nonneg hu hτ hB hμ k
  have hr : 0 ≤ B / μ := div_nonneg hB hμ.le
  have hD := schurMixedErrorBound_nonneg hu hτ (by positivity : 0 ≤ 2 * B)
    (by positivity : 0 < μ / 2)
  dsimp only [choleskyMixedSchurErrorBound]
  nlinarith [mul_nonneg hr he, mul_nonneg (sq_nonneg (B / μ)) he]

/-- The full-residual budget is monotone in the completed step count. -/
theorem choleskyMixedSchurErrorBound_le_choleskyMixedSchurErrorBound {u τ B μ : ℝ}
    (hu : 0 ≤ u) (hτ : 0 ≤ τ) (hB : 0 ≤ B) (hμ : 0 < μ) {k l : ℕ} (hkl : k ≤ l) :
    choleskyMixedSchurErrorBound u τ B μ k ≤ choleskyMixedSchurErrorBound u τ B μ l := by
  exact monotone_nat_of_le_succ (choleskyMixedSchurErrorBound_le_succ hu hτ hB hμ) hkl

/-- One mixed-error Schur update advances the entire residual's input-margin error budget,
including retired rows and columns. No assumption on symmetry of the rounded residual is
required. -/
theorem abs_sub_eliminationStep_le_choleskyMixedSchurErrorBound {N : ℕ}
    {M E M' : Matrix (Fin N) (Fin N) ℝ} {μ B u τ : ℝ} {k : ℕ} {r : Fin N}
    (hμ : 0 < μ) (hμB : μ ≤ B)
    (hημ : choleskyMixedSchurErrorBound u τ B μ k ≤ μ / 2) (hp : μ ≤ E r r)
    (hE : ∀ i j, |E i j| ≤ B)
    (herr : ∀ i j, |M i j - E i j| ≤ choleskyMixedSchurErrorBound u τ B μ k)
    (hlocal : ∀ i j, |M' i j - eliminationStep M r i j| ≤
      schurMixedErrorBound u τ (2 * B) (μ / 2)) (i j : Fin N) :
    |M' i j - eliminationStep E r i j| ≤ choleskyMixedSchurErrorBound u τ B μ (k + 1) := by
  calc |M' i j - eliminationStep E r i j|
      ≤ |M' i j - eliminationStep M r i j| +
          |eliminationStep M r i j - eliminationStep E r i j| := abs_sub_le _ _ _
    _ ≤ schurMixedErrorBound u τ (2 * B) (μ / 2) +
          (1 + 6 * (B / μ) + 2 * (B / μ) ^ 2) * choleskyMixedSchurErrorBound u τ B μ k :=
      add_le_add (hlocal i j)
        (abs_eliminationStep_sub_eliminationStep_le_of_forall_abs_sub_le
          hμ hμB hημ hp hE herr i j)
    _ = choleskyMixedSchurErrorBound u τ B μ (k + 1) := by rw [choleskyMixedSchurErrorBound]; ring

end NLAlib
