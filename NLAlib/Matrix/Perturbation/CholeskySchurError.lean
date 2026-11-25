/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Rounding
public import NLAlib.ForMathlib.Algebra.Order.Field.Basic
public import NLAlib.Matrix.Factorizations.Elimination

/-!
# An input margin recurrence for rounded Cholesky

This conservative recurrence compares the actual saved-pivot Schur updates with exact
elimination. Its dependence on the ratio of an input norm bound to a positive spectral margin
is explicit. It does not assert classical condition-independent backward stability.

## Main results

* `NLAlib.choleskySchurErrorBound_nonneg`: the recurrence is nonnegative.
* `NLAlib.choleskySchurErrorBound_le_succ`: the recurrence increases with the step count.
-/

@[expose] public section

namespace NLAlib

/-- The active-entry error sequence for saved-pivot Schur steps, with roundoff $u$, input
norm bound $B$, and lower spectral margin $\mu$. Its value is specified recursively by
this sequence: <!-- value choleskySchurErrorBound u B \mu -->
$$\eta_0=0,\quad
\eta_{k+1}=(1+6(B/\mu)+2(B/\mu)^2)\eta_k+uB(2+80(B/\mu)).$$
The estimate is intended for $0\le u\le 1/10$, $0<\mu\le B$. -/
noncomputable def choleskySchurErrorBound (u B μ : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => (1 + 6 * (B / μ) + 2 * (B / μ) ^ 2) * choleskySchurErrorBound u B μ k +
      u * B * (2 + 80 * (B / μ))

/-- Nonnegative roundoff, scale and positive margin give nonnegative propagated errors. -/
theorem choleskySchurErrorBound_nonneg {u B μ : ℝ} (hu : 0 ≤ u) (hB : 0 ≤ B)
    (hμ : 0 < μ) (k : ℕ) : 0 ≤ choleskySchurErrorBound u B μ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only [choleskySchurErrorBound]
    positivity

/-- The propagated active-entry error does not decrease with another Schur update. -/
theorem choleskySchurErrorBound_le_succ {u B μ : ℝ} (hu : 0 ≤ u) (hB : 0 ≤ B)
    (hμ : 0 < μ) (k : ℕ) :
    choleskySchurErrorBound u B μ k ≤ choleskySchurErrorBound u B μ (k + 1) := by
  have he := choleskySchurErrorBound_nonneg hu hB hμ k
  have hr : 0 ≤ B / μ := div_nonneg hB hμ.le
  dsimp only [choleskySchurErrorBound]
  nlinarith [mul_nonneg (mul_nonneg hu hB) (by positivity : 0 ≤ 2 + 80 * (B / μ)),
    mul_nonneg hr he, mul_nonneg (sq_nonneg (B / μ)) he]

/-- The input error budget is monotone in the number of completed updates. -/
theorem choleskySchurErrorBound_le_choleskySchurErrorBound {u B μ : ℝ} (hu : 0 ≤ u) (hB : 0 ≤ B)
    (hμ : 0 < μ) {k l : ℕ} (hkl : k ≤ l) :
    choleskySchurErrorBound u B μ k ≤ choleskySchurErrorBound u B μ l := by
  exact monotone_nat_of_le_succ (choleskySchurErrorBound_le_succ hu hB hμ) hkl

private theorem abs_eliminationStep_sub_eliminationStep_le_of_entries {N : ℕ}
    {M E : Matrix (Fin N) (Fin N) ℝ} {μ B η : ℝ} {k : Fin N}
    (hμ : 0 < μ) (hμB : μ ≤ B) (hημ : η ≤ μ / 2)
    (hp : μ ≤ E k k) (hE : ∀ i j, |E i j| ≤ B)
    (i j : Fin N) (hkk : |M k k - E k k| ≤ η) (hij : |M i j - E i j| ≤ η)
    (hik : |M i k - E i k| ≤ η) (hkj : |M k j - E k j| ≤ η) :
    |eliminationStep M k i j - eliminationStep E k i j| ≤
      (1 + 6 * (B / μ) + 2 * (B / μ) ^ 2) * η := by
  have hB : 0 ≤ B := hμ.le.trans hμB
  have ha : μ / 2 ≤ M k k := by
    have h := (abs_le.mp hkk).1
    linarith
  have hm : |M k j| ≤ 2 * B := by
    calc |M k j| ≤ |M k j - E k j| + |E k j| := by
           simpa only [sub_add_cancel] using abs_add_le (M k j - E k j) (E k j)
         _ ≤ η + B := add_le_add hkj (hE k j)
         _ ≤ 2 * B := by linarith
  have hq := abs_mul_div_sub_mul_div_le hμ ha hp hm
    (hE i k) (hE k j) hik hkj hkk
  have he : eliminationStep M k i j - eliminationStep E k i j =
      (M i j - E i j) - (M i k * M k j / M k k - E i k * E k j / E k k) := by
    simp only [eliminationStep_apply, div_eq_mul_inv]
    ring
  rw [he]
  calc |(M i j - E i j) - (M i k * M k j / M k k - E i k * E k j / E k k)|
      ≤ |M i j - E i j| + |M i k * M k j / M k k - E i k * E k j / E k k| :=
        abs_sub _ _
    _ ≤ η + (6 * (B / μ) + 2 * (B / μ) ^ 2) * η := add_le_add hij hq
    _ = (1 + 6 * (B / μ) + 2 * (B / μ) ^ 2) * η := by ring

/-- The exact Schur map is Lipschitz on an active block whose reference pivot is at least
$\mu$, provided the entrywise perturbation is at most $\mu/2$ and $\mu\le B$. -/
theorem abs_eliminationStep_sub_eliminationStep_le {N : ℕ}
    {M E : Matrix (Fin N) (Fin N) ℝ} {μ B η : ℝ} {k : Fin N}
    (hμ : 0 < μ) (hμB : μ ≤ B) (hημ : η ≤ μ / 2)
    (hp : μ ≤ E k k) (hE : ∀ i j, |E i j| ≤ B)
    (herr : ∀ i j, k ≤ i → k ≤ j → |M i j - E i j| ≤ η)
    (i j : Fin N) (hi : k ≤ i) (hj : k ≤ j) :
    |eliminationStep M k i j - eliminationStep E k i j| ≤
      (1 + 6 * (B / μ) + 2 * (B / μ) ^ 2) * η := by
  exact abs_eliminationStep_sub_eliminationStep_le_of_entries hμ hμB hημ hp hE i j
    (herr k k le_rfl le_rfl) (herr i j hi hj) (herr i k hi le_rfl) (herr k j le_rfl hj)

/-- The same Schur sensitivity estimate holds on the entire matrix, including retired
rows and columns, when the full stored residual approximates its exact reference. -/
theorem abs_eliminationStep_sub_eliminationStep_le_of_forall_abs_sub_le {N : ℕ}
    {M E : Matrix (Fin N) (Fin N) ℝ} {μ B η : ℝ} {k : Fin N}
    (hμ : 0 < μ) (hμB : μ ≤ B) (hημ : η ≤ μ / 2)
    (hp : μ ≤ E k k) (hE : ∀ i j, |E i j| ≤ B)
    (herr : ∀ i j, |M i j - E i j| ≤ η) (i j : Fin N) :
    |eliminationStep M k i j - eliminationStep E k i j| ≤
      (1 + 6 * (B / μ) + 2 * (B / μ) ^ 2) * η := by
  exact abs_eliminationStep_sub_eliminationStep_le_of_entries hμ hμB hημ hp hE i j
    (herr k k) (herr i j) (herr i k) (herr k j)

private theorem roundingFactor_five_le {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1 / 10) :
    Computation.roundingFactor 5 u ≤ 10 * u := by
  have hd : 0 < 1 - 5 * u := by linarith
  have h := Computation.roundingFactor_le (n := 5) hu (by norm_num; linarith)
  norm_num at h
  exact h.trans ((div_le_iff₀ hd).mpr (by nlinarith))

/-- A saved-pivot local rounding defect propagates the active-entry error by the explicit
input-margin recurrence. Only active entries need to approximate their exact reference. -/
theorem abs_sub_eliminationStep_le_choleskySchurErrorBound {N : ℕ}
    {M E M' : Matrix (Fin N) (Fin N) ℝ} {μ B u : ℝ} {k : ℕ} {r : Fin N}
    (hμ : 0 < μ) (hμB : μ ≤ B) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 10)
    (hημ : choleskySchurErrorBound u B μ k ≤ μ / 2) (hp : μ ≤ E r r)
    (hE : ∀ i j, |E i j| ≤ B)
    (herr : ∀ i j, r ≤ i → r ≤ j → |M i j - E i j| ≤ choleskySchurErrorBound u B μ k)
    (hlocal : ∀ i j, |M' i j - eliminationStep M r i j| ≤
      u * |M i j| + Computation.roundingFactor 5 u * |M i r * M r j / M r r|)
    (i j : Fin N) (hi : r ≤ i) (hj : r ≤ j) :
    |M' i j - eliminationStep E r i j| ≤ choleskySchurErrorBound u B μ (k + 1) := by
  let η := choleskySchurErrorBound u B μ k
  have hB : 0 ≤ B := hμ.le.trans hμB
  have hm : ∀ a b, r ≤ a → r ≤ b → |M a b| ≤ 2 * B := by
    intro a b ha hb
    calc |M a b| ≤ |M a b - E a b| + |E a b| := by
           simpa only [sub_add_cancel] using abs_add_le (M a b - E a b) (E a b)
         _ ≤ η + B := add_le_add (herr a b ha hb) (hE a b)
         _ ≤ 2 * B := by dsimp [η]; linarith
  have ha : μ / 2 ≤ M r r := by
    have h := (abs_le.mp (herr r r le_rfl le_rfl)).1
    linarith
  have ha0 : 0 < M r r := by linarith
  have hq : |M i r * M r j / M r r| ≤ 8 * B ^ 2 / μ := by
    rw [abs_div, abs_mul, abs_of_pos ha0]
    calc |M i r| * |M r j| / M r r ≤ (2 * B) * (2 * B) / (μ / 2) := by
           gcongr
           · exact hm i r hi le_rfl
           · exact hm r j le_rfl hj
         _ = 8 * B ^ 2 / μ := by ring
  have hd : |M' i j - eliminationStep M r i j| ≤ u * B * (2 + 80 * (B / μ)) := by
    calc |M' i j - eliminationStep M r i j|
        ≤ u * |M i j| + Computation.roundingFactor 5 u * |M i r * M r j / M r r| :=
          hlocal i j
      _ ≤ u * (2 * B) + (10 * u) * (8 * B ^ 2 / μ) := by
        gcongr
        · exact hm i j hi hj
        · exact roundingFactor_five_le hu hu1
      _ = u * B * (2 + 80 * (B / μ)) := by ring
  calc |M' i j - eliminationStep E r i j|
      ≤ |M' i j - eliminationStep M r i j| +
          |eliminationStep M r i j - eliminationStep E r i j| := abs_sub_le _ _ _
    _ ≤ u * B * (2 + 80 * (B / μ)) +
          (1 + 6 * (B / μ) + 2 * (B / μ) ^ 2) * η :=
      add_le_add hd (abs_eliminationStep_sub_eliminationStep_le hμ hμB hημ hp hE herr i j hi hj)
    _ = choleskySchurErrorBound u B μ (k + 1) := by rw [choleskySchurErrorBound]; ring

end NLAlib
