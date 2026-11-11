/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Math.Recurrence

/-!
# Full residual projection in conjugate gradients

The basis stores unnormalized residuals. A sweep subtracts each component along a stored
column, dividing by its squared norm. For exact CG the residuals are already orthogonal,
so the sweep leaves every later residual unchanged.

## Main results

* `NLAlib.Krylov.CG.Reorth.sweepVec_eq_self`: a sweep fixes an orthogonal vector.
* `Matrix.PosDef.sweepVec_cgState_r`: full reorthogonalization fixes exact CG residuals.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open scoped Matrix

variable {n : Type*} [Fintype n]

/-- Subtract the component along an unnormalized column. -/
noncomputable def projectOff (q v : n → ℝ) : n → ℝ :=
  v - ((q ⬝ᵥ v) / (q ⬝ᵥ q)) • q

/-- Sequential full projection against the first `k` columns. -/
noncomputable def sweepVec (Q : ℕ → n → ℝ) (v : n → ℝ) : ℕ → n → ℝ
  | 0 => v
  | k + 1 => projectOff (Q k) (sweepVec Q v k)

/-- A vector orthogonal to a column is fixed by its projection, even when that column is zero. -/
theorem projectOff_eq_self {q v : n → ℝ} (h : q ⬝ᵥ v = 0) : projectOff q v = v := by
  simp [projectOff, h]

/-- A full sweep fixes a vector orthogonal to every column it visits. -/
theorem sweepVec_eq_self (Q : ℕ → n → ℝ) (v : n → ℝ) (k : ℕ)
    (h : ∀ j < k, Q j ⬝ᵥ v = 0) : sweepVec Q v k = v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sweepVec, ih (fun j hj => h j (by omega))]
    exact projectOff_eq_self (h k (by omega))

/-- The exact CG residual at index `k` survives projection against every earlier residual.
This reuses the established residual orthogonality theorem; it does not assume a program run.
[HestenesStiefel1952, Theorem 5:1]. -/
theorem _root_.Matrix.PosDef.sweepVec_cgState_r {A : Matrix n n ℝ} (hA : A.PosDef)
    (b x₀ : n → ℝ) (k : ℕ) :
    sweepVec (fun j => (cgState A b x₀ j).r) (cgState A b x₀ k).r k =
      (cgState A b x₀ k).r := by
  apply sweepVec_eq_self
  intro j hj
  simpa only [star_trivial] using hA.star_cgState_r_dotProduct_eq_zero (b := b) (x₀ := x₀) hj

end NLAlib.Krylov.CG.Reorth
