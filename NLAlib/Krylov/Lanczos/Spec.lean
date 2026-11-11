/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosRecurrence
public import NLAlib.Ops.Catalog.Operator

/-!
# Packed outputs of Lanczos over operations

Basis columns and coefficients are compared directly with the existing pure Lanczos
recurrence. The coefficient prefix is shared by ordinary and fully reorthogonalized programs;
additional coefficient storage is allowed. For Hermitian matrices the basis is canonical.

## Main results

* `NLAlib.Krylov.Lanczos.Output` specifies the stored basis, coefficients and input norm.
* `NLAlib.Krylov.Lanczos.Output.basis_eq_arnoldiMatrix` identifies the canonical basis.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops
open scoped Matrix

/-- Packed Lanczos output: column-major basis through the final state, alpha coefficients,
beta coefficients starting at `cap`, and input norm at `2*cap+1`.
[Paige1972, §2]; [Saad2011, §6.6]. -/
structure Output {K : Type} [Inhabited K] (dec : K → ℝ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (cap : ℕ) (vs cs : List K) : Prop where
  /-- Every requested basis column, including zero columns after breakdown. -/
  basis : ∀ j ≤ cap, ∀ i : Fin n,
    dec (vec vs (j * n + i)) = (lanczosState A b j).cur i
  /-- Every diagonal coefficient. -/
  alpha : ∀ j < cap, dec (vec cs j) = lanczosAlpha A (lanczosState A b j)
  /-- Every coupling coefficient, including the initial zero. -/
  beta : ∀ j ≤ cap, dec (vec cs (cap + j)) = (lanczosState A b j).beta
  /-- The norm used to normalize the initial input. -/
  inputNorm : dec (vec cs (2 * cap + 1)) = ‖WithLp.toLp 2 b‖

/-- For a Hermitian matrix, the decoded stored basis is the canonical Arnoldi/Lanczos basis,
including zero columns after exact breakdown. [Saad2011, §6.6]. -/
theorem Output.basis_eq_arnoldiMatrix {K : Type} [Inhabited K] {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {vs cs : List K}
    (h : Output dec A b cap vs cs) (hA : A.IsHermitian) :
    (fun i : Fin n => fun j : Fin (cap + 1) => dec (vec vs (j * n + i))) =
      arnoldiMatrix A b (cap + 1) := by
  rw [← hA.lanczosMatrix_eq_arnoldiMatrix]
  funext i j
  exact h.basis j (by omega) i

end NLAlib.Krylov.Lanczos
