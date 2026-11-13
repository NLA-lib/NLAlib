/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.StoredCertificate

/-!
# A positive-roundoff stored scalar CG certificate

A one-dimensional problem with cap one admits the actual raw identity matrix and nonzero
right-hand side. A strictly positive scalar roundoff and the genuinely inflating machine
satisfy the complete precision window, yielding the scalar-only stored CG certificate.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Examples.supply`: nonempty raw spectral inputs.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Examples.algorithm`: positive-roundoff scalar CG.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Examples

open Ops
open scoped Matrix

/-- The regression uses dimension one and permits one actual CG step. -/
def domain (d : Fin 2 → ℕ) : Prop := d = ![1, 1]

/-- The concrete size/cap pair belongs to the declared size domain. -/
theorem admitted : ∃ d, domain d := ⟨![1, 1], rfl⟩

/-- The actual one-word dense input is the identity matrix, without preprocessing. -/
theorem denseMatrix_one : StoredOperator.denseMatrix 1 1 [1] = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  norm_num [StoredOperator.denseMatrix]

/-- Actual identity matrix words and a nonzero raw RHS witness the positive spectral problem.
This supplies data and capacity only, without assuming any execution or numerical output. -/
theorem supply (d : Fin 2 → ℕ) (hd : domain d) :
    ∃ raw rhs : List ℝ, raw.length = d 0 * d 0 ∧ rhs.length = d 0 ∧
      Stored.accepts (fun _ => 1) (fun _ => 1) d raw rhs := by
  change d = ![1, 1] at hd
  subst d
  refine ⟨[1], [1], by norm_num, by norm_num, ?_⟩
  change (StoredOperator.denseMatrix 1 1 ([1] : List ℝ))ᵀ =
      StoredOperator.denseMatrix 1 1 ([1] : List ℝ) ∧
    spectrum ℝ (StoredOperator.denseMatrix 1 1 ([1] : List ℝ)) ⊆ Set.Icc 1 1
  rw [denseMatrix_one]
  simp

/-- Multiplying actual word ones changes the result at the chosen positive roundoff.
This rules out an accidental specialization to the exact scalar machine. -/
theorem mul_one_ne_one : (inflMachine (1 / 100000000)).mul 1 1 ≠ 1 := by
  norm_num [inflMachine]

/-- The strictly positive roundoff is one hundred-millionth; the scalar machine inflates
its results by one plus that value, so this certificate is not an exact-arithmetic instance. -/
noncomputable def algorithm :
    Algorithm (RoundedScalarBlas.model
      (Stored.problem (fun _ => 1) (fun _ => 1) domain admitted supply)
      (inflMachine (1 / 100000000)))
      (Stored.scalarSpecification (fun _ => 1) (fun _ => 1) domain admitted supply
        (fun _ => 64 / 100000000)) := by
  refine Stored.scalarAlgorithm (fun _ => 1) (fun _ => 1) domain admitted supply
    (inflMachine (1 / 100000000)) (1 / 100000000) (stdModel_infl (by norm_num))
    (by norm_num) (fun _ => 4 / 100000000) (fun _ => 64 / 100000000) ?_ ?_ ?_ ?_ ?_
  all_goals
    intro d hd
    change d = ![1, 1] at hd
    subst d
  · norm_num [ScalarProducts.roundoff]
  · constructor <;>
      norm_num [Blas.seq.err, Blas.level1Err, Blas.seqSumErr]
  · norm_num
  · norm_num
  · norm_num

end NLAlib.Krylov.CG.HSCG.Carried.Rounded.Stored.Examples
