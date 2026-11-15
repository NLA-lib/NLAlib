/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.StoredCertificate
public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.StoredExamples

/-!
# A positive-roundoff stored scalar PCG certificate

The one-dimensional identity input and cap one reuse the raw data fixture for scalar CG.
Both PCG operators receive their own actual raw identity block. Strictly positive scalar
roundoff satisfies the explicit geometric continuation window; multiplication differs from
exact arithmetic. The certificate includes literal-zero initialization and all scalar costs.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Examples.algorithm`: positive-roundoff scalar PCG.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Examples

open Ops
open HSCG.Carried.Rounded.Stored.Examples (domain admitted)

/-- The existing raw identity matrix and nonzero right-hand side supply both independently
stored operators, with the two reference spectral windows equal to the singleton one. -/
theorem supply (d : Fin 2 → ℕ) (hd : domain d) :
    ∃ rawA rawP rhs : List ℝ,
      rawA.length = d 0 * d 0 ∧ rawP.length = d 0 * d 0 ∧ rhs.length = d 0 ∧
        Stored.accepts (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) d rawA rawP rhs := by
  obtain ⟨raw, rhs, hr, hb, h⟩ := HSCG.Carried.Rounded.Stored.Examples.supply d hd
  exact ⟨raw, raw, rhs, hr, hr, hb, h.1, h.1, h.2, h.2⟩

/-- Actual word multiplication is nonexact at the chosen strictly positive scalar roundoff. -/
theorem mul_one_ne_one : (inflMachine (1 / 1000000000000)).mul 1 1 ≠ 1 := by
  norm_num [inflMachine]

/-- The complete actual scalar PCG implementation admits dimension one, cap one, raw identity
system and preconditioner words and a nonzero RHS at unit roundoff one trillionth. -/
noncomputable def algorithm :
    Algorithm (RoundedScalarBlas.model
      (Stored.problem (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
        domain admitted supply) (inflMachine (1 / 1000000000000)))
      (Stored.specification (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
        domain admitted supply (inflMachine (1 / 1000000000000)) (1 / 1000000000000)
        (stdModel_infl (by norm_num)) (by norm_num) (fun _ => 64 / 1000000000000)) := by
  refine Stored.algorithm (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    domain admitted supply (inflMachine (1 / 1000000000000)) (1 / 1000000000000)
    (stdModel_infl (by norm_num)) (by norm_num) (fun _ => 64 / 1000000000000)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals
    intro d hd
    change d = ![1, 1] at hd
    subst d
  · constructor <;> norm_num [StoredContext.relativeError, ScalarProducts.roundoff,
      Blas.seq.err, Blas.level1Err, Blas.seqSumErr]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end NLAlib.Krylov.CG.HSPCG.Rounded.Stored.Examples
