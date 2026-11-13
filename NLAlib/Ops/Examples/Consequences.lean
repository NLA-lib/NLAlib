/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Certification
public import NLAlib.Ops.Examples.Resources

/-!
# Mathematical consequences without recertifying execution

Two different canonical programs reuse their existing complete resource certificates. Only
the mathematical consequence of the output is supplied: a magnitude identity for repeated
addition, and absence of remaining buffer contents after mixed-format scratch cleanup.
The statement still requires total execution under the same jointly realized primitive model.

## Main results

* `NLAlib.Ops.Examples.Consequences.magnitudeAlgorithm`: exact magnitude of repeated addition.
* `NLAlib.Ops.Examples.Consequences.cleanedAlgorithm`: mixed allocation leaves no stored words.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.Consequences

open Certification Resources


/-- The same count/work/span/byte limits, with the magnitude of the actual stored result. -/
noncomputable def magnitudeSpecification : Specification ScalarOp Empty repeatProblem :=
  { repeatSpecification with
    good d x _ _ m := ∃ y : ℝ,
      m.store.get 1 0 = some y ∧ abs y = (d 0 : ℝ) * abs (show ℝ from x.val.1) }

/-- Once the exact value is known, the canonical magnitude proof contains only arithmetic. -/
noncomputable def magnitudeAlgorithm : Algorithm repeatModel magnitudeSpecification :=
  repeatAlgorithm.mapPost _ fun d _ x _ _ m hg => by
    refine ⟨(d 0 : ℝ) * (show ℝ from x.val.1), hg, ?_⟩
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (d 0))]

/-- Mixed allocation has the same resource limits and leaves every cell unreadable. -/
noncomputable def cleanedSpecification : Specification Empty Empty mixedProblem :=
  { mixedSpecification with good := fun _ _ _ _ m =>
      m.pos = 0 ∧ ∀ b i, m.store.get b i = none }

/-- No allocation, index, cost, format or workspace proof is repeated for the new property. -/
noncomputable def cleanedAlgorithm : Algorithm mixedModel cleanedSpecification :=
  mixedAlgorithm.mapPost _ fun _ _ _ _ _ m hg => by
    refine ⟨hg.2, ?_⟩
    intro b i
    simp [hg.1, Store.get]

/-- Postcondition transport preserves the actual first-order program. -/
example : magnitudeAlgorithm.program = repeatAlgorithm.program := rfl

/-- The different mixed-allocation example also retains its exact program. -/
example : cleanedAlgorithm.program = mixedAlgorithm.program := rfl

end NLAlib.Ops.Examples.Consequences
