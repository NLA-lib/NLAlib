/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.ContextDense

/-!
# Rounded dense context calls

The existing fixed dense leaf reads the declared isolated raw matrix and performs the
supplied machine's scalar operations. A local numerical kernel bound transfers to its
operator contract; totality and storage preservation follow from the generic word proof.

## Main results

* `NLAlib.Ops.ContextDenseRounded.output_eq_ofFn_wordKernel`: the output of the leaf is the
  word kernel of the stored rows.
-/

@[expose] public section

namespace NLAlib.Ops.ContextDenseRounded

open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op]

/-- The deterministic vector action of the actual scalar dense row recurrence. -/
noncomputable def wordKernel (M : Machine ℝ) (n : ℕ) (raw : List ℝ)
    (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => StoredDense.rowWord M n n raw (List.ofFn v) i

/-- The actual output words are exactly the fixed vector kernel on the actual input words. -/
theorem output_eq_ofFn_wordKernel (M : Machine ℝ) (n : ℕ) (raw xs : List ℝ)
    (hx : xs.length = n) :
    (List.range n).map (StoredDense.rowWord M n n raw xs) =
      List.ofFn (wordKernel M n raw (decv id n xs)) := by
  unfold wordKernel
  rw [ofFn_decv hx]
  apply List.ext_getElem <;> simp

end NLAlib.Ops.ContextDenseRounded
