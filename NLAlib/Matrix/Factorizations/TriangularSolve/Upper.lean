/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.TriangularSolve.Routine

/-!
# Back substitution with an upper triangular stored matrix

The existing back-substitution routine reads the transpose of a stored lower factor.
This routine reads an upper factor directly, in the same column-major representation used
by LU. Its judgment reuses the shared substitution-loop proof; no transpose copy is made.

## Main results

* `NLAlib.TriangularSolve.upper_meets`: the direct upper solve gives its rounding trace.
-/

@[expose] public section

namespace NLAlib.TriangularSolve

open Ops Computation

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Back substitution on the upper triangle of a packed matrix, in place on the right-hand
side. One scoped scratch cell holds each product. -/
def upper : Routine Op Tst := routine% [n] (U : n * n, x : n) → (x) {
  let t ← alloc 1;
  for i < n {
    for j < i {
      call (Has.inj ScalarOp.mul) [] (U[(n - 1 - j) * n + (n - 1 - i)],
        x[(n - 1 - j)]) → (t);
      call (Has.inj ScalarOp.sub) [] (x[(n - 1 - i)], t) → (x[(n - 1 - i)])
    };
    call (Has.inj ScalarOp.div) [] (x[(n - 1 - i)],
      U[(n - 1 - i) * n + (n - 1 - i)]) → (x[(n - 1 - i)])
  }
}

variable [Inhabited K]

/-- The output is a back-substitution trace for the supplied upper matrix, with nonzero
stored diagonal. The transposition in the trace's argument compensates for its convention
of taking a stored lower factor. -/
def upperSpec (u : ℝ) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (Us, xs) → (xs')
    requires ∀ i < n, dec (vec Us (i * n + i)) ≠ 0
    ensures IsBackSubstTrace u (fun i j => dec (vec Us (i * n + j)))
      (fun i => dec (vec xs i)) n (fun i => dec (vec xs' i))

/-- Direct upper substitution meets its trace specification under the standard scalar
rounding model and a nonzero stored diagonal. Only the right-hand side is written. -/
theorem upper_meets {M : Machine K} {I : Interp Op Tst K} {u : ℝ} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : StdModel u dec M) :
    (upper (Op := Op) (Tst := Tst)).Meets I (upperSpec u dec) := by
  routine_intro [n] (U, x) reads (Us, xs)
  change Writes .total I τ _ (Env.frame [n] [U, x, x]) (Fp.blocks [x] [n]) _ m
  alloc as t
  have hUs₁ := Store.Below.readBlock_of hbelow_t hl.1 hUs
  have hne : ∀ r < n, dec (vec Us ((n - 1 - r) * n + (n - 1 - r))) ≠ 0 :=
    fun r hr => hpre (n - 1 - r) (by omega)
  refine (writes_substLoop (τ := τ) (m := ⟨s_t, m.pos⟩) hI hM (n := n) rfl (fun _ _ => rfl)
    (σ := fun r => n - 1 - r) (x := x) (w := (t, 0))
    (p := fun r j => (U.1, U.2 + (n - 1 - j) * n + (n - 1 - r)))
    (e := fun r => (U.1, U.2 + (n - 1 - r) * n + (n - 1 - r)))
    (T := fun r j => vec Us ((n - 1 - j) * n + (n - 1 - r))) (xs := xs)
    (fun _ _ => by omega) (fun r hr l hl h => by
      have h' : n - 1 - r = n - 1 - l := h
      omega)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun r hr j hj => get_matrix_entry hUs₁ (by omega) (by omega))
    (fun r hr => get_matrix_entry hUs₁ (by omega) (by omega))
    (fun _ _ _ _ => hUx) (fun _ _ => hUx)
    (fun _ _ _ _ => Nat.ne_of_lt hl.1) (fun _ _ => Nat.ne_of_lt hl.1) (Nat.ne_of_lt hl.2)
    (Nat.lt_of_lt_of_eq Nat.one_pos ht.symm)
    (Store.Below.readBlock_of hbelow_t hl.2 hxs) hne).mono ?_ ?_
  · fp_sub
  · rintro m' - ⟨hpos, ys, hys, htr⟩ s₂ - hB
    exact ⟨hpos, [ys], Mem.readBlocks_of_cons (Store.Below.readBlock_of hB hl.2 hys) rfl, htr⟩

end NLAlib.TriangularSolve
