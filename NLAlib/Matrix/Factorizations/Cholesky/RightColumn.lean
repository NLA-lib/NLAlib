/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Level1

/-!
# Right-looking Cholesky column normalization

The residual pivot and the entries below it determine one contiguous factor-column suffix.
The scalar tree computes the pivot square root, copies the residual column and divides each
entry by that saved root. A single output operand contains the diagonal followed by the
normalized entries, allowing the full factorization to write one packed factor column.

## Main results

* `NLAlib.Cholesky.rightColumn_meets`: exact machine-word normalization of one factor column.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Square-root the pivot, copy and normalize the residual entries below it, and write the
root as the first entry of the same contiguous output. Every arithmetic step is scalar. -/
def rightColumn : Routine Op Tst := routine% [n] (p : 1, x : n) → (y : n + 1) {
  let t ← alloc 1;
  call (Has.inj ScalarOp.sqrt) [] (p) → (t);
  run (copyLoopRoutine (Op := Op) (Tst := Tst)) [n] (x, y[1]);
  run (scalLoopRoutine (Op := Op) (Tst := Tst)) [n] (t, y[1]);
  call (Has.inj ScalarOp.copy) [] (t) → (y)
}

variable [Inhabited K]

/-- The words of a right-looking factor-column suffix: the machine square root followed
by the actual scalar quotients of the supplied residual words by that root. -/
def rightColumnSpec (M : Machine K) : Routine.Spec K :=
  spec% [n] ([p], xs) → (ys) ensures
    ys = M.sqrt p :: scalF M (M.sqrt p) (vec xs) n

/-- The right-looking column tree computes its stated word list for every scalar machine.
Numerical validity of the root and divisor belongs to the factorization error argument. -/
theorem rightColumn_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (rightColumn (Op := Op) (Tst := Tst)).Meets I (rightColumnSpec M) := by
  routine_intro [n] (p, x, y) reads (ps, xs)
  obtain ⟨v, hv, rfl⟩ := Store.readBlock_one_eq_some.mp hps
  obtain ⟨hlp, hlx, hly⟩ := hl
  change Writes .total I τ _ (Env.frame [n] [p, x, y]) (Fp.blocks [y] [n + 1]) _ m
  alloc as t
  have hty : t ≠ y.1 := by
    change m.store.length ≠ y.1
    exact Nat.ne_of_gt hly
  step (hI .sqrt) as m₁ hfr₁ ⟨hpos₁, r, hr, rfl⟩
  call (copyLoopRoutine_meets hI (fun _ => True)) [n] (x, (y.1, y.2 + 1))
    as m₂ hfr₂ hpos₂ (copied) hcopied
  obtain rfl : copied = xs := (List.cons.inj hcopied).1
  call (scalLoopRoutine_meets_exact hI) [n] ((t, 0), (y.1, y.2 + 1))
    as m₃ hfr₃ hpos₃ (scaled) hscaled
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change m.store.length < m₂.store.length ∧ y.1 < m₂.store.length
    simp only [List.length_singleton] at hlen_t
    constructor <;> omega
  step (hI .copy) as m₄ hfr₄ ⟨hpos₄, root, hroot, rfl⟩
  have htail : m₄.store.readBlock y.1 (y.2 + 1) n = some scaled := by keep
  intro s₂ hs₂ hB₂
  refine ⟨?_, [M.sqrt v :: scaled], Mem.readBlocks_of_cons ?_ rfl, ?_⟩
  · change m₄.pos = m.pos + 0
    omega
  · have hd := Store.Below.get_of hB₂ hly hroot
    have ht := Store.Below.readBlock_of hB₂ hly htail
    simp only [Store.readBlock_succ, hd, ht, Option.bind_some, Option.map_some]
  · change M.sqrt v :: scaled = M.sqrt v :: scalF M (M.sqrt v) (vec copied) n
    exact congrArg (List.cons _) hscaled

end NLAlib.Cholesky
