/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.CholeskyRoundingError
public import NLAlib.Matrix.Factorizations.TriangularSolve.Substitution

/-!
# Forward and back substitution as routines

`NLAlib.TriangularSolve.forward` solves with a lower triangular matrix stored by columns and
`NLAlib.TriangularSolve.backward` with its transpose, both in place, over scalar operations. The
running value of a row is kept in the cell of its solution entry, so one scratch cell (the
product) suffices. Both are generic over the signature, so each can be run at a precision tag.

## Main definitions

* `NLAlib.TriangularSolve.forward`, `NLAlib.TriangularSolve.forwardSpec`: forward substitution.
* `NLAlib.TriangularSolve.backward`, `NLAlib.TriangularSolve.backwardSpec`: back substitution
  with the transpose.

## Main results

* `NLAlib.TriangularSolve.forward_meets`: the block written is a substitution trace.
* `NLAlib.TriangularSolve.backward_meets`: the block written is a back substitution trace.
-/

@[expose] public section

namespace NLAlib.TriangularSolve

open Ops Computation

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- **Forward substitution** with the lower triangle of $\mathbf{L}$, stored by columns, in place
on $\mathbf{x}$. -/
def forward : Routine Op Tst := routine% [n] (L : n * n, x : n) → (x) {
  let t ← alloc 1;
  for i < n {
    for j < i {
      call (Has.inj ScalarOp.mul) [] (L[j * n + i], x[j]) → (t);
      call (Has.inj ScalarOp.sub) [] (x[i], t) → (x[i])
    };
    call (Has.inj ScalarOp.div) [] (x[i], L[i * n + i]) → (x[i])
  }
}

/-- **Back substitution** with the transpose of the lower triangle of $\mathbf{L}$, stored by
columns, in place on $\mathbf{x}$; rows are taken from the last. -/
def backward : Routine Op Tst := routine% [n] (L : n * n, x : n) → (x) {
  let t ← alloc 1;
  for i < n {
    for j < i {
      call (Has.inj ScalarOp.mul) [] (L[(n - 1 - i) * n + (n - 1 - j)], x[(n - 1 - j)]) → (t);
      call (Has.inj ScalarOp.sub) [] (x[(n - 1 - i)], t) → (x[(n - 1 - i)])
    };
    call (Has.inj ScalarOp.div) [] (x[(n - 1 - i)],
      L[(n - 1 - i) * n + (n - 1 - i)]) → (x[(n - 1 - i)])
  }
}

variable [Inhabited K]

/-- With a nonzero stored diagonal, the block written is a trace of forward substitution at unit
roundoff $u$ on the decoded matrix and right-hand side. -/
def forwardSpec (u : ℝ) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (Ls, xs) → (xs')
    requires ∀ i < n, dec (vec Ls (i * n + i)) ≠ 0
    ensures IsSubstTrace (fun _ => RelErr u) (fun i j => dec (vec Ls (j * n + i)))
      (fun i => dec (vec xs i)) n (fun i => dec (vec xs' i))

/-- With a nonzero stored diagonal, the block written is a trace of back substitution with the
transpose, at unit roundoff $u$, on the decoded matrix and right-hand side. -/
def backwardSpec (u : ℝ) (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (Ls, xs) → (xs')
    requires ∀ i < n, dec (vec Ls (i * n + i)) ≠ 0
    ensures IsBackSubstTrace u (fun i j => dec (vec Ls (j * n + i)))
      (fun i => dec (vec xs i)) n (fun i => dec (vec xs' i))

/-- Forward substitution meets its specification under the standard model, for a nonzero stored
diagonal. -/
theorem forward_meets {M : Machine K} {I : Interp Op Tst K} {u : ℝ} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : StdModel u dec M) :
    (forward (Op := Op) (Tst := Tst)).Meets I (forwardSpec u dec) := by
  routine_intro [n] (L, x) reads (Ls, xs)
  change Writes .total I τ _ (Env.frame [n] [L, x, x]) (Fp.blocks [x] [n]) _ m
  alloc as t
  have hLs₁ := Store.Below.readBlock_of hbelow_t hl.1 hLs
  refine (writes_substLoop (τ := τ) (m := ⟨s_t, m.pos⟩) hI hM (n := n) rfl (fun _ _ => rfl)
    (σ := fun r => r) (x := x) (w := (t, 0))
    (p := fun r j => (L.1, L.2 + j * n + r)) (e := fun r => (L.1, L.2 + r * n + r))
    (T := fun r j => vec Ls (j * n + r)) (xs := xs)
    (fun _ hr => hr) (fun _ _ _ _ h => h)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun r hr j hj => get_matrix_entry hLs₁ (by omega) hr)
    (fun r hr => get_matrix_entry hLs₁ hr hr)
    (fun _ _ _ _ => hLx) (fun _ _ => hLx)
    (fun _ _ _ _ => Nat.ne_of_lt hl.1) (fun _ _ => Nat.ne_of_lt hl.1) (Nat.ne_of_lt hl.2)
    (Nat.lt_of_lt_of_eq Nat.one_pos ht.symm)
    (Store.Below.readBlock_of hbelow_t hl.2 hxs) hpre).mono ?_ ?_
  · fp_sub
  · rintro m' - ⟨hpos, ys, hys, htr⟩ s₂ - hB
    exact ⟨hpos, [ys], Mem.readBlocks_of_cons (Store.Below.readBlock_of hB hl.2 hys) rfl, htr⟩

/-- Back substitution with the transpose meets its specification under the standard model, for a
nonzero stored diagonal. -/
theorem backward_meets {M : Machine K} {I : Interp Op Tst K} {u : ℝ} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : StdModel u dec M) :
    (backward (Op := Op) (Tst := Tst)).Meets I (backwardSpec u dec) := by
  routine_intro [n] (L, x) reads (Ls, xs)
  change Writes .total I τ _ (Env.frame [n] [L, x, x]) (Fp.blocks [x] [n]) _ m
  alloc as t
  have hLs₁ := Store.Below.readBlock_of hbelow_t hl.1 hLs
  have hne : ∀ r < n, dec (vec Ls ((n - 1 - r) * n + (n - 1 - r))) ≠ 0 :=
    fun r hr => hpre (n - 1 - r) (by omega)
  refine (writes_substLoop (τ := τ) (m := ⟨s_t, m.pos⟩) hI hM (n := n) rfl (fun _ _ => rfl)
    (σ := fun r => n - 1 - r) (x := x) (w := (t, 0))
    (p := fun r j => (L.1, L.2 + (n - 1 - r) * n + (n - 1 - j)))
    (e := fun r => (L.1, L.2 + (n - 1 - r) * n + (n - 1 - r)))
    (T := fun r j => vec Ls ((n - 1 - r) * n + (n - 1 - j))) (xs := xs)
    (fun _ _ => by omega) (fun r hr l hl h => by
      have h' : n - 1 - r = n - 1 - l := h
      omega)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)
    (fun r hr j hj => get_matrix_entry hLs₁ (by omega) (by omega))
    (fun r hr => get_matrix_entry hLs₁ (by omega) (by omega))
    (fun _ _ _ _ => hLx) (fun _ _ => hLx)
    (fun _ _ _ _ => Nat.ne_of_lt hl.1) (fun _ _ => Nat.ne_of_lt hl.1) (Nat.ne_of_lt hl.2)
    (Nat.lt_of_lt_of_eq Nat.one_pos ht.symm)
    (Store.Below.readBlock_of hbelow_t hl.2 hxs) hne).mono ?_ ?_
  · fp_sub
  · rintro m' - ⟨hpos, ys, hys, htr⟩ s₂ - hB
    exact ⟨hpos, [ys], Mem.readBlocks_of_cons (Store.Below.readBlock_of hB hl.2 hys) rfl, htr⟩

end NLAlib.TriangularSolve
