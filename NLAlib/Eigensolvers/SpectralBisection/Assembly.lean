/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.SpectralBisection

/-!
# Mathematical assembly of bisection child results

A node outcome specifies its children and combines their basis/eigenvalue outputs. This is
ordinary dependent matrix mathematics, factored from the existing recursive algorithm for
reuse in upward traversal proofs.

## Main results

* `NLAlib.EighStep.assemble`: the mathematical output assembled from child results.
* `NLAlib.eighAux_succ_eq_assemble`: the existing recursion uses exactly this assembly.
-/

@[expose] public section

namespace NLAlib

/-- The dimension of a child of a node outcome. Leaves have no occupied child. -/
def EighStep.childSize {F : Type*} {k : ℕ} : EighStep F k → Bool → ℕ
  | .leaf .., _ => 0
  | .shift .., _ => k
  | .split kp .., true => kp
  | .split kp .., false => k - kp

/-- A constructor's occupied children. A shifted node has only its selected side. -/
def EighStep.HasChild {F : Type*} {k : ℕ} : EighStep F k → Bool → Prop
  | .leaf .., _ => False
  | .shift side .., b => b = side
  | .split .., _ => True

/-- The slot of a mathematical child within its parent's interval. -/
def EighStep.childSlot {F : Type*} {k : ℕ} (step : EighStep F k) (lo : ℕ) (b : Bool) : ℕ :=
  match step, b with
  | .split kp .., false => lo + kp
  | _, _ => lo

/-- The mathematical matrix passed to each child. A leaf's empty child is never evaluated
by assembly; its empty matrix needs no distinguished scalar value. -/
def EighStep.childMatrix {F : Type*} {k : ℕ} :
    (step : EighStep F k) → (b : Bool) →
      Matrix (Fin (step.childSize b)) (Fin (step.childSize b)) (F × F)
  | .leaf .., _ => Matrix.of fun i _ => i.elim0
  | .shift _ A _, _ => A
  | .split _ _ _ _ Ap _ _, true => Ap
  | .split _ _ _ _ _ Am _, false => Am

/-- Assemble a leaf, a shifted child, or the two projected children with their shifted
values. The split uses exactly the finite sum equivalence of the recursive algorithm. -/
def EighStep.assemble {F Su Sg : Type*} (M : FloatMachine F Su Sg) {k : ℕ}
    (step : EighStep F k)
    (child : (b : Bool) → Matrix (Fin (step.childSize b)) (Fin (step.childSize b)) (F × F) ×
      (Fin (step.childSize b) → F)) :
    Matrix (Fin k) (Fin k) (F × F) × (Fin k → F) :=
  match step with
  | .leaf U d => (U, d)
  | .shift b _ sigma => ((child b).1, fun i => M.add ((child b).2 i) sigma)
  | .split kp hp Qp Qm _ _ sigma =>
    let e : Fin k ≃ Fin kp ⊕ Fin (k - kp) :=
      (finCongr (Nat.add_sub_of_le hp).symm).trans finSumFinEquiv.symm
    ((Matrix.fromCols (M.mm Qp (child true).1) (M.mm Qm (child false).1)).submatrix id e,
      fun i => Sum.elim (fun j => M.add ((child true).2 j) sigma)
        (fun j => M.sub ((child false).2 j) sigma) (e i))

/-- The recursive mathematical algorithm combines its child outputs by ordinary assembly. -/
theorem eighAux_succ_eq_assemble {F Su Sg : Type*} [Inhabited Sg] (M : FloatMachine F Su Sg)
    (N signFuel : ℕ) (R₀ beta : F) (f : ℕ) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) (F × F)) (R eps : F) (ell : ℕ)
    (samples : List Bool → EighSample Su Sg N) :
    eighAux M N signFuel R₀ beta (f + 1) A R eps ell samples =
      let step := eighStep M N signFuel R₀ beta A R eps ell (samples [])
      let p := eighNextParams M R eps ell
      step.assemble M (fun b => eighAux M N signFuel R₀ beta f (step.childMatrix b)
        p.1 p.2 (ell + 1) (fun a => samples (b :: a))) := by
  simp only [eighAux]
  cases h : eighStep M N signFuel R₀ beta A R eps ell (samples []) <;>
    simp only [EighStep.assemble, EighStep.childMatrix, EighStep.childSize]

end NLAlib
