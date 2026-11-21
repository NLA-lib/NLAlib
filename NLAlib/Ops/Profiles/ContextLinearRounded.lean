/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.ContextLinear
public import NLAlib.Ops.Profiles.ContextDenseRounded

/-!
# Rounded local contracts for a stored matrix context

The fixed context transformation reads the isolated matrix through scalar arithmetic. Scalar
and vector calls retain their declared local contracts. The proof-side fallback forwards those
same calls and interprets only the matrix product exactly, outside the isolated regime.

## Main results

* `NLAlib.Ops.ContextLinearRounded.relation`: exhaustive rounded source relations.
* `NLAlib.Ops.ContextLinearRounded.fallback_satisfies`: jointly valid proof-side fallback.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Ops.ContextLinearRounded

/-- Rounded real vector relations indexed by the existing level-one operation names. -/
def blasRelation (e : Blas1Err) : Blas1Op → BlockRel ℝ
  | .sum => sumRel id e.sum
  | .dot => dotRel id e.dot
  | .axpy => axpyRel id e.axpy
  | .nrm2 => nrm2Rel id e.dot e.sqrt
  | .scal => scalRel id e.scal
  | .copy => copyRel

/-- Scalar machine functions, rounded vector relations and a normwise matrix product. -/
noncomputable def relation {n : ℕ} (M : Machine ℝ) (e : Blas1Err)
    (A : Matrix (Fin n) (Fin n) ℝ) (error : ℝ) : Standard.Operation → BlockRel ℝ
  | .scalar o => (M.fn o).rel
  | .blas o => blasRelation e o
  | .matvec => matvecErrorRel id A error

/-- Vector admission is explicit, while matrix products have their ordinary separate output. -/
def admissible (ok : ℕ → Prop) (n : ℕ) :
    Standard.Operation → List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop
  | .scalar _ => AnyOperands
  | .blas .axpy | .blas .scal => InPlace ok
  | .blas _ => OutApart ok
  | .matvec => MatvecOperands n n

/-- Recover the standard numerical interfaces from the exhaustive source relations. -/
theorem laws {n : ℕ} {M : Machine ℝ} {e : Blas1Err} {ok : ℕ → Prop}
    {A : Matrix (Fin n) (Fin n) ℝ} {error : ℝ}
    {I : Interp Standard.Operation CmpTst ℝ}
    (h : ∀ o, I.Satisfies .total o ((relation M e A error o).spec (admissible ok n o))) :
    IsScalar M I ∧ IsBlas1 id e ok I ∧ IsMatvec id A error I :=
  ⟨fun o => h (.scalar o),
    ⟨h (.blas .sum), h (.blas .dot), h (.blas .axpy), h (.blas .nrm2),
      h (.blas .scal), h (.blas .copy)⟩, h .matvec⟩

/-- Outside the isolated context, keep the target's scalar/vector behavior and use an exact
matrix product. This interpreter exists only inside the proof, never in the executed tree. -/
noncomputable def fallback {n : ℕ} (I : Interp RCLikeBlas.Operation CmpTst ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Interp Standard.Operation CmpTst ℝ where
  call o := match o with
    | .scalar a => I.call (.inl a)
    | .blas a => I.call (.inr a)
    | .matvec => (Functional.interp id (fun _ : Standard.Operation => exactMatvecFn A)).call o
  test := I.test
  index := I.index

/-- Target local contracts and a nonnegative matvec allowance jointly realize every source
contract even outside the isolated snapshot. No numerical output is a premise. -/
theorem fallback_satisfies {n : ℕ} {M : Machine ℝ} {e : Blas1Err} {ok : ℕ → Prop}
    {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar M I) (hB : IsBlas1 id e ok I)
    (A : Matrix (Fin n) (Fin n) ℝ) {error : ℝ} (herror : 0 ≤ error) (o : Standard.Operation) :
    (fallback I A).Satisfies .total o ((relation M e A error o).spec (admissible ok n o)) := by
  cases o with
  | scalar a => exact hS a
  | blas a => cases a with
    | sum => exact hB.sum
    | dot => exact hB.dot
    | axpy => exact hB.axpy
    | nrm2 => exact hB.nrm2
    | scal => exact hB.scal
    | copy => exact hB.copy
  | matvec =>
    have hA : IsExactMatvec id A (fallback I A) :=
      (Interp.ofFns_isFn (Tst := CmpTst)
        (fun _ : Standard.Operation => exactMatvecFn A) .total .matvec AnyOperands).satisfies_matvec
    exact hA.isMatvec herror

end NLAlib.Ops.ContextLinearRounded
