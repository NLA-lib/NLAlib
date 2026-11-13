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

The fixed context transformation reads the protected matrix through scalar arithmetic. Scalar
and vector calls retain their declared local contracts. The proof-side fallback forwards those
same calls and interprets only the matrix product exactly, outside the protected regime.

## Main results

* `NLAlib.Ops.ContextLinearRounded.relation`: exhaustive rounded source relations.
* `NLAlib.Ops.ContextLinearRounded.fallback_meets`: jointly valid proof-side fallback.
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
    (h : ∀ o, I.Meets .total o ((relation M e A error o).spec (admissible ok n o))) :
    IsScalar M I ∧ IsBlas1 id e ok I ∧ IsMatvec id A error I :=
  ⟨fun o => h (.scalar o),
    ⟨h (.blas .sum), h (.blas .dot), h (.blas .axpy), h (.blas .nrm2),
      h (.blas .scal), h (.blas .copy)⟩, h .matvec⟩

/-- Outside the protected context, keep the target's scalar/vector behavior and use an exact
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
contract even outside the protected snapshot. No numerical output is a premise. -/
theorem fallback_meets {n : ℕ} {M : Machine ℝ} {e : Blas1Err} {ok : ℕ → Prop}
    {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar M I) (hB : IsBlas1 id e ok I)
    (A : Matrix (Fin n) (Fin n) ℝ) {error : ℝ} (herror : 0 ≤ error) (o : Standard.Operation) :
    (fallback I A).Meets .total o ((relation M e A error o).spec (admissible ok n o)) := by
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
        (fun _ : Standard.Operation => exactMatvecFn A) .total .matvec AnyOperands).meets_matvec
    exact hA.isMatvec herror

/-- A context-protected scalar dense product meets its rounded local source contract. Its
error premise concerns only the actual word kernel, not an execution of the enclosing program. -/
theorem matvec_active {I : Interp RCLikeBlas.Operation CmpTst ℝ} {M : Machine ℝ}
    (hS : IsScalar M I) (context : List (ℕ × ℕ)) (index : Fin context.length)
    {n cutoff : ℕ} {reference : Store ℝ} (raw : List ℝ) {e : Blas1Err} {error : ℝ}
    {ok : ℕ → Prop}
    (hError : ∀ xs : List ℝ,
      ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n xs -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw xs)))‖ ≤
          error * ‖WithLp.toLp 2 (decv id n xs)‖)
    (hc : ∀ z ∈ context, z.1 < cutoff)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw)
    {d : List ℕ} {ins outs : List (ℕ × ℕ)} {τ : Tape ℝ} {mem : Mem ℝ}
    (hs : mem.ContextSnapshot cutoff reference) (ho : ∀ z ∈ outs, cutoff ≤ z.1)
    (hp : (((relation M e (StoredOperator.denseMatrix n n raw) error .matvec).spec
      (admissible ok n .matvec)).on .total d ins outs τ mem).pre mem) :
    Mode.total.Holds ((I.linkContext (ContextLinear.table context.length index) context).callS
      .matvec d ins outs τ mem)
      ((((relation M e (StoredOperator.denseMatrix n n raw) error .matvec).spec
        (admissible ok n .matvec)).on .total d ins outs τ mem).post mem) := by
  have hi := hc context[index] (List.getElem_mem ..)
  have hd := (hs.2.readBlock hi context[index].2 (n * n)).trans hData
  exact ContextDenseRounded.callS_source hS context index rfl raw hError
    (hs.live hc) hi hd ho hp

/-- Protected matrix data and the target's local scalar/vector contracts give exhaustive
rounded source laws for the proof-side guarded interpretation. -/
theorem meets_guarded {I : Interp RCLikeBlas.Operation CmpTst ℝ} {M : Machine ℝ}
    {e : Blas1Err} {ok : ℕ → Prop} (hS : IsScalar M I) (hB : IsBlas1 id e ok I)
    (context : List (ℕ × ℕ)) (index : Fin context.length) {n cutoff : ℕ}
    (reference : Store ℝ) (raw : List ℝ) {error : ℝ} (herror : 0 ≤ error)
    (hError : ∀ xs : List ℝ,
      ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n xs -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw xs)))‖ ≤
          error * ‖WithLp.toLp 2 (decv id n xs)‖)
    (hc : ∀ z ∈ context, z.1 < cutoff)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw) :
    ∀ o, ((I.linkContext (ContextLinear.table context.length index) context).guardContext
      (fun o => (relation M e (StoredOperator.denseMatrix n n raw) error o).spec
        (admissible ok n o)) (Mem.ContextSnapshot cutoff reference) cutoff
      (fallback I (StoredOperator.denseMatrix n n raw))).Meets .total o
      ((relation M e (StoredOperator.denseMatrix n n raw) error o).spec (admissible ok n o)) := by
  intro o
  apply Interp.meets_guardContext _ _ _ _ _ _ (fallback_meets hS hB _ herror o)
  intro d ins outs τ mem hs ho hp
  cases o with
  | scalar o =>
    rw [Interp.linkContext_callS_inr I (by rfl)]
    exact hS o d ins outs τ mem hp
  | blas o =>
    rw [Interp.linkContext_callS_inr I (by rfl)]
    cases o with
    | sum => exact hB.sum d ins outs τ mem hp
    | dot => exact hB.dot d ins outs τ mem hp
    | axpy => exact hB.axpy d ins outs τ mem hp
    | nrm2 => exact hB.nrm2 d ins outs τ mem hp
    | scal => exact hB.scal d ins outs τ mem hp
    | copy => exact hB.copy d ins outs τ mem hp
  | matvec => exact matvec_active hS context index raw hError hc hData hs ho hp

/-- Guarded rounded source laws for reusing an existing total numerical word theorem.
The protected matrix is decoded from the raw input words and comparisons stay unchanged. -/
theorem guarded_laws {I : Interp RCLikeBlas.Operation CmpTst ℝ} {M : Machine ℝ}
    {e : Blas1Err} {ok : ℕ → Prop} (hS : IsScalar M I) (hB : IsBlas1 id e ok I)
    (hCmp : IsCmp id I) (context : List (ℕ × ℕ)) (index : Fin context.length)
    {n cutoff : ℕ} (reference : Store ℝ) (raw : List ℝ) {error : ℝ} (herror : 0 ≤ error)
    (hError : ∀ xs : List ℝ,
      ‖WithLp.toLp 2 (StoredOperator.denseMatrix n n raw *ᵥ decv id n xs -
        decv id n ((List.range n).map (StoredDense.rowWord M n n raw xs)))‖ ≤
          error * ‖WithLp.toLp 2 (decv id n xs)‖)
    (hc : ∀ z ∈ context, z.1 < cutoff)
    (hData : reference.readBlock context[index].1 context[index].2 (n * n) = some raw) :
    let J := (I.linkContext (ContextLinear.table context.length index) context).guardContext
      (fun o => (relation M e (StoredOperator.denseMatrix n n raw) error o).spec
        (admissible ok n o)) (Mem.ContextSnapshot cutoff reference) cutoff
      (fallback I (StoredOperator.denseMatrix n n raw))
    IsScalar M J ∧ IsBlas1 id e ok J ∧
      IsMatvec id (StoredOperator.denseMatrix n n raw) error J ∧ IsCmp id J := by
  obtain ⟨hs, hb, ha⟩ := laws
    (meets_guarded hS hB context index reference raw herror hError hc hData)
  exact ⟨hs, hb, ha, hCmp⟩

end NLAlib.Ops.ContextLinearRounded
