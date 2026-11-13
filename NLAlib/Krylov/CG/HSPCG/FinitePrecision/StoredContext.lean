/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.StoredContext
public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Preconditioner
public import NLAlib.Matrix.FinitePrecision.StoredDense
public import NLAlib.Ops.Profiles.ContextLinearRounded
public import NLAlib.Ops.Profiles.RoundedScalarBlas

/-!
# Rounded scalar implementations of both stored PCG operators

Both operator capabilities retain the actual input words. The system contract follows from
standard scalar rounding. The applied inverse preconditioner is the actual deterministic
scalar row kernel, represented by the existing possibly nonlinear matrix-vector oracle.
The context guard is used only in the proof; its fallback is never emitted in the program.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.StoredContext.oracle`: the actual preconditioner action.
* `NLAlib.Krylov.CG.HSPCG.Rounded.StoredContext.guarded_meets`: both raw operator contracts.
* `NLAlib.Krylov.CG.HSPCG.Rounded.StoredContext.scalar_guarded_laws`: scalar-only backend laws.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded.StoredContext

open Ops

/-- Relative normwise allowance of the actual dense scalar row implementation. -/
noncomputable def relativeError (u : ℝ) (n : ℕ) : ℝ :=
  ScalarProducts.roundoff u n * Real.sqrt n

/-- The dense scalar allowance is nonnegative at nonnegative unit roundoff. -/
theorem relativeError_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    0 ≤ relativeError u n :=
  mul_nonneg (ScalarProducts.roundoff_nonneg hu n) (Real.sqrt_nonneg _)

/-- The existing oracle with the actual scalar row action and decoded raw reference matrix.
Its accuracy is derived from scalar standard-model laws, with no supplied oracle callback. -/
noncomputable def oracle {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu : 0 ≤ u) (n : ℕ) (raw : List ℝ) :
    MatvecOracle (StoredOperator.denseMatrix n n raw) where
  mulVec := ContextDenseRounded.wordKernel M n raw
  ε := relativeError u n
  ε_nonneg := relativeError_nonneg hu n
  norm_sub_mulVec_le v := by
    have h := hM.norm_mulVec_sub_rowWord_le hu n n raw (List.ofFn v)
    have hout : decv id n ((List.range n).map
        (StoredDense.rowWord M n n raw (List.ofFn v))) =
        ContextDenseRounded.wordKernel M n raw v :=
      funext fun i => StoredDense.decv_map_rowWord M n n raw (List.ofFn v) i
    simpa only [decv_ofFn, hout, relativeError] using h

/-- Exhaustive source relations: local scalar/BLAS laws, rounded system multiplication,
and the functional action of the actual stored preconditioner. -/
noncomputable def relation (M : Machine ℝ) (e : Blas1Err) (u : ℝ)
    (n : ℕ) (systemRaw preconditionerRaw : List ℝ) : Signature → BlockRel ℝ
  | .scalar o => (M.fn o).rel
  | .blas o => ContextLinearRounded.blasRelation e o
  | .operator => matvecErrorRel id (StoredOperator.denseMatrix n n systemRaw)
      (relativeError u n * specNorm (StoredOperator.denseMatrix n n systemRaw))
  | .preconditioner => (matvecFn
      (ContextDenseRounded.wordKernel M n preconditionerRaw)).rel

/-- The same explicit admissions as the existing two-operator PCG storage profile. -/
abbrev admissible := HSPCG.StoredContext.admissible

/-- The fixed two-operator context table preserves scalar and vector calls. -/
abbrev table := HSPCG.StoredContext.table

/-- Proof-side fallback keeps actual scalar/vector operations and uses only local reference
operator functions outside the protected context. -/
noncomputable def fallback {n : ℕ} (I : Interp RCLikeBlas.Operation CmpTst ℝ)
    (M : Machine ℝ) (systemRaw preconditionerRaw : List ℝ) :
    Interp Signature CmpTst ℝ where
  call o := match o with
    | .scalar a => I.call (.inl a)
    | .blas a => I.call (.inr a)
    | .operator => (Functional.interp id (fun _ : Signature =>
        exactMatvecFn (StoredOperator.denseMatrix n n systemRaw))).call o
    | .preconditioner => (Functional.interp id (fun _ : Signature =>
        matvecFn (ContextDenseRounded.wordKernel M n preconditionerRaw))).call o
  test := I.test
  index := I.index

/-- Every fallback primitive satisfies its declared local relation. -/
theorem fallback_meets {n : ℕ} {M : Machine ℝ} {e : Blas1Err} {u : ℝ}
    {I : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar M I) (hB : IsBlas1 id e (fun _ => True) I) (hu : 0 ≤ u)
    (systemRaw preconditionerRaw : List ℝ) (o : Signature) :
    (fallback (n := n) I M systemRaw preconditionerRaw).Meets .total o
      ((relation M e u n systemRaw preconditionerRaw o).spec (admissible n o)) := by
  cases o with
  | scalar a => exact hS a
  | blas a => cases a with
    | sum => exact hB.sum
    | dot => exact hB.dot
    | axpy => exact hB.axpy
    | nrm2 => exact hB.nrm2
    | scal => exact hB.scal
    | copy => exact hB.copy
  | operator =>
    have hA : IsExactMatvec id (StoredOperator.denseMatrix n n systemRaw)
        (fallback (n := n) I M systemRaw preconditionerRaw) :=
      (Interp.ofFns_isFn (Tst := CmpTst) (fun _ : Signature =>
        exactMatvecFn (StoredOperator.denseMatrix n n systemRaw)) .total .operator
          AnyOperands).meets_matvec
    exact hA.isMatvec (mul_nonneg (relativeError_nonneg hu n) (specNorm_nonneg _))
  | preconditioner =>
    exact Interp.ofFns_isFn (Tst := CmpTst) (fun _ : Signature =>
      matvecFn (ContextDenseRounded.wordKernel M n preconditionerRaw)) .total
        .preconditioner (MatvecOperands n n)

/-- Protected delegation to both actual raw operators. This definition changes only the
interpretation used to prove the source program; the target consists of the fixed table. -/
noncomputable def guarded (I : Interp RCLikeBlas.Operation CmpTst ℝ)
    (M : Machine ℝ) (e : Blas1Err) (u : ℝ)
    (context : List (ℕ × ℕ)) (systemIndex preconditionerIndex : Fin context.length)
    (cutoff : ℕ) (reference : Store ℝ) (n : ℕ) (systemRaw preconditionerRaw : List ℝ) :
    Interp Signature CmpTst ℝ :=
  (I.linkContext (table context.length systemIndex preconditionerIndex) context).guardContext
    (fun o => (relation M e u n systemRaw preconditionerRaw o).spec (admissible n o))
    (Mem.ContextSnapshot cutoff reference) cutoff
    (fallback (n := n) I M systemRaw preconditionerRaw)

/-- The actual system product has its derived dense scalar allowance; the preconditioner
has the fixed actual scalar action. Both read the raw capabilities protected by the snapshot. -/
theorem guarded_meets {I : Interp RCLikeBlas.Operation CmpTst ℝ} {M : Machine ℝ}
    {u : ℝ} {e : Blas1Err} (hM : StdModel u id M) (hu : 0 ≤ u)
    (hS : IsScalar M I) (hB : IsBlas1 id e (fun _ => True) I)
    (context : List (ℕ × ℕ)) (systemIndex preconditionerIndex : Fin context.length)
    {n cutoff : ℕ} (reference : Store ℝ) (systemRaw preconditionerRaw : List ℝ)
    (hc : ∀ z ∈ context, z.1 < cutoff)
    (hA : reference.readBlock context[systemIndex].1 context[systemIndex].2 (n * n) =
      some systemRaw)
    (hP : reference.readBlock context[preconditionerIndex].1 context[preconditionerIndex].2
      (n * n) = some preconditionerRaw) :
    ∀ o, (guarded I M e u context systemIndex preconditionerIndex cutoff reference n
      systemRaw preconditionerRaw).Meets .total o
      ((relation M e u n systemRaw preconditionerRaw o).spec (admissible n o)) := by
  intro o
  apply Interp.meets_guardContext _ _ _ _ _ _ (fallback_meets hS hB hu _ _ o)
  intro d ins outs τ mem hs ho hp
  cases o with
  | scalar a =>
    rw [Interp.linkContext_callS_inr I (by rfl)]
    exact hS a d ins outs τ mem hp
  | blas b =>
    rw [Interp.linkContext_callS_inr I (by rfl)]
    cases b <;> first
      | exact hB.sum d ins outs τ mem hp
      | exact hB.dot d ins outs τ mem hp
      | exact hB.axpy d ins outs τ mem hp
      | exact hB.nrm2 d ins outs τ mem hp
      | exact hB.scal d ins outs τ mem hp
      | exact hB.copy d ins outs τ mem hp
  | operator =>
    have hi := hc context[systemIndex] (List.getElem_mem ..)
    have hd := (hs.2.readBlock hi context[systemIndex].2 (n * n)).trans hA
    exact ContextDenseRounded.callS_source hS context systemIndex rfl systemRaw
      (hM.norm_mulVec_sub_rowWord_le hu n n systemRaw) (hs.live hc) hi hd ho hp
  | preconditioner =>
    have hi := hc context[preconditionerIndex] (List.getElem_mem ..)
    have hd := (hs.2.readBlock hi context[preconditionerIndex].2 (n * n)).trans hP
    exact ContextDenseRounded.callS_source_fn hS context preconditionerIndex rfl
      preconditionerRaw (hs.live hc) hi hd ho hp

/-- The proof-side guard preserves the actual deterministic dot function, alongside its
numerical relation. Repeated dot calls on identical words therefore agree. -/
theorem guarded_dot {I : Interp RCLikeBlas.Operation CmpTst ℝ} {M : Machine ℝ}
    {e : Blas1Err} {u : ℝ}
    (hD : I.IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn M)
      (OutApart (fun _ => True)))
    (context : List (ℕ × ℕ)) (systemIndex preconditionerIndex : Fin context.length)
    (cutoff : ℕ) (reference : Store ℝ) (n : ℕ) (systemRaw preconditionerRaw : List ℝ) :
    (guarded I M e u context systemIndex preconditionerIndex cutoff reference n
      systemRaw preconditionerRaw).IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn M)
        (OutApart (fun _ => True)) := by
  classical
  intro d ins outs τ mem hp
  change Mode.total.Holds
    (((I.linkContext (table context.length systemIndex preconditionerIndex) context).guardContext
      (fun o => (relation M e u n systemRaw preconditionerRaw o).spec (admissible n o))
      (Mem.ContextSnapshot cutoff reference) cutoff
      (fallback (n := n) I M systemRaw preconditionerRaw)).callS (.blas .dot)
        d ins outs τ mem) _
  rw [Interp.callS_guardContext]
  by_cases hg : mem.ContextSnapshot cutoff reference ∧ ∀ z ∈ outs, cutoff ≤ z.1
  · rw [if_pos hg]
    have hpN : (((relation M e u n systemRaw preconditionerRaw (.blas .dot)).spec
        (admissible n (.blas .dot))).on .total d ins outs τ mem).pre mem := by
      refine ⟨hp.1, hp.2.1, ?_⟩
      intro h
      obtain ⟨hl, ⟨vals, hr, _⟩, hz⟩ := hp.2.2 h
      exact ⟨hl, ⟨vals, hr, trivial⟩, hz⟩
    rw [if_pos hpN, Interp.linkContext_callS_inr I (by rfl)]
    exact hD d ins outs τ mem hp
  · rw [if_neg hg]
    exact hD d ins outs τ mem hp

/-- Scalar, rounded BLAS, derived system, functional preconditioner and comparison laws
for the same protected two-operator implementation. No solver-success premise is required. -/
theorem guarded_laws {I : Interp RCLikeBlas.Operation CmpTst ℝ} {M : Machine ℝ}
    {u : ℝ} {e : Blas1Err} (hM : StdModel u id M) (hu : 0 ≤ u)
    (hS : IsScalar M I) (hB : IsBlas1 id e (fun _ => True) I)
    (hCmp : IsCmp id I)
    (context : List (ℕ × ℕ)) (systemIndex preconditionerIndex : Fin context.length)
    {n cutoff : ℕ} (reference : Store ℝ) (systemRaw preconditionerRaw : List ℝ)
    (hc : ∀ z ∈ context, z.1 < cutoff)
    (hA : reference.readBlock context[systemIndex].1 context[systemIndex].2 (n * n) =
      some systemRaw)
    (hP : reference.readBlock context[preconditionerIndex].1 context[preconditionerIndex].2
      (n * n) = some preconditionerRaw) :
    let J := guarded I M e u context systemIndex preconditionerIndex cutoff reference n
      systemRaw preconditionerRaw
    IsScalar M J ∧ IsBlas1 id e (fun _ => True) J ∧
      IsMatvec id (StoredOperator.denseMatrix n n systemRaw)
        (relativeError u n * specNorm (StoredOperator.denseMatrix n n systemRaw)) J ∧
      J.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
        (matvecFn (oracle hM hu n preconditionerRaw).mulVec) (MatvecOperands n n) ∧
      IsCmp id J := by
  have h := guarded_meets hM hu hS hB context systemIndex preconditionerIndex
    reference systemRaw preconditionerRaw hc hA hP
  exact ⟨fun o => h (.scalar o),
    ⟨h (.blas .sum), h (.blas .dot), h (.blas .axpy), h (.blas .nrm2),
      h (.blas .scal), h (.blas .copy)⟩, h .operator, h .preconditioner, hCmp⟩

/-- After the actual vector lowering, scalar standard-model laws alone give all rounded
PCG interfaces, including deterministic dot products and the actual stored preconditioner. -/
theorem scalar_guarded_laws {I : Interp ScalarOp CmpTst ℝ} {M : Machine ℝ}
    {u : ℝ} (hM : StdModel u id M) (hu : 0 ≤ u)
    (hS : IsScalar M I) (hCmp : IsCmp id I)
    (context : List (ℕ × ℕ)) (systemIndex preconditionerIndex : Fin context.length)
    {n cutoff : ℕ} (reference : Store ℝ) (systemRaw preconditionerRaw : List ℝ)
    (hc : ∀ z ∈ context, z.1 < cutoff)
    (hA : reference.readBlock context[systemIndex].1 context[systemIndex].2 (n * n) =
      some systemRaw)
    (hP : reference.readBlock context[preconditionerIndex].1 context[preconditionerIndex].2
      (n * n) = some preconditionerRaw) :
    let J := guarded (I.link RoundedScalarBlas.table) M (Blas.seq.err u) u context
      systemIndex preconditionerIndex cutoff reference n systemRaw preconditionerRaw
    IsScalar M J ∧ IsBlas1 id (Blas.seq.err u) (fun _ => True) J ∧
      IsMatvec id (StoredOperator.denseMatrix n n systemRaw)
        (relativeError u n * specNorm (StoredOperator.denseMatrix n n systemRaw)) J ∧
      J.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
        (matvecFn (oracle hM hu n preconditionerRaw).mulVec) (MatvecOperands n n) ∧
      IsCmp id J ∧
      J.IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn M) (OutApart (fun _ => True)) := by
  obtain ⟨hs, hb⟩ := RoundedScalarBlas.laws hM hu hS
  obtain ⟨hs', hb', ha', hp', hc'⟩ := guarded_laws hM hu hs hb hCmp context
    systemIndex preconditionerIndex reference systemRaw preconditionerRaw hc hA hP
  exact ⟨hs', hb', ha', hp', hc', guarded_dot (RoundedScalarBlas.isFn_dot hS)
    context systemIndex preconditionerIndex cutoff reference n systemRaw preconditionerRaw⟩

end NLAlib.Krylov.CG.HSPCG.Rounded.StoredContext
