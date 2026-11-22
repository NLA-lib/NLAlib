/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.Integrator
public import NLAlib.Ops.Blas.Level1

/-!
# Example: the integrator, one level down

The update of `NLAlib.Ops.Examples.Integrator` is implemented by scalar arithmetic in floating
point, and the certificate of the integrator is carried down by linking. The product with the
matrix stays an operation.

## Main definitions

* `NLAlib.Ops.Examples.Integrator.MyLowOperation`: scalar arithmetic and the product.
* `NLAlib.Ops.Examples.Integrator.myAxpy`: the update as a loop of scalar operations.
* `NLAlib.Ops.Examples.Integrator.myTable`: the update by `myAxpy`, the product by itself.
* `NLAlib.Ops.Examples.Integrator.myLowModel`: the standard model of floating point arithmetic,
  and the product.

## Main results

* `NLAlib.Ops.Examples.Integrator.myAxpy_meets`: the loop has the error $(1 + u)^2 - 1$.
* `NLAlib.Ops.Examples.Integrator.myAxpy_implements`: its interface is that of the update.
* `NLAlib.Ops.Examples.Integrator.myLinkedAlgorithm`: the certificate of the linked program.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.Integrator

open NLAlib.Ops
open scoped Matrix Matrix.Norms.L2Operator

/-- The operations one level down: scalar arithmetic, and the product with the matrix. -/
inductive MyLowOperation where
  /-- A scalar operation. -/
  | scalar (o : ScalarOp)
  /-- `matvec [n, n] (x) → (y)`. -/
  | matvec

/-- The scalar operations are one family of the closed type of the lower model; a routine
written over any type with scalar operations (`axpyLoopRoutine`) runs in it through this
embedding and its projection. -/
instance : Has ScalarOp MyLowOperation where
  inj := .scalar
  proj
    | .scalar o => some o
    | .matvec => none
  proj_inj _ := rfl
  inj_of_proj o g h := by
    cases o with
    | scalar o => cases h; rfl
    | matvec => cases h

/-- The update `y ← y ⊕ (α ⊗ x)`, entry by entry, with one scratch cell: the library's loop
`NLAlib.Ops.axpyLoopRoutine`. -/
def myAxpy : Routine MyLowOperation Empty := axpyLoopRoutine

/-- In the standard model of floating point arithmetic with unit roundoff $u \ge 0$, the loop
meets the specification read off the contract of the update, with $e = (1 + u)^2 - 1$. -/
theorem myAxpy_meets {M : Machine ℝ} {I : Interp MyLowOperation Empty ℝ} (hI : IsScalar M I)
    {u : ℝ} (hM : StdModel u id M) (hu : 0 ≤ u) :
    myAxpy.Meets I (.ofRel (myAxpyRel ((1 + u) ^ 2 - 1)) fun _ => True) := by
  rw [myAxpyRel_eq]
  exact axpyLoopRoutine_meets hI hM hu fun _ => True

/-- The interface of the loop is that of the update: three blocks read, the last one updated in
place, the other two in other buffers. -/
theorem myAxpy_implements (e : ℝ) :
    myAxpy.Implements (myAxpyRel e) (InPlace fun _ => True) (fun ins _ => ins) := by
  rw [myAxpyRel_eq]
  exact axpyLoopRoutine_implements id e fun _ => True

/-- What replaces each operation: the update by `myAxpy`, the product by itself. -/
def myTable : Table MyOperation MyLowOperation Empty
  | .axpy => .inl myAxpy.impl
  | .matvec => .inr .matvec

/-! ### The lower model -/

/-- The storage of the operands of each lower operation. -/
def myLowSignature : MyLowOperation → OperandSignature
  | .scalar (.lit _) => ⟨[], [.cell]⟩
  | .scalar .add | .scalar .sub | .scalar .mul | .scalar .div => ⟨[.cell, .cell], [.cell]⟩
  | .scalar .neg | .scalar .sqrt | .scalar .copy => ⟨[.cell], [.cell]⟩
  | .matvec => ⟨[.cell], [.cell]⟩

/-- The weight of a lower call: one for a scalar operation, $2 n^2$ for a product. -/
def myLowWork : MyLowOperation → List ℕ → ℕ
  | .scalar _, _ => 1
  | .matvec, d => 2 * d.headD 0 ^ 2

/-- Calls weighed by `myLowWork`, structural instructions by one, no workspace. -/
def myLowResources : ResourceModel MyLowOperation Empty where
  formats := [.cell]
  operation := myLowSignature
  testInputs q := nomatch q
  indexInputs q := nomatch q
  workspace _ _ := 0
  queryWorkspace q := nomatch q
  operationWork := myLowWork
  operationSpan := myLowWork
  queryWork q := nomatch q
  querySpan q := nomatch q
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le q := nomatch q
  core_span_le _ _ := le_rfl

/-- The scalar operations of a machine, and the exact product. -/
noncomputable def myLowFns (M : Machine ℝ) (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) :
    MyLowOperation → BlockFn ℝ
  | .scalar o => M.fn o
  | .matvec => myExactMatvec A

/-- The lower model: scalar operations are those of the machine `M`, the product satisfies
the contract of `matvec`, and the machine with the exact product is the witness. -/
noncomputable def myLowModel (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (M : Machine ℝ) : AccessModel MyLowOperation Empty myProblem where
  word := 0
  operation _ _
    | .scalar o => (M.fn o).rel.spec AnyOperands
    | .matvec => (myMatvecRel A δ).spec (OutApart fun _ => True)
  query _ _ q := nomatch q
  resources := myLowResources
  realize _ _ _ := ⟨Interp.ofFns (myLowFns M A), fun o => by
    cases o with
    | scalar o => exact Interp.ofFns_isFn (myLowFns M A) .total (.scalar o) AnyOperands
    | matvec => exact myExactMatvec_satisfies A hδ (myLowFns M A) .matvec rfl,
    fun q => nomatch q⟩

/-- Every contract of the lower model is in operand form: the model is confined. -/
instance confined_myLowModel (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (M : Machine ℝ) : (myLowModel A δ hδ M).Confined :=
  ⟨fun _ _ o => by cases o <;> exact BlockRel.confined_spec _ _, fun _ _ q => nomatch q⟩

/-- The contracts depend on the parameters of the model, not on the size or the input: the
lower model is uniform. -/
instance uniform_myLowModel (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (M : Machine ℝ) : (myLowModel A δ hδ M).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ q => nomatch q⟩

/-- The lower model is not charged: a product with a matrix of order $0$ weighs nothing. -/
theorem not_charged_myLowModel (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (M : Machine ℝ) : ¬ (myLowModel A δ hδ M).Charged :=
  fun h => lt_irrefl 0 (h.operation .matvec [])

/-! ### The linked certificate -/

/-- The linked program: the integrator with each update replaced by `myAxpy`. -/
def myLinkedProgram : Program MyLowOperation Empty 2 2 := myProgram.link myTable

/-- The calls of the linked tree: $N$ products at $[n, n]$, and $N n$ scalar
multiplications and $N n$ scalar additions, and no other operation. -/
theorem myLinkedProgram_calls (d : Fin 2 → ℕ) :
    Count.original (staticCost myLinkedProgram d) =
      d 1 • (Count.one MyLowOperation.matvec [d 0, d 0] +
        d 0 • (Count.one (MyLowOperation.scalar .mul) [] +
          Count.one (MyLowOperation.scalar .add) [])) := by
  rw [staticCost, original_stmtCost_instrument]
  simp [myLinkedProgram, Program.link, Stmt.link, myTable, myAxpy, axpyLoopRoutine, axpyLoop,
    Routine.impl, Routine.nin, Routine.nout, Impl.Fits, Access.readable, Access.writable,
    Port.read, Port.update, myProgram, Routine.close,
    Routine.bindsFit, Routine.flat, Port.flat, myIntegrate, myStep, Program.environment,
    List.ofFn_succ, Routine.closeDims, Routine.closeOps, List.range_succ, stmtCost, useCost,
    IExp.evalList, IExp.eval, Finset.sum_const, Has.inj]

/-- The scratch of the linked tree: at most the $n$ cells of `Y` and the one cell that
`myAxpy` allocates. -/
theorem myLinkedProgram_peak (d : Fin 2 → ℕ) :
    staticPeak myLowResources myLinkedProgram d ≤ d 0 + 1 := by
  rw [staticPeak, myLowResources.queryReserve_of_zero (fun q => nomatch q), Nat.add_zero]
  simp [myLinkedProgram, Program.link, Stmt.link, myTable, myAxpy, axpyLoopRoutine, axpyLoop,
    Routine.impl, Routine.nin, Routine.nout, Impl.Fits, Access.readable, Access.writable,
    Port.read, Port.update, myProgram, Routine.close,
    Routine.bindsFit, Routine.flat, Port.flat, myIntegrate, myStep, Program.environment,
    List.ofFn_succ, Routine.closeDims, Routine.closeOps, List.range_succ, stmtPeak_tally,
    Stmt.instrument, indexBookkeeping, operandBookkeeping, stmtPeak, myLowResources,
    instrumentWorkspace, IExp.evalList, IExp.eval, Has.inj]

/-- The work of the linked tree: $N$ products weighing $2 n^2$; in each round, $22$
instructions for each entry of the update (two scalar operations and twenty structural
instructions) and $34$ more; and $11$ outside the loop. -/
def myLinkedWork (d : Fin 2 → ℕ) : ℕ :=
  2 * d 1 * d 0 ^ 2 + 22 * d 1 * d 0 + 34 * d 1 + 11

/-- The weighted count of the linked tree is `myLinkedWork`. -/
theorem work_myLinkedProgram (d : Fin 2 → ℕ) :
    myLowResources.work (staticCost myLinkedProgram d) = myLinkedWork d := by
  rw [staticCost]
  simp [myLinkedProgram, Program.link, Stmt.link, myTable, myAxpy, axpyLoopRoutine, axpyLoop,
    Routine.impl, Routine.nin, Routine.nout, Impl.Fits, Access.readable, Access.writable,
    Port.read, Port.update, myProgram, Routine.close,
    Routine.bindsFit, Routine.flat, Port.flat, myIntegrate, myStep, Program.environment,
    List.ofFn_succ, Routine.closeDims, Routine.closeOps, List.range_succ, stmtCost, useCost,
    IExp.evalList, IExp.eval, Has.inj, Stmt.instrument, indexBookkeeping, operandBookkeeping,
    ResourceModel.work, myLowResources, myLowWork, lift_stmtCost_tally, IExp.bookkeeping,
    myLinkedWork]
  ring

/-- Calls run one after another, so the span of the linked tree is its work. -/
theorem span_myLinkedProgram (d : Fin 2 → ℕ) :
    myLowResources.span (staticCost myLinkedProgram d) = myLinkedWork d := by
  rw [staticCost]
  simp [myLinkedProgram, Program.link, Stmt.link, myTable, myAxpy, axpyLoopRoutine, axpyLoop,
    Routine.impl, Routine.nin, Routine.nout, Impl.Fits, Access.readable, Access.writable,
    Port.read, Port.update, myProgram, Routine.close,
    Routine.bindsFit, Routine.flat, Port.flat, myIntegrate, myStep, Program.environment,
    List.ofFn_succ, Routine.closeDims, Routine.closeOps, List.range_succ, stmtCost, useCost,
    IExp.evalList, IExp.eval, Has.inj, Stmt.instrument, indexBookkeeping, operandBookkeeping,
    ResourceModel.span, myLowResources, myLowWork, lift_stmtCost_tally, IExp.bookkeeping,
    myLinkedWork]
  ring


/-- The claims about the linked program: the accuracy of `mySpec` at $e = (1 + u)^2 - 1$; the
count of the linked tree as the budget, and in closed form its work and span (`myLinkedWork`), its
scratch ($n + 1$ cells) and its memory. -/
noncomputable def myLowSpec (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ u : ℝ) :
    Specification MyLowOperation Empty myProblem where
  good d x _ _ μ := myGood A δ ((1 + u) ^ 2 - 1) d x μ
  budget := staticCost myLinkedProgram
  work := myLinkedWork
  span := myLinkedWork
  scratch d := d 0 + 1
  memory d := 2 + 2 * d 0

/-- The allowance of the update is nonnegative. -/
theorem axpyErr_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ (1 + u) ^ 2 - 1 := by nlinarith

/-- The certificate after linking: in the standard model of floating point arithmetic with
unit roundoff $u \ge 0$, the linked program meets the accuracy bound of the integrator with
$e = (1 + u)^2 - 1$, within the count and the scratch of the linked tree. Its one real
obligation is that the linked update satisfies the contract of `axpy`, which is
`myAxpy_meets` with `myAxpy_implements`; the analysis of the iteration is not repeated. -/
noncomputable def myLinkedAlgorithm (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (M : Machine ℝ) (u : ℝ) (hM : StdModel u id M) (hu : 0 ≤ u) :
    Algorithm (myLowModel A δ hδ M) (myLowSpec A δ u) :=
  (myAlgorithm A δ ((1 + u) ^ 2 - 1) hδ (axpyErr_nonneg hu)).link myTable
    (myLowModel A δ hδ M) (myLowSpec A δ u) (by rfl)
    (fun _ _ _ I hI => ⟨fun o => by
      cases o with
      | matvec => exact Interp.link_satisfies_kept rfl (hI.1 .matvec)
      | axpy =>
        exact Interp.link_satisfies rfl
          ((myAxpy_meets (fun o => hI.1 (.scalar o)) hM hu).satisfies_ofRel
            (myAxpy_implements _) fun _ _ _ _ => trivial),
      fun q => nomatch q⟩)
    (fun _ _ _ _ _ _ _ hg _ _ => hg)
    (fun _ _ => le_rfl) (fun d _ => myLinkedProgram_peak d)
    (fun d _ => (work_myLinkedProgram d).le) (fun d _ => (span_myLinkedProgram d).le)
    (fun d _ x => by
      rw [initialBytes_myProblem]
      change 1 + d 0 + (d 0 + 1) ≤ 2 + 2 * d 0
      omega)


end NLAlib.Ops.Examples.Integrator
