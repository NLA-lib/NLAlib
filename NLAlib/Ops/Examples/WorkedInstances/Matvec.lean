/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.WorkedInstances.Basic
public import NLAlib.Ops.Profiles.StoredDense
public import NLAlib.Ops.Profiles.RoundedScalarBlas
public import NLAlib.Ops.RoutineProblem

/-!
# Worked instance: a dense matrix-vector product

The scalar routine of the dense stored operator (`NLAlib.Ops.StoredDense.implRoutine`), which
streams each row of a matrix stored column by column through a loop of products, run with
exact real arithmetic on
$$A = \begin{pmatrix} 1 & 2 & 3 \\ 4 & 5 & 6 \end{pmatrix}, \qquad x = (1, 1, 2).$$
It exercises the indexing of a matrix in a flat buffer (entry $(i, j)$ at cell $j m + i$), a
routine run inside a loop, and an allocation.

Expected, from `scripts/worked_instances.py` (`Matvec`): the stored words
`[1, 4, 2, 5, 3, 6]`, the output `[9, 21]`, `2` literal zeros, `6` multiplications and `6`
additions, and one scratch cell. The total of `260` instructions and the formula
$33 m n + 23 m + 16$ are regression values.

## Main definitions

* `NLAlib.Ops.Examples.WorkedInstances.Matvec.domain`: a matrix and a vector, each in its
  buffer, and a blank buffer for the product.

## Main results

* `NLAlib.Ops.Examples.WorkedInstances.Matvec.run`: at every size, the product is written.
* `NLAlib.Ops.Examples.WorkedInstances.Matvec.calls`,
  `NLAlib.Ops.Examples.WorkedInstances.Matvec.work`,
  `NLAlib.Ops.Examples.WorkedInstances.Matvec.peak`: the calls, the instructions and the scratch
  of the tree at every size.
* `NLAlib.Ops.Examples.WorkedInstances.Matvec.memory_instance`,
  `NLAlib.Ops.Examples.WorkedInstances.Matvec.instance_run`: the initial memory and the run on
  the instance.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.WorkedInstances.Matvec

open Matrix

/-- The dense product over the scalar operations. -/
abbrev routine : Routine ScalarOp CmpTst := StoredDense.implRoutine

/-- The admitted inputs: every real matrix with `d 0` rows and `d 1` columns, stored column by
column, and every vector of length `d 1`; the third buffer is `d 0` blank cells. -/
def domain : routine.Domain ℝ 2 3 where
  valid _ := True
  In d := Matrix (Fin (d 0)) (Fin (d 1)) ℝ × (Fin (d 1) → ℝ)
  accepts _ _ := True
  slot d := ![.stored (Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 1)) Prod.fst,
    .stored (Codec.vector (d 1)) Prod.snd, .blank (d 0)]
  fits := by
    domain_fits
    exact Nat.mul_comm _ _
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq] at h0 h1
    exact Prod.ext ((Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 1)).encode_injective h0)
      ((Codec.vector (d 1)).encode_injective h1)
  admitted := ⟨fun _ => 0, trivial⟩
  inhabited _ _ := ⟨(0, fun _ => 0), trivial⟩

/-- A matrix, a vector and blank cells for the product: the problem of the dense product. -/
abbrev problem : Problem ℝ 2 3 := domain.problem

/-- The scalar-only model with unit weights and exact real arithmetic. -/
noncomputable abbrev model : AccessModel ScalarOp CmpTst problem :=
  RoundedScalarBlas.model problem RCLikeBlas.machine

/-- The fixed program: the routine on the three supplied buffers. -/
def program : Program ScalarOp CmpTst 2 3 := routine.close 2 3

/-- The tree of the dense product has no test. -/
theorem program_straight : program.body.Straight :=
  Stmt.straight_of_isStraight rfl

/-- The specification of the product: the relation of the dense stored operator. -/
abbrev spec : Routine.Spec ℝ :=
  Routine.Spec.ofRel (StoredOperator.denseFunctions (K := ℝ) .matvec).rel fun _ => True

/-- At every size, for every matrix and vector and every interpretation of the exact scalar
model, the execution rules derive an outcome of the program from the supplied buffers, and
the third buffer then holds the product $A x$. The outcome comes from the judgment of the
routine (`NLAlib.Ops.StoredDense.implRoutine_meets`) through the counted certificate of the
routine on its problem. -/
theorem run (d : Fin 2 → ℕ) (A : Matrix (Fin (d 0)) (Fin (d 1)) ℝ) (x : Fin (d 1) → ℝ)
    (I : Interp ScalarOp CmpTst ℝ)
    (hI : model.contracts d (domain.input d (A, x) trivial) I) (τ : Tape ℝ) :
    ∃ st, Reference.Execution program I model.resources domain.formats τ d
        (domain.memory d (A, x)) st ∧
      st.mem.store.readBlock 2 0 (d 0) = some (List.ofFn (A *ᵥ x)) := by
  obtain ⟨st, hr, -, -, ys, hys, hpost⟩ :=
    domain.checked_post (Sp := fun _ _ => spec)
      (work := fun d => CountPoly.eval (List.ofFn d) program.countPoly)
      (domain.certify (M := model) (fun _ _ => spec)
        (fun d => CountPoly.eval (List.ofFn d) program.countPoly)
        (fun _ _ _ _ hI => StoredDense.implRoutine_meets (RoundedScalarBlas.model_laws hI).1)
        (fun d _ x _ τ => ⟨trivial, _, rfl,
          by simp [StoredOperator.denseFunctions, StoredOperator.functions]⟩)
        (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl))
      d trivial (A, x) trivial I hI τ
  refine ⟨st, hr, ?_⟩
  read_outputs hys as (zs)
  have h : some [List.ofFn fun i : Fin (d 0) => ∑ j : Fin (d 1),
      StoredOperator.denseMatrix (d 0) (d 1) ((EntryCodec.scalar ℝ).packFinMatrix A) i j *
        (List.ofFn x).getD j 0] = some [zs] := hpost
  obtain rfl : _ = zs := by simpa using h
  rw [hzs, StoredOperator.denseMatrix_packFinMatrix]
  rfl

/-- The tree contains, for each row, one literal zero and one multiplication and one addition
for each column, and no other operation. -/
theorem calls (d : Fin 2 → ℕ) :
    Count.original (staticCost program d) =
      d 0 • (Count.one (ScalarOp.lit 0) [] +
        d 1 • (Count.one ScalarOp.mul [] + Count.one ScalarOp.add [])) := by
  rw [staticCost, original_stmtCost_instrument]
  exact StoredDense.stmtCost_impl (d 0) (d 1) 0 0 0

/-- The tree contains exactly $33 m n + 23 m + 16$ instructions, each of weight one. -/
theorem work (d : Fin 2 → ℕ) :
    model.resources.work (staticCost program d) = 33 * d 0 * d 1 + 23 * d 0 + 16 := by
  rw [staticCost]
  simp [program, routine, StoredDense.implRoutine, StoredOperator.matvecRoutine,
    StoredDense.impl, StoredDense.apply, ScalarProducts.sum, ScalarProducts.step,
    Routine.close, Routine.bindsFit, Routine.flat, Port.flat,
    Program.environment, List.ofFn_succ, List.range_succ, stmtCost, useCost, IExp.evalList,
    IExp.eval, Stmt.instrument, indexBookkeeping, operandBookkeeping, IExp.bookkeeping,
    ResourceModel.work, RoundedScalarBlas.model, Functional.model, Functional.modelWithAdm,
    RoundedScalarBlas.resources, Functional.cellResources, lift_one_stmtCost_tally,
    lift_one_one, Finset.sum_const]
  ring

/-- The scratch of the tree is its one accumulator cell. -/
theorem peak (d : Fin 2 → ℕ) : staticPeak model.resources program d = 1 := by
  rw [staticPeak_eq, ResourceModel.queryReserve_of_zero _ (fun _ _ => rfl), Nat.add_zero]
  exact StoredDense.stmtPeak_impl_zero (d 0) (d 1) [0, 0, 0]

/-- The matrix of the instance. -/
abbrev amat : Matrix (Fin 2) (Fin 3) ℝ := !![1, 2, 3; 4, 5, 6]

/-- The vector of the instance. -/
abbrev xvec : Fin 3 → ℝ := ![1, 1, 2]

/-- The matrix of the instance is stored column by column. -/
theorem encode_amat :
    (Codec.matrix (EntryCodec.scalar ℝ) 2 3).encode amat = [1, 4, 2, 5, 3, 6] := by
  simp [Codec.matrix, EntryCodec.packFinMatrix, List.ofFn_succ, finProdFinEquiv, Fin.divNat,
    Fin.modNat, EntryCodec.scalar]

/-- The initial memory of the instance: the words of the matrix, column by column, the vector,
and two uninitialized cells. -/
theorem memory_instance : domain.memory ![2, 3] (amat, xvec) =
    ⟨[[some 1, some 4, some 2, some 5, some 3, some 6], [some 1, some 1, some 2],
      [none, none]], 0⟩ := by
  have hA : (domain.slot ![2, 3] 0).buffer (amat, xvec) =
      [some 1, some 4, some 2, some 5, some 3, some 6] := by
    change ((Codec.matrix (EntryCodec.scalar ℝ) 2 3).encode amat).map some = _
    rw [encode_amat]
    rfl
  have hx : (domain.slot ![2, 3] 1).buffer (amat, xvec) = [some 1, some 1, some 2] := by
    change ((Codec.vector 3).encode xvec).map some = _
    simp [Codec.vector, List.ofFn_succ]
  have hy : (domain.slot ![2, 3] 2).buffer (amat, xvec) = [none, none] := rfl
  simpa [Inputs.memory, Inputs.buffers, List.ofFn_succ] using ⟨hA, hx, hy⟩

/-- The instance. With exact real arithmetic, from the memory of
`NLAlib.Ops.Examples.WorkedInstances.Matvec.memory_instance`, the execution rules derive one
outcome of the dense product: the third buffer holds `[9, 21]`; the run makes `2` literal
zeros, `6` multiplications and `6` additions, and no other operation, `260` instructions in
all; its peak scratch is one cell. -/
theorem instance_run (I : Interp ScalarOp CmpTst ℝ)
    (hI : model.contracts ![2, 3] (domain.input ![2, 3] (amat, xvec) trivial) I) (τ : Tape ℝ) :
    ∃ st, Reference.Execution program I model.resources domain.formats τ ![2, 3]
        (domain.memory ![2, 3] (amat, xvec)) st ∧
      st.mem.store.readBlock 2 0 2 = some [9, 21] ∧
      Count.original st.cost = 2 • (Count.one (ScalarOp.lit 0) [] +
        3 • (Count.one ScalarOp.mul [] + Count.one ScalarOp.add [])) ∧
      model.resources.work st.cost = 260 ∧ st.peak = 1 := by
  obtain ⟨st, hr, hout⟩ := run ![2, 3] amat xvec I hI τ
  obtain ⟨hc, hp⟩ := hr.eq_static_of_straight program_straight
  refine ⟨st, hr, ?_, ?_, ?_, ?_⟩
  · have h : st.mem.store.readBlock 2 0 2 = some (List.ofFn (amat *ᵥ xvec)) := hout
    rw [h]
    simp [List.ofFn_succ]
    norm_num
  · rw [hc, calls]
    rfl
  · rw [hc, work]
    rfl
  · rw [hp, peak]

end NLAlib.Ops.Examples.WorkedInstances.Matvec
