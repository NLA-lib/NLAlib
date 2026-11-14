/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Confined
public import NLAlib.Ops.Examples.Certification
public import NLAlib.Ops.Examples.Resources

/-!
# Certificates that mislead, and the properties that reject them

Three complete `NLAlib.Ops.Algorithm` certificates from the 2026-11-14 audit. Each is a true
statement about its model whose headline reading is false, and each fails one of the properties
of `NLAlib.Ops.Confined`:

* `NLAlib.Ops.Examples.Oracles.oracleAlgorithm`: one unit-cost call writes a number that is in no
  buffer. Its model is not uniform: the contract of the primitive is chosen per input.
* `NLAlib.Ops.Examples.Oracles.sumAlgorithm`: one unit-cost call with no operand and no dimension
  sums a stored vector of any length. Its model is uniform and not confined.
* `NLAlib.Ops.Examples.Oracles.freeAlgorithm`: the repeated-addition program of
  `NLAlib.Ops.Examples.Certification` at total work zero. Its model is not charged.

The types `Problem`, `AccessModel` and `Specification` accept all three. A reader of a
certificate checks that its model is uniform or names its oracle, is confined and is charged;
`scripts/OpsPrograms.lean` reports the three properties for every certificate.

## Main results

* `NLAlib.Ops.Examples.Oracles.not_uniform_oracleModel`,
  `NLAlib.Ops.Examples.Oracles.not_confined_sumModel`,
  `NLAlib.Ops.Examples.Oracles.not_charged_freeModel`: the three rejections.
* `NLAlib.Ops.Examples.Oracles.confined_repeatModel`: the honest example model has all three
  properties.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.Oracles

open Certification

/-- One primitive without operands, unit work and span, no workspace. -/
def unitResources : ResourceModel Unit Empty where
  formats := [.cell]
  operation _ := ⟨[], []⟩
  testInputs q := nomatch q
  indexInputs q := nomatch q
  workspace _ _ := 0
  queryWorkspace q := nomatch q
  operationWork _ _ := 1
  operationSpan _ _ := 1
  queryWork q := nomatch q
  querySpan q := nomatch q
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le q := nomatch q
  core_span_le _ _ := le_rfl

/-- The budget of one call without operands: one primitive, work one, no scratch. -/
noncomputable def oneCall : Count (Unit ⊕ Bookkeeping) Empty := Count.one (.inl ()) []

/-- The program of both oracle examples: one call, without dimensions or operands. -/
def callProgram (b : ℕ) : Program Unit Empty 1 b := ⟨.call () [] [] []⟩

theorem staticCost_callProgram (b : ℕ) (d : Fin 1 → ℕ) :
    staticCost (callProgram b) d = oneCall := by
  simp [staticCost, callProgram, Stmt.instrument, tally, indexBookkeeping, operandBookkeeping,
    stmtCost, useCost, IExp.evalList, oneCall]

theorem staticPeak_callProgram (b : ℕ) (d : Fin 1 → ℕ) :
    staticPeak unitResources (callProgram b) d = 0 := by
  rw [staticPeak, unitResources.queryReserve_of_zero (fun q => nomatch q), Nat.add_zero]
  simp [callProgram, Stmt.instrument, tally, indexBookkeeping, operandBookkeeping, stmtPeak,
    unitResources, instrumentWorkspace, IExp.evalList]

theorem work_oneCall : unitResources.work oneCall = 1 := by
  simp [ResourceModel.work, oneCall, Count.one, Count.lift, unitResources]

theorem span_oneCall : unitResources.span oneCall = 1 := by
  simp [ResourceModel.span, oneCall, Count.one, Count.lift, unitResources]

/-! ### An answer oracle: the contract of a primitive depends on the input -/

/-- A real number as semantic data. The only buffer is one uninitialised output cell: the
number is stored nowhere. -/
def oracleProblem : Problem ℝ 1 1 where
  formats _ := .cell
  valid _ := True
  Data _ := ℝ
  admissible _ _ buffers := buffers = ![[none]]
  admitted := ⟨fun _ => 0, trivial⟩
  supply _ _ := ⟨0, ![[none]], rfl⟩

/-- The input holding the number `a`. -/
def oracleInput (d : Fin 1 → ℕ) (a : ℝ) : oracleProblem.Input d := ⟨⟨a, ![[none]]⟩, rfl⟩

theorem initial_oracleProblem (d : Fin 1 → ℕ) (x : oracleProblem.Input d) :
    oracleProblem.initial d x = ⟨[[none]], 0⟩ := by
  obtain ⟨⟨x, buffers⟩, h⟩ := x
  change buffers = ![[none]] at h
  subst buffers
  rfl

/-- The contract of the primitive at the input `a`: write `a` into the cell `(0, 0)`. -/
def oracleContract (a : ℝ) : Contract ℝ where
  spec _ _ ins outs _ := ⟨fun m => m.Live (ins ++ outs), fun m m' => m' = m.upd (0, 0) a⟩

/-- A jointly realized model whose one primitive is an oracle for the semantic data. -/
noncomputable def oracleModel : AccessModel Unit Empty oracleProblem where
  word := 0
  operation _ x _ := oracleContract x.val.1
  query _ _ q := nomatch q
  resources := unitResources
  realize _ _ x := by
    refine ⟨⟨fun _ _ _ _ _ m => some (m.upd (0, 0) x.val.1), (fun q => nomatch q),
      (fun q => nomatch q)⟩, ?_, fun q => nomatch q⟩
    intro _ d ins outs τ m hpre
    change m.Live (ins ++ outs) at hpre
    refine ⟨m.upd (0, 0) x.val.1, ?_, rfl⟩
    have hs : (m.upd (0, 0) (x.val.1 : ℝ)).store.shape = m.store.shape := Store.shape_upd ..
    rw [Interp.callS_of_live hpre]
    simp [hs]

/-- "The answer, with one operation, work one, no scratch, one cell of memory." -/
noncomputable def oracleSpecification : Specification Unit Empty oracleProblem where
  budget _ := oneCall
  scratch _ := 0
  work _ := 1
  span _ := 1
  memory _ := 1
  good _ x _ _ m' := m'.store.get 0 0 = some x.val.1

/-- **A misleading certificate.** A fixed program outputs a number that is in no buffer, with
one primitive call that reads nothing. -/
noncomputable def oracleAlgorithm : Algorithm oracleModel oracleSpecification :=
  Algorithm.ofWp (callProgram 1) (by decide)
    (fun d _ x I hI τ => by
      rw [initial_oracleProblem]
      refine wp_call (hI.1 ()) (d := []) (a := []) (b := []) rfl rfl rfl ?_ ?_
      · change Mem.Live _ ([] ++ [])
        simp
      · rintro m' hm' c -
        change m' = _ at hm'
        subst hm'
        exact Store.get_upd_self (by simp [Store.len]) _)
    (fun d _ => (staticCost_callProgram 1 d).le)
    (fun d _ => (staticPeak_callProgram 1 d).le)
    (fun _ _ => work_oneCall.le)
    (fun _ _ => span_oneCall.le)
    (fun d _ x => by
      obtain ⟨⟨x, buffers⟩, h⟩ := x
      change buffers = ![[none]] at h
      subst buffers
      simp [oracleSpecification, Problem.initialBytes, oracleProblem])

/-- The oracle model is not uniform: its contract differs at two inputs. -/
theorem not_uniform_oracleModel : ¬ oracleModel.Uniform := by
  intro h
  have e := h.operation (fun _ => 0) (oracleInput _ 0) (fun _ => 0) (oracleInput _ 1) ()
  have e' := congrArg (fun C : Contract ℝ =>
    (C.spec .total [] [] [] []).post ⟨[[none]], 0⟩ ⟨[[some 0]], 0⟩) e
  have h1 : (⟨[[some 0]], 0⟩ : Mem ℝ) = (⟨[[none]], 0⟩ : Mem ℝ).upd (0, 0) 1 := e'.mp rfl
  simp [Mem.upd, Store.upd] at h1

/-! ### Ambient authority: a primitive reads a buffer that is not an operand -/

/-- `n` reals in buffer `0` and one uninitialised output cell in buffer `1`. -/
def sumProblem : Problem ℝ 1 2 where
  formats _ := .cell
  valid _ := True
  Data d := Fin (d 0) → ℝ
  admissible _ x buffers := buffers = ![(List.ofFn x).map some, [none]]
  admitted := ⟨fun _ => 0, trivial⟩
  supply _ _ := ⟨0, ![(List.ofFn (0 : Fin _ → ℝ)).map some, [none]], rfl⟩

/-- The sum of the initialised cells of buffer `0`: a function of the memory alone. -/
noncomputable def total (m : Mem ℝ) : ℝ := (((m.store[0]?).getD []).filterMap id).sum

/-- An input-independent contract: write the sum of buffer `0` into the cell `(1, 0)`. -/
noncomputable def sumContract : Contract ℝ where
  spec _ _ ins outs _ := ⟨fun m => m.Live (ins ++ outs), fun m m' => m' = m.upd (1, 0) (total m)⟩

/-- A jointly realized, uniform model whose primitive is not confined to its operands. -/
noncomputable def sumModel : AccessModel Unit Empty sumProblem where
  word := 0
  operation _ _ _ := sumContract
  query _ _ q := nomatch q
  resources := unitResources
  realize _ _ _ := by
    refine ⟨⟨fun _ _ _ _ _ m => some (m.upd (1, 0) (total m)), (fun q => nomatch q),
      (fun q => nomatch q)⟩, ?_, fun q => nomatch q⟩
    intro _ d ins outs τ m hpre
    change m.Live (ins ++ outs) at hpre
    refine ⟨m.upd (1, 0) (total m), ?_, rfl⟩
    rw [Interp.callS_of_live hpre]
    simp [Mem.upd]

/-- "The sum of `n` reals, with one operation and work one." -/
noncomputable def sumSpecification : Specification Unit Empty sumProblem where
  budget _ := oneCall
  scratch _ := 0
  work _ := 1
  span _ := 1
  memory d := d 0 + 1
  good _ x _ _ m' := m'.store.get 1 0 = some (∑ i, x.val.1 i)

/-- **A misleading certificate.** A fixed program sums `n` stored reals, for every `n`, with one
call that names no operand and no dimension, at total work one. -/
noncomputable def sumAlgorithm : Algorithm sumModel sumSpecification :=
  Algorithm.ofWp (callProgram 2) (by decide)
    (fun d _ x I hI τ => by
      obtain ⟨⟨x, buffers⟩, h⟩ := x
      change buffers = ![(List.ofFn x).map some, [none]] at h
      subst buffers
      refine wp_call (hI.1 ()) (d := []) (a := []) (b := []) rfl rfl rfl ?_ ?_
      · change Mem.Live _ ([] ++ [])
        simp
      · rintro m' hm' c -
        change m' = _ at hm'
        subst hm'
        change (Store.upd _ 1 0 _).get 1 0 = _
        rw [Store.get_upd_self (by simp [Problem.initial, Store.len])]
        simp only [total, Problem.initial, id_eq, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
          List.ofFn_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
          List.ofFn_zero, List.length_cons, List.length_nil, zero_add, Order.lt_two_iff, zero_le,
          getElem?_pos, List.getElem_cons_zero, Option.getD_some, List.filterMap_map,
          Function.comp_apply, List.filterMap_some, Option.some.injEq]
        exact List.sum_ofFn (f := (x : Fin (d 0) → ℝ)))
    (fun d _ => (staticCost_callProgram 2 d).le)
    (fun d _ => (staticPeak_callProgram 2 d).le)
    (fun _ _ => work_oneCall.le)
    (fun _ _ => span_oneCall.le)
    (fun d _ x => by
      obtain ⟨⟨x, buffers⟩, h⟩ := x
      change buffers = ![(List.ofFn x).map some, [none]] at h
      subst buffers
      simp only [sumSpecification, Problem.initialBytes, sumProblem, Nat.succ_eq_add_one,
        Nat.reduceAdd, Fin.isValue]
      simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_fin_one, StorageFormat.bytes_cell, one_mul, List.length_map,
        List.length_cons, List.length_nil, List.sum_cons, List.sum_nil, Fin.isValue]
      have hlen := List.length_ofFn (f := (x : Fin (d 0) → ℝ))
      omega)

/-- The contracts of `sumModel` do not depend on the input. -/
instance uniform_sumModel : sumModel.Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ q => nomatch q⟩

/-- The summing model is not confined: a call without output operands changes buffer `1`,
which a confined call cannot do (`NLAlib.Ops.Contract.Confined.frame`). -/
theorem not_confined_sumModel : ¬ sumModel.Confined := by
  intro h
  obtain ⟨x⟩ := sumProblem.inputs_exist (fun _ => 0) trivial
  have hC : sumContract.Confined := h.operation (fun _ => 0) x ()
  have hf := hC.frame (md := .total) (d := []) (ins := []) (outs := []) (w := [])
    (m := ⟨[[some 1], [none]], 0⟩) (m' := (⟨[[some 1], [none]], 0⟩ : Mem ℝ).upd (1, 0) 1)
    (by simp [sumContract, total]) (b := 1) (by simp)
  simp [Mem.upd, Store.upd] at hf

/-! ### Free work: every weight of the resource model is zero -/

/-- The resources of the repeated-addition example with every work and span weight zero. -/
def freeResources : ResourceModel ScalarOp Empty :=
  { repeatResources with
    operationWork := fun _ _ => 0
    operationSpan := fun _ _ => 0
    coreWork := fun _ _ => 0
    coreSpan := fun _ _ => 0
    operation_span_le := fun _ _ => le_rfl
    core_span_le := fun _ _ => le_rfl }

/-- The exact scalar model of the repeated-addition example, with the free resources. -/
noncomputable def freeModel : AccessModel ScalarOp Empty repeatProblem :=
  { repeatModel with resources := freeResources }

theorem work_freeResources (c : Count (ScalarOp ⊕ Bookkeeping) Empty) :
    freeResources.work c = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => exact map_zero _
  | add a b ha hb => rw [map_add, ha, hb]
  | single k n =>
    rw [ResourceModel.work, Count.lift_single]
    obtain ⟨(_ | _) | q, d⟩ := k
    · rfl
    · rfl
    · exact q.elim

/-- The budget is the static count of the program itself; work and span are zero. -/
noncomputable def freeSpecification : Specification ScalarOp Empty repeatProblem :=
  { repeatSpecification with
    budget := fun d => staticCost repeatProgram d
    work := fun _ => 0
    span := fun _ => 0 }

/-- **A misleading certificate.** The `n`-fold addition program, certified at total work zero
and span zero for every `n`, under a budget that is the program's own static count. -/
noncomputable def freeAlgorithm : Algorithm freeModel freeSpecification :=
  Algorithm.ofWp repeatProgram (by decide)
    (fun d _ x I hI τ => (wp_repeat hI.1 d x τ).mono fun _ hg _ _ => hg)
    (fun _ _ => le_rfl)
    (fun d _ => by
      rw [staticPeak]
      change _ + freeResources.queryReserve _ ≤ _
      rw [freeResources.queryReserve_of_zero (fun q => nomatch q), Nat.add_zero]
      simp [repeatProgram, Stmt.instrument, tally, indexBookkeeping, operandBookkeeping,
        IExp.bookkeeping, stmtPeak, Program.environment, freeModel, freeResources,
        repeatResources, instrumentWorkspace, freeSpecification, repeatSpecification])
    (fun _ _ => (work_freeResources _).le)
    (fun _ _ => Nat.le_of_eq (Nat.eq_zero_of_le_zero
      ((freeResources.span_le_work _).trans (work_freeResources _).le)))
    (fun d _ x => by simp [freeSpecification, repeatSpecification, initialBytes_repeatProblem])

/-- The free model is not charged. -/
theorem not_charged_freeModel : ¬ freeModel.Charged :=
  fun h => lt_irrefl 0 (h.core .skip [])

/-- The free model keeps the contracts of the honest model: it is confined. -/
instance confined_freeModel : freeModel.Confined :=
  ⟨fun _ _ _ => BlockRel.confined_spec _ _, fun _ _ q => nomatch q⟩

/-- It is uniform. -/
instance uniform_freeModel : freeModel.Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ q => nomatch q⟩

/-! ### The honest example models have the properties -/

/-- A model without primitives or queries is confined. -/
instance confined_mixedModel : Resources.mixedModel.Confined :=
  ⟨(fun _ _ o => nomatch o), fun _ _ q => nomatch q⟩

/-- A model without primitives or queries is uniform. -/
instance uniform_mixedModel : Resources.mixedModel.Uniform :=
  ⟨(fun _ _ _ _ o => nomatch o), fun _ _ _ _ q => nomatch q⟩


/-- The exact scalar model of the repeated-addition example is confined. -/
instance confined_repeatModel : repeatModel.Confined :=
  ⟨fun _ _ _ => BlockRel.confined_spec _ _, fun _ _ q => nomatch q⟩

/-- It is uniform. -/
instance uniform_repeatModel : repeatModel.Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ q => nomatch q⟩

/-- It is charged: every scalar call and structural instruction costs one unit. -/
instance charged_repeatModel : repeatModel.Charged :=
  ⟨fun _ _ => Nat.one_pos, (fun q => nomatch q), fun _ _ => Nat.one_pos⟩

end NLAlib.Ops.Examples.Oracles
