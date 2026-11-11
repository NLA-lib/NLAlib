/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Law
public import NLAlib.Ops.Catalog.Scalar

/-!
# A uniform certificate and structural adversarial regressions

The fixed program `NLAlib.Ops.Examples.Certification.repeatProgram` adds a supplied real number
to zero `n` times. Its certificate covers every natural size and every real input. Its count
includes the literal and additions, index evaluation, operand addressing, sequence, loop entry
and every executed round. The proof uses the ordinary total program logic.

The final examples are kernel-checked rejection claims: an impossible decoding cannot supply a
model realization, an impossible postcondition has no algorithm certificate, an abort is not a
certified program, a tree-building function is not one fixed program, and bookkeeping cannot be
omitted from the budget. They invoke no linter.

## Main results

* `NLAlib.Ops.Examples.Certification.repeatAlgorithm`: a certificate for all sizes and inputs.
* `NLAlib.Ops.Examples.Certification.repeatAlgorithmLinked`: fixed-table linking retains it.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.Certification

/-- One real input and an uninitialized output cell, at every natural size. -/
def repeatProblem : Problem ℝ 1 2 where
  formats _ := .cell
  valid _ := True
  Data _ := ℝ
  admissible _ x buffers := buffers = ![[some x], [none]]
  admitted := ⟨fun _ => 0, trivial⟩
  supply _ _ := ⟨0, ![[some 0], [none]], rfl⟩

/-- The explicitly supplied input buffers for a real input. -/
def repeatInput (d : Fin 1 → ℕ) (x : ℝ) : repeatProblem.Input d :=
  ⟨⟨x, ![[some x], [none]]⟩, rfl⟩

/-- Admissibility states exactly which raw buffers have been supplied. -/
theorem initial_repeatProblem (d : Fin 1 → ℕ) (x : repeatProblem.Input d) :
    repeatProblem.initial d x = ⟨[[some x.val.1], [none]], 0⟩ := by
  obtain ⟨⟨x, buffers⟩, h⟩ := x
  change buffers = ![[some x], [none]] at h
  subst buffers
  rfl

/-- A sequential unit-work configuration for the abstract one-byte scalar example. -/
def repeatResources : ResourceModel ScalarOp Empty where
  formats := [.cell]
  operation
    | .lit _ => ⟨[], [.cell]⟩
    | .add | .sub | .mul | .div => ⟨[.cell, .cell], [.cell]⟩
    | .neg | .sqrt | .copy => ⟨[.cell], [.cell]⟩
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

/-- No queries occur in the empty query signature. -/
@[simp] theorem queryReserve_repeatResources (c : Count (ScalarOp ⊕ Bookkeeping) Empty) :
    repeatResources.queryReserve c = 0 :=
  repeatResources.queryReserve_of_zero (fun q => nomatch q) c

/-- The supplied input and output slots occupy two abstract payload bytes. -/
theorem initialBytes_repeatProblem (d : Fin 1 → ℕ) (x : repeatProblem.Input d) :
    repeatProblem.initialBytes d x = 2 := by
  obtain ⟨⟨x, buffers⟩, h⟩ := x
  change buffers = ![[some x], [none]] at h
  subst buffers
  rfl

/-- The exact scalar model, with a realization of both contracts at every problem instance. -/
noncomputable def repeatModel : AccessModel ScalarOp Empty repeatProblem where
  word := 0
  operation _ _ o := (exactMachine.fn o).rel.spec AnyOperands
  query _ _ q := nomatch q
  resources := repeatResources
  realize _ _ _ := ⟨Interp.ofFns exactMachine.fn,
    isScalar_ofFns _ _ (fun _ => rfl), fun q => nomatch q⟩

/-- One fixed tree: `z := 0; repeat n times: z := z + x`. Only the runtime environment supplies
the size. There is no host computation on the concrete size during tree construction. -/
def repeatProgram : Program ScalarOp Empty 1 2 :=
  ⟨.seq (.call (.lit 0) [] [] [⟨1, .const 0⟩])
    (.loop (.var 0) (.call .add [] [⟨1, .const 0⟩, ⟨0, .const 0⟩] [⟨1, .const 0⟩]))⟩

/-- The specified instruction count: one literal, `n` additions, and every structural instruction
of the fixed program, including `n` rounds and three addressed operands per addition. -/
noncomputable def repeatCount (n : ℕ) : Count (ScalarOp ⊕ Bookkeeping) Empty :=
  Count.one (.inr .sequence) [] + Count.one (.inr .indexConst) [] +
    Count.one (.inr .operand) [] + Count.one (.inl (.lit 0)) [] +
    Count.one (.inr .indexVar) [] + Count.one (.inr .loop) [] +
    n • (Count.one (.inr .round) [] +
      (3 • Count.one (.inr .indexConst) [] + 3 • Count.one (.inr .operand) [] +
        Count.one (.inl .add) []))

/-- Projecting the full instruction budget recovers the literal and addition counts exactly. -/
theorem original_repeatCount (n : ℕ) :
    Count.original (repeatCount n) =
      Count.one (.lit 0) [] + n • Count.one .add [] := by
  simp [repeatCount]

/-- The independently specified claim, with a size-only budget and an input-dependent output. -/
noncomputable def repeatSpecification : Specification ScalarOp Empty repeatProblem where
  budget d := repeatCount (d 0)
  scratch _ := 0
  work d := 6 + 8 * d 0
  span d := 6 + 8 * d 0
  memory _ := 2
  good d x _ _ m' := m'.store.get 1 0 = some ((d 0 : ℝ) * (show ℝ from x.val.1))

/-- The total program-logic proof of the source program. -/
theorem wp_repeat {I : Interp ScalarOp Empty ℝ} (hI : IsScalar exactMachine I)
    (d : Fin 1 → ℕ) (input : repeatProblem.Input d) (τ : Tape ℝ) :
    Wp .total I τ repeatProgram.body (Program.environment (b := 2) d)
      (fun m' => m'.store.get 1 0 = some ((d 0 : ℝ) * (show ℝ from input.val.1)))
      (repeatProblem.initial d input) := by
  rw [initial_repeatProblem]
  let x : ℝ := input.val.1
  let m : Mem ℝ := ⟨[[some x], [none]], 0⟩
  change Wp .total I τ repeatProgram.body (Program.environment (b := 2) d) _ m
  refine wp_seq (wp_call_const (hI (.lit 0)) rfl rfl rfl trivial (by simp [m, Store.len]) ?_)
  refine wp_loop (k := d 0) (by simp [Program.environment, IExp.eval])
    (fun i m' => m' = m.upd (1, 0) ((i : ℝ) * x)) ?_ ?_ ?_
  · norm_num [exactMachine]
  · rintro i hi m' rfl
    refine wp_call_bin (hI .add) rfl rfl rfl trivial
      (a := (i : ℝ) * x) (b := x) ?_ ?_ rfl
      (by
        change 0 < (m.store.upd 1 0 ((i : ℝ) * x)).len 1
        rw [Store.len_upd]
        simp [m, Store.len]) ?_
    · exact Store.get_upd_self (by simp [m, Store.len]) _
    · change (m.store.upd 1 0 ((i : ℝ) * x)).get 0 0 = some x
      rw [Store.get_upd_of_ne (Or.inl (by omega))]
      rfl
    · change m.upd (1, 0) ((i : ℝ) * x + x) = m.upd (1, 0) ((↑(i + 1) : ℝ) * x)
      congr 1
      simp [Nat.cast_add, add_mul]
  · rintro m' rfl
    exact Store.get_upd_self (by simp [m, Store.len]) _

/-- The instrumented count is the specified closed form, not a budget defined by the tree. -/
theorem staticCost_repeatProgram (d : Fin 1 → ℕ) :
    stmtCost repeatProgram.body.instrument (Program.environment (b := 2) d).idx =
      repeatCount (d 0) := by
  classical
  simp [repeatProgram, Stmt.instrument, tally, indexBookkeeping, operandBookkeeping,
    IExp.bookkeeping, stmtCost, useCost, Program.environment, IExp.eval, repeatCount,
    smul_smul, Nat.mul_comm]
  module

/-- There is no scratch in either the source program or its structural instrumentation. -/
theorem staticPeak_repeatProgram (d : Fin 1 → ℕ) :
    stmtPeak (instrumentWorkspace repeatModel.workspace) repeatProgram.body.instrument
      (Program.environment (b := 2) d).idx = 0 := by
  simp [repeatProgram, Stmt.instrument, tally, indexBookkeeping, operandBookkeeping,
    IExp.bookkeeping, stmtPeak, Program.environment, repeatModel, AccessModel.workspace,
      repeatResources, instrumentWorkspace]

/-- The independently specified complete budget gives the expected sequential work. -/
theorem work_repeatCount (n : ℕ) : repeatResources.work (repeatCount n) = 6 + 8 * n := by
  simp [ResourceModel.work, repeatCount, Count.one, Count.lift, repeatResources]
  omega

/-- The unit sequential configuration has the same span and work. -/
theorem span_repeatCount (n : ℕ) : repeatResources.span (repeatCount n) = 6 + 8 * n :=
  work_repeatCount n

/-- Full canonical static scratch bytes are zero for this allocation-free program. -/
theorem peak_repeatProgram (d : Fin 1 → ℕ) :
    staticPeak repeatResources repeatProgram d = 0 := by
  rw [staticPeak, queryReserve_repeatResources, Nat.add_zero]
  exact staticPeak_repeatProgram d

/-- A uniform certificate with fixed formats, counts, work, span and total resident payload. -/
noncomputable def repeatAlgorithm : Algorithm repeatModel repeatSpecification :=
  Algorithm.ofWp repeatProgram (by decide)
    (fun d _ x I hI τ => by
      have h := wp_repeat hI.1 d x τ
      exact h.mono fun _ hg _ _ => hg)
    (fun d _ => le_of_eq (staticCost_repeatProgram d))
    (fun d _ => le_of_eq (peak_repeatProgram d))
    (fun d _ => le_of_eq (work_repeatCount (d 0)))
    (fun d _ => le_of_eq (span_repeatCount (d 0)))
    (fun d _ x => by simp [repeatSpecification, initialBytes_repeatProblem])

/-- The target proposition includes all resource dimensions, without extra prover assumptions. -/
theorem certifies_repeatProgram : repeatProgram.Certifies repeatModel repeatSpecification :=
  repeatAlgorithm.correct

/-- Fixed linking rechecks format compatibility and all resource budgets. -/
noncomputable def repeatAlgorithmLinked : Algorithm repeatModel repeatSpecification := by
  refine repeatAlgorithm.link Table.id repeatModel repeatSpecification ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [Program.wellTyped, Program.link] using repeatAlgorithm.wellTyped
  · intro d hd x I hI
    exact hI
  · intro d hd x τ c m' hc hg c' hc'
    exact hg
  · intro d hd
    change stmtCost (repeatProgram.body.link Table.id).instrument
      (Program.environment (b := 2) d).idx ≤ repeatCount (d 0)
    simpa only [Stmt.link_id] using le_of_eq (staticCost_repeatProgram d)
  · intro d hd
    change staticPeak repeatResources (repeatProgram.link Table.id) d ≤ 0
    simpa only [staticPeak, staticCost, Program.link, Stmt.link_id]
      using le_of_eq (peak_repeatProgram d)
  · intro d hd
    exact le_of_eq (work_repeatCount (d 0))
  · intro d hd
    exact le_of_eq (span_repeatCount (d 0))
  · intro d hd x
    simp [repeatSpecification, initialBytes_repeatProblem]

/-! ### Structural rejection claims -/

/-- Model assumptions are exactly satisfaction of the declared primitive contracts. -/
example (M : AccessModel ScalarOp Empty repeatProblem) (d : Fin 1 → ℕ)
    (x : repeatProblem.Input d) (I : Interp ScalarOp Empty ℝ) :
    M.contracts d x I ↔ (∀ o, I.Meets .total o (M.operation d x o)) ∧
      (∀ q, I.MeetsQuery q (M.query d x q)) := Iff.rfl

/-- An arbitrary stronger model assumption is not a field of the core model. -/
example : True := by
  fail_if_success
    have : AccessModel ScalarOp Empty repeatProblem :=
      { repeatModel with contracts := fun _ _ _ => True }
  trivial

/-- An impossible joint arithmetic contract cannot be realized by changing witness names. -/
example (M : AccessModel ScalarOp Empty repeatProblem)
    (h : M.contracts = fun _ _ I =>
      IsScalar exactMachine I ∧ StdModel (1 / 100) (fun _ : ℝ => 0) exactMachine) : False := by
  obtain ⟨I, hI⟩ := M.realize (fun _ => 0) trivial (repeatInput (fun _ => 0) 0)
  change M.contracts _ _ I at hI
  rw [h] at hI
  have hf := hI.2.lit 1
  norm_num at hf

/-- A liberal theorem, or a theorem of `True` named "success", cannot fill the total field. -/
example : ¬ Nonempty (Algorithm repeatModel
    { repeatSpecification with good := fun _ _ _ _ _ => False }) :=
  Algorithm.not_nonempty (fun _ _ _ _ _ _ h => h) (fun _ _ => 0)

/-- Even a size-independent abort cannot be certified under a realized model. -/
example (A : Algorithm repeatModel repeatSpecification) : A.program.body ≠ .abort :=
  A.body_ne_abort

/-- A function constructing a literal from a concrete size is not one fixed program. -/
example : True := by
  let family : ℕ → Stmt ScalarOp Empty :=
    fun n => .call (.lit (n.factorial : ℚ)) [] [] [⟨1, .const 0⟩]
  fail_if_success
    have : Program ScalarOp Empty 1 2 := ⟨family⟩
  trivial

/-- An empty size domain cannot masquerade as a specified problem. -/
example (P : Problem ℝ 1 2) (h : ∀ d, ¬ P.valid d) : False := by
  obtain ⟨d, hd⟩ := P.admitted
  exact h d hd

/-- An admitted size cannot have an empty type of supplied inputs. -/
example (P : Problem ℝ 1 2) (d : Fin 1 → ℕ) (hd : P.valid d)
    (h : P.Input d → False) : False := by
  obtain ⟨x⟩ := P.inputs_exist d hd
  exact h x

/-- An empty word type cannot make the universal tape quantifier vacuous. -/
example (P : Problem Empty 1 0) : ¬ Nonempty (AccessModel Unit Unit P) := by
  rintro ⟨M⟩
  exact Empty.elim M.word

/-- Canonical execution cannot omit even a skipped statement's structural instruction. -/
example (I : Interp ScalarOp Empty ℝ) (τ : Tape ℝ) (d : Fin 1 → ℕ) (m : Mem ℝ) (hlen :
  m.store.length = 2) :
    ∀ st, exec (⟨.skip⟩ : Program ScalarOp Empty 1 2) I repeatResources repeatProblem.formats τ d
      m = some st →
      ¬ st.cost ≤ 0 := by
  intro st hr hc
  have ht : (⟨.skip⟩ : Program ScalarOp Empty 1 2).wellTyped
      repeatResources repeatProblem.formats = true := by decide
  simp [exec, ht, hlen, Stmt.instrument, tally, evalCounted,
    Interp.callS_instrument_inr, St.reserveQueries] at hr
  subst st
  have h := hc (.inl (.inr .skip), [])
  simp [St.init, Count.one] at h

/-- Canonical execution counts index arithmetic even when a loop executes no rounds. -/
example (I : Interp ScalarOp Empty ℝ) (τ : Tape ℝ) (d : Fin 1 → ℕ) (m : Mem ℝ) (hlen :
  m.store.length = 2) :
    ∃ st, exec (⟨.loop (.const 0 * .const 0) .skip⟩ : Program ScalarOp Empty 1 2)
      I repeatResources repeatProblem.formats τ d m = some st ∧ st.cost (.inl (.inr .indexMul),
        []) = 1 := by
  let c : Count (ScalarOp ⊕ Bookkeeping) Empty :=
    Count.one (.inr .indexConst) [] + Count.one (.inr .indexConst) [] +
      Count.one (.inr .indexMul) [] + Count.one (.inr .loop) []
  refine ⟨⟨m, c, 0, 0⟩, ?_, ?_⟩
  · have ht : (⟨.loop (.const 0 * .const 0) .skip⟩ : Program ScalarOp Empty 1 2).wellTyped
        repeatResources repeatProblem.formats = true := by decide
    rw [exec, if_pos ⟨ht, hlen⟩]
    simp [Stmt.instrument, tally, IExp.bookkeeping, evalCounted, IExp.eval,
      Interp.callS_instrument_inr, instrumentWorkspace, iter, St.init, c,
      show repeatResources.workspace = (fun _ _ => 0) from rfl, St.reserveQueries]
  · simp [c, Count.one]

/-- A call outside the declared operation signature is rejected by the core syntax. -/
example : True := by
  fail_if_success
    have : Program ScalarOp Empty 1 2 := ⟨.call () [] [] []⟩
  trivial

end NLAlib.Ops.Examples.Certification
