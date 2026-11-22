/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Randomized
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Eigensolvers.Schur.Completion
public import NLAlib.Eigensolvers.SmallEig.Certification
public import NLAlib.Eigensolvers.HessenbergAccumulate
public import NLAlib.Eigensolvers.Schur.Composition

/-!
# The dense Schur solver as a canonical certificate

The dense Schur pipeline over the model of the small-eigenvalue solver
(`NLAlib.SmallEig.smallEigModel`: scalar arithmetic of a machine `Mch`, exact dimension literals,
comparisons and index conversion, draws of the tape streams and the exact polar disk sampler, unit
costs) is a canonical certificate (`NLAlib.Ops.Algorithm`) built from component data: the four
stage programs, the termination of the pipeline, and a bound on the instrumented static count of
each stage at the offsets the pipeline passes to it. Its work and span are the sum of the stages'
bounds and the glue $128(N + 1)^2$, $N$ the order (`NLAlib.Schur.schurPipelineWork`), so a
swapped stage swaps its cost term (`NLAlib.Schur.size_stmtCost_schurPipelineWith_le`). Every
primitive, test and structural instruction is counted, the stages' included. The every-tape
output claim is the frame: the run writes only the matrix, the accumulator and the flag. The
Schur form is the postcondition of `NLAlib.Ops.Specification.Accepts` in
`NLAlib.Schur.denseSchur_algorithm_measureReal_not_accepts_le`.

## Main definitions

* `NLAlib.Schur.schurPipelineRoutine`, `NLAlib.Schur.schurPipelineSpec`.
* `NLAlib.Schur.schurPipelineProgram`, `NLAlib.Schur.schurPipelineProblem`,
  `NLAlib.Schur.schurPipelineWork`, `NLAlib.Schur.schurPipelineSpecification`,
  `NLAlib.Schur.schurPipelineAlgorithm`: the generic certificate from component data.
* `NLAlib.Schur.denseSchurProblem`, `NLAlib.Schur.denseSchurWork`,
  `NLAlib.Schur.denseSchurAlgorithm`: the instance.

## Main results

* `NLAlib.Schur.denseSchur_algorithm_measureReal_not_accepts_le`: the dense Schur theorem on one
  counted run.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops SmallEig ShiftedQR MeasureTheory ProbabilityTheory
open scoped Matrix

/-! ### The generic program, problem and specification -/

/-- **The routine of the dense Schur pipeline** of the stages `Nm`, `Reg`, `Red`, `Core`:
`[n, nr, nq, k, F, T] (A : update 2 (n + 1)², P : read nr + nq) →
(U : write 2 (n + 1)², Fl : write 1)`, the tree `NLAlib.Schur.schurPipelineWith` at the order
`n + 1`. The dimension `n` is one less than the order, so that every dimension is the order of a
nonempty matrix. The number of draws depends on the data, so the routine declares none. The
written operands are unreported: the every-tape statement of the pipeline is its footprint, and
the Schur form of the output is a statement in probability
(`NLAlib.Schur.denseSchur_algorithm_measureReal_not_accepts_le`). The tree has one variable for
the matrix, named in both positions of the call. -/
def schurPipelineRoutine (Nm Reg Red Core : Stmt SmallEigOp Tst) : Routine SmallEigOp Tst :=
  routine% [n, nr, nq, k, F, T] (unreported A : 2 * ((n + 1) * (n + 1)), P : nr + nq) →
      (A, unreported U : 2 * ((n + 1) * (n + 1)), unreported Fl : 1)
    draws unspecified one variable {
    run (schurPipelineWith Nm Reg Red Core) [n + 1, nr, nq, k, F, T] (A, P, A, U, Fl)
  }

/-- The input of the pipeline at the dimensions `dims`: the words of a matrix of order `n + 1`
and the parameter words `ws`. Nothing is claimed of the written blocks. -/
def schurPipelineSpec (ws : List ℝ) (dims : List ℕ) : Routine.Spec ℝ :=
  .terminates fun d _ X => d = dims ∧
    ∃ A : Matrix (Fin (d.headD 0 + 1)) (Fin (d.headD 0 + 1)) ℂ, X = [matrixWords A, ws]

/-- **The dense Schur pipeline program** of the stages `Nm`, `Reg`, `Red`, `Core` at the order
`d 0 + 1`, `d 1` regularizer words, `d 2` core words and the core dimensions `d 3`, `d 4`, `d 5`,
on the four supplied buffers (matrix, parameter words, accumulator, flag): the routine
`NLAlib.Schur.schurPipelineRoutine` on those buffers. -/
def schurPipelineProgram (Nm Reg Red Core : Stmt SmallEigOp Tst) : Program SmallEigOp Tst 6 4 :=
  (schurPipelineRoutine Nm Reg Red Core).close 6 4

/-- The program is the frame of the pipeline at the order `d 0 + 1` on the supplied buffers. -/
theorem schurPipelineProgram_eq (Nm Reg Red Core : Stmt SmallEigOp Tst) :
    schurPipelineProgram Nm Reg Red Core =
      ⟨.frame [.var 0 + .const 1, .var 1, .var 2, .var 3, .var 4, .var 5]
        [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨0, .var 6⟩, ⟨2, .var 8⟩, ⟨3, .var 9⟩]
        (schurPipelineWith Nm Reg Red Core)⟩ := rfl

/-- **The inputs** at the sizes `d`: the matrix of order `d 0 + 1` and the reals
$\delta, \varphi$. -/
structure SchurData (d : Fin 6 → ℕ) where
  /-- The matrix. -/
  matrix : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ
  /-- The backward error. -/
  δ : ℝ
  /-- The failure probability. -/
  φ : ℝ

/-- **The admitted sizes** on the machine `Mch`: the natural literals up to the order $n + 1$ are
exact and the sizes are those of some $0 < \delta \le 1$, $0 < \varphi \le 1$. No rounding model
is needed: the run completes on any scalar machine (`NLAlib.Schur.denseSchur_completes`). -/
def SchurSizes (Mch : Machine ℝ) (sizes : ℕ → ℝ → ℝ → Fin 6 → ℕ) (d : Fin 6 → ℕ) : Prop :=
  IsExactNatLit id Mch (d 0 + 1) ∧
    ∃ δ φ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < φ ∧ φ ≤ 1 ∧ sizes (d 0) δ φ = d

/-- **The admitted inputs** of the dense Schur pipeline on the machine `Mch`, for the word
function `words` and the size function `sizes` of $(n, \delta, \varphi)$, at the sizes
`NLAlib.Schur.SchurSizes`: every matrix of order `d 0 + 1` and all reals $\delta, \varphi$
whose sizes are `d`. The first operand holds the words of the matrix. The reals are in no
buffer: the second operand holds the parameter words `words`, computed from them, at the
`d 1 + d 2` cells of its port. The accumulator and the flag are blank. -/
noncomputable def schurPipelineInputs (Mch : Machine ℝ) (words : ℕ → ℝ → ℝ → List ℝ)
    (sizes : ℕ → ℝ → ℝ → Fin 6 → ℕ) (admitted : ∃ d, SchurSizes Mch sizes d) :
    (schurPipelineRoutine .skip .skip .skip .skip).Domain ℝ 6 4 where
  valid := SchurSizes Mch sizes
  In := SchurData
  accepts d x := sizes (d 0) x.δ x.φ = d
  slot d := ![.stored (Codec.complexMatrix (d 0 + 1)) SchurData.matrix,
    .derivedOfLength (d 1 + d 2) (fun x => words (d 0) x.δ x.φ),
    .blank (2 * ((d 0 + 1) * (d 0 + 1))), .blank 1]
  fits := by
    intro d i p hp
    fin_cases i <;> (
      have hport := Option.some.inj hp
      subst hport
      constructor <;>
        simp [Slot.len, Slot.held, Slot.derivedOfLength, Access.readable, Codec.complexMatrix,
          List.ofFn_succ])
  Unstored _ := ℝ × ℝ
  unstored _ x := (x.δ, x.φ)
  faithful d x y hu h := by
    have h0 := h 0
    simp only [Slot.input, Matrix.cons_val_zero, Option.some.injEq] at h0
    have hm := (Codec.complexMatrix (d 0 + 1)).encode_injective h0
    obtain ⟨_, _, _⟩ := x
    obtain ⟨_, _, _⟩ := y
    simp only [Prod.mk.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    obtain rfl : _ = _ := hm
    rfl
  admitted := admitted
  inhabited d hd := by
    obtain ⟨-, δ, φ, -, -, -, -, hs⟩ := hd
    exact ⟨⟨0, δ, φ⟩, hs⟩

/-- **The problem** of the dense Schur pipeline on the machine `Mch`: the problem of the admitted
inputs `NLAlib.Schur.schurPipelineInputs`. -/
noncomputable abbrev schurPipelineProblem (Mch : Machine ℝ) (words : ℕ → ℝ → ℝ → List ℝ)
    (sizes : ℕ → ℝ → ℝ → Fin 6 → ℕ) (admitted : ∃ d, SchurSizes Mch sizes d) :
    Problem ℝ 6 4 :=
  (schurPipelineInputs Mch words sizes admitted).problem

/-- **The work (and span) of the pipeline** from the stages' work bounds $W_\bullet$: their sum
and the glue $128(N + 1)^2$, $N$ = `d 0 + 1` (the scaling loops, the identity, the branch and the
frames, `NLAlib.Schur.size_stmtCost_schurPipelineWith_le`). -/
def schurPipelineWork (WNm WReg WRed WCore : (Fin 6 → ℕ) → ℕ) (d : Fin 6 → ℕ) : ℕ :=
  WNm d + WReg d + WRed d + WCore d + 128 * (d 0 + 2) ^ 2

/-- The payload words of the four supplied buffers. -/
def schurPipelineInputWords (d : Fin 6 → ℕ) : ℕ :=
  2 * ((d 0 + 1) * (d 0 + 1)) + (d 1 + d 2) + 2 * ((d 0 + 1) * (d 0 + 1)) + 1

/-- **The specification of the dense Schur pipeline**: the budget, scratch and resident memory of
the static count, the work and the span `NLAlib.Schur.schurPipelineWork`, and on every tape the
frame: the run writes only the matrix, the accumulator and the flag. -/
noncomputable def schurPipelineSpecification (Mch : Machine ℝ) (words : ℕ → ℝ → ℝ → List ℝ)
    (sizes : ℕ → ℝ → ℝ → Fin 6 → ℕ) (admitted : ∃ d, SchurSizes Mch sizes d)
    (Nm Reg Red Core : Stmt SmallEigOp Tst) (WNm WReg WRed WCore : (Fin 6 → ℕ) → ℕ) :
    Specification SmallEigOp Tst (schurPipelineProblem Mch words sizes admitted) where
  budget := staticCost (schurPipelineProgram Nm Reg Red Core)
  scratch := staticPeak smallEigResources (schurPipelineProgram Nm Reg Red Core)
  work := schurPipelineWork WNm WReg WRed WCore
  span := schurPipelineWork WNm WReg WRed WCore
  memory d := schurPipelineInputWords d +
    staticPeak smallEigResources (schurPipelineProgram Nm Reg Red Core) d
  good d x _ _ m := (schurPipelineProblem Mch words sizes admitted).initial d x |>.store.EqOff
    (schurFp (d 0) (0, 0) (2, 0) (3, 0)) m.store

section Generic

variable {Mch : Machine ℝ} {words : ℕ → ℝ → ℝ → List ℝ} {sizes : ℕ → ℝ → ℝ → Fin 6 → ℕ}
  {admitted : ∃ d, SchurSizes Mch sizes d}

/-- The static count of the pipeline program, its structural instructions included, is at most
the work `NLAlib.Schur.schurPipelineWork` of bounds on the stages' instrumented static counts at
the offsets the pipeline passes to them: zero, and $n_r$ = `d 1` for the core's parameter words
(`NLAlib.Schur.size_stmtCost_schurPipelineWith_le`). -/
theorem size_staticCost_schurPipelineProgram_le {Nm Reg Red Core : Stmt SmallEigOp Tst}
    {WNm WReg WRed WCore : (Fin 6 → ℕ) → ℕ}
    (hNm : ∀ d, Count.size (stmtCost Nm.instrument [d 0 + 1, 0, 0]) ≤ WNm d)
    (hReg : ∀ d, Count.size (stmtCost Reg.instrument [d 0 + 1, d 1, 0, 0, 0]) ≤ WReg d)
    (hRed : ∀ d, Count.size (stmtCost Red.instrument [d 0 + 1, 0, 0, 0, 0]) ≤ WRed d)
    (hCore : ∀ d, Count.size (stmtCost Core.instrument
      [d 0 + 1, d 2, d 3, d 4, d 5, 0, d 1, 0, 0, 0, 0]) ≤ WCore d)
    (d : Fin 6 → ℕ) :
    Count.size (staticCost (schurPipelineProgram Nm Reg Red Core) d) ≤
      schurPipelineWork WNm WReg WRed WCore d := by
  have he : (Program.environment (b := 4) d).idx = [d 0, d 1, d 2, d 3, d 4, d 5, 0, 0, 0, 0] :=
    rfl
  have h := size_stmtCost_schurPipelineWith_le Nm Reg Red Core (d 0 + 1) (d 1) (d 2) (d 3) (d 4)
    (d 5)
  have h1 := hNm d
  have h2 := hReg d
  have h3 := hRed d
  have h4 := hCore d
  simp only [staticCost, schurPipelineProgram_eq, he, Stmt.instrument, stmtCost, tally,
    indexBookkeeping, operandBookkeeping, IExp.bookkeeping, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, useCost, IExp.evalList, IExp.eval,
    List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.map_some, Option.getD_some, map_add, map_zero, Count.one, size_single]
  unfold schurPipelineWork
  have hsq : 2 ^ 2 ≤ (d 0 + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hsq' : (d 0 + 1 + 1) ^ 2 = (d 0 + 2) ^ 2 := by ring
  omega

/-- The sizes of an input of the problem are those of its reals. -/
theorem schurPipelineProblem_sizes_eq (d : Fin 6 → ℕ)
    (x : (schurPipelineProblem Mch words sizes admitted).Input d) :
    sizes (d 0) x.val.1.δ x.val.1.φ = d :=
  (schurPipelineInputs Mch words sizes admitted).accepts_data x

/-- The four supplied buffers of an input, when the words have the sizes' count: the matrix
words, the parameter words, uninitialized room for the accumulator and the flag. -/
theorem schurPipelineProblem_buffers
    (hwords : ∀ n δ φ, (words n δ φ).length = sizes n δ φ 1 + sizes n δ φ 2) (d : Fin 6 → ℕ)
    (x : (schurPipelineProblem Mch words sizes admitted).Input d) :
    x.val.2 = ![(matrixWords x.val.1.matrix).map some,
      (words (d 0) x.val.1.δ x.val.1.φ).map some,
      List.replicate (2 * ((d 0 + 1) * (d 0 + 1))) none, [none]] := by
  rw [(schurPipelineInputs Mch words sizes admitted).buffers_eq x]
  funext i
  fin_cases i
  · rfl
  · refine Slot.buffer_derivedOfLength ?_
    rw [hwords, schurPipelineProblem_sizes_eq d x]
  · rfl
  · rfl

/-- The initial payload of an input is `NLAlib.Schur.schurPipelineInputWords`. -/
theorem schurPipelineProblem_initialBytes (d : Fin 6 → ℕ)
    (x : (schurPipelineProblem Mch words sizes admitted).Input d) :
    (schurPipelineProblem Mch words sizes admitted).initialBytes d x =
      schurPipelineInputWords d := by
  refine ((schurPipelineInputs Mch words sizes admitted).initialBytes_eq x).trans ?_
  simp [schurPipelineInputs, Slot.len, Slot.derivedOfLength, Codec.complexMatrix, List.ofFn_succ,
    schurPipelineInputWords, Nat.add_assoc]

/-- The initial memory holds the input of the pipeline (`NLAlib.Schur.SchurPipelineInput`) at
the four supplied buffers, when the words have the sizes' count (the parameter operand has
`d 1 + d 2` cells). -/
theorem schurPipelineProblem_initial_input
    (hwords : ∀ n δ φ, (words n δ φ).length = sizes n δ φ 1 + sizes n δ φ 2) (d : Fin 6 → ℕ)
    (x : (schurPipelineProblem Mch words sizes admitted).Input d) :
    SchurPipelineInput (words (d 0) x.val.1.δ x.val.1.φ) (0, 0) (1, 0) (2, 0) (3, 0)
      x.val.1.matrix ((schurPipelineProblem Mch words sizes admitted).initial d x) := by
  have hb := schurPipelineProblem_buffers hwords d x
  have hs : ((schurPipelineProblem Mch words sizes admitted).initial d x).store =
      List.ofFn x.val.2 := rfl
  have hA := Problem.initial_readBlock (P := schurPipelineProblem Mch words sizes admitted) d x
    (0 : Fin 4) (xs := matrixWords x.val.1.matrix) (by rw [hb]; rfl)
  have hP := Problem.initial_readBlock (P := schurPipelineProblem Mch words sizes admitted) d x
    (1 : Fin 4) (xs := words (d 0) x.val.1.δ x.val.1.φ) (by rw [hb]; rfl)
  refine ⟨?_, ?_, ?_, by simpa [HoldsMatrix] using hA, by simpa using hP⟩
  · simp [Mem.Live, Problem.initial]
  · simp [hs, hb, Mem.Room, Store.len, List.ofFn_succ]
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨Fp.disj_inBlock_of_ne (by omega), Fp.disj_inBlock_of_ne (by omega),
      Fp.disj_inBlock_of_ne (by omega)⟩, ⟨Fp.disj_inBlock_of_ne (by omega),
      Fp.disj_inBlock_of_ne (by omega)⟩, Fp.disj_inBlock_of_ne (by omega)⟩

/-- **The dense Schur pipeline as a canonical certificate, from component data**: the fixed
program `NLAlib.Schur.schurPipelineProgram` of any four stages, over the model
`NLAlib.SmallEig.smallEigModel` with the unit costs, given that it passes the storage discipline
(`ht`), its routine meets the every-tape specification `NLAlib.Schur.schurPipelineSpec` under
every interpretation of the model (`hmeets`: it terminates and writes only the matrix, the
accumulator and the flag), and the stages' instrumented static counts at the
pipeline's offsets are at most $W_\bullet$, succeeds within the static budget, scratch and
memory, with work and span at most `NLAlib.Schur.schurPipelineWork` of the $W_\bullet$.
Algorithm: dense-schur (run model) -/
noncomputable def schurPipelineAlgorithm (sU : ℕ) (Nm Reg Red Core : Stmt SmallEigOp Tst)
    (WNm WReg WRed WCore : (Fin 6 → ℕ) → ℕ)
    (hNm : ∀ d, Count.size (stmtCost Nm.instrument [d 0 + 1, 0, 0]) ≤ WNm d)
    (hReg : ∀ d, Count.size (stmtCost Reg.instrument [d 0 + 1, d 1, 0, 0, 0]) ≤ WReg d)
    (hRed : ∀ d, Count.size (stmtCost Red.instrument [d 0 + 1, 0, 0, 0, 0]) ≤ WRed d)
    (hCore : ∀ d, Count.size (stmtCost Core.instrument
      [d 0 + 1, d 2, d 3, d 4, d 5, 0, d 1, 0, 0, 0, 0]) ≤ WCore d)
    (hwords : ∀ n δ φ, (words n δ φ).length = sizes n δ φ 1 + sizes n δ φ 2)
    (ht : (schurPipelineProgram Nm Reg Red Core).wellTyped smallEigResources
      (schurPipelineProblem Mch words sizes admitted).formats = true)
    (hmeets : ∀ d, SchurSizes Mch sizes d →
      ∀ (x : (schurPipelineProblem Mch words sizes admitted).Input d) (I : Interp SmallEigOp Tst ℝ),
      (smallEigModel (schurPipelineProblem Mch words sizes admitted) Mch sU).contracts d x I →
      (schurPipelineRoutine Nm Reg Red Core).Meets I
        (schurPipelineSpec (words (d 0) x.val.1.δ x.val.1.φ) (List.ofFn d))) :
    Algorithm (smallEigModel (schurPipelineProblem Mch words sizes admitted) Mch sU)
      (schurPipelineSpecification Mch words sizes admitted Nm Reg Red Core WNm WReg WRed WCore) :=
  ((schurPipelineInputs Mch words sizes admitted).cast (schurPipelineRoutine Nm Reg Red Core)
      rfl rfl).algorithm
    (fun d x => schurPipelineSpec (words (d 0) x.δ x.φ) (List.ofFn d)) hmeets
    (fun d _ x hx _ => by
      have hw : (Slot.derivedOfLength (d 1 + d 2) fun x : SchurData d =>
          words (d 0) x.δ x.φ).words x = words (d 0) x.δ x.φ :=
        Slot.words_derivedOfLength (by
          have hx' : sizes (d 0) x.δ x.φ = d := hx
          rw [hwords, hx'])
      refine ⟨rfl, x.matrix, ?_⟩
      change [matrixWords x.matrix, (Slot.derivedOfLength (d 1 + d 2) fun x : SchurData d =>
        words (d 0) x.δ x.φ).words x] = _
      rw [hw]
      rfl)
    (fun d _ x τ m' hfr _ ys _ _ c _ => by
      change Store.EqOff (Fp.blocks [(0, 0), (2, 0), (3, 0)]
        [2 * ((d 0 + 1) * (d 0 + 1)), 2 * ((d 0 + 1) * (d 0 + 1)), 1]) _ _ at hfr
      refine hfr.mono ?_
      unfold schurFp
      fp_sub)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun d _ => (smallEigResources_work _).trans_le
      (size_staticCost_schurPipelineProgram_le hNm hReg hRed hCore d))
    (fun d _ => (smallEigResources_span _).trans_le
      (size_staticCost_schurPipelineProgram_le hNm hReg hRed hCore d))
    (fun d _ x =>
      Nat.add_le_add_right (schurPipelineProblem_initialBytes (admitted := admitted) d x).le _)
    (ht := ht)

/-- What the generic certificate states: at every admitted size, for every admitted input, every
interpretation satisfying the contracts of the model and every tape, the run of the fixed program
from the supplied buffers succeeds within the scratch, the budget, the work and the span of the
specification, and its final memory satisfies the output condition
(`NLAlib.Ops.Routine.Domain.Checked`). The deterministic claim is termination within the
footprint only. The accuracy is a statement about the stages, with probability over the draws:
for the dense instance it is `NLAlib.Schur.denseSchurClaim`. -/
theorem schurPipeline_checked (sU : ℕ) (Nm Reg Red Core : Stmt SmallEigOp Tst)
    (WNm WReg WRed WCore : (Fin 6 → ℕ) → ℕ)
    (hNm : ∀ d, Count.size (stmtCost Nm.instrument [d 0 + 1, 0, 0]) ≤ WNm d)
    (hReg : ∀ d, Count.size (stmtCost Reg.instrument [d 0 + 1, d 1, 0, 0, 0]) ≤ WReg d)
    (hRed : ∀ d, Count.size (stmtCost Red.instrument [d 0 + 1, 0, 0, 0, 0]) ≤ WRed d)
    (hCore : ∀ d, Count.size (stmtCost Core.instrument
      [d 0 + 1, d 2, d 3, d 4, d 5, 0, d 1, 0, 0, 0, 0]) ≤ WCore d)
    (hwords : ∀ n δ φ, (words n δ φ).length = sizes n δ φ 1 + sizes n δ φ 2)
    (ht : (schurPipelineProgram Nm Reg Red Core).wellTyped smallEigResources
      (schurPipelineProblem Mch words sizes admitted).formats = true)
    (hmeets : ∀ d, SchurSizes Mch sizes d →
      ∀ (x : (schurPipelineProblem Mch words sizes admitted).Input d) (I : Interp SmallEigOp Tst ℝ),
      (smallEigModel (schurPipelineProblem Mch words sizes admitted) Mch sU).contracts d x I →
      (schurPipelineRoutine Nm Reg Red Core).Meets I
        (schurPipelineSpec (words (d 0) x.val.1.δ x.val.1.φ) (List.ofFn d))) :
    ((schurPipelineInputs Mch words sizes admitted).cast (schurPipelineRoutine Nm Reg Red Core)
      rfl rfl).Checked
      (schurPipelineAlgorithm sU Nm Reg Red Core WNm WReg WRed WCore hNm hReg hRed hCore hwords
        ht hmeets) :=
  ((schurPipelineInputs Mch words sizes admitted).cast (schurPipelineRoutine Nm Reg Red Core)
    rfl rfl).checked_all _

end Generic

/-! ### The instance -/

/-- The sizes of a run of the dense Schur solver at $(n, \delta, \varphi)$: $n$, the numbers of
regularizer and core words, the shift degree, the iteration cap and the leaf cap. -/
noncomputable def denseSchurSizes (n : ℕ) (δ φ : ℝ) : Fin 6 → ℕ :=
  ![n, (denseSchurRegParams n δ φ).length,
    (denseSchurThreshold n δ φ ::
      (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ)).length,
    denseSchurDegree n δ φ, denseSchurCap n δ φ, denseSchurLeafCap n δ φ]

/-- The parameter words have the sizes' count. -/
theorem length_denseSchurParams (n : ℕ) (δ φ : ℝ) :
    (denseSchurParams n δ φ).length = denseSchurSizes n δ φ 1 + denseSchurSizes n δ φ 2 := by
  simp [denseSchurParams, denseSchurParamsWith, denseSchurSizes]

/-- **The problem** of the dense Schur solver on the machine `Mch`. -/
noncomputable def denseSchurProblem (Mch : Machine ℝ)
    (admitted : ∃ d, SchurSizes Mch denseSchurSizes d) : Problem ℝ 6 4 :=
  schurPipelineProblem Mch denseSchurParams denseSchurSizes admitted

/-- **The work (and span) of the dense Schur solver** at the sizes
$(n, n_r, n_q, k, F, T)$ = `d`: `NLAlib.Schur.schurPipelineWork` of the monomial bounds of the
instrumented static counts of its four stages, $120(n + 1)^2$ for the Frobenius norm
(`NLAlib.Schur.size_stmtCost_frobNormStage_le`), $201(n + 1)^2$ for the Ginibre regularizer
(`NLAlib.Schur.size_stmtCost_ginibrePerturb_le`), $2998(n + 1)^3$ for the reduction with its
accumulated unitary (`NLAlib.Schur.size_stmtCost_hessenbergReduceQ_le`) and
$380748(n + 1)^3(k + 1)^4(n_r + n_q + 1)(F + 1)(T + 1)^2$ for the rounded shifted QR core with the
`SmallEig` leaf (`NLAlib.ShiftedQR.size_stmtCost_roundedShQRSchur_le`), and the glue
$128(n + 2)^2$. Every primitive, test and structural instruction is counted at unit cost; the
parameter words are supplied in the input and their computation is not charged. -/
def denseSchurWork (d : Fin 6 → ℕ) : ℕ :=
  schurPipelineWork (fun d => 120 * (d 0 + 1) ^ 2) (fun d => 201 * (d 0 + 1) ^ 2)
    (fun d => 2998 * (d 0 + 1) ^ 3)
    (fun d => 380748 * (d 0 + 1) ^ 3 * (d 3 + 1) ^ 4 * (d 1 + d 2 + 1) * (d 4 + 1) *
      (d 5 + 1) ^ 2) d

/-- **The specification of the dense Schur solver** on the machine `Mch`:
`NLAlib.Schur.schurPipelineSpecification` of its four stages, with the work and span
`NLAlib.Schur.denseSchurWork`. -/
noncomputable def denseSchurSpecification (Mch : Machine ℝ)
    (admitted : ∃ d, SchurSizes Mch denseSchurSizes d) (sG : ℕ) :
    Specification SmallEigOp Tst (denseSchurProblem Mch admitted) :=
  schurPipelineSpecification Mch denseSchurParams denseSchurSizes admitted frobNormStage
    (ginibrePerturb sG) hessenbergReduceQ (roundedShQRSchur sG) (fun d => 120 * (d 0 + 1) ^ 2)
    (fun d => 201 * (d 0 + 1) ^ 2) (fun d => 2998 * (d 0 + 1) ^ 3)
    (fun d => 380748 * (d 0 + 1) ^ 3 * (d 3 + 1) ^ 4 * (d 1 + d 2 + 1) * (d 4 + 1) *
      (d 5 + 1) ^ 2)

-- The kernel evaluates the discipline over the whole tree; its recursion is deep.
set_option maxRecDepth 100000 in
/-- The dense Schur program passes the storage discipline of the costs. -/
theorem denseSchurProgram_wellTyped (sG : ℕ) {Mch : Machine ℝ}
    {admitted : ∃ d, SchurSizes Mch denseSchurSizes d} :
    (schurPipelineProgram frobNormStage (ginibrePerturb sG) hessenbergReduceQ
      (roundedShQRSchur sG)).wellTyped smallEigResources
      (denseSchurProblem Mch admitted).formats = true := by
  kernel_rfl

/-- The dense Schur program terminates on every admitted input, interpretation of the model and
tape, and writes only the matrix, the accumulator and the flag
(`NLAlib.Schur.denseSchur_completes`, no rounding model). -/
theorem denseSchurProgram_wp {Mch : Machine ℝ} {admitted : ∃ d, SchurSizes Mch denseSchurSizes d}
    {sU sG : ℕ} {d : Fin 6 → ℕ} (hd : SchurSizes Mch denseSchurSizes d)
    (x : (denseSchurProblem Mch admitted).Input d) {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (denseSchurProblem Mch admitted) Mch sU).contracts d x I) (τ : Tape ℝ) :
    Wp .total I τ (schurPipelineProgram frobNormStage (ginibrePerturb sG) hessenbergReduceQ
        (roundedShQRSchur sG)).body (Program.environment (b := 4) d)
      (fun m => ((denseSchurProblem Mch admitted).initial d x).store.EqOff
        (schurFp (d 0) (0, 0) (2, 0) (3, 0)) m.store)
      ((denseSchurProblem Mch admitted).initial d x) := by
  obtain ⟨hNat, -⟩ := hd
  obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
  have hin := schurPipelineProblem_initial_input (admitted := admitted)
    length_denseSchurParams d x
  have hl5 : ((denseSchurProblem Mch admitted).initial d x).Live
      [(0, 0), (1, 0), (0, 0), (2, 0), (3, 0)] := fun y hy => hin.1 y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp)
  have hsz := schurPipelineProblem_sizes_eq d x
  refine wp_frame ?_ ?_ hl5 (Wp.mono (denseSchur_completes (O := SmallEigOp) (Q := Tst)
    (sG := sG) hS hL hNat hQ hC hSmp hDisk hin τ) fun _ h => h.1)
  · have h := fun i => (congrFun hsz i).symm
    simp [Program.environment, IExp.evalList, IExp.eval, denseSchurDims, denseSchurDimsWith,
      List.ofFn_succ, h 1, h 2, h 3, h 4, h 5, denseSchurSizes]
  · simp [Program.environment, Operand.evalList, Operand.eval, IExp.eval, List.ofFn_succ]

/-- **The routine of the dense Schur solver meets its every-tape specification**: on the
words of a matrix of order $n + 1$ and the words `NLAlib.Schur.denseSchurParams`, at the
dimensions of `NLAlib.Schur.denseSchurDims`, it terminates on every tape and writes only the
matrix, the accumulator and the flag (`NLAlib.Schur.denseSchur_completes`, no rounding model). -/
theorem denseSchurRoutine_meets {Mch : Machine ℝ} {I : Interp SmallEigOp Tst ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) (hSmp : IsSample I) {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {δ φ : ℝ} :
    (schurPipelineRoutine frobNormStage (ginibrePerturb sG) hessenbergReduceQ
      (roundedShQRSchur sG)).Meets I
      (schurPipelineSpec (denseSchurParams n δ φ) (n :: (denseSchurDims n δ φ).tail)) := by
  routine_intro [n', nr, nq, k, F, T] (a, p, uo, f) reads (ws, ps)
  obtain ⟨hd, A, heq⟩ := hpre
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ : n' = n ∧ nr = (denseSchurRegParams n δ φ).length ∧
      nq = (denseSchurThreshold n δ φ ::
        (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ)).length ∧
      k = denseSchurDegree n δ φ ∧ F = denseSchurCap n δ φ ∧ T = denseSchurLeafCap n δ φ := by
    simpa [denseSchurDims, denseSchurDimsWith] using hd
  obtain ⟨rfl, rfl⟩ : ws = matrixWords A ∧ ps = denseSchurParams n' δ φ := by simpa using heq
  have hlen : (denseSchurParams n' δ φ).length = (denseSchurRegParams n' δ φ).length +
      (denseSchurThreshold n' δ φ ::
        (denseSchurShQRParams n' δ φ ++ denseSchurLeafParams n' δ φ)).length := by
    simp [denseSchurParams, denseSchurParamsWith]
  rw [← hlen] at hps
  have hin : SchurPipelineInput (denseSchurParams n' δ φ) a p uo f A m := by
    refine ⟨by room, ?_, by disjoint, hws, hps⟩
    simp only [Mem.room_cons, Mem.room_nil, and_true]
    exact ⟨hroom.1, Store.le_len_of_readBlock hps (by rw [hlen, List.length_cons]; omega),
      hroom.2.1, hroom.2.2⟩
  have hT := denseSchur_completes (sG := sG) hS hL hNat hQ hC hSmp hDisk hin τ
  refine (hT.in_frame (ρ := Env.frame [n', (denseSchurRegParams n' δ φ).length,
    (denseSchurThreshold n' δ φ ::
      (denseSchurShQRParams n' δ φ ++ denseSchurLeafParams n' δ φ)).length,
    denseSchurDegree n' δ φ, denseSchurCap n' δ φ, denseSchurLeafCap n' δ φ] [a, p, uo, f])
    rfl rfl (by room)).mono ?_ ?_
  · unfold schurFp
    fp_sub
  · rintro m' - -
    exact ⟨trivial, [], rfl, trivial⟩

/-- **The dense Schur solver as a canonical certificate**: `NLAlib.Schur.schurPipelineAlgorithm`
with the four stages of `NLAlib.Schur.denseSchur` and their static counts, over the model
`NLAlib.SmallEig.smallEigModel` (no oracle) with the unit costs: it succeeds on every admitted
input, interpretation of the model and tape, within the static budget, scratch and memory, with
work and span at most `NLAlib.Schur.denseSchurWork`, writing only the matrix, the accumulator and
the flag. The Schur form holds with probability at least $1 - \varphi$
(`NLAlib.Schur.denseSchur_algorithm_measureReal_not_accepts_le`).
Algorithm: dense-schur (run model) -/
noncomputable def denseSchurAlgorithm (Mch : Machine ℝ)
    (admitted : ∃ d, SchurSizes Mch denseSchurSizes d) (sU sG : ℕ) :
    Algorithm (smallEigModel (denseSchurProblem Mch admitted) Mch sU)
      (denseSchurSpecification Mch admitted sG) :=
  schurPipelineAlgorithm sU _ _ _ _ _ _ _ _ (fun d => size_stmtCost_frobNormStage_le (d 0))
    (fun d => size_stmtCost_ginibrePerturb_le sG (d 0) (d 1))
    (fun d => size_stmtCost_hessenbergReduceQ_le (d 0))
    (fun d => size_stmtCost_roundedShQRSchur_le sG (d 0) (d 2) (d 3) (d 4) (d 5) (d 1))
    length_denseSchurParams (denseSchurProgram_wellTyped sG)
    (fun d hd x _ hI => by
      obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
      have h := denseSchurRoutine_meets (sG := sG) (n := d 0) (δ := x.val.1.δ) (φ := x.val.1.φ)
        hS hL hd.1 hQ hC hSmp hDisk
      have hsz := fun i => congrFun (schurPipelineProblem_sizes_eq d x) i
      have hdims : d 0 :: (denseSchurDims (d 0) x.val.1.δ x.val.1.φ).tail = List.ofFn d := by
        simp [denseSchurDims, denseSchurDimsWith, List.ofFn_succ, ← hsz 1, ← hsz 2, ← hsz 3,
          ← hsz 4, ← hsz 5, denseSchurSizes]
      rw [hdims] at h
      exact h)

/-- **The dense Schur solver, on one run.** Let the machine `Mch` have the standard model at
$\boldsymbol{u}$; let the tape $\xi$ have the stream laws `law`, with `law` $s_U$ uniform on
$[0, 1]$ and `law` $s_G$ the standard real Gaussian law. Let $(n, n_r, n_q, k, F, T)$ = `d` be
admitted and let the input `x` hold a complex $\mathbf{A}$ of order $n + 1$, $0 < \delta \le 1$,
$0 < \varphi \le 1$ and $\boldsymbol{u} \le \boldsymbol{u}_0$. Let `I` meet the model, be
measurable and read the tape only in its windows. Then
$$\mathbb{P}\bigl[\mathsf{denseSchurAlgorithm}(\mathbf{A}) \text{ fails, exceeds its budget,
  scratch, memory, work or span, writes outside } \mathbf{A}, \widehat{\mathbf{U}} \text{ and the
  flag, or stores no flag } 0 \text{ and } \widehat{\mathbf{U}}, \widehat{\mathbf{T}} \text{ with
  } \widehat{\mathbf{T}} \text{ upper triangular},\ \|\mathbf{A} - \widehat{\mathbf{U}}
  \widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le \delta\|\mathbf{A}\|_2,\
  \|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} - \mathbf{I}\|_2 \le 58R\boldsymbol{u}
  \bigr] \le \varphi\,,$$
on one counted run, with the work and the span `NLAlib.Schur.denseSchurWork`. Here
$\boldsymbol{u}_0$ is `NLAlib.Schur.uDenseSchur` and $R$ is `NLAlib.Schur.denseSchurRotations`.
[BanksGarzaVargasSrivastava2022, Theorem 1.4] with [BanksGarzaVargasSrivastava2025, Theorem 1.1];
there only the eigenvalues are computed.

Note: General form, any program meeting the model: `NLAlib.Ops.Algorithm`; the statement on the
program is `NLAlib.Schur.denseSchur_measureReal_not_schur_le`.
Result: dense-schur-certificate-accuracy -/
theorem denseSchur_algorithm_measureReal_not_accepts_le {Mch : Machine ℝ}
    {admitted : ∃ d, SchurSizes Mch denseSchurSizes d} {u : ℝ} (hM : StdModel u id Mch)
    {law : ℕ → Measure ℝ} {sU sG : ℕ} (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {d : Fin 6 → ℕ} (hd : SchurSizes Mch denseSchurSizes d)
    (x : (denseSchurProblem Mch admitted).Input d) {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (denseSchurProblem Mch admitted) Mch sU).contracts d x I)
    (hIm : I.IsMeasurable) {win : SmallEigOp → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hδ : 0 < x.val.1.δ) (hδ1 : x.val.1.δ ≤ 1) (hφ : 0 < x.val.1.φ) (hφ1 : x.val.1.φ ≤ 1)
    (hu : u ≤ uDenseSchur (d 0) x.val.1.δ x.val.1.φ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ (denseSchurSpecification Mch admitted sG).Accepts smallEigResources d x
      (exec (denseSchurAlgorithm Mch admitted sU sG).program I smallEigResources
        (denseSchurProblem Mch admitted).formats (ξ ω) d
        ((denseSchurProblem Mch admitted).initial d x))
      fun _ m => ((denseSchurProblem Mch admitted).initial d x).store.EqOff
          (schurFp (d 0) (0, 0) (2, 0) (3, 0)) m.store ∧
        SchurOutput (0, 0) (2, 0) (3, 0) x.val.1.matrix x.val.1.δ
          (58 * denseSchurRotations (d 0) x.val.1.δ x.val.1.φ * u) m} ≤ x.val.1.φ := by
  have := hξ.isProbabilityMeasure
  obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
  have hin := schurPipelineProblem_initial_input (admitted := admitted)
    length_denseSchurParams d x
  have hT := denseSchur_measureReal_not_schur_le (O := SmallEigOp) (Q := Tst) (sG := sG) hS hM
    hL hd.1 hQ hC hIm hloc hSmp hDisk hU hG hδ hδ1 hφ hφ1 hu hin hξ
  refine (denseSchurAlgorithm Mch admitted sU sG).measureReal_not_accepts_le_of_wp hd x
    I hI P ξ _ ?_
  refine (measureReal_mono ?_).trans hT
  intro ω hω hW
  have hl3 := hin.1
  have hl5 : ((denseSchurProblem Mch admitted).initial d x).Live
      [(0, 0), (1, 0), (0, 0), (2, 0), (3, 0)] := fun y hy => hl3 y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp)
  have hsz := schurPipelineProblem_sizes_eq d x
  refine hω (wp_frame ?_ ?_ hl5 hW)
  · have h := fun i => (congrFun hsz i).symm
    simp [Program.environment, IExp.evalList, IExp.eval, denseSchurDims, denseSchurDimsWith,
      List.ofFn_succ, h 1, h 2, h 3, h 4, h 5, denseSchurSizes]
  · simp [Program.environment, Operand.evalList, Operand.eval, IExp.eval, List.ofFn_succ]

/-- What the certificate states: at every admitted size, for every admitted input, every
interpretation satisfying the contracts of the model and every tape, the run of the fixed program
from the supplied buffers succeeds within the scratch, the budget, the work and the span of the
specification, and its final memory satisfies the output condition
(`NLAlib.Ops.Routine.Domain.Checked`). The deterministic claim is termination within the
footprint only; the accuracy of the stored Schur form holds with probability over the draws:
`NLAlib.Schur.denseSchurClaim`. -/
theorem denseSchur_checked (Mch : Machine ℝ)
    (admitted : ∃ d, SchurSizes Mch denseSchurSizes d) (sU sG : ℕ) :
    ((schurPipelineInputs Mch denseSchurParams denseSchurSizes admitted).cast
      (schurPipelineRoutine frobNormStage (ginibrePerturb sG) hessenbergReduceQ
        (roundedShQRSchur sG)) rfl rfl).Checked (denseSchurAlgorithm Mch admitted sU sG) :=
  ((schurPipelineInputs Mch denseSchurParams denseSchurSizes admitted).cast
    (schurPipelineRoutine frobNormStage (ginibrePerturb sG) hessenbergReduceQ
      (roundedShQRSchur sG)) rfl rfl).checked_all _

/-! ### The randomized claim -/

/-- **The randomized claim of the dense Schur certificate**
([BanksGarzaVargasSrivastava2022, Theorem 1.4] with [BanksGarzaVargasSrivastava2025,
Theorem 1.1]). The entries of the tape are independent, uniform on $[0, 1]$ on the stream $s_U$
and standard Gaussian on the stream $s_G$. For $0 < \delta \le 1$, $0 < \varphi \le 1$ and
$\boldsymbol{u} \le \boldsymbol{u}_0$ (`NLAlib.Schur.uDenseSchur`), and an interpretation that
is measurable and reads the tape only in its windows, the counted run writes only the matrix,
the accumulator and the flag, and stores the flag $0$ with an upper triangular
$\widehat{\mathbf{T}}$ and a $\widehat{\mathbf{U}}$ within $58 R \boldsymbol{u}$ of unitary
whose product is within $\delta \|\mathbf{A}\|_2$ of $\mathbf{A}$, except with probability at
most $\varphi$. -/
noncomputable def denseSchurClaim (Mch : Machine ℝ)
    (admitted : ∃ d, SchurSizes Mch denseSchurSizes d) (sU sG : ℕ) {u : ℝ}
    (hM : StdModel u id Mch) : RandomizedClaim (denseSchurAlgorithm Mch admitted sU sG) where
  law _ _ := TapeModel.streams [(sU, volume.restrict (Set.Icc 0 1)), (sG, gaussianReal 0 1)]
  admits d x := 0 < x.val.1.δ ∧ x.val.1.δ ≤ 1 ∧ 0 < x.val.1.φ ∧ x.val.1.φ ≤ 1 ∧
    u ≤ uDenseSchur (d 0) x.val.1.δ x.val.1.φ
  interprets _ _ I := I.IsMeasurable ∧
    ∃ win : SmallEigOp → List ℕ → ℕ, ∀ o, I.TapeLocal o (win o)
  event d x _ _ m := ((denseSchurProblem Mch admitted).initial d x).store.EqOff
      (schurFp (d 0) (0, 0) (2, 0) (3, 0)) m.store ∧
    SchurOutput (0, 0) (2, 0) (3, 0) x.val.1.matrix x.val.1.δ
      (58 * denseSchurRotations (d 0) x.val.1.δ x.val.1.φ * u) m
  bound _ x := x.val.1.φ
  holds := fun d hd x hx I hI hint Ω _ μ _ tape hlaw => by
    obtain ⟨law, hfix, hξ⟩ := hlaw
    obtain ⟨hIm, win, hloc⟩ := hint
    obtain ⟨hδ, hδ1, hφ, hφ1, hu⟩ := hx
    exact denseSchur_algorithm_measureReal_not_accepts_le hM (hfix _ (List.Mem.head _))
      (hfix _ (List.Mem.tail _ (List.Mem.head _))) hd x hI hIm hloc hδ hδ1 hφ hφ1 hu hξ

end NLAlib.Schur
