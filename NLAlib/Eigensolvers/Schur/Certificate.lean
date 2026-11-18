/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.Dense
public import NLAlib.Eigensolvers.SmallEig.Certificate

/-!
# The dense Schur solver as a canonical certificate

The dense Schur pipeline over the model of the small-eigenvalue solver
(`NLAlib.SmallEig.smallEigModel`: scalar arithmetic of a machine `Mch`, exact dimension literals,
comparisons and index conversion, draws of the tape streams and the exact polar disk sampler, unit
costs) is a canonical certificate (`NLAlib.Ops.Algorithm`) built from component data: the four
stage programs, the termination of the pipeline, and a static work bound of each stage. Its work
and span are the sum of the stages' bounds and the glue $64(N + 1)^2$
(`NLAlib.Schur.schurPipelineWork`), so a swapped stage swaps its cost term
(`NLAlib.Schur.size_stmtCost_schurPipelineWith_le`). The every-tape output claim is the frame:
the run writes only the matrix, the accumulator and the flag. The Schur form is the postcondition
of `NLAlib.Ops.Specification.Accepts` in
`NLAlib.Schur.denseSchur_algorithm_measureReal_not_accepts_le`.

## Main definitions

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

/-- **The dense Schur pipeline program** of the stages `Nm`, `Reg`, `Red`, `Core` at the order
`d 0 + 1`, `d 1` regularizer words, `d 2` core words and the core dimensions `d 3`, `d 4`, `d 5`,
on the four supplied buffers (matrix, parameter words, accumulator, flag). -/
def schurPipelineProgram (Nm Reg Red Core : Impl SmallEigOp Tst) : Program SmallEigOp Tst 6 4 :=
  ⟨.frame [.var 0 + .const 1, .var 1, .var 2, .var 3, .var 4, .var 5]
    [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨0, .var 6⟩, ⟨2, .var 8⟩, ⟨3, .var 9⟩]
    (schurPipelineWith Nm Reg Red Core).body⟩

/-- **The semantic input** at the sizes `d`, for the word function `words` and the size function
`sizes` of $(n, \delta, \varphi)$: the matrix of order `d 0 + 1` and the reals $\delta, \varphi$,
with the sizes the ones they determine. -/
structure SchurData (words : ℕ → ℝ → ℝ → List ℝ) (sizes : ℕ → ℝ → ℝ → Fin 6 → ℕ)
    (d : Fin 6 → ℕ) where
  /-- The matrix. -/
  matrix : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ
  /-- The backward error. -/
  δ : ℝ
  /-- The failure probability. -/
  φ : ℝ
  /-- The sizes are those of $(n, \delta, \varphi)$. -/
  sizes_eq : sizes (d 0) δ φ = d

/-- The four raw buffers of an input: the matrix words, the parameter words, uninitialized room for
the accumulator and the flag. -/
noncomputable def SchurData.buffers {words : ℕ → ℝ → ℝ → List ℝ}
    {sizes : ℕ → ℝ → ℝ → Fin 6 → ℕ} {d : Fin 6 → ℕ} (x : SchurData words sizes d) :
    Fin 4 → Buf ℝ :=
  ![(matrixWords x.matrix).map some, (words (d 0) x.δ x.φ).map some,
    List.replicate (2 * ((d 0 + 1) * (d 0 + 1))) none, [none]]

/-- **The admitted sizes** on the machine `Mch`: the natural literals up to the order $n + 1$ are
exact, and the sizes are those of some $0 < \delta \le 1$, $0 < \varphi \le 1$. -/
def SchurSizes (Mch : Machine ℝ) (sizes : ℕ → ℝ → ℝ → Fin 6 → ℕ) (d : Fin 6 → ℕ) : Prop :=
  IsExactNatLit id Mch (d 0 + 1) ∧
    ∃ δ φ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < φ ∧ φ ≤ 1 ∧ sizes (d 0) δ φ = d

/-- **The problem** of the dense Schur pipeline on the machine `Mch`: the four raw buffers of
`NLAlib.Schur.SchurData.buffers` at the admitted sizes `NLAlib.Schur.SchurSizes`. -/
noncomputable def schurPipelineProblem (Mch : Machine ℝ) (words : ℕ → ℝ → ℝ → List ℝ)
    (sizes : ℕ → ℝ → ℝ → Fin 6 → ℕ) (admitted : ∃ d, SchurSizes Mch sizes d) :
    Problem ℝ 6 4 where
  formats _ := .cell
  valid := SchurSizes Mch sizes
  Data := SchurData words sizes
  admissible _ x buffers := buffers = x.buffers
  admitted := admitted
  supply d hd := by
    obtain ⟨-, δ, φ, -, -, -, -, hs⟩ := hd
    exact ⟨⟨0, δ, φ, hs⟩, _, rfl⟩

/-- **The work (and span) of the pipeline** from the stages' work bounds $W_\bullet$: their sum
and the glue $64(N + 1)^2$, $N$ = `d 0 + 1`. -/
def schurPipelineWork (WNm WReg WRed WCore : (Fin 6 → ℕ) → ℕ) (d : Fin 6 → ℕ) : ℕ :=
  WNm d + WReg d + WRed d + WCore d + 64 * (d 0 + 2) ^ 2

/-- The payload words of the four supplied buffers. -/
def schurPipelineInputWords (d : Fin 6 → ℕ) : ℕ :=
  2 * ((d 0 + 1) * (d 0 + 1)) + (d 1 + d 2) + 2 * ((d 0 + 1) * (d 0 + 1)) + 1

/-- **The specification of the dense Schur pipeline**: the budget, scratch and resident memory of
the static count, the work and the span `NLAlib.Schur.schurPipelineWork`, and on every tape the
frame: the run writes only the matrix, the accumulator and the flag. -/
noncomputable def schurPipelineSpecification (Mch : Machine ℝ) (words : ℕ → ℝ → ℝ → List ℝ)
    (sizes : ℕ → ℝ → ℝ → Fin 6 → ℕ) (admitted : ∃ d, SchurSizes Mch sizes d)
    (Nm Reg Red Core : Impl SmallEigOp Tst) (WNm WReg WRed WCore : (Fin 6 → ℕ) → ℕ) :
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

/-- The static count of the pipeline program is at most the work
`NLAlib.Schur.schurPipelineWork` of the stages' static work bounds
(`NLAlib.Schur.size_stmtCost_schurPipelineWith_le`). -/
theorem size_staticCost_schurPipelineProgram_le {Nm Reg Red Core : Impl SmallEigOp Tst}
    {WNm WReg WRed WCore : (Fin 6 → ℕ) → ℕ}
    (hNm : ∀ d, Count.size (stmtCost Nm.body [d 0 + 1]) ≤ WNm d)
    (hReg : ∀ d, Count.size (stmtCost Reg.body [d 0 + 1, d 1]) ≤ WReg d)
    (hRed : ∀ d, Count.size (stmtCost Red.body [d 0 + 1]) ≤ WRed d)
    (hCore : ∀ d, Count.size (stmtCost Core.body [d 0 + 1, d 2, d 3, d 4, d 5]) ≤ WCore d)
    (d : Fin 6 → ℕ) :
    Count.size (staticCost (schurPipelineProgram Nm Reg Red Core) d) ≤
      schurPipelineWork WNm WReg WRed WCore d := sorry

/-- The initial payload of an input is `NLAlib.Schur.schurPipelineInputWords` when the words
have the sizes' count. -/
theorem schurPipelineProblem_initialBytes
    (hwords : ∀ n δ φ, (words n δ φ).length = sizes n δ φ 1 + sizes n δ φ 2) (d : Fin 6 → ℕ)
    (x : (schurPipelineProblem Mch words sizes admitted).Input d) :
    (schurPipelineProblem Mch words sizes admitted).initialBytes d x =
      schurPipelineInputWords d := by
  unfold Problem.initialBytes
  have hb : x.val.2 = x.val.1.buffers := x.property
  rw [hb]
  have hw : (words (d 0) x.val.1.δ x.val.1.φ).length = d 1 + d 2 := by
    rw [hwords, x.val.1.sizes_eq]
  simp [schurPipelineProblem, SchurData.buffers, List.ofFn_succ, schurPipelineInputWords, hw,
    Nat.add_assoc]

/-- The initial memory holds the input of the pipeline (`NLAlib.Schur.SchurPipelineInput`) at
the four supplied buffers. -/
theorem schurPipelineProblem_initial_input (d : Fin 6 → ℕ)
    (x : (schurPipelineProblem Mch words sizes admitted).Input d) :
    SchurPipelineInput (words (d 0) x.val.1.δ x.val.1.φ) (0, 0) (1, 0) (2, 0) (3, 0)
      x.val.1.matrix ((schurPipelineProblem Mch words sizes admitted).initial d x) := by
  have hb : x.val.2 = x.val.1.buffers := x.property
  have hs : ((schurPipelineProblem Mch words sizes admitted).initial d x).store =
      List.ofFn x.val.2 := rfl
  have hA := Problem.initial_readBlock (P := schurPipelineProblem Mch words sizes admitted) d x
    (0 : Fin 4) (xs := matrixWords x.val.1.matrix) (by rw [hb]; rfl)
  have hP := Problem.initial_readBlock (P := schurPipelineProblem Mch words sizes admitted) d x
    (1 : Fin 4) (xs := words (d 0) x.val.1.δ x.val.1.φ) (by rw [hb]; rfl)
  refine ⟨?_, ?_, ?_, by simpa [HoldsMatrix] using hA, by simpa using hP⟩
  · simp [Mem.Live, Problem.initial]
  · simp [hs, hb, Mem.Room, Store.len, SchurData.buffers, List.ofFn_succ]
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨Fp.disj_inBlock_of_ne (by omega), Fp.disj_inBlock_of_ne (by omega),
      Fp.disj_inBlock_of_ne (by omega)⟩, ⟨Fp.disj_inBlock_of_ne (by omega),
      Fp.disj_inBlock_of_ne (by omega)⟩, Fp.disj_inBlock_of_ne (by omega)⟩

/-- **The dense Schur pipeline as a canonical certificate, from component data**: the fixed
program `NLAlib.Schur.schurPipelineProgram` of any four stages, over the model
`NLAlib.SmallEig.smallEigModel` with the unit costs, given that it passes the storage discipline
(`ht`), terminates on every admitted input, interpretation of the model and tape writing only the
matrix, the accumulator and the flag (`hwp`), and the stages' static counts are at most
$W_\bullet$, succeeds within the static budget, scratch and memory, with work and span at most
`NLAlib.Schur.schurPipelineWork` of the $W_\bullet$.
Algorithm: dense-schur (run model) -/
noncomputable def schurPipelineAlgorithm (sU : ℕ) (Nm Reg Red Core : Impl SmallEigOp Tst)
    (WNm WReg WRed WCore : (Fin 6 → ℕ) → ℕ)
    (hNm : ∀ d, Count.size (stmtCost Nm.body [d 0 + 1]) ≤ WNm d)
    (hReg : ∀ d, Count.size (stmtCost Reg.body [d 0 + 1, d 1]) ≤ WReg d)
    (hRed : ∀ d, Count.size (stmtCost Red.body [d 0 + 1]) ≤ WRed d)
    (hCore : ∀ d, Count.size (stmtCost Core.body [d 0 + 1, d 2, d 3, d 4, d 5]) ≤ WCore d)
    (hwords : ∀ n δ φ, (words n δ φ).length = sizes n δ φ 1 + sizes n δ φ 2)
    (ht : (schurPipelineProgram Nm Reg Red Core).wellTyped smallEigResources
      (schurPipelineProblem Mch words sizes admitted).formats = true)
    (hwp : ∀ d, SchurSizes Mch sizes d →
      ∀ (x : (schurPipelineProblem Mch words sizes admitted).Input d) (I : Interp SmallEigOp Tst ℝ),
      (smallEigModel (schurPipelineProblem Mch words sizes admitted) Mch sU).contracts d x I →
      ∀ τ, Wp .total I τ (schurPipelineProgram Nm Reg Red Core).body
        (Program.environment (b := 4) d)
        (fun m => ((schurPipelineProblem Mch words sizes admitted).initial d x).store.EqOff
          (schurFp (d 0) (0, 0) (2, 0) (3, 0)) m.store)
        ((schurPipelineProblem Mch words sizes admitted).initial d x)) :
    Algorithm (smallEigModel (schurPipelineProblem Mch words sizes admitted) Mch sU)
      (schurPipelineSpecification Mch words sizes admitted Nm Reg Red Core WNm WReg WRed WCore) :=
  Algorithm.ofWp (schurPipelineProgram Nm Reg Red Core) ht
    (fun d hd x I hI τ => (hwp d hd x I hI τ).mono fun _ h _ _ => h)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun d _ => (smallEigResources_work _).trans_le
      (size_staticCost_schurPipelineProgram_le hNm hReg hRed hCore d))
    (fun d _ => (smallEigResources_span _).trans_le
      (size_staticCost_schurPipelineProgram_le hNm hReg hRed hCore d))
    (fun d _ x => by rw [schurPipelineProblem_initialBytes hwords]; exact le_rfl)

end Generic

/-! ### The instance -/

/-- The sizes of a run of the dense Schur solver at $(n, \delta, \varphi)$: $n$, the numbers of
regularizer and core words, the shift degree, the iteration cap and the leaf cap. -/
noncomputable def denseSchurSizes (n : ℕ) (δ φ : ℝ) : Fin 6 → ℕ :=
  ![n, (denseSchurRegParams n δ φ).length,
    (denseSchurThreshold n δ φ ::
      (denseSchurShQRParams n δ φ ++ denseSchurLeafParams n δ φ)).length,
    denseSchurDegree n δ φ, denseSchurCap n δ φ, denseSchurLeafCap n δ φ]

/-- **The problem** of the dense Schur solver on the machine `Mch`. -/
noncomputable def denseSchurProblem (Mch : Machine ℝ)
    (admitted : ∃ d, SchurSizes Mch denseSchurSizes d) : Problem ℝ 6 4 :=
  schurPipelineProblem Mch denseSchurParams denseSchurSizes admitted

/-- **The work (and span) of the dense Schur solver**: `NLAlib.Schur.schurPipelineWork` of the
static counts of its four stages (the Frobenius norm, the Ginibre regularizer, the reduction with
its accumulated unitary, the rounded shifted QR core with the `SmallEig` leaf) at their
dimensions, each at most a polynomial of its sizes (`NLAlib.Schur.denseSchur_work_le`). -/
noncomputable def denseSchurWork (sG : ℕ) (d : Fin 6 → ℕ) : ℕ :=
  schurPipelineWork
    (fun d => Count.size (stmtCost (frobNormStage (O := SmallEigOp) (Q := Tst)).body [d 0 + 1]))
    (fun d => Count.size (stmtCost (ginibrePerturb (O := SmallEigOp) (Q := Tst) sG).body
      [d 0 + 1, d 1]))
    (fun d => Count.size (stmtCost (hessenbergReduceQ (O := SmallEigOp) (Q := Tst)).body [d 0 + 1]))
    (fun d => Count.size (stmtCost (roundedShQRSchur (O := SmallEigOp) (Q := Tst) sG).body
      [d 0 + 1, d 2, d 3, d 4, d 5])) d

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
(`NLAlib.Schur.denseSchur_terminates`). -/
theorem denseSchurProgram_wp {Mch : Machine ℝ} {admitted : ∃ d, SchurSizes Mch denseSchurSizes d}
    {sU sG : ℕ} {d : Fin 6 → ℕ} (hd : SchurSizes Mch denseSchurSizes d)
    (x : (denseSchurProblem Mch admitted).Input d) {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (denseSchurProblem Mch admitted) Mch sU).contracts d x I) (τ : Tape ℝ) :
    Wp .total I τ (schurPipelineProgram frobNormStage (ginibrePerturb sG) hessenbergReduceQ
        (roundedShQRSchur sG)).body (Program.environment (b := 4) d)
      (fun m => ((denseSchurProblem Mch admitted).initial d x).store.EqOff
        (schurFp (d 0) (0, 0) (2, 0) (3, 0)) m.store)
      ((denseSchurProblem Mch admitted).initial d x) := sorry

/-- The parameter words have the sizes' count. -/
theorem length_denseSchurParams (n : ℕ) (δ φ : ℝ) :
    (denseSchurParams n δ φ).length = denseSchurSizes n δ φ 1 + denseSchurSizes n δ φ 2 := by
  simp [denseSchurParams, denseSchurParamsWith, denseSchurSizes]

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
      (schurPipelineSpecification Mch denseSchurParams denseSchurSizes admitted frobNormStage
        (ginibrePerturb sG) hessenbergReduceQ (roundedShQRSchur sG)
        (fun d => Count.size (stmtCost (frobNormStage (O := SmallEigOp) (Q := Tst)).body
          [d 0 + 1]))
        (fun d => Count.size (stmtCost (ginibrePerturb (O := SmallEigOp) (Q := Tst) sG).body
          [d 0 + 1, d 1]))
        (fun d => Count.size (stmtCost (hessenbergReduceQ (O := SmallEigOp) (Q := Tst)).body
          [d 0 + 1]))
        (fun d => Count.size (stmtCost (roundedShQRSchur (O := SmallEigOp) (Q := Tst) sG).body
          [d 0 + 1, d 2, d 3, d 4, d 5]))) :=
  schurPipelineAlgorithm sU _ _ _ _ _ _ _ _ (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => le_rfl) length_denseSchurParams (denseSchurProgram_wellTyped sG)
    (fun _ hd x _ hI τ => denseSchurProgram_wp hd x hI τ)

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
    P.real {ω | ¬ (schurPipelineSpecification Mch denseSchurParams denseSchurSizes admitted
        frobNormStage (ginibrePerturb sG) hessenbergReduceQ (roundedShQRSchur sG)
        (fun d => Count.size (stmtCost (frobNormStage (O := SmallEigOp) (Q := Tst)).body
          [d 0 + 1]))
        (fun d => Count.size (stmtCost (ginibrePerturb (O := SmallEigOp) (Q := Tst) sG).body
          [d 0 + 1, d 1]))
        (fun d => Count.size (stmtCost (hessenbergReduceQ (O := SmallEigOp) (Q := Tst)).body
          [d 0 + 1]))
        (fun d => Count.size (stmtCost (roundedShQRSchur (O := SmallEigOp) (Q := Tst) sG).body
          [d 0 + 1, d 2, d 3, d 4, d 5]))).Accepts smallEigResources d x
      (exec (denseSchurAlgorithm Mch admitted sU sG).program I smallEigResources
        (denseSchurProblem Mch admitted).formats (ξ ω) d
        ((denseSchurProblem Mch admitted).initial d x))
      fun _ m => ((denseSchurProblem Mch admitted).initial d x).store.EqOff
          (schurFp (d 0) (0, 0) (2, 0) (3, 0)) m.store ∧
        SchurOutput (0, 0) (2, 0) (3, 0) x.val.1.matrix x.val.1.δ
          (58 * denseSchurRotations (d 0) x.val.1.δ x.val.1.φ * u) m} ≤ x.val.1.φ := by
  have := hξ.isProbabilityMeasure
  obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
  have hin := schurPipelineProblem_initial_input (admitted := admitted) d x
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
  have hsz := x.val.1.sizes_eq
  refine hω (wp_frame ?_ ?_ hl5 hW)
  · have h := fun i => (congrFun hsz i).symm
    simp [Program.environment, IExp.evalList, IExp.eval, denseSchurDims, denseSchurDimsWith,
      List.ofFn_succ, h 1, h 2, h 3, h 4, h 5, denseSchurSizes]
  · simp [Program.environment, Operand.evalList, Operand.eval, IExp.eval, List.ofFn_succ]

end NLAlib.Schur
