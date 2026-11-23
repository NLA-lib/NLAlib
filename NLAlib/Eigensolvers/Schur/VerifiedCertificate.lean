/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Schur.VerifiedDense
public import NLAlib.Eigensolvers.Schur.Certificate

/-!
# The verified dense Schur solver as a canonical certificate

The verified dense Schur solver (`NLAlib.Schur.verifiedSchur`) over the model of the
small-eigenvalue solver (`NLAlib.SmallEig.smallEigModel`) on a machine `Mch` with the standard
model at $\boldsymbol{u}$ is a canonical certificate (`NLAlib.Ops.Algorithm`) whose every-tape
claim (`good`) is the **flag-conditional Schur form**: on every admitted input, interpretation of
the model and tape, the run writes only the matrix, the accumulator and the flag, and if it stores
the flag $0$ then $\widehat{\mathbf{T}}$ is upper triangular and
$\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le
\delta\|\mathbf{A}\|_2$. The admitted inputs are those whose $(\delta, \varphi)$ the precision
$\boldsymbol{u}$ of the machine supports ($\boldsymbol{u} \le$ `NLAlib.Schur.uVerifiedSchur`).
The work is the dense solver's and $O(n^3)$ for the check.

## Main definitions

* `NLAlib.Schur.verifiedSchurProgram`, `NLAlib.Schur.verifiedSchurProblem`,
  `NLAlib.Schur.verifiedSchurWork`, `NLAlib.Schur.verifiedSchurSpecification`,
  `NLAlib.Schur.verifiedSchurAlgorithm`.

## Main results

* `NLAlib.Schur.verifiedSchur_work_le`: the operation count.
* `NLAlib.Schur.verifiedSchur_algorithm_measureReal_not_accepts_le`: the flag is $0$ except with
  probability $\varphi$, on one counted run.
-/

@[expose] public section

namespace NLAlib.Schur

open Ops SmallEig ShiftedQR MeasureTheory ProbabilityTheory
open scoped Matrix

/-- The sizes of a run of the verified dense Schur solver at $(n, \delta, \varphi)$: those of the
dense solver at the internal backward error. -/
noncomputable def verifiedSchurSizes (n : ℕ) (δ φ : ℝ) : Fin 6 → ℕ :=
  denseSchurSizes n (verifiedSchurDelta n δ) φ

/-- **The admitted sizes** of the verified dense Schur solver on the machine `Mch` at the unit
roundoff $\boldsymbol{u}$: the natural literals up to the order are exact and the sizes are those
of some $0 < \delta \le 1$, $0 < \varphi \le 1$ that the precision supports. -/
def VerifiedSchurSizes (Mch : Machine ℝ) (u : ℝ) (d : Fin 6 → ℕ) : Prop :=
  IsExactNatLit id Mch (d 0 + 1) ∧ ∃ δ φ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < φ ∧ φ ≤ 1 ∧
    u ≤ uVerifiedSchur (d 0) δ φ ∧ verifiedSchurSizes (d 0) δ φ = d

/-- **The problem** of the verified dense Schur solver: the four raw buffers of
`NLAlib.Schur.SchurData.buffers` with the words `NLAlib.Schur.verifiedSchurParams`, at an input
$(\mathbf{A}, \delta, \varphi)$ with $0 < \delta \le 1$, $0 < \varphi \le 1$ and
$\boldsymbol{u} \le$ `NLAlib.Schur.uVerifiedSchur`. -/
noncomputable def verifiedSchurProblem (Mch : Machine ℝ) (u : ℝ)
    (admitted : ∃ d, VerifiedSchurSizes Mch u d) : Problem ℝ 6 4 where
  formats _ := .cell
  valid := VerifiedSchurSizes Mch u
  Data := SchurData (verifiedSchurParams u) verifiedSchurSizes
  admissible d x buffers := buffers = x.buffers ∧ 0 < x.δ ∧ x.δ ≤ 1 ∧ 0 < x.φ ∧ x.φ ≤ 1 ∧
    u ≤ uVerifiedSchur (d 0) x.δ x.φ
  admitted := admitted
  supply d hd := by
    obtain ⟨-, δ, φ, hδ, hδ1, hφ, hφ1, hu, hs⟩ := hd
    exact ⟨⟨0, δ, φ, hs⟩, _, rfl, hδ, hδ1, hφ, hφ1, hu⟩

/-- **The verified dense Schur program** at the order `d 0 + 1` and the dimensions `d 1`, …,
`d 5` on the four supplied buffers. -/
def verifiedSchurProgram (sG : ℕ) : Program SmallEigOp Tst 6 4 :=
  ⟨.frame [.var 0 + .const 1, .var 1, .var 2, .var 3, .var 4, .var 5]
    [⟨0, .var 6⟩, ⟨1, .var 7⟩, ⟨0, .var 6⟩, ⟨2, .var 8⟩, ⟨3, .var 9⟩]
    (verifiedSchur (O := SmallEigOp) (Q := Tst) sG).body⟩

/-- **The work (and span) of the verified dense Schur solver** at the sizes
$(n, n_r, n_q, k, F, T)$ = `d`: the dense solver's
$384547(n + 1)^3(k + 1)^4(n_r + n_q + 1)(F + 1)(T + 1)^2$ (`NLAlib.Schur.denseSchur_work_le`),
the check's $1619(n + 1)^3$, the copy's $32(n + 1)^2$ and $128$ for the frames. -/
def verifiedSchurWork (d : Fin 6 → ℕ) : ℕ :=
  384547 * (d 0 + 1) ^ 3 * (d 3 + 1) ^ 4 * (d 1 + d 2 + 1) * (d 4 + 1) * (d 5 + 1) ^ 2 +
    1619 * (d 0 + 1) ^ 3 + 32 * (d 0 + 1) ^ 2 + 128

/-- The payload words of the four supplied buffers. -/
def verifiedSchurInputWords (d : Fin 6 → ℕ) : ℕ :=
  2 * ((d 0 + 1) * (d 0 + 1)) + (d 1 + d 2 + 2) + 2 * ((d 0 + 1) * (d 0 + 1)) + 1

/-- **The specification of the verified dense Schur solver**: the static budget, scratch and
memory, the work and span `NLAlib.Schur.verifiedSchurWork`, and on every tape the frame and the
flag-conditional Schur form: if the flag is $0$, the stored $\widehat{\mathbf{T}}$ is upper
triangular, $\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf
H}\|_2 \le \delta\|\mathbf{A}\|_2$ and $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} -
\mathbf{I}\|_2 \le 58R\boldsymbol{u}$, $R$ the rotation count at the internal backward error. -/
noncomputable def verifiedSchurSpecification (Mch : Machine ℝ) (u : ℝ)
    (admitted : ∃ d, VerifiedSchurSizes Mch u d) (sG : ℕ) :
    Specification SmallEigOp Tst (verifiedSchurProblem Mch u admitted) where
  budget := staticCost (verifiedSchurProgram sG)
  scratch := staticPeak smallEigResources (verifiedSchurProgram sG)
  work := verifiedSchurWork
  span := verifiedSchurWork
  memory d := verifiedSchurInputWords d + staticPeak smallEigResources (verifiedSchurProgram sG) d
  good d x _ _ m := ((verifiedSchurProblem Mch u admitted).initial d x).store.EqOff
      (schurFp (d 0) (0, 0) (2, 0) (3, 0)) m.store ∧
    (m.store.get 3 0 = some 0 → SchurOutput (0, 0) (2, 0) (3, 0) x.val.1.matrix x.val.1.δ
      (58 * denseSchurRotations (d 0) (verifiedSchurDelta (d 0) x.val.1.δ) x.val.1.φ * u) m)

/-- **The operation count of the verified dense Schur solver** (on every tape): the instrumented
static count of `NLAlib.Schur.verifiedSchur` at the order $n + 1$, $n_r$ regularizer words, $n_q$
core words, the shift degree $k$, the iteration cap $F$, the leaf cap $T$ and zero offsets is at
most the dense solver's $384547(n + 1)^3(k + 1)^4(n_r + n_q + 1)(F + 1)(T + 1)^2$
(`NLAlib.Schur.denseSchur_work_le`) and $1619(n + 1)^3 + 32(n + 1)^2 + 64$ for the copy and the
check (`NLAlib.Schur.size_stmtCost_verifiedSchurWith_le`). -/
theorem verifiedSchur_work_le {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O]
    [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q] (sG n nr nq k F T : ℕ) :
    Count.size (stmtCost (verifiedSchur (O := O) (Q := Q) sG).body.instrument
        [n + 1, nr, nq, k, F, T, 0, 0, 0, 0, 0]) ≤
      384547 * (n + 1) ^ 3 * (k + 1) ^ 4 * (nr + nq + 1) * (F + 1) * (T + 1) ^ 2 +
        1619 * (n + 1) ^ 3 + 32 * (n + 1) ^ 2 + 64 := by
  have h1 := size_stmtCost_verifiedSchurWith_le (denseSchur (O := O) (Q := Q) sG) n nr nq k F T
  have h2 := denseSchur_work_le (O := O) (Q := Q) sG n nr nq k F T
  unfold verifiedSchur
  omega

/-- The initial memory of an input holds the input of the verified solver at the four supplied
buffers. -/
theorem verifiedSchurProblem_initial_input {Mch : Machine ℝ} {u : ℝ}
    {admitted : ∃ d, VerifiedSchurSizes Mch u d} (d : Fin 6 → ℕ)
    (x : (verifiedSchurProblem Mch u admitted).Input d) :
    SchurPipelineInput (verifiedSchurParams u (d 0) x.val.1.δ x.val.1.φ) (0, 0) (1, 0) (2, 0)
      (3, 0) x.val.1.matrix ((verifiedSchurProblem Mch u admitted).initial d x) := by
  have hb : x.val.2 = x.val.1.buffers := x.property.1
  have hs : ((verifiedSchurProblem Mch u admitted).initial d x).store = List.ofFn x.val.2 := rfl
  have hA := Problem.initial_readBlock (P := verifiedSchurProblem Mch u admitted) d x
    (0 : Fin 4) (xs := matrixWords x.val.1.matrix) (by rw [hb]; rfl)
  have hP := Problem.initial_readBlock (P := verifiedSchurProblem Mch u admitted) d x
    (1 : Fin 4) (xs := verifiedSchurParams u (d 0) x.val.1.δ x.val.1.φ) (by rw [hb]; rfl)
  refine ⟨?_, ?_, ?_, by simpa [HoldsMatrix] using hA, by simpa using hP⟩
  · simp [Mem.Live, Problem.initial]
  · simp [hs, hb, Mem.Room, Store.len, SchurData.buffers, List.ofFn_succ]
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true]
    exact ⟨⟨Fp.disj_inBlock_of_ne (by omega), Fp.disj_inBlock_of_ne (by omega),
      Fp.disj_inBlock_of_ne (by omega)⟩, ⟨Fp.disj_inBlock_of_ne (by omega),
      Fp.disj_inBlock_of_ne (by omega)⟩, Fp.disj_inBlock_of_ne (by omega)⟩

/-- The initial payload of an input is `NLAlib.Schur.verifiedSchurInputWords`. -/
theorem verifiedSchurProblem_initialBytes {Mch : Machine ℝ} {u : ℝ}
    {admitted : ∃ d, VerifiedSchurSizes Mch u d} (d : Fin 6 → ℕ)
    (x : (verifiedSchurProblem Mch u admitted).Input d) :
    (verifiedSchurProblem Mch u admitted).initialBytes d x = verifiedSchurInputWords d := by
  unfold Problem.initialBytes
  have hb : x.val.2 = x.val.1.buffers := x.property.1
  rw [hb]
  have hl : ∀ n δ φ, (verifiedSchurParams u n δ φ).length =
      verifiedSchurSizes n δ φ 1 + verifiedSchurSizes n δ φ 2 + 2 := fun n δ φ => by
    simp [verifiedSchurParams, verifiedSchurSizes, denseSchurSizes, denseSchurParams,
      denseSchurParamsWith]
    omega
  have hw : (verifiedSchurParams u (d 0) x.val.1.δ x.val.1.φ).length = d 1 + d 2 + 2 := by
    rw [hl, x.val.1.sizes_eq]
  simp [verifiedSchurProblem, SchurData.buffers, List.ofFn_succ, verifiedSchurInputWords, hw,
    Nat.add_assoc]

-- The kernel evaluates the discipline over the whole tree; its recursion is deep.
set_option maxRecDepth 100000 in
/-- The verified dense Schur program passes the storage discipline of the costs. -/
theorem verifiedSchurProgram_wellTyped (sG : ℕ) {Mch : Machine ℝ} {u : ℝ}
    {admitted : ∃ d, VerifiedSchurSizes Mch u d} :
    (verifiedSchurProgram sG).wellTyped smallEigResources
      (verifiedSchurProblem Mch u admitted).formats = true := by
  kernel_rfl

/-- The static count of the verified dense Schur program, its frame included, is at most
`NLAlib.Schur.verifiedSchurWork`. -/
theorem size_staticCost_verifiedSchurProgram_le (sG : ℕ) (d : Fin 6 → ℕ) :
    Count.size (staticCost (verifiedSchurProgram sG) d) ≤ verifiedSchurWork d := by
  have he : (Program.environment (b := 4) d).idx = [d 0, d 1, d 2, d 3, d 4, d 5, 0, 0, 0, 0] :=
    rfl
  have h := verifiedSchur_work_le (O := SmallEigOp) (Q := Tst) sG (d 0) (d 1) (d 2) (d 3) (d 4)
    (d 5)
  simp only [staticCost, verifiedSchurProgram, he, Stmt.instrument, stmtCost, tally,
    indexBookkeeping, operandBookkeeping, IExp.bookkeeping, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, useCost, IExp.evalList, IExp.eval,
    List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.map_some, Option.getD_some, map_add, map_zero, Count.one, size_single]
  unfold verifiedSchurWork
  omega

/-- **The flag-conditional Schur form on every tape**: on a machine `Mch` with the standard model
at $\boldsymbol{u}$, for every admitted input, interpretation of the model and tape, the verified
program terminates, writes only the matrix, the accumulator and the flag, and a flag $0$ certifies
the Schur form (`NLAlib.Schur.verifiedSchur_writes`). -/
theorem verifiedSchurProgram_wp {Mch : Machine ℝ} {u : ℝ} (hM : StdModel u id Mch)
    {admitted : ∃ d, VerifiedSchurSizes Mch u d} {sU sG : ℕ} {d : Fin 6 → ℕ}
    (hd : VerifiedSchurSizes Mch u d) (x : (verifiedSchurProblem Mch u admitted).Input d)
    {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (verifiedSchurProblem Mch u admitted) Mch sU).contracts d x I)
    (τ : Tape ℝ) :
    Wp .total I τ (verifiedSchurProgram sG).body (Program.environment (b := 4) d)
      (fun m => ∀ c, c ≤ (verifiedSchurSpecification Mch u admitted sG).budget d →
        (verifiedSchurSpecification Mch u admitted sG).good d x τ c m)
      ((verifiedSchurProblem Mch u admitted).initial d x) := by
  obtain ⟨hNat, -⟩ := hd
  obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
  obtain ⟨-, hδ, hδ1, -, -, hu⟩ := x.property
  have hin := verifiedSchurProblem_initial_input (admitted := admitted) d x
  have hl5 : ((verifiedSchurProblem Mch u admitted).initial d x).Live
      [(0, 0), (1, 0), (0, 0), (2, 0), (3, 0)] := fun y hy => hin.1 y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp)
  have hsz := x.val.1.sizes_eq
  refine wp_frame ?_ ?_ hl5 (Wp.mono (verifiedSchur_writes (O := SmallEigOp) (Q := Tst) (sG := sG)
    hS hM hL hNat hQ hC hSmp hDisk hδ hδ1 hu hin τ) fun _ h _ _ => ⟨h.1, h.2.2.2⟩)
  · have h := fun i => (congrFun hsz i).symm
    simp [Program.environment, IExp.evalList, IExp.eval, denseSchurDims, denseSchurDimsWith,
      List.ofFn_succ, h 1, h 2, h 3, h 4, h 5, verifiedSchurSizes, denseSchurSizes]
  · simp [Program.environment, Operand.evalList, Operand.eval, IExp.eval, List.ofFn_succ]

/-- **The verified dense Schur solver as a canonical certificate**: the fixed program
`NLAlib.Schur.verifiedSchurProgram`, over the model `NLAlib.SmallEig.smallEigModel` (no oracle)
with the unit costs on a machine with the standard model at $\boldsymbol{u}$, succeeds on every
admitted input, interpretation of the model and tape, within the static budget, scratch and
memory, with work and span at most `NLAlib.Schur.verifiedSchurWork`, writing only the matrix, the
accumulator and the flag, and with the **flag-conditional Schur form** as its every-tape claim:
a flag $0$ certifies $\widehat{\mathbf{T}}$ upper triangular,
$\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le
\delta\|\mathbf{A}\|_2$ and the orthogonality bound. The flag is $0$ with probability at least
$1 - \varphi$ (`NLAlib.Schur.verifiedSchur_algorithm_measureReal_not_accepts_le`).
Algorithm: verified-schur (run model) -/
noncomputable def verifiedSchurAlgorithm (Mch : Machine ℝ) {u : ℝ} (hM : StdModel u id Mch)
    (admitted : ∃ d, VerifiedSchurSizes Mch u d) (sU sG : ℕ) :
    Algorithm (smallEigModel (verifiedSchurProblem Mch u admitted) Mch sU)
      (verifiedSchurSpecification Mch u admitted sG) :=
  Algorithm.ofWp (verifiedSchurProgram sG) (verifiedSchurProgram_wellTyped sG)
    (fun _ hd x _ hI τ => verifiedSchurProgram_wp hM hd x hI τ)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun d _ => (smallEigResources_work _).trans_le (size_staticCost_verifiedSchurProgram_le sG d))
    (fun d _ => (smallEigResources_span _).trans_le (size_staticCost_verifiedSchurProgram_le sG d))
    (fun d _ x => by rw [verifiedSchurProblem_initialBytes]; exact le_rfl)

/-- **The verified dense Schur solver, on one run.** Let the machine `Mch` have the standard model
at $\boldsymbol{u}$; let the tape $\xi$ have the stream laws `law`, with `law` $s_U$ uniform on
$[0, 1]$ and `law` $s_G$ the standard real Gaussian law. Let `d` be admitted and the input `x`
hold a complex $\mathbf{A}$ of order $n + 1$, $0 < \delta \le 1$, $0 < \varphi \le 1$ with
$\boldsymbol{u} \le \boldsymbol{u}_0$. Let `I` meet the model, be measurable and read the tape
only in its windows. Then
$$\mathbb{P}\bigl[\mathsf{verifiedSchurAlgorithm}(\mathbf{A}) \text{ fails, exceeds its budget,
  scratch, memory, work or span, writes outside } \mathbf{A}, \widehat{\mathbf{U}} \text{ and the
  flag, or stores no flag } 0 \text{ with a Schur output of } \mathbf{A}\bigr] \le \varphi\,,$$
on one counted run. On every tape a flag $0$ certifies the Schur form (the specification's
`good`). Here $\boldsymbol{u}_0$ is `NLAlib.Schur.uVerifiedSchur`.
[BanksGarzaVargasSrivastava2022, Theorem 1.4] with [BanksGarzaVargasSrivastava2025, Theorem 1.1]
for the solver; the a posteriori check has no printed source.
Result: verified-schur-certificate -/
theorem verifiedSchur_algorithm_measureReal_not_accepts_le {Mch : Machine ℝ} {u : ℝ}
    (hM : StdModel u id Mch) {admitted : ∃ d, VerifiedSchurSizes Mch u d}
    {law : ℕ → Measure ℝ} {sU sG : ℕ} (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {d : Fin 6 → ℕ} (hd : VerifiedSchurSizes Mch u d)
    (x : (verifiedSchurProblem Mch u admitted).Input d) {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (verifiedSchurProblem Mch u admitted) Mch sU).contracts d x I)
    (hIm : I.IsMeasurable) {win : SmallEigOp → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ (verifiedSchurSpecification Mch u admitted sG).Accepts smallEigResources d x
      (exec (verifiedSchurAlgorithm Mch hM admitted sU sG).program I smallEigResources
        (verifiedSchurProblem Mch u admitted).formats (ξ ω) d
        ((verifiedSchurProblem Mch u admitted).initial d x))
      fun _ m => ((verifiedSchurProblem Mch u admitted).initial d x).store.EqOff
          (schurFp (d 0) (0, 0) (2, 0) (3, 0)) m.store ∧
        SchurOutput (0, 0) (2, 0) (3, 0) x.val.1.matrix x.val.1.δ
          (58 * denseSchurRotations (d 0) (verifiedSchurDelta (d 0) x.val.1.δ) x.val.1.φ * u)
          m} ≤ x.val.1.φ := by
  have := hξ.isProbabilityMeasure
  obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
  obtain ⟨-, hδ, hδ1, hφ, hφ1, hu⟩ := x.property
  have hin := verifiedSchurProblem_initial_input (admitted := admitted) d x
  have hT := verifiedSchur_measureReal_not_schur_le (O := SmallEigOp) (Q := Tst) (sG := sG) hS hM
    hL hd.1 hQ hC hIm hloc hSmp hDisk hU hG hδ hδ1 hφ hφ1 hu hin hξ
  refine (verifiedSchurAlgorithm Mch hM admitted sU sG).measureReal_not_accepts_le_of_wp hd x
    I hI P ξ _ ?_
  refine (measureReal_mono ?_).trans hT
  intro ω hω hW
  have hl5 : ((verifiedSchurProblem Mch u admitted).initial d x).Live
      [(0, 0), (1, 0), (0, 0), (2, 0), (3, 0)] := fun y hy => hin.1 y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp)
  have hsz := x.val.1.sizes_eq
  refine hω (wp_frame ?_ ?_ hl5 (hW.mono le_rfl fun m _ h => (h.mono (by
    obtain ⟨-, hd1, -⟩ := verifiedSchur_params_basic (n := d 0) hδ hδ1 hu
    exact hd1) le_rfl)))
  · have h := fun i => (congrFun hsz i).symm
    simp [Program.environment, IExp.evalList, IExp.eval, denseSchurDims, denseSchurDimsWith,
      List.ofFn_succ, h 1, h 2, h 3, h 4, h 5, verifiedSchurSizes, denseSchurSizes]
  · simp [Program.environment, Operand.evalList, Operand.eval, IExp.eval, List.ofFn_succ]

end NLAlib.Schur
