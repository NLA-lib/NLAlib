/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedCertificate
public import NLAlib.Eigensolvers.SmallEig.Theorems

/-!
# The small-eigenvalue solver as a canonical certificate

The headline theorems of `NLAlib.Eigensolvers.SmallEig.Theorems` state the probability of a
correct output and the static count of `NLAlib.SmallEig.smallEigProg` separately. This file
states them for **one run**: the program, fixed before every size and input, is a canonical
certificate (`NLAlib.Ops.Algorithm`) over a jointly realized access model, with explicit work and
span polynomials; and the probability that this counted run fails, exceeds a resource bound of
the specification, or fails to store the spectrum of a nearby matrix is at most $\varphi$.

The model has no oracle: scalar arithmetic is the function of a machine `Mch` (its standard model
at $\boldsymbol{u}$ is a hypothesis of the probability statement only); dimension literals,
comparisons and index conversion are exact; a draw stores the next entry of its stream; the polar
disk sampler is exact on the stream $s_U$. Every contract is a function, so the model is realized
by the interpretation of these functions. Every primitive, query and structural instruction costs
one unit of work and span and no workspace, so the work and the span are the number of
instructions of the static count: an explicit polynomial in the sizes.

The same signature and contracts serve every program over scalar arithmetic, index literals,
draws and the polar sampler (`NLAlib.SmallEig.smallEigModel` takes any problem); the rounded
shifted QR algorithm with the small-eigenvalue program uses them too
(`NLAlib.Eigensolvers.ShiftedQR.RoundedSmallEigCertificate`).

The every-tape output claim (`NLAlib.Ops.Specification.good`) is the frame and the stored output:
the run writes only the output, and the $2(n + 1)$ output words are stored. No accuracy claim
holds on every tape (on a tape whose perturbation has a tiny gap the decoupling may stop early).
The spectrum claim is the postcondition of `NLAlib.Ops.Specification.Accepts` in
`NLAlib.SmallEig.smallEig_algorithm_measureReal_not_accepts_le`, bounded through the
probabilistic program logic (`NLAlib.Ops.Algorithm.measureReal_not_accepts_le_of_wp`).

## Main definitions

* `NLAlib.SmallEig.SmallEigOp`, `NLAlib.SmallEig.smallEigModel`,
  `NLAlib.SmallEig.smallEigResources`: the signature, the access model and the unit costs.
* `NLAlib.SmallEig.smallEigProgram`, `NLAlib.SmallEig.smallEigProblem`: the program and the
  problem.
* `NLAlib.SmallEig.smallEigWork`: the explicit work and span polynomial.
* `NLAlib.SmallEig.smallEigAlgorithm`: the certificate.

## Main results

* `NLAlib.SmallEig.confined_smallEigModel`, `NLAlib.SmallEig.uniform_smallEigModel`,
  `NLAlib.SmallEig.charged_smallEigModel`: the model is confined, uniform and charged.
* `NLAlib.SmallEig.smallEigModel_laws`: the laws the program proofs use.
* `NLAlib.SmallEig.smallEigProgram_work_le`: the work and span of every run.
* `NLAlib.SmallEig.smallEig_algorithm_measureReal_not_accepts_le`: the headline, on one run.
-/

@[expose] public section

namespace NLAlib.SmallEig

open Ops ShiftedQR MeasureTheory ProbabilityTheory
open scoped Matrix

/-! ### The signature, the contracts and the costs -/

/-- The operations of the small-eigenvalue solver: scalar arithmetic, index literals, draws from
the tape streams and the polar disk sampler. No eigenvalue kernel. -/
abbrev SmallEigOp := ScalarOp ⊕ (IndexOp ⊕ (SampleOp ⊕ DiskSampleOp))

instance : Has IndexOp SmallEigOp := Has.sumRight _ _ _ inferInstance

instance : Has SampleOp SmallEigOp := Has.sumRight _ _ _ (Has.sumRight _ _ _ inferInstance)

instance : Has DiskSampleOp SmallEigOp := Has.sumRight _ _ _ (Has.sumRight _ _ _ inferInstance)

/-- An exact polar disk sampler given as the block function `NLAlib.ShiftedQR.polarDiskFn` meets
the relational contract of the sampler. -/
theorem isPolarDiskSampler_of_isFn {O Q : Type} [Has DiskSampleOp O] {s : ℕ} {I : Interp O Q ℝ}
    (h : I.IsFn .total (Has.inj DiskSampleOp.polar) (polarDiskFn s) AnyOperands) :
    IsPolarDiskSampler s I := by
  refine h.meets_rel (fun _ _ _ h => h) rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
  intro d w xs m ins outs _ _ _ _ _
  refine ⟨_, rfl, rfl, ?_⟩
  rintro R rfl
  rfl

/-- The block functions of the model: the machine's arithmetic and literals, the draws of the
tape streams and the exact polar sampler on the stream `sU`. -/
noncomputable def smallEigFunctions (Mch : Machine ℝ) (sU : ℕ) : SmallEigOp → BlockFn ℝ
  | .inl o => Mch.fn o
  | .inr (.inl _) => Mch.indexFn
  | .inr (.inr (.inl (.draw s))) => BlockFn.draw s
  | .inr (.inr (.inr .polar)) => polarDiskFn sU

/-- The realizing interpretation: the block functions of `NLAlib.SmallEig.smallEigFunctions`,
exact comparisons and index conversion. -/
noncomputable def smallEigInterp (Mch : Machine ℝ) (sU : ℕ) : Interp SmallEigOp Tst ℝ where
  call o := (Interp.ofFns (Tst := Tst) (smallEigFunctions Mch sU)).call o
  test := cmpInterp.test
  index := cmpInterp.index

/-- Operand formats count real words. -/
def smallEigSignature : SmallEigOp → OperandSignature
  | .inl (.lit _) | .inr (.inl _) | .inr (.inr (.inl _)) => ⟨[], [.cell]⟩
  | .inl .add | .inl .sub | .inl .mul | .inl .div => ⟨[.cell, .cell], [.cell]⟩
  | .inl .neg | .inl .sqrt | .inl .copy => ⟨[.cell], [.cell]⟩
  | .inr (.inr (.inr _)) => ⟨[.cell], [.cell]⟩

/-- **The unit costs**: every primitive, query and structural instruction costs one unit of work
and span and no workspace. -/
def smallEigResources : ResourceModel SmallEigOp Tst where
  formats := [.cell]
  operation := smallEigSignature
  testInputs q := match q with | .inl c => c.lens.map (fun _ => .cell) | .inr _ => []
  indexInputs q := match q with | .inl _ => [] | .inr _ => [.cell]
  workspace _ _ := 0
  queryWorkspace _ _ := 0
  operationWork _ _ := 1
  operationSpan _ _ := 1
  queryWork _ _ := 1
  querySpan _ _ := 1
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le _ _ := le_rfl
  core_span_le _ _ := le_rfl

/-- Under the unit costs the work of a count is its number of instructions. -/
theorem smallEigResources_work (c : Count (SmallEigOp ⊕ Bookkeeping) Tst) :
    smallEigResources.work c = Count.size c := by
  have h : (Sum.elim (Sum.elim smallEigResources.operationWork smallEigResources.coreWork)
      smallEigResources.queryWork : (SmallEigOp ⊕ Bookkeeping) ⊕ Tst → List ℕ → ℕ) =
      fun _ _ => 1 := by
    funext k ds
    rcases k with (o | o) | q <;> rfl
  simp only [ResourceModel.work, Count.size, h]

/-- Under the unit costs the span of a count is its number of instructions. -/
theorem smallEigResources_span (c : Count (SmallEigOp ⊕ Bookkeeping) Tst) :
    smallEigResources.span c = Count.size c := by
  have h : (Sum.elim (Sum.elim smallEigResources.operationSpan smallEigResources.coreSpan)
      smallEigResources.querySpan : (SmallEigOp ⊕ Bookkeeping) ⊕ Tst → List ℕ → ℕ) =
      fun _ _ => 1 := by
    funext k ds
    rcases k with (o | o) | q <;> rfl
  simp only [ResourceModel.span, Count.size, h]

/-- **The access model** of the small-eigenvalue solver, for any problem `P`: the functional
contracts of `NLAlib.SmallEig.smallEigFunctions` (the machine `Mch`, the draws, the exact polar
sampler on the stream `sU`), exact comparisons and index conversion, and the unit costs. It is
realized by `NLAlib.SmallEig.smallEigInterp`. -/
noncomputable def smallEigModel {r b : ℕ} (P : Problem ℝ r b) (Mch : Machine ℝ) (sU : ℕ) :
    AccessModel SmallEigOp Tst P where
  word := 0
  operation _ _ o := (smallEigFunctions Mch sU o).rel.spec AnyOperands
  query _ _ := Dense.queryContract id
  resources := smallEigResources
  realize _ _ _ := by
    refine ⟨smallEigInterp Mch sU, fun o => ?_, ?_⟩
    · exact Interp.ofFns_isFn (Tst := Tst) (smallEigFunctions Mch sU) .total o AnyOperands
    · rintro (c | q)
      · exact ⟨fun d a m xs h => by
          change (m.readBlocks a c.lens).map (c.fn id) = _
          rw [h]; rfl, fun _ _ => rfl⟩
      · cases q
        exact ⟨fun _ _ _ => rfl, fun a m xs h => by
          change ((m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn id xs.flatten) = _
          rw [h]; rfl⟩

/-- **The small-eigenvalue model is confined**: every contract is in operand form. -/
instance confined_smallEigModel {r b : ℕ} (P : Problem ℝ r b) (Mch : Machine ℝ) (sU : ℕ) :
    (smallEigModel P Mch sU).Confined :=
  ⟨fun _ _ _ => BlockRel.confined_spec _ _, fun _ _ q => Dense.confined_queryContract id q⟩

/-- **The small-eigenvalue model is uniform**: no contract depends on the input. -/
instance uniform_smallEigModel {r b : ℕ} (P : Problem ℝ r b) (Mch : Machine ℝ) (sU : ℕ) :
    (smallEigModel P Mch sU).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- **The small-eigenvalue model is charged**: every primitive, query and structural instruction
costs one unit of work. -/
instance charged_smallEigModel {r b : ℕ} (P : Problem ℝ r b) (Mch : Machine ℝ) (sU : ℕ) :
    (smallEigModel P Mch sU).Charged :=
  ⟨fun _ _ => Nat.one_pos, fun _ _ => Nat.one_pos, fun _ _ => Nat.one_pos⟩

/-- The contracts of the model give the laws used by the program proofs. -/
theorem smallEigModel_laws {r b : ℕ} {P : Problem ℝ r b} {Mch : Machine ℝ} {sU : ℕ}
    {d : Fin r → ℕ} {x : P.Input d} {I : Interp SmallEigOp Tst ℝ}
    (h : (smallEigModel P Mch sU).contracts d x I) :
    IsScalar Mch I ∧ IsIndexLit Mch I ∧ IsCmp id I ∧ IsToNat id I ∧ IsSample I ∧
      IsPolarDiskSampler sU I := by
  refine ⟨fun o => h.1 (.inl o), h.1 (.inr (.inl .lit)), ?_, ?_,
    fun s => h.1 (.inr (.inr (.inl (.draw s)))),
    isPolarDiskSampler_of_isFn (h.1 (.inr (.inr (.inr .polar))))⟩
  · intro c ds a m xs hr
    exact (h.2 (.inl c)).1 ds a m xs hr
  · intro a m xs hr
    exact (h.2 (.inr .toNat)).2 a m xs hr

/-! ### The program and the problem -/

/-- **The small-eigenvalue program**: `NLAlib.SmallEig.smallEigProg` with the Gaussian stream
`sG` at the order `d 0 + 1`, `d 1` parameter words and the cap `d 2`, on the three supplied
buffers (matrix, parameter words, output). -/
def smallEigProgram (sG : ℕ) : Program SmallEigOp Tst 3 3 :=
  ⟨.frame [.var 0 + .const 1, .var 1, .var 2] [⟨0, .var 3⟩, ⟨1, .var 4⟩, ⟨0, .var 3⟩, ⟨2, .var 5⟩]
    (smallEigProg (O := SmallEigOp) (Q := Tst) sG).body⟩

/-- **The semantic input** at the sizes `d`, for the order bound $n_{\max}$ and the tail records
$c_1, c_2$: the matrix of order `d 0 + 1` and the reals $\Sigma, \delta, \varphi$ of the parameter
words, with the number of words and the cap the ones they determine. -/
structure SmallEigData (nmax : ℕ) (c₁ c₂ : PolyLogTail) (d : Fin 3 → ℕ) where
  /-- The matrix. -/
  matrix : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ
  /-- The norm bound. -/
  S : ℝ
  /-- The backward error. -/
  δ : ℝ
  /-- The failure probability. -/
  φ : ℝ
  /-- The number of parameter words. -/
  words_eq : d 1 = (smallEigParams nmax S δ φ c₁ c₂).length
  /-- The cap. -/
  cap_eq : d 2 = smallEigCap nmax S δ φ c₁ c₂

/-- The three raw buffers of an input: the matrix words (overwritten by the triangular block), the
parameter words and uninitialized room for the $2(n + 1)^2$ words of the accumulator. -/
noncomputable def SmallEigData.buffers {nmax : ℕ} {c₁ c₂ : PolyLogTail} {d : Fin 3 → ℕ}
    (x : SmallEigData nmax c₁ c₂ d) : Fin 3 → Buf ℝ :=
  ![(matrixWords x.matrix).map some, (smallEigParams nmax x.S x.δ x.φ c₁ c₂).map some,
    List.replicate (2 * ((d 0 + 1) * (d 0 + 1))) none]

/-- **The admitted sizes** on the machine `Mch`: the natural literals up to the order $n + 1$
are exact, the order is at most $n_{\max}$, and the sizes are those of some parameter reals. No
rounding model is assumed: the run terminates on every tape at such a machine
(`NLAlib.SmallEig.smallEigProgram_wp`, from `NLAlib.SmallEig.smallEigProg_completes`). -/
def SmallEigSizes (Mch : Machine ℝ) (nmax : ℕ) (c₁ c₂ : PolyLogTail) (d : Fin 3 → ℕ) : Prop :=
  IsExactNatLit id Mch (d 0 + 1) ∧ d 0 + 1 ≤ nmax ∧
    ∃ S δ φ : ℝ, d 1 = (smallEigParams nmax S δ φ c₁ c₂).length ∧
      d 2 = smallEigCap nmax S δ φ c₁ c₂

/-- **The problem** of the small-eigenvalue solver on the machine `Mch`, with the order bound
$n_{\max}$ and the tail records $c_1, c_2$: the three raw buffers of
`NLAlib.SmallEig.SmallEigData.buffers` at the admitted sizes `NLAlib.SmallEig.SmallEigSizes`. -/
noncomputable def smallEigProblem (Mch : Machine ℝ) (nmax : ℕ) (c₁ c₂ : PolyLogTail)
    (admitted : ∃ d, SmallEigSizes Mch nmax c₁ c₂ d) : Problem ℝ 3 3 where
  formats _ := .cell
  valid := SmallEigSizes Mch nmax c₁ c₂
  Data := SmallEigData nmax c₁ c₂
  admissible _ x buffers := buffers = x.buffers
  admitted := admitted
  supply d hd := by
    obtain ⟨-, -, S, δ, φ, hw, hT⟩ := hd
    exact ⟨⟨0, S, δ, φ, hw, hT⟩, _, rfl⟩

variable {Mch : Machine ℝ} {nmax : ℕ} {c₁ c₂ : PolyLogTail}
  {admitted : ∃ d, SmallEigSizes Mch nmax c₁ c₂ d}

/-- The initial memory holds the input of the small-eigenvalue program
(`NLAlib.SmallEig.SmallEigInput`) at the three supplied buffers. -/
theorem smallEigProblem_initial_input (d : Fin 3 → ℕ)
    (x : (smallEigProblem Mch nmax c₁ c₂ admitted).Input d) :
    SmallEigInput nmax x.val.1.S x.val.1.δ x.val.1.φ c₁ c₂ (0, 0) (1, 0) (2, 0) x.val.1.matrix
      ((smallEigProblem Mch nmax c₁ c₂ admitted).initial d x) := by
  have hb : x.val.2 = x.val.1.buffers := x.property
  have hs : ((smallEigProblem Mch nmax c₁ c₂ admitted).initial d x).store =
      List.ofFn x.val.1.buffers := by
    change List.ofFn x.val.2 = _
    rw [hb]
  have hA := Problem.initial_readBlock (P := smallEigProblem Mch nmax c₁ c₂ admitted) d x
    (0 : Fin 3) (xs := matrixWords x.val.1.matrix) (by rw [hb]; rfl)
  have hP := Problem.initial_readBlock (P := smallEigProblem Mch nmax c₁ c₂ admitted) d x
    (1 : Fin 3) (xs := smallEigParams nmax x.val.1.S x.val.1.δ x.val.1.φ c₁ c₂)
    (by rw [hb]; rfl)
  refine ⟨by simpa [HoldsMatrix] using hA, by simpa using hP, ?_, ?_,
    Fp.disj_inBlock_of_ne (by omega),
    Fp.disj_sup_right.mpr ⟨Fp.disj_inBlock_of_ne (by omega), Fp.disj_inBlock_of_ne (by omega)⟩⟩
  · simp [Mem.Live, Problem.initial]
  · simp [hs, Store.len, SmallEigData.buffers, List.ofFn_succ]

/-! ### The work and span polynomial -/

/-- The slot bounds of the program's initial indices: the three sizes, then three zero
offsets. -/
def smallEigSlots : List WorkMono :=
  [⟨1, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩] ++ List.replicate 3 (WorkMono.const 0)

-- The kernel evaluates the bound of the whole instrumented tree; its recursion is deep.
set_option maxRecDepth 100000 in
/-- The monomial bound of the instructions of the instrumented program is
$517058\,b_0^4 b_2^2$ (`NLAlib.SmallEig.smallEigWork`). -/
theorem stmtWorkMono_smallEigProgram (sG : ℕ) :
    stmtWorkMono (smallEigProgram sG).body.instrument smallEigSlots = ⟨517058, [4, 0, 2]⟩ := by
  kernel_rfl

/-- **The work (and span) polynomial** of the small-eigenvalue solver at the sizes
$(n, n_q, T)$ = `d`: $517058\,(n + 1)^4(T + 1)^2$, the
monomial bound of the instructions of the instrumented program, each of unit weight; it is larger
than the constant $80390$ of `NLAlib.SmallEig.smallEig_work_le` because it also counts the frame
of the program. The parameter words (thresholds, scales and caps, real numbers
with logarithms and roots) are
supplied in the input and their computation is not charged, as for the merged
algorithm. The monomial is an envelope of the paper's count $n^4 + n^3\log^2$, not its shape: the
cap $T$ = `NLAlib.SmallEig.smallEigCap` is the largest loop count ($m$, $t$, $m_2$), a logarithm of
$n_{\max}\Sigma/(\delta\varphi)$ up to constants (bounded in the proof of
`NLAlib.SmallEig.logb_inv_uSmallEig_le`). -/
def smallEigWork (d : Fin 3 → ℕ) : ℕ := 517058 * (d 0 + 1) ^ 4 * (d 2 + 1) ^ 2

/-- The number of instructions of the static count of the program is at most
`NLAlib.SmallEig.smallEigWork`. -/
theorem size_staticCost_smallEigProgram_le (sG : ℕ) (d : Fin 3 → ℕ) :
    Count.size (staticCost (smallEigProgram sG) d) ≤ smallEigWork d := by
  have hσ : SlotsLe [d 0 + 1, d 1 + 1, d 2 + 1] (Program.environment (b := 3) d).idx
      smallEigSlots := by
    change List.Forall₂ _ [d 0, d 1, d 2, 0, 0, 0] _
    simp [smallEigSlots, WorkMono.eval, WorkMono.const]
  have h := size_stmtCost_le_stmtWorkMono (by simp) (smallEigProgram sG).body.instrument hσ
  rw [stmtWorkMono_smallEigProgram] at h
  simpa [staticCost, WorkMono.eval, smallEigWork, mul_assoc] using h

/-- The work and span of every run: under the unit costs, every successful counted run of
the program has work and span at most `NLAlib.SmallEig.smallEigWork` at its sizes. -/
theorem smallEigProgram_work_le {K : Type} (sG : ℕ) {I : Interp SmallEigOp Tst K} {τ : Tape K}
    {formats : Fin 3 → StorageFormat} {d : Fin 3 → ℕ} {m : Mem K}
    {st : St (SmallEigOp ⊕ Bookkeeping) Tst K}
    (hr : exec (smallEigProgram sG) I smallEigResources formats τ d m = some st) :
    smallEigResources.work st.cost ≤ smallEigWork d ∧
      smallEigResources.span st.cost ≤ smallEigWork d := by
  have h := (size_mono (exec_static hr).1).trans (size_staticCost_smallEigProgram_le sG d)
  exact ⟨(smallEigResources_work _).trans_le h, (smallEigResources_span _).trans_le h⟩

/-! ### The certificate -/

/-- The payload words of the three supplied buffers. -/
def smallEigInputWords (d : Fin 3 → ℕ) : ℕ :=
  2 * ((d 0 + 1) * (d 0 + 1)) + d 1 + 2 * ((d 0 + 1) * (d 0 + 1))

theorem smallEigProblem_initialBytes (d : Fin 3 → ℕ)
    (x : (smallEigProblem Mch nmax c₁ c₂ admitted).Input d) :
    (smallEigProblem Mch nmax c₁ c₂ admitted).initialBytes d x = smallEigInputWords d := by
  unfold Problem.initialBytes
  have hb : x.val.2 = x.val.1.buffers := x.property
  rw [hb]
  simp [smallEigProblem, SmallEigData.buffers, List.ofFn_succ, smallEigInputWords,
    ← x.val.1.words_eq, Nat.add_assoc]

/-- The every-tape output claim: the run writes only the block and the accumulator, and both
are stored (a Schur pair, `NLAlib.Schur.HoldsSchurPair`, with no accuracy claim). -/
def SmallEigFrame (d : Fin 3 → ℕ) (μ μ' : Mem ℝ) : Prop :=
  μ.store.EqOff (Store.inBlock 0 0 (2 * ((d 0 + 1) * (d 0 + 1))) ⊔
            Store.inBlock 2 0 (2 * ((d 0 + 1) * (d 0 + 1)))) μ'.store ∧
    ∃ U T : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ,
      Schur.HoldsSchurPair (0, 0) (2, 0) U T μ'.store

/-- **The specification of the small-eigenvalue solver**: the budget, scratch and resident
memory of the static count, the work and the span `NLAlib.SmallEig.smallEigWork`, and on every
tape the frame and the stored output (`NLAlib.SmallEig.SmallEigFrame`). -/
noncomputable def smallEigSpecification (Mch : Machine ℝ) (nmax : ℕ) (c₁ c₂ : PolyLogTail)
    (admitted : ∃ d, SmallEigSizes Mch nmax c₁ c₂ d) (sG : ℕ) :
    Specification SmallEigOp Tst (smallEigProblem Mch nmax c₁ c₂ admitted) where
  budget := staticCost (smallEigProgram sG)
  scratch := staticPeak smallEigResources (smallEigProgram sG)
  work := smallEigWork
  span := smallEigWork
  memory d := smallEigInputWords d + staticPeak smallEigResources (smallEigProgram sG) d
  good d x _ _ m := SmallEigFrame d ((smallEigProblem Mch nmax c₁ c₂ admitted).initial d x) m

/-- The program terminates on every admitted input, tape and interpretation of the model, writes
only the output and leaves it stored. -/
theorem smallEigProgram_wp {sU sG : ℕ} {d : Fin 3 → ℕ} (hd : SmallEigSizes Mch nmax c₁ c₂ d)
    (x : (smallEigProblem Mch nmax c₁ c₂ admitted).Input d) {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (smallEigProblem Mch nmax c₁ c₂ admitted) Mch sU).contracts d x I)
    (τ : Tape ℝ) :
    Wp .total I τ (smallEigProgram sG).body (Program.environment (b := 3) d)
      (SmallEigFrame d ((smallEigProblem Mch nmax c₁ c₂ admitted).initial d x))
      ((smallEigProblem Mch nmax c₁ c₂ admitted).initial d x) := by
  obtain ⟨hNat, -, -⟩ := hd
  obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
  have hin := smallEigProblem_initial_input (admitted := admitted) d x
  obtain ⟨hW, hq, hl3, hroom, hwo, hqwo⟩ := hin
  have hl4 : ((smallEigProblem Mch nmax c₁ c₂ admitted).initial d x).Live
      [(0, 0), (1, 0), (0, 0), (2, 0)] := fun y hy => hl3 y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> simp)
  have hT : CompletingLeafRoutine (d 0 + 1) _ _ _ I := smallEigProg_completes (O := SmallEigOp)
    (Q := Tst) (sG := sG) hS hL hNat hC hQ hSmp hDisk
    (smallEigCaps_smallEigParams nmax x.val.1.S x.val.1.δ x.val.1.φ c₁ c₂)
    (by simp [length_smallEigParams])
  refine wp_frame ?_ ?_ hl4 ((hT x.val.1.matrix le_rfl hW hq hl3 hroom hwo hqwo).mono le_rfl
    fun μ' _ ⟨Tb, Ub, hTb, hUb⟩ => ⟨Ub, Tb, hTb, hUb⟩)
  · simp [Program.environment, IExp.evalList, IExp.eval, x.val.1.words_eq, x.val.1.cap_eq,
      List.ofFn_succ]
  · simp [Program.environment, Operand.evalList, Operand.eval, IExp.eval, List.ofFn_succ]

/-- The program passes the storage discipline of the costs. -/
theorem smallEigProgram_wellTyped (sG : ℕ) :
    (smallEigProgram sG).wellTyped smallEigResources
      (smallEigProblem Mch nmax c₁ c₂ admitted).formats = true := by
  kernel_rfl

/-- **The small-eigenvalue solver as a canonical certificate**: the fixed program
`NLAlib.SmallEig.smallEigProgram`, over the model `NLAlib.SmallEig.smallEigModel` (no oracle)
with the unit costs, succeeds on every admitted input, interpretation of the model and tape,
within the static budget, scratch and memory, with work and span at most
`NLAlib.SmallEig.smallEigWork`, writing only the output and leaving it stored. The output's
accuracy holds with probability at least $1 - \varphi$
(`NLAlib.SmallEig.smallEig_algorithm_measureReal_not_accepts_le`).
Algorithm: small-eig (run model) -/
noncomputable def smallEigAlgorithm (Mch : Machine ℝ) (nmax : ℕ) (c₁ c₂ : PolyLogTail)
    (admitted : ∃ d, SmallEigSizes Mch nmax c₁ c₂ d) (sU sG : ℕ) :
    Algorithm (smallEigModel (smallEigProblem Mch nmax c₁ c₂ admitted) Mch sU)
      (smallEigSpecification Mch nmax c₁ c₂ admitted sG) :=
  Algorithm.ofWp (smallEigProgram sG) (smallEigProgram_wellTyped sG)
    (fun _ hd x _ hI τ => (smallEigProgram_wp hd x hI τ).mono fun _ h _ _ => h)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun d _ => (smallEigResources_work _).trans_le (size_staticCost_smallEigProgram_le sG d))
    (fun d _ => (smallEigResources_span _).trans_le (size_staticCost_smallEigProgram_le sG d))
    (fun d _ x => by rw [smallEigProblem_initialBytes]; exact le_rfl)

/-! ### The headline on one run -/

/-- **The small-eigenvalue solver, on one run** ([BanksGarzaVargasSrivastava2025, Theorem 1.1],
corrected: $\Sigma$ an input, the base case of order $1$, every loop capped, the error absolute).
Let the machine `Mch` have the standard model at $\boldsymbol{u}$; let the tape $\xi$ have the
stream laws `law`, with `law` $s_U$ uniform on $[0, 1]$ and `law` $s_G$ the standard real
Gaussian law; let the eigenvalue gap and the eigenvector condition of a complex Ginibre
perturbation have the tails $c_1$, $c_2$ with $b_1, b_2 > 0$. Let $(n, n_q, T)$ = `d` be admitted
(in particular $n + 1 \le n_{\max}$) and let the input `x` hold a matrix $\mathbf{M}$ of order
$n + 1$ with $\|\mathbf{M}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ (`NLAlib.SmallEig.uSmallEig` at
$n_{\max}$). Let `I` meet the model, be measurable and read the tape only in its windows. Then
$$\mathbb{P}\bigl[\mathsf{smallEigAlgorithm}(\mathbf{M}) \text{ fails, exceeds its budget,
  scratch, memory, work or span, writes outside its output, or lists no }
  \operatorname{spec}(\mathbf{M} + \mathbf{E}),\ \|\mathbf{E}\|_2 \le \delta\bigr]
  \le \varphi\,,$$
on one counted run, with the work and the span `NLAlib.SmallEig.smallEigWork`.
Result: small-eig-certificate-accuracy -/
theorem smallEig_algorithm_measureReal_not_accepts_le {u : ℝ} (hM : StdModel u id Mch)
    {law : ℕ → Measure ℝ} {sU sG : ℕ} (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) (hA : c₁.BoundsGinibreGap)
    (hB : c₂.BoundsGinibreCondition) (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {d : Fin 3 → ℕ} (hd : SmallEigSizes Mch nmax c₁ c₂ d)
    (x : (smallEigProblem Mch nmax c₁ c₂ admitted).Input d) {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (smallEigProblem Mch nmax c₁ c₂ admitted) Mch sU).contracts d x I)
    (hIm : I.IsMeasurable) {win : SmallEigOp → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hMS : specNorm x.val.1.matrix ≤ x.val.1.S) (hδ : 0 < x.val.1.δ)
    (hδS : x.val.1.δ ≤ x.val.1.S) (hφ : 0 < x.val.1.φ) (hφ1 : x.val.1.φ ≤ 1)
    (hu : u ≤ uSmallEig nmax x.val.1.S x.val.1.δ x.val.1.φ c₁ c₂)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ (smallEigSpecification Mch nmax c₁ c₂ admitted sG).Accepts smallEigResources d x
      (exec (smallEigAlgorithm Mch nmax c₁ c₂ admitted sU sG).program I smallEigResources
        (smallEigProblem Mch nmax c₁ c₂ admitted).formats (ξ ω) d
        ((smallEigProblem Mch nmax c₁ c₂ admitted).initial d x))
      fun _ m => ((smallEigProblem Mch nmax c₁ c₂ admitted).initial d x).store.EqOff
          (Store.inBlock 0 0 (2 * ((d 0 + 1) * (d 0 + 1))) ⊔
            Store.inBlock 2 0 (2 * ((d 0 + 1) * (d 0 + 1)))) m.store ∧
        SmallEigSpectrum (0, 0) (2, 0) x.val.1.matrix x.val.1.δ m} ≤ x.val.1.φ := by
  have := hξ.isProbabilityMeasure
  obtain ⟨hS, hL, hC, hQ, hSmp, hDisk⟩ := smallEigModel_laws hI
  have hin := smallEigProblem_initial_input (admitted := admitted) d x
  -- TH1 (`smallEig_measureReal_not_spectrum_le`), applied as it is stated.
  have hT := smallEig_measureReal_not_spectrum_le (O := SmallEigOp) (Q := Tst) (sG := sG) hS hM
    hL hd.1 hQ hC hIm hloc hSmp hDisk hU hG hA hB hb₁ hb₂ hd.2.1 hMS hδ hδS hφ hφ1 hu hin hξ
  refine (smallEigAlgorithm Mch nmax c₁ c₂ admitted sU sG).measureReal_not_accepts_le_of_wp hd x
    I hI P ξ _ ?_
  refine (measureReal_mono ?_).trans hT
  intro ω hω hW
  have hl3 := hin.2.2.1
  have hl4 : ((smallEigProblem Mch nmax c₁ c₂ admitted).initial d x).Live
      [(0, 0), (1, 0), (0, 0), (2, 0)] := fun y hy => hl3 y (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> simp)
  refine hω (wp_frame ?_ ?_ hl4 hW)
  · simp [Program.environment, IExp.evalList, IExp.eval, smallEigDims, x.val.1.words_eq,
      x.val.1.cap_eq, List.ofFn_succ]
  · simp [Program.environment, Operand.evalList, Operand.eval, IExp.eval, List.ofFn_succ]


/-! ### With the proved random-matrix tails -/

/-- **The small-eigenvalue solver, on one run, unconditional**.
The unconditional form of `NLAlib.SmallEig.smallEig_algorithm_measureReal_not_accepts_le`
([BanksGarzaVargasSrivastava2025, Theorem 1.1]): the eigenvalue-gap and eigenvector-condition tails
of a complex Ginibre perturbation are proved, at the records
`NLAlib.ginibreGapTail` <!-- value ginibreGapTail --> $(10000e, 5, 1/2, 2)$ and
`NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail --> $(128e, 3, 2, 2)$.
Result: small-eig-certificate-accuracy -/
theorem smallEig_algorithm_measureReal_not_accepts_le_unconditional
    {admitted : ∃ d, SmallEigSizes Mch nmax ginibreGapTail
      ginibreConditionTail d} {u : ℝ} (hM : StdModel u id Mch)
    {law : ℕ → Measure ℝ} {sU sG : ℕ} (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {d : Fin 3 → ℕ} (hd : SmallEigSizes Mch nmax
      ginibreGapTail ginibreConditionTail d)
    (x : (smallEigProblem Mch nmax ginibreGapTail ginibreConditionTail
      admitted).Input d) {I : Interp SmallEigOp Tst ℝ}
    (hI : (smallEigModel (smallEigProblem Mch nmax ginibreGapTail
      ginibreConditionTail admitted) Mch sU).contracts d x I)
    (hIm : I.IsMeasurable) {win : SmallEigOp → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hMS : specNorm x.val.1.matrix ≤ x.val.1.S) (hδ : 0 < x.val.1.δ)
    (hδS : x.val.1.δ ≤ x.val.1.S) (hφ : 0 < x.val.1.φ) (hφ1 : x.val.1.φ ≤ 1)
    (hu : u ≤ uSmallEig nmax x.val.1.S x.val.1.δ x.val.1.φ ginibreGapTail
      ginibreConditionTail)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ (smallEigSpecification Mch nmax ginibreGapTail
      ginibreConditionTail admitted sG).Accepts smallEigResources d x
      (exec (smallEigAlgorithm Mch nmax ginibreGapTail
        ginibreConditionTail admitted sU sG).program I smallEigResources
        (smallEigProblem Mch nmax ginibreGapTail ginibreConditionTail
          admitted).formats (ξ ω) d
        ((smallEigProblem Mch nmax ginibreGapTail ginibreConditionTail
          admitted).initial d x))
      fun _ m => ((smallEigProblem Mch nmax ginibreGapTail
        ginibreConditionTail admitted).initial d x).store.EqOff
          (Store.inBlock 0 0 (2 * ((d 0 + 1) * (d 0 + 1))) ⊔
            Store.inBlock 2 0 (2 * ((d 0 + 1) * (d 0 + 1)))) m.store ∧
        SmallEigSpectrum (0, 0) (2, 0) x.val.1.matrix x.val.1.δ m} ≤ x.val.1.φ := by
  apply smallEig_algorithm_measureReal_not_accepts_le
    (hA := boundsGinibreGap_ginibreGapTail) (hB := boundsGinibreCondition_ginibreConditionTail)
    (hb₁ := ginibreGapTail_b_pos) (hb₂ := ginibreConditionTail_b_pos) <;> assumption

end NLAlib.SmallEig
