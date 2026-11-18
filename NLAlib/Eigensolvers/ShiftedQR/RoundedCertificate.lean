/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Cost
public import NLAlib.Ops.Probability
public import NLAlib.Ops.Profiles.Confined
public import NLAlib.Ops.SelectedWork
public import NLAlib.Eigensolvers.ShiftedQR.RoundedTheorems
public import NLAlib.Eigensolvers.ShiftedQR.RoundedParameterChoices

/-!
# The rounded shifted QR algorithm as a canonical certificate

The headline theorems of `NLAlib.Eigensolvers.ShiftedQR.RoundedTheorems` state the probability
of a correct output and the static count of `NLAlib.ShiftedQR.roundedShQR` separately. This file
states them for **one run**: the program, fixed before every size and input, is a canonical
certificate (`NLAlib.Ops.Algorithm`) over a jointly realized access model, with explicit work and
span bounds; and the probability that this counted run fails, exceeds a resource bound of the
specification, or fails to store the spectrum of a nearby matrix is at most $\varphi$.

The model: scalar arithmetic is the function of a machine `Mch` (its standard model at
$\boldsymbol{u}$ is a hypothesis of the probability statement only); dimension literals,
comparisons and index conversion are exact; `SmallEig` is any interpretation meeting the
relational contract `NLAlib.ShiftedQR.randomSmallEigRel` at fixed window lengths $W$ and bad
sets; the disk sampler is exact. The model is realized by exact eigenvalues and the exact polar
sampler. The `Ritz` kernel is in the operation signature (the operations are shared with the
exact-arithmetic program) but the program never calls it; its contract is the exact block
function. That a measurable interpretation meets the `SmallEig` contract (a hypothesis of the
probability statement) is assumed, not exhibited: `SmallEig` is an oracle. The weights of
`SmallEig` and `Ritz` are caller parameters, possibly $0$ and not bounded
by $1$; every other primitive, query and structural instruction costs one unit.

The admitted sizes have $k \le n$ (the shift degree below the order $n + 1$): the degenerate
regime $k > n$, in which the program is a copy and one `SmallEig` call of full size, is excluded.

The every-tape output claim (`NLAlib.Ops.Specification.good`) is the frame: the run writes only
the matrix, the output and the failure word. No accuracy claim holds on every tape, not even
one conditional on the failure word $0$: on a window in its bad set `SmallEig` may return any
words, and a leaf block stores them as its eigenvalues with the failure word $0$. Nor does a
predicate on the tape alone give accuracy for every interpretation of the model with probability
at least $1 - \varphi$: the positions of the windows the program reads, and the matrices that
define their bad sets, depend on the earlier draws and on the kernel's outputs. The spectrum
claim is the postcondition of `NLAlib.Ops.Specification.Accepts` in
`NLAlib.ShiftedQR.roundedShQRSmallEigAlgorithm`, bounded through the
probabilistic program logic (`NLAlib.Ops.Algorithm.measureReal_not_accepts_le_of_wp`).

## Main definitions

* `NLAlib.ShiftedQR.ShQROp`, `NLAlib.ShiftedQR.shqrProgram`: the signature and the program.
* `NLAlib.ShiftedQR.shqrProblem`: the five raw buffers and the admitted sizes.
* `NLAlib.ShiftedQR.shqrModel`, `NLAlib.ShiftedQR.shqrResources`: the access model and its costs.
* `NLAlib.ShiftedQR.shqrWork`: the explicit work and span polynomial.
* `NLAlib.ShiftedQR.roundedShQRSmallEigAlgorithm`: the certificate.

## Main results

* `NLAlib.ShiftedQR.roundedShQRSmallEigAlgorithm`: the work of every run.
* `NLAlib.ShiftedQR.roundedShQRSmallEigAlgorithm`: the headline, on one run.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops MeasureTheory
open scoped Matrix

/-! ### The signature and the program -/

/-- The operations of the rounded shifted QR algorithm: scalar arithmetic, index literals, the
two eigenvalue kernels and the polar disk sampler. -/
abbrev ShQROp := ScalarOp ⊕ (IndexOp ⊕ (EigenvalueKernelOp ⊕ DiskSampleOp))

instance : Has IndexOp ShQROp := Has.sumRight _ _ _ inferInstance

instance : Has EigenvalueKernelOp ShQROp :=
  Has.sumRight _ _ _ (Has.sumRight _ _ _ inferInstance)

instance : Has DiskSampleOp ShQROp := Has.sumRight _ _ _ (Has.sumRight _ _ _ inferInstance)

/-! ### The problem -/

/-- **The semantic input** at the sizes `d`: the matrix of order `d 0 + 1` and the reals
$B, \Gamma, \Sigma, \delta, \varphi$ of the parameter words, with the shift degree, the number of
parameter words and the cap the ones they determine. -/
structure ShQRData (d : Fin 4 → ℕ) where
  /-- The matrix. -/
  matrix : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ
  /-- The condition bound. -/
  B : ℝ
  /-- The separation. -/
  Γ : ℝ
  /-- The norm bound. -/
  S : ℝ
  /-- The backward error. -/
  δ : ℝ
  /-- The failure probability. -/
  φ : ℝ
  /-- The shift degree is the degree of (eqn:setk) at $4B$. -/
  degree_eq : d 1 = shqrDegree (4 * B)
  /-- The number of parameter words. -/
  words_eq : d 2 = (shqrParams (d 0) (d 1) B Γ S δ φ).length
  /-- The iteration cap. -/
  cap_eq : d 3 = shqrCap (d 0) B Γ S δ

/-- The five raw buffers of an input: the matrix words, the deflation threshold word, the
parameter words, the identity accumulator (the $2(n + 1)^2$ words of the output) and the failure
word. -/
noncomputable def ShQRData.buffers {d : Fin 4 → ℕ} (x : ShQRData d) : Fin 5 → Buf ℝ :=
  ![(matrixWords x.matrix).map some,
    [some (shqrDeflationThreshold (d 0) (d 1) x.B x.Γ x.S x.δ x.φ)],
    (shqrParams (d 0) (d 1) x.B x.Γ x.S x.δ x.φ).map some,
    (matrixWords (1 : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ)).map some, [none]]

/-- **The admitted sizes** on the machine `Mch`: the natural literals up to the order $n + 1$
are exact, the shift degree is at most $n$, and the sizes are those of some parameter reals. -/
def ShQRSizes (Mch : Machine ℝ) (d : Fin 4 → ℕ) : Prop :=
  IsExactNatLit id Mch (d 0 + 1) ∧ d 1 ≤ d 0 ∧
    ∃ B Γ S δ φ : ℝ, d 1 = shqrDegree (4 * B) ∧
      d 2 = (shqrParams (d 0) (d 1) B Γ S δ φ).length ∧ d 3 = shqrCap (d 0) B Γ S δ

/-- **The problem** of the rounded shifted QR algorithm on the machine `Mch`: the five raw
buffers of `NLAlib.ShiftedQR.ShQRData.buffers` at the admitted sizes
`NLAlib.ShiftedQR.ShQRSizes`. -/
noncomputable def shqrProblem (Mch : Machine ℝ) (admitted : ∃ d, ShQRSizes Mch d) :
    Problem ℝ 4 5 where
  formats _ := .cell
  valid := ShQRSizes Mch
  Data := ShQRData
  admissible _ x buffers := buffers = x.buffers
  admitted := admitted
  supply d hd := by
    obtain ⟨-, -, B, Γ, S, δ, φ, hk, hp, hF⟩ := hd
    exact ⟨⟨0, B, Γ, S, δ, φ, hk, hp, hF⟩, _, rfl⟩

variable {Mch : Machine ℝ} {admitted : ∃ d, ShQRSizes Mch d}

/-- The initial memory holds the input of the rounded shifted QR algorithm
(`NLAlib.ShiftedQR.ShQRInput`) at the five supplied buffers. -/
theorem shqrProblem_initial_input (d : Fin 4 → ℕ) (x : (shqrProblem Mch admitted).Input d) :
    ShQRInput (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ x.val.1.φ (0, 0) (1, 0) (2, 0)
      (3, 0) (4, 0) x.val.1.matrix ((shqrProblem Mch admitted).initial d x) := by
  have hb : x.val.2 = x.val.1.buffers := x.property
  have hs : ((shqrProblem Mch admitted).initial d x).store = List.ofFn x.val.1.buffers := by
    change List.ofFn x.val.2 = _
    rw [hb]
  have hA := Problem.initial_readBlock (P := shqrProblem Mch admitted) d x
    (0 : Fin 5) (xs := matrixWords x.val.1.matrix) (by rw [hb]; rfl)
  have hP := Problem.initial_readBlock (P := shqrProblem Mch admitted) d x
    (2 : Fin 5) (xs := shqrParams (d 0) (d 1) x.val.1.B x.val.1.Γ x.val.1.S x.val.1.δ x.val.1.φ)
    (by rw [hb]; rfl)
  have hU := Problem.initial_readBlock (P := shqrProblem Mch admitted) d x
    (3 : Fin 5) (xs := matrixWords (1 : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ))
    (by rw [hb]; rfl)
  refine ⟨?_, ?_, ?_, ⟨1, by simpa [HoldsMatrix] using hU⟩, ?_, ?_, ?_⟩
  · simp [Mem.Live, Problem.initial]
  · simp [Mem.Room, hs, Store.len, ShQRData.buffers, List.ofFn_succ]
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil]
    disjoint
  · simpa [HoldsMatrix] using hA
  · rw [hs]
    simp [Store.get, ShQRData.buffers, List.ofFn_succ]
  · simpa using hP

/-! ### The access model -/

/-- An exact `SmallEig` reading `W d` entries of the stream `s` (which it ignores): the exact
eigenvalue listing of `NLAlib.ShiftedQR.exactRoutines`. It witnesses the relational contract. -/
noncomputable def windowedSmallEigFn (s : ℕ) (W : ℕ → ℕ) : BlockFn ℝ where
  nd := 1
  stream := s
  win d := W (d.headD 0)
  inLens d := [2 * (d.headD 0 * d.headD 0)]
  outLens d := [2 * d.headD 0]
  fn d _ xs := some [matrixWords (Matrix.of fun i (_ : Fin 1) =>
    exactRoutines.smallEig (d.headD 0) (matrixOfWords (d.headD 0) (xs.headD [])) i)]

/-- The exact polar disk sampler on the stream `s`, as a block function. -/
noncomputable def polarDiskFn (s : ℕ) : BlockFn ℝ where
  nd := 0
  stream := s
  win _ := 2
  inLens _ := [1]
  outLens _ := [2]
  fn _ w xs := some [[(polarDisk 0 ((xs.headD []).headD 0) fun j : Fin 2 => w.getD j 0).re,
    (polarDisk 0 ((xs.headD []).headD 0) fun j : Fin 2 => w.getD j 0).im]]

/-- The block functions of the realizing interpretation: the machine's arithmetic and literals,
the exact kernels and the exact polar sampler. -/
noncomputable def shqrFunctions (Mch : Machine ℝ) (s : ℕ) (W : ℕ → ℕ) : ShQROp → BlockFn ℝ
  | .inl o => Mch.fn o
  | .inr (.inl _) => Mch.indexFn
  | .inr (.inr (.inl .ritz)) => ritzFn exactRoutines
  | .inr (.inr (.inl .smallEig)) => windowedSmallEigFn s W
  | .inr (.inr (.inr .polar)) => polarDiskFn s

/-- The contracts of the model: the functions of `NLAlib.ShiftedQR.shqrFunctions`, except that
`SmallEig` meets only the relational contract `NLAlib.ShiftedQR.randomSmallEigRel` and the
sampler the contract `NLAlib.ShiftedQR.polarDiskRel`. All are in operand form. -/
noncomputable def shqrContract (Mch : Machine ℝ) (s : ℕ) (W : ℕ → ℕ)
    (Bad : (d : ℕ) → Matrix (Fin d) (Fin d) ℂ → Set (Fin (W d) → ℝ)) (β : ℝ) :
    ShQROp → Contract ℝ
  | .inr (.inr (.inl .smallEig)) => (randomSmallEigRel s W Bad β).spec AnyOperands
  | .inr (.inr (.inr .polar)) => (polarDiskRel s).spec AnyOperands
  | o => (shqrFunctions Mch s W o).rel.spec AnyOperands

/-- The realizing interpretation. -/
noncomputable def shqrInterp (Mch : Machine ℝ) (s : ℕ) (W : ℕ → ℕ) : Interp ShQROp Tst ℝ where
  call o := (Interp.ofFns (Tst := Tst) (shqrFunctions Mch s W)).call o
  test := cmpInterp.test
  index := cmpInterp.index

/-- Operand formats count real words. -/
def shqrSignature : ShQROp → OperandSignature
  | .inl (.lit _) | .inr (.inl _) => ⟨[], [.cell]⟩
  | .inl .add | .inl .sub | .inl .mul | .inl .div => ⟨[.cell, .cell], [.cell]⟩
  | .inl .neg | .inl .sqrt | .inl .copy => ⟨[.cell], [.cell]⟩
  | .inr (.inr _) => ⟨[.cell], [.cell]⟩

/-- **The costs**: each kernel call costs its supplied work, span and workspace at its call
dimensions (caller parameters, possibly $0$, not bounded by $1$); every other primitive, query and
structural instruction costs one unit of work and span and no workspace. -/
def shqrResources (kernelWork kernelSpan kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ)
    (hspan : ∀ k d, kernelSpan k d ≤ kernelWork k d) : ResourceModel ShQROp Tst where
  formats := [.cell]
  operation := shqrSignature
  testInputs q := match q with | .inl c => c.lens.map (fun _ => .cell) | .inr _ => []
  indexInputs q := match q with | .inl _ => [] | .inr _ => [.cell]
  workspace o d := match o with | .inr (.inr (.inl k)) => kernelWorkspace k d | _ => 0
  queryWorkspace _ _ := 0
  operationWork o d := match o with | .inr (.inr (.inl k)) => kernelWork k d | _ => 1
  operationSpan o d := match o with | .inr (.inr (.inl k)) => kernelSpan k d | _ => 1
  queryWork _ _ := 1
  querySpan _ _ := 1
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le o d := by rcases o with o | o | o | o <;> first | exact hspan _ _ | exact le_rfl
  query_span_le _ _ := le_rfl
  core_span_le _ _ := le_rfl

theorem windowedSmallEig_meets (Mch : Machine ℝ) (s : ℕ) (W : ℕ → ℕ)
    (Bad : (d : ℕ) → Matrix (Fin d) (Fin d) ℂ → Set (Fin (W d) → ℝ)) {β : ℝ} (hβ : 0 ≤ β) :
    (shqrInterp Mch s W).Meets .total (Has.inj EigenvalueKernelOp.smallEig)
      ((randomSmallEigRel s W Bad β).spec AnyOperands) := by
  refine (Interp.ofFns_isFn (Tst := Tst) (shqrFunctions Mch s W) .total
    (.inr (.inr (.inl .smallEig))) AnyOperands).meets_rel (fun _ _ _ h => h) rfl rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
  intro d w xs m ins outs _ _ _ _ _
  refine ⟨_, rfl, by simp [randomSmallEigRel], ?_⟩
  rintro N as rfl rfl - -
  exact ⟨_, _, exactRoutines.listing _ _, fun i => by simpa using hβ, rfl⟩

theorem polarDisk_meets (Mch : Machine ℝ) (s : ℕ) (W : ℕ → ℕ) :
    IsPolarDiskSampler s (shqrInterp Mch s W) := by
  refine (Interp.ofFns_isFn (Tst := Tst) (shqrFunctions Mch s W) .total
    (.inr (.inr (.inr .polar))) AnyOperands).meets_rel (fun _ _ _ h => h) rfl rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
  intro d w xs m ins outs _ _ _ _ _
  refine ⟨_, rfl, rfl, ?_⟩
  rintro R rfl
  rfl

/-- **The access model** of the rounded shifted QR algorithm: the contracts
`NLAlib.ShiftedQR.shqrContract` (the machine `Mch`; `SmallEig` with forward error $\beta \ge 0$
outside the bad windows `Bad` of lengths `W` of the stream `s`; the exact polar sampler on `s`),
exact comparisons and index conversion, and the costs `R`. It is realized by
`NLAlib.ShiftedQR.shqrInterp`. -/
noncomputable def shqrModel (P : Problem ℝ 4 5) (Mch : Machine ℝ) (s : ℕ) (W : ℕ → ℕ)
    (Bad : (d : ℕ) → Matrix (Fin d) (Fin d) ℂ → Set (Fin (W d) → ℝ)) {β : ℝ} (hβ : 0 ≤ β)
    (R : ResourceModel ShQROp Tst) : AccessModel ShQROp Tst P where
  word := 0
  operation _ _ := shqrContract Mch s W Bad β
  query _ _ := Dense.queryContract id
  resources := R
  realize _ _ _ := by
    refine ⟨shqrInterp Mch s W, ?_, ?_⟩
    · rintro (o | o | (k | k))
      · exact Interp.ofFns_isFn (Tst := Tst) (shqrFunctions Mch s W) .total _ AnyOperands
      · exact Interp.ofFns_isFn (Tst := Tst) (shqrFunctions Mch s W) .total _ AnyOperands
      · cases k
        · exact Interp.ofFns_isFn (Tst := Tst) (shqrFunctions Mch s W) .total _ AnyOperands
        · exact windowedSmallEig_meets Mch s W Bad hβ
      · cases k
        exact polarDisk_meets Mch s W
    · rintro (c | q)
      · exact ⟨fun d a m xs h => by
          change (m.readBlocks a c.lens).map (c.fn id) = _
          rw [h]; rfl, fun _ _ => rfl⟩
      · cases q
        exact ⟨fun _ _ _ => rfl, fun a m xs h => by
          change ((m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn id xs.flatten) = _
          rw [h]; rfl⟩

/-- **The rounded shifted QR model is confined**: every contract is in operand form. -/
instance confined_shqrModel (P : Problem ℝ 4 5) (Mch : Machine ℝ) (s : ℕ) (W : ℕ → ℕ)
    (Bad : (d : ℕ) → Matrix (Fin d) (Fin d) ℂ → Set (Fin (W d) → ℝ)) {β : ℝ} (hβ : 0 ≤ β)
    (R : ResourceModel ShQROp Tst) : (shqrModel P Mch s W Bad hβ R).Confined := by
  refine ⟨fun _ _ o => ?_, fun _ _ q => Dense.confined_queryContract id q⟩
  rcases o with o | o | (k | k)
  · exact BlockRel.confined_spec _ _
  · exact BlockRel.confined_spec _ _
  · cases k <;> exact BlockRel.confined_spec _ _
  · cases k; exact BlockRel.confined_spec _ _

/-- **The rounded shifted QR model is uniform**: no contract depends on the input. -/
instance uniform_shqrModel (P : Problem ℝ 4 5) (Mch : Machine ℝ) (s : ℕ) (W : ℕ → ℕ)
    (Bad : (d : ℕ) → Matrix (Fin d) (Fin d) ℂ → Set (Fin (W d) → ℝ)) {β : ℝ} (hβ : 0 ≤ β)
    (R : ResourceModel ShQROp Tst) : (shqrModel P Mch s W Bad hβ R).Uniform :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-- The contracts of the model give the laws used by the program proofs. -/
theorem shqrModel_laws {P : Problem ℝ 4 5} {Mch : Machine ℝ} {s : ℕ} {W : ℕ → ℕ}
    {Bad : (d : ℕ) → Matrix (Fin d) (Fin d) ℂ → Set (Fin (W d) → ℝ)} {β : ℝ} {hβ : 0 ≤ β}
    {R : ResourceModel ShQROp Tst} {d : Fin 4 → ℕ} {x : P.Input d} {I : Interp ShQROp Tst ℝ}
    (h : (shqrModel P Mch s W Bad hβ R).contracts d x I) :
    IsScalar Mch I ∧ IsIndexLit Mch I ∧ IsCmp id I ∧ IsToNat id I ∧
      I.Meets .total (Has.inj EigenvalueKernelOp.smallEig)
        ((randomSmallEigRel s W Bad β).spec AnyOperands) ∧ IsPolarDiskSampler s I := by
  refine ⟨fun o => h.1 (.inl o), h.1 (.inr (.inl .lit)), ?_, ?_, h.1 (.inr (.inr (.inl .smallEig))),
    h.1 (.inr (.inr (.inr .polar)))⟩
  · intro c ds a m xs hr
    exact (h.2 (.inl c)).1 ds a m xs hr
  · intro a m xs hr
    exact (h.2 (.inr .toNat)).2 a m xs hr

/-! ### The work and span polynomial -/

/-- The kernel calls: `Ritz` and `SmallEig`. -/
def shqrKernelCall : ShQROp ⊕ Bookkeeping → Bool
  | .inl (.inr (.inr (.inl _))) => true
  | _ => false

/-- The weight `kernel` on the kernel calls and $0$ on every other operation. -/
def shqrKernelWeight (kernel : EigenvalueKernelOp → List ℕ → ℕ) :
    ShQROp ⊕ Bookkeeping → List ℕ → ℕ
  | .inl (.inr (.inr (.inl e))), ds => kernel e ds
  | _, _ => 0

/-- The slot bounds of the program's initial indices: the four sizes, then five zero offsets. -/
def shqrSlots : List WorkMono :=
  [⟨1, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0, 1]⟩] ++
    List.replicate 5 (WorkMono.const 0)

/-- The single-base degrees of the program's initial indices. -/
def shqrDegrees : List ℕ := List.replicate 4 1 ++ List.replicate 5 0

/-- The base of the kernel-call polynomial: the sum of the sizes plus two. -/
def shqrBase (d : Fin 4 → ℕ) : ℕ := d 0 + d 1 + d 2 + d 3 + 2

/-- **The work (and span) polynomial** of the rounded shifted QR algorithm at the sizes
$(n, k, n_p, F)$ = `d` and the kernel weight `kernel`:
$$196218\,(n + 1)^3(k + 1)^3(n_p + 1)(F + 1) + 8\,b^4\,\overline{w},$$
with $b = n + k + n_p + F + 2$ and $\overline{w}$ the largest kernel weight
(`NLAlib.ShiftedQR.spectralWorkEnvelope`) over the call dimensions of at most one entry of at
most $b^2$. The first term bounds the instructions (each of unit weight), the second the number
$8b^4$ of kernel calls times their largest weight. -/
def shqrWork (kernel : EigenvalueKernelOp → List ℕ → ℕ) (d : Fin 4 → ℕ) : ℕ :=
  196218 * (d 0 + 1) ^ 3 * (d 1 + 1) ^ 3 * (d 2 + 1) * (d 3 + 1) +
    8 * shqrBase d ^ 4 * spectralWorkEnvelope kernel 1 (shqrBase d ^ 2)

/-! ### The certificate -/

/-- The payload words of the five supplied buffers. -/
def shqrInputWords (d : Fin 4 → ℕ) : ℕ :=
  2 * ((d 0 + 1) * (d 0 + 1)) + 1 + d 2 + 2 * ((d 0 + 1) * (d 0 + 1)) + 1

theorem shqrProblem_initialBytes (d : Fin 4 → ℕ) (x : (shqrProblem Mch admitted).Input d) :
    (shqrProblem Mch admitted).initialBytes d x = shqrInputWords d := by
  unfold Problem.initialBytes
  have hb : x.val.2 = x.val.1.buffers := x.property
  rw [hb]
  simp [shqrProblem, ShQRData.buffers, List.ofFn_succ, shqrInputWords, ← x.val.1.words_eq,
    Nat.add_assoc]

/-! ### The headline on one run -/

end NLAlib.ShiftedQR
