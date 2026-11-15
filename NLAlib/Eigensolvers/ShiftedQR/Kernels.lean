/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Storage
public import NLAlib.Matrix.QRIteration.Ritz
public import NLAlib.Matrix.Spectral.EigenvalueListing
public import NLAlib.Ops.Profiles.Dense
public import NLAlib.Ops.Logic.Functional

/-!
# Local exact eigenvalue kernels for shifted QR

Ritz extraction and small-matrix eigenvalue listing operate on the actual interleaved real
words of one matrix. Their assumptions concern these local routines alone. Scalar arithmetic,
dimension literals, comparisons and index conversion are realized on the same interpretation.
The reference routines use exact characteristic-polynomial roots with multiplicity.

## Main results

* `NLAlib.ShiftedQR.KernelRoutines`: local numerical obligations for the two kernels.
* `NLAlib.ShiftedQR.exactRoutines`: a simultaneous exact mathematical realization.
* `NLAlib.ShiftedQR.model`: the joint access model with explicit resource charges.
* `NLAlib.ShiftedQR.laws_model`: its scalar, index, kernel and query contracts.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- Two local spectral kernels; neither primitive performs an iteration or a shift search. -/
inductive EigenvalueKernelOp where
  /-- Trailing-block Ritz values: dimensions `[N,k]`, one `2*N*N`-word input, `2*k` outputs. -/
  | ritz
  /-- All eigenvalues with multiplicity: dimensions `[N]`, `2*N*N` input words, `2*N` outputs. -/
  | smallEig
  deriving DecidableEq

/-- The closed operation collection used by the scalar shifted-QR implementation. -/
abbrev Op := ScalarOp ⊕ (IndexOp ⊕ EigenvalueKernelOp)

instance : Has IndexOp Op := Has.sumRight _ _ _ inferInstance

instance : Has EigenvalueKernelOp Op := Has.sumRight _ _ _ inferInstance

/-- Comparisons and natural-index conversion have distinct query names. -/
abbrev Tst := CmpTst ⊕ IdxTst

/-- Local routines and their mathematical obligations. Ritz optimality is required only for
positive order within a Hessenberg matrix; eigenvalue listings retain algebraic multiplicity.
No execution, convergence or whole-algorithm conclusion is assumed here. -/
structure KernelRoutines (θ : ℝ) where
  /-- A list of Ritz values of the requested order. -/
  ritz : ∀ (N _k : ℕ), Matrix (Fin N) (Fin N) ℂ → List ℂ
  /-- The requested output size is respected even outside the optimality domain. -/
  length_ritz : ∀ N k H, (ritz N k H).length = k
  /-- Local Ritz optimality on a Hessenberg matrix, for orders that fit its trailing block. -/
  optimal : ∀ n k (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
    IsUpperHessenberg H → 0 < k → k ≤ n →
    IsOptimalRitzValues θ H (ritz (n + 1) k H)
  /-- The small-matrix kernel returns a family of exactly the matrix's dimension. -/
  smallEig : ∀ N, Matrix (Fin N) (Fin N) ℂ → Fin N → ℂ
  /-- All roots are returned with algebraic multiplicity. -/
  listing : ∀ N H, IsEigenvalueListing H (smallEig N H)

/-- The exact reference Ritz extraction. Empty matrices have no optimality requirement. -/
noncomputable def exactRitz : ∀ (N _k : ℕ), Matrix (Fin N) (Fin N) ℂ → List ℂ
  | 0, k, _ => List.replicate k 0
  | _ + 1, k, H => ritzValues k H

/-- Exact reference routines jointly witness the two local numerical contracts. -/
noncomputable def exactRoutines : KernelRoutines 1 where
  ritz := exactRitz
  length_ritz N k H := by
    cases N with
    | zero => simp [exactRitz]
    | succ n => exact length_ritzValues k H
  optimal _ _ H hH hk hkn := hH.isOptimalRitzValues_one_ritzValues hk hkn
  smallEig N H := Classical.choose (exists_isEigenvalueListing H)
  listing N H := Classical.choose_spec (exists_isEigenvalueListing H)

/-- The same exact root routines meet every Ritz factor at least one. Only the proof of
optimality changes; the actual input/output functions and root ordering remain identical. -/
noncomputable def exactRoutinesFor (θ : ℝ) (hθ : 1 ≤ θ) : KernelRoutines θ where
  ritz := exactRoutines.ritz
  length_ritz := exactRoutines.length_ritz
  optimal n k H hH hk hkn := by
    change IsOptimalRitzValues θ H (ritzValues k H)
    have ho := hH.isOptimalRitzValues_one_ritzValues hk hkn
    unfold IsOptimalRitzValues at ho ⊢
    exact ho.trans (pow_le_pow_left₀
      (mul_nonneg zero_le_one (hessenbergPotential_nonneg _ _))
      (mul_le_mul_of_nonneg_right hθ (hessenbergPotential_nonneg _ _)) _)
  smallEig := exactRoutines.smallEig
  listing := exactRoutines.listing

/-- The exact local block function of the Ritz kernel at the actual call dimensions. -/
def ritzFn {θ : ℝ} (K : KernelRoutines θ) : BlockFn ℝ where
  nd := 2
  inLens d := [2 * (d.headD 0 * d.headD 0)]
  outLens d := [2 * (d.getD 1 0)]
  fn d _ xs := match d, xs with
    | [N, k], [as] => some [matrixWords (listColumn (K.ritz N k (matrixOfWords N as)) k)]
    | _, _ => none

/-- The exact local block function of the small eigenvalue-listing kernel. -/
def smallEigFn {θ : ℝ} (K : KernelRoutines θ) : BlockFn ℝ where
  nd := 1
  inLens d := [2 * (d.headD 0 * d.headD 0)]
  outLens d := [2 * (d.headD 0)]
  fn d _ xs := match d, xs with
    | [N], [as] =>
      some [matrixWords (Matrix.of fun i (_ : Fin 1) => K.smallEig N (matrixOfWords N as) i)]
    | _, _ => none

/-- The output column recovers exactly the Ritz list, without truncation or extra roots. -/
theorem KernelRoutines.ofFn_listColumn {θ : ℝ} (K : KernelRoutines θ)
    (N k : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) :
    List.ofFn (fun i => listColumn (K.ritz N k H) k i 0) = K.ritz N k H := by
  apply List.ext_getElem
  · simp [K.length_ritz]
  · intro i hi hi'
    simp only [List.getElem_ofFn, listColumn]
    exact List.getD_eq_getElem _ _ hi'

/-- Every primitive has its own local word function; no whole-program oracle is present. -/
noncomputable def functions {θ : ℝ} (K : KernelRoutines θ) : Op → BlockFn ℝ
  | .inl o => exactMachine.fn o
  | .inr (.inl _) => exactMachine.indexFn
  | .inr (.inr .ritz) => ritzFn K
  | .inr (.inr .smallEig) => smallEigFn K

/-- Each supplied spectral routine is applied to precisely the decoded input matrix. -/
def IsEigenvalueKernels {O Q : Type} [Has EigenvalueKernelOp O] {θ : ℝ}
    (K : KernelRoutines θ) (I : Interp O Q ℝ) : Prop :=
  I.IsFn .total (Has.inj EigenvalueKernelOp.ritz) (ritzFn K) AnyOperands ∧
  I.IsFn .total (Has.inj EigenvalueKernelOp.smallEig) (smallEigFn K) AnyOperands

/-- An interpretation of the exact routines already satisfies every admissible Ritz factor;
no operation or interpretation is replaced when the parameter factor changes. -/
theorem IsEigenvalueKernels.exactRoutinesFor {O Q : Type} [Has EigenvalueKernelOp O]
    {I : Interp O Q ℝ} (hI : IsEigenvalueKernels exactRoutines I) (θ : ℝ) (hθ : 1 ≤ θ) :
    IsEigenvalueKernels (exactRoutinesFor θ hθ) I := hI

/-- A Ritz call writes the requested list of the supplied local routine applied to the actual
input matrix. Input/output overlap is permitted because the input block is read first. -/
theorem writes_ritz {O Q : Type} [Has EigenvalueKernelOp O] {θ : ℝ}
    {K : KernelRoutines θ} {I : Interp O Q ℝ} {τ : Tape ℝ} {ρ : Env} {μ : Mem ℝ}
    (hI : IsEigenvalueKernels K I) {ds : List IExp} {ins outs : List Operand}
    {N k : ℕ} {a b : ℕ × ℕ} {H : Matrix (Fin N) (Fin N) ℂ}
    (hd : IExp.evalList ρ.idx ds = some [N, k])
    (ha : Operand.evalList ρ ins = some [a]) (hb : Operand.evalList ρ outs = some [b])
    (hl : μ.Live [a, b]) (hH : HoldsMatrix a H μ.store)
    (hB : b.2 + 2 * k ≤ μ.store.len b.1) :
    Writes .total I τ (.call (Has.inj EigenvalueKernelOp.ritz) ds ins outs) ρ
      (Store.inBlock b.1 b.2 (2 * k))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix b (listColumn (K.ritz N k H) k) μ'.store) μ := by
  simpa only [HoldsMatrix, Nat.one_mul, ritzFn, Nat.add_zero] using
    (writes_call_fn1 hI.1 (xs := [matrixWords H]) (l := 2 * k) hd ha hb rfl rfl trivial hl
      (by simp [Mem.readBlocks, ritzFn, show μ.store.readBlock a.1 a.2 (2 * (N * N)) =
        some (matrixWords H) from hH])
      (by simp [ritzFn]) (by simp) hB)

/-- A small-eigenvalue call writes every characteristic-polynomial root with multiplicity of
its actual stored matrix. The local listing law belongs to the supplied routine. -/
theorem writes_smallEig {O Q : Type} [Has EigenvalueKernelOp O] {θ : ℝ}
    {K : KernelRoutines θ} {I : Interp O Q ℝ} {τ : Tape ℝ} {ρ : Env} {μ : Mem ℝ}
    (hI : IsEigenvalueKernels K I) {ds : List IExp} {ins outs : List Operand}
    {N : ℕ} {a b : ℕ × ℕ} {H : Matrix (Fin N) (Fin N) ℂ}
    (hd : IExp.evalList ρ.idx ds = some [N])
    (ha : Operand.evalList ρ ins = some [a]) (hb : Operand.evalList ρ outs = some [b])
    (hl : μ.Live [a, b]) (hH : HoldsMatrix a H μ.store)
    (hB : b.2 + 2 * N ≤ μ.store.len b.1) :
    Writes .total I τ (.call (Has.inj EigenvalueKernelOp.smallEig) ds ins outs) ρ
      (Store.inBlock b.1 b.2 (2 * N))
      (fun μ' => μ'.pos = μ.pos ∧
        HoldsMatrix b (Matrix.of fun i (_ : Fin 1) => K.smallEig N H i) μ'.store) μ := by
  simpa only [HoldsMatrix, Nat.one_mul, smallEigFn, Nat.add_zero] using
    (writes_call_fn1 hI.2 (xs := [matrixWords H]) (l := 2 * N)
      (y := matrixWords (Matrix.of fun i (_ : Fin 1) => K.smallEig N H i))
      hd ha hb rfl rfl trivial hl
      (by simp [Mem.readBlocks, smallEigFn, show μ.store.readBlock a.1 a.2 (2 * (N * N)) =
        some (matrixWords H) from hH])
      (by simp [smallEigFn]) (by rw [length_matrixWords, Nat.one_mul]) hB)

/-- One interpretation supplies arithmetic, size literals and the two local kernels together. -/
noncomputable def interp {θ : ℝ} (K : KernelRoutines θ) : Interp Op Tst ℝ where
  call o := (Interp.ofFns (Tst := Tst) (functions K)).call o
  test := cmpInterp.test
  index := cmpInterp.index

/-- Operand formats count actual real words. Spectral operations each read and write one block. -/
def signature : Op → OperandSignature
  | .inl (.lit _) | .inr (.inl _) => ⟨[], [.cell]⟩
  | .inl .add | .inl .sub | .inl .mul | .inl .div => ⟨[.cell, .cell], [.cell]⟩
  | .inl .neg | .inl .sqrt | .inl .copy => ⟨[.cell], [.cell]⟩
  | .inr (.inr _) => ⟨[.cell], [.cell]⟩

/-- Explicit sequential costs. Kernel work and workspace depend on the actual call dimensions;
scalar, query and structural instructions cost one unit, with no hidden spectral work. -/
def resources (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ) :
    ResourceModel Op Tst where
  formats := [.cell]
  operation := signature
  testInputs q := match q with | .inl c => c.lens.map (fun _ => .cell) | .inr _ => []
  indexInputs q := match q with | .inl _ => [] | .inr _ => [.cell]
  workspace o d := match o with | .inr (.inr k) => kernelWorkspace k d | _ => 0
  queryWorkspace _ _ := 0
  operationWork o d := match o with | .inr (.inr k) => kernelWork k d | _ => 1
  operationSpan o d := match o with | .inr (.inr k) => kernelWork k d | _ => 1
  queryWork _ _ := 1
  querySpan _ _ := 1
  coreWork _ _ := 1
  coreSpan _ _ := 1
  operation_span_le _ _ := le_rfl
  query_span_le _ _ := le_rfl
  core_span_le _ _ := le_rfl

/-- Joint local contracts for the reference interpretation on the same real-word memory. -/
theorem interp_contracts {θ : ℝ} (K : KernelRoutines θ) :
    IsScalar exactMachine (interp K) ∧ IsIndexLit exactMachine (interp K) ∧
      IsEigenvalueKernels K (interp K) ∧ IsCmp id (interp K) ∧ IsToNat id (interp K) := by
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro o
    exact Interp.ofFns_isFn (Tst := Tst) (functions K) .total (.inl o) AnyOperands
  · exact Interp.ofFns_isFn (Tst := Tst) (functions K) .total (.inr (.inl .lit)) AnyOperands
  · exact Interp.ofFns_isFn (Tst := Tst) (functions K) .total (.inr (.inr .ritz)) AnyOperands
  · exact Interp.ofFns_isFn (Tst := Tst) (functions K) .total (.inr (.inr .smallEig)) AnyOperands
  · intro c d a m xs h
    change (m.readBlocks a c.lens).map (c.fn id) = _
    rw [h]
    rfl
  · intro a m xs h
    change ((m.readBlocks a (a.map fun _ => 1)).bind fun xs => toNatFn id xs.flatten) = _
    rw [h]
    rfl

/-- Exact arithmetic and local numerical kernels with declared costs, jointly realizable at
all admitted inputs. Local Ritz/eigenvalue assumptions are carried by the supplied routines. -/
noncomputable def model {r b : ℕ} (P : Problem ℝ r b) {θ : ℝ} (K : KernelRoutines θ)
    (R : ResourceModel Op Tst) : AccessModel Op Tst P where
  word := 0
  operation _ _ o := ((functions K) o).rel.spec AnyOperands
  query _ _ := Dense.queryContract id
  resources := R
  realize _ _ _ := by
    refine ⟨interp K, ?_, ?_⟩
    · intro o
      exact Interp.ofFns_isFn (Tst := Tst) (functions K) .total o AnyOperands
    · intro q
      rcases q with c | q
      · exact ⟨fun d a m xs h => (interp_contracts K).2.2.2.1 c d a m xs h,
          fun _ _ => rfl⟩
      · cases q
        exact ⟨fun _ _ _ => rfl,
          fun a m xs h => (interp_contracts K).2.2.2.2 a m xs h⟩

/-- The declared model exposes exactly the local contracts used by scalar program proofs. -/
theorem laws_model {r b : ℕ} {P : Problem ℝ r b} {θ : ℝ} (K : KernelRoutines θ)
    (R : ResourceModel Op Tst) (d : Fin r → ℕ) (x : P.Input d) (I : Interp Op Tst ℝ)
    (h : (model P K R).contracts d x I) :
    IsScalar exactMachine I ∧ IsIndexLit exactMachine I ∧ IsEigenvalueKernels K I ∧
      IsCmp id I ∧ IsToNat id I := by
  refine ⟨fun o => h.1 (.inl o), h.1 (.inr (.inl .lit)),
    ⟨h.1 (.inr (.inr .ritz)), h.1 (.inr (.inr .smallEig))⟩, ?_, ?_⟩
  · intro c ds a m xs hr
    exact (h.2 (.inl c)).1 ds a m xs hr
  · intro a m xs hr
    exact (h.2 (.inr .toNat)).2 a m xs hr

end NLAlib.ShiftedQR
