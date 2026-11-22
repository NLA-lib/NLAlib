/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.DeflationInput
public import NLAlib.Eigensolvers.ShiftedQR.DeflationProgram
public import NLAlib.Eigensolvers.ShiftedQR.DeflationRoutine

/-!
# Canonical exact deflation certificate

One fixed scalar implementation initializes the threshold from the supplied tolerance,
executes the allocating worklist, and stores the roots of a nearby matrix. The complete
resource manifest counts that actual syntax, including its local spectral-kernel calls.
The decoupling implementation is fixed when constructing the certificate; its local contract
is proved under the standard exact operation laws.

## Main results

* `NLAlib.ShiftedQR.deflationProgram`: the raw three-buffer program.
* `NLAlib.ShiftedQR.deflationSpecification`: output words and all five resource bounds.
* `NLAlib.ShiftedQR.deflationAlgorithm`: total certification from a fixed decoupling body.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- The dimensions are order minus one, Ritz depth, Ritz count, iteration cap and grid bound.
The three supplied buffers contain the matrix, five raw parameters and root-output slots. -/
def deflationProgram (D : Stmt Op Tst) : Program Op Tst 5 3 := (deflationRoutine D).close 5 3

/-- The resource manifest belongs to the actual fixed deflation tree. Resident bytes include
all supplied input and output capacity as well as the full scoped scratch peak. -/
noncomputable def deflationSpecification (D : Stmt Op Tst)
    (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ) :
    Specification Op Tst deflationProblem where
  budget := staticCost (deflationProgram D)
  scratch := staticPeak (resources kernelWork kernelWorkspace) (deflationProgram D)
  work d := (resources kernelWork kernelWorkspace).work (staticCost (deflationProgram D) d)
  span d := (resources kernelWork kernelWorkspace).span (staticCost (deflationProgram D) d)
  memory d := 2 * ((d 0 + 1) * (d 0 + 1)) + 5 + 2 * (d 0 + 1) +
    staticPeak (resources kernelWork kernelWorkspace) (deflationProgram D) d
  good d x _ _ μ := μ.pos = 0 ∧ μ.store.length = 3 ∧
    ∃ (roots : Fin (d 0 + 1) → ℂ)
      (E : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ),
      HoldsMatrix (2, 0) (Matrix.of fun i (_ : Fin 1) => roots i) μ.store ∧
      specNorm E ≤ (d 0 : ℝ) *
        (deflationInputParams d x 4 * frobNorm (deflationInputMatrix d x)) ∧
      (deflationInputMatrix d x + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)

/-- Certify one fixed decoupling implementation using only local standard exact operation
contracts. The model exposes scalar arithmetic, index operations, comparisons, bounded index
queries and the two specified spectral kernels; every other operation is explicit syntax.
Algorithm: shifted-qr (run model) -/
noncomputable def deflationAlgorithm (D : Stmt Op Tst)
    (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ)
    (hTyped : (deflationProgram D).wellTyped (resources kernelWork kernelWorkspace)
      deflationProblem.formats = true)
    (hD : ∀ (θ : ℝ) (hθ : 1 ≤ θ) (I : Interp Op Tst ℝ),
      IsScalar exactMachine I → IsIndexLit exactMachine I → IsCmp id I → IsToNat id I →
      IsEigenvalueKernels (exactRoutinesFor θ hθ) I → DecouplingContract θ D I) :
    Algorithm (model deflationProblem exactRoutines (resources kernelWork kernelWorkspace))
      (deflationSpecification D kernelWork kernelWorkspace) := by
  refine (deflationInputs.cast (deflationRoutine D) rfl rfl).algorithmAt
    (fun d x => deflationSpec (deflationInputMatrix d x) (deflationInputParams d x 0)
      (deflationInputParams d x 1) (deflationInputParams d x 2) (deflationInputParams d x 3)
      (deflationInputParams d x 4) (deflationInputs.accepts_data x).2.2.1.choose)
    (ht := hTyped) ?_ ?_ ?_ (hmemory := ?_)
  · intro d _ x I hI
    obtain ⟨hS, hL, hK, hC, hQ⟩ := laws_model exactRoutines _ d x I hI
    have hθ := (deflationInputs.accepts_data x).2.2.1.choose_spec.2.2.2.1
    have hKθ := hK.exactRoutinesFor _ hθ
    exact deflationRoutine_meets hS exactModel_exactMachine hL hQ hC hKθ D
      (hD _ hθ I hS hL hC hQ hKθ)
  · intro d _ x _
    obtain ⟨hk, hHess, -, hM⟩ := deflationInputs.accepts_data x
    exact ⟨rfl, hk, hHess, by
      simp [Routine.Domain.blocks, Routine.Domain.cast, deflationInputs, Routine.sel,
        deflationRoutine, Slot.words, Codec.complexMatrix, Codec.vector, List.ofFn_succ,
        Access.readable],
      (deflationInputs.accepts_data x).2.2.1.choose_spec, hM⟩
  · intro d _ x τ m' hfr hpos ys hys hpost c _
    obtain ⟨roots, E, rfl, hNorm, hRoots⟩ := hpost
    change m'.readBlocks [(2, 0)] [2 * (d 0 + 1)] = some _ at hys
    obtain ⟨z, zs, hz, hread, heq⟩ := Mem.readBlocks_one hys
    obtain rfl : (2, 0) = z := by simpa using hz
    obtain rfl : zs = matrixWords (Matrix.of fun i (_ : Fin 1) => roots i) := by
      simpa using heq.symm
    refine ⟨hpos.trans (Nat.zero_add 0), by simpa [Problem.initial] using hfr.length_eq,
      roots, E, ?_, hNorm, hRoots⟩
    change m'.store.readBlock 2 0 (2 * (1 * (d 0 + 1))) = some _
    rwa [Nat.one_mul]
  · intro d _ x
    exact Nat.add_le_add_right (initialBytes_deflationProblem d x).le _

/-- What the certificate states: at every admitted size, for every admitted input, every
interpretation satisfying the contracts of the model and every tape, the run of the fixed program
from the supplied buffers succeeds within the scratch, the budget, the work and the span of the
specification, and its final memory satisfies the output condition
(`NLAlib.Ops.Routine.Domain.Checked`). -/
theorem deflation_checked (D : Stmt Op Tst)
    (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ)
    (hTyped : (deflationProgram D).wellTyped (resources kernelWork kernelWorkspace)
      deflationProblem.formats = true)
    (hD : ∀ (θ : ℝ) (hθ : 1 ≤ θ) (I : Interp Op Tst ℝ),
      IsScalar exactMachine I → IsIndexLit exactMachine I → IsCmp id I → IsToNat id I →
      IsEigenvalueKernels (exactRoutinesFor θ hθ) I → DecouplingContract θ D I) :
    (deflationInputs.cast (deflationRoutine D) rfl rfl).Checked
      (deflationAlgorithm D kernelWork kernelWorkspace hTyped hD) :=
  (deflationInputs.cast (deflationRoutine D) rfl rfl).checked_all _

end NLAlib.ShiftedQR
