/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.DeflationInput
public import NLAlib.Eigensolvers.ShiftedQR.DeflationProgram

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
def deflationProgram (D : Impl Op Tst) : Program Op Tst 5 3 :=
  ⟨.frame [.var 0 + .const 1, .var 1, .var 2, .var 3, .var 4]
    [⟨0, .var 5⟩, ⟨1, .var 6⟩, ⟨2, .var 7⟩] (solve D).body⟩

/-- The resource manifest belongs to the actual fixed deflation tree. Resident bytes include
all supplied input and output capacity as well as the full scoped scratch peak. -/
noncomputable def deflationSpecification (D : Impl Op Tst)
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
      specNorm E ≤ (d 0 : ℝ) * (vec x.val.1.parameterWords 4 * frobNorm (x.val.1.matrix d)) ∧
      (x.val.1.matrix d + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)

/-- Length five identifies the raw parameter list with its five decoded words. -/
theorem deflation_parameters_eq {p : List ℝ} (hp : p.length = 5) :
    p = [vec p 0, vec p 1, vec p 2, vec p 3, vec p 4] := by
  apply List.ext_getElem
  · simpa using hp
  · intro i hi hj
    have hi5 : i < 5 := by omega
    interval_cases i <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, vec] <;>
      exact (List.getD_eq_getElem p default hi).symm

/-- Initial capacity and separation follow from the raw problem's three supplied buffers. -/
theorem initial_deflation_geometry (d : Fin 5 → ℕ)
    (x : deflationProblem.Input d) :
    let μ := deflationProblem.initial d x
    μ.Live [(0, 0), (1, 0), (2, 0)] ∧
      μ.Room [(0, 0), (1, 0), (2, 0)]
        [2 * ((d 0 + 1) * (d 0 + 1)), 5, 2 * (d 0 + 1)] ∧
      μ.store.length = 3 := by
  have hs : (deflationProblem.initial d x).store =
      [x.val.1.matrixWords.map some, x.val.1.parameterWords.map some,
        List.replicate (2 * (d 0 + 1)) none] := by
    change List.ofFn x.val.2 = _
    rw [deflation_input_buffers]
    rfl
  refine ⟨?_, ?_, by simp [Problem.initial]⟩
  · simp [Mem.Live, Problem.initial]
  · simp [Mem.Room, hs, Store.len, x.property.1.1, x.property.1.2.1]

/-- Certify one fixed decoupling implementation using only local standard exact operation
contracts. The model exposes scalar arithmetic, index operations, comparisons, bounded index
queries and the two specified spectral kernels; every other operation is explicit syntax.
Algorithm: shifted-qr (run model) -/
noncomputable def deflationAlgorithm (D : Impl Op Tst)
    (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ)
    (hTyped : (deflationProgram D).wellTyped (resources kernelWork kernelWorkspace)
      deflationProblem.formats = true)
    (hD : ∀ (θ : ℝ) (hθ : 1 ≤ θ) (I : Interp Op Tst ℝ),
      IsScalar exactMachine I → IsIndexLit exactMachine I → IsCmp id I → IsToNat id I →
      IsEigenvalueKernels (exactRoutinesFor θ hθ) I → DecouplingContract θ D I) :
    Algorithm (model deflationProblem exactRoutines (resources kernelWork kernelWorkspace))
      (deflationSpecification D kernelWork kernelWorkspace) := by
  refine Algorithm.ofWp (deflationProgram D) hTyped ?_
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d _ x I hI tape
    obtain ⟨hS, hL, hK, hC, hQ⟩ := laws_model exactRoutines _ d x I hI
    rcases x.property.1 with ⟨_, hp, hk, hHess, hGlobal, hM⟩
    have hθ := hGlobal.2.2.2.1
    have hKθ := hK.exactRoutinesFor _ hθ
    obtain ⟨hl, hr, hlength⟩ := initial_deflation_geometry d x
    have hRaw := initial_deflation_parameters d x
    rw [deflation_parameters_eq hp] at hRaw
    have hw := solve_writes (tape := tape) hS exactModel_exactMachine hL hQ hC hKθ D
      (hD _ hθ I hS hL hC hQ hKθ) hl hr (by disjoint) hHess
      (initial_deflation_matrix d x) hGlobal hM hRaw
    refine (hw.in_frame ?_ rfl hl).wp ?_
    · simp [Program.environment, List.ofFn_succ, IExp.evalList,
        IExp.eval, hk]
    · intro μ' hfr ⟨hpos, hOutput⟩ c _
      exact ⟨hpos, hfr.length_eq.trans hlength, hOutput⟩
  · intro d _ x
    rw [initialBytes_deflationProblem]
    exact le_rfl

end NLAlib.ShiftedQR
