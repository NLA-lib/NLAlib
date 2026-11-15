/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Exact

/-!
# Forward error of the actual shifted QR output

The backward certificate supplies the stored eigenvalues of a nearby matrix. Bauer–Fike
and the raw eigenvector-conditioning hypothesis place each stored value near the input
spectrum. This is a directed inclusion: different output entries may select the same input
eigenvalue. No bijective matching, reverse coverage, or sorted ordering is claimed.

The stronger canonical certificate retains the complete original backward postcondition,
fixed program, operation model, and every resource bound.

## Main results

* `NLAlib.ShiftedQR.deflation_good_forward_error`: actual output and raw-parameter forward error.
* `NLAlib.ShiftedQR.deflationForwardSpecification`: backward and forward output guarantees.
* `NLAlib.ShiftedQR.exactForwardAlgorithm`: total certification of the unchanged scalar program.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- The Bauer–Fike consequence of the computed characteristic-polynomial root listing. -/
private theorem roots_exists_norm_sub_le {n : ℕ}
    {H E V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d roots : Fin (n + 1) → ℂ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hRoots : (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ))
    (i : Fin (n + 1)) : ∃ j, ‖d j - roots i‖ ≤ pseudoConditionNumber V * specNorm E := by
  have hm : roots i ∈ (H + E).charpoly.roots := by
    rw [hRoots, Multiset.mem_coe, List.mem_ofFn]
    exact ⟨i, rfl⟩
  obtain ⟨v, hv, heig⟩ := exists_mulVec_eq_smul_of_mem_spectrum (A := H + E)
    (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr ((Polynomial.mem_roots'.mp hm).2))
  exact exists_norm_sub_le_pseudoConditionNumber_mul_specNorm hV hHV hv heig

/-- Each actual stored output is close to an input eigenvalue. With order $N$, raw tolerance
$\delta$ and raw conditioning parameter $B$, the distance is at most
$(B/2)(N-1)\delta\|\mathbf{H}\|_{\mathsf{F}}$. This is a directed nearest-spectrum guarantee,
not a one-to-one matching. The complete backward output retains algebraic multiplicities. -/
def DeflationForwardOutput (d : Fin 5 → ℕ) (x : deflationProblem.Input d) (μ : Mem ℝ) : Prop :=
  ∃ roots : Fin (d 0 + 1) → ℂ,
    HoldsMatrix (2, 0) (Matrix.of fun i (_ : Fin 1) => roots i) μ.store ∧
    ∀ i, ∃ z : ℂ, z ∈ spectrum ℂ (x.val.1.matrix d) ∧
      ‖z - roots i‖ ≤ (vec x.val.1.parameterWords 0 / 2) *
        ((d 0 : ℝ) * (vec x.val.1.parameterWords 4 * frobNorm (x.val.1.matrix d)))

/-- The original backward postcondition and raw input hypotheses imply a forward error for
actual output words. The estimate is Bauer–Fike with the input's eigenvector condition at
most half its raw conditioning parameter. [GolubVanLoan2013, Theorem 7.2.2]. -/
theorem deflation_good_forward_error
    {kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ}
    {d : Fin 5 → ℕ} {x : deflationProblem.Input d} {tape : Tape ℝ}
    {count : Count (Op ⊕ Bookkeeping) Tst} {μ : Mem ℝ}
    (hGood : (deflationSpecification scalarDecouple kernelWork kernelWorkspace).good
      d x tape count μ) : DeflationForwardOutput d x μ := by
  obtain ⟨_, _, roots, E, hStored, hE, hRoots⟩ := hGood
  obtain ⟨V, eigen, hV, hHV, hκ, _⟩ := x.property.1.2.2.2.2.1.1
  have hListing := isEigenvalueListing_of_mul_eq_mul_diagonal
    ((Matrix.isUnit_iff_isUnit_det _).mp hV) hHV
  have hκ' : pseudoConditionNumber V ≤ vec x.val.1.parameterWords 0 / 2 := by
    linarith
  have hε : 0 ≤ (d 0 : ℝ) *
      (vec x.val.1.parameterWords 4 * frobNorm (x.val.1.matrix d)) :=
    (specNorm_nonneg E).trans hE
  refine ⟨roots, hStored, fun i => ?_⟩
  obtain ⟨j, hj⟩ := roots_exists_norm_sub_le hV hHV hRoots i
  refine ⟨eigen j, ?_, hj.trans ?_⟩
  · rw [hListing.spectrum_eq_range]
    exact ⟨j, rfl⟩
  · exact (mul_le_mul_of_nonneg_left hE (pseudoConditionNumber_nonneg V)).trans
      (mul_le_mul_of_nonneg_right hκ' hε)

/-- Add the directed forward estimate while retaining the entire backward guarantee and
all original instruction, scratch, work, span and resident-memory bounds. -/
noncomputable def deflationForwardSpecification
    (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ) :
    Specification Op Tst deflationProblem :=
  { deflationSpecification scalarDecouple kernelWork kernelWorkspace with
    good := fun d x tape count μ =>
      (deflationSpecification scalarDecouple kernelWork kernelWorkspace).good d x tape count μ ∧
        DeflationForwardOutput d x μ }

/-- Total shifted QR certification with both backward and forward error. The same fixed
scalar program runs under the same exact scalar/index/local-spectral operation model; raw
admissibility supplies every numerical premise and no successful-execution premise is added.
[GolubVanLoan2013, Theorem 7.2.2].
Algorithm: shifted-qr (run model) -/
noncomputable def exactForwardAlgorithm
    (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ) :
    Algorithm (model deflationProblem exactRoutines (resources kernelWork kernelWorkspace))
      (deflationForwardSpecification kernelWork kernelWorkspace) :=
  (exactAlgorithm kernelWork kernelWorkspace).mapPost _
    (fun _ _ _ _ _ _ hGood => ⟨hGood, deflation_good_forward_error hGood⟩)

end NLAlib.ShiftedQR
