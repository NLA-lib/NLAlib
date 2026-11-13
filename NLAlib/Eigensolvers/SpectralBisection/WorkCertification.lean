/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.ProgramWork
public import NLAlib.Eigensolvers.SpectralBisection.WorkSpecification
public import NLAlib.Eigensolvers.SpectralBisection.StoragePolynomial

/-!
# Total spectral-bisection certification with partition-sensitive matrix work

The existing total word proof supplies execution of the fixed program. The actual counted
matrix bound and independent workspace envelope refine its resource claims on that same run.
Nonmatrix instructions retain their conservative full static charges.

## Main results

* `NLAlib.SpectralBisection.workCertifiedAlgorithm`: total output and resource certificate.
* `NLAlib.SpectralBisection.certifies_work`: certification of the explicit fixed program.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

section

variable {K : Type} [Inhabited K]

/-- The fixed dense solver is total on every admitted raw input and tape, with exact stored
word output, tape consumption and cleanup. Root sizes are at least two and natural literals
through `max n 4` decode exactly. Matrix costs are dominated by a monotone superadditive
largest-dimension function; scratch uses the independent polynomial plus finite workspace
envelope. Scalar, sampling, literal, query and structural work retain their full static charges.
The matrix-cost domination is global, including empty and all-zero dimension lists. -/
noncomputable def workCertifiedAlgorithm
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) (T : ℕ → ℕ)
    (hLit : ∀ d, domain d → IsExactNatLit dec M (max (d 0) 4))
    (hN : ∀ d, domain d → 2 ≤ d 0) (hT : Monotone T)
    (hadd : ∀ i j, T i + T j ≤ T (i + j))
    (hMatrix : ∀ o ds, matrixWork o ds ≤ T (ds.foldr max 0)) :
    Algorithm
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (workSpecification M dec mm qr domain admitted matrixWorkspace T) := by
  refine ⟨program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst), ?_⟩
  let original := manifestAlgorithm M dec mm qr domain admitted matrixWork matrixWorkspace hLit
  intro d hd x I hI τ
  obtain ⟨st, hr, _, hc, _, _, _, hgood⟩ := original.correct d hd x I hI τ
  rcases Dense.laws_functionalModel M dec (EntryCodec.pair K) mm qr
    (Dense.resources matrixWork matrixWorkspace) d x I hI with
    ⟨hS, hL, hMM, hQR, hSample, hC, hQ⟩
  have hKernel := program_kernelWeight_le_of_exec M dec mm qr
    hS hL hC hMM hQR hQ hSample d x (hLit d hd) T hT hadd
    (Dense.resources matrixWork matrixWorkspace) hr
  have hWork := Dense.work_le_of_kernelWeight_le matrixWork matrixWorkspace T hMatrix hc hKernel
  have hPeak : st.peak ≤
      (workSpecification M dec mm qr domain admitted matrixWorkspace T).scratch d :=
    (exec_static hr).2.trans
      (staticPeak_workspaceEnvelope_le matrixWork matrixWorkspace d (hN d hd))
  have hMemory : (problem (K := K) domain admitted).initialBytes d x + st.peak ≤
      (workSpecification M dec mm qr domain admitted matrixWorkspace T).memory d := by
    rw [initialBytes_problem]
    exact Nat.add_le_add_left hPeak _
  refine ⟨st, hr, hPeak, hc, hWork, ?_, hMemory, hgood⟩
  change (Dense.resources matrixWork matrixWorkspace).span st.cost ≤
    (Dense.resources (fun _ _ => 0) matrixWorkspace).work (staticBudget d) +
      (d 1 + 1) * (2 * d 2 + 11) * T (d 0)
  rw [Dense.span_eq_work]
  exact hWork

/-- Under exact bounded natural literals, admitted root sizes at least two and the declared
monotone superadditive matrix-cost domination, the explicit fixed program succeeds with
the word, storage, full instruction, work and sequential-span claims of its specification. -/
theorem certifies_work
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) (T : ℕ → ℕ)
    (hLit : ∀ d, domain d → IsExactNatLit dec M (max (d 0) 4))
    (hN : ∀ d, domain d → 2 ≤ d 0) (hT : Monotone T)
    (hadd : ∀ i j, T i + T j ≤ T (i + j))
    (hMatrix : ∀ o ds, matrixWork o ds ≤ T (ds.foldr max 0)) :
    (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).Certifies
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (workSpecification M dec mm qr domain admitted matrixWorkspace T) :=
  (workCertifiedAlgorithm M dec mm qr domain admitted matrixWork matrixWorkspace T
    hLit hN hT hadd hMatrix).correct

end

end NLAlib.SpectralBisection
