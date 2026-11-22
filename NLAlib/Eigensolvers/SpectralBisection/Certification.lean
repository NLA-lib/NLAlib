/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Specification
public import NLAlib.Eigensolvers.SpectralBisection.Solve

/-!
# Certification from actual supplied word buffers

The fixed dense program has total output and resource certification for every admitted raw
input and tape. Its problem supplies a packed matrix, three scalar words and empty output
capacity. Primitive contracts and independent dimension-only resource bounds are explicit.

## Main results

* `NLAlib.SpectralBisection.initial_problem_geometry`: actual initial capacities and separation.
* `NLAlib.SpectralBisection.boundedBisectionAlgorithm`: independent output and resource claims.
* `NLAlib.SpectralBisection.bisectionAlgorithm`: full syntactic manifest certification.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {K : Type} [Inhabited K] {domain : (Fin 3 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The four supplied buffers are live and separated, and both uninitialized output blocks
have their declared capacities. Every fact follows from the construction of the problem. -/
theorem initial_problem_geometry (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    let μ := (problem (K := K) domain admitted).initial d x
    μ.Live [(0, 0), (1, 0), (2, 0), (3, 0)] ∧
      Fp.Apart [(0, 0), (1, 0), (2, 0), (3, 0)]
        [2 * (d 0 * d 0), 3, 2 * (d 0 * d 0), d 0] ∧
      μ.Room [(2, 0), (3, 0)] [2 * (d 0 * d 0), d 0] ∧
      μ.store.length = 4 ∧ μ.pos = 0 := by
  dsimp only
  refine ⟨?_, ?_, (inputs (K := K) domain admitted).room_initial x, ?_, rfl⟩
  · exact
      Problem.live_slots (P := problem (K := K) domain admitted) d x
  · disjoint
  · simp [Problem.initial]

/-- Transparent full-tree count, scratch, work, span and resident-capacity declarations for
the fixed dense program. Matrix operation costs and workspace come from the supplied profile. -/
noncomputable def manifestSpecification (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) :
    Specification DenseOp (CmpTst ⊕ IdxTst) (problem (K := K) domain admitted) :=
  let R := Dense.resources matrixWork matrixWorkspace
  let p := bisectionProgram (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)
  wordSpecification M dec mm qr domain admitted staticBudget
    (staticPeak R p) (fun d => R.work (staticBudget d)) (fun d => R.span (staticBudget d))
    (fun d => 4 * (d 0 * d 0) + d 0 + 3 + staticPeak R p d)

/-- Canonical total certification for the fixed dense program. Bounded natural literals are
exact on every admitted dimension. The five independent resource claims refer to the same
fixed tree and supplied resource profile; no execution or whole-program hypothesis is assumed. -/
noncomputable def boundedBisectionAlgorithm (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (budget : (Fin 3 → ℕ) → Count (DenseOp ⊕ Bookkeeping) (CmpTst ⊕ IdxTst))
    (scratch work span memory : (Fin 3 → ℕ) → ℕ)
    (hLit : ∀ d, domain d → IsExactNatLit dec M (max (d 0) 4))
    (hCost : ∀ d, domain d → staticBudget d ≤ budget d)
    (hScratch : ∀ d, domain d → staticPeak (Dense.resources matrixWork matrixWorkspace)
      (bisectionProgram (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)) d ≤ scratch d)
    (hWork : ∀ d, domain d → (Dense.resources matrixWork matrixWorkspace).work (budget d) ≤ work d)
    (hSpan : ∀ d, domain d → (Dense.resources matrixWork matrixWorkspace).span (budget d) ≤ span d)
    (hMemory : ∀ d, domain d → 4 * (d 0 * d 0) + d 0 + 3 + scratch d ≤ memory d) :
    Algorithm
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (wordSpecification M dec mm qr domain admitted budget scratch work span memory) := by
  refine (inputs (K := K) domain admitted).algorithm
    (fun d x => bisectionSpec M dec mm qr (x.2 0) (x.2 1) (x.2 2) x.1)
    (ht := wellTyped_bisectionProgram matrixWork matrixWorkspace) ?_ ?_ ?_ hCost hScratch hWork
    hSpan ?_
  · intro d hd x I hI
    rcases Dense.laws_functionalModel M dec (EntryCodec.pair K) mm qr
      (Dense.resources matrixWork matrixWorkspace) d x I hI with
      ⟨hS, hL, hMM, hQR, hSample, hC, hQ⟩
    exact bisectionRoutine_meets M dec mm qr _ _ _ _ hS hL hC hMM hQR hQ hSample
  · intro d hd x _ τ
    exact ⟨rfl, hLit d hd, rfl, rfl⟩
  · intro d hd x τ ν hfr hpos ys hys hpost c _
    rcases initial_problem_geometry d x with ⟨-, -, -, hLength, -⟩
    have hFinalLength : ν.store.length = 4 := hfr.length_eq.trans hLength
    change ν.readBlocks [(2, 0), (3, 0)] [2 * (d 0 * d 0), d 0] = some ys at hys
    obtain ⟨z, w, us, ds, -, -, -, rfl⟩ := Mem.readBlocks_two hys
    obtain ⟨rfl, rfl⟩ : us = _ ∧ ds = _ := hpost
    refine ⟨storesResult_iff_readBlocks.mpr ?_, hpos.trans (Nat.zero_add _), hFinalLength⟩
    simpa [resultOperands, resultLengths] using hys
  · intro d hd x
    change (problem (K := K) domain admitted).initialBytes d x + scratch d ≤ memory d
    rw [initialBytes_problem]
    exact hMemory d hd

/-- The transparent syntactic manifest, with work/span and memory evaluated on that same
manifest and profile, has a canonical certificate for every admitted raw input and tape. -/
noncomputable def bisectionAlgorithm (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (hLit : ∀ d, domain d → IsExactNatLit dec M (max (d 0) 4)) :
    Algorithm
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (manifestSpecification M dec mm qr domain admitted matrixWork matrixWorkspace) := by
  apply boundedBisectionAlgorithm M dec mm qr domain admitted matrixWork matrixWorkspace
    staticBudget _ _ _ _ hLit
  all_goals intros; exact le_rfl

/-- The fixed spectral-bisection program satisfies its actual word output specification and
all transparent manifest bounds under the generated dense functional model. -/
theorem certifies_manifest (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (hLit : ∀ d, domain d → IsExactNatLit dec M (max (d 0) 4)) :
    (bisectionProgram (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).Certifies
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (manifestSpecification M dec mm qr domain admitted matrixWork matrixWorkspace) :=
  (bisectionAlgorithm M dec mm qr domain admitted matrixWork matrixWorkspace hLit).correct

/-- What the certificate states: at every admitted size, for every admitted input, every
interpretation satisfying the contracts of the model and every tape, the run of the fixed program
from the supplied buffers succeeds within the scratch, the budget, the work, the span and the
memory of the
specification, and its final memory satisfies the output condition
(`NLAlib.Ops.Routine.Domain.Checked`). The accuracy of the stored diagonalization holds with
probability over the draws: `NLAlib.SpectralBisection.countedBisectionClaim`. -/
theorem bisection_checked (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (hLit : ∀ d, domain d → IsExactNatLit dec M (max (d 0) 4)) :
    (inputs (K := K) domain admitted).Checked
      (bisectionAlgorithm M dec mm qr domain admitted matrixWork matrixWorkspace hLit) :=
  (inputs (K := K) domain admitted).checked_all _

end NLAlib.SpectralBisection
