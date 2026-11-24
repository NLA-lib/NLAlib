/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Resources
public import NLAlib.Eigensolvers.Sign.Routine

/-!
# Canonical certification of capped matrix sign iteration

The raw matrix and parameter words determine the mathematical capped result. Total
execution returns exactly that packed matrix and releases scoped scratch. The certificate
bounds all calls, queries, structural instructions and payload in that same execution.
Numerical accuracy is a separate theorem about the returned mathematical quantity.

## Main results

* `NLAlib.Sign.wordSpecification` states the actual stored matrix and full resources.
* `NLAlib.Sign.signAlgorithm` certifies the fixed program under functional primitives.
* `NLAlib.Sign.certifies_signProgram` exposes the certificate for that exact program.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {K Su Sg : Type} [Inhabited K]

/-- The mathematical word result, unchanged tape position and release of all scoped
buffers, with a transparent complete syntactic manifest for the actual fixed tree. -/
noncomputable def wordSpecification (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) :
    Specification DenseOp (CmpTst ⊕ IdxTst) (problem (K := K) domain admitted) where
  budget := staticBudget
  scratch := staticPeak (Dense.resources matrixWork matrixWorkspace) signProgram
  work d := (Dense.resources matrixWork matrixWorkspace).work (staticBudget d)
  span d := (Dense.resources matrixWork matrixWorkspace).span (staticBudget d)
  memory d := 4 * (d 0 * d 0) + 2 +
    staticPeak (Dense.resources matrixWork matrixWorkspace) signProgram d
  good d x _ _ m :=
    m.store.readBlock 2 0 (2 * (d 0 * d 0)) =
      some ((EntryCodec.pair K).packFinMatrix
        (newtonSchulzSign (M.toFloatMachine dec mm qr unif normal)
          (tolerance d x) (scale d x) (d 1) (inputMatrix d x))) ∧
      m.pos = 0 ∧ m.store.length = 3

/-- Functional scalar, index, matrix and comparison contracts suffice for total execution
at every admitted raw input and cap. The distinct decoded zero and one premise makes the
matrix stopping predicate agree with its mathematical definition. No success or numerical
accuracy assumption is needed for this exact word-result certificate. -/
noncomputable def signAlgorithm (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (h01 : dec (M.lit 0) ≠ dec (M.lit 1)) :
    Algorithm
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (wordSpecification M dec mm qr unif normal domain admitted matrixWork matrixWorkspace) := by
  refine (inputs (K := K) domain admitted).algorithm
    (fun _ _ => signSpec M dec mm qr unif normal) ?_ ?_ ?_ (hmemory := ?_)
    (ht := wellTyped_signProgram matrixWork matrixWorkspace)
  · intro d hd x I hI
    rcases Dense.laws_functionalModel M dec (EntryCodec.pair K) mm qr
      (Dense.resources matrixWork matrixWorkspace) d x I hI with
      ⟨hS, hL, hMM, _, _, hC, _⟩
    exact signRoutine_meets dec mm qr unif normal hS hC hMM hL h01
  · intro d hd x _ _
    trivial
  · intro d hd x τ m' hfr hpos ys hys hrel c _
    read_outputs hys as (zs)
    have hval : zs = (EntryCodec.pair K).packFinMatrix
        (newtonSchulzSign (M.toFloatMachine dec mm qr unif normal)
          (tolerance d x) (scale d x) (d 1) (inputMatrix d x)) := by
      have h : zs = (EntryCodec.pair K).packFinMatrix
          (newtonSchulzSign (M.toFloatMachine dec mm qr unif normal)
            (tolerance d x) (scale d x) (d 1) ((EntryCodec.pair K).matrix (d 0) (d 0)
              ((EntryCodec.pair K).packFinMatrix (inputMatrix d x)))) := hrel
      rw [EntryCodec.matrix_packFinMatrix] at h
      exact h
    refine ⟨?_, hpos, by simpa [Problem.initial] using hfr.length_eq⟩
    rw [← hval]
    exact hzs
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

/-- The canonical sign certificate concerns precisely the declared fixed tree. -/
theorem certifies_signProgram (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (h01 : dec (M.lit 0) ≠ dec (M.lit 1)) :
    signProgram.Certifies
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (wordSpecification M dec mm qr unif normal domain admitted matrixWork matrixWorkspace) :=
  (signAlgorithm M dec mm qr unif normal domain admitted matrixWork matrixWorkspace
    h01).correct

/-- What the certificate states: at every admitted size, for every admitted input, every
interpretation satisfying the contracts of the model and every tape, the run of the fixed program
from the supplied buffers succeeds within the scratch, the budget, the work, the span and the
memory of the
specification, and its final memory satisfies the output condition
(`NLAlib.Ops.Inputs.Checked`). Every matrix and pair of parameters is admitted. -/
theorem sign_checked (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (h01 : dec (M.lit 0) ≠ dec (M.lit 1)) :
    (inputs (K := K) domain admitted).Checked
      (signAlgorithm M dec mm qr unif normal domain admitted matrixWork matrixWorkspace h01) :=
  (inputs (K := K) domain admitted).checked_all _

end NLAlib.Sign
