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
* `NLAlib.Sign.certifiedAlgorithm` certifies the fixed program under functional primitives.
* `NLAlib.Sign.certifies_fixedProgram` exposes the certificate for that exact program.
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
  scratch := staticPeak (Dense.resources matrixWork matrixWorkspace) fixedProgram
  work d := (Dense.resources matrixWork matrixWorkspace).work (staticBudget d)
  span d := (Dense.resources matrixWork matrixWorkspace).span (staticBudget d)
  memory d := 4 * (d 0 * d 0) + 2 +
    staticPeak (Dense.resources matrixWork matrixWorkspace) fixedProgram d
  good d x _ _ m :=
    m.store.readBlock 2 0 (2 * (d 0 * d 0)) =
      some ((EntryCodec.pair K).packFinMatrix
        (newtonSchulzSign (M.toFloatMachine dec mm qr unif normal)
          (vec x.val.1.2 0) (vec x.val.1.2 1) (d 1) (inputMatrix d x))) ∧
      m.pos = 0 ∧ m.store.length = 3

/-- Functional scalar, index, matrix and comparison contracts suffice for total execution
at every admitted raw input and cap. The distinct decoded zero and one premise makes the
matrix stopping predicate agree with its mathematical definition. No success or numerical
accuracy assumption is needed for this exact word-result certificate. -/
noncomputable def certifiedAlgorithm (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (h01 : dec (M.lit 0) ≠ dec (M.lit 1)) :
    Algorithm
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (wordSpecification M dec mm qr unif normal domain admitted matrixWork matrixWorkspace) := by
  refine Routine.algorithm (r := 2) (b := 3) (signRoutine (Has.inj MatrixOp.mul))
    (fun _ _ => signSpec M dec mm qr unif normal)
    (fun d x => [(EntryCodec.pair K).packFinMatrix (inputMatrix d x),
      [vec x.val.1.2 0, vec x.val.1.2 1]]) (ht := wellTyped_fixedProgram matrixWork matrixWorkspace)
    ?_ ?_ ?_ (hmemory := ?_)
  · intro d hd x I hI
    rcases Dense.laws_functionalModel M dec (EntryCodec.pair K) mm qr
      (Dense.resources matrixWork matrixWorkspace) d x I hI with
      ⟨hS, hL, hMM, _, _, hC, _⟩
    exact signRoutine_meets dec mm qr unif normal hS hC hMM hL h01
  · intro d hd x
    rcases initial_geometry d x with ⟨-, -, hRoom, -⟩
    exact ⟨Mem.readBlocks_of_cons (initial_matrix d x)
        (Mem.readBlocks_of_cons (initial_parameters d x) rfl), fun _ => trivial, hRoom⟩
  · intro d hd x τ m' hfr hpos ys hys hrel c _
    rcases initial_geometry d x with ⟨-, -, -, hLength⟩
    read_outputs hys as (zs)
    have hval : zs = (EntryCodec.pair K).packFinMatrix
        (newtonSchulzSign (M.toFloatMachine dec mm qr unif normal)
          (vec x.val.1.2 0) (vec x.val.1.2 1) (d 1) (inputMatrix d x)) := by
      have h : zs = (EntryCodec.pair K).packFinMatrix
          (newtonSchulzSign (M.toFloatMachine dec mm qr unif normal)
            (vec [vec x.val.1.2 0, vec x.val.1.2 1] 0) (vec [vec x.val.1.2 0, vec x.val.1.2 1] 1)
            (d 1) ((EntryCodec.pair K).matrix (d 0) (d 0)
              ((EntryCodec.pair K).packFinMatrix (inputMatrix d x)))) := hrel
      rw [EntryCodec.matrix_packFinMatrix] at h
      exact h
    refine ⟨?_, hpos, hfr.length_eq.trans hLength⟩
    rw [← hval]
    exact hzs
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

/-- The canonical sign certificate concerns precisely the declared fixed tree. -/
theorem certifies_fixedProgram (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K)
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (h01 : dec (M.lit 0) ≠ dec (M.lit 1)) :
    fixedProgram.Certifies
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (wordSpecification M dec mm qr unif normal domain admitted matrixWork matrixWorkspace) :=
  (certifiedAlgorithm M dec mm qr unif normal domain admitted matrixWork matrixWorkspace
    h01).correct

end NLAlib.Sign
