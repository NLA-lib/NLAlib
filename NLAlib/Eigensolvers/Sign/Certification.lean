/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Resources
public import NLAlib.Eigensolvers.Sign.Solve

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
  refine Algorithm.ofWp fixedProgram (wellTyped_fixedProgram matrixWork matrixWorkspace)
    ?_ (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ => le_rfl) ?_
  · intro d hd x I hI τ
    rcases Dense.laws_functionalModel M dec (EntryCodec.pair K) mm qr
      (Dense.resources matrixWork matrixWorkspace) d x I hI with
      ⟨hS, hL, hMM, _, _, hC, _⟩
    rcases initial_geometry d x with ⟨hl, hAP, hRoom, hLength⟩
    have hr := writes_program dec mm qr unif normal hS hC hMM hL
      (τ := τ) (m := (problem (K := K) domain admitted).initial d x)
      (n := d 0) (cap := d 1) (a := (0, 0)) (par := (1, 0)) (x := (2, 0))
      (inputMatrix d x) (vec x.val.1.2 0) (vec x.val.1.2 1) h01 hl hAP
      (initial_matrix d x) (initial_parameters d x) hRoom.1
    apply hr.wp
    intro ν hfr h c _
    have hFinalLength : ν.store.length = 3 := hfr.length_eq.trans hLength
    exact ⟨h.2, h.1, hFinalLength⟩
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
