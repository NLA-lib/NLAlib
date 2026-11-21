/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.RoutineProblem
public import NLAlib.Eigensolvers.Deflation.Routine
public import NLAlib.Ops.Profiles.Dense
public import NLAlib.Ops.Certification

/-!
# Canonical output and resource certificate for randomized deflation

One fixed program receives a raw square matrix and empty output capacity. It consumes
exactly its square Gaussian word sample, returns the actual selected QR columns and releases
all four scratch matrices. Its complete resource claims describe that same execution.

## Main results

* `NLAlib.Deflation.problem` supplies only raw input and output capacity.
* `NLAlib.Deflation.deflateProgram` fixes the implementation before sizes or data.
* `NLAlib.Deflation.wordSpecification` specifies its stored sample-dependent output.
* `NLAlib.Deflation.deflateAlgorithm` proves total output and resource correctness.
-/

@[expose] public section

namespace NLAlib.Deflation

open Ops

variable {K : Type} [Inhabited K]

/-- The admitted inputs of the deflation: at the sizes of `domain`, every square matrix of
complex pairs, held by the first operand as its packed words; the block of the requested basis
columns is blank. -/
def inputs (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) :
    (deflateRoutine (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).Domain K 2 2 where
  valid := domain
  In d := Matrix (Fin (d 0)) (Fin (d 0)) (K × K)
  accepts _ _ := True
  slot d := ![.stored (Codec.matrix (EntryCodec.pair K) (d 0) (d 0)) id,
    .blank (2 * (d 0 * d 1))]
  fits := by
    intro d i p hp
    fin_cases i <;> (
      have hport := Option.some.inj hp
      subst hport
      constructor <;>
        simp [Slot.len, Slot.held, Access.readable, Codec.matrix, EntryCodec.pair,
          List.ofFn_succ, Nat.mul_comm])
  faithful d x y _ h := (Codec.matrix (EntryCodec.pair K) (d 0) (d 0)).encode_injective (by
    have h0 := h 0
    simpa only [Slot.input, Matrix.cons_val_zero, Option.some.injEq, id] using h0)
  admitted := admitted
  inhabited _ _ := ⟨fun _ _ => default, trivial⟩

/-- The projector, packed in the first buffer, and blank capacity for the requested basis
columns: the problem of the deflation. -/
abbrev problem (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem K 2 2 :=
  (inputs (K := K) domain admitted).problem

/-- The entire sampled projection and QR implementation is one fixed dense program. -/
def deflateProgram : Program DenseOp (CmpTst ⊕ IdxTst) 2 2 :=
  (deflateRoutine (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).close 2 2

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The matrix of an input of the problem. -/
abbrev inputMatrix (d : Fin 2 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    Matrix (Fin (d 0)) (Fin (d 0)) (K × K) := x.val.1

/-- Every supplied input and output slot contributes to resident payload. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    (problem (K := K) domain admitted).initialBytes d x =
      2 * (d 0 * d 0) + 2 * (d 0 * d 1) := by
  refine ((inputs (K := K) domain admitted).initialBytes_eq x).trans ?_
  simp [inputs, Slot.len, Codec.matrix, EntryCodec.pair, List.ofFn_succ]
  ring

/-- The full static manifest includes all sampling, copying, kernels and core instructions. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) :
    Count (DenseOp ⊕ Bookkeeping) (CmpTst ⊕ IdxTst) := staticCost deflateProgram d

/-- The actual sampled QR columns, exact sample advance and cleanup, with transparent
dimension-only full resource bounds. Column selection is admitted only when rank ≤ size. -/
noncomputable def wordSpecification (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) :
    Specification DenseOp (CmpTst ⊕ IdxTst) (problem (K := K) domain admitted) where
  budget := staticBudget
  scratch := staticPeak (Dense.resources matrixWork matrixWorkspace) deflateProgram
  work d := (Dense.resources matrixWork matrixWorkspace).work (staticBudget d)
  span d := (Dense.resources matrixWork matrixWorkspace).span (staticBudget d)
  memory d := 2 * (d 0 * d 0) + 2 * (d 0 * d 1) +
    staticPeak (Dense.resources matrixWork matrixWorkspace) deflateProgram d
  good d x tape _ m := ∃ hrank : d 1 ≤ d 0,
    m.store.readBlock 1 0 (2 * (d 0 * d 1)) =
      some ((EntryCodec.pair K).packFinMatrix
        ((qr (mm (inputMatrix d x) (sampleMatrix (d 0) 0 tape))).1.submatrix id
          (Fin.castLE hrank))) ∧ m.pos = 2 * (d 0 * d 0) ∧ m.store.length = 2

/-- Primitive functional contracts and the requested-rank bound imply total canonical
deflation with the exact sample-dependent stored result and every resource bound. Numerical
accuracy and a tape distribution are separate mathematical assumptions about that result. -/
noncomputable def deflateAlgorithm (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (hRank : ∀ d, domain d → d 1 ≤ d 0) :
    Algorithm
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (wordSpecification mm qr domain admitted matrixWork matrixWorkspace) := by
  refine (inputs (K := K) domain admitted).algorithm (fun _ _ => deflateSpec mm qr)
    ?_ ?_ ?_ (hmemory := ?_)
  · intro d hd x I hI
    rcases Dense.laws_functionalModel M dec (EntryCodec.pair K) mm qr
      (Dense.resources matrixWork matrixWorkspace) d x I hI with
      ⟨hS, _, hMM, hQR, hSample, _, _⟩
    exact deflateRoutine_meets hS hSample hMM hQR
  · intro d hd x _ _
    exact hRank d hd
  · intro d hd x tape m' hfr hpos ys hys hrel c _
    read_outputs hys as (zs)
    obtain ⟨hrank, hval⟩ : ∃ hrank : d 1 ≤ d 0, zs = (EntryCodec.pair K).packFinMatrix
        ((qr (mm ((EntryCodec.pair K).matrix (d 0) (d 0)
            ((EntryCodec.pair K).packFinMatrix (inputMatrix d x)))
          (sampleMatrix (d 0) 0 tape))).1.submatrix id (Fin.castLE hrank)) := hrel
    rw [EntryCodec.matrix_packFinMatrix] at hval
    refine ⟨hrank, ?_, hpos.eq_of_start rfl, by simpa [Problem.initial] using hfr.length_eq⟩
    rw [← hval]
    exact hzs
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Deflation
