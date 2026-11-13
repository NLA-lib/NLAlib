/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Deflation.Execution
public import NLAlib.Ops.Profiles.Dense
public import NLAlib.Ops.Certification

/-!
# Canonical output and resource certificate for randomized deflation

One fixed program receives a raw square matrix and empty output capacity. It consumes
exactly its square Gaussian word sample, returns the actual selected QR columns and releases
all four scratch matrices. Its complete resource claims describe that same execution.

## Main results

* `NLAlib.Deflation.problem` supplies only raw input and output capacity.
* `NLAlib.Deflation.fixedProgram` fixes the implementation before sizes or data.
* `NLAlib.Deflation.wordSpecification` specifies its stored sample-dependent output.
* `NLAlib.Deflation.certifiedAlgorithm` proves total output and resource correctness.
-/

@[expose] public section

namespace NLAlib.Deflation

open Ops

variable {K : Type} [Inhabited K]

/-- Raw projector words and uninitialized capacity for the requested basis columns. The
admitted dimension/rank domain is explicit and inhabited. -/
def problem (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem K 2 2 where
  formats _ := .cell
  valid := domain
  Data _ := List K
  admissible d xs buffers :=
    buffers = ![xs.map some, List.replicate (2 * (d 0 * d 1)) none] ∧
      xs.length = 2 * (d 0 * d 0)
  admitted := admitted
  supply d _ := ⟨List.replicate (2 * (d 0 * d 0)) default,
    ![(List.replicate (2 * (d 0 * d 0)) default).map some,
      List.replicate (2 * (d 0 * d 1)) none], rfl, List.length_replicate ..⟩

/-- The entire sampled projection and QR implementation is one fixed dense program. -/
def fixedProgram : Program DenseOp (CmpTst ⊕ IdxTst) 2 2 :=
  ⟨(program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).body⟩

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The input relation identifies the exact raw words and output capacity. -/
theorem input_buffers (d : Fin 2 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    x.val.2 = ![x.val.1.map some, List.replicate (2 * (d 0 * d 1)) none] := x.property.1

/-- Decode the input only in the specification, without computing any initial word. -/
def inputMatrix (d : Fin 2 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    Matrix (Fin (d 0)) (Fin (d 0)) (K × K) :=
  (EntryCodec.pair K).matrix (d 0) (d 0) x.val.1

/-- Actual raw input reads, live handles and output room follow from the supplied buffers. -/
theorem initial_geometry (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    let m := (problem (K := K) domain admitted).initial d x
    m.Live [(0, 0), (1, 0)] ∧
      m.store.readBlock 0 0 (2 * (d 0 * d 0)) =
        some ((EntryCodec.pair K).packFinMatrix (inputMatrix d x)) ∧
      m.Room [(1, 0)] [2 * (d 0 * d 1)] ∧ m.store.length = 2 := by
  dsimp only
  have hs : ((problem (K := K) domain admitted).initial d x).store =
      [x.val.1.map some, List.replicate (2 * (d 0 * d 1)) none] := by
    change List.ofFn x.val.2 = _
    rw [input_buffers]
    rfl
  refine ⟨by simp [Mem.Live], ?_, by simp [Mem.Room, hs, Store.len], by simp⟩
  have hread := Problem.initial_readBlock (P := problem (K := K) domain admitted) d x (0 : Fin 2)
    (show x.val.2 0 = x.val.1.map some by rw [input_buffers]; rfl)
  rw [x.property.2] at hread
  have hlen : x.val.1.length = d 0 * d 0 * (EntryCodec.pair K).width := by
    simpa only [EntryCodec.pair, Nat.mul_comm] using x.property.2
  rwa [inputMatrix, (EntryCodec.pair K).packFinMatrix_matrix _ _ _ hlen]

/-- Every supplied input and output slot contributes to resident payload. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    (problem (K := K) domain admitted).initialBytes d x =
      2 * (d 0 * d 0) + 2 * (d 0 * d 1) := by
  rw [Problem.initialBytes, input_buffers]
  simp [problem, List.ofFn_succ, x.property.2]

/-- The full static manifest includes all sampling, copying, kernels and core instructions. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) :
    Count (DenseOp ⊕ Bookkeeping) (CmpTst ⊕ IdxTst) := staticCost fixedProgram d

/-- The actual sampled QR columns, exact sample advance and cleanup, with transparent
dimension-only full resource bounds. Column selection is admitted only when rank ≤ size. -/
noncomputable def wordSpecification (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) :
    Specification DenseOp (CmpTst ⊕ IdxTst) (problem (K := K) domain admitted) where
  budget := staticBudget
  scratch := staticPeak (Dense.resources matrixWork matrixWorkspace) fixedProgram
  work d := (Dense.resources matrixWork matrixWorkspace).work (staticBudget d)
  span d := (Dense.resources matrixWork matrixWorkspace).span (staticBudget d)
  memory d := 2 * (d 0 * d 0) + 2 * (d 0 * d 1) +
    staticPeak (Dense.resources matrixWork matrixWorkspace) fixedProgram d
  good d x tape _ m := ∃ hrank : d 1 ≤ d 0,
    m.store.readBlock 1 0 (2 * (d 0 * d 1)) =
      some ((EntryCodec.pair K).packFinMatrix
        ((qr (mm (inputMatrix d x) (sampleMatrix (d 0) 0 tape))).1.submatrix id
          (Fin.castLE hrank))) ∧ m.pos = 2 * (d 0 * d 0) ∧ m.store.length = 2

/-- Primitive functional contracts and the requested-rank bound imply total canonical
deflation with the exact sample-dependent stored result and every resource bound. Numerical
accuracy and a tape distribution are separate mathematical assumptions about that result. -/
noncomputable def certifiedAlgorithm (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ)
    (hRank : ∀ d, domain d → d 1 ≤ d 0) :
    Algorithm
      (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K) mm qr
        (Dense.resources matrixWork matrixWorkspace))
      (wordSpecification mm qr domain admitted matrixWork matrixWorkspace) := by
  refine Algorithm.ofWp fixedProgram (by rfl) ?_ (fun _ _ => le_rfl)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl) ?_
  · intro d hd x I hI tape
    rcases Dense.laws_functionalModel M dec (EntryCodec.pair K) mm qr
      (Dense.resources matrixWork matrixWorkspace) d x I hI with
      ⟨hS, _, hMM, hQR, hSample, _, _⟩
    rcases initial_geometry d x with ⟨hl, hP, hRoom, hLength⟩
    have hr := writes_program hS hSample hMM hQR (tape := tape)
      (m := (problem (K := K) domain admitted).initial d x)
      (p := (0, 0)) (z := (1, 0)) (inputMatrix d x) (hRank d hd) hl hP hRoom.1
    apply hr.wp
    intro m' hf h c _
    refine ⟨hRank d hd, h.2, ?_, hf.length_eq.trans hLength⟩
    simpa only [Problem.initial, Nat.zero_add] using h.1
  · intro d hd x
    rw [initialBytes_problem]
    exact le_rfl

end NLAlib.Deflation
