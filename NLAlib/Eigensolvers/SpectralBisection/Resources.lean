/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Alg
public import NLAlib.Ops.Profiles.Dense
public import NLAlib.Ops.Certification

/-!
# Supplied buffers and resource declarations for spectral bisection

The problem supplies its raw matrix, three scalar parameters, and uninitialized output
capacity. Initial memory does no numerical preprocessing. The same fixed program has an
independent full syntactic manifest, including primitive calls, queries and structural work.
Format checking and a manifest alone are not a total numerical/resource certificate.

## Main results

* `NLAlib.SpectralBisection.problem`: explicit raw input and output buffers.
* `NLAlib.SpectralBisection.initialBytes_problem`: all supplied resident word capacity.
* `NLAlib.SpectralBisection.wellTyped_program`: every primitive uses its declared storage format.
* `NLAlib.SpectralBisection.staticBudget`: the complete instrumented syntactic manifest.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {K : Type} [Inhabited K]

/-- Raw matrix words, three stored parameters, and empty output slots for a basis and values.
The size domain is explicit and inhabited. The matrix is an interleaved square block; the
parameters are radius, tolerance and sign accuracy, in that order. -/
def problem (domain : (Fin 3 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem K 3 4 where
  formats _ := .cell
  valid := domain
  Data _ := List K × List K
  admissible d data buffers :=
    buffers = ![data.1.map some, data.2.map some,
      List.replicate (2 * (d 0 * d 0)) none, List.replicate (d 0) none] ∧
      data.1.length = 2 * (d 0 * d 0) ∧ data.2.length = 3
  admitted := admitted
  supply d _ := ⟨(List.replicate (2 * (d 0 * d 0)) default, List.replicate 3 default),
    ![(List.replicate (2 * (d 0 * d 0)) default).map some,
      (List.replicate 3 default).map some, List.replicate (2 * (d 0 * d 0)) none,
      List.replicate (d 0) none], rfl, List.length_replicate .., List.length_replicate ..⟩

variable {domain : (Fin 3 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- Admissibility fixes the actual supplied raw buffers; no encoded output is computed here. -/
theorem input_buffers (d : Fin 3 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    x.val.2 = ![x.val.1.1.map some, x.val.1.2.map some,
      List.replicate (2 * (d 0 * d 0)) none, List.replicate (d 0) none] := x.property.1

/-- The supplied matrix block has exactly two scalar words per square entry. -/
theorem length_input_matrix (d : Fin 3 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    x.val.1.1.length = 2 * (d 0 * d 0) := x.property.2.1

/-- The supplied parameter block has exactly its three declared words. -/
theorem length_input_parameters (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) : x.val.1.2.length = 3 := x.property.2.2

/-- Resident capacity includes both the supplied matrix and output basis, the output values,
and all three supplied scalar parameters, including every initially empty output slot. -/
theorem initialBytes_problem (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    (problem (K := K) domain admitted).initialBytes d x =
      4 * (d 0 * d 0) + d 0 + 3 := by
  rw [Problem.initialBytes, input_buffers]
  simp [problem, List.ofFn_succ, length_input_matrix, length_input_parameters]
  omega

/-- The supplied matrix reads as its original raw list of words. -/
theorem initial_readBlock_matrix (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    ((problem (K := K) domain admitted).initial d x).store.readBlock 0 0 (2 * (d 0 * d 0)) =
      some x.val.1.1 := by
  have h := Problem.initial_readBlock (P := problem (K := K) domain admitted) d x (0 : Fin 4)
    (show x.val.2 0 = x.val.1.1.map some by rw [input_buffers]; rfl)
  rwa [length_input_matrix d x] at h

/-- The supplied scalar parameters read as their original raw list of words. -/
theorem initial_readBlock_parameters (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    ((problem (K := K) domain admitted).initial d x).store.readBlock 1 0 3 = some x.val.1.2 := by
  have h := Problem.initial_readBlock (P := problem (K := K) domain admitted) d x (1 : Fin 4)
    (show x.val.2 1 = x.val.1.2.map some by rw [input_buffers]; rfl)
  rwa [length_input_parameters d x] at h

/-- The finite word matrix represented by the supplied raw interleaved input block. This is
a mathematical decoder for the specification; it is not executed as input preprocessing. -/
def inputMatrix (d : Fin 3 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    Matrix (Fin (d 0)) (Fin (d 0)) (K × K) :=
  (EntryCodec.pair K).matrix (d 0) (d 0) x.val.1.1

/-- Every raw supplied matrix is exactly the packed finite word matrix in the specification.
The codec's inverse law prevents a hidden representability or padding condition. -/
theorem initial_readBlock_inputMatrix (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    ((problem (K := K) domain admitted).initial d x).store.readBlock 0 0 (2 * (d 0 * d 0)) =
      some ((EntryCodec.pair K).packFinMatrix (inputMatrix d x)) := by
  have hlen : x.val.1.1.length = d 0 * d 0 * (EntryCodec.pair K).width := by
    simpa only [EntryCodec.pair, Nat.mul_comm] using length_input_matrix d x
  rw [inputMatrix, (EntryCodec.pair K).packFinMatrix_matrix _ _ _ hlen]
  exact initial_readBlock_matrix d x

/-- Each supplied scalar parameter is readable at its declared position in the parameter
buffer. No algorithm-dependent scalar is supplied through this interface. -/
theorem initial_get_parameter (d : Fin 3 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) (i : Fin 3) :
    ((problem (K := K) domain admitted).initial d x).store.get 1 i = some (vec x.val.1.2 i) := by
  simpa only [Nat.zero_add] using
    Store.get_of_readBlock (initial_readBlock_parameters d x) i.isLt default

/-- The full budget is computed from the fixed instrumented tree before any input executes.
It contains all scalar/matrix/sample calls, queries and core addressing/control instructions. -/
noncomputable def staticBudget (d : Fin 3 → ℕ) :
    Count (DenseOp ⊕ Bookkeeping) (CmpTst ⊕ IdxTst) :=
  staticCost (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)) d

/-- The entire fixed program respects the standard dense signature's storage formats,
independently of the chosen matrix work and scratch functions. This is format checking;
execution, numerical output and sharp resource bounds require their own proofs. -/
theorem wellTyped_program (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) :
    (program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)).wellTyped
      (Dense.resources matrixWork matrixWorkspace) (fun _ => .cell) = true := by
  rfl

end NLAlib.SpectralBisection
