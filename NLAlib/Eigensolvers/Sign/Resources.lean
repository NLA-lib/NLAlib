/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Alg
public import NLAlib.Ops.Profiles.Dense
public import NLAlib.Ops.Certification

/-!
# Supplied buffers for capped matrix sign iteration

The problem supplies matrix words, two parameter words and uninitialized output capacity.
The fixed program computes the capped sign iteration using its own scoped workspace.
Resources include the complete instrumented tree and all supplied capacity.

## Main results

* `NLAlib.Sign.problem` declares the raw inputs and output capacity.
* `NLAlib.Sign.fixedProgram` fixes one tree before sizes or input values.
* `NLAlib.Sign.initial_geometry` gives the supplied block reads and capacities.
* `NLAlib.Sign.initialBytes_problem` counts all supplied capacity.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {K : Type} [Inhabited K]

/-- A packed square matrix, tolerance and scale, and an empty packed matrix output. The
domain restricts only dimensions and cap; every word matrix and parameter pair is supplied. -/
def problem (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d) : Problem K 2 3 where
  formats _ := .cell
  valid := domain
  Data _ := List K × List K
  admissible d data buffers :=
    buffers = ![data.1.map some, data.2.map some,
      List.replicate (2 * (d 0 * d 0)) none] ∧
      data.1.length = 2 * (d 0 * d 0) ∧ data.2.length = 2
  admitted := admitted
  supply d _ := ⟨(List.replicate (2 * (d 0 * d 0)) default, List.replicate 2 default),
    ![(List.replicate (2 * (d 0 * d 0)) default).map some,
      (List.replicate 2 default).map some, List.replicate (2 * (d 0 * d 0)) none],
    rfl, List.length_replicate .., List.length_replicate ..⟩

/-- The complete sign tree uses the standard dense operation signature. Parameters are
matrix dimension and cap; the three handles are input matrix, parameters and output. -/
def fixedProgram : Program DenseOp (CmpTst ⊕ IdxTst) 2 3 :=
  ⟨(program (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst) (Has.inj MatrixOp.mul)).body⟩

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- Admissibility identifies exactly the supplied words and the empty output capacity. -/
theorem input_buffers (d : Fin 2 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    x.val.2 = ![x.val.1.1.map some, x.val.1.2.map some,
      List.replicate (2 * (d 0 * d 0)) none] := x.property.1

/-- The packed matrix is decoded only in the mathematical specification. Initialization
stores the supplied raw words without evaluating this decoder. -/
def inputMatrix (d : Fin 2 → ℕ) (x : (problem (K := K) domain admitted).Input d) :
    Matrix (Fin (d 0)) (Fin (d 0)) (K × K) :=
  (EntryCodec.pair K).matrix (d 0) (d 0) x.val.1.1

/-- Input and output capacity both count as supplied resident payload. -/
theorem initialBytes_problem (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    (problem (K := K) domain admitted).initialBytes d x = 4 * (d 0 * d 0) + 2 := by
  rw [Problem.initialBytes, input_buffers]
  simp [problem, List.ofFn_succ, x.property.2.1, x.property.2.2]
  omega

/-- Every supplied matrix is the exact packing of its finite matrix decoder. No padding
or representability assumption is hidden in this input relation. -/
theorem initial_matrix (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    ((problem (K := K) domain admitted).initial d x).store.readBlock 0 0 (2 * (d 0 * d 0)) =
      some ((EntryCodec.pair K).packFinMatrix (inputMatrix d x)) := by
  have hr := Problem.initial_readBlock (P := problem (K := K) domain admitted) d x (0 : Fin 3)
    (show x.val.2 0 = x.val.1.1.map some by rw [input_buffers]; rfl)
  rw [x.property.2.1] at hr
  have hlen : x.val.1.1.length = d 0 * d 0 * (EntryCodec.pair K).width := by
    simpa only [EntryCodec.pair, Nat.mul_comm] using x.property.2.1
  rwa [inputMatrix, (EntryCodec.pair K).packFinMatrix_matrix _ _ _ hlen]

/-- Both actual raw parameter words are readable at their declared positions. -/
theorem initial_parameters (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    ((problem (K := K) domain admitted).initial d x).store.readBlock 1 0 2 =
      some [vec x.val.1.2 0, vec x.val.1.2 1] := by
  have hr := Problem.initial_readBlock (P := problem (K := K) domain admitted) d x (1 : Fin 3)
    (show x.val.2 1 = x.val.1.2.map some by rw [input_buffers]; rfl)
  rw [x.property.2.2] at hr
  have hx : x.val.1.2 = [vec x.val.1.2 0, vec x.val.1.2 1] := by
    have hlen := x.property.2.2
    generalize x.val.1.2 = xs at hlen ⊢
    rcases xs with _ | ⟨a, xs⟩
    · simp at hlen
    rcases xs with _ | ⟨b, xs⟩
    · simp at hlen
    have hz : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst xs
    rfl
  rwa [hx] at hr

/-- All raw handles are live and separate, and the output has its declared capacity. -/
theorem initial_geometry (d : Fin 2 → ℕ)
    (x : (problem (K := K) domain admitted).Input d) :
    let m := (problem (K := K) domain admitted).initial d x
    m.Live [(0, 0), (1, 0), (2, 0)] ∧
      Fp.Apart [(0, 0), (1, 0), (2, 0)] [2 * (d 0 * d 0), 2, 2 * (d 0 * d 0)] ∧
      m.Room [(2, 0)] [2 * (d 0 * d 0)] ∧ m.store.length = 3 := by
  dsimp only
  have hs : ((problem (K := K) domain admitted).initial d x).store =
      [x.val.1.1.map some, x.val.1.2.map some,
        List.replicate (2 * (d 0 * d 0)) none] := by
    change List.ofFn x.val.2 = _
    rw [input_buffers]
    rfl
  refine ⟨?_, ?_, ?_, by simp⟩
  · simp [Mem.Live]
  · disjoint
  · simp [Mem.Room, hs, Store.len]

/-- Every primitive and structural instruction in the fixed instrumented sign tree. -/
noncomputable def staticBudget (d : Fin 2 → ℕ) :
    Count (DenseOp ⊕ Bookkeeping) (CmpTst ⊕ IdxTst) := staticCost fixedProgram d

/-- Every sign call uses the storage formats of the standard dense resource profile. -/
theorem wellTyped_fixedProgram (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) :
    fixedProgram.wellTyped (Dense.resources matrixWork matrixWorkspace) (fun _ => .cell) = true :=
  rfl

end NLAlib.Sign
