/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.BufferProblem
public import NLAlib.Ops.ContextProblem
public import NLAlib.Ops.Catalog.StoredOperator

/-!
# Supplied dense data for conjugate gradient

The raw matrix precedes the right-hand side and supplied uninitialized output capacities.
Mathematical admission refers to these actual words. Its witness proves nonemptiness only;
it performs no preprocessing and supplies no execution or output.

## Main results

* `NLAlib.Krylov.CG.StoredProblem.problem`: the declared dense matrix and vector interface.
* `NLAlib.Krylov.CG.StoredProblem.initial_matrix`: actual matrix readback.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.StoredProblem

open Ops

variable {b : ℕ}

/-- Joint raw data witnesses the mathematical input domain at every admitted size. -/
theorem context_supply (outputs : (Fin 2 → ℕ) → Fin (b + 1) → ℕ)
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (accepts : (Fin 2 → ℕ) → List ℝ → List ℝ → Prop)
    (supply : ∀ d, domain d → ∃ raw rhs : List ℝ,
      raw.length = d 0 * d 0 ∧ rhs.length = d 0 ∧ accepts d raw rhs)
    (d : Fin 2 → ℕ) (hd : domain d) :
    ∃ context : Fin 1 → List ℝ,
      ∃ x : (RawProblem.problem outputs domain admitted).Input d,
      (∀ i, (context i).length = d 0 * d 0) ∧ accepts d (context 0) x.val.1 := by
  obtain ⟨raw, rhs, hraw, hrhs, h⟩ := supply d hd
  refine ⟨fun _ => raw, ⟨⟨rhs, fun i => if i = 0 then rhs.map some
    else List.replicate (outputs d i) none⟩, rfl, hrhs⟩, fun _ => hraw, h⟩

/-- Raw matrix words, RHS words and uninitialized output capacities are all declared input. -/
abbrev problem (outputs : (Fin 2 → ℕ) → Fin (b + 1) → ℕ)
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (accepts : (Fin 2 → ℕ) → List ℝ → List ℝ → Prop)
    (supply : ∀ d, domain d → ∃ raw rhs : List ℝ,
      raw.length = d 0 * d 0 ∧ rhs.length = d 0 ∧ accepts d raw rhs) : Problem ℝ 2 (1 + (b + 1)) :=
  (RawProblem.problem outputs domain admitted).withContext 1 (fun d _ => d 0 * d 0)
    (fun d c rhs => accepts d (c 0) rhs) (context_supply outputs domain admitted accepts supply)

variable {outputs : (Fin 2 → ℕ) → Fin (b + 1) → ℕ}
  {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}
  {accepts : (Fin 2 → ℕ) → List ℝ → List ℝ → Prop}
  {supply : ∀ d, domain d → ∃ raw rhs : List ℝ,
    raw.length = d 0 * d 0 ∧ rhs.length = d 0 ∧ accepts d raw rhs}

/-- The numerical matrix is decoded from the actual initialized context words. -/
def matrix {d : Fin 2 → ℕ} (x : (problem outputs domain admitted accepts supply).Input d) :=
  StoredOperator.denseMatrix (d 0) (d 0) (x.val.1.1 0)

/-- The matrix prefix is physically readable before execution. -/
theorem initial_matrix (d : Fin 2 → ℕ)
    (x : (problem outputs domain admitted accepts supply).Input d) :
    ((problem outputs domain admitted accepts supply).initial d x).store.readBlock
      0 0 (d 0 * d 0) = some (x.val.1.1 0) :=
  Problem.withContext.initial_readBlock_context d x 0

/-- The shifted RHS reads the supplied words without conversion. -/
theorem initial_rhs (d : Fin 2 → ℕ)
    (x : (problem outputs domain admitted accepts supply).Input d) :
    ((problem outputs domain admitted accepts supply).initial d x).store.readBlock
      1 0 (d 0) = some x.val.1.2 := by
  have hlen := RawProblem.length_input d (Problem.withContext.originalInput x)
  have hr := Problem.withContext.initial_readBlock_original d x (0 : Fin (b + 1))
    (show (Problem.withContext.originalInput x).val.2 0 = x.val.1.2.map some by
      rw [RawProblem.input_buffers]; simp [Problem.withContext.originalInput])
  change x.val.1.2.length = d 0 at hlen
  change ((problem outputs domain admitted accepts supply).initial d x).store.readBlock
    1 0 x.val.1.2.length = some x.val.1.2 at hr
  rw [hlen] at hr
  exact hr

/-- Every shifted source buffer retains exactly its supplied capacity. -/
theorem initial_len (d : Fin 2 → ℕ)
    (x : (problem outputs domain admitted accepts supply).Input d) (i : Fin (b + 1)) :
    ((problem outputs domain admitted accepts supply).initial d x).store.len (1 + i.val) =
      if i = 0 then d 0 else outputs d i := by
  exact (Problem.withContext.initial_len_original d x i).trans
    (RawProblem.initial_len d (Problem.withContext.originalInput x) i)

end NLAlib.Krylov.CG.StoredProblem
