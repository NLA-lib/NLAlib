/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.BufferProblem

/-!
# Mathematically restricted raw CG inputs

Fixed-horizon variants require a horizon no larger than the initial Krylov grade. That is an
explicit mathematical admissibility condition on raw words, together with a genuine witness
at every admitted size. No successful run or computed output enters this interface.

## Main results

* `NLAlib.Krylov.CG.RawProblem.restricted`: raw words with mathematical admissibility.
* `NLAlib.Krylov.CG.RawProblem.forgetInput`: recover the ordinary raw-buffer interface.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.RawProblem

open Ops

variable {K : Type} [Inhabited K] {b : ℕ}

/-- Restrict supplied raw words by a mathematical input condition. The supply argument is
only a nonemptiness proof, not an execution or data-preparation procedure. -/
noncomputable def restricted (outputs : (Fin 2 → ℕ) → Fin (b + 1) → ℕ)
    (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)
    (accepts : (Fin 2 → ℕ) → List K → Prop)
    (supply : ∀ d, domain d → ∃ rhs : List K, rhs.length = d 0 ∧ accepts d rhs) :
    Problem K 2 (b + 1) :=
  { problem outputs domain admitted with
    admissible := fun d rhs buffers =>
      (problem (K := K) outputs domain admitted).admissible d rhs buffers ∧ accepts d rhs
    supply := fun d hd => by
      let rhs := Classical.choose (supply d hd)
      have hlen := (Classical.choose_spec (supply d hd)).1
      have haccept := (Classical.choose_spec (supply d hd)).2
      exact ⟨rhs, (fun i => if i = 0 then rhs.map some else List.replicate (outputs d i) none),
        ⟨rfl, hlen⟩, haccept⟩ }

/-- Forget only the mathematical domain proof; raw words and every buffer stay identical. -/
def forgetInput {outputs : (Fin 2 → ℕ) → Fin (b + 1) → ℕ}
    {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}
    {accepts : (Fin 2 → ℕ) → List K → Prop}
    {supply : ∀ d, domain d → ∃ rhs : List K, rhs.length = d 0 ∧ accepts d rhs}
    {d : Fin 2 → ℕ} (x : (restricted outputs domain admitted accepts supply).Input d) :
    (problem (K := K) outputs domain admitted).Input d := ⟨x.val, x.property.1⟩

end NLAlib.Krylov.CG.RawProblem
