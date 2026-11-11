/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Reorth.RoundExact
public import NLAlib.Krylov.CG.Reorth.History

/-!
# Stored-state bridges for full-reorthogonalized CG

These facts expose the three state reads and identify a round against any stored basis whose
initialized columns decode to the exact residual history.

## Main results

* `NLAlib.Krylov.CG.Reorth.state_reads`: expose the stored iterate, residual and direction.
* `NLAlib.Krylov.CG.Reorth.reorthStep_eq_cgState_of_history`: the exact recurrence bridge.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops

variable {K : Type} [Inhabited K]

/-- The three individually readable blocks of a stored CG state. -/
theorem state_reads {dec : K → ℝ} {n : ℕ} {x r p : ℕ × ℕ} {s : CGState ℝ (Fin n)}
    {μ : Mem K} (h : HSCG.StoresState dec n x r p s μ) :
    ∃ xs rs ps, μ.store.readBlock x.1 x.2 n = some xs ∧
      μ.store.readBlock r.1 r.2 n = some rs ∧ μ.store.readBlock p.1 p.2 n = some ps ∧
      HSCG.decodedState dec n xs rs ps = s := by
  obtain ⟨xs, rs, ps, hread, heq⟩ := h
  obtain ⟨xs₁, tail₁, hx, htail₁, hcons₁⟩ := Mem.readBlocks_cons_eq_some.mp hread
  have hx_eq : xs₁ = xs := (List.cons.inj hcons₁).1.symm
  subst xs₁
  have htail_eq : tail₁ = [rs, ps] := (List.cons.inj hcons₁).2.symm
  subst tail₁
  obtain ⟨rs₁, tail₂, hr, htail₂, hcons₂⟩ := Mem.readBlocks_cons_eq_some.mp htail₁
  have hr_eq : rs₁ = rs := (List.cons.inj hcons₂).1.symm
  subst rs₁
  have htail_eq₂ : tail₂ = [ps] := (List.cons.inj hcons₂).2.symm
  subst tail₂
  obtain ⟨ps₁, _, hp, _, hcons₃⟩ := Mem.readBlocks_cons_eq_some.mp htail₂
  have hp_eq : ps₁ = ps := (List.cons.inj hcons₃).1.symm
  subst ps₁
  exact ⟨xs, rs, ps, hx, hr, hp, heq⟩

private theorem sweepVec_congr {n : Type*} [Fintype n] (Q R : ℕ → n → ℝ)
    (v : n → ℝ) (k : ℕ) (h : ∀ j < k, Q j = R j) : sweepVec Q v k = sweepVec R v k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sweepVec, sweepVec, h k (by omega), ih (fun j hj => h j (by omega))]

/-- Any stored history decoding to the earlier CG residuals gives the same exact next state.
The basis may use any exact representation of those residuals. -/
theorem reorthStep_eq_cgState_of_history {dec : K → ℝ} {n j : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (b x₀ : Fin n → ℝ) (qs : List K)
    (h : ∀ i < j + 1, column dec n qs i = (cgState A b x₀ i).r) :
    reorthStep A (column dec n qs) (j + 1) (cgState A b x₀ j) = cgState A b x₀ (j + 1) := by
  apply reorthStep_eq_cgStep
  exact (sweepVec_congr _ _ _ _ h).trans (hA.sweepVec_cgState_r b x₀ (j + 1))

end NLAlib.Krylov.CG.Reorth
