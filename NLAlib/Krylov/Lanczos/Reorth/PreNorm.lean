/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.Alg
public import NLAlib.Krylov.Lanczos.Math.NormGuard
public import NLAlib.Ops.Logic.Tactic

/-!
# Total preorthogonalization norms

The raw residual's norm is saved before the two classical passes. A rounded self-dot controls
the square-root branch; zero leaves the initialized coefficient untouched. This interface
uses the same borrowed workspace as the enclosing Lanczos round.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.preNorm_writes`: rounded norm execution with actual witnesses.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

omit [Has OperatorOp Op] in
/-- The guarded preorthogonalization norm is total, including zero residuals. The stored norm
has the standard norm contract, so its positivity follows from the shared norm guard theorem. -/
theorem preNorm_writes {M : Machine K} {dec : K → ℝ} {u : ℝ} {ed : ℕ → ℝ}
    {n cap j L B V C bo vo co : ℕ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hd : ed n < 1)
    (hD : I.Meets .total (Has.inj Blas1Op.dot) ((dotRel dec ed).spec (OutApart ok)))
    (hok : ok n) (hCmp : IsCmp dec I)
    {τ : Tape K} {μ : Mem K} {ws : List K} {ν₀ : K}
    (hCL : C < L) (hlen : μ.store.length = L + 3)
    (ht : μ.store.len (L + 2) = 2)
    (hroom : co + 2 * cap + 2 + j < μ.store.len C)
    (hws : μ.store.readBlock (L + 1) 0 n = some ws)
    (hν : μ.store.get C (co + 2 * cap + 2 + j) = some ν₀) (hν₀ : dec ν₀ = 0) :
    Writes .total I τ preNorm ⟨[n,cap,bo,vo,co,j], [B,V,C,L,L + 1,L + 2]⟩
      (Fp.blocks [(L + 2,0),(C,co + 2 * cap + 2 + j)] [1,1])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ σ ν,
        μ'.store.get (L + 2) 0 = some σ ∧ μ'.store.get C (co + 2 * cap + 2 + j) = some ν ∧
        IsDotErr dec (ed n) n (vec ws) (vec ws) σ ∧
        IsNrm2Err dec (ed n) u n (vec ws) ν) μ := by
  step hD as μ₁ hfr₁ ⟨hpos₁, σ, hσ, hdot⟩
  refine writes_ite rfl rfl (hCmp.test_isPos hσ) ?_
  by_cases hp : 0 < dec σ
  · simp only [hp, decide_true, ite_true]
    step (hS .sqrt) as μ₂ hfr₂ ⟨hpos₂, ν, hν, hνword⟩
    exact ⟨by simp [hpos₂, hpos₁], σ, ν, by kept, hν, hdot,
      σ, hdot, fun hσnn => by rw [← hνword]; exact hM.sqrt σ hσnn⟩
  · simp only [hp, decide_false, Bool.false_eq_true, ite_false]
    have hwzero : decv dec n ws = 0 := by
      by_contra hne
      exact hp (hdot.self_pos_of_ne_zero hd hne)
    have hσzero : dec σ = 0 := by simpa [hwzero] using hdot.decoded
    refine (Writes.skip ?_).mono bot_le (fun _ _ h => h)
    exact ⟨hpos₁, σ, ν₀, hσ, by kept, hdot,
      σ, hdot, fun _ => by simp [hσzero, hν₀]⟩

end NLAlib.Krylov.Lanczos.Reorth
