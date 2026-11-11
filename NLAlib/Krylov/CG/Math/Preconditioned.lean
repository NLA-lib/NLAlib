/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Spec

/-!
# Nonbreakdown of preconditioned conjugate gradients

Positive definiteness of the system matrix and applied inverse preconditioner makes both
divisors positive before the initial preconditioned residual's Krylov grade.

## Main results

* `NLAlib.Krylov.CG.HSPCG.iterate_pcgStep_pcgState` identifies iterated rounds.
* `Matrix.PosDef.pcgState_nonbreakdown` supplies the divisors on an active prefix.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib.Krylov.CG.HSPCG

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- Repeated PCG rounds continue the existing state sequence from any starting index. -/
theorem iterate_pcgStep_pcgState (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k j : ℕ) :
    (pcgStep A M)^[k] (pcgState A M b x₀ j) = pcgState A M b x₀ (j + k) := by
  induction k with
  | zero => simp only [Function.iterate_zero_apply, Nat.add_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Nat.add_succ]
    rfl

/-- Every earlier PCG direction is orthogonal to the current residual for positive-definite
system and preconditioner matrices. [Saad2003, §9.2]. -/
theorem _root_.Matrix.PosDef.star_pcgState_p_dotProduct_r_eq_zero {A M : Matrix n n 𝕜}
    (hA : A.PosDef) (hM : M.PosDef) (b x₀ : n → 𝕜) {j k : ℕ} (hjk : j < k) :
    star (pcgState A M b x₀ j).p ⬝ᵥ (pcgState A M b x₀ k).r = 0 := by
  induction j with
  | zero => exact hA.star_pcgState_z_dotProduct_eq_zero hM hjk
  | succ j ih =>
    obtain ⟨β, hp⟩ : ∃ β : 𝕜, (pcgState A M b x₀ (j + 1)).p =
        (pcgState A M b x₀ (j + 1)).z + β • (pcgState A M b x₀ j).p := ⟨_, rfl⟩
    rw [hp, star_add, add_dotProduct, star_smul, smul_dotProduct,
      hA.star_pcgState_z_dotProduct_eq_zero hM hjk, ih (by omega), smul_zero, add_zero]

/-- A PCG direction pairs with its current residual as the preconditioned residual does.
[Saad2003, §9.2]. -/
theorem _root_.Matrix.PosDef.star_pcgState_p_dotProduct_r {A M : Matrix n n 𝕜}
    (hA : A.PosDef) (hM : M.PosDef) (b x₀ : n → 𝕜) (k : ℕ) :
    star (pcgState A M b x₀ k).p ⬝ᵥ (pcgState A M b x₀ k).r =
      star (pcgState A M b x₀ k).z ⬝ᵥ (pcgState A M b x₀ k).r := by
  cases k with
  | zero => rfl
  | succ j =>
    obtain ⟨β, hp⟩ : ∃ β : 𝕜, (pcgState A M b x₀ (j + 1)).p =
        (pcgState A M b x₀ (j + 1)).z + β • (pcgState A M b x₀ j).p := ⟨_, rfl⟩
    rw [hp, star_add, add_dotProduct, star_smul, smul_dotProduct,
      hA.star_pcgState_p_dotProduct_r_eq_zero hM b x₀ (Nat.lt_succ_self j),
      smul_zero, add_zero]

/-- A nonzero residual gives a nonzero PCG direction under positive-definite system and
preconditioner matrices. [Saad2003, §9.2]. -/
theorem _root_.Matrix.PosDef.pcgState_p_ne_zero_of_r_ne_zero {A M : Matrix n n ℝ}
    (hA : A.PosDef) (hM : M.PosDef) (b x₀ : n → ℝ) {k : ℕ}
    (hr : (pcgState A M b x₀ k).r ≠ 0) : (pcgState A M b x₀ k).p ≠ 0 := by
  intro hp
  have h := hA.star_pcgState_p_dotProduct_r hM b x₀ k
  simp only [star_trivial, hp, pcgState_z_eq, dotProduct_comm, dotProduct_zero] at h
  exact (hM.dotProduct_mulVec_pos hr).ne' (by simpa only [star_trivial] using h.symm)

/-- Both PCG divisors are nonzero whenever the residual is nonzero, for positive-definite
system and preconditioner matrices. [Saad2003, §9.2]. -/
theorem _root_.Matrix.PosDef.pcgState_nonbreakdown_of_r_ne_zero {A M : Matrix n n ℝ}
    (hA : A.PosDef) (hM : M.PosDef) (b x₀ : n → ℝ) {k : ℕ}
    (hr : (pcgState A M b x₀ k).r ≠ 0) : Nonbreakdown A (pcgState A M b x₀ k) := by
  refine ⟨?_, (hA.dotProduct_mulVec_pos
    (hA.pcgState_p_ne_zero_of_r_ne_zero hM b x₀ hr)).ne'⟩
  rw [pcgState_z_eq]
  exact (hM.dotProduct_mulVec_pos hr).ne'

/-- Before the preconditioned residual's Krylov grade, a PCG round has nonzero divisors.
[Saad2003, §9.2]. -/
theorem _root_.Matrix.PosDef.pcgState_nonbreakdown [DecidableEq n] {A M : Matrix n n ℝ}
    (hA : A.PosDef) (hM : M.PosDef) (b x₀ : n → ℝ) {k : ℕ}
    (hk : k < krylovGrade (M * A) (M *ᵥ (b - A *ᵥ x₀))) :
    Nonbreakdown A (pcgState A M b x₀ k) := by
  have hr : (pcgState A M b x₀ k).r ≠ 0 :=
    fun h => hk.not_ge ((hA.pcgState_r_eq_zero_iff hM b x₀ k).mp h)
  exact hA.pcgState_nonbreakdown_of_r_ne_zero hM b x₀ hr

/-- At or beyond the preconditioned Krylov grade, the mathematical PCG iterate solves the
system. This formulation does not require an already chosen solution. [Saad2003, §9.2]. -/
theorem _root_.Matrix.PosDef.mulVec_pcgIterate_of_krylovGrade_le [DecidableEq n]
    {A M : Matrix n n 𝕜} (hA : A.PosDef) (hM : M.PosDef) (b x₀ : n → 𝕜) {k : ℕ}
    (hk : krylovGrade (M * A) (M *ᵥ (b - A *ᵥ x₀)) ≤ k) :
    A *ᵥ pcgIterate A M b x₀ k = b := by
  have hr := (hA.pcgState_r_eq_zero_iff hM b x₀ k).mpr hk
  rw [pcgState_r_eq] at hr
  have he := (sub_eq_zero.mp hr).symm
  rwa [hA.pcgState_x_eq hM b x₀ k] at he

end NLAlib.Krylov.CG.HSPCG
