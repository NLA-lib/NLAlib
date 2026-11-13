/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.PCGRun

/-!
# Constructing PCG runs from local numerical defects

The initial approximate inverse-preconditioner application is retained as a fixed nonlinear
oracle action. Local defects determine a one-step run with the same terminal vectors.

## Main results

* `NLAlib.PCGRun.ofOneStep` constructs the first positive-length PCG prefix.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-- Construct a one-step zero-start PCG run from local bounded numerical defects, a
Hermitian system and an SPD reference inverse preconditioner. The approximate action need
not be linear. The final pairing may be zero. [Saad2003, Algorithm 9.1]. -/
noncomputable def PCGRun.ofOneStep (N : ℕ) (A P : Matrix (Fin N) (Fin N) ℝ)
    (O : MatvecOracle P)
    (b : Fin N → ℝ) (next : PCGState ℝ (Fin N)) (sv : Fin N → ℝ)
    (ε ν0 ν1 μ γ eγ δ eδ : ℝ) (hA : A.IsHermitian) (hP : P.PosDef)
    (hε : 0 ≤ ε) (hεle : ε ≤ 1 / 100)
    (hz : next.z = O.mulVec next.r)
    (hν0 : |ν0 - b ⬝ᵥ O.mulVec b| ≤ ε * ‖WithLp.toLp 2 b‖ * ‖WithLp.toLp 2 (O.mulVec b)‖)
    (hν1 : |ν1 - next.r ⬝ᵥ next.z| ≤ ε * ‖WithLp.toLp 2 next.r‖ * ‖WithLp.toLp 2 next.z‖)
    (hνlast : 0 ≤ ν1) (hνpos : 0 < ν0) (hμpos : 0 < μ)
    (hs : ‖WithLp.toLp 2 (A *ᵥ O.mulVec b - sv)‖ ≤
      ε * specNorm A * ‖WithLp.toLp 2 (O.mulVec b)‖)
    (hμ : |O.mulVec b ⬝ᵥ sv - μ| ≤ ε * ‖WithLp.toLp 2 (O.mulVec b)‖ * ‖WithLp.toLp 2 sv‖)
    (hγ : γ = ν0 / μ * (1 + eγ)) (heγ : |eγ| ≤ ε)
    (hδ : δ = ν1 / ν0 * (1 + eδ)) (heδ : |eδ| ≤ ε)
    (hex : ‖WithLp.toLp 2 (γ • O.mulVec b - next.x)‖ ≤
      ε * (|γ| * ‖WithLp.toLp 2 (O.mulVec b)‖))
    (her : ‖WithLp.toLp 2 (b - γ • sv - next.r)‖ ≤
      ε * (‖WithLp.toLp 2 b‖ + |γ| * ‖WithLp.toLp 2 sv‖))
    (hep : ‖WithLp.toLp 2 (next.z + δ • O.mulVec b - next.p)‖ ≤
      ε * (‖WithLp.toLp 2 next.z‖ + |δ| * ‖WithLp.toLp 2 (O.mulVec b)‖)) : PCGRun N 1 := by
  have hlt {Q : ℕ → Prop} (h : Q 0) : ∀ j < 1, Q j := by
    simpa only [Nat.lt_one_iff, forall_eq] using h
  have hle {Q : ℕ → Prop} (h0 : Q 0) (h1 : Q 1) : ∀ j ≤ 1, Q j := by
    simpa only [Nat.le_one_iff_eq_zero_or_eq_one, or_imp, forall_and, forall_eq] using ⟨h0, h1⟩
  refine { A := A, M := P, preconditioner := O, posDef_M := hP, b := b
           x := fun j => if j = 0 then 0 else next.x
           r := fun j => if j = 0 then b else next.r
           z := fun j => if j = 0 then O.mulVec b else next.z
           p := fun j => if j = 0 then O.mulVec b else next.p
           s := fun _ => sv
           ν := fun j => if j = 0 then ν0 else ν1
           μ := fun _ => μ
           γ := fun _ => γ
           δ := fun _ => δ
           es := fun _ => -(A *ᵥ O.mulVec b - sv)
           eν := fun j => if j = 0 then ν0 - b ⬝ᵥ O.mulVec b
             else ν1 - next.r ⬝ᵥ next.z
           eμ := fun _ => -(O.mulVec b ⬝ᵥ sv - μ)
           eγ := fun _ => eγ
           ex := fun _ => -(γ • O.mulVec b - next.x)
           er := fun _ => -(b - γ • sv - next.r)
           eδ := fun _ => eδ
           ep := fun _ => -(next.z + δ • O.mulVec b - next.p)
           ε := ε, isHermitian_A := hA, ε_nonneg := hε, k_pos := by omega, ε_le := hεle
           x_zero := rfl, r_zero := rfl, p_zero := rfl
           z_eq := hle rfl hz
           ν_eq := hle (by simp only [ite_true, ← add_sub_assoc, add_sub_cancel_left])
             (by simp only [if_neg Nat.one_ne_zero, ← add_sub_assoc, add_sub_cancel_left])
           abs_eν_le := hle hν0 hν1
           ν_last_nonneg := hνlast
           ν_pos := hlt hνpos
           s_eq := hlt (by
             simp only [ite_true, neg_sub, ← add_sub_assoc, add_sub_cancel_left])
           norm_es_le := hlt (by
             simpa only [ite_true, WithLp.toLp_neg, norm_neg] using hs)
           μ_eq := hlt (by
             simp only [ite_true, neg_sub, ← add_sub_assoc, add_sub_cancel_left])
           abs_eμ_le := hlt (by simpa only [ite_true, abs_neg] using hμ)
           μ_pos := hlt hμpos
           γ_eq := hlt hγ
           abs_eγ_le := hlt heγ
           x_succ := hlt (by
             simp only [ite_true, if_neg Nat.one_ne_zero, zero_add, neg_sub,
               ← add_sub_assoc, add_sub_cancel_left])
           norm_ex_le := hlt (by
             simpa only [ite_true, WithLp.toLp_neg, norm_neg, WithLp.toLp_zero, norm_zero, zero_add]
               using hex)
           r_succ := hlt (by
             simp only [ite_true, if_neg Nat.one_ne_zero, neg_sub,
               ← add_sub_assoc, add_sub_cancel_left])
           norm_er_le := hlt (by
             simpa only [ite_true, WithLp.toLp_neg, norm_neg] using her)
           δ_eq := hlt hδ
           abs_eδ_le := hlt heδ
           p_succ := hlt (by
             simp only [ite_true, if_neg Nat.one_ne_zero, neg_sub,
               ← add_sub_assoc, add_sub_cancel_left])
           norm_ep_le := hlt (by
             simpa only [ite_true, if_neg Nat.one_ne_zero, WithLp.toLp_neg, norm_neg] using hep) }

end NLAlib
