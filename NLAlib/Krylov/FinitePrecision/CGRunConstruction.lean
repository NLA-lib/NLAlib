/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.CGRun

/-!
# Constructing a CG run from local numerical defects

The constructor exposes the existing run model directly, independently of either computation
core. Local numerical error bounds, rather than successful-execution premises, are its inputs.

## Main results

* `NLAlib.CGRun.ofOneStep` constructs the first positive-length prefix.
* `NLAlib.CGRun.exists_extend` appends bounded local defects to an existing prefix.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-- Construct the existing one-step CG run from a zero-start recurrence and its bounded local
errors, including a possibly zero final residual. [Greenbaum1997SIMAX, §2]. -/
noncomputable def CGRun.ofOneStep (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (next : CGState ℝ (Fin N)) (sv : Fin N → ℝ)
    (ε ν0 ν1 θ0 θ1 μ γ eγ δ eδ : ℝ) (hA : Aᵀ = A) (hε : 0 ≤ ε) (hεle : ε ≤ 1 / 100)
    (hν0 : ν0 = ‖WithLp.toLp 2 b‖ ^ 2 * (1 + θ0))
    (hν1 : ν1 = ‖WithLp.toLp 2 next.r‖ ^ 2 * (1 + θ1))
    (hθ0 : |θ0| ≤ ε) (hθ1 : |θ1| ≤ ε) (hνpos : 0 < ν0) (hμpos : 0 < μ)
    (hs : ‖WithLp.toLp 2 (A *ᵥ b - sv)‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 b‖)
    (hμ : |b ⬝ᵥ sv - μ| ≤ ε * ‖WithLp.toLp 2 b‖ * ‖WithLp.toLp 2 sv‖)
    (hγ : γ = ν0 / μ * (1 + eγ)) (heγ : |eγ| ≤ ε)
    (hδ : δ = ν1 / ν0 * (1 + eδ)) (heδ : |eδ| ≤ ε)
    (hex : ‖WithLp.toLp 2 (γ • b - next.x)‖ ≤ ε * (|γ| * ‖WithLp.toLp 2 b‖))
    (her : ‖WithLp.toLp 2 (b - γ • sv - next.r)‖ ≤
      ε * (‖WithLp.toLp 2 b‖ + |γ| * ‖WithLp.toLp 2 sv‖))
    (hep : ‖WithLp.toLp 2 (next.r + δ • b - next.p)‖ ≤
      ε * (‖WithLp.toLp 2 next.r‖ + |δ| * ‖WithLp.toLp 2 b‖)) : CGRun N 1 := by
  have hlt {Q : ℕ → Prop} (h : Q 0) : ∀ j < 1, Q j := by
    intro j hj
    have : j = 0 := by omega
    simpa only [this] using h
  have hle {Q : ℕ → Prop} (h0 : Q 0) (h1 : Q 1) : ∀ j ≤ 1, Q j := by
    intro j hj
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · exact h0
    · exact h1
  refine { A := A, b := b
           x := fun j => if j = 0 then 0 else next.x
           r := fun j => if j = 0 then b else next.r
           p := fun j => if j = 0 then b else next.p
           s := fun _ => sv
           ν := fun j => if j = 0 then ν0 else ν1
           μ := fun _ => μ
           γ := fun _ => γ
           δ := fun _ => δ
           es := fun _ => -(A *ᵥ b - sv)
           θ := fun j => if j = 0 then θ0 else θ1
           eμ := fun _ => -(b ⬝ᵥ sv - μ)
           eγ := fun _ => eγ
           ex := fun _ => -(γ • b - next.x)
           er := fun _ => -(b - γ • sv - next.r)
           eδ := fun _ => eδ
           ep := fun _ => -(next.r + δ • b - next.p)
           ε := ε, transpose_A := hA, ε_nonneg := hε, k_pos := by omega, ε_le := hεle
           x_zero := rfl, r_zero := rfl, p_zero := rfl
           ν_eq := hle hν0 hν1
           abs_θ_le := hle hθ0 hθ1
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


namespace CGRun

private theorem forall_le_succ {k : ℕ} {Q : ℕ → Prop}
    (h : ∀ j ≤ k, Q j) (hs : Q (k + 1)) : ∀ j ≤ k + 1, Q j := by
  intro j hj
  rcases Nat.eq_or_lt_of_le hj with rfl | hj
  · exact hs
  · exact h j (by omega)

private theorem forall_lt_succ {k : ℕ} {Q : ℕ → Prop}
    (h : ∀ j < k, Q j) (hs : Q k) : ∀ j < k + 1, Q j := by
  intro j hj
  rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hj
  · exact hs
  · exact h j hj

private theorem cache_fields {N k : ℕ} (R : CGRun N k)
    (next : CGState ℝ (Fin N)) (ν θ μ γ eγ δ eδ : ℝ)
    (hνpos : 0 < R.ν k) (hν : ν = ‖WithLp.toLp 2 next.r‖ ^ 2 * (1 + θ))
    (hθ : |θ| ≤ R.ε) (hγ : γ = R.ν k / μ * (1 + eγ)) (heγ : |eγ| ≤ R.ε)
    (hδ : δ = ν / R.ν k * (1 + eδ)) (heδ : |eδ| ≤ R.ε) :
    (∀ j ≤ k + 1, (Function.update R.ν (k + 1) (ν)) j = ‖WithLp.toLp 2 ((Function.update R.r (k
      + 1) (next.r)) j)‖ ^ 2 * (1 + (Function.update R.θ (k + 1) (θ)) j)) ∧
    (∀ j ≤ k + 1, |(Function.update R.θ (k + 1) (θ)) j| ≤ R.ε) ∧
    (∀ j < k + 1, 0 < (Function.update R.ν (k + 1) (ν)) j) ∧
    (∀ j < k + 1, (Function.update R.γ k (γ)) j = (Function.update R.ν (k + 1) (ν)) j /
      (Function.update R.μ k (μ)) j * (1 + (Function.update R.eγ k (eγ)) j)) ∧
    (∀ j < k + 1, |(Function.update R.eγ k (eγ)) j| ≤ R.ε) ∧
    (∀ j < k + 1, (Function.update R.δ k (δ)) j = (Function.update R.ν (k + 1) (ν)) (j + 1) /
      (Function.update R.ν (k + 1) (ν)) j * (1 + (Function.update R.eδ k (eδ)) j)) ∧
    (∀ j < k + 1, |(Function.update R.eδ k (eδ)) j| ≤ R.ε) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact forall_le_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k + 1 by omega)] using R.ν_eq j hj) (by
      simpa only [Function.update_self, WithLp.toLp_neg, norm_neg, abs_neg] using hν)
  · exact forall_le_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k + 1 by omega)] using R.abs_θ_le j hj) (by
      simpa only [Function.update_self, WithLp.toLp_neg, norm_neg, abs_neg] using hθ)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.ν_pos j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hνpos)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.γ_eq j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hγ)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.abs_eγ_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using heγ)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.δ_eq j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hδ)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.abs_eδ_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using heδ)

private theorem product_fields {N k : ℕ} (R : CGRun N k)
    (next : CGState ℝ (Fin N)) (sv : Fin N → ℝ) (μ : ℝ) (hμpos : 0 < μ)
    (hs : ‖WithLp.toLp 2 (R.A *ᵥ R.p k - sv)‖ ≤
      R.ε * specNorm R.A * ‖WithLp.toLp 2 (R.p k)‖)
    (hμ : |R.p k ⬝ᵥ sv - μ| ≤ R.ε * ‖WithLp.toLp 2 (R.p k)‖ * ‖WithLp.toLp 2 sv‖) :
    (∀ j < k + 1, (Function.update R.s k (sv)) j = R.A *ᵥ ((Function.update R.p (k + 1)
      (next.p)) j) + (Function.update R.es k (-(R.A *ᵥ R.p k - sv))) j) ∧
    (∀ j < k + 1, ‖WithLp.toLp 2 ((Function.update R.es k (-(R.A *ᵥ R.p k - sv))) j)‖ ≤ R.ε *
      specNorm R.A * ‖WithLp.toLp 2 ((Function.update R.p (k + 1) (next.p)) j)‖) ∧
    (∀ j < k + 1, (Function.update R.μ k (μ)) j = ((Function.update R.p (k + 1) (next.p)) j) ⬝ᵥ
      ((Function.update R.s k (sv)) j) + (Function.update R.eμ k (-(R.p k ⬝ᵥ sv - μ))) j) ∧
    (∀ j < k + 1, |(Function.update R.eμ k (-(R.p k ⬝ᵥ sv - μ))) j| ≤ R.ε * ‖WithLp.toLp 2
      ((Function.update R.p (k + 1) (next.p)) j)‖ * ‖WithLp.toLp 2 ((Function.update R.s k (sv))
      j)‖) ∧
    (∀ j < k + 1, 0 < (Function.update R.μ k (μ)) j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.s_eq j hj) (by
      simp only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega), neg_sub]
      abel)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.norm_es_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hs)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.μ_eq j hj) (by
      simp only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega), neg_sub]
      abel)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.abs_eμ_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hμ)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.μ_pos j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hμpos)

private theorem update_fields {N k : ℕ} (R : CGRun N k)
    (next : CGState ℝ (Fin N)) (sv : Fin N → ℝ) (γ δ : ℝ)
    (hex : ‖WithLp.toLp 2 (R.x k + γ • R.p k - next.x)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.x k)‖ + |γ| * ‖WithLp.toLp 2 (R.p k)‖))
    (her : ‖WithLp.toLp 2 (R.r k - γ • sv - next.r)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.r k)‖ + |γ| * ‖WithLp.toLp 2 sv‖))
    (hep : ‖WithLp.toLp 2 (next.r + δ • R.p k - next.p)‖ ≤
      R.ε * (‖WithLp.toLp 2 next.r‖ + |δ| * ‖WithLp.toLp 2 (R.p k)‖)) :
    (∀ j < k + 1, (Function.update R.x (k + 1) (next.x)) (j + 1) = (Function.update R.x (k + 1)
      (next.x)) j + ((Function.update R.γ k (γ)) j) • ((Function.update R.p (k + 1) (next.p)) j)
      + (Function.update R.ex k (-(R.x k + γ • R.p k - next.x))) j) ∧
    (∀ j < k + 1, ‖WithLp.toLp 2 ((Function.update R.ex k (-(R.x k + γ • R.p k - next.x))) j)‖ ≤
      R.ε * (‖WithLp.toLp 2 ((Function.update R.x (k + 1) (next.x)) j)‖ + |(Function.update R.γ
      k (γ)) j| * ‖WithLp.toLp 2 ((Function.update R.p (k + 1) (next.p)) j)‖)) ∧
    (∀ j < k + 1, (Function.update R.r (k + 1) (next.r)) (j + 1) = (Function.update R.r (k + 1)
      (next.r)) j - ((Function.update R.γ k (γ)) j) • ((Function.update R.s k (sv)) j) +
      (Function.update R.er k (-(R.r k - γ • sv - next.r))) j) ∧
    (∀ j < k + 1, ‖WithLp.toLp 2 ((Function.update R.er k (-(R.r k - γ • sv - next.r))) j)‖ ≤
      R.ε * (‖WithLp.toLp 2 ((Function.update R.r (k + 1) (next.r)) j)‖ + |(Function.update R.γ
      k (γ)) j| * ‖WithLp.toLp 2 ((Function.update R.s k (sv)) j)‖)) ∧
    (∀ j < k + 1, (Function.update R.p (k + 1) (next.p)) (j + 1) = (Function.update R.r (k + 1)
      (next.r)) (j + 1) + ((Function.update R.δ k (δ)) j) • ((Function.update R.p (k + 1)
      (next.p)) j) + (Function.update R.ep k (-(next.r + δ • R.p k - next.p))) j) ∧
    (∀ j < k + 1, ‖WithLp.toLp 2 ((Function.update R.ep k (-(next.r + δ • R.p k - next.p))) j)‖
      ≤ R.ε * (‖WithLp.toLp 2 ((Function.update R.r (k + 1) (next.r)) (j + 1))‖ +
      |(Function.update R.δ k (δ)) j| * ‖WithLp.toLp 2 ((Function.update R.p (k + 1) (next.p))
      j)‖)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.x_succ j hj) (by
      simp only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega), neg_sub]
      abel)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.norm_ex_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hex)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.r_succ j hj) (by
      simp only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega), neg_sub]
      abel)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.norm_er_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using her)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.p_succ j hj) (by
      simp only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega), neg_sub]
      abel)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.norm_ep_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hep)

/-- Append one step's extracted data to the existing run. The hypotheses here are supplied
by actual primitive execution in the bridge, and are not assumptions of its input theorem. -/
private noncomputable def extend {N k : ℕ} (R : CGRun N k)
    (next : CGState ℝ (Fin N)) (sv : Fin N → ℝ)
    (ν θ μ γ eγ δ eδ : ℝ) (hνpos : 0 < R.ν k) (hμpos : 0 < μ)
    (hν : ν = ‖WithLp.toLp 2 next.r‖ ^ 2 * (1 + θ)) (hθ : |θ| ≤ R.ε)
    (hs : ‖WithLp.toLp 2 (R.A *ᵥ R.p k - sv)‖ ≤
      R.ε * specNorm R.A * ‖WithLp.toLp 2 (R.p k)‖)
    (hμ : |R.p k ⬝ᵥ sv - μ| ≤ R.ε * ‖WithLp.toLp 2 (R.p k)‖ * ‖WithLp.toLp 2 sv‖)
    (hγ : γ = R.ν k / μ * (1 + eγ)) (heγ : |eγ| ≤ R.ε)
    (hδ : δ = ν / R.ν k * (1 + eδ)) (heδ : |eδ| ≤ R.ε)
    (hex : ‖WithLp.toLp 2 (R.x k + γ • R.p k - next.x)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.x k)‖ + |γ| * ‖WithLp.toLp 2 (R.p k)‖))
    (her : ‖WithLp.toLp 2 (R.r k - γ • sv - next.r)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.r k)‖ + |γ| * ‖WithLp.toLp 2 sv‖))
    (hep : ‖WithLp.toLp 2 (next.r + δ • R.p k - next.p)‖ ≤
      R.ε * (‖WithLp.toLp 2 next.r‖ + |δ| * ‖WithLp.toLp 2 (R.p k)‖)) :
    CGRun N (k + 1) := by
  have hc := cache_fields R next ν θ μ γ eγ δ eδ hνpos hν hθ hγ heγ hδ heδ
  have hp := product_fields R next sv μ hμpos hs hμ
  have hu := update_fields R next sv γ δ hex her hep
  exact {
    A := R.A
    b := R.b
    x := Function.update R.x (k + 1) (next.x)
    r := Function.update R.r (k + 1) (next.r)
    p := Function.update R.p (k + 1) (next.p)
    ν := Function.update R.ν (k + 1) (ν)
    θ := Function.update R.θ (k + 1) (θ)
    s := Function.update R.s k (sv)
    μ := Function.update R.μ k (μ)
    γ := Function.update R.γ k (γ)
    δ := Function.update R.δ k (δ)
    es := Function.update R.es k (-(R.A *ᵥ R.p k - sv))
    eμ := Function.update R.eμ k (-(R.p k ⬝ᵥ sv - μ))
    eγ := Function.update R.eγ k (eγ)
    ex := Function.update R.ex k (-(R.x k + γ • R.p k - next.x))
    er := Function.update R.er k (-(R.r k - γ • sv - next.r))
    eδ := Function.update R.eδ k (eδ)
    ep := Function.update R.ep k (-(next.r + δ • R.p k - next.p))
    ε := R.ε
    transpose_A := R.transpose_A
    ε_nonneg := R.ε_nonneg
    ε_le := R.ε_le
    k_pos := by omega
    x_zero := by simpa only [Function.update_of_ne (show 0 ≠ k + 1 by omega)] using R.x_zero
    r_zero := by simpa only [Function.update_of_ne (show 0 ≠ k + 1 by omega)] using R.r_zero
    p_zero := by simpa only [Function.update_of_ne (show 0 ≠ k + 1 by omega)] using R.p_zero
    ν_eq := hc.1
    abs_θ_le := hc.2.1
    ν_pos := hc.2.2.1
    s_eq := hp.1
    norm_es_le := hp.2.1
    μ_eq := hp.2.2.1
    abs_eμ_le := hp.2.2.2.1
    μ_pos := hp.2.2.2.2
    γ_eq := hc.2.2.2.1
    abs_eγ_le := hc.2.2.2.2.1
    x_succ := hu.1
    norm_ex_le := hu.2.1
    r_succ := hu.2.2.1
    norm_er_le := hu.2.2.2.1
    δ_eq := hc.2.2.2.2.2.1
    abs_eδ_le := hc.2.2.2.2.2.2
    p_succ := hu.2.2.2.2.1
    norm_ep_le := hu.2.2.2.2.2
  }

/-- The existing run can be extended by the defects derived from one actual next step.
All previous numerical data are retained by point updates; no extra run interface is used. -/
theorem exists_extend {N k : ℕ} (R : CGRun N k)
    (next : CGState ℝ (Fin N)) (sv : Fin N → ℝ)
    (ν θ μ γ eγ δ eδ : ℝ) (hνpos : 0 < R.ν k) (hμpos : 0 < μ)
    (hν : ν = ‖WithLp.toLp 2 next.r‖ ^ 2 * (1 + θ)) (hθ : |θ| ≤ R.ε)
    (hs : ‖WithLp.toLp 2 (R.A *ᵥ R.p k - sv)‖ ≤
      R.ε * specNorm R.A * ‖WithLp.toLp 2 (R.p k)‖)
    (hμ : |R.p k ⬝ᵥ sv - μ| ≤ R.ε * ‖WithLp.toLp 2 (R.p k)‖ * ‖WithLp.toLp 2 sv‖)
    (hγ : γ = R.ν k / μ * (1 + eγ)) (heγ : |eγ| ≤ R.ε)
    (hδ : δ = ν / R.ν k * (1 + eδ)) (heδ : |eδ| ≤ R.ε)
    (hex : ‖WithLp.toLp 2 (R.x k + γ • R.p k - next.x)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.x k)‖ + |γ| * ‖WithLp.toLp 2 (R.p k)‖))
    (her : ‖WithLp.toLp 2 (R.r k - γ • sv - next.r)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.r k)‖ + |γ| * ‖WithLp.toLp 2 sv‖))
    (hep : ‖WithLp.toLp 2 (next.r + δ • R.p k - next.p)‖ ≤
      R.ε * (‖WithLp.toLp 2 next.r‖ + |δ| * ‖WithLp.toLp 2 (R.p k)‖)) :
    ∃ S : CGRun N (k + 1), S.A = R.A ∧ S.b = R.b ∧ S.ε = R.ε ∧
      S.x = Function.update R.x (k + 1) (next.x) ∧
      S.r = Function.update R.r (k + 1) (next.r) ∧
      S.p = Function.update R.p (k + 1) (next.p) ∧
      S.ν = Function.update R.ν (k + 1) (ν) ∧
      S.θ = Function.update R.θ (k + 1) (θ) ∧
      S.s = Function.update R.s k (sv) ∧
      S.μ = Function.update R.μ k (μ) ∧
      S.γ = Function.update R.γ k (γ) ∧
      S.δ = Function.update R.δ k (δ) ∧
      S.es = Function.update R.es k (-(R.A *ᵥ R.p k - sv)) ∧
      S.eμ = Function.update R.eμ k (-(R.p k ⬝ᵥ sv - μ)) ∧
      S.eγ = Function.update R.eγ k (eγ) ∧
      S.ex = Function.update R.ex k (-(R.x k + γ • R.p k - next.x)) ∧
      S.er = Function.update R.er k (-(R.r k - γ • sv - next.r)) ∧
      S.eδ = Function.update R.eδ k (eδ) ∧
      S.ep = Function.update R.ep k (-(next.r + δ • R.p k - next.p)) := by
  exact ⟨extend R next sv ν θ μ γ eγ δ eδ hνpos hμpos hν hθ hs hμ
    hγ heγ hδ heδ hex her hep, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


end CGRun

end NLAlib
