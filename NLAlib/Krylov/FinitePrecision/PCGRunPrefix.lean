/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.PCGRun

/-!
# Extending PCG run prefixes

Point updates retain an existing PCG run and append actual local defects, including the
fixed nonlinear preconditioner action and both adjacent computed pairings.

## Main results

* `NLAlib.PCGRun.exists_extend` appends one step to an existing PCG run.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

namespace PCGRun

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

private theorem cache_fields {N k : ℕ} (R : PCGRun N k)
    (ν μ γ eγ δ eδ : ℝ)
    (hνpos : 0 < R.ν k) (hγ : γ = R.ν k / μ * (1 + eγ)) (heγ : |eγ| ≤ R.ε)
    (hδ : δ = ν / R.ν k * (1 + eδ)) (heδ : |eδ| ≤ R.ε) :
    (∀ j < k + 1, 0 < (Function.update R.ν (k + 1) (ν)) j) ∧
    (∀ j < k + 1, (Function.update R.γ k (γ)) j = (Function.update R.ν (k + 1) (ν)) j /
      (Function.update R.μ k (μ)) j * (1 + (Function.update R.eγ k (eγ)) j)) ∧
    (∀ j < k + 1, |(Function.update R.eγ k (eγ)) j| ≤ R.ε) ∧
    (∀ j < k + 1, (Function.update R.δ k (δ)) j = (Function.update R.ν (k + 1) (ν)) (j + 1) /
      (Function.update R.ν (k + 1) (ν)) j * (1 + (Function.update R.eδ k (eδ)) j)) ∧
    (∀ j < k + 1, |(Function.update R.eδ k (eδ)) j| ≤ R.ε) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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

private theorem product_fields {N k : ℕ} (R : PCGRun N k)
    (next : PCGState ℝ (Fin N)) (sv : Fin N → ℝ) (μ : ℝ) (hμpos : 0 < μ)
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

private theorem update_fields {N k : ℕ} (R : PCGRun N k)
    (next : PCGState ℝ (Fin N)) (sv : Fin N → ℝ) (γ δ : ℝ)
    (hex : ‖WithLp.toLp 2 (R.x k + γ • R.p k - next.x)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.x k)‖ + |γ| * ‖WithLp.toLp 2 (R.p k)‖))
    (her : ‖WithLp.toLp 2 (R.r k - γ • sv - next.r)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.r k)‖ + |γ| * ‖WithLp.toLp 2 sv‖))
    (hep : ‖WithLp.toLp 2 (next.z + δ • R.p k - next.p)‖ ≤
      R.ε * (‖WithLp.toLp 2 next.z‖ + |δ| * ‖WithLp.toLp 2 (R.p k)‖)) :
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
    (∀ j < k + 1, (Function.update R.p (k + 1) (next.p)) (j + 1) = (Function.update R.z (k + 1)
      (next.z)) (j + 1) + ((Function.update R.δ k (δ)) j) • ((Function.update R.p (k + 1)
      (next.p)) j) + (Function.update R.ep k (-(next.z + δ • R.p k - next.p))) j) ∧
    (∀ j < k + 1, ‖WithLp.toLp 2 ((Function.update R.ep k (-(next.z + δ • R.p k - next.p))) j)‖
      ≤ R.ε * (‖WithLp.toLp 2 ((Function.update R.z (k + 1) (next.z)) (j + 1))‖ +
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
private noncomputable def extend {N k : ℕ} (R : PCGRun N k)
    (next : PCGState ℝ (Fin N)) (sv : Fin N → ℝ)
    (ν μ γ eγ δ eδ : ℝ) (hνpos : 0 < R.ν k) (hμpos : 0 < μ)
    (hz : next.z = R.preconditioner.mulVec next.r)
    (hν : |ν - next.r ⬝ᵥ next.z| ≤
      R.ε * ‖WithLp.toLp 2 next.r‖ * ‖WithLp.toLp 2 next.z‖) (hlast : 0 ≤ ν)
    (hs : ‖WithLp.toLp 2 (R.A *ᵥ R.p k - sv)‖ ≤
      R.ε * specNorm R.A * ‖WithLp.toLp 2 (R.p k)‖)
    (hμ : |R.p k ⬝ᵥ sv - μ| ≤ R.ε * ‖WithLp.toLp 2 (R.p k)‖ * ‖WithLp.toLp 2 sv‖)
    (hγ : γ = R.ν k / μ * (1 + eγ)) (heγ : |eγ| ≤ R.ε)
    (hδ : δ = ν / R.ν k * (1 + eδ)) (heδ : |eδ| ≤ R.ε)
    (hex : ‖WithLp.toLp 2 (R.x k + γ • R.p k - next.x)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.x k)‖ + |γ| * ‖WithLp.toLp 2 (R.p k)‖))
    (her : ‖WithLp.toLp 2 (R.r k - γ • sv - next.r)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.r k)‖ + |γ| * ‖WithLp.toLp 2 sv‖))
    (hep : ‖WithLp.toLp 2 (next.z + δ • R.p k - next.p)‖ ≤
      R.ε * (‖WithLp.toLp 2 next.z‖ + |δ| * ‖WithLp.toLp 2 (R.p k)‖)) :
    PCGRun N (k + 1) := by
  have hc := cache_fields R ν μ γ eγ δ eδ hνpos hγ heγ hδ heδ
  have hp := product_fields R next sv μ hμpos hs hμ
  have hu := update_fields R next sv γ δ hex her hep
  exact {
    A := R.A
    M := R.M
    preconditioner := R.preconditioner
    posDef_M := R.posDef_M
    b := R.b
    x := Function.update R.x (k + 1) (next.x)
    r := Function.update R.r (k + 1) (next.r)
    z := Function.update R.z (k + 1) next.z
    p := Function.update R.p (k + 1) (next.p)
    ν := Function.update R.ν (k + 1) (ν)
    eν := Function.update R.eν (k + 1) (ν - next.r ⬝ᵥ next.z)
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
    ep := Function.update R.ep k (-(next.z + δ • R.p k - next.p))
    ε := R.ε
    isHermitian_A := R.isHermitian_A
    ε_nonneg := R.ε_nonneg
    ε_le := R.ε_le
    k_pos := by omega
    x_zero := by simpa only [Function.update_of_ne (show 0 ≠ k + 1 by omega)] using R.x_zero
    r_zero := by simpa only [Function.update_of_ne (show 0 ≠ k + 1 by omega)] using R.r_zero
    p_zero := by simpa only [Function.update_of_ne (show 0 ≠ k + 1 by omega)] using R.p_zero
    z_eq := forall_le_succ (fun j hj => by
      simpa only [Function.update_of_ne (show j ≠ k + 1 by omega)] using R.z_eq j hj)
      (by simpa only [Function.update_self] using hz)
    ν_eq := forall_le_succ (fun j hj => by
      simpa only [Function.update_of_ne (show j ≠ k + 1 by omega)] using R.ν_eq j hj)
      (by simp only [Function.update_self]; ring)
    abs_eν_le := forall_le_succ (fun j hj => by
      simpa only [Function.update_of_ne (show j ≠ k + 1 by omega)] using R.abs_eν_le j hj)
      (by simpa only [Function.update_self] using hν)
    ν_last_nonneg := by simpa only [Function.update_self] using hlast
    ν_pos := hc.1
    s_eq := hp.1
    norm_es_le := hp.2.1
    μ_eq := hp.2.2.1
    abs_eμ_le := hp.2.2.2.1
    μ_pos := hp.2.2.2.2
    γ_eq := hc.2.1
    abs_eγ_le := hc.2.2.1
    x_succ := hu.1
    norm_ex_le := hu.2.1
    r_succ := hu.2.2.1
    norm_er_le := hu.2.2.2.1
    δ_eq := hc.2.2.2.1
    abs_eδ_le := hc.2.2.2.2
    p_succ := hu.2.2.2.2.1
    norm_ep_le := hu.2.2.2.2.2
  }

/-- The existing run can be extended by the defects derived from one actual next step.
All previous numerical data are retained by point updates; no extra run interface is used. -/
theorem exists_extend {N k : ℕ} (R : PCGRun N k)
    (next : PCGState ℝ (Fin N)) (sv : Fin N → ℝ)
    (ν μ γ eγ δ eδ : ℝ) (hνpos : 0 < R.ν k) (hμpos : 0 < μ)
    (hz : next.z = R.preconditioner.mulVec next.r)
    (hν : |ν - next.r ⬝ᵥ next.z| ≤
      R.ε * ‖WithLp.toLp 2 next.r‖ * ‖WithLp.toLp 2 next.z‖) (hlast : 0 ≤ ν)
    (hs : ‖WithLp.toLp 2 (R.A *ᵥ R.p k - sv)‖ ≤
      R.ε * specNorm R.A * ‖WithLp.toLp 2 (R.p k)‖)
    (hμ : |R.p k ⬝ᵥ sv - μ| ≤ R.ε * ‖WithLp.toLp 2 (R.p k)‖ * ‖WithLp.toLp 2 sv‖)
    (hγ : γ = R.ν k / μ * (1 + eγ)) (heγ : |eγ| ≤ R.ε)
    (hδ : δ = ν / R.ν k * (1 + eδ)) (heδ : |eδ| ≤ R.ε)
    (hex : ‖WithLp.toLp 2 (R.x k + γ • R.p k - next.x)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.x k)‖ + |γ| * ‖WithLp.toLp 2 (R.p k)‖))
    (her : ‖WithLp.toLp 2 (R.r k - γ • sv - next.r)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.r k)‖ + |γ| * ‖WithLp.toLp 2 sv‖))
    (hep : ‖WithLp.toLp 2 (next.z + δ • R.p k - next.p)‖ ≤
      R.ε * (‖WithLp.toLp 2 next.z‖ + |δ| * ‖WithLp.toLp 2 (R.p k)‖)) :
    ∃ S : PCGRun N (k + 1), S.A = R.A ∧ S.M = R.M ∧ HEq S.preconditioner R.preconditioner ∧
      S.b = R.b ∧ S.ε = R.ε ∧
      S.x = Function.update R.x (k + 1) (next.x) ∧
      S.r = Function.update R.r (k + 1) (next.r) ∧
      S.z = Function.update R.z (k + 1) next.z ∧
      S.p = Function.update R.p (k + 1) (next.p) ∧
      S.ν = Function.update R.ν (k + 1) (ν) ∧
      S.eν = Function.update R.eν (k + 1) (ν - next.r ⬝ᵥ next.z) ∧
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
      S.ep = Function.update R.ep k (-(next.z + δ • R.p k - next.p)) := by
  refine ⟨extend R next sv ν μ γ eγ δ eδ hνpos hμpos hz hν hlast hs hμ
    hγ heγ hδ heδ hex her hep, ?_⟩
  exact ⟨rfl, rfl, HEq.rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end PCGRun

end NLAlib
