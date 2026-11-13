/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.CGRun
public import NLAlib.Ops.ArithmeticError

/-!
# Transferring mixed local CG errors to the relative run theory

An active prefix whose absolute defects fit explicit relative-budget margins admits the
existing `NLAlib.CGRun` model. This reuses the backward, convergence and physical-error
theory without another run structure. The constructor retains the supplied iterates,
residuals, directions, products and computed scalars definitionally.

The margins are real hypotheses, not consequences of successful finite arithmetic. They
can fail near underflow, notably at a zero cache with a nonzero residual. Actual cache and
curvature positivity are also retained as independent prefix certificates. Mixed residual-gap
and zero-cache bounds remain applicable when the margins fail.

## Main results

* `NLAlib.CGRun.ofAbsRelErr`: a scale-certified prefix in the existing run model.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.CGRun

/-- Construct the existing CG run from mixed local certificates and explicit scale margins.
The base relative allowance is $u\ge0$ and the resulting allowance satisfies
$u\le\varepsilon\le1/100$. Each absolute allowance must fit
$(\varepsilon-u)$ times its local scale. For norm caches the scale is the squared residual
norm; for scalar divisions it is the exact quotient magnitude. Vector and curvature scales
are displayed in the hypotheses.

Cache and curvature positivity on every step taken are separate hypotheses. In particular,
this constructor does not certify a zero-cache underflow endpoint or a quotient that rounded
to zero. Every supplied data array, including the computed scalars, is preserved definitionally;
only the relative scalar witnesses are chosen. -/
noncomputable def ofAbsRelErr {n k : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (x r p s es ex er ep : ℕ → Fin n → ℝ) (ν μ γ δ : ℕ → ℝ)
    (u ε : ℝ) (ην ηs ημ ηγ ηx ηr ηδ ηp : ℕ → ℝ)
    (hA : Aᵀ = A) (hk : 0 < k) (hu : 0 ≤ u) (huε : u ≤ ε) (hε : ε ≤ 1 / 100)
    (hx0 : x 0 = 0) (hr0 : r 0 = b) (hp0 : p 0 = b)
    (hν : ∀ j ≤ k, Computation.AbsRelErr u (ην j) (‖WithLp.toLp 2 (r j)‖ ^ 2) (ν j))
    (hνmargin : ∀ j ≤ k, ην j ≤ (ε - u) * ‖WithLp.toLp 2 (r j)‖ ^ 2)
    (hνpos : ∀ j < k, 0 < ν j)
    (hs : ∀ j < k, s j = A *ᵥ p j + es j)
    (hes : ∀ j < k, ‖WithLp.toLp 2 (es j)‖ ≤
      u * (specNorm A * ‖WithLp.toLp 2 (p j)‖) + ηs j)
    (hsMargin : ∀ j < k, ηs j ≤ (ε - u) * (specNorm A * ‖WithLp.toLp 2 (p j)‖))
    (hμ : ∀ j < k, |p j ⬝ᵥ s j - μ j| ≤
      u * (‖WithLp.toLp 2 (p j)‖ * ‖WithLp.toLp 2 (s j)‖) + ημ j)
    (hμmargin : ∀ j < k, ημ j ≤
      (ε - u) * (‖WithLp.toLp 2 (p j)‖ * ‖WithLp.toLp 2 (s j)‖))
    (hμpos : ∀ j < k, 0 < μ j)
    (hγ : ∀ j < k, Computation.AbsRelErr u (ηγ j) (ν j / μ j) (γ j))
    (hγmargin : ∀ j < k, ηγ j ≤ (ε - u) * |ν j / μ j|)
    (hx : ∀ j < k, x (j + 1) = x j + γ j • p j + ex j)
    (hex : ∀ j < k, ‖WithLp.toLp 2 (ex j)‖ ≤
      u * (‖WithLp.toLp 2 (x j)‖ + |γ j| * ‖WithLp.toLp 2 (p j)‖) + ηx j)
    (hxMargin : ∀ j < k, ηx j ≤
      (ε - u) * (‖WithLp.toLp 2 (x j)‖ + |γ j| * ‖WithLp.toLp 2 (p j)‖))
    (hr : ∀ j < k, r (j + 1) = r j - γ j • s j + er j)
    (her : ∀ j < k, ‖WithLp.toLp 2 (er j)‖ ≤
      u * (‖WithLp.toLp 2 (r j)‖ + |γ j| * ‖WithLp.toLp 2 (s j)‖) + ηr j)
    (hrMargin : ∀ j < k, ηr j ≤
      (ε - u) * (‖WithLp.toLp 2 (r j)‖ + |γ j| * ‖WithLp.toLp 2 (s j)‖))
    (hδ : ∀ j < k, Computation.AbsRelErr u (ηδ j) (ν (j + 1) / ν j) (δ j))
    (hδmargin : ∀ j < k, ηδ j ≤ (ε - u) * |ν (j + 1) / ν j|)
    (hp : ∀ j < k, p (j + 1) = r (j + 1) + δ j • p j + ep j)
    (hep : ∀ j < k, ‖WithLp.toLp 2 (ep j)‖ ≤
      u * (‖WithLp.toLp 2 (r (j + 1))‖ + |δ j| * ‖WithLp.toLp 2 (p j)‖) + ηp j)
    (hpMargin : ∀ j < k, ηp j ≤
      (ε - u) * (‖WithLp.toLp 2 (r (j + 1))‖ + |δ j| * ‖WithLp.toLp 2 (p j)‖)) :
    CGRun n k := by
  classical
  let hn (j : ℕ) (hj : j ≤ k) :=
    (hν j hj).relErr_of_le (hu.trans huε)
      (by simpa only [abs_of_nonneg (sq_nonneg ‖WithLp.toLp 2 (r j)‖)]
        using hνmargin j hj)
  let hg (j : ℕ) (hj : j < k) :=
    (hγ j hj).relErr_of_le (hu.trans huε) (hγmargin j hj)
  let hd (j : ℕ) (hj : j < k) :=
    (hδ j hj).relErr_of_le (hu.trans huε) (hδmargin j hj)
  let θ (j : ℕ) := if hj : j ≤ k then (hn j hj).choose else 0
  let eγ (j : ℕ) := if hj : j < k then (hg j hj).choose else 0
  let eδ (j : ℕ) := if hj : j < k then (hd j hj).choose else 0
  exact
    { A := A, b := b, x := x, r := r, p := p, s := s, ν := ν, μ := μ, γ := γ, δ := δ
      es := es, θ := θ, eμ := fun j => μ j - p j ⬝ᵥ s j, eγ := eγ
      ex := ex, er := er, eδ := eδ, ep := ep, ε := ε
      transpose_A := hA
      ε_nonneg := hu.trans huε
      k_pos := hk
      ε_le := hε
      x_zero := hx0
      r_zero := hr0
      p_zero := hp0
      ν_eq := fun j hj => by simpa only [θ, dif_pos hj] using (hn j hj).choose_spec.2
      abs_θ_le := fun j hj => by simpa only [θ, dif_pos hj] using (hn j hj).choose_spec.1
      ν_pos := hνpos
      s_eq := hs
      norm_es_le := fun j hj => by
        nlinarith only [hes j hj, hsMargin j hj]
      μ_eq := fun j _ => by ring
      abs_eμ_le := fun j hj => by
        rw [abs_sub_comm]
        nlinarith only [hμ j hj, hμmargin j hj]
      μ_pos := hμpos
      γ_eq := fun j hj => by simpa only [eγ, dif_pos hj] using (hg j hj).choose_spec.2
      abs_eγ_le := fun j hj => by simpa only [eγ, dif_pos hj] using (hg j hj).choose_spec.1
      x_succ := hx
      norm_ex_le := fun j hj => by nlinarith only [hex j hj, hxMargin j hj]
      r_succ := hr
      norm_er_le := fun j hj => by nlinarith only [her j hj, hrMargin j hj]
      δ_eq := fun j hj => by simpa only [eδ, dif_pos hj] using (hd j hj).choose_spec.2
      abs_eδ_le := fun j hj => by simpa only [eδ, dif_pos hj] using (hd j hj).choose_spec.1
      p_succ := hp
      norm_ep_le := fun j hj => by nlinarith only [hep j hj, hpMargin j hj] }

end NLAlib.CGRun
