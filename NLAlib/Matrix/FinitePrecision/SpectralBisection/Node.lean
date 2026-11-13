/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.SpectralBisection.Assembly

/-!
# Local guarantee of a node of spectral bisection

A node of the machine
algorithm `NLAlib.eighAux` with a good sample whose children return approximate
diagonalizations returns one itself, with residual $\varepsilon(R + R_0)$ and singular values
within $\varepsilon/3$ of $1$ ([Shah2024, Lemma 4.1]), under the precision budget
`NLAlib.FloatMachine.IsEighNodeBudget`; leaves are treated directly. The assembly of the output
from the children's is in `NLAlib/Matrix/Computation/SpectralBisection/Assembly.lean`.

## Main results

* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_leaf`: the leaves.
* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighNodeBudget`:
  Lemma 4.1.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- The stored half window $\lvert\mathrm{fl}(R/\mathrm{fl}(2))\rvert \le R/2 + 2uR + u\tau$. -/
private theorem FloatMachine.IsAccurate.abs_dec_div_ofNat_two_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R : F} (hu : 0 ≤ u) (hu1 : u ≤ 1 / 1000)
    (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1 / 4) (hR : 0 ≤ dec R) (hRΩ : dec R ≤ Ω) (hΩ : 2 ≤ Ω) :
    |dec (M.div R (M.ofNat 2))| ≤ dec R / 2 + 2 * u * dec R + u * τ := by
  have h2 := abs_le.mp (abs_sub_le_of_isRoundingOf (hM.ofNat 2) (by norm_num; linarith) hu hτ₀)
  push_cast at h2
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
  have huτ := mul_le_mul_of_nonneg_left hτ hu
  have ht1 : 2 - 3 * u ≤ dec (M.ofNat 2) := by linarith
  have ht0 : 0 < dec (M.ofNat 2) := by linarith
  have hRt : dec R / dec (M.ofNat 2) ≤ dec R / 2 + u * dec R := by
    rw [div_le_iff₀ ht0]
    have := mul_le_mul_of_nonneg_right ht1 (by positivity : 0 ≤ dec R / 2 + u * dec R)
    nlinarith [mul_nonneg (mul_nonneg hu hu) hR]
  have hRt0 : 0 ≤ dec R / dec (M.ofNat 2) := div_nonneg hR ht0.le
  have hd := abs_sub_le_of_isRoundingOf (hM.div R (M.ofNat 2) ht0.ne')
    (by rw [abs_of_nonneg hRt0]; nlinarith) hu hτ₀
  rw [abs_of_nonneg hRt0, abs_sub_comm] at hd
  have h3 := abs_sub_abs_le_abs_sub (dec (M.div R (M.ofNat 2))) (dec R / dec (M.ofNat 2))
  rw [abs_of_nonneg hRt0] at h3
  nlinarith [mul_le_mul_of_nonneg_left hRt hu, mul_nonneg (mul_nonneg hu hu) hR]

/-- The child's tolerance $e'$ and window $r'$, the half window $s$ and the terms
$\kappa = e'/3$, $\rho = e'(r' + R_0)$ of the budget of a node, against $w = 1/\ell$. -/
private theorem node_budget_params {ε w R R₀ u τ e' r' κ ρ s : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8)
    (hw0 : 0 < w) (hw20 : w ≤ 1 / 20) (hR : 0 ≤ R) (hR₀ : 0 ≤ R₀) (hu : 0 ≤ u)
    (hu' : u * 1000000 ≤ ε * w) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1 / 4) (hτR : τ * 4 ≤ ε * R₀)
    (he'₁ : (1 - w) * (1 - 9 * u) * ε - u * τ ≤ e') (he'₂ : e' ≤ (1 - w) * ε + 7 * u * ε + u * τ)
    (hr'₀ : 0 ≤ r') (hr' : r' ≤ (1 / 2 + 2 * w) * (1 + 22 * u) * R + u * τ) (hκ : κ = e' / 3)
    (hs : s = R / 2 + 2 * u * R + u * τ) (hρ : ρ = e' * (r' + R₀)) :
    0 ≤ e' ∧ e' ≤ ε * (1 - w + 2 * w / 1000000) ∧ 0 ≤ κ ∧ κ ≤ 1 / 24 ∧ 0 ≤ ρ ∧ 0 ≤ s ∧
      ρ ≤ ε * (1 - w + 2 * w / 1000000) * ((1 / 2 + 2 * w + 2 * w / 1000000) * R +
        ε * w * R₀ / 10000000 + R₀) ∧
      s * (2 * κ + κ ^ 2) ≤ ((1 / 2 + w / 1000000) * R + ε * w * R₀ / 10000000) *
        (49 / 72 * (ε * (1 - w + 2 * w / 1000000))) ∧
      r' + ρ ≤ 6751 / 10000 * R + 1251 / 10000 * R₀ ∧ s ≤ 5001 / 10000 * R + R₀ / 10000 ∧
      u * R * 1000000 ≤ ε * w * R := by
  have hεw1 : ε * w ≤ 1 / 160 := by linarith [mul_le_mul hε₁ hw20 hw0.le (by norm_num)]
  have huτ : u * τ ≤ u / 4 := by linarith [mul_le_mul_of_nonneg_left hτ hu]
  have hεwR0 : 0 ≤ ε * w * R₀ := by positivity
  have hεwR : 0 ≤ ε * w * R := by positivity
  have hwR0 : 0 ≤ w * R := by positivity
  have huR0 : 0 ≤ u * R := by positivity
  have huτ0 : 0 ≤ u * τ := by positivity
  have huτR : u * τ * 10000000 ≤ ε * w * R₀ := by
    have h1 : u * τ * 4 ≤ u * (ε * R₀) := by linarith [mul_le_mul_of_nonneg_left hτR hu]
    have h2 := mul_le_mul_of_nonneg_right hu' (by positivity : 0 ≤ ε * R₀)
    have h3 := mul_le_mul_of_nonneg_left hε₁ (by positivity : 0 ≤ ε * w * R₀)
    linarith
  have huR : u * R * 1000000 ≤ ε * w * R := by linarith [mul_le_mul_of_nonneg_right hu' hR]
  have hεwR8 : ε * w * R ≤ w * R / 8 := by
    linarith [mul_le_mul_of_nonneg_right hε₁ (mul_nonneg hw0.le hR)]
  have hwuR : w * (u * R) ≤ u * R / 20 := by
    linarith [mul_le_mul_of_nonneg_right hw20 (mul_nonneg hu hR)]
  have hwR : w * R ≤ R / 20 := by linarith [mul_le_mul_of_nonneg_right hw20 hR]
  have hεwR₀ : ε * w * R₀ ≤ R₀ / 160 := by linarith [mul_le_mul_of_nonneg_right hεw1 hR₀]
  set E := ε * (1 - w + 2 * w / 1000000) with hE
  have hE' : e' ≤ E := by
    rw [hE]; linarith [mul_le_mul_of_nonneg_left hε₁ (by linarith : 0 ≤ 7 * u)]
  have he'0 : 0 ≤ e' := by
    have h1 : (1 / 2 : ℝ) ≤ (1 - w) * (1 - 9 * u) := by linarith [mul_nonneg hw0.le hu]
    linarith [mul_le_mul_of_nonneg_right h1 hε.le]
  have hE1 : E ≤ ε := by
    rw [hE]; linarith [mul_le_mul_of_nonneg_left (by linarith : 1 - w + 2 * w / 1000000 ≤ 1) hε.le]
  have hκ0 : 0 ≤ κ := by rw [hκ]; linarith
  have hκ1 : κ ≤ 1 / 24 := by rw [hκ]; linarith
  set Rr := (1 / 2 + 2 * w + 2 * w / 1000000) * R + ε * w * R₀ / 10000000 with hRr
  have hr'R : r' ≤ Rr := by rw [hRr]; linarith
  set Sb := (1 / 2 + w / 1000000) * R + ε * w * R₀ / 10000000 with hSb
  have hsS : s ≤ Sb := by rw [hs, hSb]; linarith
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hRR : 0 ≤ Rr + R₀ := by linarith [hr'₀.trans hr'R]
  have hρE : ρ ≤ E * (Rr + R₀) := by
    rw [hρ]; exact mul_le_mul hE' (by linarith) (by positivity) (he'0.trans hE')
  have hκ2 : 2 * κ + κ ^ 2 ≤ 49 / 72 * E := by
    linarith [mul_le_mul_of_nonneg_left hκ1 hκ0, sq κ]
  have hrρ : r' + ρ ≤ 6751 / 10000 * R + 1251 / 10000 * R₀ := by
    have h1 : E * (Rr + R₀) ≤ ε * (Rr + R₀) := mul_le_mul_of_nonneg_right hE1 hRR
    have h2 := mul_le_mul_of_nonneg_right hε₁ hRR
    have hRr6 : Rr ≤ 6000001 / 10000000 * R + R₀ / 1000000000 := by rw [hRr]; linarith
    linarith
  exact ⟨he'0, hE', hκ0, hκ1, by rw [hρ]; positivity, hs0, hρE,
    mul_le_mul hsS hκ2 (by positivity) (hs0.trans hsS), hrρ, by linarith, huR⟩

/-- The deflation, product and eigenvalue errors of the budget of a node, against $w = 1/\ell$. -/
private theorem node_budget_errors {ε w R R₀ u v τ η κ ρ s γ ξ Dn θ : ℝ} (hε : 0 < ε)
    (hε₁ : ε ≤ 1 / 8) (hw0 : 0 < w) (hw20 : w ≤ 1 / 20) (hR : 0 ≤ R) (hR₀ : 0 ≤ R₀)
    (hu : 0 ≤ u) (hu' : u * 1000000 ≤ ε * w) (hv : 0 ≤ v) (hv' : v * 100000 ≤ ε * w)
    (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1 / 4) (hτR : τ * 4 ≤ ε * R₀) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 24)
    (hs0 : 0 ≤ s) (hsb : s ≤ 5001 / 10000 * R + R₀ / 10000) (hρ0 : 0 ≤ ρ)
    (hρb : ρ ≤ 6751 / 10000 * R + 1251 / 10000 * R₀) (hη : η = (1 - w) * ε * w / 5)
    (hγ : γ = (2 + 2 * η) * R * η) (hξ : ξ = η * (1 + κ) + v * ((1 + η) * (1 + κ) + τ))
    (hDn : Dn = ρ / (1 - κ) ^ 2) (hθ : θ = u * (Dn + s + τ)) :
    0 ≤ η ∧ γ ≤ 4005 / 10000 * (ε * w * R) ∧ 0 ≤ ξ ∧ ξ ≤ 2084 / 10000 * (ε * w) ∧ 0 ≤ Dn ∧
      Dn ≤ 7352 / 10000 * R + 1363 / 10000 * R₀ ∧ 0 ≤ θ ∧
      (1 + κ) ^ 2 * θ ≤ ε * w * (R + R₀) / 100000 ∧
      ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ) ≤
        4345 / 10000 * (ε * w) * (12355 / 10000 * R + 1366 / 10000 * R₀) := by
  have hεw1 : ε * w ≤ 1 / 160 := by linarith [mul_le_mul hε₁ hw20 hw0.le (by norm_num)]
  have hεww : 0 ≤ ε * w * w := by positivity
  have hη0 : 0 ≤ η := by
    rw [hη]; exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) hε.le) hw0.le) (by norm_num)
  have hηw : η ≤ ε * w / 5 := by rw [hη]; linarith
  have hη1 : η ≤ 1 / 800 := by linarith
  have hγ' : γ ≤ 4005 / 10000 * (ε * w * R) := by
    rw [hγ]
    have h1 := mul_le_mul_of_nonneg_left hηw hR
    have h2 := mul_le_mul_of_nonneg_left hη1 (mul_nonneg hR hη0)
    linarith
  have hξ0 : 0 ≤ ξ := by rw [hξ]; positivity
  have hξ' : ξ ≤ 2084 / 10000 * (ε * w) := by
    rw [hξ]
    have h1 : η * (1 + κ) ≤ ε * w / 5 * (25 / 24) :=
      mul_le_mul hηw (by linarith) (by linarith) (by positivity)
    have h2 : (1 + η) * (1 + κ) ≤ (1 + 1 / 800) * (25 / 24) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    have h3 := mul_le_mul_of_nonneg_left (by linarith : (1 + η) * (1 + κ) + τ ≤ 1.31) hv
    linarith
  have hκd : (23 / 24 : ℝ) ^ 2 ≤ (1 - κ) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hDn0 : 0 ≤ Dn := by rw [hDn]; exact div_nonneg hρ0 (sq_nonneg _)
  have hDn' : Dn ≤ 7352 / 10000 * R + 1363 / 10000 * R₀ := by
    rw [hDn, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hκd)]
    have := mul_le_mul_of_nonneg_left hκd (by positivity : 0 ≤ 7352 / 10000 * R + 1363 / 10000 * R₀)
    linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact mul_nonneg hu (by linarith)
  have hεwR0 : 0 ≤ ε * w * R₀ := by positivity
  have hεwR : 0 ≤ ε * w * R := by positivity
  have hτR₀ : τ ≤ R₀ / 32 := by linarith [mul_le_mul_of_nonneg_right hε₁ hR₀]
  have hθ' : θ * 1000000 ≤ ε * w * (124 / 100 * R + 17 / 100 * R₀) := by
    rw [hθ]
    have h1 : Dn + s + τ ≤ 124 / 100 * R + 17 / 100 * R₀ := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hu
    have h3 := mul_le_mul_of_nonneg_right hu'
      (by positivity : (0 : ℝ) ≤ 124 / 100 * R + 17 / 100 * R₀)
    linarith
  have hθ1 : θ ≤ R / 10000 + R₀ / 10000 := by
    linarith [mul_le_mul_of_nonneg_right hεw1 hR, mul_le_mul_of_nonneg_right hεw1 hR₀]
  have hκ3 : (1 + κ) ^ 2 ≤ 625 / 576 := by
    have := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + κ) (by linarith : 1 + κ ≤ 25 / 24) 2
    norm_num at this ⊢; linarith
  have hT2 : ξ * (2 * (1 + κ) + ξ) ≤ 4345 / 10000 * (ε * w) := by
    have := mul_le_mul hξ' (by linarith : 2 * (1 + κ) + ξ ≤ 2.0848) (by linarith) (by positivity)
    linarith
  refine ⟨hη0, hγ', hξ0, hξ', hDn0, hDn', hθ0, by linarith [mul_le_mul_of_nonneg_right hκ3 hθ0],
    mul_le_mul hT2 (by linarith) (by linarith) (by positivity)⟩

/-- The residual and singular-value budget of a node (pure real arithmetic). -/
private theorem node_budget {ε x R R₀ u v τ e' r' η κ s ρ γ ξ Dn θ ε₀ : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8) (hx : 20 ≤ x) (hR : 0 ≤ R) (hR₀ : 0 ≤ R₀)
    (hu : 0 ≤ u) (hux : x * u * 1000000 ≤ ε) (hv : 0 ≤ v) (hvx : x * v * 100000 ≤ ε)
    (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1 / 4) (hτR : τ * 4 ≤ ε * R₀)
    (he'₁ : (1 - 1 / x) * (1 - 9 * u) * ε - u * τ ≤ e')
    (he'₂ : e' ≤ (1 - 1 / x) * ε + 7 * u * ε + u * τ)
    (hr'₀ : 0 ≤ r') (hr' : r' ≤ (1 / 2 + 2 / x) * (1 + 22 * u) * R + u * τ)
    (hη : η = (1 - 1 / x) * ε / (5 * x)) (hκ : κ = e' / 3) (hs : s = R / 2 + 2 * u * R + u * τ)
    (hρ : ρ = e' * (r' + R₀)) (hγ : γ = (2 + 2 * η) * R * η)
    (hξ : ξ = η * (1 + κ) + v * ((1 + η) * (1 + κ) + τ)) (hDn : Dn = (r' + ρ) / (1 - κ) ^ 2)
    (hθ : θ = u * (Dn + s + τ)) (hε₀ : ε₀ = u * (R + s + τ)) :
    0 ≤ κ ∧ κ < 1 ∧ 0 ≤ ξ ∧ 0 ≤ θ ∧ 0 ≤ ρ ∧ 0 ≤ Dn ∧ 0 ≤ s ∧ Dn + s ≤ 2 * R + R₀ ∧
    κ + √2 * ξ ≤ ε / 3 ∧
    γ + ρ + s * (2 * κ + κ ^ 2) +
        2 * ((1 + κ) ^ 2 * θ + ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ)) ≤ ε * (R + R₀) ∧
    ε₀ + ρ + s * (2 * κ + κ ^ 2) + (1 + κ) ^ 2 * θ ≤ ε * (R + R₀) := by
  -- the depth parameter $w = 1/x$
  obtain ⟨w, hw_def⟩ : ∃ w, w = 1 / x := ⟨_, rfl⟩
  have hx0 : 0 < x := by linarith
  have hwx : w * x = 1 := by rw [hw_def]; field_simp
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw20 : w ≤ 1 / 20 := by rw [hw_def, div_le_div_iff₀ hx0 (by norm_num)]; linarith
  rw [← hw_def] at he'₁ he'₂
  rw [show 2 / x = 2 * w by rw [hw_def]; ring] at hr'
  have hu' : u * 1000000 ≤ ε * w := by
    have := mul_le_mul_of_nonneg_left hux hw0.le
    rw [show w * (x * u * 1000000) = (w * x) * u * 1000000 by ring, hwx] at this; linarith
  have hv' : v * 100000 ≤ ε * w := by
    have := mul_le_mul_of_nonneg_left hvx hw0.le
    rw [show w * (x * v * 100000) = (w * x) * v * 100000 by ring, hwx] at this; linarith
  obtain ⟨he'0, hE', hκ0, hκ1, hρ0, hs0, hρE, hsκ, hrρ, hsb, huR⟩ := node_budget_params hε hε₁
    hw0 hw20 hR hR₀ hu hu' hτ₀ hτ hτR he'₁ he'₂ hr'₀ hr' hκ hs hρ
  obtain ⟨hη0, hγ', hξ0, hξ', hDn0, hDn', hθ0, hT1, hT3⟩ := node_budget_errors hε hε₁ hw0 hw20
    hR hR₀ hu hu' hv hv' hτ₀ hτ hτR hκ0 hκ1 hs0 hsb (by linarith) hrρ
    (by rw [hη, hw_def]; field_simp) hγ hξ hDn hθ
  have hsq2 : √2 ≤ 1.4143 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hεR : 0 ≤ ε * R := by positivity
  have hεR₀ : 0 ≤ ε * R₀ := by positivity
  have hεw : 0 ≤ ε * w := by positivity
  have hww : 0 ≤ w * w := by positivity
  have hεww : 0 ≤ ε * w * w := by positivity
  have hεw8 : ε * w ≤ w / 8 := by linarith [mul_le_mul_of_nonneg_right hε₁ hw0.le]
  have hεwR0 : 0 ≤ ε * w * R₀ := by positivity
  have hεwR : 0 ≤ ε * w * R := by positivity
  have hτR₀ : τ ≤ R₀ / 32 := by linarith [mul_le_mul_of_nonneg_right hε₁ hR₀]
  refine ⟨hκ0, by linarith, hξ0, hθ0, hρ0, hDn0, hs0, by linarith, ?_, ?_, ?_⟩
  · linarith [mul_le_mul hsq2 hξ' hξ0 (by norm_num)]
  · -- the residual of a split
    have h1 := mul_le_mul_of_nonneg_left (show (1 - w + 2 * w / 1000000) *
        (1 / 2 + 2 * w + 2 * w / 1000000) + 49 / 72 * (1 - w + 2 * w / 1000000) *
        (1 / 2 + w / 1000000) + (4005 / 10000 + 2 / 100000 + 2 * (4345 / 10000) *
        (12355 / 10000)) * w ≤ 1 by linarith) hεR
    have h2 := mul_le_mul_of_nonneg_left (show (1 - w + 2 * w / 1000000) *
        (ε * w / 10000000 + 1) + 49 / 72 * (1 - w + 2 * w / 1000000) *
        (ε * w / 10000000) + (2 / 100000 + 2 * (4345 / 10000) * (1366 / 10000)) * w ≤ 1 by
        linarith) hεR₀
    linarith
  · -- the residual of a shift
    have hε₀' : ε₀ ≤ ε * w * (R + R₀) / 100000 := by
      rw [hε₀]
      have h2 := mul_le_mul_of_nonneg_left (by linarith : R + s + τ ≤ 2 * R + R₀) hu
      have h3 := mul_le_mul_of_nonneg_right hu' (by positivity : (0 : ℝ) ≤ 2 * R + R₀)
      linarith
    have h1 := mul_le_mul_of_nonneg_left (show (1 - w + 2 * w / 1000000) *
        (1 / 2 + 2 * w + 2 * w / 1000000) + 49 / 72 * (1 - w + 2 * w / 1000000) *
        (1 / 2 + w / 1000000) + (2 / 100000) * w ≤ 1 by linarith) hεR
    have h2 := mul_le_mul_of_nonneg_left (show (1 - w + 2 * w / 1000000) *
        (ε * w / 10000000 + 1) + 49 / 72 * (1 - w + 2 * w / 1000000) *
        (ε * w / 10000000) + (2 / 100000) * w ≤ 1 by linarith) hεR₀
    linarith

/-- A leaf of `NLAlib.eighAux` is an approximate diagonalization: for a stored $\mathbf{A}$
with Hermitian decoding, $0 \le \kappa \le 1$ and a recursion budget $f + 1$, if the node has size
at most one (and $\eta \ge 0$) or the machine's leaf test $R \le \mathrm{fl}(\varepsilon R_0)$
holds (and $\|\mathbf{A}\|_2 \le \eta$), the output of `NLAlib.eighAux` is an approximate
diagonalization of $\mathbf{A}$ with residual $\eta$ and singular values within $\kappa$ of $1$. -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_leaf {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {N signFuel f k ℓ : ℕ} {R₀ β R ε : F}
    {A : Matrix (Fin k) (Fin k) (F × F)} {s : List Bool → EighSample ℝ ℂ N} {η κ : ℝ}
    (hA : (decodeMatrix dec A).IsHermitian) (hκ : 0 ≤ κ) (hκ₁ : κ ≤ 1)
    (hleaf : (k ≤ 1 ∧ 0 ≤ η) ∨
      (M.le R (M.mul ε R₀) = true ∧ specNorm (decodeMatrix dec A) ≤ η)) :
    IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec (eighAux M N signFuel R₀ β (f + 1) A R ε ℓ s).1)
      (fun i => dec ((eighAux M N signFuel R₀ β (f + 1) A R ε ℓ s).2 i)) η κ := by
  have h1 : (1 - κ) ^ 2 • (1 : Matrix (Fin k) (Fin k) ℂ) ≤ 1ᴴ * 1 := by
    rw [Matrix.conjTranspose_one, Matrix.one_mul]
    simpa using smul_one_le_smul_one (n := Fin k) (𝕜 := ℂ) (show (1 - κ) ^ 2 ≤ 1 by nlinarith)
  have h2 : (1 : Matrix (Fin k) (Fin k) ℂ)ᴴ * 1 ≤ (1 + κ) ^ 2 • 1 := by
    rw [Matrix.conjTranspose_one, Matrix.one_mul]
    simpa using smul_one_le_smul_one (n := Fin k) (𝕜 := ℂ) (show 1 ≤ (1 + κ) ^ 2 by nlinarith)
  by_cases hk : k ≤ 1
  · have hη : 0 ≤ η := by
      rcases hleaf with h | h
      · exact h.2
      · exact (specNorm_nonneg _).trans h.2
    simp only [eighAux, eighStep, if_pos hk, hM.decodeMatrix_identityMat]
    refine ⟨?_, h1, h2⟩
    have : Subsingleton (Fin k) := Fin.subsingleton_iff_le_one.mpr hk
    have hd : decodeMatrix dec A = Matrix.diagonal fun i => (dec (A i i).1 : ℂ) := by
      ext i j
      obtain rfl := Subsingleton.elim i j
      have h := congrArg Complex.im (hA.apply i i)
      simp only [decodeMatrix, decodeComplex, Matrix.map_apply, Complex.star_def,
        Complex.conj_im] at h
      apply Complex.ext <;> simp [decodeMatrix, decodeComplex]
      linarith
    simpa [hd] using hη
  · have ht := hleaf.resolve_left fun h => hk h.1
    simp only [eighAux, eighStep, if_neg hk, ht.1, if_true, hM.decodeMatrix_identityMat,
      hM.dec_zero]
    refine ⟨?_, h1, h2⟩
    simpa using ht.2

/-- The one-child outcomes of `NLAlib.eighStep`. -/
private theorem eq_hermShift_and_of_eighStep_eq_shift {F Su Sg : Type*} [Inhabited Sg]
    {M : FloatMachine F Su Sg}
    {N signFuel : ℕ} {R₀ β : F} {k : ℕ} {A : Matrix (Fin k) (Fin k) (F × F)} {R ε : F} {ℓ : ℕ}
    {smp : EighSample Su Sg N} {b : Bool} {A' : Matrix (Fin k) (Fin k) (F × F)} {σ : F}
    (h : eighStep M N signFuel R₀ β A R ε ℓ smp = .shift b A' σ) :
    A' = M.hermShift A σ ∧
      (σ = M.div R (M.ofNat 2) ∨ σ = M.neg (M.div R (M.ofNat 2))) := by
  unfold eighStep at h
  dsimp only at h
  split_ifs at h <;> simp only [EighStep.shift.injEq] at h
  · obtain ⟨-, rfl, rfl⟩ := h; exact ⟨rfl, Or.inl rfl⟩
  · obtain ⟨-, rfl, rfl⟩ := h; exact ⟨rfl, Or.inr rfl⟩

/-- `NLAlib.eighStep` is not a leaf at an internal node. -/
private theorem eighStep_ne_leaf {F Su Sg : Type*} [Inhabited Sg] {M : FloatMachine F Su Sg}
    {N signFuel : ℕ} {R₀ β : F} {k : ℕ} {A : Matrix (Fin k) (Fin k) (F × F)} {R ε : F} {ℓ : ℕ}
    {smp : EighSample Su Sg N} (hk : ¬ k ≤ 1) (hint : M.le R (M.mul ε R₀) = false)
    (U : Matrix (Fin k) (Fin k) (F × F)) (d : Fin k → F) :
    eighStep M N signFuel R₀ β A R ε ℓ smp ≠ .leaf U d := by
  unfold eighStep
  rw [if_neg hk, if_neg (by simp [hint])]
  dsimp only
  split_ifs <;> simp

/-- At a node whose leaf test $R \le \mathrm{fl}(e R_0)$ holds, $R \le e(R + R_0)$ (for
$1000u \le e \le 1/8$ and $4\tau \le eR_0$). -/
private theorem FloatMachine.IsAccurate.le_mul_add_of_le_eq_true {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R e R₀ : F} (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (he : 0 < dec e) (he₁ : dec e ≤ 1 / 8) (hR₀ : 0 < dec R₀) (hR : 0 ≤ dec R)
    (hue : u * 1000 ≤ dec e) (hτ : τ * 4 ≤ dec e * dec R₀) (hΩ : dec R₀ ≤ Ω)
    (ht : M.le R (M.mul e R₀) = true) : dec R ≤ dec e * (dec R + dec R₀) := by
  have hle := (hM.le_iff _ _).mp ht
  have hεR₀ : dec e * dec R₀ ≤ dec R₀ / 8 := by linarith [mul_le_mul_of_nonneg_right he₁ hR₀.le]
  obtain ⟨-, hm⟩ := le_and_le_of_isRoundingOf (hM.mul e R₀) (by positivity) (by linarith) hu hτ₀
  have h1 : u * (dec e * dec R₀ + τ) ≤ dec e * dec e * dec R₀ := by
    have h4 := mul_le_mul_of_nonneg_right (by linarith : u ≤ dec e / 1000)
      (by positivity : 0 ≤ dec e * dec R₀ + τ)
    have h5 := mul_le_mul_of_nonneg_left (by linarith : dec e * dec R₀ + τ ≤
      5 / 4 * (dec e * dec R₀)) (by positivity : 0 ≤ dec e / 1000)
    have h6 : 0 ≤ dec e * dec e * dec R₀ := by positivity
    linarith
  have heR0 := mul_nonneg he.le hR
  rcases le_or_gt (dec R) (dec e * dec R₀) with h | h
  · linarith
  · linarith [mul_le_mul_of_nonneg_left h.le he.le]

/-! ### Generic node lemmas for a precision budget -/

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
  {N signFuel : ℕ} {R₀ β : F} {w x t : ℝ} {y : EighNode F}

/-- The smallness facts of a node budget at a node of size at least $2$: $10^6\ell u$,
$10^5\ell\mu_{\mathrm{MM}}(k)u$ and $2 \cdot 10^7u$ are at most $\varepsilon$, $\tau \le 1/4$,
$4\tau \le \varepsilon R_0$ and $16(R_0 + R + k + \ell) \le \Omega$. -/
private theorem FloatMachine.IsEighNodeBudget.mul_le_dec_ε
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk : 2 ≤ y.k) :
    (y.ℓ : ℝ) * u * 1000000 ≤ dec y.ε ∧ (y.ℓ : ℝ) * (μM y.k * u) * 100000 ≤ dec y.ε ∧
      u * 20000000 ≤ dec y.ε ∧ τ ≤ 1 / 4 ∧ τ * 4 ≤ dec y.ε * dec R₀ ∧
      16 * (dec R₀ + dec y.R + y.k + y.ℓ) ≤ Ω := by
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hε := hB.pos_ε
  have hμM := hB.nonneg_μM
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
  have hk2 : (2 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hsk : √2 ≤ √(y.k : ℝ) := Real.sqrt_le_sqrt hk2
  have hsk1 : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hs22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have ht4 : 4 ≤ t := by nlinarith [hB.le_t, Real.sqrt_nonneg 2]
  -- the stopping condition bounds $u$ and $\mu_{\mathrm{MM}}(k)u$ by multiples of $\beta$
  have hβu : 2048 * 3 * (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u ≤ dec β :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith)
      (by positivity)) hu) (hB.mul_le_dec_β (by omega))
  have hu1 : u * 122880 ≤ dec β := by
    nlinarith [mul_nonneg hμM hu, mul_le_mul_of_nonneg_right hsk1 hu]
  have hμu : μM y.k * u * 24576 ≤ dec β := by
    nlinarith [mul_nonneg hμM hu, mul_nonneg (Real.sqrt_nonneg (y.k : ℝ)) hu]
  -- the deflation tolerance bounds $40\ell\beta$ by $\varepsilon$ (as $t \ge 4$, $x \le 1$)
  have hℓβ : (y.ℓ : ℝ) * dec β * 40 ≤ dec y.ε := by
    have hx := hB.pos_x
    have h1 : 8 * dec β ≤ 2 * t / x * dec β := by
      refine mul_le_mul_of_nonneg_right ?_ hB.pos_β.le
      rw [le_div_iff₀ hx]; nlinarith [hB.x_le]
    have h2 : (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ≤ dec y.ε / (5 * y.ℓ) :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_left hε.le (sub_le_self _ (by positivity)))
        (by positivity)
    have h3 := (h1.trans hB.defl_tol).trans h2
    rw [le_div_iff₀ (by positivity)] at h3
    linarith
  have hux : (y.ℓ : ℝ) * u * 1000000 ≤ dec y.ε := by
    nlinarith [mul_le_mul_of_nonneg_left hu1 (by linarith : (0 : ℝ) ≤ y.ℓ)]
  have hkk : (1 : ℝ) ≤ y.k * √(y.k : ℝ) := by nlinarith
  have hτk : τ * 4 ≤ τ * (4 * y.k * √(y.k : ℝ)) := by nlinarith
  refine ⟨hux, ?_, by nlinarith, ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hμu (by linarith : (0 : ℝ) ≤ y.ℓ)]
  · linarith [hB.τ_le.trans (min_le_left _ _), hB.x_le]
  · linarith [hB.τ_le.trans (min_le_right _ _)]
  · linarith [hB.Ω_le]

/-- **A shift node under a node budget**: the output of a node whose step is a shift is an
approximate diagonalization with $(\varepsilon(R + R_0), \varepsilon/3)$, given the child's. -/
private theorem FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_eighStep_eq_shift
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    {f : ℕ} {s : List Bool → EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w x t y (s []))
    (hchild : ∀ (b : Bool) (y' : EighNode F), eighChild M N signFuel R₀ β y (s []) b = some y' →
      IsApproxDiagonalization (decodeMatrix dec y'.A)
        (decodeMatrix dec (eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).1)
        (fun i => dec ((eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).2 i))
        (dec y'.ε * (dec y'.R + dec R₀)) (dec y'.ε / 3))
    (hk : 2 ≤ y.k) {b : Bool} {A' : Matrix (Fin y.k) (Fin y.k) (F × F)} {σ : F}
    (hst : eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s []) = .shift b A' σ) :
    IsApproxDiagonalization (decodeMatrix dec y.A)
      (decodeMatrix dec (eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).1)
      (fun i => dec ((eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).2 i))
      (dec y.ε * (dec y.R + dec R₀)) (dec y.ε / 3) := by
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hε := hB.pos_ε
  have hε₁ := hB.ε_le
  have hR₀ := hB.pos_R₀
  have hR0 : 0 ≤ dec y.R := (specNorm_nonneg _).trans hB.specNorm_le
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
  have hk0 : (0 : ℝ) ≤ y.k := Nat.cast_nonneg _
  obtain ⟨hux, hvx, huε, hτ4, h4τ, hΩ'⟩ := hB.mul_le_dec_ε hk
  obtain ⟨hp1, hp2, hp3⟩ := hM.dec_eighNextParams_le (R := y.R) (ε := y.ε) (m := y.ℓ) hu
    (by linarith) hτ₀ (by linarith) hB.twenty_le (by linarith) hR0 (by linarith) hε.le
    (by linarith [hB.ε_le])
  have hhalf := hM.abs_dec_div_ofNat_two_le (R := y.R) hu (by linarith [hB.ε_le]) hτ₀ hτ4 hR0
    (by linarith [hB.pos_R₀]) (by linarith [hB.pos_R₀])
  obtain ⟨rfl, hσ⟩ := eq_hermShift_and_of_eighStep_eq_shift hst
  have hy' : eighChild M N signFuel R₀ β y (s []) b = some ⟨y.k, M.hermShift y.A σ,
      (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩ := by
    simp [eighChild, hst]
  have hc := hchild b _ hy'
  obtain ⟨-, hA'R⟩ := hM.isHermitian_and_specNorm_le_of_isEighNodeBudget hB hgood hy'
  dsimp only at hc hA'R
  simp only [eighAux, hst]
  obtain ⟨hκ0, hκ1, hξ0, -, -, -, -, hDs, hsing, -, hshift⟩ := node_budget (x := (y.ℓ : ℝ))
    (R := dec y.R) (R₀ := dec R₀) (v := μM y.k * u) hε hB.ε_le hℓ' hR0 hB.pos_R₀.le hu hux
    (mul_nonneg hB.nonneg_μM hu) hvx hτ₀ hτ4 (by linarith) hp2 hp3
    ((specNorm_nonneg _).trans hA'R) hp1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hσabs : |dec σ| ≤ dec y.R / 2 + 2 * u * dec y.R + u * τ := by
    rcases hσ with rfl | rfl
    · exact hhalf
    · rw [hM.dec_neg, abs_neg]; exact hhalf
  have huR := mul_le_mul_of_nonneg_right (by linarith : u ≤ 1) hR0
  have huτ := mul_le_mul_of_nonneg_right (by linarith : u ≤ 1) hτ₀
  exact IsApproxDiagonalization.mono (hM.isApproxDiagonalization_add_of_hermShift hu hτ₀
    hB.isHermitian hB.specNorm_le hσabs hκ0 hκ1 hc hA'R (by linarith) (by linarith)) hshift hκ0
    (by linarith [mul_nonneg (Real.sqrt_nonneg 2) hξ0]) (by linarith)

/-- **A split node under a node budget**: the output of a node whose step is a split is an
approximate diagonalization with $(\varepsilon(R + R_0), \varepsilon/3)$, given the
children's. -/
private theorem FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_eighStep_eq_split
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    {f : ℕ} {s : List Bool → EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w x t y (s []))
    (hchild : ∀ (b : Bool) (y' : EighNode F), eighChild M N signFuel R₀ β y (s []) b = some y' →
      IsApproxDiagonalization (decodeMatrix dec y'.A)
        (decodeMatrix dec (eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).1)
        (fun i => dec ((eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).2 i))
        (dec y'.ε * (dec y'.R + dec R₀)) (dec y'.ε / 3))
    (hk : 2 ≤ y.k) {kp : ℕ} {hkp : kp ≤ y.k} {Qp : Matrix (Fin y.k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin y.k) (Fin (y.k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) (F × F)} {σ : F}
    (hst : eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s []) = .split kp hkp Qp Qm Ap Am σ) :
    IsApproxDiagonalization (decodeMatrix dec y.A)
      (decodeMatrix dec (eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).1)
      (fun i => dec ((eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).2 i))
      (dec y.ε * (dec y.R + dec R₀)) (dec y.ε / 3) := by
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hε := hB.pos_ε
  have hε₁ := hB.ε_le
  have hR₀ := hB.pos_R₀
  have hR0 : 0 ≤ dec y.R := (specNorm_nonneg _).trans hB.specNorm_le
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
  have hk0 : (0 : ℝ) ≤ y.k := Nat.cast_nonneg _
  obtain ⟨hux, hvx, huε, hτ4, h4τ, hΩ'⟩ := hB.mul_le_dec_ε hk
  obtain ⟨hp1, hp2, hp3⟩ := hM.dec_eighNextParams_le (R := y.R) (ε := y.ε) (m := y.ℓ) hu
    (by linarith) hτ₀ (by linarith) hB.twenty_le (by linarith) hR0 (by linarith) hε.le
    (by linarith [hB.ε_le])
  obtain ⟨hσR, ⟨Vp, hVp, hVpP, -, Wp, hWp, hQp, hAp⟩, ⟨Vm, hVm, hVmP, -, Wm, hWm, hQm, hAm⟩⟩ :=
    hM.exists_hasOrthonormalCols_specNorm_sub_le_of_isEighNodeBudget hB hgood hst
  have hyp : eighChild M N signFuel R₀ β y (s []) true = some ⟨kp, Ap,
      (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩ := by
    simp [eighChild, hst]
  have hym : eighChild M N signFuel R₀ β y (s []) false = some ⟨y.k - kp, Am,
      (eighNextParams M y.R y.ε y.ℓ).1, (eighNextParams M y.R y.ε y.ℓ).2, y.ℓ + 1⟩ := by
    simp [eighChild, hst]
  obtain ⟨-, hApR⟩ := hM.isHermitian_and_specNorm_le_of_isEighNodeBudget hB hgood hyp
  obtain ⟨-, hAmR⟩ := hM.isHermitian_and_specNorm_le_of_isEighNodeBudget hB hgood hym
  have hcp := hchild true _ hyp
  have hcm := hchild false _ hym
  dsimp only at hcp hcm hApR hAmR
  simp only [eighAux, hst]
  obtain ⟨hκ0, hκ1, hξ0, -, -, -, -, hDs, hsing, hsplit, -⟩ := node_budget (x := (y.ℓ : ℝ))
    (R := dec y.R) (R₀ := dec R₀) (v := μM y.k * u) hε hB.ε_le hℓ' hR0 hB.pos_R₀.le hu hux
    (mul_nonneg hB.nonneg_μM hu) hvx hτ₀ hτ4 (by linarith) hp2 hp3
    ((specNorm_nonneg _).trans hApR) hp1 rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hsξ := mul_nonneg (Real.sqrt_nonneg 2) hξ0
  have hσabs : |dec σ| ≤ dec y.R / 2 + 2 * u * dec y.R + u * τ := by
    rw [abs_le] at hσR ⊢
    constructor <;> linarith [mul_nonneg hu hR0, mul_nonneg hu hτ₀]
  have hη1 : (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ≤ 1 := div_le_one_of_le₀
    ((mul_le_of_le_one_left hε.le (sub_le_self _ (by positivity))).trans
      (by linarith [hB.ε_le])) (by positivity)
  have key := hM.isApproxDiagonalization_submatrix_fromCols_mm hkp
    (Nat.add_sub_of_le hkp).symm hB.nonneg_μM hu hτ₀ hVp hVm
    hWp hWm hVpP hVmP hQp hQm hAp hAm hcp hcm hApR hAmR hσabs hκ0 hκ1 (by linarith) hη1
    (by linarith) (by linarith) rfl rfl rfl
  exact IsApproxDiagonalization.mono key hsplit (by linarith) (by linarith) (by linarith)

/-- **Local guarantee under a node budget**: with budget `NLAlib.FloatMachine.IsEighNodeBudget`, a
good sample (`NLAlib.IsEighGoodSample` with parameters $(w, x, t)$) when internal and
children that are approximate diagonalizations with $(\varepsilon'(R' + R_0), \varepsilon'/3)$,
the node's output is one with $(\varepsilon(R + R_0), \varepsilon/3)$. [Shah2024, Lemma 4.1]. -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eighAux_succ_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    {f : ℕ} {s : List Bool → EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w x t y (s []))
    (hchild : ∀ (b : Bool) (y' : EighNode F), eighChild M N signFuel R₀ β y (s []) b = some y' →
      IsApproxDiagonalization (decodeMatrix dec y'.A)
        (decodeMatrix dec (eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).1)
        (fun i => dec ((eighAux M N signFuel R₀ β f y'.A y'.R y'.ε y'.ℓ fun a => s (b :: a)).2 i))
        (dec y'.ε * (dec y'.R + dec R₀)) (dec y'.ε / 3)) :
    IsApproxDiagonalization (decodeMatrix dec y.A)
      (decodeMatrix dec (eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).1)
      (fun i => dec ((eighAux M N signFuel R₀ β (f + 1) y.A y.R y.ε y.ℓ s).2 i))
      (dec y.ε * (dec y.R + dec R₀)) (dec y.ε / 3) := by
  have hA := hB.isHermitian
  have hε := hB.pos_ε
  have hR₀ := hB.pos_R₀
  have hR0 : 0 ≤ dec y.R := (specNorm_nonneg _).trans hB.specNorm_le
  by_cases hk : y.k ≤ 1
  · exact hM.isApproxDiagonalization_eighAux_succ_of_leaf hA (by positivity)
      (by linarith [hB.ε_le]) (Or.inl ⟨hk, mul_nonneg hε.le (by linarith)⟩)
  have hk2 : 2 ≤ y.k := by omega
  obtain ⟨-, -, huε, -, h4τ, hΩ'⟩ := hB.mul_le_dec_ε hk2
  have hk0 : (0 : ℝ) ≤ y.k := Nat.cast_nonneg _
  have hℓ0 : (0 : ℝ) ≤ y.ℓ := Nat.cast_nonneg _
  by_cases ht : M.le y.R (M.mul y.ε R₀) = true
  · exact hM.isApproxDiagonalization_eighAux_succ_of_leaf hA (by positivity)
      (by linarith [hB.ε_le]) (Or.inr ⟨ht, hB.specNorm_le.trans
        (hM.le_mul_add_of_le_eq_true hB.nonneg_u hB.nonneg_τ hε hB.ε_le hR₀ hR0
          (by linarith) h4τ (by linarith) ht)⟩)
  have hint : M.le y.R (M.mul y.ε R₀) = false := by simpa using ht
  rcases hst : eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ (s []) with
    ⟨U, d⟩ | ⟨b, A', σ⟩ | ⟨kp, hkp, Qp, Qm, Ap, Am, σ⟩
  · exact absurd hst (eighStep_ne_leaf hk hint U d)
  · exact hM.isApproxDiagonalization_eighAux_succ_of_eighStep_eq_shift hB hgood hchild hk2 hst
  · exact hM.isApproxDiagonalization_eighAux_succ_of_eighStep_eq_split hB hgood hchild hk2 hst

end NLAlib

