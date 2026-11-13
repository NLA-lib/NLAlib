/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.SpectralBisection.Node
public import NLAlib.Matrix.FinitePrecision.SpectralBisection.Tree

/-!
# Global deterministic guarantee of spectral bisection

If every internal node
of the recursion tree of `NLAlib.eigh` has a good sample, the output is an approximate
diagonalization with residual $2\varepsilon R_0$ and singular values of $\mathbf{U}$ in
$[1 - \varepsilon/3, 1 + \varepsilon/3]$ ([Shah2024, Theorem 4.2], deterministic part). The good
event of a node $y$ is charged in proportion to its size $k_y$ (shift distance
$w_y = 4\theta R_y/(9n\ell(\ell + 1))$, Gaussian failure
$\rho_y = \theta k_y/(6n\min(n, \ell + 1))$), and the accuracy uses the tolerance at the
deepest node. The probability is in `NLAlib/Eigensolvers/SpectralBisection/Global.lean`.

## Main results

* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample`: the
  global deterministic guarantee.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
  {N signFuel : ℕ} {R₀ β : F} {w x t : ℝ} {y : EighNode F}

/-- The global numeric consequences of the hypotheses of the global guarantee: the depth counter is
at least
$20$, the conditions of `NLAlib.FloatMachine.IsAccurate.eighNodeAt_eq_some_params` hold, and
$n\beta \le \varepsilon/4000$. -/
private lemma eigh_global_bounds {u τ Ω : ℝ} {μM : ℕ → ℝ} (hu : 0 ≤ u) (hμM : Monotone μM)
    (hμM₀ : 0 ≤ μM 0) {n : ℕ} (hn : 0 < n) {R₀ ε β θ : ℝ} (hR₀pos : 0 < R₀) (hε : 0 < ε)
    (hε₁ : ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ} (hℓ : bisectionDepth ε ≤ ℓ)
    (hβ : 0 < β)
    (hβle : β ≤ ((ℓ : ℝ) - 1) ^ 2 * ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)))))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * β)
    (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (ε * min R₀ 1))
    (hΩ : 16 * (2 * R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω) :
    20 ≤ ℓ ∧ 100 * ℓ ^ 2 * u ≤ 1 ∧ 100 * τ ≤ ε * min R₀ 1 ∧ 16 * (R₀ + ℓ) ≤ Ω ∧
      n * β ≤ ε / 4000 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.mpr hn'
  have hℓ20 : 20 ≤ ℓ := by
    refine le_trans ?_ hℓ
    have h15 : (2 : ℝ) ^ 15 ≤ ε⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hε, ← inv_pow]
      exact hε₁
    have h14 : ((14 : ℕ) : ℝ) < Real.logb 2 ε⁻¹ := by
      rw [Real.lt_logb_iff_rpow_lt one_lt_two (by positivity)]
      norm_num
      linarith
    have := Nat.lt_ceil.mpr h14
    unfold bisectionDepth
    omega
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ20
  -- $n\beta \le \varepsilon / 4000$
  have hnβ : n * β ≤ ε / 4000 := by
    have hm1 : (1 : ℝ) ≤ min (n : ℝ) (ℓ + 1) := le_min hn' (by linarith)
    have he1 : (1 : ℝ) ≤ min (n : ℝ) (Real.exp 1) :=
      le_min hn' (by linarith [Real.add_one_le_exp (1 : ℝ)])
    have hP : √(n : ℝ) ≤ √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) := by
      refine Real.sqrt_le_sqrt ?_
      calc (n : ℝ) = n * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    have hT : 2 * √(n : ℝ) ≤ 2 * √2 * √(n : ℝ) +
        √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)) := by
      have : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
      nlinarith [Real.sqrt_nonneg (Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))]
    have hnn : (n : ℝ) = √(n : ℝ) * √(n : ℝ) := (Real.mul_self_sqrt (by positivity)).symm
    have hD : 52 * 39 * 2 * (n : ℝ) * ℓ ^ 2 ≤ 52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
        √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
        (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) := by
      have h39 : (39 : ℝ) ≤ 2 * ℓ - 1 := by linarith
      calc 52 * 39 * 2 * (n : ℝ) * ℓ ^ 2 =
          52 * (ℓ : ℝ) ^ 2 * 39 * √(n : ℝ) * (2 * √(n : ℝ)) := by
            linear_combination (52 * 39 * 2 * (ℓ : ℝ) ^ 2) * hnn
        _ ≤ _ := by gcongr
    have hnum : ((ℓ : ℝ) - 1) ^ 2 * ε * √θ ≤ ℓ ^ 2 * ε := by
      have h1 : ((ℓ : ℝ) - 1) ^ 2 ≤ ℓ ^ 2 := by nlinarith
      have h2 : √θ ≤ 1 := Real.sqrt_le_one.mpr hθ₁
      calc ((ℓ : ℝ) - 1) ^ 2 * ε * √θ ≤ ℓ ^ 2 * ε * 1 := by gcongr
        _ = _ := by ring
    rw [le_div_iff₀ (lt_of_lt_of_le (by positivity) hD)] at hβle
    have := mul_le_mul_of_nonneg_left hD hβ.le
    nlinarith
  have hβ₁ : β ≤ 1 := by
    have : β ≤ n * β := le_mul_of_one_le_left hβ.le hn'
    linarith [hε₁.trans (show (2⁻¹ : ℝ) ^ 15 ≤ 1 by norm_num)]
  have hu₁ : 100 * ℓ ^ 2 * u ≤ 1 := by
    have hμn : 0 ≤ μM n := hμM₀.trans (hμM (Nat.zero_le n))
    have hQ : 1460 * (ℓ : ℝ) ^ 2 ≤ 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) := by
      calc 1460 * (ℓ : ℝ) ^ 2 = 146 * 1 * ℓ * ℓ * 10 := by ring
        _ ≤ _ := by gcongr <;> linarith [Real.sqrt_nonneg (n : ℝ)]
    have hθβ : θ * β ≤ 1 := mul_le_one₀ hθ₁ hβ.le hβ₁
    have h0 : 0 ≤ (ℓ : ℝ) ^ 2 * u := by positivity
    linarith [mul_le_mul_of_nonneg_right hQ hu]
  have hτ' : 100 * τ ≤ ε * min R₀ 1 := by
    have : 100 * τ ≤ τ * (100 * n * √(n : ℝ)) := by
      have h1 : (1 : ℝ) ≤ n * √(n : ℝ) := one_le_mul_of_one_le_of_one_le hn' hs1
      linarith [mul_le_mul_of_nonneg_left h1 hτ₀]
    exact this.trans (hτ.trans (min_le_right _ _))
  have hΩ' : 16 * (R₀ + ℓ) ≤ Ω := by
    linarith [Real.sqrt_nonneg (Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)),
      Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg 2,
      mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (n : ℝ))]
  exact ⟨hℓ20, hu₁, hτ', hΩ', hnβ⟩

/-- The arithmetic core of the deflation tolerance of the global guarantee: if
$52Q\ell^2(2\ell - 1) \le
(\ell - 1)^2\varepsilon r$ then $2Q \le (1 - 2^{-8})(\ell - 1)\varepsilon s r/(20\ell^2)$ for
$s \ge 0.39$. -/
private lemma two_mul_le_of_mul_le {Q s r ℓ ε : ℝ} (hℓ : 20 ≤ ℓ) (hs : 39 / 100 ≤ s)
    (hr : 0 ≤ r) (hε : 0 < ε) (hQ : Q * (52 * ℓ ^ 2 * (2 * ℓ - 1)) ≤ (ℓ - 1) ^ 2 * ε * r) :
    2 * Q ≤ (1 - 2⁻¹ ^ 8) * (ℓ - 1) * ε / (20 * ℓ ^ 2) * (s * r) := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h3 : 40 * (ℓ - 1) ≤ (1 - 2⁻¹ ^ 8) * s * (52 * (2 * ℓ - 1)) := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3
    (by have : 0 ≤ ℓ - 1 := by linarith
        positivity : (0 : ℝ) ≤ (ℓ - 1) * ε * r)
  have h5 : 0 < 52 * (2 * ℓ - 1) := by linarith
  refine le_of_mul_le_mul_right ?_ h5
  nlinarith [h4, hQ]

/-- The singular value threshold of the global guarantee at a node of size $K$: with
$\rho = \theta K/(6nm)$,
$5\theta/(32nm\min(n, e)) \le 15\rho/(16\min(K^2, eK)) \le 1$. -/
private lemma node_threshold_bounds {K n m e θ : ℝ} (hK2 : 2 ≤ K) (hKn : K ≤ n) (hm1 : 1 ≤ m)
    (he2 : 2 ≤ e) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) :
    5 * θ / (32 * (n * m * min n e)) ≤ 15 * (θ * K / (6 * n * m)) / (16 * min (K ^ 2) (e * K)) ∧
      15 * (θ * K / (6 * n * m)) / (16 * min (K ^ 2) (e * K)) ≤ 1 := by
  have hK0 : 0 < K := by linarith
  have hn0 : 0 < n := by linarith
  have hmin0 : 0 < min (K ^ 2) (e * K) := lt_min (by positivity) (by positivity)
  constructor
  · have h1 : min (K ^ 2) (e * K) ≤ K * min n e := by
      rw [mul_min_of_nonneg _ _ hK0.le]
      exact min_le_min (by rw [sq]; exact mul_le_mul_of_nonneg_left hKn hK0.le)
        (by rw [mul_comm])
    calc 5 * θ / (32 * (n * m * min n e)) = 15 * (θ * K / (6 * n * m)) / (16 * (K * min n e)) := by
          have : 0 < min n e := lt_min hn0 (by linarith)
          field_simp; ring
      _ ≤ _ := by gcongr
  · have h1 : 2 * K ≤ min (K ^ 2) (e * K) :=
      le_min (by rw [sq]; exact mul_le_mul_of_nonneg_right hK2 hK0.le)
        (mul_le_mul_of_nonneg_right he2 hK0.le)
    calc 15 * (θ * K / (6 * n * m)) / (16 * min (K ^ 2) (e * K)) ≤
          15 * (θ * K / (6 * n * m)) / (16 * (2 * K)) := by gcongr
      _ = 15 * θ / (192 * n * m) := by field_simp; ring
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [mul_le_mul (show (1 : ℝ) ≤ n by linarith) hm1 zero_le_one (by positivity)]

/-- The shift distance of the global guarantee at a node of window $R$:
$w = 4\theta R/(9n\ell(\ell + 1)) \le R$,
and $w/(5R)$, $w/(2R)$ in closed form. -/
private lemma node_shift_bounds {θ R n ℓ : ℝ} (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hR : 0 < R)
    (hn : 1 ≤ n) (hℓ : 20 ≤ ℓ) :
    4 * θ * R / (9 * n * ℓ * (ℓ + 1)) ≤ R ∧
      4 * θ * R / (9 * n * ℓ * (ℓ + 1)) / (5 * R) = 4 * θ / (45 * n * ℓ * (ℓ + 1)) ∧
      4 * θ * R / (9 * n * ℓ * (ℓ + 1)) / (2 * R) = 2 * θ / (9 * n * ℓ * (ℓ + 1)) ∧
      θ / (12 * n * ℓ * (ℓ + 1)) ≤ |4 * θ * R / (9 * n * ℓ * (ℓ + 1)) / (5 * R)| := by
  have hD1 : (1 : ℝ) ≤ n * ℓ * (ℓ + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn (by linarith))
      (by linarith)
  have h5 : 4 * θ * R / (9 * n * ℓ * (ℓ + 1)) / (5 * R) = 4 * θ / (45 * n * ℓ * (ℓ + 1)) := by
    field_simp; ring
  refine ⟨?_, h5, by field_simp; ring, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hθ₁ hR.le, mul_le_mul_of_nonneg_left hD1 hR.le]
  · rw [h5, abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < θ * (n * ℓ * (ℓ + 1)) := by positivity
    linarith

/-- The deflation tolerance of the global guarantee at a node: with $t \le \hat T$,
$x \ge \sqrt{5\theta/(32P)}$
and the accuracy bound on $\beta$, $2t\beta/x \le (1 - 1/L)\varepsilon_y/(5L)$. -/
private lemma node_defl_tol {ℓ L ε εy θ P T t x β : ℝ} (hℓ : 20 ≤ ℓ) (hL : ℓ ≤ L)
    (hL₂ : L ≤ 2 * ℓ) (hε : 0 < ε) (hεy : (1 - 2⁻¹ ^ 8) * ((ℓ - 1) / (L - 1)) * ε ≤ εy)
    (hθ : 0 < θ) (hP : 0 < P) (ht0 : 0 < t) (ht : t ≤ T) (hx : √(5 * θ / (32 * P)) ≤ x)
    (hβ : 0 ≤ β) (hβle : β ≤ (ℓ - 1) ^ 2 * ε * √θ / (52 * ℓ ^ 2 * (2 * ℓ - 1) * √P * T)) :
    2 * t / x * β ≤ (1 - 1 / L) * εy / (5 * L) := by
  have hc0 : 0 < √(5 * θ / (32 * P)) := Real.sqrt_pos.mpr (by positivity)
  have hT0 : 0 < T := ht0.trans_le ht
  have hcs : √(5 * θ / (32 * P)) = √(5 / 32) * (√θ / √P) := by
    rw [show 5 * θ / (32 * P) = 5 / 32 * (θ / P) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_div hθ.le]
  have hs : 39 / 100 ≤ √(5 / 32 : ℝ) := Real.le_sqrt_of_sq_le (by norm_num)
  have hD : 0 < 52 * ℓ ^ 2 * (2 * ℓ - 1) * √P * T := by
    have : 0 < 2 * ℓ - 1 := by linarith
    positivity
  rw [le_div_iff₀ hD] at hβle
  have hL0 : 0 < L - 1 := by linarith
  have hLpos : 0 < L := by linarith
  calc 2 * t / x * β ≤ 2 * T / √(5 * θ / (32 * P)) * β := by gcongr
    _ ≤ (1 - 2⁻¹ ^ 8) * (ℓ - 1) * ε / (20 * ℓ ^ 2) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hc0, hcs]
      have hQ : T * β * (52 * ℓ ^ 2 * (2 * ℓ - 1)) ≤ (ℓ - 1) ^ 2 * ε * (√θ / √P) := by
        rw [mul_div_assoc', le_div_iff₀ (Real.sqrt_pos.mpr hP)]
        linarith
      linarith [two_mul_le_of_mul_le hℓ hs (by positivity) hε hQ]
    _ ≤ (1 - 2⁻¹ ^ 8) * (ℓ - 1) * ε / (5 * L ^ 2) :=
      div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hε.le)
        (by positivity) (by nlinarith)
    _ = (1 - 1 / L) / (5 * L) * ((1 - 2⁻¹ ^ 8) * ((ℓ - 1) / (L - 1)) * ε) := by
      field_simp
    _ ≤ (1 - 1 / L) / (5 * L) * εy := by
      refine mul_le_mul_of_nonneg_left hεy (div_nonneg ?_ (by positivity))
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    _ = (1 - 1 / L) * εy / (5 * L) := by ring

/-- The floor condition of the global guarantee at a node of size $K \le n$:
$4K^{3/2}\tau \le \min(x, \varepsilon_y R_0)$. -/
private lemma node_τ_le {τ K n m e θ x ε εy R₀ : ℝ} (hτ₀ : 0 ≤ τ) (hK : 1 ≤ K) (hKn : K ≤ n)
    (hm : 1 ≤ m) (he : 0 < e) (he4 : e ≤ 4) (hθ : 0 < θ)
    (hx : √(5 * θ / (32 * (n * m * min n e))) ≤ x)
    (hτ : τ * (100 * n * √n) ≤ min (√(θ / (8 * n * m))) (ε * min R₀ 1)) (hε : 0 < ε)
    (hεy : ε / 3 ≤ εy) (hR₀ : 0 < R₀) :
    τ * (4 * K * √K) ≤ min x (εy * R₀) := by
  have hn : 0 < n := by linarith
  have h0 : τ * (4 * K * √K) * 25 ≤ τ * (100 * n * √n) := by
    calc τ * (4 * K * √K) * 25 = τ * (100 * K * √K) := by ring
      _ ≤ _ := by gcongr
  have hsq : √(θ / (8 * n * m)) ≤ 25 * √(5 * θ / (32 * (n * m * min n e))) := by
    rw [show (25 : ℝ) = √(25 ^ 2) by rw [Real.sqrt_sq (by norm_num)],
      ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have h1 : 5 * θ / (128 * (n * m)) ≤ 5 * θ / (32 * (n * m * min n e)) := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      have := min_le_right n e
      nlinarith [mul_pos hn (by linarith : (0 : ℝ) < m)]
    have h2 : θ / (8 * n * m) ≤ 25 ^ 2 * (5 * θ / (128 * (n * m))) := by
      rw [show 25 ^ 2 * (5 * θ / (128 * (n * m))) = θ / (8 * n * m) * (3125 / 16) by
        field_simp; ring]
      exact le_mul_of_one_le_right (by positivity) (by norm_num)
    nlinarith
  have h3 : ε * min R₀ 1 ≤ ε * R₀ := by gcongr; exact min_le_left _ _
  have h4 := mul_le_mul_of_nonneg_right hεy hR₀.le
  have h5 := hτ.trans (min_le_left _ _)
  have h6 := hτ.trans (min_le_right _ _)
  exact le_min (by linarith) (by linarith [mul_pos hε hR₀])

/-- The Newton–Schulz step count of a node of the global guarantee is at most the global $N_*$,
which is
nonnegative. -/
private lemma node_newtonSchulzSteps_le {n K ℓ θ R β ε : ℝ} (hn : 1 ≤ n) (hK2 : 2 ≤ K)
    (hKn : K ≤ n) (hℓ : 20 ≤ ℓ) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hR : 0 < R) (hβ : 0 < β)
    (hnβ : n * β ≤ ε / 4000) (hε₁ : ε ≤ 2⁻¹ ^ 15) :
    newtonSchulzSteps (4 * θ * R / (9 * n * ℓ * (ℓ + 1)) / (5 * R)) (β / (16 * K)) ≤
        newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (β / (16 * n)) ∧
      0 ≤ newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (β / (16 * n)) := by
  have hβ1 : β ≤ 1 := by
    linarith [le_mul_of_one_le_left hβ.le hn, show (2⁻¹ : ℝ) ^ 15 ≤ 1 by norm_num]
  have hβn : β / (16 * K) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hD1 : (1 : ℝ) ≤ n * ℓ * (ℓ + 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn (by linarith))
      (by linarith)
  refine ⟨(newtonSchulzSteps_le_of_le_abs (by positivity)
    (node_shift_bounds hθ hθ₁ hR hn hℓ).2.2.2).trans
      (newtonSchulzSteps_le_of_le (by positivity) (by gcongr) hβn),
    newtonSchulzSteps_nonneg (by positivity) ?_ (by positivity) ?_⟩
  · rw [div_le_iff₀ (by positivity)]; linarith
  · exact (div_le_div_of_nonneg_left hβ.le (by positivity) (by linarith)).trans hβn

/-- A crude bound $e \le 4$, from $e^{-1/2} \ge 1/2$. -/
private lemma exp_one_le_four : Real.exp 1 ≤ 4 := by
  have h1 := Real.add_one_le_exp (-1 / 2 : ℝ)
  have h2 : Real.exp (-1) = Real.exp (-1 / 2) * Real.exp (-1 / 2) := by
    rw [← Real.exp_add]; norm_num
  have h3 : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have h4 : 1 / 4 ≤ Real.exp (-1) := by rw [h2]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h4 (Real.exp_pos 1).le]

/-- The precision budget `NLAlib.FloatMachine.IsEighNodeBudget` at an internal node of the tree
of `NLAlib.eigh`, with the parameters of the global guarantee. -/
private lemma isEighNodeBudget_of_node (hu : 0 ≤ u) (hμM : Monotone μM) (hμQ : Monotone μQ)
    (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN) {n : ℕ} {ε : F} {θ : ℝ}
    (hR₀pos : 0 < dec R₀) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1)
    {ℓ : ℕ} (hℓ : 20 ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * dec β)
    (hustop : 2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ dec β)
    (hudefl : 16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β)
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω)
    (hnβ : n * dec β ≤ dec ε / 4000)
    (hA : (decodeMatrix dec y.A).IsHermitian) (hR : specNorm (decodeMatrix dec y.A) ≤ dec y.R)
    (hkn : y.k ≤ n) (hℓy : ℓ ≤ y.ℓ) (hℓy₂ : y.ℓ ≤ 2 * ℓ)
    (hεy : (1 - 2⁻¹ ^ 8) * (((ℓ : ℝ) - 1) / ((y.ℓ : ℝ) - 1)) * dec ε ≤ dec y.ε)
    (hεy3 : dec ε / 3 ≤ dec y.ε) (hεy' : dec y.ε ≤ dec ε) (hRy : dec y.R ≤ dec R₀)
    (hk : 2 ≤ y.k) (hRpos : 0 < dec y.R) :
    M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)))
      (√(15 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) /
        (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
      (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))))))
      y := by
  have hn : 0 < n := by omega
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK2 : (2 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hKn : (y.k : ℝ) ≤ n := by exact_mod_cast hkn
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓy' : (ℓ : ℝ) ≤ y.ℓ := by exact_mod_cast hℓy
  have hℓy₂' : (y.ℓ : ℝ) ≤ 2 * ℓ := by exact_mod_cast hℓy₂
  have hm1 : (1 : ℝ) ≤ min (n : ℝ) (ℓ + 1) := le_min hn' (by linarith)
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hμMk : 0 ≤ μM y.k := hμM₀.trans (hμM (Nat.zero_le _))
  have hν : 4 * μM y.k + 10 + 10 * √(y.k : ℝ) ≤ 4 * μM n + 10 + 10 * √(n : ℝ) := by
    linarith [hμM hkn, Real.sqrt_le_sqrt hKn]
  obtain ⟨hXlow, hXup⟩ := node_threshold_bounds hK2 hKn hm1 he2 hθ hθ₁
  obtain ⟨hwR, -, hw2, -⟩ := node_shift_bounds hθ hθ₁ hRpos hn' hℓ'
  obtain ⟨hNy, hNst⟩ := node_newtonSchulzSteps_le hn' hK2 hKn hℓ' hθ hθ₁ hRpos hβ hnβ hε₁
  rw [← hN] at hNy hNst
  have hlog : Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1)))) ≤
      Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ) := by
    have h : 16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) =
        96 * n * min (n : ℝ) (ℓ + 1) / θ / y.k := by field_simp; ring
    rw [h]
    exact Real.log_le_log (by positivity) (div_le_self (by positivity) (by linarith))
  exact
  { nonneg_μM := hμMk
    nonneg_μQ := hμQ₀.trans (hμQ (Nat.zero_le _))
    nonneg_cN := hcN
    nonneg_u := hu
    isHermitian := hA
    specNorm_le := hR
    twenty_le := hℓ.trans hℓy
    pos_ε := by linarith
    ε_le := hεy'.trans (hε₁.trans (by norm_num))
    pos_R₀ := hR₀pos
    pos_w := by positivity
    w_le := hwR
    pos_x := Real.sqrt_pos.mpr ((by positivity : (0 : ℝ) < 5 * θ / (32 * (n * min (n : ℝ) (ℓ + 1) *
      min (n : ℝ) (Real.exp 1)))).trans_le hXlow)
    x_le := Real.sqrt_le_one.mpr hXup
    le_t := le_add_of_nonneg_right (Real.sqrt_nonneg _)
    pos_β := hβ
    defl_tol := node_defl_tol hℓ' hℓy' hℓy₂' hε hεy hθ (by positivity) (by positivity)
      (add_le_add (by gcongr) (Real.sqrt_le_sqrt hlog)) (Real.sqrt_le_sqrt hXlow) hβ.le hβle
    sign_tol := by
      rw [mul_div_assoc, hw2, show (1 - 2⁻¹ ^ 7) * (2 * θ / (9 * n * ℓ * (ℓ + 1))) * dec β =
        127 / 64 * (θ * dec β) / (9 * n * ℓ * (ℓ + 1)) by ring, le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hν hu)
        (by positivity : (0 : ℝ) ≤ n * ℓ * (ℓ + 1))
      linarith [mul_pos hθ hβ]
    stop_tol := by
      refine le_trans ?_ hustop
      have h1 : (y.k : ℝ) + newtonSchulzSteps (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)) /
          (5 * dec y.R)) (dec β / (16 * y.k)) + 1 ≤ n + Nst + 1 := by linarith
      have h2 := mul_le_mul h1 hν (by positivity) (by positivity)
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2048 * u)
      linarith
    defl_u := by
      refine le_trans ?_ hudefl
      have := hμQ hkn
      have := hμM hkn
      gcongr
    mul_β_le := by
      have := mul_le_mul_of_nonneg_right hKn hβ.le
      linarith [show (2⁻¹ : ℝ) ^ 15 / 4000 ≤ 1 / 57600 by norm_num]
    fuel := hNy.trans hfuel
    nonneg_τ := hτ₀
    τ_le := by
      exact node_τ_le hτ₀ (by linarith) hKn hm1 (Real.exp_pos 1) exp_one_le_four hθ
        (Real.sqrt_le_sqrt hXlow) hτ hε hεy3 hR₀pos
    Ω_le := by
      have := Real.sqrt_le_sqrt hlog
      have := Real.sqrt_le_sqrt hKn
      have : (2 : ℝ) * √2 * √(y.k : ℝ) ≤ 2 * √2 * √(n : ℝ) := by gcongr
      linarith }

/-- The child of the node at the path $a$ is the node at the path $a + [b]$. -/
private lemma eighNodeAt_append_singleton_eq_some {F Su Sg : Type*} [Inhabited Sg]
    {M : FloatMachine F Su Sg} {N signFuel : ℕ} {R₀ β : F} {b : Bool} {y y' : EighNode F} :
    ∀ (a : List Bool) (x : EighNode F) (s : List Bool → EighSample Su Sg N),
      eighNodeAt M N signFuel R₀ β a x s = some y →
      eighChild M N signFuel R₀ β y (s a) b = some y' →
      eighNodeAt M N signFuel R₀ β (a ++ [b]) x s = some y'
  | [], x, s, h, h' => by
    obtain rfl : x = y := Option.some_injective _ h
    simpa [eighNodeAt] using h'
  | b' :: a, x, s, h, h' => by
    simp only [eighNodeAt, Option.bind_eq_some_iff] at h
    obtain ⟨z, hz, hza⟩ := h
    simp only [List.cons_append, eighNodeAt, hz, Option.bind_some]
    exact eighNodeAt_append_singleton_eq_some a z _ hza h'

/-- **Global deterministic guarantee of spectral bisection**: let the
machine meet `NLAlib.FloatMachine.IsAccurate` with $u \ge 0$, $\mu_{\mathrm{MM}}$,
$\mu_{\mathrm{QR}}$ monotone and nonnegative and $c_{\mathrm N} \ge 0$; let the stored
$\mathbf{A}$ have Hermitian decoding with $\|\mathbf{A}\|_2 \le R_0$, $R_0 > 0$,
$0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$, $\ell \ge$ `NLAlib.bisectionDepth`
$\varepsilon$, $m = \min(n, \ell + 1)$, $\hat T = 2\sqrt2\sqrt n + \sqrt{\log(96nm/\theta)}$,
$\nu = 4\mu_{\mathrm{MM}}(n) + 10 + 10\sqrt n$, the accuracy
$$0 < \beta \le \frac{(\ell - 1)^2\,\varepsilon\sqrt\theta}{52\,\ell^2(2\ell - 1)
\sqrt{n m \min(n, e)}\;\hat T} \,, \qquad
N_* = N\Bigl(\frac{\theta}{12n\ell(\ell + 1)}, \frac{\beta}{16n}\Bigr) \,,$$
$146\,n\ell(\ell + 1)\,\nu u \le \theta\beta$, $2048(n + N_* + 1)\nu u \le \beta$,
$16(4\mu_{\mathrm{QR}}(n) + 4\sqrt n(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(n) + 1)u \le \beta$,
at least $N_*$ sign steps, $0 \le \tau$, $100n^{3/2}\tau \le \min(\sqrt{\theta/(8nm)},
\varepsilon\min(R_0, 1))$ and $16(2R_0 + n + 2\ell + \hat T) \le \Omega$. If every internal node
$y$ has a good sample with $w_y = 4\theta R_y/(9n\ell(\ell + 1))$, $\rho_y = \theta k_y/(6nm)$,
$x_y = \sqrt{15\rho_y/(16\min(k_y^2, e k_y))}$ and $t_y = 2\sqrt2\sqrt{k_y} +
\sqrt{\log(16/\rho_y)}$, then `NLAlib.eigh` is an approximate diagonalization of $\mathbf{A}$
with residual $2\varepsilon R_0$ and singular values within $\varepsilon/3$ of $1$. [Shah2024,
Theorem 4.2], deterministic part. -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_eigh_of_forall_isEighGoodSample
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hμM : Monotone μM) (hμQ : Monotone μQ)
    (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0) (hcN : 0 ≤ cN) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (F × F)} (hA : (decodeMatrix dec A).IsHermitian) {ε : F}
    {θ : ℝ} (hR₀ : specNorm (decodeMatrix dec A) ≤ dec R₀) (hR₀pos : 0 < dec R₀)
    (hε : 0 < dec ε) (hε₁ : dec ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) {ℓ : ℕ}
    (hℓ : bisectionDepth (dec ε) ≤ ℓ) (hβ : 0 < dec β)
    (hβle : dec β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(n * min (n : ℝ) (ℓ + 1) * min (n : ℝ) (Real.exp 1)) *
      (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))))) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * n * ℓ * (ℓ + 1))) (dec β / (16 * n)))
    (husign : 146 * n * ℓ * (ℓ + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ θ * dec β)
    (hustop : 2048 * (n + Nst + 1) * (4 * μM n + 10 + 10 * √(n : ℝ)) * u ≤ dec β)
    (hudefl : 16 * (4 * μQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * μM n + 1) * u ≤ dec β)
    (hfuel : Nst ≤ signFuel) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (100 * n * √(n : ℝ)) ≤
      min (√(θ / (8 * n * min (n : ℝ) (ℓ + 1)))) (dec ε * min (dec R₀) 1))
    (hΩ : 16 * (2 * dec R₀ + n + 2 * ℓ + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ))) ≤ Ω)
    {s : List Bool → EighSample ℝ ℂ n}
    (hgood : ∀ (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → 2 ≤ y.k →
        M.le y.R (M.mul y.ε R₀) = false →
        IsEighGoodSample dec (4 * θ * dec y.R / (9 * n * ℓ * (ℓ + 1)))
          (√(15 * (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))) /
            (16 * min ((y.k : ℝ) ^ 2) (Real.exp 1 * y.k))))
          (2 * √2 * √(y.k : ℝ) + √(Real.log (16 / (θ * y.k / (6 * n * min (n : ℝ) (ℓ + 1))))))
          y (s a)) :
    IsApproxDiagonalization (decodeMatrix dec A) (decodeMatrix dec (eigh M signFuel ℓ A R₀ ε β s).1)
      (fun i => dec ((eigh M signFuel ℓ A R₀ ε β s).2 i)) (2 * dec ε * dec R₀) (dec ε / 3) := by
  have hκ₁ : dec ε / 3 ≤ 1 := by linarith [hε₁.trans (show (2⁻¹ : ℝ) ^ 15 ≤ 1 by norm_num)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hM.isApproxDiagonalization_eighAux_succ_of_leaf hA (by positivity) hκ₁
      (Or.inl ⟨Nat.zero_le 1, by positivity⟩)
  obtain ⟨hℓ20, hu₁, hτ', hΩ', hnβ⟩ := eigh_global_bounds hu hμM hμM₀ hn hR₀pos hε hε₁ hθ hθ₁
    hℓ hβ hβle husign hτ₀ hτ hΩ
  have hε1 : dec ε ≤ 1 := hε₁.trans (by norm_num)
  have key : ∀ (f : ℕ) (a : List Bool) (y : EighNode F),
      eighNodeAt M n signFuel R₀ β a ⟨n, A, R₀, ε, ℓ⟩ s = some y → ℓ + 1 ≤ f + a.length →
      (decodeMatrix dec y.A).IsHermitian → specNorm (decodeMatrix dec y.A) ≤ dec y.R →
      IsApproxDiagonalization (decodeMatrix dec y.A)
        (decodeMatrix dec (eighAux M n signFuel R₀ β f y.A y.R y.ε y.ℓ fun a' => s (a ++ a')).1)
        (fun i => dec ((eighAux M n signFuel R₀ β f y.A y.R y.ε y.ℓ
          fun a' => s (a ++ a')).2 i))
        (dec y.ε * (dec y.R + dec R₀)) (dec y.ε / 3) := by
    intro f
    induction f with
    | zero =>
      intro a y hy hfa _ _
      have := (hM.eighNodeAt_eq_some_params hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ' hΩ' A s hy).1
      omega
    | succ f ih =>
      intro a y hy hfa hyA hyR
      obtain ⟨hal, hkn, hℓy, hεy, hεy', hRy⟩ :=
        hM.eighNodeAt_eq_some_params hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ' hΩ' A s hy
      have hRy0 : 0 ≤ dec y.R := (specNorm_nonneg _).trans hyR
      have hεy0 : 0 < dec y.ε := by linarith
      by_cases hleaf : y.k ≤ 1 ∨ dec y.R ≤ 0
      · refine hM.isApproxDiagonalization_eighAux_succ_of_leaf hyA (by positivity)
          (by linarith) ?_
        rcases hleaf with hk | hR0
        · exact Or.inl ⟨hk, by positivity⟩
        refine Or.inr ⟨?_, hyR.trans (hR0.trans (by positivity))⟩
        rw [hM.le_iff]
        have hp : 0 < dec y.ε * dec R₀ := by positivity
        have hεR : dec y.ε * dec R₀ ≤ dec R₀ := by
          simpa using mul_le_mul_of_nonneg_right (hεy'.trans hε1) hR₀pos.le
        have hmul := hM.mul y.ε R₀ (by
          rw [abs_of_pos hp]
          linarith [Real.sqrt_nonneg (Real.log (96 * n * min (n : ℝ) (ℓ + 1) / θ)),
            Real.sqrt_nonneg (n : ℝ), Real.sqrt_nonneg 2])
        have hτR : τ ≤ dec y.ε * dec R₀ := by
          have h1 : dec ε * min (dec R₀) 1 ≤ dec ε * dec R₀ := by gcongr; exact min_le_left _ _
          have h5 := mul_le_mul_of_nonneg_right hεy hR₀pos.le
          have h6 : 0 ≤ dec ε * dec R₀ := by positivity
          linarith
        rw [abs_of_pos hp, max_eq_left hτR] at hmul
        have hu1 : u ≤ 1 := by
          have h4 : (400 : ℝ) ≤ ℓ ^ 2 := by
            have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ20
            nlinarith
          linarith [mul_le_mul_of_nonneg_right h4 hu]
        linarith [(abs_le.mp hmul).2, mul_le_mul_of_nonneg_right hu1 hp.le]
      simp only [not_or, not_le] at hleaf
      have hℓy₂ : y.ℓ ≤ 2 * ℓ := by omega
      have hεy₂ := hM.mul_le_dec_ε_of_eighNodeAt_eq_some hε hε₁ hR₀pos hℓ hu hu₁ hτ₀ hτ' hΩ' A s hy
      have hB := isEighNodeBudget_of_node (M := M) (signFuel := signFuel) hu hμM hμQ hμM₀ hμQ₀
        hcN hR₀pos hε hε₁ hθ hθ₁ hℓ20 hβ hβle hN husign hustop hudefl hfuel hτ₀ hτ hΩ hnβ hyA
        hyR hkn (by omega) hℓy₂ hεy₂ hεy hεy' hRy hleaf.1 hleaf.2
      have hg := hgood a y hy
      rw [← List.append_nil a] at hg
      refine hM.isApproxDiagonalization_eighAux_succ_of_isEighNodeBudget hB hg ?_
      intro b y' hy'
      obtain ⟨hA', hR'⟩ := hM.isHermitian_and_specNorm_le_of_isEighNodeBudget hB hg hy'
      simp only [List.append_nil] at hy'
      have h := ih (a ++ [b]) y' (eighNodeAt_append_singleton_eq_some a _ s hy hy')
        (by simp only [List.length_append, List.length_singleton]; omega) hA' hR'
      have hs : (fun a'' => s (a ++ [b] ++ a'')) = fun a'' => s (a ++ b :: a'') := by
        funext a''
        simp
      rw [hs] at h
      exact h
  rw [show 2 * dec ε * dec R₀ = dec ε * (dec R₀ + dec R₀) by ring]
  exact key (ℓ + 1) [] _ rfl (by simp) hA hR₀

end NLAlib
