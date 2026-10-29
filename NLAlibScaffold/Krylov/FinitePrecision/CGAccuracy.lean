/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import NLAlibScaffold.Krylov.FinitePrecision.CGBackward

/-!
# The residual gap and the attainable accuracy of finite-precision CG, a priori

For a conjugate gradient run `C : NLAlib.CGRun n k` on a matrix with spectrum in $[a, a']$,
$a > 0$, $\kappa = a'/a$, under (H) $k^3\varepsilon\kappa^2 \le 10^{-5}$ and
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, the computed iterates, the $\mathbf{A}$-norm error of
the computed run and the residual gap $\mathbf{g}_j = \mathbf{b} - \mathbf{A}\mathbf{x}_j -
\mathbf{r}_j$ are bounded a priori: with
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{x}_j\| \le 1.001\,M,\qquad
\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 \le 1.001\,\|\mathbf{x}_\star\|_{\mathbf{A}}^2,
\qquad \|\mathbf{g}_k\| \le 11\,k\,\varepsilon\,a'M .$$
Every rigorous gap bound in the literature keeps $\max_j\|\mathbf{x}_j\|$ (a posteriori);
[MeurantStrakos2006, §5.4] states the a priori form as a heuristic.

The proof is one joint induction (the private theorem `gapErrorInduction`) on the gap and the
true $\mathbf{A}$-norm error $E_j$ of the computed run: the descent
$\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j \ge 0.999\rho_j^2$ (G1, from the line search defect), the
step $\gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j \le 1.001\gamma_j\rho_j^2$ (G2),
$\gamma_j\|\mathbf{p}_j\| \le 1.5\|\mathbf{b}\|/a$ through the model's
$\sum_j\gamma_j\rho_j^2 \le 2\|\mathbf{b}\|^2/a$ (G2′), and the one-step inequality for
$E_{j+1}$ (G3).

The **attainable accuracy**: after $k^\star = \lceil\tfrac12(\sqrt{\kappa'} + 1)\ell\rceil$ steps,
$\kappa' = 2\kappa + 1$, $\ell = \ln(\sqrt{\kappa'}/(4\varepsilon))$, the computed residual is
below $8\varepsilon\|\mathbf{b}\|$ (`NLAlib.CGRun.ρ_le_of_cgKStar_le`, the Chebyshev bound of the
model), so the true residual is the gap up to $8\varepsilon\|\mathbf{b}\|$. Exact arithmetic is
an admissible run with zero gap, so no statement "computed residual $\ll$ true residual" holds;
the $\delta$-form compares with the gap bound instead.

Validity: (H) bounds the number of steps; with $k = k^\star$ this needs roughly
$\kappa \lesssim 0.05\,\varepsilon^{-2/7}\ell^{-6/7}$ (the research note
`~/nlalib-harness/reports/HSCG-FP-Research.md`, §4.3: $\kappa \le 80$ at $\varepsilon = u$ in
double precision, $\kappa \le 5$ for dense products at $N = 10^3$).

Research branch `research/hscg-fp`. Design: `docs/design/research/Krylov-CGRounding.md` (§9) and
the research note, §§4.2–4.3, 4.5. Constants are unoptimised and differ from the note's
(maintainer, 2026-10-29: "do whatever is cleanest proof-wise").

## Main definitions

* `NLAlib.cgKStar`: the number of steps after which the computed residual is at gap level.

## Main results

* `NLAlib.CGRun.p_dotProduct_r_ge`, `NLAlib.CGRun.γ_sq_mul_dotProduct_mulVec_le`,
  `NLAlib.CGRun.γ_mul_norm_p_le`, `NLAlib.CGRun.quadForm_sub_x_succ_le`: the one-step lemmas.
* `NLAlib.CGRun.quadForm_sub_x_le_sub_sum`, `NLAlib.CGRun.quadForm_sub_x_le`,
  `NLAlib.CGRun.norm_x_le`: the computed run's error and iterates, a priori.
* `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_energy`,
  `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_norm_sol`,
  `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_norm_b`: the residual gap, a priori.
* `NLAlib.CGRun.norm_sub_mulVec_x_le`: the true residual.
* `NLAlib.CGRun.ρ_le_of_cgKStar_le`, `NLAlib.CGRun.abs_norm_sub_mulVec_x_sub_norm_gap_le`,
  `NLAlib.CGRun.norm_sub_mulVec_x_le_of_cgKStar_le`, `NLAlib.CGRun.norm_sub_x_le_of_cgKStar_le`,
  `NLAlib.CGRun.norm_sub_mulVec_x_cgKStar_le`: the attainable accuracy.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **The number of steps to gap level**: with $\kappa' = 2\kappa + 1$,
$k^\star(\kappa, \varepsilon, \delta) = \bigl\lceil\tfrac12(\sqrt{2\kappa+1} + 1)
\ln\bigl(\sqrt{2\kappa+1}/(4\delta\varepsilon)\bigr)\bigr\rceil$. After $k^\star$ steps the
Chebyshev factor $2\sqrt{\kappa'}q^{k}$, $q = (\sqrt{\kappa'} - 1)/(\sqrt{\kappa'} + 1)$, is at
most $8\delta\varepsilon$ (`NLAlib.pow_le_of_cgKStar_le`). The research note has $\sqrt{\kappa'}$ in
place of $\sqrt{\kappa'} + 1$ (from $\ln(1/q) \ge 2/\sqrt{\kappa'}$); here
$q \le e^{-2/(\sqrt{\kappa'} + 1)}$, which is one line. -/
noncomputable def cgKStar (κ ε δ : ℝ) : ℕ :=
  ⌈(Real.sqrt (2 * κ + 1) + 1) / 2 * Real.log (Real.sqrt (2 * κ + 1) / (4 * δ * ε))⌉₊

/-- **The Chebyshev factor after $k^\star$ steps**: for $\varepsilon, \delta > 0$, $\kappa \ge 0$
and $m \ge k^\star(\kappa, \varepsilon, \delta)$, with $\kappa' = 2\kappa + 1$,
$$\Bigl(\frac{\sqrt{\kappa'} - 1}{\sqrt{\kappa'} + 1}\Bigr)^m \le
\frac{4\delta\varepsilon}{\sqrt{\kappa'}} \,.$$
Proof: $q = 1 - 2/(\sqrt{\kappa'} + 1) \le e^{-2/(\sqrt{\kappa'} + 1)}$
(`Real.add_one_le_exp`), $0 \le q$, and $2m/(\sqrt{\kappa'} + 1) \ge \ell$. Difficulty: easy. -/
theorem pow_le_of_cgKStar_le {κ ε δ : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (hδ : 0 < δ) {m : ℕ}
    (hm : cgKStar κ ε δ ≤ m) :
    ((Real.sqrt (2 * κ + 1) - 1) / (Real.sqrt (2 * κ + 1) + 1)) ^ m ≤
      4 * δ * ε / Real.sqrt (2 * κ + 1) := by
  set s := Real.sqrt (2 * κ + 1) with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef, Real.one_le_sqrt]; linarith
  set q := (s - 1) / (s + 1) with hq
  have hq0 : 0 ≤ q := div_nonneg (by linarith) (by linarith)
  have hq1 : q ≤ Real.exp (-(2 / (s + 1))) := by
    have h := Real.add_one_le_exp (-(2 / (s + 1)))
    have : q = -(2 / (s + 1)) + 1 := by rw [hq]; field_simp; ring
    rw [this]
    exact h
  have hm' : (s + 1) / 2 * Real.log (s / (4 * δ * ε)) ≤ m :=
    (Nat.le_ceil _).trans (by exact_mod_cast hm)
  have h1 : q ^ m ≤ Real.exp (-(2 / (s + 1))) ^ m := pow_le_pow_left₀ hq0 hq1 m
  rw [← Real.exp_nat_mul] at h1
  have h2 : Real.exp (m * -(2 / (s + 1))) ≤ Real.exp (-Real.log (s / (4 * δ * ε))) := by
    apply Real.exp_le_exp.mpr
    have : Real.log (s / (4 * δ * ε)) ≤ m * (2 / (s + 1)) := by
      rw [mul_div_assoc', le_div_iff₀ (by linarith)]
      linarith
    linarith
  have h3 : Real.exp (-Real.log (s / (4 * δ * ε))) = 4 * δ * ε / s := by
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  linarith

/-- $k^\star \ge 1$ for $\kappa \ge 0$, $0 < \delta \le 1$ and $0 < \varepsilon \le 1/100$:
the logarithm is at least $\ln 25 > 0$. Proof: `Nat.ceil_pos`. Difficulty: easy. -/
theorem cgKStar_pos {κ ε δ : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) : 0 < cgKStar κ ε δ := by
  apply Nat.ceil_pos.mpr
  have hs1 : 1 ≤ Real.sqrt (2 * κ + 1) := by rw [Real.one_le_sqrt]; linarith
  have h : 1 < Real.sqrt (2 * κ + 1) / (4 * δ * ε) := by
    rw [one_lt_div (by positivity)]
    nlinarith
  exact mul_pos (by linarith) (Real.log_pos h)

/-- **The window condition for $k^\star$**: for $\kappa \ge 1$ and $0 < \varepsilon \le 1/100$,
with $\ell = \ln(\sqrt{2\kappa + 1}/(4\varepsilon))$,
$\kappa^3\sqrt{\kappa}\,\varepsilon\,\ell^3 \le 7 \cdot 10^{-7}$ implies that (H) holds at
$k^\star$: $(k^\star)^3\varepsilon\kappa^2 \le 10^{-5}$. The research note has $\kappa^{7/2}
\varepsilon\ell^3 \le 1.5 \cdot 10^{-5}$ with its sharper $k^\star$.
Proof: $k^\star \le \tfrac12(\sqrt{2\kappa+1} + 1)\ell + 1 \le 2.37\sqrt{\kappa}\,\ell$ since
$\ell \ge 1$ and $\sqrt{2\kappa + 1} \le \sqrt{3}\sqrt{\kappa}$; $2.37^3 \cdot 7 \cdot 10^{-7} \le
10^{-5}$. Difficulty: easy. -/
theorem cgKStar_cube_mul_le {κ ε : ℝ} (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    (h : κ ^ 3 * Real.sqrt κ * ε *
      Real.log (Real.sqrt (2 * κ + 1) / (4 * 1 * ε)) ^ 3 ≤ 7 / 10 ^ 7) :
    (cgKStar κ ε 1 : ℝ) ^ 3 * ε * κ ^ 2 ≤ 1 / 10 ^ 5 := by
  set s := Real.sqrt (2 * κ + 1) with hsdef
  set ℓ := Real.log (s / (4 * 1 * ε)) with hℓ
  have hκ0 : 0 ≤ κ := by linarith
  have hs1 : 1 ≤ s := by rw [hsdef, Real.one_le_sqrt]; linarith
  have hsk : Real.sqrt κ ≥ 1 := by rw [ge_iff_le, Real.one_le_sqrt]; exact hκ
  -- `ℓ ≥ 1`
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by positivity)]
    have he := Real.exp_one_lt_d9
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- `s ≤ 1.74 √κ`
  have hs3 : s ≤ 174 / 100 * Real.sqrt κ := by
    have h3 : Real.sqrt 3 ≤ 174 / 100 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    calc s ≤ Real.sqrt (3 * κ) := Real.sqrt_le_sqrt (by linarith)
      _ = Real.sqrt 3 * Real.sqrt κ := Real.sqrt_mul (by norm_num) κ
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
  have hK : (cgKStar κ ε 1 : ℝ) ≤ 237 / 100 * Real.sqrt κ * ℓ := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ (s + 1) / 2 * ℓ)
    have : (s + 1) / 2 * ℓ + 1 ≤ 237 / 100 * Real.sqrt κ * ℓ := by nlinarith
    exact (le_of_lt h).trans this
  have hK0 : (0 : ℝ) ≤ cgKStar κ ε 1 := Nat.cast_nonneg _
  have hK3 : (cgKStar κ ε 1 : ℝ) ^ 3 ≤ (237 / 100 * Real.sqrt κ * ℓ) ^ 3 :=
    pow_le_pow_left₀ hK0 hK 3
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ0
  have e : (237 / 100 * Real.sqrt κ * ℓ) ^ 3 * ε * κ ^ 2 =
      (237 / 100) ^ 3 * (κ ^ 3 * Real.sqrt κ * ε * ℓ ^ 3) := by
    have : Real.sqrt κ ^ 3 = κ * Real.sqrt κ := by rw [pow_succ, hsq]
    rw [mul_pow, mul_pow, this]
    ring
  calc (cgKStar κ ε 1 : ℝ) ^ 3 * ε * κ ^ 2 ≤ (237 / 100 * Real.sqrt κ * ℓ) ^ 3 * ε * κ ^ 2 := by
        gcongr
    _ = _ := e
    _ ≤ (237 / 100) ^ 3 * (7 / 10 ^ 7) := by gcongr
    _ ≤ 1 / 10 ^ 5 := by norm_num

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-! ### The matrix of the run and (H) -/

/-- There is at least one coordinate: $n \ge 1$ since $\mathbf{r}_0 \neq \mathbf{0}$. -/
theorem n_pos {n k : ℕ} (C : CGRun n k) : 0 < n := by
  by_contra h
  have h0 : C.r 0 = 0 := funext fun i => absurd i.2 (by omega)
  have := C.ρ_pos C.k_pos
  rw [ρ, h0, WithLp.toLp_zero, norm_zero] at this
  exact lt_irrefl _ this

/-- The matrix of the run is Hermitian (it is real symmetric). -/
theorem isHermitian_A : C.A.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, C.transpose_A]

/-- The energy of $\mathbf{v}$ is $\mathbf{v}^{\mathsf{T}}\mathbf{A}\mathbf{v}$. -/
theorem quadForm_eq_dotProduct_mulVec (v : Fin n → ℝ) : quadForm C.A v = v ⬝ᵥ (C.A *ᵥ v) := by
  rw [quadForm_def, star_trivial]

/-- The symmetry of the matrix of the run:
$\mathbf{u}^{\mathsf{T}}\mathbf{A}\mathbf{v} = \mathbf{v}^{\mathsf{T}}\mathbf{A}\mathbf{u}$. -/
theorem dotProduct_mulVec_comm (u v : Fin n → ℝ) :
    u ⬝ᵥ (C.A *ᵥ v) = v ⬝ᵥ (C.A *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, C.transpose_A, dotProduct_comm]

/-- **The lower Rayleigh bound** for the matrix of the run: with spectrum in $[a, a']$,
$a\|\mathbf{v}\|^2 \le \mathbf{v}^{\mathsf{T}}\mathbf{A}\mathbf{v}$. -/
theorem mul_norm_sq_le_quadForm {a a' : ℝ} (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (v : Fin n → ℝ) : a * ‖WithLp.toLp 2 v‖ ^ 2 ≤ quadForm C.A v := by
  have hH := C.isHermitian_A
  obtain ⟨c, hc⟩ : ∃ c, c + 1 = Fintype.card (Fin n) := ⟨n - 1, by simp; have := C.n_pos; omega⟩
  have h1 := hH.eigenvalue_last_mul_le_re_quadForm hc v
  simp only [RCLike.re_to_real] at h1
  have e1 := (hH.spectrum_subset_iff.mp hs c (by omega)).1
  exact (mul_le_mul_of_nonneg_right e1 (sq_nonneg _)).trans h1

/-- **The upper Rayleigh bound** for the matrix of the run: with spectrum in $[a, a']$,
$\mathbf{v}^{\mathsf{T}}\mathbf{A}\mathbf{v} \le a'\|\mathbf{v}\|^2$. -/
theorem quadForm_le_mul_norm_sq {a a' : ℝ} (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (v : Fin n → ℝ) : quadForm C.A v ≤ a' * ‖WithLp.toLp 2 v‖ ^ 2 := by
  have hH := C.isHermitian_A
  have hpos := C.n_pos
  have h2 := hH.re_quadForm_le_eigenvalue_zero_mul v
  simp only [RCLike.re_to_real] at h2
  have e2 := (hH.spectrum_subset_iff.mp hs 0 (by simp; omega)).2
  exact h2.trans (mul_le_mul_of_nonneg_right e2 (sq_nonneg _))

/-- The spectral interval is nonempty: $a \le a'$. -/
theorem le_of_spectrum_subset_Icc {a a' : ℝ} (hs : spectrum ℝ C.A ⊆ Set.Icc a a') : a ≤ a' := by
  have e0 := C.isHermitian_A.spectrum_subset_iff.mp hs 0 (by
    simp only [Fintype.card_fin]; exact C.n_pos)
  exact e0.1.trans e0.2

/-- **The elementary consequences of the spectral hypothesis and of (H)**: with spectrum in
$[a, a']$, $a > 0$, $\kappa = a'/a$ and (H) $k^3\varepsilon\kappa^2 \le 10^{-5}$: $a \le a'$,
$1 \le \kappa$, $\|\mathbf{A}\|_2 \le a'$, $\varepsilon \le 10^{-5}$ and $k\varepsilon\kappa$,
$k^2\varepsilon\kappa$, $k^2\varepsilon\kappa^2 \le 10^{-5}$. -/
theorem le_of_cube_mul_ε_mul_sq_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    a ≤ a' ∧ 1 ≤ a' / a ∧ specNorm C.A ≤ a' ∧ C.ε ≤ 1 / 10 ^ 5 ∧
      (k : ℝ) * C.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧ (k : ℝ) ^ 2 * C.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧
      (k : ℝ) ^ 2 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
  have hn := C.n_pos
  have hherm := C.isHermitian_A
  have e0 := hherm.spectrum_subset_iff.mp hs 0 (by simp; omega)
  have e1 := hherm.spectrum_subset_iff.mp hs (n - 1) (by simp; omega)
  have haa' : a ≤ a' := e0.1.trans e0.2
  have hκ : 1 ≤ a' / a := (one_le_div ha).mpr haa'
  have hm : (1 : ℝ) ≤ k := by exact_mod_cast C.k_pos
  have hε := C.ε_nonneg
  have hspec : specNorm C.A ≤ a' := by
    have hc : n - 1 + 1 = Fintype.card (Fin n) := by simp; omega
    rw [hherm.specNorm_eq_max hc, abs_of_pos (ha.trans_le e0.1), abs_of_pos (ha.trans_le e1.1)]
    exact max_le e0.2 e1.2
  have hκ2 : a' / a ≤ (a' / a) ^ 2 := by nlinarith
  have hm2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hm3 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by nlinarith
  have hX : 0 ≤ C.ε * (a' / a) := by positivity
  have hY : 0 ≤ C.ε * (a' / a) ^ 2 := by positivity
  have h22 : (k : ℝ) ^ 2 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_right hm3 hY
    nlinarith
  have h2 : (k : ℝ) ^ 2 * C.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_left hκ2 (by positivity : 0 ≤ (k : ℝ) ^ 2 * C.ε)
    nlinarith
  have h1 : (k : ℝ) * C.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_right hm2 hX
    nlinarith
  have h0 : C.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_right hm hX
    nlinarith
  have he : C.ε ≤ 1 / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_left hκ hε
    nlinarith
  exact ⟨haa', hκ, hspec, he, h1, h2, h22⟩

private theorem acc_εκ {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) : C.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
  obtain ⟨-, hκ, -, -, hkεκ, -, -⟩ := C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall
  have h1k : (1 : ℝ) ≤ k := by exact_mod_cast C.k_pos
  have := mul_le_mul_of_nonneg_right h1k (by have := C.ε_nonneg; positivity :
    0 ≤ C.ε * (a' / a))
  nlinarith

/-- **The residual against the energy** for the matrix of the run:
$\|\mathbf{A}\mathbf{e}\|^2 \le a'\,\mathbf{e}^{\mathsf{T}}\mathbf{A}\mathbf{e}$
(Cauchy–Schwarz for the form of $\mathbf{A}$). -/
theorem norm_mulVec_sq_le_mul_quadForm {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (e : Fin n → ℝ) :
    ‖WithLp.toLp 2 (C.A *ᵥ e)‖ ^ 2 ≤ a' * quadForm C.A e := by
  have hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (C.A *ᵥ x) := fun x => by
    have := (C.mul_norm_sq_le_quadForm hs x)
    rw [C.quadForm_eq_dotProduct_mulVec] at this
    exact le_trans (by positivity) this
  set v := C.A *ᵥ e with hv
  have hCS : (e ⬝ᵥ (C.A *ᵥ v)) ^ 2 ≤ (e ⬝ᵥ (C.A *ᵥ e)) * (v ⬝ᵥ (C.A *ᵥ v)) := by
    have hd := discrim_le_zero (a := v ⬝ᵥ (C.A *ᵥ v)) (b := 2 * (e ⬝ᵥ (C.A *ᵥ v)))
      (c := e ⬝ᵥ (C.A *ᵥ e)) (fun x => by
        have h := hpsd (e + x • v)
        have hc := C.dotProduct_mulVec_comm v e
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
          smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
        rw [hc] at h
        have : v ⬝ᵥ (C.A *ᵥ v) * (x * x) + 2 * (e ⬝ᵥ (C.A *ᵥ v)) * x + e ⬝ᵥ (C.A *ᵥ e) =
            e ⬝ᵥ (C.A *ᵥ e) + x * (e ⬝ᵥ (C.A *ᵥ v)) +
              x * (e ⬝ᵥ (C.A *ᵥ v) + x * (v ⬝ᵥ (C.A *ᵥ v))) := by
          ring
        linarith)
    unfold discrim at hd
    nlinarith
  have h1 : e ⬝ᵥ (C.A *ᵥ v) = ‖WithLp.toLp 2 v‖ ^ 2 := by
    rw [C.dotProduct_mulVec_comm, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
  have h2 : v ⬝ᵥ (C.A *ᵥ v) ≤ a' * ‖WithLp.toLp 2 v‖ ^ 2 := by
    have := (C.quadForm_le_mul_norm_sq hs v)
    rwa [C.quadForm_eq_dotProduct_mulVec] at this
  have he0 := hpsd e
  rw [h1] at hCS
  rw [C.quadForm_eq_dotProduct_mulVec]
  rcases (sq_nonneg ‖WithLp.toLp 2 v‖).lt_or_eq with hpos | hzero
  · have : (‖WithLp.toLp 2 v‖ ^ 2) ^ 2 ≤ (e ⬝ᵥ (C.A *ᵥ e)) * (a' * ‖WithLp.toLp 2 v‖ ^ 2) :=
      hCS.trans (mul_le_mul_of_nonneg_left h2 he0)
    nlinarith
  · rw [← hzero]
    have ha' : 0 ≤ a' := ha.le.trans (C.le_of_spectrum_subset_Icc hs)
    positivity

/-! ### One step -/

/-- **Descent (G1)**: under (H), $\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j \ge
0.999\,\|\mathbf{r}_j\|^2$ for $j < k$. Exact CG has equality; here the line search defect
$\mathbf{p}_{j-1}^{\mathsf{T}}\mathbf{r}_j$ enters through
$\mathbf{p}_j = \mathbf{r}_j + \delta_{j-1}\mathbf{p}_{j-1} + \mathbf{e}^p_{j-1}$.
Proof: `NLAlib.CGRun.abs_p_dotProduct_r_succ_le` with $\Pi = 2\kappa$, $K = 1.05\kappa$
(`NLAlib.CGRun.norm_p_sq_le`, `NLAlib.CGRun.specNorm_mul_γ_mul_norm_p_sq_le`), so
$\lvert\delta_{j-1}\mathbf{p}_{j-1}^{\mathsf{T}}\mathbf{r}_j\rvert \le
26k\varepsilon\kappa\rho_j^2$, and
$\lvert\mathbf{e}^{p\mathsf{T}}_{j-1}\mathbf{r}_j\rvert \le
\varepsilon(\rho_j + \delta_{j-1}\|\mathbf{p}_{j-1}\|)\rho_j \le 5\varepsilon\kappa\rho_j^2$
(`NLAlib.CGRun.δ_mul_norm_p_le`). Difficulty: easy. -/
theorem p_dotProduct_r_ge {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j < k) :
    (1 - 1 / 1000) * C.ρ j ^ 2 ≤ C.p j ⬝ᵥ C.r j := by
  obtain ⟨-, hκ, -, hε5, hkεκ, -, -⟩ := C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have hP : ∀ i < k, ‖WithLp.toLp 2 (C.p i)‖ ≤ 2 * (a' / a) * C.ρ i := fun i hi => by
    have h := C.norm_p_sq_le ha hs hsmall hi
    have h2 : ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ (2 * (a' / a) * C.ρ i) ^ 2 := by
      have := C.ρ_nonneg i
      nlinarith [sq_nonneg (C.ρ i)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by have := C.ρ_nonneg i; positivity)
      two_ne_zero).mp h2
  have hK := fun i (hi : i < k) => C.specNorm_mul_γ_mul_norm_p_sq_le ha hs hsmall hi
  rcases j with _ | i
  · rw [C.p_zero, ← C.r_zero, ρ, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    have : 0 ≤ C.r 0 ⬝ᵥ C.r 0 := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    linarith
  · have hi : i < k := by omega
    have hτ := C.abs_p_dotProduct_r_succ_le hP hK hi
    obtain ⟨hδ0, hδ1, -⟩ := C.δ_bounds hi
    have hep := C.norm_ep_le' hi
    have hD := C.δ_mul_norm_p_le hi
    have hPi := hP (i + 1) hj
    have hid : C.p (i + 1) ⬝ᵥ C.r (i + 1) =
        C.ρ (i + 1) ^ 2 + C.δ i * (C.p i ⬝ᵥ C.r (i + 1)) + C.ep i ⬝ᵥ C.r (i + 1) := by
      rw [C.p_succ i hi, add_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul, ρ,
        EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    rw [hid]
    set ρ1 := C.ρ (i + 1)
    have hρ1 : 0 ≤ ρ1 := C.ρ_nonneg _
    -- the line search term
    have hik : ((i : ℕ) + 1 : ℝ) ≤ k := by exact_mod_cast hj.le
    have hY : 5 * ((i : ℝ) + 1) * C.ε * (1 + 2 * (a' / a) + 21 / 20 * (a' / a)) ≤
        21 / 10 ^ 5 := by
      have h1 : 1 + 2 * (a' / a) + 21 / 20 * (a' / a) ≤ 41 / 10 * (a' / a) := by linarith
      have h2 : ((i : ℝ) + 1) * C.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
        have := mul_le_mul_of_nonneg_right hik (by positivity : 0 ≤ C.ε * (a' / a))
        nlinarith
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 5 * ((i : ℝ) + 1) * C.ε)
      nlinarith
    have hτ' : |C.p i ⬝ᵥ C.r (i + 1)| ≤ 21 / 10 ^ 5 * C.ρ i ^ 2 := by
      refine hτ.trans ?_
      have := mul_le_mul_of_nonneg_right hY (sq_nonneg (C.ρ i))
      linarith
    have hδτ : |C.δ i * (C.p i ⬝ᵥ C.r (i + 1))| ≤ 22 / 10 ^ 5 * ρ1 ^ 2 := by
      rw [abs_mul, abs_of_nonneg hδ0]
      calc C.δ i * |C.p i ⬝ᵥ C.r (i + 1)| ≤ C.δ i * (21 / 10 ^ 5 * C.ρ i ^ 2) :=
            mul_le_mul_of_nonneg_left hτ' hδ0
        _ = 21 / 10 ^ 5 * (C.δ i * C.ρ i ^ 2) := by ring
        _ ≤ 21 / 10 ^ 5 * ((1 + 31 / 10 * C.ε) * ρ1 ^ 2) := by gcongr
        _ ≤ 22 / 10 ^ 5 * ρ1 ^ 2 := by nlinarith [sq_nonneg ρ1]
    -- the direction update term
    have hepr : |C.ep i ⬝ᵥ C.r (i + 1)| ≤ 5 / 10 ^ 5 * ρ1 ^ 2 := by
      refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans ?_
      have h1 : ‖WithLp.toLp 2 (C.ep i)‖ ≤ C.ε * (ρ1 + 21 / 20 * (2 * (a' / a) * ρ1 + ρ1)) := by
        refine hep.trans (mul_le_mul_of_nonneg_left ?_ hε0)
        linarith
      have h2 : C.ε * (ρ1 + 21 / 20 * (2 * (a' / a) * ρ1 + ρ1)) ≤ 5 / 10 ^ 5 * ρ1 := by
        have : C.ε * (ρ1 + 21 / 20 * (2 * (a' / a) * ρ1 + ρ1)) =
            ρ1 * (41 / 20 * C.ε + 21 / 10 * (C.ε * (a' / a))) := by ring
        rw [this]
        have hεκ : C.ε ≤ C.ε * (a' / a) := le_mul_of_one_le_right hε0 hκ
        have h0 : C.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
          have h1k : (1 : ℝ) ≤ k := by exact_mod_cast C.k_pos
          have := mul_le_mul_of_nonneg_right h1k (by positivity : 0 ≤ C.ε * (a' / a))
          nlinarith
        nlinarith
      calc ‖WithLp.toLp 2 (C.ep i)‖ * ‖WithLp.toLp 2 (C.r (i + 1))‖ ≤
            5 / 10 ^ 5 * ρ1 * ρ1 := mul_le_mul_of_nonneg_right (h1.trans h2) hρ1
        _ = _ := by ring
    have := (abs_le.mp hδτ).1
    have := (abs_le.mp hepr).1
    nlinarith [sq_nonneg ρ1]

/-- **The step against the residual (G2)**: under (H), for $j < k$,
$\gamma_j^2\,\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j \le 1.001\,\gamma_j\|\mathbf{r}_j\|^2$.
Proof: $\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j = \mu_j - e^\mu_j -
\mathbf{p}_j^{\mathsf{T}}\mathbf{e}^s_j \le \mu_j + 2.1\varepsilon\kappa\,
\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j$ and $\gamma_j\mu_j = \nu_j(1 + \eta^\gamma_j)$
(`NLAlib.CGRun.γ_mul_μ`). Difficulty: easy. -/
theorem γ_sq_mul_dotProduct_mulVec_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {j : ℕ} (hj : j < k) :
    C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) ≤ (1 + 1 / 1000) * (C.γ j * C.ρ j ^ 2) := by
  obtain ⟨haa', hκ, hspec, hε5, -, -, -⟩ := C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall
  have hεκ := C.acc_εκ ha hs hsmall
  have hε0 := C.ε_nonneg
  have hγ := C.γ_pos hj
  have hN0 := specNorm_nonneg C.A
  set N := ‖WithLp.toLp 2 (C.p j)‖ with hN
  have hNn : 0 ≤ N := norm_nonneg _
  set P := C.p j ⬝ᵥ (C.A *ᵥ C.p j) with hPdef
  have hP0 : a * N ^ 2 ≤ P := by
    have := (C.mul_norm_sq_le_quadForm hs (C.p j))
    rwa [C.quadForm_eq_dotProduct_mulVec] at this
  have hμ : C.μ j = P + C.p j ⬝ᵥ C.es j + C.eμ j := by
    rw [C.μ_eq j hj, C.s_eq j hj, dotProduct_add]
  have h1 : |C.p j ⬝ᵥ C.es j| ≤ C.ε * a' * N ^ 2 := by
    refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans ?_
    have := C.norm_es_le j hj
    calc N * ‖WithLp.toLp 2 (C.es j)‖ ≤ N * (C.ε * specNorm C.A * N) :=
          mul_le_mul_of_nonneg_left this hNn
      _ ≤ N * (C.ε * a' * N) := by gcongr
      _ = _ := by ring
  have h2 : |C.eμ j| ≤ 2 * C.ε * a' * N ^ 2 := by
    refine (C.abs_eμ_le j hj).trans ?_
    have hs' := C.norm_s_le hj
    have : ‖WithLp.toLp 2 (C.s j)‖ ≤ 2 * a' * N := by
      refine hs'.trans ?_
      have : (1 + C.ε) * specNorm C.A ≤ 2 * a' := by nlinarith
      exact mul_le_mul_of_nonneg_right this hNn
    calc C.ε * N * ‖WithLp.toLp 2 (C.s j)‖ ≤ C.ε * N * (2 * a' * N) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have h3 : a' * N ^ 2 ≤ a' / a * P := by
    have := mul_le_mul_of_nonneg_left hP0 (by positivity : 0 ≤ a' / a)
    calc a' * N ^ 2 = a' / a * (a * N ^ 2) := by field_simp
      _ ≤ _ := this
  have hPμ : P * (1 - 3 / 10 ^ 5) ≤ C.μ j := by
    have := (abs_le.mp h1).1
    have := (abs_le.mp h2).1
    have h4 : C.ε * (a' * N ^ 2) ≤ C.ε * (a' / a * P) := mul_le_mul_of_nonneg_left h3 hε0
    have hP0' : 0 ≤ P := le_trans (by positivity) hP0
    have h5 : C.ε * (a' / a) * P ≤ 1 / 10 ^ 5 * P := mul_le_mul_of_nonneg_right hεκ hP0'
    nlinarith
  have hgm := C.γ_mul_μ hj
  rw [C.ν_eq' hj.le] at hgm
  have hθ := abs_le.mp (C.abs_θ_le j hj.le)
  have he := abs_le.mp (C.abs_eγ_le j hj)
  have hρ2 : 0 ≤ C.ρ j ^ 2 := sq_nonneg _
  have h6 : C.γ j * C.μ j ≤ (1 + 1 / 10 ^ 5) ^ 2 * C.ρ j ^ 2 := by
    rw [hgm]
    have : (1 + C.θ j) * (1 + C.eγ j) ≤ (1 + 1 / 10 ^ 5) ^ 2 := by nlinarith
    nlinarith
  have h7 : C.γ j ^ 2 * P * (1 - 3 / 10 ^ 5) ≤ C.γ j * ((1 + 1 / 10 ^ 5) ^ 2 * C.ρ j ^ 2) := by
    calc C.γ j ^ 2 * P * (1 - 3 / 10 ^ 5) = C.γ j * (C.γ j * (P * (1 - 3 / 10 ^ 5))) := by ring
      _ ≤ C.γ j * (C.γ j * C.μ j) := by gcongr
      _ ≤ _ := by gcongr
  have hγρ : 0 ≤ C.γ j * C.ρ j ^ 2 := by positivity
  nlinarith

/-- **The step length, a priori (G2′)**: under (H), $\gamma_j\|\mathbf{p}_j\| \le
1.5\|\mathbf{b}\|/a$ for $j < k$.
Proof: $a\gamma_j^2\|\mathbf{p}_j\|^2 \le \gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j
\le 1.001\gamma_j\rho_j^2$ (`NLAlib.CGRun.γ_sq_mul_dotProduct_mulVec_le`) and
$\sum_{j<k}\gamma_j\rho_j^2 \le 2\|\mathbf{b}\|^2/a$ (`NLAlib.CGRun.sum_γ_mul_ρ_sq_le`, the model).
Difficulty: easy. -/
theorem γ_mul_norm_p_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j < k) :
    C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ≤ 3 / 2 * ‖WithLp.toLp 2 C.b‖ / a := by
  have hsum := C.sum_γ_mul_ρ_sq_le ha hs hsmall
  have hγ := C.γ_pos hj
  have hle : C.γ j * C.ρ j ^ 2 ≤ ∑ i ∈ Finset.range k, C.γ i * C.ρ i ^ 2 :=
    Finset.single_le_sum (f := fun i => C.γ i * C.ρ i ^ 2)
      (fun i hi => mul_nonneg (C.γ_pos (Finset.mem_range.mp hi)).le (sq_nonneg _))
      (Finset.mem_range.mpr hj)
  have h2 := C.γ_sq_mul_dotProduct_mulVec_le ha hs hsmall hj
  have hP0 : a * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ C.p j ⬝ᵥ (C.A *ᵥ C.p j) := by
    have := (C.mul_norm_sq_le_quadForm hs (C.p j))
    rwa [C.quadForm_eq_dotProduct_mulVec] at this
  set B := ‖WithLp.toLp 2 C.b‖
  set X := C.γ j * ‖WithLp.toLp 2 (C.p j)‖
  have hX0 : 0 ≤ X := by positivity
  have h3 : a * X ^ 2 ≤ (1 + 1 / 1000) * (2 * B ^ 2 / a) := by
    have := mul_le_mul_of_nonneg_left hP0 (sq_nonneg (C.γ j))
    have h4 : (1 + 1 / 1000) * (C.γ j * C.ρ j ^ 2) ≤ (1 + 1 / 1000) * (2 * B ^ 2 / a) := by
      gcongr
      exact hle.trans hsum
    have : a * X ^ 2 = C.γ j ^ 2 * (a * ‖WithLp.toLp 2 (C.p j)‖ ^ 2) := by
      simp only [X]
      ring
    linarith
  have h5 : X ^ 2 ≤ (3 / 2 * B / a) ^ 2 := by
    have : (3 / 2 * B / a) ^ 2 = 9 / 4 * B ^ 2 / a ^ 2 := by ring
    rw [this, le_div_iff₀ (by positivity)]
    have h6 : (1 + 1 / 1000) * (2 * B ^ 2 / a) * a = (1 + 1 / 1000) * 2 * B ^ 2 := by
      field_simp
    nlinarith [sq_nonneg B]
  exact (pow_le_pow_iff_left₀ hX0 (by positivity) two_ne_zero).mp h5

/-- The energy of a difference:
$\|\mathbf{u} - \mathbf{v}\|_{\mathbf{A}}^2 = \|\mathbf{u}\|_{\mathbf{A}}^2 -
2\,\mathbf{v}^{\mathsf{T}}\mathbf{A}\mathbf{u} + \|\mathbf{v}\|_{\mathbf{A}}^2$. -/
theorem quadForm_sub_eq (u v : Fin n → ℝ) :
    quadForm C.A (u - v) = quadForm C.A u - 2 * (v ⬝ᵥ (C.A *ᵥ u)) + quadForm C.A v := by
  simp only [C.quadForm_eq_dotProduct_mulVec, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
  rw [C.dotProduct_mulVec_comm u v]
  ring

/-- **The energy after the exact step, expanded**: for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
with the gap $\mathbf{g}_j = \mathbf{b} - \mathbf{A}\mathbf{x}_j - \mathbf{r}_j$,
$$\|\mathbf{x}_\star - \mathbf{x}_j - \gamma_j\mathbf{p}_j\|_{\mathbf{A}}^2 =
\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 -
2\gamma_j\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j - 2\gamma_j\mathbf{p}_j^{\mathsf{T}}\mathbf{g}_j +
\gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j .$$
Proof: $\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_j) = \mathbf{r}_j + \mathbf{g}_j$. -/
theorem quadForm_sub_x_sub_smul_p_eq {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) (j : ℕ) :
    quadForm C.A (xs - C.x j - C.γ j • C.p j) = quadForm C.A (xs - C.x j) -
      2 * C.γ j * (C.p j ⬝ᵥ C.r j) - 2 * C.γ j * (C.p j ⬝ᵥ (C.b - C.A *ᵥ C.x j - C.r j)) +
        C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) := by
  set e := xs - C.x j with he
  have hpAe : C.p j ⬝ᵥ (C.A *ᵥ e) =
      C.p j ⬝ᵥ C.r j + C.p j ⬝ᵥ (C.b - C.A *ᵥ C.x j - C.r j) := by
    rw [← dotProduct_add, he, Matrix.mulVec_sub, hx]
    congr 1
    abel
  have hexp : (e - C.γ j • C.p j) ⬝ᵥ (C.A *ᵥ (e - C.γ j • C.p j)) = e ⬝ᵥ (C.A *ᵥ e) -
      2 * C.γ j * (C.p j ⬝ᵥ (C.A *ᵥ e)) + C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [C.dotProduct_mulVec_comm e (C.p j)]
    ring
  rw [C.quadForm_eq_dotProduct_mulVec, C.quadForm_eq_dotProduct_mulVec, hexp, hpAe]
  ring

/-- G3 with the nonnegativity of the bracket, for the induction. -/
private theorem quadForm_sub_x_succ_le_aux {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) :
    0 ≤ quadForm C.A (xs - C.x j) - 99 / 100 * (C.γ j * C.ρ j ^ 2) +
          2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ ∧
    quadForm C.A (xs - C.x (j + 1)) ≤
      (Real.sqrt (quadForm C.A (xs - C.x j) - 99 / 100 * (C.γ j * C.ρ j ^ 2) +
          2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖) +
        Real.sqrt a' * ‖WithLp.toLp 2 (C.ex j)‖) ^ 2 := by
  have haa' := C.le_of_spectrum_subset_Icc hs
  have ha' : 0 ≤ a' := ha.le.trans haa'
  have hγ := C.γ_pos hj
  have hG1 := C.p_dotProduct_r_ge ha hs hsmall hj
  have hG2 := C.γ_sq_mul_dotProduct_mulVec_le ha hs hsmall hj
  have hwe := C.quadForm_sub_x_sub_smul_p_eq hx j
  set g := C.b - C.A *ᵥ C.x j - C.r j with hg
  set e := xs - C.x j with he
  set w := e - C.γ j • C.p j with hw
  set v := C.ex j
  set X := quadForm C.A e - 99 / 100 * (C.γ j * C.ρ j ^ 2) +
    2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * ‖WithLp.toLp 2 g‖ with hX
  have hxe : xs - C.x (j + 1) = w - v := by
    rw [C.x_succ j hj, hw, he]
    abel
  have hpg : |C.p j ⬝ᵥ g| ≤ ‖WithLp.toLp 2 (C.p j)‖ * ‖WithLp.toLp 2 g‖ :=
    EuclideanSpace.abs_dotProduct_le_norm _ _
  have hQw0 : 0 ≤ quadForm C.A w := le_trans (by positivity) (C.mul_norm_sq_le_quadForm hs w)
  have hQw : quadForm C.A w ≤ X := by
    rw [hwe, hX]
    have h1 := (abs_le.mp hpg).1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * C.γ j)
    have h3 := mul_le_mul_of_nonneg_left hG1 (by positivity : 0 ≤ 2 * C.γ j)
    have h4 : 0 ≤ C.γ j * C.ρ j ^ 2 := by positivity
    nlinarith
  refine ⟨hQw0.trans hQw, ?_⟩
  set W := Real.sqrt (quadForm C.A w)
  have hW0 : 0 ≤ W := Real.sqrt_nonneg _
  have hW2 : W ^ 2 = quadForm C.A w := Real.sq_sqrt hQw0
  have hsa : Real.sqrt a' ^ 2 = a' := Real.sq_sqrt ha'
  have hsa0 : 0 ≤ Real.sqrt a' := Real.sqrt_nonneg _
  have hAw : ‖WithLp.toLp 2 (C.A *ᵥ w)‖ ≤ Real.sqrt a' * W := by
    have h := C.norm_mulVec_sq_le_mul_quadForm ha hs w
    have h' : ‖WithLp.toLp 2 (C.A *ᵥ w)‖ ^ 2 ≤ (Real.sqrt a' * W) ^ 2 := by
      rw [mul_pow, hsa, hW2]
      exact h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h'
  have hvw : |v ⬝ᵥ (C.A *ᵥ w)| ≤ ‖WithLp.toLp 2 v‖ * (Real.sqrt a' * W) :=
    (EuclideanSpace.abs_dotProduct_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hAw (norm_nonneg _))
  have hQv : quadForm C.A v ≤ (Real.sqrt a' * ‖WithLp.toLp 2 v‖) ^ 2 := by
    rw [mul_pow, hsa]
    exact (C.quadForm_le_mul_norm_sq hs v)
  have hWX : W ≤ Real.sqrt X := Real.sqrt_le_sqrt hQw
  have hv0 := norm_nonneg (WithLp.toLp 2 v)
  rw [hxe, C.quadForm_sub_eq w v]
  calc quadForm C.A w - 2 * (v ⬝ᵥ (C.A *ᵥ w)) + quadForm C.A v ≤
        (W + Real.sqrt a' * ‖WithLp.toLp 2 v‖) ^ 2 := by
        have := (abs_le.mp hvw).1
        nlinarith
    _ ≤ _ := by gcongr

/-- **One step of the computed run's $\mathbf{A}$-norm error (G3)**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $j < k$, with the gap
$\mathbf{g}_j = \mathbf{b} - \mathbf{A}\mathbf{x}_j - \mathbf{r}_j$,
$$\|\mathbf{x}_\star - \mathbf{x}_{j+1}\|_{\mathbf{A}} \le
\sqrt{\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 - 0.99\,\gamma_j\|\mathbf{r}_j\|^2 +
2\gamma_j\|\mathbf{p}_j\|\|\mathbf{g}_j\|} + \sqrt{a'}\,\|\mathbf{e}^x_j\| \,.$$
Proof: $\mathbf{w} = \mathbf{x}_\star - \mathbf{x}_j - \gamma_j\mathbf{p}_j$ has
$\|\mathbf{w}\|_{\mathbf{A}}^2 = E_j^2 - 2\gamma_j\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j -
2\gamma_j\mathbf{p}_j^{\mathsf{T}}\mathbf{g}_j + \gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}
\mathbf{p}_j$ (G1, G2), and $\mathbf{x}_\star - \mathbf{x}_{j+1} = \mathbf{w} - \mathbf{e}^x_j$
with $\|\mathbf{A}\mathbf{w}\|^2 \le a'\|\mathbf{w}\|_{\mathbf{A}}^2$. Difficulty: easy. -/
theorem quadForm_sub_x_succ_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) :
    quadForm C.A (xs - C.x (j + 1)) ≤
      (Real.sqrt (quadForm C.A (xs - C.x j) - 99 / 100 * (C.γ j * C.ρ j ^ 2) +
          2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖) +
        Real.sqrt a' * ‖WithLp.toLp 2 (C.ex j)‖) ^ 2 := by
  exact (C.quadForm_sub_x_succ_le_aux ha hs hsmall hx hj).2

/-! ### The joint induction -/

/-- **The solution against the right-hand side**: with spectrum in $[a, a']$, $a > 0$, for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\|\mathbf{x}_\star\| \le \|\mathbf{b}\|/a$. -/
theorem norm_le_norm_b_div_of_mulVec_eq {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 xs‖ ≤ ‖WithLp.toLp 2 C.b‖ / a := by
  have h1 := (C.mul_norm_sq_le_quadForm hs xs)
  rw [C.quadForm_eq_dotProduct_mulVec, hx] at h1
  have h2 := (le_abs_self _).trans (EuclideanSpace.abs_dotProduct_le_norm xs C.b)
  rw [le_div_iff₀ ha]
  rcases (norm_nonneg (WithLp.toLp 2 xs)).lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]
    simp

/-- **The energy of the solution, from above**: with spectrum in $[a, a']$, $a > 0$, for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$\|\mathbf{x}_\star\|_{\mathbf{A}}^2 \le \|\mathbf{b}\|^2/a$. -/
theorem quadForm_le_norm_b_sq_div_of_mulVec_eq {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    quadForm C.A xs ≤ ‖WithLp.toLp 2 C.b‖ ^ 2 / a := by
  have h := C.norm_le_norm_b_div_of_mulVec_eq ha hs hx
  rw [C.quadForm_eq_dotProduct_mulVec, hx]
  refine (le_abs_self _).trans ((EuclideanSpace.abs_dotProduct_le_norm xs C.b).trans ?_)
  calc ‖WithLp.toLp 2 xs‖ * ‖WithLp.toLp 2 C.b‖ ≤
        ‖WithLp.toLp 2 C.b‖ / a * ‖WithLp.toLp 2 C.b‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖WithLp.toLp 2 C.b‖ ^ 2 / a := by ring

/-- **The energy of the solution, from below**: with spectrum in $[a, a']$, $a > 0$, for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$\|\mathbf{b}\|^2/a \le \kappa\,\|\mathbf{x}_\star\|_{\mathbf{A}}^2$. -/
theorem norm_b_sq_div_le_mul_quadForm_of_mulVec_eq {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 C.b‖ ^ 2 / a ≤ a' / a * quadForm C.A xs := by
  have h := C.norm_mulVec_sq_le_mul_quadForm ha hs xs
  rw [hx] at h
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h ha.le

private theorem acc_norm_sq_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (v : Fin n → ℝ) : ‖WithLp.toLp 2 v‖ ^ 2 ≤ quadForm C.A v / a := by
  rw [le_div_iff₀ ha, mul_comm]
  exact (C.mul_norm_sq_le_quadForm hs v)

/-- **The smallness of step $j \le k$ under (H)**: $j\varepsilon\kappa$, $j^2\varepsilon\kappa$,
$j^2\varepsilon\kappa^2 \le 10^{-5}$ (`NLAlib.CGRun.le_of_cube_mul_ε_mul_sq_le`). -/
theorem le_of_cube_mul_ε_mul_sq_le_of_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j ≤ k) :
    (j : ℝ) * C.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧ (j : ℝ) ^ 2 * C.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧
      (j : ℝ) ^ 2 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
  obtain ⟨-, hκ, -, -, hkεκ, hk2εκ, hk2εκ2⟩ := C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have hjr : (j : ℝ) ≤ k := by exact_mod_cast hj
  have hj2 : (j : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hjr 2
  have hT0 : 0 ≤ C.ε * (a' / a) := by positivity
  have hT1 : 0 ≤ C.ε * (a' / a) ^ 2 := by positivity
  refine ⟨le_trans ?_ hkεκ, le_trans ?_ hk2εκ, le_trans ?_ hk2εκ2⟩
  · have := mul_le_mul_of_nonneg_right hjr hT0
    linarith
  · have := mul_le_mul_of_nonneg_right hj2 hT0
    linarith
  · have := mul_le_mul_of_nonneg_right hj2 hT1
    linarith

/-- The crude a priori bounds at step $j$ used by the induction: from $E_j^2 \le
2\|\mathbf{b}\|^2/a$ and $\|\mathbf{g}_j\| \le 12j\varepsilon\kappa\|\mathbf{b}\|$,
$\|\mathbf{x}_\star - \mathbf{x}_j\| \le 2\|\mathbf{b}\|/a$, $\|\mathbf{x}_j\| \le
3\|\mathbf{b}\|/a$ and $\rho_j \le 3\kappa\|\mathbf{b}\|$. -/
private theorem acc_step_facts {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k)
    (hG : ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ ≤
      12 * j * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖)
    (hQ : quadForm C.A (xs - C.x j) ≤ 2 * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)) :
    ‖WithLp.toLp 2 (xs - C.x j)‖ ≤ 2 * ‖WithLp.toLp 2 C.b‖ / a ∧
      ‖WithLp.toLp 2 (C.x j)‖ ≤ 3 * ‖WithLp.toLp 2 C.b‖ / a ∧
      C.ρ j ≤ 3 * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by
  obtain ⟨haa', hκ, hspec, -, -, -, -⟩ := C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have hjε : (j : ℝ) * C.ε ≤ 1 / 100 := C.mul_ε_le' hj
  set κ := a' / a with hκdef
  set B := ‖WithLp.toLp 2 C.b‖ with hB
  have hB0 : 0 ≤ B := norm_nonneg _
  have ha'κ : a' = κ * a := by rw [hκdef]; field_simp
  have hxs := C.norm_le_norm_b_div_of_mulVec_eq ha hs hx
  have he : ‖WithLp.toLp 2 (xs - C.x j)‖ ≤ 2 * B / a := by
    have h1 := C.acc_norm_sq_le ha hs (xs - C.x j)
    have h2 : ‖WithLp.toLp 2 (xs - C.x j)‖ ^ 2 ≤ (2 * B / a) ^ 2 := by
      refine h1.trans ?_
      rw [div_le_iff₀ ha]
      have : (2 * B / a) ^ 2 * a = 4 * (B ^ 2 / a) := by field_simp; ring
      rw [this]
      have : 0 ≤ B ^ 2 / a := by positivity
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
  refine ⟨he, ?_, ?_⟩
  · have h := norm_sub_le (WithLp.toLp 2 xs) (WithLp.toLp 2 (xs - C.x j))
    rw [← WithLp.toLp_sub, sub_sub_cancel] at h
    have : 3 * B / a = B / a + 2 * B / a := by ring
    linarith
  · have hAe : ‖WithLp.toLp 2 (C.A *ᵥ (xs - C.x j))‖ ≤ a' * (2 * B / a) :=
      (norm_toLp_mulVec_le _ _).trans (mul_le_mul hspec he (norm_nonneg _) (by linarith))
    have hid : C.r j = C.A *ᵥ (xs - C.x j) - (C.b - C.A *ᵥ C.x j - C.r j) := by
      rw [Matrix.mulVec_sub, hx]
      abel
    have h := norm_sub_le (WithLp.toLp 2 (C.A *ᵥ (xs - C.x j)))
      (WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j))
    rw [← WithLp.toLp_sub, ← hid] at h
    have h2 : a' * (2 * B / a) = 2 * κ * B := by rw [ha'κ]; field_simp
    have hκB : 0 ≤ κ * B := by positivity
    have h3 : 12 * (j : ℝ) * C.ε * κ * B ≤ 12 / 100 * κ * B := by
      have := mul_le_mul_of_nonneg_right hjε hκB
      linarith
    change ‖WithLp.toLp 2 (C.r j)‖ ≤ _
    linarith

/-- The gap step of the induction. -/
private theorem acc_gap_step {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k)
    (hG : ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ ≤
      12 * j * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖)
    (hQ : quadForm C.A (xs - C.x j) ≤ 2 * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x (j + 1) - C.r (j + 1))‖ ≤
      12 * ((j + 1 : ℕ) : ℝ) * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by
  obtain ⟨haa', hκ, hspec, -, -, -, -⟩ := C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall
  obtain ⟨-, hxj, hρ⟩ := C.acc_step_facts ha hs hsmall hx hj.le hG hQ
  have hε0 := C.ε_nonneg
  have hγp := C.γ_mul_norm_p_le ha hs hsmall hj
  set κ := a' / a with hκdef
  set B := ‖WithLp.toLp 2 C.b‖ with hB
  have hB0 : 0 ≤ B := norm_nonneg _
  have ha'κ : a' = κ * a := by rw [hκdef]; field_simp
  have h := C.norm_sub_mulVec_x_sub_r_succ_le hj
  have h0 : ‖WithLp.toLp 2 (C.x j)‖ + 4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ≤ 9 * B / a := by
    have : 9 * B / a = 3 * B / a + 4 * (3 / 2 * B / a) := by ring
    have : 4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ = 4 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) := by
      ring
    linarith
  have h1 : specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ + 4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) ≤
      a' * (9 * B / a) :=
    mul_le_mul hspec h0 (by have := C.γ_pos hj; positivity) (by linarith)
  have h2 : a' * (9 * B / a) = 9 * κ * B := by rw [ha'κ]; field_simp
  have h3 : C.ε * (specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ +
      4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j) ≤ C.ε * (12 * κ * B) := by
    refine mul_le_mul_of_nonneg_left ?_ hε0
    linarith
  push_cast
  linarith

/-- The error step of the induction:
$E_{j+1}^2 \le E_j^2 - 0.99\gamma_j\rho_j^2 + (36j + 19)\varepsilon\kappa\|\mathbf{b}\|^2/a$. -/
private theorem acc_err_step {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k)
    (hG : ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ ≤
      12 * j * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖)
    (hQ : quadForm C.A (xs - C.x j) ≤ 2 * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)) :
    quadForm C.A (xs - C.x (j + 1)) ≤ quadForm C.A (xs - C.x j) -
      99 / 100 * (C.γ j * C.ρ j ^ 2) +
        (36 * j + 19) * (C.ε * (a' / a)) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  obtain ⟨haa', hκ, -, -, -, -, -⟩ := C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall
  obtain ⟨hjT, -, -⟩ := C.le_of_cube_mul_ε_mul_sq_le_of_le ha hs hsmall hj.le
  obtain ⟨-, hxj, -⟩ := C.acc_step_facts ha hs hsmall hx hj.le hG hQ
  obtain ⟨hX0, hstep⟩ := C.quadForm_sub_x_succ_le_aux ha hs hsmall hx hj
  have hε0 := C.ε_nonneg
  have hε1 := C.ε_le
  have hγ := C.γ_pos hj
  have hγp := C.γ_mul_norm_p_le ha hs hsmall hj
  have hγρ : 0 ≤ C.γ j * C.ρ j ^ 2 := by positivity
  set κ := a' / a with hκdef
  set B := ‖WithLp.toLp 2 C.b‖ with hB
  set u := B ^ 2 / a with hu
  have hB0 : 0 ≤ B := norm_nonneg _
  have hu0 : 0 ≤ u := by positivity
  have hT0 : 0 ≤ C.ε * κ := by positivity
  have ha'κ : a' = κ * a := by rw [hκdef]; field_simp
  have ha' : 0 ≤ a' := by linarith
  set G := ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ with hGdef
  set Qj := quadForm C.A (xs - C.x j) with hQj
  set X := Qj - 99 / 100 * (C.γ j * C.ρ j ^ 2) +
    2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * G with hX
  have hX1 : X ≤ Qj - 99 / 100 * (C.γ j * C.ρ j ^ 2) + 36 * j * (C.ε * κ) * u := by
    have h1 : 2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * G ≤
        2 * (3 / 2 * B / a) * (12 * j * C.ε * κ * B) :=
      mul_le_mul (by linarith) hG (norm_nonneg _) (by positivity)
    have h2 : 2 * (3 / 2 * B / a) * (12 * j * C.ε * κ * B) = 36 * j * (C.ε * κ) * u := by
      rw [hu]
      ring
    linarith
  have hX4 : X ≤ 4 * u := by
    have : 36 * (j : ℝ) * (C.ε * κ) * u ≤ 36 / 10 ^ 5 * u := by
      have := mul_le_mul_of_nonneg_right hjT hu0
      linarith
    linarith
  set t := Real.sqrt a' * ‖WithLp.toLp 2 (C.ex j)‖ with ht
  have hex : ‖WithLp.toLp 2 (C.ex j)‖ ≤ C.ε * (9 / 2 * B / a) := by
    refine (C.norm_ex_le j hj).trans (mul_le_mul_of_nonneg_left ?_ hε0)
    rw [abs_of_pos hγ]
    have : 9 / 2 * B / a = 3 * B / a + 3 / 2 * B / a := by ring
    linarith
  have ht0 : 0 ≤ t := by positivity
  have ht2 : t ^ 2 ≤ 81 / 4 * C.ε ^ 2 * κ * u := by
    rw [ht, mul_pow, Real.sq_sqrt ha']
    have h1 : ‖WithLp.toLp 2 (C.ex j)‖ ^ 2 ≤ (C.ε * (9 / 2 * B / a)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hex 2
    have h2 : a' * (C.ε * (9 / 2 * B / a)) ^ 2 = 81 / 4 * C.ε ^ 2 * κ * u := by
      rw [hu, ha'κ]
      field_simp
      ring
    calc a' * ‖WithLp.toLp 2 (C.ex j)‖ ^ 2 ≤ a' * (C.ε * (9 / 2 * B / a)) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 ha'
      _ = _ := h2
  have hXt : Real.sqrt X * t ≤ 9 * (C.ε * κ) * u := by
    have h1 : (Real.sqrt X * t) ^ 2 ≤ (9 * (C.ε * κ) * u) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hX0]
      have h2 : X * t ^ 2 ≤ 4 * u * (81 / 4 * C.ε ^ 2 * κ * u) :=
        mul_le_mul hX4 ht2 (sq_nonneg _) (by positivity)
      have h3 : 4 * u * (81 / 4 * C.ε ^ 2 * κ * u) ≤ (9 * (C.ε * κ) * u) ^ 2 := by
        have e1 : 4 * u * (81 / 4 * C.ε ^ 2 * κ * u) = 81 * C.ε ^ 2 * u ^ 2 * κ := by ring
        have e2 : (9 * (C.ε * κ) * u) ^ 2 = 81 * C.ε ^ 2 * u ^ 2 * κ ^ 2 := by ring
        rw [e1, e2]
        have : κ ≤ κ ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left this (by positivity)
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
  have ht2' : t ^ 2 ≤ 1 / 4 * (C.ε * κ) * u := by
    have e : 81 / 4 * C.ε ^ 2 * κ * u = 81 / 4 * C.ε * (C.ε * κ * u) := by ring
    have := mul_le_mul_of_nonneg_right (by linarith : 81 / 4 * C.ε ≤ 1 / 4)
      (by positivity : 0 ≤ C.ε * κ * u)
    have e2 : 1 / 4 * (C.ε * κ * u) = 1 / 4 * (C.ε * κ) * u := by ring
    linarith
  have e : (Real.sqrt X + t) ^ 2 = X + 2 * (Real.sqrt X * t) + t ^ 2 := by
    rw [add_sq, Real.sq_sqrt hX0]
    ring
  rw [e] at hstep
  have e2 : (36 * (j : ℝ) + 19) * (C.ε * κ) * u =
      36 * j * (C.ε * κ) * u + 19 * (C.ε * κ) * u := by ring
  have : 0 ≤ (C.ε * κ) * u := by positivity
  linarith

/-- The joint induction on the gap and the computed run's error (G4). -/
private theorem gapErrorInduction {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ ≤
        12 * j * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ ∧
      quadForm C.A (xs - C.x j) + 99 / 100 * ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2 ≤
        quadForm C.A xs + 25 * j ^ 2 * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  have hQ0 := C.quadForm_le_norm_b_sq_div_of_mulVec_eq ha hs hx
  have hε0 := C.ε_nonneg
  induction j with
  | zero =>
    rw [C.x_zero, C.r_zero, Matrix.mulVec_zero, sub_zero, sub_self, WithLp.toLp_zero, norm_zero,
      sub_zero, Finset.sum_range_zero]
    push_cast
    constructor <;> linarith
  | succ j ih =>
    have hjk : j < k := by omega
    obtain ⟨hG, hQ⟩ := ih hjk.le
    obtain ⟨hjT, hj2T, -⟩ := C.le_of_cube_mul_ε_mul_sq_le_of_le ha hs hsmall hjk.le
    set u := ‖WithLp.toLp 2 C.b‖ ^ 2 / a with hu
    have hu0 : 0 ≤ u := by positivity
    have hS0 : 0 ≤ ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2 := Finset.sum_nonneg fun i hi =>
      mul_nonneg (C.γ_pos (by have := Finset.mem_range.mp hi; omega)).le (sq_nonneg _)
    have hQ2 : quadForm C.A (xs - C.x j) ≤ 2 * u := by
      have : 25 * (j : ℝ) ^ 2 * C.ε * (a' / a) * u ≤ 25 / 10 ^ 5 * u := by
        have := mul_le_mul_of_nonneg_right hj2T hu0
        linarith
      linarith
    refine ⟨C.acc_gap_step ha hs hsmall hx hjk hG hQ2, ?_⟩
    have h := C.acc_err_step ha hs hsmall hx hjk hG hQ2
    rw [Finset.sum_range_succ]
    have hT : 0 ≤ C.ε * (a' / a) * u := by
      have := (C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall).2.1
      have : 0 ≤ a' / a := by linarith
      positivity
    have e : 25 * (((j + 1 : ℕ) : ℝ)) ^ 2 * C.ε * (a' / a) * u =
        25 * (j : ℝ) ^ 2 * C.ε * (a' / a) * u + (50 * j + 25) * (C.ε * (a' / a) * u) := by
      push_cast
      ring
    have e2 : (36 * (j : ℝ) + 19) * (C.ε * (a' / a)) * u =
        (36 * j + 19) * (C.ε * (a' / a) * u) := by ring
    have hjj : (36 * (j : ℝ) + 19) * (C.ε * (a' / a) * u) ≤
        (50 * j + 25) * (C.ε * (a' / a) * u) :=
      mul_le_mul_of_nonneg_right (by have : (0 : ℝ) ≤ j := j.cast_nonneg; linarith) hT
    rw [e]
    linarith

/-- **The residual gap, a priori, in $\|\mathbf{b}\|$**: under (H), for $j \le k$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_j - \mathbf{r}_j\| \le 12\,j\,\varepsilon\,\kappa\,
\|\mathbf{b}\| .$$
No solution is needed in the statement. The research note has $9$.
Proof: the private induction `gapErrorInduction` of this file. Difficulty: moderate. -/
theorem norm_sub_mulVec_x_sub_r_le_norm_b {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ ≤
      12 * j * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by
  have hherm := C.isHermitian_A
  have hPD : C.A.PosDef := hherm.posDef_iff_eigenvalue_pos.mpr fun i hi =>
    ha.trans_le (hherm.spectrum_subset_iff.mp hs i hi).1
  have hx : C.A *ᵥ (C.A⁻¹ *ᵥ C.b) = C.b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      hPD.isUnit), Matrix.one_mulVec]
  exact (C.gapErrorInduction ha hs hsmall hx hj).1

/-- **The computed estimator bounds the computed run's error decrease (one-sided ER3)**: under
(H), for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $j \le k$,
$$\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 \le \|\mathbf{x}_\star\|_{\mathbf{A}}^2 -
0.99\sum_{i<j}\gamma_i\|\mathbf{r}_i\|^2 + 25\,j^2\varepsilon\kappa\,\frac{\|\mathbf{b}\|^2}{a}
\,.$$
The exact relation, for the model, is `NLAlib.CGRun.quadForm_backwardH_sub_cgIterate_eq`; this
is the computed run's own error. The research note has $0.999$ and $30$.
Proof: the private induction `gapErrorInduction` of this file. Difficulty: moderate. -/
theorem quadForm_sub_x_le_sub_sum {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    quadForm C.A (xs - C.x j) ≤ quadForm C.A xs -
      99 / 100 * ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2 +
        25 * j ^ 2 * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  have h := (C.gapErrorInduction ha hs hsmall hx hj).2
  linarith

/-- **The computed run's $\mathbf{A}$-norm error, a priori**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $j \le k$,
$\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 \le 1.001\,\|\mathbf{x}_\star\|_{\mathbf{A}}^2$.
Proof: `NLAlib.CGRun.quadForm_sub_x_le_sub_sum` and
$\|\mathbf{b}\|^2/a \le \kappa\|\mathbf{x}_\star\|_{\mathbf{A}}^2$ (from
$\|\mathbf{A}\mathbf{x}_\star\|^2 \le a'\|\mathbf{x}_\star\|_{\mathbf{A}}^2$), $25j^2\varepsilon
\kappa^2 \le 2.5 \cdot 10^{-4}$. Difficulty: easy. -/
theorem quadForm_sub_x_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    quadForm C.A (xs - C.x j) ≤ (1 + 1 / 1000) * quadForm C.A xs := by
  have h := (C.gapErrorInduction ha hs hsmall hx hj).2
  obtain ⟨-, hκ, -, -, -, -, -⟩ := C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall
  obtain ⟨-, -, hj2⟩ := C.le_of_cube_mul_ε_mul_sq_le_of_le ha hs hsmall hj
  have hge := C.norm_b_sq_div_le_mul_quadForm_of_mulVec_eq ha hs hx
  have hε0 := C.ε_nonneg
  have hQ0 : 0 ≤ quadForm C.A xs := le_trans (by positivity) (C.mul_norm_sq_le_quadForm hs xs)
  have hS0 : 0 ≤ ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2 := Finset.sum_nonneg fun i hi =>
    mul_nonneg (C.γ_pos (by have := Finset.mem_range.mp hi; omega)).le (sq_nonneg _)
  have h1 : 25 * (j : ℝ) ^ 2 * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) ≤
      25 * (j : ℝ) ^ 2 * C.ε * (a' / a) * (a' / a * quadForm C.A xs) :=
    mul_le_mul_of_nonneg_left hge (by positivity)
  have h2 : 25 * (j : ℝ) ^ 2 * C.ε * (a' / a) * (a' / a * quadForm C.A xs) =
      25 * ((j : ℝ) ^ 2 * C.ε * (a' / a) ^ 2) * quadForm C.A xs := by ring
  have h3 : 25 * ((j : ℝ) ^ 2 * C.ε * (a' / a) ^ 2) * quadForm C.A xs ≤
      25 * (1 / 10 ^ 5) * quadForm C.A xs := by gcongr
  linarith

/-- **The computed iterates, a priori**: under (H), for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$
and $j \le k$,
$$\|\mathbf{x}_j\| \le 1.001\Bigl(\|\mathbf{x}_\star\| +
\frac{\|\mathbf{x}_\star\|_{\mathbf{A}}}{\sqrt{a}}\Bigr) ,$$
the exact-arithmetic bound on $\max_j\|\mathbf{x}_j\|$ through the $\mathbf{A}$-norm.
[MeurantStrakos2006, §5.4] assert $\|\mathbf{x}_j\| \le 2\|\mathbf{x}_\star\|$ "to within a
small error" for finite-precision CG without proof; this is $\sqrt{\kappa}$ weaker and proved.
Proof: $\|\mathbf{x}_j\| \le \|\mathbf{x}_\star\| + \|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}
/\sqrt{a}$ and `NLAlib.CGRun.quadForm_sub_x_le`. Difficulty: easy. -/
theorem norm_x_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (C.x j)‖ ≤
      (1 + 1 / 1000) * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  have hQ := C.quadForm_sub_x_le ha hs hsmall hx hj
  have hQ0 : 0 ≤ quadForm C.A xs := le_trans (by positivity) (C.mul_norm_sq_le_quadForm hs xs)
  have he2 := C.acc_norm_sq_le ha hs (xs - C.x j)
  set M := Real.sqrt (quadForm C.A xs) / Real.sqrt a
  have hM0 : 0 ≤ M := by positivity
  have hM2 : M ^ 2 = quadForm C.A xs / a := by
    rw [div_pow, Real.sq_sqrt hQ0, Real.sq_sqrt ha.le]
  have he : ‖WithLp.toLp 2 (xs - C.x j)‖ ≤ (1 + 1 / 1000) * M := by
    have h : ‖WithLp.toLp 2 (xs - C.x j)‖ ^ 2 ≤ ((1 + 1 / 1000) * M) ^ 2 := by
      rw [mul_pow, hM2]
      refine he2.trans ?_
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ ha.le
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
  have h := norm_sub_le (WithLp.toLp 2 xs) (WithLp.toLp 2 (xs - C.x j))
  rw [← WithLp.toLp_sub, sub_sub_cancel] at h
  have := norm_nonneg (WithLp.toLp 2 xs)
  nlinarith

/-- The error of the computed iterate, a priori:
$\|\mathbf{x}_\star - \mathbf{x}_j\| \le 1.001\|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$. -/
private theorem acc_norm_sub_x_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (xs - C.x j)‖ ≤
      (1 + 1 / 1000) * (Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  have hQ := C.quadForm_sub_x_le ha hs hsmall hx hj
  have hQ0 : 0 ≤ quadForm C.A xs := le_trans (by positivity) (C.mul_norm_sq_le_quadForm hs xs)
  have he2 := C.acc_norm_sq_le ha hs (xs - C.x j)
  have hM2 : (Real.sqrt (quadForm C.A xs) / Real.sqrt a) ^ 2 = quadForm C.A xs / a := by
    rw [div_pow, Real.sq_sqrt hQ0, Real.sq_sqrt ha.le]
  have h : ‖WithLp.toLp 2 (xs - C.x j)‖ ^ 2 ≤
      ((1 + 1 / 1000) * (Real.sqrt (quadForm C.A xs) / Real.sqrt a)) ^ 2 := by
    rw [mul_pow, hM2]
    refine he2.trans ?_
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ ha.le
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- $a\|\mathbf{v}\| \le \|\mathbf{A}\mathbf{v}\|$. -/
private theorem acc_mul_norm_le {a a' : ℝ} (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (v : Fin n → ℝ) : a * ‖WithLp.toLp 2 v‖ ≤ ‖WithLp.toLp 2 (C.A *ᵥ v)‖ := by
  have h1 := (C.mul_norm_sq_le_quadForm hs v)
  rw [C.quadForm_eq_dotProduct_mulVec] at h1
  have h2 := (le_abs_self _).trans (EuclideanSpace.abs_dotProduct_le_norm v (C.A *ᵥ v))
  rcases (norm_nonneg (WithLp.toLp 2 v)).lt_or_eq with hpos | hzero
  · exact le_of_mul_le_mul_left (by nlinarith) hpos
  · rw [← hzero, mul_zero]
    exact norm_nonneg _

/-- $\|\mathbf{b}\| \le a'\|\mathbf{x}_\star\|$. -/
private theorem acc_norm_b_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) : ‖WithLp.toLp 2 C.b‖ ≤ a' * ‖WithLp.toLp 2 xs‖ := by
  rw [← hx]
  exact (norm_toLp_mulVec_le _ _).trans
    (mul_le_mul_of_nonneg_right (C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall).2.2.1 (norm_nonneg _))

/-! ### The residual gap -/

/-- **The residual gap, a priori**: under (H), for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
with $M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k - \mathbf{r}_k\| \le 11\,k\,\varepsilon\,a'M .$$
[Greenbaum1997SIMAX]; [StrakosTichy2002, (7.16)], there with $\|\mathbf{x}_\star\| +
\max_j\|\mathbf{x}_j\|$ (a posteriori) and $+O(\varepsilon^2)$; here
$\max_j\|\mathbf{x}_j\| \le 1.001M$ is proved (`NLAlib.CGRun.norm_x_le`).
Proof: `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le` with $\|\mathbf{x}_j\| \le 1.001M$,
$\gamma_j\|\mathbf{p}_j\| \le 1.02(\|\mathbf{x}_j\| + \|\mathbf{x}_{j+1}\|)$ (the iterate
update), $\rho_j \le \|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_j)\| + \|\mathbf{g}_j\| \le
1.002a'M$. Difficulty: easy. -/
theorem norm_sub_mulVec_x_sub_r_le_energy {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k - C.r k)‖ ≤
      11 * k * C.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  obtain ⟨haa', hκ, hspec, hε5, hkεκ, -, -⟩ := C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have hε1 := C.ε_le
  set M := ‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a with hM
  have hxs0 := norm_nonneg (WithLp.toLp 2 xs)
  have hM' : Real.sqrt (quadForm C.A xs) / Real.sqrt a ≤ M := by linarith
  have hxsM : ‖WithLp.toLp 2 xs‖ ≤ M := by
    have : 0 ≤ Real.sqrt (quadForm C.A xs) / Real.sqrt a := by positivity
    linarith
  have hM0 : 0 ≤ M := by positivity
  have ha' : 0 ≤ a' := by linarith
  have hB := C.acc_norm_b_le ha hs hsmall hx
  have hterm : ∀ j < k, specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ +
      4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j ≤ 11 * (a' * M) := fun j hj => by
    have hxj := C.norm_x_le ha hs hsmall hx hj.le
    have hxj1 := C.norm_x_le ha hs hsmall hx (j := j + 1) hj
    have hγ := C.γ_pos hj
    -- the step through the iterate update
    have hγp : C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ≤ 201 / 100 * M := by
      have hid : C.γ j • C.p j = C.x (j + 1) - C.x j - C.ex j := by
        rw [C.x_succ j hj]
        abel
      have h1 : C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ≤ ‖WithLp.toLp 2 (C.x (j + 1))‖ +
          ‖WithLp.toLp 2 (C.x j)‖ + ‖WithLp.toLp 2 (C.ex j)‖ := by
        have := norm_sub_le (WithLp.toLp 2 (C.x (j + 1) - C.x j)) (WithLp.toLp 2 (C.ex j))
        have h2 := norm_sub_le (WithLp.toLp 2 (C.x (j + 1))) (WithLp.toLp 2 (C.x j))
        rw [← WithLp.toLp_sub, ← hid, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
          abs_of_pos hγ] at this
        rw [← WithLp.toLp_sub] at h2
        linarith
      have h3 := C.norm_ex_le j hj
      rw [abs_of_pos hγ] at h3
      have h4 : C.ε * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) ≤ 1 / 10 ^ 5 *
          (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) :=
        mul_le_mul_of_nonneg_right hε5 (by positivity)
      have h5 : C.ε * ‖WithLp.toLp 2 (C.x j)‖ ≤ 1 / 10 ^ 5 * ((1 + 1 / 1000) * M) :=
        mul_le_mul hε5 hxj (norm_nonneg _) (by norm_num)
      nlinarith
    -- the residual through the true residual and the gap
    have hρ : C.ρ j ≤ 1002 / 1000 * (a' * M) := by
      have he := C.acc_norm_sub_x_le ha hs hsmall hx hj.le
      have hG := C.norm_sub_mulVec_x_sub_r_le_norm_b ha hs hsmall hj.le
      have hid : C.r j = C.A *ᵥ (xs - C.x j) - (C.b - C.A *ᵥ C.x j - C.r j) := by
        rw [Matrix.mulVec_sub, hx]
        abel
      have h := norm_sub_le (WithLp.toLp 2 (C.A *ᵥ (xs - C.x j)))
        (WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j))
      rw [← WithLp.toLp_sub, ← hid] at h
      have hAe : ‖WithLp.toLp 2 (C.A *ᵥ (xs - C.x j))‖ ≤ a' * ((1 + 1 / 1000) * M) :=
        (norm_toLp_mulVec_le _ _).trans (mul_le_mul hspec (he.trans (by nlinarith))
          (norm_nonneg _) ha')
      have hjT : (j : ℝ) * C.ε * (a' / a) ≤ 1 / 10 ^ 5 :=
        (C.le_of_cube_mul_ε_mul_sq_le_of_le ha hs hsmall hj.le).1
      have hG' : 12 * (j : ℝ) * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ ≤
          12 * (1 / 10 ^ 5) * (a' * M) := by
        have : 12 * (j : ℝ) * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ =
            12 * ((j : ℝ) * C.ε * (a' / a)) * ‖WithLp.toLp 2 C.b‖ := by ring
        rw [this]
        exact mul_le_mul (by linarith) (hB.trans (mul_le_mul_of_nonneg_left hxsM ha'))
          (norm_nonneg _) (by norm_num)
      change ‖WithLp.toLp 2 (C.r j)‖ ≤ _
      nlinarith
    have h1 : ‖WithLp.toLp 2 (C.x j)‖ + 4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ≤ 905 / 100 * M := by
      nlinarith
    have h2 := mul_le_mul hspec h1 (by positivity) ha'
    nlinarith
  refine (C.norm_sub_mulVec_x_sub_r_le).trans ?_
  have hsum : ∑ j ∈ Finset.range k, (specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ +
      4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j) ≤ k * (11 * (a' * M)) := by
    have := Finset.sum_le_sum fun j (hj : j ∈ Finset.range k) => hterm j (Finset.mem_range.mp hj)
    simpa using this
  calc C.ε * ∑ j ∈ Finset.range k, (specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ +
        4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j) ≤ C.ε * (k * (11 * (a' * M))) :=
        mul_le_mul_of_nonneg_left hsum hε0
    _ = _ := by ring

/-- **The residual gap, a priori, in $\|\mathbf{x}_\star\|$**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k - \mathbf{r}_k\| \le 22\,k\,\varepsilon\sqrt{\kappa}\,
a'\|\mathbf{x}_\star\| .$$
$\sqrt{\kappa}$ worse than the folklore $O(k\varepsilon)a'\|\mathbf{x}_\star\|$, which rests on
a Euclidean monotonicity of the errors not known in finite precision. The research note has $20$.
Proof: `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_energy` and
$\|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a} \le \sqrt{\kappa}\|\mathbf{x}_\star\|$. Difficulty:
easy. -/
theorem norm_sub_mulVec_x_sub_r_le_norm_sol {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k - C.r k)‖ ≤
      22 * k * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ := by
  have h := C.norm_sub_mulVec_x_sub_r_le_energy ha hs hsmall hx
  obtain ⟨haa', hκ, -, -, -, -, -⟩ := C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have ha' : 0 ≤ a' := by linarith
  have hQ := (C.quadForm_le_mul_norm_sq hs xs)
  have hs1 : 1 ≤ Real.sqrt (a' / a) := by rw [Real.one_le_sqrt]; exact hκ
  have hxs0 := norm_nonneg (WithLp.toLp 2 xs)
  have hq : Real.sqrt (quadForm C.A xs) ≤ Real.sqrt a' * ‖WithLp.toLp 2 xs‖ := by
    rw [← Real.sqrt_sq hxs0, ← Real.sqrt_mul ha']
    exact Real.sqrt_le_sqrt hQ
  have h1 : Real.sqrt (quadForm C.A xs) / Real.sqrt a ≤
      Real.sqrt (a' / a) * ‖WithLp.toLp 2 xs‖ := by
    rw [Real.sqrt_div' a' ha.le, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hq (Real.sqrt_nonneg _)
  have h2 : ‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a ≤
      2 * Real.sqrt (a' / a) * ‖WithLp.toLp 2 xs‖ := by nlinarith
  refine h.trans ?_
  have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 11 * (k : ℝ) * C.ε * a')
  linarith

/-- **The true residual**: under (H), for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, with
$\kappa' = 2\kappa + 1$, $q = (\sqrt{\kappa'} - 1)/(\sqrt{\kappa'} + 1)$ and
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k\| \le 2\sqrt{\kappa'}\,q^k\|\mathbf{b}\| +
11\,k\,\varepsilon\,a'M .$$
Proof: $\mathbf{b} - \mathbf{A}\mathbf{x}_k = \mathbf{r}_k + \mathbf{g}_k$,
`NLAlib.CGRun.ρ_le_chebyshev`, `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_energy`. Difficulty:
easy. -/
theorem norm_sub_mulVec_x_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k)‖ ≤
      2 * Real.sqrt (2 * (a' / a) + 1) *
          ((Real.sqrt (2 * (a' / a) + 1) - 1) / (Real.sqrt (2 * (a' / a) + 1) + 1)) ^ k *
          ‖WithLp.toLp 2 C.b‖ +
        11 * k * C.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  have hid : C.b - C.A *ᵥ C.x k = C.r k + (C.b - C.A *ᵥ C.x k - C.r k) := by abel
  rw [hid, WithLp.toLp_add]
  refine (norm_add_le _ _).trans ?_
  have h1 := C.ρ_le_chebyshev ha hs hsmall le_rfl
  have h2 := C.norm_sub_mulVec_x_sub_r_le_energy ha hs hsmall hx
  change C.ρ k + _ ≤ _
  linarith

/-! ### Attainable accuracy -/

private theorem acc_norm_true_le (j : ℕ) : ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j)‖ ≤
    C.ρ j + ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ := by
  set g := C.b - C.A *ᵥ C.x j - C.r j with hg
  have hid : C.b - C.A *ᵥ C.x j = C.r j + g := by rw [hg]; abel
  rw [hid, WithLp.toLp_add]
  exact norm_add_le _ _

/-- **The computed residual at gap level**: under (H), for $\varepsilon, \delta > 0$ and
$k^\star(\kappa, \varepsilon, \delta) \le j \le k$ (`NLAlib.cgKStar`),
$\|\mathbf{r}_j\| \le 8\delta\varepsilon\|\mathbf{b}\|$. With $\delta = 1$ this is the level of
every a priori gap bound ($\|\mathbf{b}\| \le a'M$); with $\delta < 1$ it is the $\delta$-form
of "the computed residual is negligible", the only true one: exact arithmetic is an admissible
run with zero gap.
Proof: `NLAlib.CGRun.ρ_le_chebyshev` and `NLAlib.pow_le_of_cgKStar_le`. Difficulty: easy. -/
theorem ρ_le_of_cgKStar_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) (hε : 0 < C.ε) {δ : ℝ}
    (hδ : 0 < δ) {j : ℕ} (hkj : cgKStar (a' / a) C.ε δ ≤ j) (hj : j ≤ k) :
    C.ρ j ≤ 8 * δ * C.ε * ‖WithLp.toLp 2 C.b‖ := by
  obtain ⟨-, hκ, -, -, -, -, -⟩ := C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall
  have h1 := C.ρ_le_chebyshev ha hs hsmall hj
  have h2 := pow_le_of_cgKStar_le (by linarith : 0 ≤ a' / a) hε hδ hkj
  set s := Real.sqrt (2 * (a' / a) + 1) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hB := norm_nonneg (WithLp.toLp 2 C.b)
  have e : 2 * s * (4 * δ * C.ε / s) = 8 * δ * C.ε := by field_simp; ring
  calc C.ρ j ≤ _ := h1
    _ ≤ 2 * s * (4 * δ * C.ε / s) * ‖WithLp.toLp 2 C.b‖ := by gcongr
    _ = 8 * δ * C.ε * ‖WithLp.toLp 2 C.b‖ := by rw [e]

/-- **Past $k^\star(\delta)$ the true residual is the gap** up to $\delta$ times the gap's
level: under (H), for $\varepsilon, \delta > 0$ and $k^\star(\kappa, \varepsilon, \delta) \le j
\le k$,
$$\bigl\lvert\|\mathbf{b} - \mathbf{A}\mathbf{x}_j\| -
\|\mathbf{b} - \mathbf{A}\mathbf{x}_j - \mathbf{r}_j\|\bigr\rvert \le
8\delta\varepsilon\|\mathbf{b}\| .$$
Proof: the triangle inequality and `NLAlib.CGRun.ρ_le_of_cgKStar_le`. Difficulty: easy. -/
theorem abs_norm_sub_mulVec_x_sub_norm_gap_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hε : 0 < C.ε) {δ : ℝ} (hδ : 0 < δ) {j : ℕ} (hkj : cgKStar (a' / a) C.ε δ ≤ j)
    (hj : j ≤ k) :
    |‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j)‖ - ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖| ≤
      8 * δ * C.ε * ‖WithLp.toLp 2 C.b‖ := by
  have h := C.ρ_le_of_cgKStar_le ha hs hsmall hε hδ hkj hj
  set g := C.b - C.A *ᵥ C.x j - C.r j with hg
  have hid : C.b - C.A *ᵥ C.x j = C.r j + g := by rw [hg]; abel
  rw [hid, WithLp.toLp_add]
  have := abs_norm_sub_norm_le (WithLp.toLp 2 (C.r j) + WithLp.toLp 2 g) (WithLp.toLp 2 g)
  rw [add_sub_cancel_right] at this
  exact this.trans h

/-- **Attainable accuracy at a prescribed step**: under (H), for $\varepsilon > 0$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $k \ge k^\star(\kappa, \varepsilon, 1)$, with
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k\| \le (11k + 8)\,\varepsilon\,a'M .$$
The bound grows linearly in $k$: the term $\mathbf{A}\mathbf{e}^x_j$ of the gap does not decay
(as in [Greenbaum1997SIMAX]), so the best step is $k^\star$
(`NLAlib.CGRun.norm_sub_mulVec_x_cgKStar_le`).
Proof: `NLAlib.CGRun.ρ_le_of_cgKStar_le`, `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_energy` and
$\|\mathbf{b}\| \le a'\|\mathbf{x}_\star\|$. Difficulty: easy. -/
theorem norm_sub_mulVec_x_le_of_cgKStar_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hε : 0 < C.ε) {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) (hk : cgKStar (a' / a) C.ε 1 ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k)‖ ≤
      (11 * k + 8) * C.ε * a' *
        (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  have h1 := C.acc_norm_true_le k
  have h2 := C.ρ_le_of_cgKStar_le ha hs hsmall hε one_pos hk le_rfl
  have h3 := C.norm_sub_mulVec_x_sub_r_le_energy ha hs hsmall hx
  have hB := C.acc_norm_b_le ha hs hsmall hx
  have ha' : 0 ≤ a' := ha.le.trans (C.le_of_spectrum_subset_Icc hs)
  have hM : ‖WithLp.toLp 2 xs‖ ≤
      ‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a := by
    have : 0 ≤ Real.sqrt (quadForm C.A xs) / Real.sqrt a := by positivity
    linarith
  have h4 : 8 * 1 * C.ε * ‖WithLp.toLp 2 C.b‖ ≤
      8 * C.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
    have := mul_le_mul_of_nonneg_left (hB.trans (mul_le_mul_of_nonneg_left hM ha'))
      (by have := C.ε_nonneg; positivity : (0 : ℝ) ≤ 8 * C.ε)
    linarith
  have e : (11 * (k : ℝ) + 8) * C.ε * a' *
      (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) =
      11 * k * C.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) +
        8 * C.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
    ring
  rw [e]
  linarith

/-- **Attainable accuracy in $\|\mathbf{x}_\star\|$**: under (H), for $\varepsilon > 0$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $k \ge k^\star(\kappa, \varepsilon, 1)$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k\| \le (22k + 8)\,\varepsilon\sqrt{\kappa}\,a'
\|\mathbf{x}_\star\| .$$
Proof: `NLAlib.CGRun.ρ_le_of_cgKStar_le`, `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_norm_sol`.
Difficulty: easy. -/
theorem norm_sub_mulVec_x_le_norm_sol_of_cgKStar_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hε : 0 < C.ε) {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) (hk : cgKStar (a' / a) C.ε 1 ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k)‖ ≤
      (22 * k + 8) * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ := by
  obtain ⟨-, hκ, -, -, -, -, -⟩ := C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall
  have h1 := C.acc_norm_true_le k
  have h2 := C.ρ_le_of_cgKStar_le ha hs hsmall hε one_pos hk le_rfl
  have h3 := C.norm_sub_mulVec_x_sub_r_le_norm_sol ha hs hsmall hx
  have hB := C.acc_norm_b_le ha hs hsmall hx
  have ha' : 0 ≤ a' := ha.le.trans (C.le_of_spectrum_subset_Icc hs)
  have hs1 : 1 ≤ Real.sqrt (a' / a) := by rw [Real.one_le_sqrt]; exact hκ
  have h4 : 8 * 1 * C.ε * ‖WithLp.toLp 2 C.b‖ ≤
      8 * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ := by
    have h5 : a' * ‖WithLp.toLp 2 xs‖ ≤ Real.sqrt (a' / a) * (a' * ‖WithLp.toLp 2 xs‖) :=
      le_mul_of_one_le_left (by positivity) hs1
    have := mul_le_mul_of_nonneg_left (hB.trans h5)
      (by have := C.ε_nonneg; positivity : (0 : ℝ) ≤ 8 * C.ε)
    linarith
  have e : (22 * (k : ℝ) + 8) * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ =
      22 * k * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ +
        8 * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ := by ring
  rw [e]
  linarith

/-- **Attainable accuracy in $\|\mathbf{b}\|$**: under (H), for $\varepsilon > 0$ and
$k \ge k^\star(\kappa, \varepsilon, 1)$,
$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k\| \le (12k + 8)\,\varepsilon\,\kappa\,\|\mathbf{b}\|$.
The research note has $9k + 8$.
Proof: `NLAlib.CGRun.ρ_le_of_cgKStar_le`, `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_norm_b`.
Difficulty: easy. -/
theorem norm_sub_mulVec_x_le_norm_b_of_cgKStar_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hε : 0 < C.ε) (hk : cgKStar (a' / a) C.ε 1 ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k)‖ ≤ (12 * k + 8) * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by
  obtain ⟨-, hκ, -, -, -, -, -⟩ := C.le_of_cube_mul_ε_mul_sq_le ha hs hsmall
  have h1 := C.acc_norm_true_le k
  have h2 := C.ρ_le_of_cgKStar_le ha hs hsmall hε one_pos hk le_rfl
  have h3 := C.norm_sub_mulVec_x_sub_r_le_norm_b ha hs hsmall le_rfl
  have hB := norm_nonneg (WithLp.toLp 2 C.b)
  have h4 : 8 * 1 * C.ε * ‖WithLp.toLp 2 C.b‖ ≤ 8 * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by
    have h5 : C.ε * ‖WithLp.toLp 2 C.b‖ ≤ (a' / a) * (C.ε * ‖WithLp.toLp 2 C.b‖) :=
      le_mul_of_one_le_left (by have := C.ε_nonneg; positivity) hκ
    linarith
  have e : (12 * (k : ℝ) + 8) * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ =
      12 * k * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ +
        8 * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by ring
  rw [e]
  linarith

/-- **The forward error at a prescribed step**: under (H), for $\varepsilon > 0$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $k \ge k^\star(\kappa, \varepsilon, 1)$, with
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$\|\mathbf{x}_\star - \mathbf{x}_k\| \le (11k + 8)\,\varepsilon\,\kappa\,M$.
Proof: $\|\mathbf{x}_\star - \mathbf{x}_k\| \le \|\mathbf{b} - \mathbf{A}\mathbf{x}_k\|/a$ and
`NLAlib.CGRun.norm_sub_mulVec_x_le_of_cgKStar_le`. Difficulty: easy. -/
theorem norm_sub_x_le_of_cgKStar_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) (hε : 0 < C.ε) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) (hk : cgKStar (a' / a) C.ε 1 ≤ k) :
    ‖WithLp.toLp 2 (xs - C.x k)‖ ≤
      (11 * k + 8) * C.ε * (a' / a) *
        (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  have h := C.norm_sub_mulVec_x_le_of_cgKStar_le ha hs hsmall hε hx hk
  have h1 := C.acc_mul_norm_le hs (xs - C.x k)
  rw [Matrix.mulVec_sub, hx] at h1
  rw [← div_le_div_iff_of_pos_right ha] at h1
  rw [mul_div_cancel_left₀ _ ha.ne'] at h1
  refine h1.trans ?_
  rw [div_le_iff₀ ha]
  have e : (11 * (k : ℝ) + 8) * C.ε * (a' / a) *
      (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) * a =
      (11 * k + 8) * C.ε * a' *
        (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
    field_simp
  rw [e]
  exact h

/-- **Attainable accuracy, a priori**: for $\varepsilon > 0$, $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$, $k \ge k^\star = k^\star(\kappa, \varepsilon, 1)$ and (H) **at $k^\star$ only**,
$(k^\star)^3\varepsilon\kappa^2 \le 10^{-5}$, with $\kappa' = 2\kappa + 1$,
$\ell = \ln(\sqrt{\kappa'}/(4\varepsilon))$ and
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_{k^\star}\| \le
\Bigl(\frac{11}{2}(\sqrt{\kappa'} + 1)\,\ell + 19\Bigr)\varepsilon\,a'M ,$$
an attainable relative residual of order $\kappa\ln(1/\varepsilon)\,\varepsilon$ (one
$\sqrt{\kappa}$ from $M \le (1 + \sqrt{\kappa})\|\mathbf{x}_\star\|$, one from
$k^\star \propto \sqrt{\kappa}$). `NLAlib.cgKStar_cube_mul_le` gives the hypothesis at $k^\star$
from $\kappa^{7/2}\varepsilon\ell^3 \le 7 \cdot 10^{-7}$. No printed source; the research note has
$\tfrac{11}{2}\sqrt{\kappa'}\ell + 19$.
Proof: `NLAlib.CGRun.norm_sub_mulVec_x_le_of_cgKStar_le` on `C.take k⋆`
(`NLAlib.cgKStar_pos`) and $k^\star \le \tfrac12(\sqrt{\kappa'} + 1)\ell + 1$. Difficulty: easy. -/
theorem norm_sub_mulVec_x_cgKStar_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hε : 0 < C.ε) (hk : cgKStar (a' / a) C.ε 1 ≤ k)
    (hsmall : (cgKStar (a' / a) C.ε 1 : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x (cgKStar (a' / a) C.ε 1))‖ ≤
      (11 / 2 * (Real.sqrt (2 * (a' / a) + 1) + 1) *
          Real.log (Real.sqrt (2 * (a' / a) + 1) / (4 * 1 * C.ε)) + 19) * C.ε * a' *
        (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  have haa' := C.le_of_spectrum_subset_Icc hs
  have ha' : 0 ≤ a' := ha.le.trans haa'
  have hκ0 : 0 ≤ a' / a := div_nonneg ha' ha.le
  have hε1 := C.ε_le
  set K := cgKStar (a' / a) C.ε 1 with hKdef
  have hK0 : 0 < K := cgKStar_pos hκ0 hε hε1 one_pos le_rfl
  set M := ‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a with hM
  have h : ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x K)‖ ≤ (11 * K + 8) * C.ε * a' * M :=
    (C.take K hK0 hk).norm_sub_mulVec_x_le_of_cgKStar_le ha hs hsmall hε hx le_rfl
  set s := Real.sqrt (2 * (a' / a) + 1) with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef, Real.one_le_sqrt]; linarith
  set ℓ := Real.log (s / (4 * 1 * C.ε)) with hℓ
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; nlinarith)
  have hK : (K : ℝ) ≤ (s + 1) / 2 * ℓ + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (s + 1) / 2 * ℓ)).le
  have hM0 : 0 ≤ M := by positivity
  have hεaM : 0 ≤ C.ε * a' * M := by positivity
  refine h.trans ?_
  have e1 : (11 * (K : ℝ) + 8) * C.ε * a' * M = (11 * K + 8) * (C.ε * a' * M) := by ring
  have e2 : (11 / 2 * (s + 1) * ℓ + 19) * C.ε * a' * M =
      (11 / 2 * (s + 1) * ℓ + 19) * (C.ε * a' * M) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (by linarith) hεaM

end CGRun

end NLAlib
