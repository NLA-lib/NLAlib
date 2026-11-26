/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.BlockKrylovSum

/-!
# One run of block Krylov iteration with a Gaussian start block, Frobenius norm

Bounds for one truncated run of randomized block Krylov iteration,
$\llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_k$ (`NLAlib.rbki`), with a standard
Gaussian test matrix $\mathbf{X}$ of $\ell \ge 2k + 1$ columns, in the Frobenius norm, with no gap
in the spectrum and no factor of the dimension. The same Gaussian block is used for both
sketches in the
general two-block theorem, giving depth $O(\log(k/\varepsilon)/\sqrt{\varepsilon})$.

## Main results

* `integral_frobNorm_sub_truncatedSVD_rbki_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`:
  the explicit Frobenius error bound.
* `integral_schattenNorm_sub_mul_rangeProjector_rbki_rpow_le_one_add_mul_of_hasLaw_gaussianMatrix`:
  the two-sided Schatten bound for $1 \le p \le 2$.
* `exists_forall_integral_frobNorm_sub_truncatedSVD_rbki_sq_le_of_hasLaw_gaussianMatrix`:
  the asymptotic Frobenius form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

section Gaussian

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l m n : Type*} [Fintype l]
  [Fintype m] [Fintype n] [DecidableEq n] {X : Ω → Matrix n l ℝ}

/-! ### Depth $O(\log(k/\varepsilon)/\sqrt{\varepsilon})$ -/

/-- The three error terms of the single-run instance at `γ = ε/6` sum to at most `ε`. -/
private theorem frobenius_parameters {k j L q : ℕ} (hk : 0 < k) (hkj : k = j + 1)
    (hl : 2 * k + 1 ≤ L) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq : 1 + Real.sqrt 3 * Real.log (24 * k / ε) / (2 * Real.sqrt ε) ≤ q) :
    1 ≤ q ∧
      1 + 2 * k * (ε / 6) / ((j : ℝ) + 1) +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt (ε / 6)) *
          ((k : ℝ) / ((L : ℝ) - k - 1)) +
        4 * Real.exp (-3 * ((q : ℝ) - 1)) *
          (((k : ℝ) + j) / ((L : ℝ) - k - j - 1)) ≤ 1 + ε := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkr : (j : ℝ) + 1 = k := by exact_mod_cast hkj.symm
  have hlr : (2 : ℝ) * k + 1 ≤ L := by exact_mod_cast hl
  have harg : 1 < 24 * k / ε := (lt_div_iff₀ hε).mpr (by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith)
  have hlog : 0 < Real.log (24 * k / ε) := Real.log_pos harg
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have hq0 : 1 ≤ q := by
    have : (0 : ℝ) < Real.sqrt 3 * Real.log (24 * k / ε) / (2 * Real.sqrt ε) := by positivity
    exact_mod_cast (show (1 : ℝ) ≤ q by linarith)
  have hqn : (0 : ℝ) ≤ q - 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq0
    linarith
  have hid : Real.sqrt 2 * Real.sqrt (ε / 6) * Real.sqrt 3 = Real.sqrt ε := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * (ε / 6))]
    congr 1
    ring
  have hbase : Real.log (24 * k / ε) ≤
      2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt (ε / 6) := by
    apply (mul_le_mul_iff_right₀ hs3).mp
    have hm := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt ε)).mp
      (show Real.sqrt 3 * Real.log (24 * k / ε) / (2 * Real.sqrt ε) ≤ (q : ℝ) - 1 by linarith)
    calc Real.sqrt 3 * Real.log (24 * k / ε) ≤ ((q : ℝ) - 1) * (2 * Real.sqrt ε) := hm
      _ = Real.sqrt 3 * (2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt (ε / 6)) := by
        rw [← hid]
        ring
  have hscale : 2 * Real.sqrt 2 * Real.sqrt (ε / 6) ≤ 3 := by
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hse := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ε / 6)
    have hmul := mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (ε / 6))
    have hp : (Real.sqrt 2 * Real.sqrt (ε / 6)) ^ 2 = ε / 3 := by
      rw [mul_pow, hs2, hse]
      ring
    nlinarith [sq_nonneg (2 * Real.sqrt 2 * Real.sqrt (ε / 6) - 3)]
  have hexp : Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt (ε / 6)) ≤
      ε / (24 * k) := by
    calc _ ≤ Real.exp (-Real.log (24 * k / ε)) := Real.exp_le_exp.mpr (by linarith)
      _ = ε / (24 * k) := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have hexp2 : Real.exp (-3 * ((q : ℝ) - 1)) ≤ ε / (24 * k) :=
    (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hscale hqn])).trans hexp
  have hr1 : (k : ℝ) / ((L : ℝ) - k - 1) ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  have hr2 : ((k : ℝ) + j) / ((L : ℝ) - k - j - 1) ≤ 2 * k := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith
  have ht1 := mul_le_mul_of_nonneg_left hr1
    (show 0 ≤ 4 * k * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt (ε / 6)) by positivity)
  have ht2 := mul_le_mul_of_nonneg_left hr2
    (show 0 ≤ 4 * Real.exp (-3 * ((q : ℝ) - 1)) by positivity)
  have he1 := mul_le_mul_of_nonneg_left hexp (show (0 : ℝ) ≤ 4 * k by positivity)
  have he2 := mul_le_mul_of_nonneg_left hexp2 (show (0 : ℝ) ≤ 8 * k by positivity)
  have hcancel : (k : ℝ) * (ε / (24 * k)) = ε / 24 := by
    field_simp [ne_of_gt hk0]
  have hfirst : 2 * k * (ε / 6) / ((j : ℝ) + 1) = ε / 3 := by
    rw [hkr]
    field_simp [ne_of_gt hk0]
    norm_num
  constructor
  · exact hq0
  · rw [hfirst]
    nlinarith

/-- **A $(1 + \varepsilon)$ rank-$k$ approximation from one Gaussian block Krylov run, Frobenius
norm.** Let $\mathbf{A}$ be a real $m \times n$ matrix, $\mathbf{X}$ a standard Gaussian
$n \times \ell$ test matrix (independent standard normal entries), $k \ge 1$, $\ell \ge 2k + 1$
and $0 < \varepsilon \le 1$. If $q \ge 1 + c\log(Ck/\varepsilon)/\sqrt{\varepsilon}$, then
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_k
\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
Here $c = \sqrt{3}/2$ and $C = 24$.
[MuscoMusco2015, Theorem 11]; there with probability $99/100$, a block of $k$ columns, depth
$O(\log d/\sqrt{\varepsilon})$ and unspecified constants, here in expectation, for a block of at
least $2k + 1$ columns, with $\log(k/\varepsilon)$ in place of $\log d$ and explicit constants.

Note: the instance of
`NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le_of_hasLaw_gaussianMatrix` at
$\mathbf{X}_1 = \mathbf{X}_2 = \mathbf{X}$, $j = k - 1$ and $\gamma = \varepsilon/6$; its three
error terms are each at most $\varepsilon/3$. The run uses
$O(k\varepsilon^{-1/2}\log(k/\varepsilon))$ products with $\mathbf{A}$ or
$\mathbf{A}^{\mathsf{H}}$. Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_truncatedSVD_rbki_sq_le_of_hasLaw_gaussianMatrix`.
Result: rbki-frobenius-error -/
theorem integral_frobNorm_sub_truncatedSVD_rbki_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k q : ℕ} (hk : 0 < k)
    (hl : 2 * k + 1 ≤ Fintype.card l) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq : 1 + Real.sqrt 3 * Real.log (24 * k / ε) / (2 * Real.sqrt ε) ≤ q) :
    ∫ ω, frobNorm (A - truncatedSVD (rbki A (X ω) q) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  let j := k - 1
  have hkj : k = j + 1 := by dsimp [j]; omega
  have hparam := frobenius_parameters hk hkj hl hε hε1 hq
  have h := integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_range_le_of_hasLaw_gaussianMatrix
    A hX hX
    (k := k) (j := j) (by omega) (by omega) hparam.1 hparam.1
    (γ := ε / 6) (by positivity) (by linarith)
    ((measurable_blockKrylovMatrix (Aᴴ * A) q).comp_aemeasurable
      hX.aemeasurable)
    (fun _ => le_rfl) (fun _ => le_rfl)
  exact h.trans (mul_le_mul_of_nonneg_right hparam.2 (sq_nonneg _))


-- A declaration name cited in the docstring exceeds 100 characters.
set_option linter.style.longLine false in
/-- **A $(1 + \varepsilon)$ rank-$k$ approximation from one Gaussian block Krylov run, Schatten
norms with $1 \le p \le 2$.** Let $1 \le p \le 2$, let $\mathbf{A}$ be a real $m \times n$
matrix, $\mathbf{X}$ a standard Gaussian $n \times \ell$ test matrix (independent standard normal
entries), $k \ge 1$, $\ell \ge 2k + 1$ and $0 < \varepsilon \le 1$. Write
$\mathbf{B} = \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_k$ and
$\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}$ for the projector onto its row space. If
$q \ge 1 + c\log(Ck/\varepsilon)/\sqrt{\varepsilon}$, then
$$\mathbb{E}\|\mathbf{A} - \mathbf{A}\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}\|_{S_p}^p \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{S_p}^p\,.$$
Here $c = \sqrt{3}/2$ and $C = 24$.
[MuscoMusco2015, Theorem 11]; [BakshiClarksonWoodruff2022, Theorem 3.1]; there in the Frobenius
norm with a block of $k$ columns, and in Schatten norms for an algorithm that selects one of two
runs, each with constant probability and unspecified constants, here in expectation of the
$p$-th power, for one run with a block of at least $2k + 1$ columns and explicit constants.

Note: the output $\mathbf{A}\mathbf{P}_{\mathbf{B}^{\mathsf{H}}}$ has rank at most $k$; for
$p < 2$ the bound is for this two-sided output, not for $\mathbf{B}$. The instance of
`NLAlib.integral_schattenNorm_sub_mul_rangeProjector_rsvd_rpow_le_of_range_le_of_hasLaw_gaussianMatrix`
at $\mathbf{X}_1 = \mathbf{X}_2 = \mathbf{X}$, $j = k - 1$ and $\gamma = \varepsilon/6$.
Result: rbki-schatten-error -/
theorem
    integral_schattenNorm_sub_mul_rangeProjector_rbki_rpow_le_one_add_mul_of_hasLaw_gaussianMatrix
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) {k q : ℕ} (hk : 0 < k)
    (hl : 2 * k + 1 ≤ Fintype.card l) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq : 1 + Real.sqrt 3 * Real.log (24 * k / ε) / (2 * Real.sqrt ε) ≤ q) :
    ∫ ω, schattenNorm p (A - A * rangeProjector (truncatedSVD (rbki A (X ω) q) k)ᴴ) ^
        p.toReal ∂μ ≤
      (1 + ε) * schattenNorm p (A - truncatedSVD A k) ^ p.toReal := by
  let j := k - 1
  have hkj : k = j + 1 := by dsimp [j]; omega
  have hparam := frobenius_parameters hk hkj hl hε hε1 hq
  have h :=
    integral_schattenNorm_sub_mul_rangeProjector_rsvd_rpow_le_of_range_le_of_hasLaw_gaussianMatrix
    hp1 hp2 A hX hX
    (k := k) (j := j) (by omega) (by omega) hparam.1 hparam.1
    (γ := ε / 6) (by positivity) (by linarith)
    ((measurable_blockKrylovMatrix (Aᴴ * A) q).comp_aemeasurable
      hX.aemeasurable)
    (fun _ => le_rfl) (fun _ => le_rfl)
  exact h.trans (mul_le_mul_of_nonneg_right hparam.2 (by positivity))


end Gaussian

/-! ### Asymptotic forms -/

/-- **$O(\log(k/\varepsilon)/\sqrt{\varepsilon})$ depth suffices for a $(1 + \varepsilon)$
rank-$k$ approximation from one Gaussian block Krylov run in the Frobenius norm**: there are
absolute constants $C, \varepsilon_0 > 0$ such that for a real matrix $\mathbf{A}$, a standard
Gaussian $n \times \ell$ test matrix $\mathbf{X}$ (independent standard normal entries),
$k \ge 1$, $0 < \varepsilon \le \varepsilon_0$, a block $\ell \ge 2k + 1$ and a depth
$q \ge C\log(k/\varepsilon)/\sqrt{\varepsilon}$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\rrbracket_k
\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
With $\ell = O(k)$ the run uses $O(k\varepsilon^{-1/2}\log(k/\varepsilon))$ products with
$\mathbf{A}$ or $\mathbf{A}^{\mathsf{H}}$. The asymptotic form of
`NLAlib.integral_frobNorm_sub_truncatedSVD_rbki_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`.
[MuscoMusco2015, Theorem 11]; there with depth $O(\log d/\sqrt{\varepsilon})$, probability
$99/100$ and a block of $k$ columns; here in expectation.
Asymptotic:
NLAlib.integral_frobNorm_sub_truncatedSVD_rbki_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
Result: rbki-frobenius-error -/
theorem exists_forall_integral_frobNorm_sub_truncatedSVD_rbki_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [DecidableEq n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (k q : ℕ) (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → 0 < k → 0 < ε → ε ≤ ε₀ →
      2 * k + 1 ≤ Fintype.card l → C * (Real.log (k / ε) / Real.sqrt ε) ≤ q →
      ∫ ω, frobNorm (A - truncatedSVD (rbki A (X ω) q) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  refine ⟨100, Real.exp (-1), by norm_num, Real.exp_pos _, ?_⟩
  intro Ω m n l _ _ _ _ _ μ A X k q ε hX hk hε hε0 hl hq
  have hε1 : ε ≤ 1 := hε0.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hεexp : ε * Real.exp 1 ≤ 1 := by
    calc ε * Real.exp 1 ≤ Real.exp (-1) * Real.exp 1 :=
          mul_le_mul_of_nonneg_right hε0 (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; norm_num
  have harg : Real.exp 1 ≤ k / ε := (le_div_iff₀ hε).mpr (by nlinarith)
  have hL : 1 ≤ Real.log (k / ε) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) harg
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hs1 : Real.sqrt ε ≤ 1 := (Real.sqrt_le_one).mpr hε1
  have hs3 : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hlog : Real.log (24 * k / ε) ≤ 25 * Real.log (k / ε) := by
    rw [show 24 * (k : ℝ) / ε = 24 * (k / ε) by ring,
      Real.log_mul (by norm_num) (by positivity)]
    have h24 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 24)
    linarith
  apply integral_frobNorm_sub_truncatedSVD_rbki_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    A hX hk hl hε hε1
  have hlog0 : 0 ≤ Real.log (24 * k / ε) := Real.log_nonneg (by
    apply (one_le_div hε).mpr
    nlinarith)
  have hnum := mul_le_mul hs3 hlog hlog0 (by norm_num : (0 : ℝ) ≤ 2)
  have hdepth : 100 * Real.log (k / ε) ≤ (q : ℝ) * Real.sqrt ε := by
    apply (div_le_iff₀ hs).mp
    simpa only [mul_div_assoc] using hq
  have hdepth1 : 2 * Real.sqrt ε + Real.sqrt 3 * Real.log (24 * k / ε) ≤
      (q : ℝ) * (2 * Real.sqrt ε) := by nlinarith
  have heq : 1 + Real.sqrt 3 * Real.log (24 * k / ε) / (2 * Real.sqrt ε) =
      (2 * Real.sqrt ε + Real.sqrt 3 * Real.log (24 * k / ε)) /
        (2 * Real.sqrt ε) := by field_simp
  rw [heq]
  exact (div_le_iff₀ (by positivity)).mpr hdepth1


end NLAlib
