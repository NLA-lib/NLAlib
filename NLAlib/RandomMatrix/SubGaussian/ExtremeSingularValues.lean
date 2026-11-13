/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Deriv
public import NLAlib.ForMathlib.Data.Finset.Max
public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Norms.Net
public import NLAlib.Matrix.Spectral.SingularValues
public import NLAlib.Probability.Isotropic
public import NLAlib.Probability.SubExponential.Tail
public import NLAlib.Probability.SubGaussian.Square
public import NLAlib.Probability.SubGaussianVector.Basic

/-!
# Extreme singular values of matrices with independent sub-Gaussian rows

For a random $m \times n$ matrix $\mathbf{X}$ ($\lvert m \rvert$ rows, $\lvert n \rvert$ columns)
whose rows are independent, isotropic and sub-Gaussian with proxy $c$,
and <!-- value subgaussianRowsConstant -->$w = 24c(\sqrt{\lvert n \rvert} + t)$ (the constant is
`subgaussianRowsConstant`), for $t \ge 0$ and $w \le \sqrt{\lvert m \rvert}$: outside
probability $2 e^{-t^2}$,
$$(\sqrt{\lvert m \rvert} - w)^2 \mathbf{I} \preceq \mathbf{X}^{\mathsf{H}}\mathbf{X}
\preceq (\sqrt{\lvert m \rvert} + w)^2 \mathbf{I} \,,$$
hence $\sqrt{\lvert m \rvert} - w \le \sigma_{\min}(\mathbf{X})$ and
$\|\mathbf{X}\|_2 \le \sqrt{\lvert m \rvert} + w$. Also the fixed-vector bound: for a unit
$\mathbf{x}$, $\|\mathbf{X}\mathbf{x}\|^2 - \lvert m \rvert$ is sub-exponential with parameters
$32 c^2 \lvert m \rvert$, $4 c$.

**Naming.** The suffix `_of_isSubgaussianVector` stands for the three row hypotheses, always taken
together and in this order: `hind : iIndepFun (fun i ω => X ω i) μ` (independent rows),
`hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ` and
`hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ`. No $1 \le c$ hypothesis is stated: with rows and
columns present, isotropy and `HasSubgaussianMGF.integral_sq_le` give it.

A standard Gaussian matrix satisfies the hypotheses with $c = 1$, but there the bounds of
`NLAlib/RandomMatrix/Gaussian/ExtremeSingularValues.lean` are better in every regime
($\sqrt{\lvert m \rvert} \pm (\sqrt{\lvert n \rvert} + \sqrt{2} \, t)$ outside $2 e^{-t^2}$).

## Main definitions

* `NLAlib.subgaussianRowsConstant`: the constant $C_{\mathrm{SG}}$ of the bounds, of
  value <!-- value subgaussianRowsConstant -->$24$.

## Main results

* `NLAlib.hasSubexponentialMGF_norm_mulVec_sq_sub_of_isSubgaussianVector`: the fixed-vector bound.
* The two-sided Gram bound (in namespace `NLAlib`):
  `measureReal_not_smul_one_le_conjTranspose_mul_self_and_le_smul_one_le_of_isSubgaussianVector`.
* Its one-sided forms and the singular-value tails
  `NLAlib.measureReal_singularValues_le_le_of_isSubgaussianVector`,
  `NLAlib.measureReal_specNorm_ge_le_of_isSubgaussianVector`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal

namespace NLAlib

/-- The constant $C_{\mathrm{SG}}$ of the sub-Gaussian rows theorem: singular values
within <!-- value subgaussianRowsConstant -->
$\sqrt{\lvert m \rvert} \pm 24c(\sqrt{\lvert n \rvert} + t)$ outside probability $2 e^{-t^2}$.
[Vershynin2018, Theorem 4.6.1] leaves it unspecified ($C K^2$ there). The value proved
is <!-- value subgaussianRowsConstant -->$24$: the net argument needs
$C_{\mathrm{SG}}^2 / 256 \ge \max(1, \log 9)$, that is
$C_{\mathrm{SG}} \ge 16 \sqrt{\log 9} \approx 23.72$, so the margin is thin and the proof uses
$(\sqrt{\lvert n \rvert} + t)^2 \ge \lvert n \rvert + t^2$ and a $1/4$-net exactly. Smaller is
better; the API is the upper bound `subgaussianRowsConstant_le`. -/
noncomputable irreducible_def subgaussianRowsConstant : ℝ := 24

/-- The sub-Gaussian rows constant is positive. -/
theorem subgaussianRowsConstant_pos : 0 < subgaussianRowsConstant := by
  rw [subgaussianRowsConstant_def]
  norm_num

/-- An explicit upper bound, $24$, on `subgaussianRowsConstant`, whose value
is <!-- value subgaussianRowsConstant -->$24$. -/
theorem subgaussianRowsConstant_le : subgaussianRowsConstant ≤ 24 := by
  rw [subgaussianRowsConstant_def]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] [DecidableEq n] {X : Ω → Matrix m n ℝ} {c : ℝ≥0}

/-- **The fixed-vector bound**: for an $m \times n$ random matrix $\mathbf{X}$ with independent
isotropic sub-Gaussian rows with proxy $c$, a unit vector $\mathbf{x}$ and $v, b \ge 0$ with
$2c \le b$ and $16 c^2 b \le (b - 2c) v$, $\|\mathbf{X}\mathbf{x}\|^2 - \lvert m \rvert$ is
sub-exponential with parameters $v \lvert m \rvert$ and $b$: each
$\langle \mathbf{X}_{i,:}, \mathbf{x} \rangle^2 - 1$ is sub-exponential with parameters $v$, $b$
(`HasSubgaussianMGF.hasSubexponentialMGF_sq_sub_integral_of_le`), and the rows are independent.
Honorio and Jaakkola's pair is $(32 c^2, 4 c)$.
[Vershynin2018, proof of Theorem 4.6.1], with the constants of the squared sub-Gaussian. -/
theorem hasSubexponentialMGF_norm_mulVec_sq_sub_of_isSubgaussianVector
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {x : n → ℝ} (hx : ‖WithLp.toLp 2 x‖ = 1)
    {v b : ℝ≥0} (hb : 2 * c ≤ b) (hv : 16 * (c : ℝ) ^ 2 * b ≤ ((b : ℝ) - 2 * c) * v) :
    HasSubexponentialMGF (fun ω => ‖WithLp.toLp 2 (X ω *ᵥ x)‖ ^ 2 - Fintype.card m)
      (v * Fintype.card m) b μ := by
  have := hind.isProbabilityMeasure
  have hxn : ‖WithLp.toLp 2 x‖₊ = 1 := by rw [← NNReal.coe_eq_one, coe_nnnorm, hx]
  have hrow (i : m) :
      HasSubexponentialMGF (fun ω => (x ⬝ᵥ X ω i) ^ 2 - 1) v b μ := by
    have h := (hsub i).hasSubgaussianMGF x
    rw [hxn, one_pow, mul_one] at h
    have hint : ∫ ω, (RCLike.re (x ⬝ᵥ X ω i)) ^ 2 ∂μ = 1 := by
      have h2 := (hiso i).integral_norm_dotProduct_sq x
      simpa only [RCLike.re_to_real, Real.norm_eq_abs, sq_abs, hx, one_pow] using h2
    have h2 := h.hasSubexponentialMGF_sq_sub_integral_of_le hb hv
    rw [hint] at h2
    simpa only [RCLike.re_to_real] using h2
  have hY : iIndepFun (fun i ω => (x ⬝ᵥ X ω i) ^ 2 - 1) μ :=
    hind.comp (fun _ v => (x ⬝ᵥ v) ^ 2 - 1) (fun _ => by simp only [dotProduct]; fun_prop)
  have hsum := HasSubexponentialMGF.sum_of_iIndepFun hY (s := Finset.univ) fun i _ => hrow i
  refine (hsum.mono ?_ (Finset.sup_le fun _ _ => le_rfl)).congr (ae_of_all _ fun ω => ?_)
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  · dsimp only
    rw [Finset.sum_sub_distrib, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotProduct_comm]
    rfl

/-! ### Deterministic steps -/

omit [Fintype m] in
/-- With a coordinate, an isotropic sub-Gaussian vector has proxy at least $1$: a coordinate has
second moment $1$, at most the proxy by `HasSubgaussianMGF.integral_sq_le`. -/
theorem IsSubgaussianVector.one_le_of_isIsotropic [Nonempty n] [IsProbabilityMeasure μ]
    {y : Ω → n → ℝ} (hsub : IsSubgaussianVector y c μ) (hiso : IsIsotropic y μ) :
    1 ≤ (c : ℝ) := by
  obtain ⟨j⟩ := ‹Nonempty n›
  have hu : ‖WithLp.toLp 2 (Pi.single j 1 : n → ℝ)‖ = 1 := by
    have h := PiLp.norm_single 2 (fun _ : n => ℝ) j (1 : ℝ)
    rw [norm_one] at h
    exact h
  have hun : ‖WithLp.toLp 2 (Pi.single j 1 : n → ℝ)‖₊ = 1 := by
    rw [← NNReal.coe_eq_one, coe_nnnorm, hu]
  have h1 := (hsub.hasSubgaussianMGF (Pi.single j 1)).integral_sq_le
  have h2 := hiso.integral_norm_dotProduct_sq (Pi.single j 1)
  rw [hun, one_pow, mul_one] at h1
  simp only [RCLike.re_to_real] at h1
  simp only [Real.norm_eq_abs, sq_abs, hu, one_pow] at h2
  linarith

/-- The upper Gram bound
$\mathbf{A}^{\mathsf{H}}\mathbf{A} \preceq (\sqrt{N} + w)^2 \mathbf{I}$ from a Gram error at most
$\max(\sqrt{N} w, w^2)$. -/
private lemma conjTranspose_mul_self_le_of_specNorm_le {A : Matrix m n ℝ} {N w : ℝ} (hN : 0 ≤ N)
    (hw : 0 ≤ w) (h : specNorm (Aᴴ * A - N • (1 : Matrix n n ℝ)) ≤ max (√N * w) (w ^ 2)) :
    Aᴴ * A ≤ (√N + w) ^ 2 • (1 : Matrix n n ℝ) := by
  refine (conjTranspose_mul_self_le_add_smul_one_of_specNorm_sub_smul_one_le (T := A) (N := N)
    le_rfl).trans (smul_one_le_smul_one ?_)
  have hsw := mul_nonneg (Real.sqrt_nonneg N) hw
  have hm : max (√N * w) (w ^ 2) ≤ √N * w + w ^ 2 :=
    max_le (by nlinarith [sq_nonneg w]) (by linarith)
  have e : (√N + w) ^ 2 = N + 2 * (√N * w) + w ^ 2 := by rw [add_sq, Real.sq_sqrt hN]; ring
  linarith

/-- The lower Gram bound
$(\sqrt{N} - w)^2 \mathbf{I} \preceq \mathbf{A}^{\mathsf{H}}\mathbf{A}$ from a Gram error at most
$\max(\sqrt{N} w, w^2)$, for $0 \le w \le \sqrt{N}$. -/
private lemma le_conjTranspose_mul_self_of_specNorm_le {A : Matrix m n ℝ} {N w : ℝ} (hN : 0 ≤ N)
    (hw : 0 ≤ w) (hwN : w ≤ √N)
    (h : specNorm (Aᴴ * A - N • (1 : Matrix n n ℝ)) ≤ max (√N * w) (w ^ 2)) :
    (√N - w) ^ 2 • (1 : Matrix n n ℝ) ≤ Aᴴ * A := by
  refine (smul_one_le_smul_one ?_).trans
    (sub_smul_one_le_conjTranspose_mul_self_of_specNorm_sub_smul_one_le (T := A) (N := N) le_rfl)
  have hm : max (√N * w) (w ^ 2) = √N * w := max_eq_left (by nlinarith)
  have e : (√N - w) ^ 2 = N - 2 * (√N * w) + w ^ 2 := by rw [sub_sq, Real.sq_sqrt hN]; ring
  rw [hm] at h
  nlinarith

/-- The spectral norm bound $\|\mathbf{A}\|_2 < \sqrt{N} + w$ from a Gram error below
$\max(\sqrt{N} w, w^2)$. -/
private lemma specNorm_lt_of_specNorm_lt {A : Matrix m n ℝ} {N w : ℝ} (hN : 0 ≤ N) (hw : 0 ≤ w)
    (h : specNorm (Aᴴ * A - N • (1 : Matrix n n ℝ)) < max (√N * w) (w ^ 2)) :
    specNorm A < √N + w := by
  have hs := specNorm_nonneg (Aᴴ * A - N • (1 : Matrix n n ℝ))
  have h2 := (specNorm_sq_le_iff_conjTranspose_mul_self_le (by positivity)).mpr
    (conjTranspose_mul_self_le_add_smul_one_of_specNorm_sub_smul_one_le (T := A) (N := N) le_rfl)
  have hsw := mul_nonneg (Real.sqrt_nonneg N) hw
  have hm : max (√N * w) (w ^ 2) ≤ √N * w + w ^ 2 :=
    max_le (by nlinarith [sq_nonneg w]) (by linarith)
  have e : (√N + w) ^ 2 = N + 2 * (√N * w) + w ^ 2 := by rw [add_sq, Real.sq_sqrt hN]; ring
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) (by linarith)

/-- The smallest singular value bound $\sqrt{N} - w < \sigma_{\min}(\mathbf{A})$ from a Gram error
below $\max(\sqrt{N} w, w^2)$. -/
private lemma lt_singularValues_of_specNorm_lt {A : Matrix m n ℝ} {N w : ℝ} (hN : 0 ≤ N)
    (hw : 0 ≤ w) {k : ℕ} (hk : k + 1 = Fintype.card n)
    (h : specNorm (Aᴴ * A - N • (1 : Matrix n n ℝ)) < max (√N * w) (w ^ 2)) :
    √N - w < singularValues A k := by
  rcases lt_or_ge (√N) w with hwN | hwN
  · exact (sub_neg.mpr hwN).trans_le (singularValues_nonneg A k)
  have h2 := le_singularValues_last_sq_of_smul_one_le hk
    (sub_smul_one_le_conjTranspose_mul_self_of_specNorm_sub_smul_one_le (T := A) (N := N) le_rfl)
  have hm : max (√N * w) (w ^ 2) = √N * w := max_eq_left (by nlinarith)
  have e : (√N - w) ^ 2 = N - 2 * (√N * w) + w ^ 2 := by rw [sub_sq, Real.sq_sqrt hN]; ring
  rw [hm] at h
  exact lt_of_pow_lt_pow_left₀ 2 (singularValues_nonneg A k) (by nlinarith)

/-! ### The net argument -/

/-- The fixed-vector tail at the level of the net argument:
$r / 2 \le \bigl\lvert \|\mathbf{X}\mathbf{x}\|^2 - N \bigr\rvert$ with
$r = \max(\sqrt{N} w, w^2)$, $N = \lvert m \rvert$, has probability at most
$2 \exp\bigl(-(9/4)(\lvert n \rvert + t^2)\bigr)$. -/
private lemma measureReal_half_le_abs_le [Nonempty m]
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (hc : 1 ≤ (c : ℝ)) {t : ℝ} (ht : 0 ≤ t)
    {x : n → ℝ} (hx : ‖WithLp.toLp 2 x‖ = 1) :
    μ.real {ω | max (√(Fintype.card m : ℝ) *
        (subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)))
        ((subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)) ^ 2) / 2 ≤
      |‖WithLp.toLp 2 (X ω *ᵥ x)‖ ^ 2 - Fintype.card m|} ≤
      2 * Real.exp (-(9 / 4 * ((Fintype.card n : ℝ) + t ^ 2))) := by
  set N : ℝ := (Fintype.card m : ℝ) with hN_def
  set d : ℝ := (Fintype.card n : ℝ) with hd_def
  set w := subgaussianRowsConstant * c * (√d + t) with hw_def
  set r := max (√N * w) (w ^ 2) with hr_def
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ c := c.2
  have hc' : (0 : ℝ) < c := by linarith
  have hN : 0 < N := by rw [hN_def]; exact_mod_cast Fintype.card_pos
  have hw0 : 0 ≤ w := by rw [hw_def, subgaussianRowsConstant_def]; positivity
  have hr1 : √N * w ≤ r := le_max_left _ _
  have hr2 : w ^ 2 ≤ r := le_max_right _ _
  have hr0 : 0 ≤ r := (sq_nonneg w).trans hr2
  have e : w ^ 2 = 576 * c ^ 2 * (d + t ^ 2) + 1152 * c ^ 2 * (√d * t) := by
    have := Real.sq_sqrt hd0
    rw [hw_def, subgaussianRowsConstant_def]
    linear_combination 576 * (c : ℝ) ^ 2 * this
  have hdt : 0 ≤ 1152 * (c : ℝ) ^ 2 * (√d * t) := by positivity
  have hw2 : 576 * c ^ 2 * (d + t ^ 2) ≤ w ^ 2 := by linarith
  have hrN : N * w ^ 2 ≤ r ^ 2 := by
    have := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg N) hw0) hr1 2
    rwa [mul_pow, Real.sq_sqrt hN0] at this
  refine ((hasSubexponentialMGF_norm_mulVec_sq_sub_of_isSubgaussianVector hind hsub hiso
    hx (v := 32 * c ^ 2) (b := 4 * c) (mul_le_mul_of_nonneg_right (by norm_num) c.2)
    (by push_cast; nlinarith [pow_nonneg c.coe_nonneg 3])).measureReal_abs_ge_le
    (by positivity)).trans ?_
  gcongr
  push_cast
  have hdt2 : 0 ≤ d + t ^ 2 := by positivity
  refine le_min ?_ ?_
  · rw [le_div_iff₀ (by have := mul_pos (pow_pos hc' 2) hN; linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hw2 hN0]
  · rw [le_div_iff₀ (by linarith)]
    have hcc : (c : ℝ) * (d + t ^ 2) ≤ c ^ 2 * (d + t ^ 2) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hdt2
    nlinarith [mul_nonneg hc0 hdt2]

/-- **The net argument**: with rows and columns present, the Gram error
$\|\mathbf{X}^{\mathsf{H}}\mathbf{X} - N \mathbf{I}\|_2$, $N = \lvert m \rvert$, is below
$\max(\sqrt{N} w, w^2)$ outside probability $2 e^{-t^2}$. -/
private lemma measureReal_not_specNorm_lt [Nonempty m] [Nonempty n]
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ¬ specNorm ((X ω)ᴴ * X ω - (Fintype.card m : ℝ) • (1 : Matrix n n ℝ)) <
      max (√(Fintype.card m : ℝ) * (subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)))
        ((subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)) ^ 2)} ≤
      2 * Real.exp (-t ^ 2) := by
  have := hind.isProbabilityMeasure
  have hc : 1 ≤ (c : ℝ) :=
    (hsub (Classical.arbitrary m)).one_le_of_isIsotropic (hiso (Classical.arbitrary m))
  set N : ℝ := (Fintype.card m : ℝ) with hN_def
  set d : ℝ := (Fintype.card n : ℝ) with hd_def
  set w := subgaussianRowsConstant * c * (√d + t) with hw_def
  set r := max (√N * w) (w ^ 2) with hr_def
  have hd1 : 1 ≤ d := by rw [hd_def]; exact_mod_cast Fintype.card_pos
  have hw0 : 0 < w := by
    rw [hw_def, subgaussianRowsConstant_def]
    have : 1 ≤ √d := Real.one_le_sqrt.mpr hd1
    exact mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hr0 : 0 < r := (pow_pos hw0 2).trans_le (le_max_right _ _)
  obtain ⟨net, hcard, hunit, hnet⟩ :=
    exists_finset_specNorm_le_div_of_isHermitian ℝ n (ε := 1 / 4) (by norm_num) (by norm_num)
  rw [Module.finrank_fintype_fun_eq_card] at hcard
  norm_num at hcard
  have hsub' : {ω | ¬ specNorm ((X ω)ᴴ * X ω - N • (1 : Matrix n n ℝ)) < r} ⊆
      ⋃ x ∈ net, {ω | r / 2 ≤ |‖WithLp.toLp 2 (X ω *ᵥ x)‖ ^ 2 - N|} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hnot
    obtain ⟨M, hM0, hMr, hM⟩ := Finset.exists_le_lt_of_forall_lt net
      (fun x => |‖WithLp.toLp 2 (X ω *ᵥ x)‖ ^ 2 - N|) (half_pos hr0) hnot
    have hH := (Matrix.isHermitian_conjTranspose_mul_self (X ω)).sub (isHermitian_real_smul_one N)
    have h := hnet _ hH hM0 fun x hx => by
      rw [quadForm_sub_left, map_sub, quadForm_conjTranspose_mul_self, RCLike.ofReal_re,
        re_quadForm_real_smul_one, hunit x hx, one_pow, mul_one]
      exact hM x hx
    rw [show M / (1 - 2 * (1 / 4 : ℝ)) = 2 * M by ring] at h
    exact hω (h.trans_lt (by linarith))
  calc μ.real {ω | ¬ specNorm ((X ω)ᴴ * X ω - N • (1 : Matrix n n ℝ)) < r}
    _ ≤ μ.real (⋃ x ∈ net, {ω | r / 2 ≤ |‖WithLp.toLp 2 (X ω *ᵥ x)‖ ^ 2 - N|}) :=
      measureReal_mono hsub' (measure_ne_top _ _)
    _ ≤ ∑ x ∈ net, μ.real {ω | r / 2 ≤ |‖WithLp.toLp 2 (X ω *ᵥ x)‖ ^ 2 - N|} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ net, 2 * Real.exp (-(9 / 4 * (d + t ^ 2))) :=
      Finset.sum_le_sum fun x hx => measureReal_half_le_abs_le hind hsub hiso hc ht (hunit x hx)
    _ = net.card * (2 * Real.exp (-(9 / 4 * (d + t ^ 2)))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (9 / 4) ^ Fintype.card n * (2 * Real.exp (-(9 / 4 * (d + t ^ 2)))) := by
      gcongr
      exact hcard.trans (pow_le_pow_left₀ (by norm_num)
        ((Real.log_le_iff_le_exp (by norm_num)).1 Real.log_nine_le_nine_div_four) _)
    _ = 2 * Real.exp (-(9 / 4 * t ^ 2)) := by
      rw [← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add, hd_def]
      ring_nf
    _ ≤ 2 * Real.exp (-t ^ 2) := by
      gcongr
      nlinarith [sq_nonneg t]

/-- The Gram error is at most $\max(\sqrt{N} w, w^2)$ outside probability $2 e^{-t^2}$, with no
nonemptiness hypothesis (with no rows or no columns the event is empty). -/
private lemma measureReal_not_specNorm_le
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ¬ specNorm ((X ω)ᴴ * X ω - (Fintype.card m : ℝ) • (1 : Matrix n n ℝ)) ≤
      max (√(Fintype.card m : ℝ) * (subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)))
        ((subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)) ^ 2)} ≤
      2 * Real.exp (-t ^ 2) := by
  have := hind.isProbabilityMeasure
  rcases isEmpty_or_nonempty m with hm | hm
  · have hall : ∀ ω, specNorm ((X ω)ᴴ * X ω - (Fintype.card m : ℝ) • (1 : Matrix n n ℝ)) ≤
        max (√(Fintype.card m : ℝ) *
          (subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)))
          ((subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)) ^ 2) := fun ω => by
      rw [Subsingleton.elim (X ω) 0, Fintype.card_eq_zero, Nat.cast_zero, zero_smul,
        Matrix.conjTranspose_zero, Matrix.zero_mul, sub_zero, specNorm_zero]
      exact (sq_nonneg _).trans (le_max_right _ _)
    simp only [hall, not_true_eq_false, Set.ofPred_false, measureReal_empty]
    positivity
  rcases isEmpty_or_nonempty n with hn | hn
  · have hall : ∀ ω, specNorm ((X ω)ᴴ * X ω - (Fintype.card m : ℝ) • (1 : Matrix n n ℝ)) ≤
        max (√(Fintype.card m : ℝ) *
          (subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)))
          ((subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)) ^ 2) := fun ω => by
      rw [Subsingleton.elim ((X ω)ᴴ * X ω - (Fintype.card m : ℝ) • (1 : Matrix n n ℝ)) 0,
        specNorm_zero]
      exact (sq_nonneg _).trans (le_max_right _ _)
    simp only [hall, not_true_eq_false, Set.ofPred_false, measureReal_empty]
    positivity
  refine (measureReal_mono fun ω => ?_).trans (measureReal_not_specNorm_lt hind hsub hiso ht)
  simp only [Set.mem_ofPred_eq]
  exact fun hω h => hω h.le

/-! ### The extreme singular values -/

/-- **Independent isotropic sub-Gaussian rows**, the Gram sandwich: for an $m \times n$ random
matrix $\mathbf{X}$ whose rows are independent, isotropic and sub-Gaussian with proxy $c$,
with <!-- value subgaussianRowsConstant -->$w = 24c(\sqrt{\lvert n \rvert} + t)$ (the constant is
`subgaussianRowsConstant`), $0 \le t$ and $w \le \sqrt{\lvert m \rvert}$,
$$(\sqrt{\lvert m \rvert} - w)^2 \mathbf{I} \preceq \mathbf{X}^{\mathsf{H}}\mathbf{X}
\preceq (\sqrt{\lvert m \rvert} + w)^2 \mathbf{I}$$
outside probability $2 e^{-t^2}$.
[Vershynin2018, Theorem 4.6.1], there for the singular values with an unspecified constant
$C K^2$; here in Loewner form with the named constant `subgaussianRowsConstant`. For a standard
Gaussian matrix the Gram sandwich of `NLAlib/RandomMatrix/Gaussian/ExtremeSingularValues.lean`
is better in every regime.
Result: subgaussian-matrix-norm -/
theorem
measureReal_not_smul_one_le_conjTranspose_mul_self_and_le_smul_one_le_of_isSubgaussianVector
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {t : ℝ} (ht : 0 ≤ t)
    (hw : subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t) ≤ √(Fintype.card m : ℝ)) :
    μ.real {ω | ¬ ((√(Fintype.card m : ℝ) -
        subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)) ^ 2 • (1 : Matrix n n ℝ) ≤
      (X ω)ᴴ * X ω ∧ (X ω)ᴴ * X ω ≤ (√(Fintype.card m : ℝ) +
        subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)) ^ 2 • (1 : Matrix n n ℝ))} ≤
      2 * Real.exp (-t ^ 2) := by
  have := hind.isProbabilityMeasure
  have hw0 : 0 ≤ subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t) :=
    mul_nonneg (mul_nonneg subgaussianRowsConstant_pos.le c.2)
      (add_nonneg (Real.sqrt_nonneg _) ht)
  refine (measureReal_mono fun ω => ?_).trans (measureReal_not_specNorm_le hind hsub hiso ht)
  simp only [Set.mem_ofPred_eq]
  exact fun hω h => hω ⟨le_conjTranspose_mul_self_of_specNorm_le (Nat.cast_nonneg _) hw0 hw h,
    conjTranspose_mul_self_le_of_specNorm_le (Nat.cast_nonneg _) hw0 h⟩

/-- The lower Gram bound for independent isotropic sub-Gaussian rows:
$(\sqrt{\lvert m \rvert} - w)^2 \mathbf{I} \preceq \mathbf{X}^{\mathsf{H}}\mathbf{X}$ outside
probability $2 e^{-t^2}$,
with <!-- value subgaussianRowsConstant -->$w = 24c(\sqrt{\lvert n \rvert} + t)$ (the constant is
`subgaussianRowsConstant`), $0 \le t$ and $w \le \sqrt{\lvert m \rvert}$ (the base must be
nonnegative). [Vershynin2018, Theorem 4.6.1], in Loewner form. For a standard Gaussian matrix
`NLAlib.measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix` is better
in every regime. -/
theorem measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_isSubgaussianVector
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {t : ℝ} (ht : 0 ≤ t)
    (hw : subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t) ≤ √(Fintype.card m : ℝ)) :
    μ.real {ω | ¬ (√(Fintype.card m : ℝ) -
        subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)) ^ 2 • (1 : Matrix n n ℝ) ≤
      (X ω)ᴴ * X ω} ≤ 2 * Real.exp (-t ^ 2) := by
  have := hind.isProbabilityMeasure
  refine (measureReal_mono fun ω => ?_).trans
    (measureReal_not_smul_one_le_conjTranspose_mul_self_and_le_smul_one_le_of_isSubgaussianVector
      hind hsub hiso ht hw)
  simp only [Set.mem_ofPred_eq]
  exact fun hω h => hω h.1

/-- The upper Gram bound for independent isotropic sub-Gaussian rows:
$\mathbf{X}^{\mathsf{H}}\mathbf{X} \preceq (\sqrt{\lvert m \rvert} + w)^2 \mathbf{I}$ outside
probability $2 e^{-t^2}$,
with <!-- value subgaussianRowsConstant -->$w = 24c(\sqrt{\lvert n \rvert} + t)$ (the constant is
`subgaussianRowsConstant`) and $0 \le t$.
[Vershynin2018, Theorem 4.6.1], in Loewner form. For a standard Gaussian matrix
`NLAlib.measureReal_not_conjTranspose_mul_self_le_smul_one_le_of_hasLaw_gaussianMatrix` is better
in every regime. -/
theorem measureReal_not_conjTranspose_mul_self_le_smul_one_le_of_isSubgaussianVector
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ¬ (X ω)ᴴ * X ω ≤ (√(Fintype.card m : ℝ) +
      subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)) ^ 2 • (1 : Matrix n n ℝ)} ≤
      2 * Real.exp (-t ^ 2) := by
  have := hind.isProbabilityMeasure
  have hw0 : 0 ≤ subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t) :=
    mul_nonneg (mul_nonneg subgaussianRowsConstant_pos.le c.2)
      (add_nonneg (Real.sqrt_nonneg _) ht)
  refine (measureReal_mono fun ω => ?_).trans (measureReal_not_specNorm_le hind hsub hiso ht)
  simp only [Set.mem_ofPred_eq]
  exact fun hω h => hω (conjTranspose_mul_self_le_of_specNorm_le (Nat.cast_nonneg _) hw0 h)

/-- The lower tail of the smallest singular value for independent isotropic sub-Gaussian rows:
$\mathbb{P}[\sigma_k(\mathbf{X}) \le \sqrt{\lvert m \rvert} - w] \le 2 e^{-t^2}$,
with <!-- value subgaussianRowsConstant -->$w = 24c(\sqrt{\lvert n \rvert} + t)$ (the constant is
`subgaussianRowsConstant`) and $0 \le t$; $\sigma_k = \sigma_{\min}$ is the singular value of
index $k$ with $k + 1 = \lvert n \rvert$. The rows must exist (`[Nonempty m]`): with no rows the
hypotheses leave $c$ free, and for $c = 0$ the event is everything. [Vershynin2018, Theorem 4.6.1].
For a standard Gaussian matrix `NLAlib.measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix` is
better in every regime. -/
theorem measureReal_singularValues_le_le_of_isSubgaussianVector [Nonempty m]
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {k : ℕ} (hk : k + 1 = Fintype.card n) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | singularValues (X ω) k ≤
      √(Fintype.card m : ℝ) - subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t)} ≤
      2 * Real.exp (-t ^ 2) := by
  have := hind.isProbabilityMeasure
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Fintype.card_eq_zero] at hk
    omega
  have hw0 : 0 ≤ subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t) :=
    mul_nonneg (mul_nonneg subgaussianRowsConstant_pos.le c.2)
      (add_nonneg (Real.sqrt_nonneg _) ht)
  refine (measureReal_mono fun ω => ?_).trans (measureReal_not_specNorm_lt hind hsub hiso ht)
  simp only [Set.mem_ofPred_eq]
  exact fun hω h => (not_le.mpr (lt_singularValues_of_specNorm_lt (Nat.cast_nonneg _) hw0 hk h)) hω

/-- The upper tail of the spectral norm for independent isotropic sub-Gaussian rows:
$\mathbb{P}[\|\mathbf{X}\|_2 \ge \sqrt{\lvert m \rvert} + w] \le 2 e^{-t^2}$,
with <!-- value subgaussianRowsConstant -->$w = 24c(\sqrt{\lvert n \rvert} + t)$ (the constant is
`subgaussianRowsConstant`) and $0 \le t$. The rows must exist (`[Nonempty m]`), as in
`NLAlib.measureReal_singularValues_le_le_of_isSubgaussianVector`. [Vershynin2018, Theorem 4.6.1].
For a standard Gaussian matrix `NLAlib.measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix` is
better in every regime. -/
theorem measureReal_specNorm_ge_le_of_isSubgaussianVector [Nonempty m]
    (hind : iIndepFun (fun i ω => X ω i) μ) (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √(Fintype.card m : ℝ) +
      subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t) ≤ specNorm (X ω)} ≤
      2 * Real.exp (-t ^ 2) := by
  have := hind.isProbabilityMeasure
  have hw0 : 0 ≤ subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t) :=
    mul_nonneg (mul_nonneg subgaussianRowsConstant_pos.le c.2)
      (add_nonneg (Real.sqrt_nonneg _) ht)
  rcases isEmpty_or_nonempty n with hn | hn
  · have hN : 0 < √(Fintype.card m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
    have hall : ∀ ω, ¬ √(Fintype.card m : ℝ) +
        subgaussianRowsConstant * c * (√(Fintype.card n : ℝ) + t) ≤ specNorm (X ω) := by
      intro ω
      rw [Subsingleton.elim (X ω) 0, specNorm_zero, not_le]
      positivity
    simp only [hall, Set.ofPred_false, measureReal_empty]
    positivity
  refine (measureReal_mono fun ω => ?_).trans (measureReal_not_specNorm_lt hind hsub hiso ht)
  simp only [Set.mem_ofPred_eq]
  exact fun hω h => (not_le.mpr (specNorm_lt_of_specNorm_lt (Nat.cast_nonneg _) hw0 h)) hω

end NLAlib
