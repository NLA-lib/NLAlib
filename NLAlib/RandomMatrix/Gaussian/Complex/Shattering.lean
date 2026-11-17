/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Complex
public import NLAlib.Matrix.Spectral.Diagonalizable
public import NLAlib.Matrix.Spectral.EigenvalueListing

/-!
# Eigenvalue gap and eigenvector condition of a Ginibre perturbation

For a complex matrix $\mathbf{M}$ of order $n$, $\gamma > 0$ and a standard complex Gaussian
matrix $\mathbf{G}$, the perturbation $\mathbf{M} + \gamma n^{-1/2}\mathbf{G}$ has, with high
probability, eigenvalues separated by a polynomial in $\gamma/n$ (Theorem A) and a diagonalization
whose eigenvector matrix has a condition number polynomial in $n/\gamma$ (Theorem B)
([BanksGarzaVargasSrivastava2025, Lemmas B.1 and B.2], from
[BanksGarzaVargasKulkarniSrivastava2020] and [BanksKulkarniMukherjeeSrivastava2021]). This file
states both, in a polylogarithmic tail form with a record of constants $(C, a, b, c)$, as named
predicates (`NLAlib.ComplexGaussianGapTail`, `NLAlib.ComplexGaussianConditionTail`), and their
preferred forms; the theorems are taken as hypotheses until they are proved. The records are
normalized once ($C \ge 1$, $a, c \ge 0$), which keeps the tails monotone in the order and the
norm ratio. The two events combine, after a shift by $4\gamma\mathbf{I}$ when $\|\mathbf{M}\|_2$
is small, into the diagonalization class (condition at most $t_2^{-1}$, separation at least
$t_1$) that the eigenvalue solver of [BanksGarzaVargasSrivastava2025] consumes, and a tail can be
inverted at a target failure probability.

## Main definitions

* `NLAlib.PolyLogTail`, `NLAlib.PolyLogTail.normalize`: the record of a tail
  $C n^a \tau^b K^c$ and its normalization.
* `NLAlib.ComplexGaussianGapTail`, `NLAlib.ComplexGaussianConditionTail`: Theorems A and B in
  tail form.
* `NLAlib.ComplexGaussianGapPreferred`, `NLAlib.ComplexGaussianConditionPreferred`: the
  preferred forms.
* `NLAlib.polyLogTailInverse`: a parameter at which a normalized tail is at most a target.

## Main results

* `NLAlib.PolyLogTail.le_normalize`, `NLAlib.ComplexGaussianGapTail.normalize`,
  `NLAlib.ComplexGaussianConditionTail.normalize`.
* `NLAlib.exists_complexGaussianGapTail_iff`, `NLAlib.exists_complexGaussianConditionTail_iff`:
  the asymptotic forms are the existence of a record.
* `NLAlib.complexGaussianGapTail_of_preferred`,
  `NLAlib.complexGaussianConditionTail_of_preferred`: the preferred forms imply the tail forms.
* `NLAlib.measureReal_not_exists_class_le_of_hasLaw_complexGaussianMatrix`: the class event.
* `NLAlib.polyLogTailInverse_spec`: the inverted tail.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-! ### The tail record and the two predicates -/

/-- The constants $(C, a, b, c)$ of a polylogarithmic tail
$C\,n^a\,\tau^b\,K^c$ in the order $n$, a small parameter $\tau$ and a logarithmic factor $K$. -/
structure PolyLogTail where
  /-- The leading constant. -/
  C : ℝ
  /-- The exponent of the order. -/
  a : ℝ
  /-- The exponent of the small parameter. -/
  b : ℝ
  /-- The exponent of the logarithmic factor. -/
  c : ℝ

/-- The normalized record $(\max(C, 1), \max(a, 0), b, \max(c, 0))$: a tail valid for a record
is valid for its normalization, since the order is at least $1$ and the logarithmic factor at
least $1$ where the tails are used, and the normalized tail is monotone in both. -/
noncomputable def PolyLogTail.normalize (t : PolyLogTail) : PolyLogTail :=
  ⟨max t.C 1, max t.a 0, t.b, max t.c 0⟩

/-- **The eigenvalue gap of a Ginibre perturbation in tail form** with the record $c$
([BanksGarzaVargasSrivastava2025, Lemma B.1], Theorem A of the weak form): for every standard
complex Gaussian matrix $\mathbf{G}$ of order $n$, every $\mathbf{M}$ and $\gamma, t$ with
$0 < 2\gamma \le \|\mathbf{M}\|_2$ and $0 < t \le \gamma$,
$$\mathbb{P}\bigl[\text{no listing } \boldsymbol{\lambda} \text{ of }
  \mathbf{M} + \gamma n^{-1/2}\mathbf{G} \text{ with } \lvert\lambda_i - \lambda_j\rvert > t
  \text{ for } i \ne j\bigr] \le C n^a (t/\gamma)^b
  (\|\mathbf{M}\|_2/\gamma + \log(\gamma/t))^c\,.$$ -/
def ComplexGaussianGapTail (c : PolyLogTail) : Prop :=
  ∀ {Ω : Type} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {n : Type} [Fintype n] [DecidableEq n] {G : Ω → Matrix n n ℂ},
    HasLaw G (complexGaussianMatrix n n) μ → ∀ (M : Matrix n n ℂ) {γ t : ℝ},
    0 < γ → 2 * γ ≤ specNorm M → 0 < t → t ≤ γ →
    μ.real {ω | ¬ ∃ d : n → ℂ,
      IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
        ∀ i j, i ≠ j → t < ‖d i - d j‖} ≤
      c.C * (Fintype.card n : ℝ) ^ c.a * (t / γ) ^ c.b * (specNorm M / γ + Real.log (γ / t)) ^ c.c

/-- **The eigenvector condition of a Ginibre perturbation in tail form** with the record $c$
([BanksGarzaVargasSrivastava2025, Lemma B.2], Theorem B of the weak form): for every standard
complex Gaussian matrix $\mathbf{G}$ of order $n$, every $\mathbf{M}$ and $\gamma, t$ with
$0 < 2\gamma \le \|\mathbf{M}\|_2$ and $0 < t \le 1$, the probability that
$\mathbf{M} + \gamma n^{-1/2}\mathbf{G}$ has no diagonalization
$\mathbf{V}\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le t^{-1}$ is at most
$C n^a t^b (\|\mathbf{M}\|_2/\gamma + \log(1/t))^c$. -/
def ComplexGaussianConditionTail (c : PolyLogTail) : Prop :=
  ∀ {Ω : Type} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {n : Type} [Fintype n] [DecidableEq n] {G : Ω → Matrix n n ℂ},
    HasLaw G (complexGaussianMatrix n n) μ → ∀ (M : Matrix n n ℂ) {γ t : ℝ},
    0 < γ → 2 * γ ≤ specNorm M → 0 < t → t ≤ 1 →
    μ.real {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
      (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
        pseudoConditionNumber V ≤ t⁻¹} ≤
      c.C * (Fintype.card n : ℝ) ^ c.a * t ^ c.b * (specNorm M / γ + Real.log t⁻¹) ^ c.c

/-- The normalized record dominates: for $x = 0$ or $x \ge 1$, $y \ge 0$ and $z \ge 1$,
$C x^a y^b z^c \le \bar C x^{\bar a} y^{\bar b} z^{\bar c}$ for the normalized record
$(\bar C, \bar a, \bar b, \bar c) = (\max(C, 1), \max(a, 0), b, \max(c, 0))$. -/
theorem PolyLogTail.le_normalize (c : PolyLogTail) {x y z : ℝ} (hx : x = 0 ∨ 1 ≤ x)
    (hy : 0 ≤ y) (hz : 1 ≤ z) :
    c.C * x ^ c.a * y ^ c.b * z ^ c.c ≤
      c.normalize.C * x ^ c.normalize.a * y ^ c.normalize.b * z ^ c.normalize.c := by
  simp only [PolyLogTail.normalize]
  have hx0 : 0 ≤ x := by rcases hx with rfl | hx <;> linarith
  have hxa : x ^ c.a ≤ x ^ max c.a 0 := by
    rcases hx with rfl | hx
    · rcases eq_or_ne c.a 0 with h | h
      · simp [h]
      · rw [Real.zero_rpow h]
        exact Real.rpow_nonneg le_rfl _
    · exact Real.rpow_le_rpow_of_exponent_le hx (le_max_left _ _)
  have hzc : z ^ c.c ≤ z ^ max c.c 0 := Real.rpow_le_rpow_of_exponent_le hz (le_max_left _ _)
  have hP : 0 ≤ x ^ c.a * y ^ c.b * z ^ c.c := by
    have := Real.rpow_nonneg hx0 c.a
    have := Real.rpow_nonneg hy c.b
    have := Real.rpow_nonneg (zero_le_one.trans hz) c.c
    positivity
  calc c.C * x ^ c.a * y ^ c.b * z ^ c.c = c.C * (x ^ c.a * y ^ c.b * z ^ c.c) := by ring
    _ ≤ max c.C 1 * (x ^ c.a * y ^ c.b * z ^ c.c) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hP
    _ ≤ max c.C 1 * (x ^ max c.a 0 * y ^ c.b * z ^ max c.c 0) := by
        have := Real.rpow_nonneg hy c.b
        have := Real.rpow_nonneg hx0 (max c.a 0)
        gcongr
    _ = _ := by ring

/-- The cardinality of a finite type is $0$ or at least $1$, as a real number. -/
private theorem card_eq_zero_or_one_le (n : Type) [Fintype n] :
    (Fintype.card n : ℝ) = 0 ∨ 1 ≤ (Fintype.card n : ℝ) := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h | h
  · left
    simp [h]
  · right
    exact_mod_cast h

/-- A gap tail holds for its normalized record. -/
theorem ComplexGaussianGapTail.normalize {c : PolyLogTail} (h : ComplexGaussianGapTail c) :
    ComplexGaussianGapTail c.normalize := by
  intro Ω _ μ n _ _ G hG M γ t hγ hM ht htγ
  refine (h hG M hγ hM ht htγ).trans (c.le_normalize (card_eq_zero_or_one_le n)
    (div_nonneg ht.le hγ.le) ?_)
  have h2 : 2 ≤ specNorm M / γ := (le_div_iff₀ hγ).mpr hM
  have hl : 0 ≤ Real.log (γ / t) := Real.log_nonneg ((one_le_div ht).mpr htγ)
  linarith

/-- A condition tail holds for its normalized record. -/
theorem ComplexGaussianConditionTail.normalize {c : PolyLogTail}
    (h : ComplexGaussianConditionTail c) : ComplexGaussianConditionTail c.normalize := by
  intro Ω _ μ n _ _ G hG M γ t hγ hM ht ht1
  refine (h hG M hγ hM ht ht1).trans (c.le_normalize (card_eq_zero_or_one_le n) ht.le ?_)
  have h2 : 2 ≤ specNorm M / γ := (le_div_iff₀ hγ).mpr hM
  have hl : 0 ≤ Real.log t⁻¹ := Real.log_nonneg ((one_le_inv₀ ht).mpr ht1)
  linarith

/-! ### The asymptotic forms -/

/-- The asymptotic form of the gap tail (some constants $C, a, c$ and $b > 0$) is the existence
of a tail record with $b > 0$. -/
theorem exists_complexGaussianGapTail_iff :
    (∃ (C a b c : ℝ), 0 < b ∧ ∀ {Ω : Type} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
      {n : Type} [Fintype n] [DecidableEq n] {G : Ω → Matrix n n ℂ},
      HasLaw G (complexGaussianMatrix n n) μ → ∀ (M : Matrix n n ℂ) {γ t : ℝ},
      0 < γ → 2 * γ ≤ specNorm M → 0 < t → t ≤ γ →
      μ.real {ω | ¬ ∃ d : n → ℂ,
        IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
          ∀ i j, i ≠ j → t < ‖d i - d j‖} ≤
        C * (Fintype.card n : ℝ) ^ a * (t / γ) ^ b * (specNorm M / γ + Real.log (γ / t)) ^ c) ↔
    ∃ c : PolyLogTail, 0 < c.b ∧ ComplexGaussianGapTail c := by
  constructor
  · rintro ⟨C, a, b, c, hb, h⟩
    exact ⟨⟨C, a, b, c⟩, hb, fun hG M => h hG M⟩
  · rintro ⟨⟨C, a, b, c⟩, hb, h⟩
    exact ⟨C, a, b, c, hb, fun hG M => h hG M⟩

/-- The asymptotic form of the condition tail (some constants $C, a, c$ and $b > 0$) is the
existence of a tail record with $b > 0$. -/
theorem exists_complexGaussianConditionTail_iff :
    (∃ (C a b c : ℝ), 0 < b ∧ ∀ {Ω : Type} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
      {n : Type} [Fintype n] [DecidableEq n] {G : Ω → Matrix n n ℂ},
      HasLaw G (complexGaussianMatrix n n) μ → ∀ (M : Matrix n n ℂ) {γ t : ℝ},
      0 < γ → 2 * γ ≤ specNorm M → 0 < t → t ≤ 1 →
      μ.real {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
        (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
          pseudoConditionNumber V ≤ t⁻¹} ≤
        C * (Fintype.card n : ℝ) ^ a * t ^ b * (specNorm M / γ + Real.log t⁻¹) ^ c) ↔
    ∃ c : PolyLogTail, 0 < c.b ∧ ComplexGaussianConditionTail c := by
  constructor
  · rintro ⟨C, a, b, c, hb, h⟩
    exact ⟨⟨C, a, b, c⟩, hb, fun hG M => h hG M⟩
  · rintro ⟨⟨C, a, b, c⟩, hb, h⟩
    exact ⟨C, a, b, c, hb, fun hG M => h hG M⟩

/- The asymptotic gap form, with its binders as they will be proved, gives a record. -/
example (h : ∃ (C a b c : ℝ), 0 < b ∧ ∀ {Ω : Type} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
      {n : Type} [Fintype n] [DecidableEq n] {G : Ω → Matrix n n ℂ},
      HasLaw G (complexGaussianMatrix n n) μ → ∀ (M : Matrix n n ℂ) {γ t : ℝ},
      0 < γ → 2 * γ ≤ specNorm M → 0 < t → t ≤ γ →
      μ.real {ω | ¬ ∃ d : n → ℂ,
        IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
          ∀ i j, i ≠ j → t < ‖d i - d j‖} ≤
        C * (Fintype.card n : ℝ) ^ a * (t / γ) ^ b * (specNorm M / γ + Real.log (γ / t)) ^ c) :
    ∃ c : PolyLogTail, 0 < c.b ∧ ComplexGaussianGapTail c :=
  exists_complexGaussianGapTail_iff.mp h

/- The asymptotic condition form, with its binders as they will be proved, gives a record. -/
example (h : ∃ (C a b c : ℝ), 0 < b ∧ ∀ {Ω : Type} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
      {n : Type} [Fintype n] [DecidableEq n] {G : Ω → Matrix n n ℂ},
      HasLaw G (complexGaussianMatrix n n) μ → ∀ (M : Matrix n n ℂ) {γ t : ℝ},
      0 < γ → 2 * γ ≤ specNorm M → 0 < t → t ≤ 1 →
      μ.real {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
        (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
          pseudoConditionNumber V ≤ t⁻¹} ≤
        C * (Fintype.card n : ℝ) ^ a * t ^ b * (specNorm M / γ + Real.log t⁻¹) ^ c) :
    ∃ c : PolyLogTail, 0 < c.b ∧ ComplexGaussianConditionTail c :=
  exists_complexGaussianConditionTail_iff.mp h

/-! ### The preferred forms -/

/-- The preferred form of the gap theorem ([BanksGarzaVargasSrivastava2025, Lemma B.1], from
[BanksGarzaVargasKulkarniSrivastava2020, Proposition D.5]): for every standard complex Gaussian
$\mathbf{G}$ of order $n$, every $\mathbf{M}$, $\gamma > 0$ and $t \ge 0$, the probability that
$\mathbf{M} + \gamma n^{-1/2}\mathbf{G}$ has no listing with all gaps above $t$ is at most
$n^3t^2/\gamma^2$. -/
def ComplexGaussianGapPreferred : Prop :=
  ∀ {Ω : Type} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {n : Type} [Fintype n] [DecidableEq n] {G : Ω → Matrix n n ℂ},
    HasLaw G (complexGaussianMatrix n n) μ → ∀ (M : Matrix n n ℂ) {γ t : ℝ},
    0 < γ → 0 ≤ t →
    μ.real {ω | ¬ ∃ d : n → ℂ,
      IsEigenvalueListing (M + (γ / √(Fintype.card n : ℝ)) • G ω) d ∧
        ∀ i j, i ≠ j → t < ‖d i - d j‖} ≤
      (Fintype.card n : ℝ) ^ 3 * t ^ 2 / γ ^ 2

/-- The preferred form of the condition theorem ([BanksGarzaVargasSrivastava2025, Lemma B.2],
through Davies' bound [BanksKulkarniMukherjeeSrivastava2021, Theorem 1.5]): for every standard
complex Gaussian $\mathbf{G}$ of order $n$, every $\mathbf{M}$, $0 < \gamma < \|\mathbf{M}\|_2$ and
$t > 0$, the probability that $\mathbf{M} + \gamma n^{-1/2}\mathbf{G}$ has no diagonalization with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le t^{-1}$ is at most
$2(2\sqrt2 + \|\mathbf{M}\|_2/\gamma + \sqrt{4\log(1/t)/n})^2 n^3 t^2$. -/
def ComplexGaussianConditionPreferred : Prop :=
  ∀ {Ω : Type} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {n : Type} [Fintype n] [DecidableEq n] {G : Ω → Matrix n n ℂ},
    HasLaw G (complexGaussianMatrix n n) μ → ∀ (M : Matrix n n ℂ) {γ t : ℝ},
    0 < γ → γ < specNorm M → 0 < t →
    μ.real {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
      (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
        pseudoConditionNumber V ≤ t⁻¹} ≤
      2 * (2 * √2 + specNorm M / γ + √(4 * Real.log t⁻¹ / Fintype.card n)) ^ 2 *
        (Fintype.card n : ℝ) ^ 3 * t ^ 2

/-- The preferred gap form is the gap tail with the record $(1, 3, 2, 0)$. -/
theorem complexGaussianGapTail_of_preferred (h : ComplexGaussianGapPreferred) :
    ComplexGaussianGapTail ⟨1, 3, 2, 0⟩ := by
  intro Ω _ μ n _ _ G hG M γ t hγ _ ht _
  refine (h hG M hγ ht.le).trans (le_of_eq ?_)
  simp only [Real.rpow_ofNat, Real.rpow_zero, one_mul, mul_one, div_pow]
  ring

/-- The preferred condition form is the condition tail with the record $(18, 3, 2, 2)$: in the
range $2\gamma \le \|\mathbf{M}\|_2$, $2\sqrt2 + 1 \le 1.92\|\mathbf{M}\|_2/\gamma$ and
$\sqrt{4L} \le L + 1$. -/
theorem complexGaussianConditionTail_of_preferred (h : ComplexGaussianConditionPreferred) :
    ComplexGaussianConditionTail ⟨18, 3, 2, 2⟩ := by
  intro Ω _ μ n _ _ G hG M γ t hγ hM ht ht1
  refine (h hG M hγ (by linarith) ht).trans ?_
  simp only [Real.rpow_ofNat]
  set m := specNorm M / γ
  set L := Real.log t⁻¹
  have hm : 2 ≤ m := (le_div_iff₀ hγ).mpr hM
  have hL : 0 ≤ L := Real.log_nonneg ((one_le_inv₀ ht).mpr ht1)
  have hs2 : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have h4 : √(4 * L / Fintype.card n) ≤ L + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    rcases card_eq_zero_or_one_le n with h0 | h1
    · rw [h0, div_zero]
      positivity
    · nlinarith [div_le_self (by positivity : (0:ℝ) ≤ 4 * L) h1, sq_nonneg (L - 1)]
  have hsum : 0 ≤ 2 * √2 + m + √(4 * L / Fintype.card n) := by positivity
  have hle : 2 * √2 + m + √(4 * L / Fintype.card n) ≤ 3 * (m + L) := by linarith
  have hsq := pow_le_pow_left₀ hsum hle 2
  have hnt : 0 ≤ (Fintype.card n : ℝ) ^ 3 * t ^ 2 := by positivity
  calc 2 * (2 * √2 + m + √(4 * L / Fintype.card n)) ^ 2 * (Fintype.card n : ℝ) ^ 3 * t ^ 2
      = 2 * (2 * √2 + m + √(4 * L / Fintype.card n)) ^ 2 * ((Fintype.card n : ℝ) ^ 3 * t ^ 2) := by
        ring
    _ ≤ 2 * (3 * (m + L)) ^ 2 * ((Fintype.card n : ℝ) ^ 3 * t ^ 2) := by gcongr
    _ = 18 * (Fintype.card n : ℝ) ^ 3 * t ^ 2 * (m + L) ^ 2 := by ring

/-! ### The class event -/

/-- A normalized tail is nonnegative. -/
private theorem tail_nonneg (c : PolyLogTail) (k : ℕ) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ c.normalize.C * (k : ℝ) ^ c.normalize.a * y ^ c.normalize.b * z ^ c.normalize.c := by
  have h1 : 0 ≤ c.normalize.C := zero_le_one.trans (le_max_right _ _)
  have := Real.rpow_nonneg (Nat.cast_nonneg k) c.normalize.a
  have := Real.rpow_nonneg hy c.normalize.b
  have := Real.rpow_nonneg hz c.normalize.c
  positivity

/-- A normalized tail is monotone in its logarithmic factor. -/
private theorem tail_mono_base (c : PolyLogTail) {x y : ℝ} (k : ℕ) {w : ℝ} (hw : 0 ≤ w)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    c.normalize.C * (k : ℝ) ^ c.normalize.a * w ^ c.normalize.b * x ^ c.normalize.c ≤
      c.normalize.C * (k : ℝ) ^ c.normalize.a * w ^ c.normalize.b * y ^ c.normalize.c := by
  have h1 : 0 ≤ c.normalize.C := zero_le_one.trans (le_max_right _ _)
  have := Real.rpow_nonneg (Nat.cast_nonneg k) c.normalize.a
  have := Real.rpow_nonneg hw c.normalize.b
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy (le_max_right _ _)) (by positivity)

/-- A shift $s \mathbf{I}$ that puts the norm of $\mathbf{M}$ in $[2\gamma, \|\mathbf{M}\|_2 +
4\gamma]$: none when $2\gamma \le \|\mathbf{M}\|_2$, else $4\gamma$. -/
private theorem exists_shift_specNorm {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    {γ : ℝ} (hγ : 0 < γ) (M : Matrix n n ℂ) :
    ∃ s : ℂ, 2 * γ ≤ specNorm (M + s • 1) ∧ specNorm (M + s • 1) ≤ specNorm M + 4 * γ := by
  by_cases h : 2 * γ ≤ specNorm M
  · exact ⟨0, by rwa [zero_smul, add_zero], by rw [zero_smul, add_zero]; linarith⟩
  · refine ⟨(4 * γ : ℝ), ?_, ?_⟩
    · have hs : specNorm (((4 * γ : ℝ) : ℂ) • (1 : Matrix n n ℂ)) = 4 * γ := by
        rw [specNorm_smul, specNorm_one, mul_one, Complex.norm_real, Real.norm_of_nonneg
          (by linarith)]
      have := specNorm_sub_le (M + ((4 * γ : ℝ) : ℂ) • (1 : Matrix n n ℂ)) M
      rw [add_sub_cancel_left, hs] at this
      linarith
    · refine (specNorm_add_le _ _).trans ?_
      rw [specNorm_smul, specNorm_one, mul_one, Complex.norm_real, Real.norm_of_nonneg
        (by linarith)]

/-- The class event of $\mathbf{M}$ is contained in the union of the gap and the condition events
of the shift $\mathbf{M} + s\mathbf{I}$: a diagonalization of the shifted matrix shifts back,
and its diagonal is a listing, a permutation of any other. -/
private theorem subset_class_shift {Ω : Type} {n : Type} [Fintype n] [DecidableEq n]
    {G : Ω → Matrix n n ℂ} (M : Matrix n n ℂ) (s : ℂ) {β t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) :
    {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧ (M + β • G ω) * V = V * Matrix.diagonal d ∧
        pseudoConditionNumber V ≤ t₂⁻¹ ∧ ∀ i j, i ≠ j → t₁ ≤ ‖d i - d j‖} ⊆
      {ω | ¬ ∃ d : n → ℂ, IsEigenvalueListing (M + s • 1 + β • G ω) d ∧
          ∀ i j, i ≠ j → t₁ < ‖d i - d j‖} ∪
        {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
          (M + s • 1 + β • G ω) * V = V * Matrix.diagonal d ∧ pseudoConditionNumber V ≤ t₂⁻¹} := by
  intro ω hω
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  obtain ⟨⟨d₁, hd₁, hgap⟩, ⟨V, d, hV, hVd, hκ⟩⟩ := hc
  have hd := isEigenvalueListing_of_mul_eq_mul_diagonal ((Matrix.isUnit_iff_isUnit_det V).mp hV)
    hVd
  obtain ⟨e, he⟩ := hd₁.exists_equiv_eq hd
  refine hω ⟨V, fun i => d i - s, hV, ?_, hκ, fun i j hij => ?_⟩
  · have hdiag : Matrix.diagonal (fun i => d i - s) = Matrix.diagonal d - s • 1 := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, h]
    rw [hdiag, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← hVd]
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
    abel
  · have h := hgap (e.symm i) (e.symm j) (e.symm.injective.ne hij)
    simp only [he, Function.comp_apply, Equiv.apply_symm_apply] at h
    simpa using h.le

/-- **A Ginibre perturbation is in the diagonalization class** ([BanksGarzaVargasSrivastava2025,
Lemma 6.5], in class form): let the tails $c_1$ (gap) and $c_2$ (condition) hold, with
normalized records $\bar c_1, \bar c_2$. For every standard complex Gaussian $\mathbf{G}$ of order
$n$, every $\mathbf{M}$ (no norm condition), $\gamma > 0$, $0 < t_1 \le \gamma$ and
$0 < t_2 \le 1$, with $K = (\|\mathbf{M}\|_2 + 4\gamma)/\gamma$, the probability that
$\mathbf{M} + \gamma n^{-1/2}\mathbf{G}$ has no diagonalization
$\mathbf{V}\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le t_2^{-1}$ and $\lvert d_i - d_j\rvert \ge t_1$ for
$i \ne j$ is at most
$$\bar C_1 n^{\bar a_1}(t_1/\gamma)^{\bar b_1}(K + \log(\gamma/t_1))^{\bar c_1} +
  \bar C_2 n^{\bar a_2}t_2^{\bar b_2}(K + \log(1/t_2))^{\bar c_2}\,.$$
When $\|\mathbf{M}\|_2 < 2\gamma$ the tails are applied to $\mathbf{M} + 4\gamma\mathbf{I}$, whose
diagonalizations are those of $\mathbf{M}$ shifted. -/
theorem measureReal_not_exists_class_le_of_hasLaw_complexGaussianMatrix {c₁ c₂ : PolyLogTail}
    (hA : ComplexGaussianGapTail c₁) (hB : ComplexGaussianConditionTail c₂) {Ω : Type}
    {_mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type} [Fintype n] [DecidableEq n]
    {G : Ω → Matrix n n ℂ} (hG : HasLaw G (complexGaussianMatrix n n) μ) (M : Matrix n n ℂ)
    {γ t₁ t₂ : ℝ} (hγ : 0 < γ) (ht₁ : 0 < t₁) (ht₁γ : t₁ ≤ γ) (ht₂ : 0 < t₂) (ht₂1 : t₂ ≤ 1) :
    μ.real {ω | ¬ ∃ (V : Matrix n n ℂ) (d : n → ℂ), IsUnit V ∧
      (M + (γ / √(Fintype.card n : ℝ)) • G ω) * V = V * Matrix.diagonal d ∧
        pseudoConditionNumber V ≤ t₂⁻¹ ∧ ∀ i j, i ≠ j → t₁ ≤ ‖d i - d j‖} ≤
      c₁.normalize.C * (Fintype.card n : ℝ) ^ c₁.normalize.a * (t₁ / γ) ^ c₁.normalize.b *
          ((specNorm M + 4 * γ) / γ + Real.log (γ / t₁)) ^ c₁.normalize.c +
        c₂.normalize.C * (Fintype.card n : ℝ) ^ c₂.normalize.a * t₂ ^ c₂.normalize.b *
          ((specNorm M + 4 * γ) / γ + Real.log t₂⁻¹) ^ c₂.normalize.c := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.mpr inferInstance
  have hL₁ : 0 ≤ Real.log (γ / t₁) := Real.log_nonneg ((one_le_div ht₁).mpr ht₁γ)
  have hL₂ : 0 ≤ Real.log t₂⁻¹ := Real.log_nonneg ((one_le_inv₀ ht₂).mpr ht₂1)
  have hK : 0 ≤ (specNorm M + 4 * γ) / γ := div_nonneg (by linarith [specNorm_nonneg M]) hγ.le
  have hT₁ := tail_nonneg c₁ (Fintype.card n) (div_nonneg ht₁.le hγ.le) (add_nonneg hK hL₁)
  have hT₂ := tail_nonneg c₂ (Fintype.card n) ht₂.le (add_nonneg hK hL₂)
  rcases isEmpty_or_nonempty n with hn | hn
  · have h1 : (1 : Matrix n n ℂ) = 0 := Subsingleton.elim _ _
    have hκ : pseudoConditionNumber (1 : Matrix n n ℂ) ≤ t₂⁻¹ := by
      simp [pseudoConditionNumber, h1, ht₂.le]
    refine (measureReal_mono (s₂ := ∅) ?_).trans ?_
    · intro ω hω
      change ¬ _ at hω
      exact hω ⟨1, 1, isUnit_one, Subsingleton.elim _ _, hκ, fun i => isEmptyElim i⟩
    · rw [measureReal_empty]
      exact add_nonneg hT₁ hT₂
  obtain ⟨s, hs₁, hs₂⟩ := exists_shift_specNorm hγ M
  set M' := M + s • (1 : Matrix n n ℂ)
  refine (measureReal_mono (subset_class_shift (G := G) M s ht₁.le)).trans
    ((measureReal_union_le _ _).trans (add_le_add ?_ ?_))
  · refine (hA.normalize hG M' hγ hs₁ ht₁ ht₁γ).trans
      (tail_mono_base c₁ (Fintype.card n) (div_nonneg ht₁.le hγ.le) ?_ ?_)
    · exact add_nonneg (div_nonneg (specNorm_nonneg _) hγ.le) hL₁
    · linarith [(div_le_div_iff_of_pos_right hγ).mpr hs₂]
  · refine (hB.normalize hG M' hγ hs₁ ht₂ ht₂1).trans
      (tail_mono_base c₂ (Fintype.card n) ht₂.le ?_ ?_)
    · exact add_nonneg (div_nonneg (specNorm_nonneg _) hγ.le) hL₂
    · linarith [(div_le_div_iff_of_pos_right hγ).mpr hs₂]

/-! ### Inverting a tail -/

/-- The scale of a normalized tail record $c$ at the order $N$ and the norm ratio $K$:
$C N^a (K + 1)^c (1 + 2c/b)^c e^{b/2}$, which bounds $C N^a \tau^{b/2}(K + \log(1/\tau))^c$ for
$0 < \tau \le 1$. -/
noncomputable def polyLogTailScale (c : PolyLogTail) (N K : ℝ) : ℝ :=
  c.C * N ^ c.a * (K + 1) ^ c.c * ((1 + 2 * c.c / c.b) ^ c.c * Real.exp (c.b / 2))

/-- The parameter $\tau = \min(1, (\varphi/s)^{2/b})$, $s$ the scale
`NLAlib.polyLogTailScale` of $c$ at $N$ and $K$: at it the tail of a normalized record with
$b > 0$ is at most $\varphi$. -/
noncomputable def polyLogTailInverse (c : PolyLogTail) (N K φ : ℝ) : ℝ :=
  min 1 ((φ / polyLogTailScale c N K) ^ (2 / c.b))


/-- $(1 + L)^c \le (1 + 2c/b)^c e^{\Lambda}$ for $L = 2\Lambda/b$, $\Lambda \ge 0$, $b > 0$ and
$c \ge 0$: the polylogarithmic factor is absorbed by half of the exponent. -/
private theorem one_add_rpow_le_exp {b c Λ : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (hΛ : 0 ≤ Λ) :
    (1 + 2 / b * Λ) ^ c ≤ (1 + 2 * c / b) ^ c * Real.exp Λ := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa using Real.one_le_exp hΛ
  have hc0 := hc.ne'
  have hb0 := hb.ne'
  have h1 : 1 + 2 / b * Λ ≤ (1 + 2 * c / b) * Real.exp (Λ / c) := by
    have he := Real.add_one_le_exp (Λ / c)
    have e1 : (1 + 2 * c / b) * (Λ / c + 1) = 1 + 2 / b * Λ + (Λ / c + 2 * c / b) := by
      field_simp
      ring
    have h2 : 0 ≤ Λ / c + 2 * c / b := by positivity
    nlinarith [mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 1 + 2 * c / b)]
  calc (1 + 2 / b * Λ) ^ c ≤ ((1 + 2 * c / b) * Real.exp (Λ / c)) ^ c :=
        Real.rpow_le_rpow (by positivity) h1 hc.le
    _ = (1 + 2 * c / b) ^ c * Real.exp Λ := by
        rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul,
          div_mul_cancel₀ _ hc.ne']

/-- The inverted tail of a record with $b > 0$, normalized: for $N \ge 1$, $K \ge 0$ and
$0 < \varphi \le 1$, the parameter $\tau$ = `NLAlib.polyLogTailInverse` is in $(0, 1]$, the
normalized tail $\bar C M^{\bar a}\tau^{b}(K + \log(1/\tau))^{\bar c}$ is at most $\varphi$ at every
$1 \le M \le N$, and $\log(1/\tau) = (2/b)\log(s/\varphi)$ for the scale $s$ =
`NLAlib.polyLogTailScale`. -/
theorem polyLogTailInverse_spec {c : PolyLogTail} (hb : 0 < c.b) {N K φ : ℝ} (hN : 1 ≤ N)
    (hK : 0 ≤ K) (hφ : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < polyLogTailInverse c.normalize N K φ ∧ polyLogTailInverse c.normalize N K φ ≤ 1 ∧
      (∀ M : ℝ, 1 ≤ M → M ≤ N →
        c.normalize.C * M ^ c.normalize.a * polyLogTailInverse c.normalize N K φ ^ c.normalize.b *
          (K + Real.log (polyLogTailInverse c.normalize N K φ)⁻¹) ^ c.normalize.c ≤ φ) ∧
      Real.log (polyLogTailInverse c.normalize N K φ)⁻¹ =
        2 / c.b * Real.log (polyLogTailScale c.normalize N K / φ) := by
  set d := c.normalize with hd
  have hC : 1 ≤ d.C := le_max_right _ _
  have ha : 0 ≤ d.a := le_max_right _ _
  have hc : 0 ≤ d.c := le_max_right _ _
  have hbn : d.b = c.b := rfl
  have hb0 := hb.ne'
  have hC0 : 0 ≤ d.C := zero_le_one.trans hC
  set s := polyLogTailScale d N K with hsdef
  have hNa : 1 ≤ N ^ d.a := Real.one_le_rpow hN ha
  have hKc : 1 ≤ (K + 1) ^ d.c := Real.one_le_rpow (by linarith) hc
  have hBc : 1 ≤ (1 + 2 * d.c / c.b) ^ d.c := Real.one_le_rpow (by
    have : 0 ≤ 2 * d.c / c.b := by positivity
    linarith) hc
  have hE : 1 < Real.exp (c.b / 2) := Real.one_lt_exp_iff.mpr (by positivity)
  have hs : 1 < s := by
    simp only [hsdef, polyLogTailScale, hbn]
    have h1 : 1 ≤ d.C * N ^ d.a * (K + 1) ^ d.c := by
      have := mul_le_mul hC hNa zero_le_one (by linarith)
      have := mul_le_mul this hKc zero_le_one (by positivity)
      linarith
    have h2 : 1 < (1 + 2 * d.c / c.b) ^ d.c * Real.exp (c.b / 2) := by nlinarith
    nlinarith
  set Λ := Real.log (s / φ)
  have hΛ : 0 < Λ := Real.log_pos ((one_lt_div hφ).mpr (by linarith))
  have hτ : polyLogTailInverse d N K φ = Real.exp (-(2 / c.b * Λ)) := by
    have e : (φ / s) ^ (2 / c.b) = Real.exp (-(2 / c.b * Λ)) := by
      rw [Real.rpow_def_of_pos (by positivity), show φ / s = (s / φ)⁻¹ by rw [inv_div],
        Real.log_inv]
      congr 1
      rw [show Real.log (s / φ) = Λ from rfl]
      ring
    rw [polyLogTailInverse, ← hsdef, hbn, e, min_eq_right (Real.exp_le_one_iff.mpr (by
      have : 0 < 2 / c.b * Λ := by positivity
      linarith))]
  have hL : Real.log (polyLogTailInverse d N K φ)⁻¹ = 2 / c.b * Λ := by
    rw [hτ, Real.log_inv, Real.log_exp, neg_neg]
  refine ⟨by rw [hτ]; exact Real.exp_pos _, by rw [hτ]; exact Real.exp_le_one_iff.mpr (by
    have : 0 < 2 / c.b * Λ := by positivity
    linarith), fun M hM hMN => ?_, ?_⟩
  · rw [hL, hτ, hbn, ← Real.exp_mul]
    have hMa : M ^ d.a ≤ N ^ d.a := Real.rpow_le_rpow (by linarith) hMN ha
    have hKL : (K + 2 / c.b * Λ) ^ d.c ≤ (K + 1) ^ d.c * (1 + 2 / c.b * Λ) ^ d.c := by
      rw [← Real.mul_rpow (by linarith) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith [mul_nonneg hK (by positivity :
        (0 : ℝ) ≤ 2 / c.b * Λ)]) hc
    have hOne := one_add_rpow_le_exp hb hc hΛ.le
    have e2 : -(2 / c.b * Λ) * c.b = -Λ + -Λ := by field_simp; ring
    have hφs : Real.exp (-Λ) = φ / s := by
      rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
    have hT : (K + 2 / c.b * Λ) ^ d.c ≤ (K + 1) ^ d.c * ((1 + 2 * d.c / c.b) ^ d.c * Real.exp Λ) :=
      hKL.trans (mul_le_mul_of_nonneg_left hOne (by positivity))
    rw [e2, Real.exp_add, hφs]
    have hMa0 : 0 ≤ M ^ d.a := Real.rpow_nonneg (by linarith) _
    have hs' : d.C * N ^ d.a * (K + 1) ^ d.c * (1 + 2 * d.c / c.b) ^ d.c ≤ s := by
      simp only [hsdef, polyLogTailScale, hbn]
      have : 0 ≤ d.C * N ^ d.a * (K + 1) ^ d.c * (1 + 2 * d.c / c.b) ^ d.c := by positivity
      nlinarith
    have hexp : Real.exp Λ * (φ / s) = 1 := by
      rw [← hφs, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc d.C * M ^ d.a * (φ / s * (φ / s)) * (K + 2 / c.b * Λ) ^ d.c
        ≤ d.C * N ^ d.a * (φ / s * (φ / s)) *
            ((K + 1) ^ d.c * ((1 + 2 * d.c / c.b) ^ d.c * Real.exp Λ)) := by
          gcongr
      _ = d.C * N ^ d.a * (K + 1) ^ d.c * (1 + 2 * d.c / c.b) ^ d.c * (φ / s) *
            (Real.exp Λ * (φ / s)) := by ring
      _ ≤ s * (φ / s) * 1 := by
          rw [hexp]
          gcongr
      _ = φ := by field_simp
  · rw [hL]

end NLAlib
