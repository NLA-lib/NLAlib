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

* `NLAlib.ComplexGaussianGapTail.normalize`, `NLAlib.ComplexGaussianConditionTail.normalize`.
* `NLAlib.exists_complexGaussianGapTail_iff`, `NLAlib.exists_complexGaussianConditionTail_iff`:
  the asymptotic forms are the existence of a record.
* `NLAlib.complexGaussianGapTail_of_preferred`,
  `NLAlib.complexGaussianConditionTail_of_preferred`: the preferred forms imply the tail forms.
* `NLAlib.measureReal_not_exists_class_le_of_hasLaw_complexGaussianMatrix`: the class event.
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

/-- A gap tail holds for its normalized record. -/
theorem ComplexGaussianGapTail.normalize {c : PolyLogTail} (h : ComplexGaussianGapTail c) :
    ComplexGaussianGapTail c.normalize := by
  sorry

/-- A condition tail holds for its normalized record. -/
theorem ComplexGaussianConditionTail.normalize {c : PolyLogTail}
    (h : ComplexGaussianConditionTail c) : ComplexGaussianConditionTail c.normalize := by
  sorry

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
  sorry

/-- The preferred condition form is the condition tail with the record $(18, 3, 2, 2)$: in the
range $2\gamma \le \|\mathbf{M}\|_2$, $2\sqrt2 + 1 \le 1.92\|\mathbf{M}\|_2/\gamma$ and
$\sqrt{4L} \le L + 1$. -/
theorem complexGaussianConditionTail_of_preferred (h : ComplexGaussianConditionPreferred) :
    ComplexGaussianConditionTail ⟨18, 3, 2, 2⟩ := by
  sorry

/-! ### The class event -/

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
  sorry

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

end NLAlib
