/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Basic
public import NLAlib.Ops.ArithmeticError
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Accumulated rounding errors

The rounding factor <!-- value Computation.roundingFactor n u --> $\gamma_n = (1 - u)^{-n} - 1$,
`NLAlib.Computation.roundingFactor n u`, of [CarsonMaShao2026, (3)], and its algebra: a product
of $n$ factors $(1 + \delta_i)^{\pm 1}$ with $\lvert \delta_i \rvert \le u < 1$ is
$1 + \theta_n$ with $\lvert \theta_n \rvert \le \gamma_n$, with no condition on $nu$, and the
composition rule $(1 + \gamma_k)(1 + \gamma_j) = 1 + \gamma_{k+j}$ holds with equality. It is at
most Higham's $nu/(1 - nu)$ when $nu < 1$ [Higham2002, §3.1]. A rounding error analysis
tracks the number of factors with `NLAlib.Computation.IsRoundingProduct` (closed under products,
inverses and ratios, the counts adding) and evaluates $\gamma_n$ only at the end. The relation
`NLAlib.Computation.RelErr u a z` says that $z$ is $a$ with relative error at most $u$, the error
clause of the standard model.

## Main definitions

* `NLAlib.Computation.roundingFactor`: $\gamma_n$.
* `NLAlib.Computation.RelErr`: relative error at most $u$.
* `NLAlib.Computation.IsRoundingProduct`: $1 + \theta$ is a product of $j$ factors
  $(1 + \delta_i)^{\pm 1}$, $\lvert \delta_i \rvert \le u$ (Higham's $\theta_j$).

## Main results

* `NLAlib.Computation.abs_prod_one_add_zpow_sub_one_le`: the product of $n$ factors
  $(1 + \delta_i)^{\pm 1}$ is $1 + \theta_n$, $\lvert \theta_n \rvert \le \gamma_n$, for $u < 1$.
* `NLAlib.Computation.roundingFactor_add_add_mul`:
  $\gamma_k + \gamma_j + \gamma_k\gamma_j = \gamma_{k+j}$.
* `NLAlib.Computation.abs_one_add_mul_one_add_sub_one_le`: $(1 + \theta_k)(1 + \theta_j) =
  1 + \theta_{k+j}$.
* `NLAlib.Computation.roundingFactor_le`: $\gamma_n \le nu/(1 - nu)$ for $nu < 1$.
* `NLAlib.Computation.IsRoundingProduct.abs_le`, `NLAlib.Computation.IsRoundingProduct.mul`,
  `NLAlib.Computation.IsRoundingProduct.inv`, `NLAlib.Computation.IsRoundingProduct.div`:
  [Higham2002, Lemma 3.3] for products of rounding errors, with the ratio rule
  $(1 + \theta_k)/(1 + \theta_j) = 1 + \theta_{k+j}$ for all $j$, $k$.
* `NLAlib.Computation.isRoundingProduct_iff`: the values $1 + \theta_j$ fill the interval
  $[(1 - u)^j, (1 - u)^{-j}]$.
* `NLAlib.Computation.exists_isRoundingProduct_sum_mul_one_add_eq`: a weighted mean of
  $1 + \theta_j$'s is a $1 + \theta_j$.
-/

@[expose] public section

namespace NLAlib.Computation

/-- **The accumulated rounding factor** <!-- value Computation.roundingFactor n u -->
$\gamma_n = (1 - u)^{-n} - 1$ of [CarsonMaShao2026, (3)], the bound on $n$ accumulated relative
errors of size at most $u$, in the standard model and in the model
$\mathrm{fl}(x \circ y) = (x \circ y)/(1 + \delta)$. It is finite for every $n$ when $u < 1$,
and at most Higham's $nu/(1 - nu)$ when $nu < 1$. -/
noncomputable def roundingFactor (n : ℕ) (u : ℝ) : ℝ := ((1 - u) ^ n)⁻¹ - 1


variable {u : ℝ} {n k j : ℕ}

/-- **$\gamma_0 = 0$.** [CarsonMaShao2026, (3)]. -/
theorem roundingFactor_zero : roundingFactor 0 u = 0 := by
  simp [roundingFactor]

/-- **$1 + \gamma_n = (1 - u)^{-n}$.** [CarsonMaShao2026, (3)]. -/
theorem one_add_roundingFactor : 1 + roundingFactor n u = ((1 - u) ^ n)⁻¹ := by
  rw [roundingFactor]
  ring

/-- **$\gamma_1 = u/(1 - u)$** for $u \ne 1$. [CarsonMaShao2026, (3)]. -/
theorem roundingFactor_one (hu1 : u ≠ 1) : roundingFactor 1 u = u / (1 - u) := by
  have : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  rw [roundingFactor, pow_one]
  field_simp
  ring

/-- **$\gamma_n \ge 0$** for $0 \le u < 1$. [CarsonMaShao2026, (3)]. -/
theorem roundingFactor_nonneg (hu : 0 ≤ u) (hu1 : u < 1) :
    0 ≤ roundingFactor n u := by
  rw [roundingFactor, sub_nonneg]
  exact (one_le_inv₀ (pow_pos (by linarith) n)).mpr (pow_le_one₀ (by linarith) (by linarith))

/-- The accumulated factor is nonnegative under $nu<1$, including $n=0$ without
requiring $u<1$. This retains empty-kernel cases in dimension-dependent error bounds. -/
theorem roundingFactor_nonneg_of_mul_lt_one (hu : 0 ≤ u) (hn : (n : ℝ) * u < 1) :
    0 ≤ roundingFactor n u := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [roundingFactor_zero]
  · exact roundingFactor_nonneg hu
      ((le_mul_of_one_le_left hu (by exact_mod_cast hn0)).trans_lt hn)

/-- **$\gamma_1 \ge u$**, so a single rounding error is within $\gamma_1$: for
$u < 1$, $u \le \gamma_1$. [CarsonMaShao2026, (3)]. -/
theorem le_roundingFactor_one (hu1 : u < 1) : u ≤ roundingFactor 1 u := by
  rw [roundingFactor_one hu1.ne, le_div_iff₀ (by linarith)]
  nlinarith [sq_nonneg u]

/-- **Adding accumulated errors is exact** [CarsonMaShao2026, Lemma 2], (10) there: for every
$u$, $\gamma_k + \gamma_j + \gamma_k\gamma_j =
\gamma_{k+j}$, that is, $(1 + \gamma_k)(1 + \gamma_j) =
1 + \gamma_{k+j}$. -/
theorem roundingFactor_add_add_mul :
    roundingFactor k u + roundingFactor j u +
        roundingFactor k u * roundingFactor j u =
      roundingFactor (k + j) u := by
  simp only [roundingFactor, pow_add, mul_inv]
  ring

/-- **$\gamma_n$ is monotone in $n$**: for $0 \le u < 1$ and $k \le n$,
$\gamma_k \le \gamma_n$. [CarsonMaShao2026, Lemma 2]. -/
theorem roundingFactor_le_roundingFactor (hu : 0 ≤ u) (hu1 : u < 1)
    (hkn : k ≤ n) : roundingFactor k u ≤ roundingFactor n u := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [← roundingFactor_add_add_mul]
  have := roundingFactor_nonneg (n := k) hu hu1
  have := roundingFactor_nonneg (n := m) hu hu1
  nlinarith

/-- **Composing accumulated errors** [CarsonMaShao2026, Lemma 2]: for every $u$, if
$\lvert \theta \rvert \le \gamma_k$ and $\lvert \theta' \rvert \le \gamma_j$,
then $\lvert (1 + \theta)(1 + \theta') - 1 \rvert \le \gamma_{k+j}$. -/
theorem abs_one_add_mul_one_add_sub_one_le {θ θ' : ℝ}
    (hθ : |θ| ≤ roundingFactor k u) (hθ' : |θ'| ≤ roundingFactor j u) :
    |(1 + θ) * (1 + θ') - 1| ≤ roundingFactor (k + j) u := by
  calc |(1 + θ) * (1 + θ') - 1| = |θ + θ' + θ * θ'| := by ring_nf
    _ ≤ |θ| + |θ'| + |θ| * |θ'| := by
      rw [← abs_mul]; exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ roundingFactor k u + roundingFactor j u +
        roundingFactor k u * roundingFactor j u := by
      gcongr; exact (abs_nonneg _).trans hθ
    _ = roundingFactor (k + j) u := roundingFactor_add_add_mul

/-- **Scaling the index** [CarsonMaShao2026, Lemma 2]: for $0 \le u < 1$,
$i\gamma_k \le \gamma_{ik}$. -/
theorem mul_roundingFactor_le (i : ℕ) (hu : 0 ≤ u) (hu1 : u < 1) :
    i * roundingFactor k u ≤ roundingFactor (i * k) u := by
  have h0 := roundingFactor_nonneg (n := k) hu hu1
  have hb := one_add_mul_le_pow (a := roundingFactor k u) (by linarith) i
  have hp : (1 + roundingFactor k u) ^ i = 1 + roundingFactor (i * k) u := by
    rw [one_add_roundingFactor, one_add_roundingFactor, inv_pow, ← pow_mul,
      Nat.mul_comm k i]
  linarith

/-- **One more rounding** [CarsonMaShao2026, Lemma 2]: for $0 \le u < 1$,
$\gamma_k + u \le \gamma_{k+1}$. -/
theorem roundingFactor_add_le (hu : 0 ≤ u) (hu1 : u < 1) :
    roundingFactor k u + u ≤ roundingFactor (k + 1) u := by
  have h1 := le_roundingFactor_one hu1
  have := mul_nonneg (roundingFactor_nonneg (n := k) hu hu1)
    (roundingFactor_nonneg (n := 1) hu hu1)
  linarith [roundingFactor_add_add_mul (k := k) (j := 1) (u := u)]

/-- **The rounding factor bounds $n$ rounding errors upward**: for $0 \le u < 1$,
$(1 + u)^n - 1 \le \gamma_n$, as $(1 + u)(1 - u) \le 1$. [CarsonMaShao2026, §2]. -/
theorem one_add_pow_sub_one_le_roundingFactor (hu : 0 ≤ u) (hu1 : u < 1) :
    (1 + u) ^ n - 1 ≤ roundingFactor n u := by
  have h1u : 0 < (1 - u) ^ n := pow_pos (by linarith) n
  rw [roundingFactor, sub_le_sub_iff_right, ← one_div, le_div_iff₀ h1u, ← mul_pow]
  exact pow_le_one₀ (by nlinarith) (by nlinarith)

/-- $\gamma_n \ge nu$ for $0 \le u < 1$: $1 + nu \le (1 + u)^n \le (1 - u)^{-n}$. -/
theorem le_roundingFactor (hu : 0 ≤ u) (hu1 : u < 1) : n * u ≤ roundingFactor n u := by
  linarith [one_add_mul_le_pow (a := u) (by linarith) n,
    one_add_pow_sub_one_le_roundingFactor (n := n) hu hu1]

/-- **The rounding factor is at most Higham's** [CarsonMaShao2026, §2]: for $0 \le u$ and
$nu < 1$, $\gamma_n \le nu/(1 - nu)$, the constant of [Higham2002, §3.1], by Bernoulli's
inequality $1 - nu \le (1 - u)^n$. -/
theorem roundingFactor_le (hu : 0 ≤ u) (hn : n * u < 1) :
    roundingFactor n u ≤ n * u / (1 - n * u) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [roundingFactor]
  have hu1 : u < 1 := lt_of_le_of_lt (le_mul_of_one_le_left hu (by exact_mod_cast hn0)) hn
  have hbern : 1 - n * u ≤ (1 - u) ^ n := by
    simpa [sub_eq_add_neg] using one_add_mul_le_pow (a := -u) (by linarith) n
  have h := inv_anti₀ (by linarith) hbern
  have he : n * u / (1 - n * u) = (1 - n * u)⁻¹ - 1 := by
    field_simp [show 1 - n * u ≠ 0 by linarith]; ring
  rw [roundingFactor, he]
  linarith

/-- A factor $(1 + \delta)^{\pm 1}$ with $\lvert \delta \rvert \le u < 1$ lies in
$[1 - u, (1 - u)^{-1}]$. -/
private theorem one_add_zpow_mem_Icc {δ : ℝ} {ρ : ℤ} (hδ : |δ| ≤ u) (hu1 : u < 1)
    (hρ : ρ = 1 ∨ ρ = -1) : 1 - u ≤ (1 + δ) ^ ρ ∧ (1 + δ) ^ ρ ≤ (1 - u)⁻¹ := by
  have h1u : 0 < 1 - u := by linarith
  have hu : 0 ≤ u := (abs_nonneg _).trans hδ
  have hinv : 1 + u ≤ (1 - u)⁻¹ := by
    rw [← one_div, le_div_iff₀ h1u]; nlinarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp hδ
  have hpos : 0 < 1 + δ := by linarith
  rcases hρ with h | h <;> simp only [h, zpow_one, zpow_neg]
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨(le_inv_comm₀ h1u hpos).mpr (by linarith), inv_anti₀ h1u (by linarith)⟩

/-- **Products of rounding errors** [CarsonMaShao2026, Lemma 2], (6) there: for
$\lvert \delta_i \rvert \le u < 1$ and exponents $\rho_i = \pm 1$ ($i$ in a finite set $s$ of
$n$ elements),
$$\Bigl\lvert \prod_{i \in s} (1 + \delta_i)^{\rho_i} - 1 \Bigr\rvert \le
\gamma_n\,.$$ No condition on $nu$ is needed. -/
theorem abs_prod_one_add_zpow_sub_one_le {ι : Type} (s : Finset ι)
    (δ : ι → ℝ) (ρ : ι → ℤ) (hδ : ∀ i ∈ s, |δ i| ≤ u) (hρ : ∀ i ∈ s, ρ i = 1 ∨ ρ i = -1)
    (hu1 : u < 1) :
    |∏ i ∈ s, (1 + δ i) ^ ρ i - 1| ≤ roundingFactor s.card u := by
  have h1u : 0 < 1 - u := by linarith
  have hfac := fun i hi => one_add_zpow_mem_Icc (hδ i hi) hu1 (hρ i hi)
  have hlo : (1 - u) ^ s.card ≤ ∏ i ∈ s, (1 + δ i) ^ ρ i := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => h1u.le) (fun i hi => (hfac i hi).1)
  have hhi : ∏ i ∈ s, (1 + δ i) ^ ρ i ≤ ((1 - u) ^ s.card)⁻¹ := by
    rw [← inv_pow, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun i hi => h1u.le.trans (hfac i hi).1) (fun i hi => (hfac i hi).2)
  -- `1 - a ≤ a⁻¹ - 1` for `a = (1 - u)^n ∈ (0, 1]`
  have hp : 0 < (1 - u) ^ s.card := pow_pos h1u _
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp [roundingFactor]
  have hu : 0 ≤ u := (abs_nonneg _).trans (hδ i₀ hi₀)
  have hp1 : (1 - u) ^ s.card ≤ 1 := pow_le_one₀ h1u.le (by linarith)
  have hinv : 1 ≤ ((1 - u) ^ s.card)⁻¹ := (one_le_inv₀ hp).mpr hp1
  have hsym : 1 - (1 - u) ^ s.card ≤ ((1 - u) ^ s.card)⁻¹ - 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hinv), mul_inv_cancel₀ hp.ne']
  rw [roundingFactor, abs_le]
  constructor <;> linarith

/-! ### Products of rounding errors -/

/-- `IsRoundingProduct u j θ`: $1 + \theta = \prod_{i<j} (1 + \delta_i)^{\rho_i}$ for some
$\lvert \delta_i \rvert \le u$ and $\rho_i = \pm 1$, the quantity $\theta_j$ of
[Higham2002, Lemma 3.1]. Unlike the bound $\lvert \theta \rvert \le \gamma_j$ for $u < 1$
(`NLAlib.Computation.IsRoundingProduct.abs_le`), the predicate is closed under inversion with
the same $j$. -/
def IsRoundingProduct (u : ℝ) (j : ℕ) (θ : ℝ) : Prop :=
  ∃ (δ : Fin j → ℝ) (ρ : Fin j → ℤ), (∀ i, |δ i| ≤ u) ∧ (∀ i, ρ i = 1 ∨ ρ i = -1) ∧
    ∏ i, (1 + δ i) ^ ρ i = 1 + θ

variable {θ θ' : ℝ}

/-- **The empty product**: $\theta_0 = 0$. [Higham2002, Lemma 3.1]. -/
theorem isRoundingProduct_zero : IsRoundingProduct u 0 0 :=
  ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩

/-- **One rounding error** is a product of one factor: $\lvert \delta \rvert \le u$ gives
$\theta_1 = \delta$. [Higham2002, Lemma 3.1]. -/
theorem isRoundingProduct_one_of_abs_le (hθ : |θ| ≤ u) : IsRoundingProduct u 1 θ :=
  ⟨fun _ => θ, fun _ => 1, fun _ => hθ, fun _ => Or.inl rfl, by simp⟩

/-- **Products of rounding errors are bounded by $\gamma_j$**
[CarsonMaShao2026, Lemma 2], (6) there: if $1 + \theta$ is a product of $j$ factors
$(1 + \delta_i)^{\pm 1}$ with $\lvert \delta_i \rvert \le u$ and $u < 1$, then
$\lvert \theta \rvert \le \gamma_j$, with no condition on $ju$. -/
theorem IsRoundingProduct.abs_le (h : IsRoundingProduct u j θ)
    (hu1 : u < 1) : |θ| ≤ roundingFactor j u := by
  obtain ⟨δ, ρ, hδ, hρ, he⟩ := h
  have := abs_prod_one_add_zpow_sub_one_le Finset.univ δ ρ
    (fun i _ => hδ i) (fun i _ => hρ i) hu1
  simpa [he] using this

/-- **Multiplying products of rounding errors** [Higham2002, Lemma 3.3]:
$(1 + \theta_k)(1 + \theta_j) = 1 + \theta_{k+j}$. -/
theorem IsRoundingProduct.mul (h : IsRoundingProduct u k θ) (h' : IsRoundingProduct u j θ') :
    IsRoundingProduct u (k + j) ((1 + θ) * (1 + θ') - 1) := by
  obtain ⟨δ, ρ, hδ, hρ, he⟩ := h
  obtain ⟨δ', ρ', hδ', hρ', he'⟩ := h'
  refine ⟨Fin.append δ δ', Fin.append ρ ρ', fun i => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hδ, hδ']
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hρ, hρ']
  · rw [Fin.prod_univ_add]
    simp [he, he']

/-- **Inverting a product of rounding errors** keeps its length:
$(1 + \theta_j)^{-1} = 1 + \theta_j$ [Higham2002, Lemma 3.3]. -/
theorem IsRoundingProduct.inv (h : IsRoundingProduct u j θ) :
    IsRoundingProduct u j ((1 + θ)⁻¹ - 1) := by
  obtain ⟨δ, ρ, hδ, hρ, he⟩ := h
  refine ⟨δ, -ρ, hδ, fun i => by rcases hρ i with h | h <;> simp [h], ?_⟩
  simp [zpow_neg, Finset.prod_inv_distrib, he]

/-- **The ratio of products of rounding errors** [Higham2002, Lemma 3.3]:
$(1 + \theta_k)/(1 + \theta_j) = 1 + \theta_{k+j}$, for all $j$ and $k$. -/
theorem IsRoundingProduct.div (h : IsRoundingProduct u k θ) (h' : IsRoundingProduct u j θ') :
    IsRoundingProduct u (k + j) ((1 + θ) / (1 + θ') - 1) := by
  simpa [div_eq_mul_inv] using h.mul h'.inv

/-- **An inverted rounding error** is within $\gamma_1 = u/(1 - u)$ of $1$: for
$\lvert \delta \rvert \le u < 1$, $\lvert (1 + \delta)^{-1} - 1 \rvert \le \gamma_1$.
[CarsonMaShao2026, Lemma 2]. -/
theorem abs_inv_one_add_sub_one_le {δ : ℝ} (hδ : |δ| ≤ u) (hu1 : u < 1) :
    |(1 + δ)⁻¹ - 1| ≤ roundingFactor 1 u := by
  simpa using ((isRoundingProduct_one_of_abs_le hδ).inv).abs_le hu1

/-- **A shorter product is a longer one**: for $0 \le u$ and $j \le k$, $1 + \theta_j$ is a
$1 + \theta_k$ (pad with factors $1 + 0$). [Higham2002, Lemma 3.1]. -/
theorem IsRoundingProduct.mono (h : IsRoundingProduct u j θ) (hu : 0 ≤ u) (hjk : j ≤ k) :
    IsRoundingProduct u k θ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  have h0 : IsRoundingProduct u m 0 :=
    ⟨fun _ => 0, fun _ => 1, fun _ => by simpa using hu, fun _ => Or.inl rfl, by simp⟩
  simpa using h.mul h0

/-- **The values of a product of rounding errors** [Higham2002, Lemma 3.1]: for
$0 \le u < 1$, $1 + \theta$ is a product of $j$ factors $(1 + \delta_i)^{\pm 1}$ with
$\lvert \delta_i \rvert \le u$ exactly when $(1 - u)^j \le 1 + \theta \le (1 - u)^{-j}$. -/
theorem isRoundingProduct_iff (hu : 0 ≤ u) (hu1 : u < 1) :
    IsRoundingProduct u j θ ↔ (1 - u) ^ j ≤ 1 + θ ∧ 1 + θ ≤ ((1 - u) ^ j)⁻¹ := by
  have h1u : 0 < 1 - u := by linarith
  constructor
  · rintro ⟨δ, ρ, hδ, hρ, he⟩
    rw [← he]
    have hfac := fun i => one_add_zpow_mem_Icc (hδ i) hu1 (hρ i)
    constructor
    · simpa using Finset.prod_le_prod (s := Finset.univ) (fun _ _ => h1u.le)
        (fun i _ => (hfac i).1)
    · rw [← inv_pow]
      simpa using Finset.prod_le_prod (s := Finset.univ) (fun i _ => h1u.le.trans (hfac i).1)
        (fun i _ => (hfac i).2)
  rintro ⟨hlo, hhi⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have : θ = 0 := by simp at hlo hhi; linarith
    exact this ▸ isRoundingProduct_zero
  have hpj : 0 < (1 - u) ^ j := pow_pos h1u j
  have hj0 : j ≠ 0 := hj.ne'
  -- a `y ∈ [(1 - u)^j, 1]` is `r^j` with `r = y^{1/j} ∈ [1 - u, 1]`
  have root : ∀ y, (1 - u) ^ j ≤ y → y ≤ 1 → ∃ r, |r - 1| ≤ u ∧ r ^ j = y := by
    intro y hy1 hy2
    have hy0 : 0 ≤ y := hpj.le.trans hy1
    refine ⟨y ^ (j⁻¹ : ℝ), abs_le.mpr ⟨?_, ?_⟩, Real.rpow_inv_natCast_pow hy0 hj0⟩
    · have := Real.rpow_le_rpow hpj.le hy1 (by positivity : (0 : ℝ) ≤ (j : ℝ)⁻¹)
      rw [Real.pow_rpow_inv_natCast h1u.le hj0] at this
      linarith
    · have := Real.rpow_le_rpow hy0 hy2 (by positivity : (0 : ℝ) ≤ (j : ℝ)⁻¹)
      rw [Real.one_rpow] at this
      linarith
  rcases le_or_gt (1 + θ) 1 with hle | hgt
  · obtain ⟨r, hr, hrj⟩ := root (1 + θ) hlo hle
    exact ⟨fun _ => r - 1, fun _ => 1, fun _ => hr, fun _ => Or.inl rfl, by simp [hrj]⟩
  · have hpos : 0 < 1 + θ := by linarith
    obtain ⟨r, hr, hrj⟩ := root (1 + θ)⁻¹ (by rw [le_inv_comm₀ hpj hpos]; exact hhi)
      (inv_le_one_of_one_le₀ hgt.le)
    exact ⟨fun _ => r - 1, fun _ => -1, fun _ => hr, fun _ => Or.inr rfl,
      by simp [hrj]⟩

/-- **A weighted mean of products of rounding errors** is one: for $0 \le u < 1$, weights
$w_i \ge 0$ and $1 + \theta_i$ products of $j$ factors $(1 + \delta)^{\pm 1}$,
$\sum_i w_i(1 + \theta_i) = \bigl(\sum_i w_i\bigr)(1 + \theta)$ with $1 + \theta$ again such a
product, as the values fill an interval (`NLAlib.Computation.isRoundingProduct_iff`). This is
how [Higham2002, §3.1] passes from (3.4) to a single $\theta_j$ for a sum of nonnegative
terms. -/
theorem exists_isRoundingProduct_sum_mul_one_add_eq {ι : Type} (hu : 0 ≤ u) (hu1 : u < 1)
    (s : Finset ι) (w θs : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hθ : ∀ i ∈ s, IsRoundingProduct u j (θs i)) :
    ∃ θ, IsRoundingProduct u j θ ∧ ∑ i ∈ s, w i * (1 + θs i) = (∑ i ∈ s, w i) * (1 + θ) := by
  have hpj : 0 < (1 - u) ^ j := pow_pos (by linarith) j
  have hb := fun i hi => (isRoundingProduct_iff hu hu1).mp (hθ i hi)
  have hW : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  rcases hW.eq_or_lt with hW0 | hWpos
  · refine ⟨0, isRoundingProduct_zero.mono hu (Nat.zero_le j), ?_⟩
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hW0.symm
    rw [← hW0, zero_mul]
    exact Finset.sum_eq_zero fun i hi => by rw [hz i hi, zero_mul]
  refine ⟨(∑ i ∈ s, w i * (1 + θs i)) / ∑ i ∈ s, w i - 1,
    (isRoundingProduct_iff hu hu1).mpr ⟨?_, ?_⟩, ?_⟩
  · rw [add_sub_cancel, le_div_iff₀ hWpos, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hb i hi).1 (hw i hi)
  · rw [add_sub_cancel, div_le_iff₀ hWpos, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [mul_comm ((1 - u) ^ j)⁻¹]
    exact mul_le_mul_of_nonneg_left (hb i hi).2 (hw i hi)
  · rw [add_sub_cancel, mul_div_cancel₀ _ hWpos.ne']

end NLAlib.Computation
