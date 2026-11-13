/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.ArithmeticOperation
public import NLAlib.Matrix.FinitePrecision.Rounding
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Rounding traces of the BLAS kernels

A run of a kernel under an error contract computes, in decoded values, a **trace**: the sequence
of intermediate values of the kernel's recursion, each operation's result related to the exact
result on the previous values by an error relation `err`. The run lemmas of
the stored-operation analyses
identify actual intermediate values with such traces; this file bounds traces without
assuming a program execution. Under the
standard model (`err` the relation `NLAlib.Computation.RelErr u` of relative error) the
bounds are those of [Higham2002, Chapters 3 and 8] with the rounding factor
$\gamma_n = (1 - u)^{-n} - 1$ of [CarsonMaShao2026], under $u < 1$ alone. A model with underflow
reuses them: an absolute error in a multiplication or division is pushed onto its operands.

## Main definitions

* `NLAlib.Computation.IsDotTrace`: recursive accumulation of $\sum_k x_k y_k$, as `dot` and
  each row of `gemv` and `gemm` compute it.
* `NLAlib.Computation.IsSubstRowTrace`, `NLAlib.Computation.IsSubstTrace`: forward
  substitution, as `trsvLower` computes it.

## Main results

* `NLAlib.Computation.IsDotTrace.exists_eq_sum_mul_one_add`: backward error of an inner
  product, [Higham2002, §3.1].
* `NLAlib.Computation.IsDotTrace.exists_eq_sum_mul_one_add_isRoundingProduct`: the same with
  each $1 + \eta_k$ a product of rounding factors.
* `NLAlib.Computation.IsDotTrace.abs_sum_mul_sub_le`: forward error of an inner product.
* `NLAlib.Computation.exists_eq_mul_one_add_add_mul_one_add_of_relErr`: one `axpy` entry.
* `NLAlib.Computation.IsSubstTrace.exists_sum_add_mul_eq`: backward error of forward
  substitution, [Higham2002, Theorem 8.5].
-/

@[expose] public section

namespace NLAlib.Computation

open Finset

/-- **A trace of recursive accumulation** of $\sum_{k<n} x_k y_k$ under the error relation
`err`: $s_0 = 0$ and, for each $k < n$, a product $q_k$ related by `err` to $x_k y_k$ and
$s_{k+1}$ related by `err` to $s_k + q_k$, equal to $q_k$ when $s_k = 0$ (adding zero is
exact). This is what `dot` computes, and what `gemv` computes in each entry. -/
def IsDotTrace (err : BinOp → ℝ → ℝ → Prop) (x y : ℕ → ℝ) (n : ℕ) (s : ℕ → ℝ) : Prop :=
  s 0 = 0 ∧ ∀ k < n, ∃ q : ℝ, err .mul (x k * y k) q ∧ err .add (s k + q) (s (k + 1)) ∧
    (s k = 0 → s (k + 1) = q)

/-- **A partial trace of one row of forward substitution**: row $i$ of the lower triangular
system with entries $t_{ij}$, right side $b$ and computed solution $x$, after $k$ steps, under
the error relation `err`: $s_0 = b_i$ and, for each $j < k$, a product $q_j$ related to
$t_{ij}x_j$ and $s_{j+1}$ related to $s_j - q_j$. -/
def IsSubstRowTrace (err : BinOp → ℝ → ℝ → Prop) (t : ℕ → ℕ → ℝ) (b x : ℕ → ℝ) (i k : ℕ)
    (s : ℕ → ℝ) : Prop :=
  s 0 = b i ∧ ∀ j < k, ∃ q : ℝ, err .mul (t i j * x j) q ∧ err .sub (s j - q) (s (j + 1))

/-- **A trace of forward substitution** for the lower triangular system with entries $t_{ij}$
and right side $b$, under the error relation `err`: for each row $i < n$, a full row trace $s$
(`NLAlib.Computation.IsSubstRowTrace` after $i$ steps) and $x_i$ related to $s_i/t_{ii}$. This is
what `trsvLower` computes. -/
def IsSubstTrace (err : BinOp → ℝ → ℝ → Prop) (t : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (n : ℕ)
    (x : ℕ → ℝ) : Prop :=
  ∀ i < n, ∃ s : ℕ → ℝ, IsSubstRowTrace err t b x i i s ∧ err .div (s i / t i i) (x i)

variable {u : ℝ} {n : ℕ}

/-- A rounding error of size at most $u < 1$ leaves $1 + \delta$ nonzero. -/
private theorem one_add_ne_zero_of_abs_le {δ : ℝ} (hδ : |δ| ≤ u) (hu1 : u < 1) : 1 + δ ≠ 0 := by
  have := neg_abs_le δ
  intro h
  linarith

/-- Choosing a witness for each index below a bound. -/
private theorem exists_fun_of_forall_lt {α : Type} [Nonempty α] {k : ℕ} {Q : ℕ → α → Prop}
    (h : ∀ j < k, ∃ a, Q j a) : ∃ f : ℕ → α, ∀ j < k, Q j (f j) := by
  classical
  refine ⟨fun j => if hj : j < k then (h j hj).choose else Classical.arbitrary α, fun j hj => ?_⟩
  simp only [dif_pos hj]
  exact (h j hj).choose_spec

/-- The invariant of a trace of recursive accumulation: after $k \le n$ steps,
$s_k = \sum_{j<k} x_j y_j (1 + \eta_j)$ with each $1 + \eta_j$ a product of $k$ rounding
factors. -/
private theorem IsDotTrace.exists_eq_sum_of_le {x y s : ℕ → ℝ}
    (h : IsDotTrace (fun _ => RelErr u) x y n s) (hu : 0 ≤ u) :
    ∀ k ≤ n, ∃ η : ℕ → ℝ, (∀ j < k, IsRoundingProduct u k (η j)) ∧
      s k = ∑ j ∈ range k, x j * y j * (1 + η j) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨0, by simp, by simp [h.1]⟩
  | succ k ih =>
    intro hk
    obtain ⟨η, hη, hs⟩ := ih (by omega)
    obtain ⟨q, ⟨δ, hδ, rfl⟩, ⟨ε, hε, hs₁⟩, h0⟩ := h.2 k (by omega)
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · refine ⟨fun _ => δ, fun j _ => isRoundingProduct_one_of_abs_le hδ, ?_⟩
      rw [h0 h.1]
      simp
    refine ⟨fun j => if j < k then (1 + η j) * (1 + ε) - 1 else (1 + δ) * (1 + ε) - 1,
      fun j hj => ?_, ?_⟩
    · by_cases hjk : j < k
      · simp only [if_pos hjk]
        exact (hη j hjk).mul (isRoundingProduct_one_of_abs_le hε)
      · simp only [if_neg hjk]
        exact ((isRoundingProduct_one_of_abs_le hδ).mul
          (isRoundingProduct_one_of_abs_le hε)).mono hu (by omega)
    · simp only [hs₁, hs, sum_range_succ, lt_irrefl, if_false, add_mul, sum_mul]
      congr 1
      · refine sum_congr rfl fun j hj => ?_
        rw [if_pos (mem_range.mp hj)]
        ring
      · ring

/-- **Backward error of an inner product, product form** [Higham2002, §3.1], (3.4) there:
under the standard model with unit roundoff $0 \le u$, the result $s_n$ of a trace of recursive
accumulation is
$$s_n = \sum_{k<n} x_k y_k (1 + \eta_k)\,,$$
each $1 + \eta_k$ a product of $n$ factors $(1 + \delta)^{\pm 1}$ with
$\lvert \delta \rvert \le u$ (`NLAlib.Computation.IsRoundingProduct`), so that the
$\theta$-algebra of [Higham2002, Lemma 3.3] applies to it without loss. -/
theorem IsDotTrace.exists_eq_sum_mul_one_add_isRoundingProduct {x y s : ℕ → ℝ}
    (h : IsDotTrace (fun _ => RelErr u) x y n s) (hu : 0 ≤ u) :
    ∃ η : ℕ → ℝ, (∀ k < n, IsRoundingProduct u n (η k)) ∧
      s n = ∑ k ∈ range n, x k * y k * (1 + η k) :=
  h.exists_eq_sum_of_le hu n le_rfl

/-- **Backward error of an inner product** [Higham2002, §3.1], (3.4) there,
with the factor of [CarsonMaShao2026, (3)]: under the standard model with unit roundoff
$0 \le u < 1$, the result $s_n$ of a trace of recursive accumulation is the exact inner product
of slightly perturbed data,
$$s_n = \sum_{k<n} x_k y_k (1 + \eta_k)\,, \qquad
\lvert \eta_k \rvert \le \gamma_n = (1 - u)^{-n} - 1\,,$$ with no condition on $nu$.
Result: inner-product-backward-error -/
theorem IsDotTrace.exists_eq_sum_mul_one_add {x y s : ℕ → ℝ}
    (h : IsDotTrace (fun _ => RelErr u) x y n s) (hu : 0 ≤ u) (hu1 : u < 1) :
    ∃ η : ℕ → ℝ, (∀ k < n, |η k| ≤ roundingFactor n u) ∧
      s n = ∑ k ∈ range n, x k * y k * (1 + η k) :=
  let ⟨η, hη, hs⟩ := h.exists_eq_sum_mul_one_add_isRoundingProduct hu
  ⟨η, fun k hk => (hη k hk).abs_le hu1, hs⟩

/-- **Forward error of an inner product** [Higham2002, §3.1], (3.5) there, with
the factor of [CarsonMaShao2026, (3)]: under the standard model with $0 \le u < 1$,
$$\Bigl\lvert \sum_{k<n} x_k y_k - s_n \Bigr\rvert \le \gamma_n \sum_{k<n}
\lvert x_k \rvert \lvert y_k \rvert\,, \qquad \gamma_n = (1 - u)^{-n} - 1\,.$$
Result: inner-product-forward-error -/
theorem IsDotTrace.abs_sum_mul_sub_le {x y s : ℕ → ℝ}
    (h : IsDotTrace (fun _ => RelErr u) x y n s) (hu : 0 ≤ u) (hu1 : u < 1) :
    |∑ k ∈ range n, x k * y k - s n| ≤
      roundingFactor n u * ∑ k ∈ range n, |x k| * |y k| := by
  obtain ⟨η, hη, hs⟩ := h.exists_eq_sum_mul_one_add hu hu1
  have hdiff : ∑ k ∈ range n, x k * y k - s n = -∑ k ∈ range n, x k * y k * η k := by
    rw [hs, ← sum_sub_distrib, ← sum_neg_distrib]
    exact sum_congr rfl fun k _ => by ring
  rw [hdiff, abs_neg, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  rw [abs_mul, abs_mul, mul_comm (roundingFactor n u)]
  exact mul_le_mul_of_nonneg_left (hη k (mem_range.mp hk)) (by positivity)

/-- **One entry of `axpy`** under the standard model: if $q$ is $ax$ with
relative error at most $u$ and $z$ is $q + y$ with relative error at most $u$, and $u < 1$, then
$$z = ax(1 + \theta) + y(1 + \delta)\,, \qquad
\lvert \theta \rvert \le \gamma_2 = (1 - u)^{-2} - 1\,,\quad
\lvert \delta \rvert \le u\,.$$ From the model (2.4) of [Higham2002, §2.2] and
[CarsonMaShao2026, Lemma 2]. -/
theorem exists_eq_mul_one_add_add_mul_one_add_of_relErr {a x y q z : ℝ}
    (hq : RelErr u (a * x) q) (hz : RelErr u (q + y) z) (hu1 : u < 1) :
    ∃ θ δ : ℝ, |θ| ≤ roundingFactor 2 u ∧ |δ| ≤ u ∧
      z = a * x * (1 + θ) + y * (1 + δ) := by
  obtain ⟨δ₁, hδ₁, rfl⟩ := hq
  obtain ⟨δ₂, hδ₂, rfl⟩ := hz
  have hγ1 := le_roundingFactor_one hu1
  refine ⟨(1 + δ₁) * (1 + δ₂) - 1, δ₂, ?_, hδ₂, by ring⟩
  exact abs_one_add_mul_one_add_sub_one_le (k := 1) (j := 1)
    (hδ₁.trans hγ1) (hδ₂.trans hγ1)

/-- A product of $k + 1$ rounding factors, $(1 + d)^{e}$ times $k$ inverted factors
$(1 + c_l)^{-1}$, is $1 + \theta$ with $\lvert \theta \rvert \le \gamma_{k+1}$. -/
private theorem abs_zpow_mul_inv_prod_sub_one_le (c : ℕ → ℝ) (d : ℝ) (k : ℕ)
    (hc : ∀ l < k, |c l| ≤ u) (hd : |d| ≤ u) (hu1 : u < 1) (e : ℤ)
    (he : e = 1 ∨ e = -1) :
    |(1 + d) ^ e * (∏ l ∈ range k, (1 + c l))⁻¹ - 1| ≤ roundingFactor (k + 1) u := by
  have key := abs_prod_one_add_zpow_sub_one_le (u := u) (range (k + 1))
    (fun l => if l < k then c l else d) (fun l => if l < k then -1 else e)
    (fun l hl => by
      by_cases hlk : l < k
      · simpa [hlk] using hc l hlk
      · simpa [hlk] using hd)
    (fun l _ => by by_cases hlk : l < k <;> simp [hlk, he]) hu1
  rw [card_range, prod_range_succ] at key
  simp only [lt_irrefl, if_false] at key
  rw [prod_congr rfl (g := fun l => (1 + c l) ^ (-1 : ℤ)) fun l hl => by
    simp [mem_range.mp hl]] at key
  simpa [zpow_neg_one, prod_inv_distrib, mul_comm] using key

/-- **One row of forward substitution**: under the hypotheses of
`NLAlib.Computation.IsSubstTrace.exists_sum_add_mul_eq`, row $i$ is solved
exactly by a perturbed row, $\sum_{j \le i} t_{ij}(1 + \theta_j)\hat{x}_j = b_i$ with
$\lvert \theta_j \rvert \le \gamma_n$. -/
private theorem IsSubstRowTrace.exists_sum_eq {t : ℕ → ℕ → ℝ} {b x s : ℕ → ℝ} {i : ℕ}
    (hrow : IsSubstRowTrace (fun _ => RelErr u) t b x i i s) (hdiv : RelErr u (s i / t i i) (x i))
    (hd : t i i ≠ 0) (hu : 0 ≤ u) (hu1 : u < 1) (hi : i < n) :
    ∃ θ : ℕ → ℝ, (∀ j ≤ i, |θ j| ≤ roundingFactor n u) ∧
      ∑ j ∈ range (i + 1), (t i j + t i j * θ j) * x j = b i := by
  obtain ⟨f, hf⟩ := exists_fun_of_forall_lt (k := i) (Q := fun j (de : ℝ × ℝ) =>
      |de.1| ≤ u ∧ |de.2| ≤ u ∧ s (j + 1) = (s j - t i j * x j * (1 + de.1)) * (1 + de.2))
    fun j hj => by
      obtain ⟨q, ⟨δ, hδ, rfl⟩, ⟨ε, hε, h⟩⟩ := hrow.2 j hj
      exact ⟨(δ, ε), hδ, hε, h⟩
  set E : ℕ → ℝ := fun k => ∏ l ∈ range k, (1 + (f l).2) with hE
  have hE0 : ∀ k ≤ i, E k ≠ 0 := fun k hk => prod_ne_zero_iff.mpr fun l hl =>
    one_add_ne_zero_of_abs_le (hf l (by have := mem_range.mp hl; omega)).2.1 hu1
  have hs : ∀ k ≤ i,
      s k = E k * (b i - ∑ j ∈ range k, t i j * x j * ((1 + (f j).1) * (E j)⁻¹)) := by
    intro k
    induction k with
    | zero => intro _; simp [hE, hrow.1]
    | succ k ih =>
      intro hk
      have hEk := hE0 k (by omega)
      rw [(hf k (by omega)).2.2, ih (by omega), sum_range_succ]
      simp only [hE, prod_range_succ] at hEk ⊢
      field_simp
      ring
  obtain ⟨δ', hδ', hx⟩ := hdiv
  have hδ'0 := one_add_ne_zero_of_abs_le hδ' hu1
  have hsi : s i = t i i * x i * (1 + δ')⁻¹ := by
    rw [hx]
    field_simp
  have hγ : ∀ m ≤ n, roundingFactor m u ≤ roundingFactor n u := fun m hm =>
    roundingFactor_le_roundingFactor hu hu1 hm
  refine ⟨fun j => if j < i then (1 + (f j).1) * (E j)⁻¹ - 1 else (1 + δ')⁻¹ * (E i)⁻¹ - 1,
    fun j hj => ?_, ?_⟩
  · by_cases hji : j < i
    · simp only [if_pos hji]
      have := abs_zpow_mul_inv_prod_sub_one_le (fun l => (f l).2) (f j).1 j
        (fun l hl => (hf l (by omega)).2.1) (hf j hji).1 hu1 1 (Or.inl rfl)
      rw [zpow_one] at this
      exact this.trans (hγ _ (by omega))
    · simp only [if_neg hji]
      have := abs_zpow_mul_inv_prod_sub_one_le (fun l => (f l).2) δ' i
        (fun l hl => (hf l hl).2.1) hδ' hu1 (-1) (Or.inr rfl)
      rw [zpow_neg_one] at this
      exact this.trans (hγ _ (by omega))
  · have hb := hs i le_rfl
    rw [hsi] at hb
    have hEi := hE0 i le_rfl
    simp only [sum_range_succ, lt_irrefl, if_false]
    rw [sum_congr rfl fun j hj => by rw [if_pos (mem_range.mp hj)]]
    have : b i = t i i * x i * (1 + δ')⁻¹ * (E i)⁻¹ +
        ∑ j ∈ range i, t i j * x j * ((1 + (f j).1) * (E j)⁻¹) := by
      rw [hb]
      field_simp
      ring
    rw [this, add_comm (t i i * x i * _ * _)]
    congr 1
    · exact sum_congr rfl fun j _ => by ring
    · ring

/-- **Backward error of forward substitution** [Higham2002, Theorem 8.5], from
[Higham2002, Lemma 8.4], with the factor of [CarsonMaShao2026, (3)]: under the standard model
with $0 \le u < 1$, if every diagonal entry $t_{ii}$ ($i < n$) is nonzero, a trace $\hat{x}$ of
forward substitution solves a nearby system exactly: for some $\Delta t_{ij}$ with
$\lvert \Delta t_{ij} \rvert \le \gamma_n \lvert t_{ij} \rvert$ ($j \le i < n$),
$\gamma_n = (1 - u)^{-n} - 1$,
$$\sum_{j \le i} (t_{ij} + \Delta t_{ij})\,\hat{x}_j = b_i \qquad (i < n)\,.$$
Result: forward-substitution-backward-error -/
theorem IsSubstTrace.exists_sum_add_mul_eq {t : ℕ → ℕ → ℝ} {b x : ℕ → ℝ}
    (h : IsSubstTrace (fun _ => RelErr u) t b n x) (hdiag : ∀ i < n, t i i ≠ 0) (hu : 0 ≤ u)
    (hu1 : u < 1) :
    ∃ Δ : ℕ → ℕ → ℝ, (∀ i < n, ∀ j ≤ i, |Δ i j| ≤ roundingFactor n u * |t i j|) ∧
      ∀ i < n, ∑ j ∈ range (i + 1), (t i j + Δ i j) * x j = b i := by
  obtain ⟨θ, hθ⟩ := exists_fun_of_forall_lt (k := n) (Q := fun i (θ : ℕ → ℝ) =>
      (∀ j ≤ i, |θ j| ≤ roundingFactor n u) ∧
        ∑ j ∈ range (i + 1), (t i j + t i j * θ j) * x j = b i)
    fun i hi => by
      obtain ⟨s, hrow, hdiv⟩ := h i hi
      exact hrow.exists_sum_eq hdiv (hdiag i hi) hu hu1 hi
  refine ⟨fun i j => t i j * θ i j, fun i hi j hj => ?_, fun i hi => (hθ i hi).2⟩
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hθ i hi).1 j hj) (abs_nonneg _)

end NLAlib.Computation
