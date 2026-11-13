/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.LinearAlgebra.Lagrange
public import NLAlib.Polynomial.Approximation.MinimaxError
public import NLAlib.ForMathlib.Topology.Order.IntermediateValue
public import NLAlib.ForMathlib.Topology.ContinuousMap.Compact

/-!
# Alternation and equioscillation

The alternation predicate of best uniform approximation: a real function alternates in sign at
$k$ ordered points of a set, with modulus at least a level $\varepsilon$. It is the hypothesis of
de la Vallée Poussin's lower bound and, at the level of the uniform error, the conclusion of
Chebyshev's equioscillation theorem.

De la Vallée Poussin: an error $f - p$, $\deg p \le n$, that alternates at $n + 2$ points of $s$
with level $\varepsilon$ gives $\varepsilon \le E_n(f; s)$, on any set and for any $f$.
Chebyshev: on $[a, b]$, $a < b$, with $f$ continuous, $p$ is a best approximation if and only if
$f - p$ equioscillates at $n + 2$ points; the best approximation is unique and interpolates $f$
at $n + 1$ interior points. The Chebyshev polynomial $T_n$ alternates at $n + 1$ points, which
gives $E_n(x^{n + 1}; [-1, 1]) = 2^{-n}$.

## Main definitions

* `NLAlib.AlternatesOn`: alternation at $k$ ordered points with level $\varepsilon$, with its
  raw-condition constructor `NLAlib.alternatesOn_iff`.

## Main results

* `NLAlib.AlternatesOn.mono`, `NLAlib.AlternatesOn.exists_eq_of_abs_le`: the API of the
  predicate.
* `NLAlib.AlternatesOn.exists_le_abs_sub_eval`, `NLAlib.AlternatesOn.le_minimaxError`: de la
  Vallée Poussin's lower bound.
* `NLAlib.AlternatesOn.minimaxError_eq`: an equioscillating error is the minimax error.
* `NLAlib.alternatesOn_of_isUniformApproxOn_minimaxError`,
  `NLAlib.isUniformApproxOn_minimaxError_iff_exists_alternatesOn`: Chebyshev's equioscillation
  theorem.
* `NLAlib.eq_of_isUniformApproxOn_minimaxError`: uniqueness.
* `NLAlib.exists_eval_eq_of_isUniformApproxOn_minimaxError`: the best approximation interpolates.
* `NLAlib.alternatesOn_minimaxPoly`, `NLAlib.eq_minimaxPoly_of_isUniformApproxOn_minimaxError`:
  the chosen best approximation `NLAlib.minimaxPoly` equioscillates and is the best one.
* `NLAlib.exists_degree_le_or_alternatesOn`: the sign-block lemma, for later strengthenings.
* `NLAlib.alternatesOn_eval_T_real`, `NLAlib.minimaxError_pow_Icc_neg_one_one`: the Chebyshev
  example.
-/

@[expose] public section

open Polynomial

namespace NLAlib

/-- The function $g$ **alternates on $s$ at $k$ points with level $\varepsilon$**: there are
points $x_0 < x_1 < \dots < x_{k-1}$ of $s$ and a sign $\sigma \in \{1, -1\}$ with
$\varepsilon \le \sigma(-1)^i g(x_i)$ for every $i$. For $\varepsilon > 0$ the values
$g(x_i)$ alternate in sign and have modulus at least $\varepsilon$ (de la Vallée Poussin's
hypothesis); when also $\lvert g \rvert \le \varepsilon$ on $s$,
$g(x_i) = \sigma(-1)^i\varepsilon$ (equioscillation). For $\varepsilon \le 0$ the condition is
weaker than a sign change. [Trefethen2019, Theorem 10.1]; [Rivlin1981, Ch. 1]. -/
def AlternatesOn (g : ℝ → ℝ) (s : Set ℝ) (k : ℕ) (ε : ℝ) : Prop :=
  ∃ x : Fin k → ℝ, StrictMono x ∧ (∀ i, x i ∈ s) ∧
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ i : Fin k, ε ≤ σ * (-1) ^ (i : ℕ) * g (x i)

/-- Raw-condition constructor and elimination rule for `AlternatesOn`. -/
theorem alternatesOn_iff {g : ℝ → ℝ} {s : Set ℝ} {k : ℕ} {ε : ℝ} :
    AlternatesOn g s k ε ↔ ∃ x : Fin k → ℝ, StrictMono x ∧ (∀ i, x i ∈ s) ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ i : Fin k, ε ≤ σ * (-1) ^ (i : ℕ) * g (x i) :=
  Iff.rfl

/-! ### The predicate -/

/-- Alternation is monotone: if $g$ alternates on $s$ at $k$ points with level $\varepsilon$,
then it alternates on every $t \supseteq s$ with every level $\eta \le \varepsilon$. -/
theorem AlternatesOn.mono {g : ℝ → ℝ} {s t : Set ℝ} {k : ℕ} {ε η : ℝ}
    (h : AlternatesOn g s k ε) (hst : s ⊆ t) (hηε : η ≤ ε) : AlternatesOn g t k η := by
  obtain ⟨x, hx, hxs, σ, hσ, h⟩ := h
  exact ⟨x, hx, fun i => hst (hxs i), σ, hσ, fun i => hηε.trans (h i)⟩

/-- An alternation at the level of the uniform bound is an equioscillation: if $g$ alternates on
$s$ at $k$ points with level $\varepsilon$ and $\lvert g \rvert \le \varepsilon$ on $s$, then
there are $x_0 < \dots < x_{k-1}$ in $s$ and $\sigma \in \{1, -1\}$ with
$g(x_i) = \sigma(-1)^i\varepsilon$. -/
theorem AlternatesOn.exists_eq_of_abs_le {g : ℝ → ℝ} {s : Set ℝ} {k : ℕ} {ε : ℝ}
    (h : AlternatesOn g s k ε) (hg : ∀ x ∈ s, |g x| ≤ ε) :
    ∃ x : Fin k → ℝ, StrictMono x ∧ (∀ i, x i ∈ s) ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ i : Fin k, g (x i) = σ * (-1) ^ (i : ℕ) * ε := by
  obtain ⟨x, hmono, hx, σ, hσ, hle⟩ := h
  refine ⟨x, hmono, hx, σ, hσ, fun i => ?_⟩
  have hgi := abs_le.mp (hg _ (hx i))
  have hi := hle i
  rcases hσ with rfl | rfl <;> rcases neg_one_pow_eq_or ℝ (i : ℕ) with h | h <;>
    rw [h] at hi ⊢ <;> linarith [hgi.1, hgi.2]

/-! ### De la Vallée Poussin -/

/-- The sign $\sigma(-1)^i$ of an alternation has modulus $1$. -/
private theorem abs_mul_neg_one_pow {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (i : ℕ) :
    |σ * (-1) ^ i| = 1 := by
  rcases hσ with rfl | rfl <;> simp

/-- Values with the alternating signs $\sigma(-1)^i$ change sign between consecutive points. -/
private theorem mul_neg_of_pos_mul_neg_one_pow {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {k : ℕ}
    {u : Fin (k + 1) → ℝ} (hu : ∀ i : Fin (k + 1), 0 < σ * (-1) ^ (i : ℕ) * u i) (i : Fin k) :
    u i.castSucc * u i.succ < 0 := by
  have h1 := hu i.castSucc
  have h2 := hu i.succ
  simp only [Fin.val_castSucc, Fin.val_succ, pow_succ] at h1 h2
  rcases hσ with rfl | rfl <;> rcases neg_one_pow_eq_or ℝ (i : ℕ) with h | h <;>
    rw [h] at h1 h2 <;> nlinarith

/-- **De la Vallée Poussin's theorem, pointwise.** If $\deg p \le n$ and $f - p$ alternates on
$s$ at $n + 2$ points with level $\varepsilon$, then every real polynomial $q$ of degree at most
$n$ has $\varepsilon \le \lvert f(x) - q(x) \rvert$ at some $x \in s$. No continuity of $f$ and
no structure of $s$ are needed. [Trefethen2019, Exercise 10.3]. -/
theorem AlternatesOn.exists_le_abs_sub_eval {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {p : ℝ[X]} {ε : ℝ}
    (h : AlternatesOn (fun x => f x - p.eval x) s (n + 2) ε) (hp : p.degree ≤ n) {q : ℝ[X]}
    (hq : q.degree ≤ n) : ∃ x ∈ s, ε ≤ |f x - q.eval x| := by
  obtain ⟨x, hx, hxs, σ, hσ, h⟩ := h
  by_contra! H
  -- `q - p` has the signs of the alternation at every point
  have key : ∀ i : Fin (n + 2), 0 < σ * (-1) ^ (i : ℕ) * (q - p).eval (x i) := by
    intro i
    have h3 := (le_abs_self (σ * (-1) ^ (i : ℕ) * (f (x i) - q.eval (x i)))).trans_eq
      (by rw [abs_mul, abs_mul_neg_one_pow hσ, one_mul])
    rw [eval_sub, show q.eval (x i) - p.eval (x i) =
      (f (x i) - p.eval (x i)) - (f (x i) - q.eval (x i)) by ring, mul_sub]
    linarith [h i, H (x i) (hxs i)]
  -- so it has `n + 1` zeros, and degree at most `n`
  obtain ⟨c, hc, hzero⟩ := exists_strictMono_eq_zero_of_mul_neg (k := n + 1)
    (f := fun t => (q - p).eval t) (v := x) hx (q - p).continuous.continuousOn
    (mul_neg_of_pos_mul_neg_one_pow hσ key)
  have hd : q - p = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (s := Finset.univ)
      (v := c) hc.injective.injOn ?_ (fun i _ => (hzero i).2)
    rw [Finset.card_univ, Fintype.card_fin]
    exact ((degree_sub_le q p).trans (max_le hq hp)).trans_lt
      (by exact_mod_cast Nat.lt_succ_self n)
  simpa [hd] using key 0

/-- **De la Vallée Poussin's lower bound.** If $\deg p \le n$, $p$ is within some finite
$\eta$ of $f$ on $s$, and $f - p$ alternates on $s$ at $n + 2$ points with level
$\varepsilon$, then $\varepsilon \le E_n(f; s)$. The set $s$ is arbitrary (a finite spectrum, a
union of intervals); the finite $\eta$ only excludes the junk value of `minimaxError`.
[Trefethen2019, Exercise 10.3].
Result: de-la-vallee-poussin -/
theorem AlternatesOn.le_minimaxError {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {p : ℝ[X]} {ε : ℝ}
    (h : AlternatesOn (fun x => f x - p.eval x) s (n + 2) ε) (hp : p.degree ≤ n) {η : ℝ}
    (hη : Metric.IsUniformApproxOn (fun x => p.eval x) f s η) : ε ≤ minimaxError f s n := by
  unfold minimaxError
  refine le_csInf ⟨η, p, hp, hη⟩ ?_
  rintro ε' ⟨q, hq, hq'⟩
  obtain ⟨x, hxs, hx⟩ := h.exists_le_abs_sub_eval hp hq
  have hdist := hq' x hxs
  rw [Real.dist_eq, abs_sub_comm] at hdist
  exact hx.trans hdist

/-- **An equioscillating error is the minimax error**: if $\deg p \le n$,
$\lvert f - p \rvert \le \varepsilon$ on $s$ and $f - p$ alternates on $s$ at $n + 2$ points
with level $\varepsilon$, then $E_n(f; s) = \varepsilon$, and $p$ is a best approximation. On
any set, for any $f$: the certificate direction of the equioscillation theorem.
[Trefethen2019, Theorem 10.1].
Result: equioscillation -/
theorem AlternatesOn.minimaxError_eq {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {p : ℝ[X]} {ε : ℝ}
    (h : AlternatesOn (fun x => f x - p.eval x) s (n + 2) ε) (hp : p.degree ≤ n)
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f s ε) : minimaxError f s n = ε := by
  have hne : s.Nonempty := by
    obtain ⟨x, -, hxs, -⟩ := h
    exact ⟨x 0, hxs 0⟩
  exact le_antisymm (minimaxError_le_of_isUniformApproxOn hp (hε.nonneg hne) hε)
    (h.le_minimaxError hp hε)

/-! ### Chebyshev's equioscillation theorem -/

/-- Prepending a point of opposite sign to an alternation lengthens it by one. -/
private theorem alternatesOn_vecCons {e : ℝ → ℝ} {s : Set ℝ} {k : ℕ} {E r σ : ℝ}
    {v : Fin (k + 1) → ℝ} (hv : StrictMono v) (hvs : ∀ i, v i ∈ s) (hσ : σ = 1 ∨ σ = -1)
    (hvE : ∀ i : Fin (k + 1), E ≤ σ * (-1) ^ (i : ℕ) * e (v i)) (hr : r ∈ s) (hrv : r < v 0)
    (her : E ≤ -σ * e r) : AlternatesOn e s (k + 2) E := by
  refine ⟨Matrix.vecCons r v, hv.vecCons hrv, Fin.cases hr hvs, -σ,
    by rcases hσ with rfl | rfl <;> norm_num, Fin.cases (by simpa using her) fun i => ?_⟩
  simp only [Matrix.cons_val_succ, Fin.val_succ, pow_succ]
  linarith [hvE i]

/-- The constant $e(a)$ has the sign of $e$ at the extremal points when $e$ never takes the
value $-e(a)$ on $[a, b]$. -/
private theorem exists_degree_le_const {e : ℝ → ℝ} {a b E : ℝ} (n : ℕ) (hE : 0 < E)
    (hea : |e a| = E) (hT : ¬ ∃ y ∈ Set.Icc a b, e y = -e a) :
    ∃ q : ℝ[X], q.degree ≤ n ∧ (∀ x ∈ Set.Icc a b, |e x| = E → 0 < e x * q.eval x) ∧
      ∀ x ≤ a, 0 < e a * q.eval x := by
  have ha : e a ≠ 0 := fun h => by simp [h] at hea; linarith
  refine ⟨C (e a), degree_C_le.trans (WithBot.coe_le_coe.2 (Nat.zero_le n)), fun x hx hxE => ?_,
    fun x _ => by simpa using mul_self_pos.2 ha⟩
  rcases abs_eq_abs.1 (hxE.trans hea.symm) with h | h
  · simpa [h] using mul_self_pos.2 ha
  · exact absurd ⟨x, hx, h⟩ hT

/-- The pivot of the sign-block lemma: the least point $y$ of $[a, b]$ with $e(y) = -e(a)$, and
a point $z \in (a, y)$ above every extremal point below $y$. -/
private theorem exists_pivot {e : ℝ → ℝ} {a b E : ℝ} (he : ContinuousOn e (Set.Icc a b))
    (hE : 0 < E) (hea : |e a| = E) (hT : ∃ y ∈ Set.Icc a b, e y = -e a) :
    ∃ y z, a < z ∧ z < y ∧ y ≤ b ∧ e y = -e a ∧
      ∀ x ∈ Set.Icc a b, |e x| = E → x < y → e x = e a ∧ x < z := by
  have ha : e a ≠ 0 := fun h => by simp [h] at hea; linarith
  have hcl := he.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := -e a))
  obtain ⟨y, ⟨hyI, hy⟩, hyl⟩ :=
    (isCompact_Icc.of_isClosed_subset hcl Set.inter_subset_left).exists_isLeast hT
  have hy' : e y = -e a := hy
  have hay : a < y := lt_of_le_of_ne hyI.1 fun h => ha (by subst h; linarith)
  have hcl' := (he.mono (Set.Icc_subset_Icc_right hyI.2)).preimage_isClosed_of_isClosed
    isClosed_Icc (isClosed_singleton (x := e a))
  obtain ⟨u, ⟨huI, hu⟩, hug⟩ := (isCompact_Icc.of_isClosed_subset hcl'
    Set.inter_subset_left).exists_isGreatest ⟨a, ⟨le_rfl, hay.le⟩, rfl⟩
  have hu' : e u = e a := hu
  have huy : u < y := lt_of_le_of_ne huI.2 fun h => ha (by subst h; linarith)
  refine ⟨y, (u + y) / 2, by linarith [huI.1], by linarith, hyI.2, hy', fun x hx hxE hxy => ?_⟩
  rcases abs_eq_abs.1 (hxE.trans hea.symm) with h | h
  · exact ⟨h, by linarith [hug ⟨⟨hx.1, hxy.le⟩, h⟩]⟩
  · exact absurd (hyl ⟨hx, h⟩) (not_le.2 hxy)

/-- **The sign-block lemma** behind the equioscillation theorem. Let $e$ be continuous on
$[a, b]$, $E > 0$ and $\lvert e(a) \rvert = E$. Either some real $q$ of degree at most $n$ has the
sign of $e$ at its extremal points, $e(x)q(x) > 0$ at every $x \in [a, b]$ with
$\lvert e(x) \rvert = E$, and the sign of $e(a)$ to the left of $a$, $e(a)q(x) > 0$ for every
$x \le a$; or $e$ alternates at $n + 2$ points of $\{x \in [a, b] : \lvert e(x) \rvert = E\}$
with level $E$. The second clause of the first alternative is what makes the induction on $n$
compose; the lemma is public so that the equioscillation theorem on compact sets and its
weighted form reuse it.
[Trefethen2019, proof of Theorem 10.1] uses the sign-changing perturbation to prove necessity. -/
theorem exists_degree_le_or_alternatesOn (n : ℕ) {e : ℝ → ℝ} {a b E : ℝ}
    (he : ContinuousOn e (Set.Icc a b)) (hE : 0 < E) (hab : a ≤ b) (hea : |e a| = E) :
    (∃ q : ℝ[X], q.degree ≤ n ∧ (∀ x ∈ Set.Icc a b, |e x| = E → 0 < e x * q.eval x) ∧
      ∀ x ≤ a, 0 < e a * q.eval x) ∨
    AlternatesOn e {x | x ∈ Set.Icc a b ∧ |e x| = E} (n + 2) E := by
  induction n generalizing a with
  | zero =>
    by_cases hT : ∃ y ∈ Set.Icc a b, e y = -e a
    · right
      obtain ⟨y, z, haz, hzy, hyb, hy, -⟩ := exists_pivot he hE hea hT
      have hyE : |e y| = E := by rw [hy, abs_neg, hea]
      have hys : y ∈ {x | x ∈ Set.Icc a b ∧ |e x| = E} := ⟨⟨by linarith, hyb⟩, hyE⟩
      have has : a ∈ {x | x ∈ Set.Icc a b ∧ |e x| = E} := ⟨⟨le_rfl, hab⟩, hea⟩
      rcases (abs_eq hE.le).1 hea with h | h
      · exact alternatesOn_vecCons (v := ![y]) (σ := -1) strictMono_vecEmpty
          (Fin.forall_fin_one.2 hys) (Or.inr rfl) (Fin.forall_fin_one.2 (by simp; linarith))
          has (by simp; linarith) (by linarith)
      · exact alternatesOn_vecCons (v := ![y]) (σ := 1) strictMono_vecEmpty
          (Fin.forall_fin_one.2 hys) (Or.inl rfl) (Fin.forall_fin_one.2 (by simp; linarith))
          has (by simp; linarith) (by linarith)
    · exact Or.inl (exists_degree_le_const 0 hE hea hT)
  | succ n ih =>
    by_cases hT : ∃ y ∈ Set.Icc a b, e y = -e a
    · obtain ⟨y, z, haz, hzy, hyb, hy, hlow⟩ := exists_pivot he hE hea hT
      have hyE : |e y| = E := by rw [hy, abs_neg, hea]
      rcases ih (he.mono (Set.Icc_subset_Icc_left (by linarith))) hyb hyE with
        ⟨q, hq, hqs, hql⟩ | ⟨v, hv, hvs, σ, hσ, hvE⟩
      · left
        refine ⟨(X - C z) * q, ?_, fun x hx hxE => ?_, fun x hx => ?_⟩
        · refine (degree_mul_le _ _).trans ?_
          rw [degree_X_sub_C, Nat.cast_succ, add_comm]
          exact add_le_add_left hq 1
        · simp only [eval_mul, eval_sub, eval_X, eval_C]
          rcases lt_or_ge x y with hxy | hxy
          · obtain ⟨h1, h2⟩ := hlow x hx hxE hxy
            have := hql x hxy.le
            rw [hy] at this
            rw [h1]
            nlinarith
          · have := hqs x ⟨hxy, hx.2⟩ hxE
            nlinarith
        · simp only [eval_mul, eval_sub, eval_X, eval_C]
          have := hql x (by linarith)
          rw [hy] at this
          nlinarith
      · right
        have h0 := hvE 0
        obtain ⟨⟨hv0y, -⟩, -⟩ := hvs 0
        have hvs' : ∀ i, v i ∈ {x | x ∈ Set.Icc a b ∧ |e x| = E} := fun i =>
          ⟨⟨by linarith [(hvs i).1.1], (hvs i).1.2⟩, (hvs i).2⟩
        have hys : y ∈ {x | x ∈ Set.Icc a b ∧ |e x| = E} := ⟨⟨by linarith, hyb⟩, hyE⟩
        have has : a ∈ {x | x ∈ Set.Icc a b ∧ |e x| = E} := ⟨⟨le_rfl, hab⟩, hea⟩
        simp only [Fin.val_zero, pow_zero, mul_one] at h0
        rcases (abs_eq hE.le).1 hea with h | h
        · rcases hσ with rfl | rfl
          · exact alternatesOn_vecCons hv hvs' (Or.inl rfl) hvE hys
              (lt_of_le_of_ne hv0y fun h' => by rw [← h'] at h0; linarith) (by linarith)
          · exact alternatesOn_vecCons hv hvs' (Or.inr rfl) hvE has (by linarith)
              (by linarith)
        · rcases hσ with rfl | rfl
          · exact alternatesOn_vecCons hv hvs' (Or.inl rfl) hvE has (by linarith)
              (by linarith)
          · exact alternatesOn_vecCons hv hvs' (Or.inr rfl) hvE hys
              (lt_of_le_of_ne hv0y fun h' => by rw [← h'] at h0; linarith) (by linarith)
    · exact Or.inl (exists_degree_le_const _ hE hea hT)

/-- Equispaced interior points: $x_i = a + (b - a)(i + 1)/(k + 1)$, $i < k$, are strictly
increasing and lie in $(a, b)$. -/
private theorem exists_strictMono_mem_Ioo {a b : ℝ} (hab : a < b) (k : ℕ) :
    ∃ x : Fin k → ℝ, StrictMono x ∧ ∀ i, x i ∈ Set.Ioo a b := by
  have hba : 0 < b - a := sub_pos.mpr hab
  refine ⟨fun i => a + (b - a) * ((i : ℝ) + 1) / (k + 1), fun i j hij => ?_, fun i => ?_⟩
  · have : ((i : ℕ) : ℝ) < j := by exact_mod_cast hij
    dsimp only
    gcongr
  · have hi : ((i : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast i.isLt
    have h0 : 0 < (b - a) * ((i : ℝ) + 1) / (k + 1) := by positivity
    have h1 : (b - a) * ((i : ℝ) + 1) / (k + 1) < b - a := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    constructor <;> linarith

/-- An error that vanishes on $[a, b]$, $a < b$, alternates there at any number $k$ of points
with level $0$: the zero-error case of the equioscillation theorem. -/
private theorem alternatesOn_Icc_zero_of_eq_zero {g : ℝ → ℝ} {a b : ℝ} (hab : a < b) (k : ℕ)
    (hg : ∀ x ∈ Set.Icc a b, g x = 0) : AlternatesOn g (Set.Icc a b) k 0 := by
  obtain ⟨x, hx, hxs⟩ := exists_strictMono_mem_Ioo hab k
  exact ⟨x, hx, fun i => Set.Ioo_subset_Icc_self (hxs i), 1, Or.inl rfl, fun i => by
    rw [hg _ (Set.Ioo_subset_Icc_self (hxs i)), mul_zero]⟩

/-- A best approximation with positive error attains it: if $\deg p \le n$,
$\lvert f - p \rvert \le E_n(f; [a, b])$ on $[a, b]$ and $E_n(f; [a, b]) > 0$, the extremal set
$\{x \in [a, b] : \lvert f(x) - p(x) \rvert = E_n\}$ has a least element. -/
private theorem exists_isLeast_abs_sub_eval_eq_minimaxError {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n))
    (hE : 0 < minimaxError f (Set.Icc a b) n) :
    ∃ c, IsLeast {x | x ∈ Set.Icc a b ∧ |f x - p.eval x| = minimaxError f (Set.Icc a b) n} c := by
  have he : ContinuousOn (fun x => |f x - p.eval x|) (Set.Icc a b) :=
    (hf.sub p.continuous.continuousOn).abs
  have hK : IsClosed (Set.Icc a b ∩ (fun x => |f x - p.eval x|) ⁻¹'
      {minimaxError f (Set.Icc a b) n}) :=
    he.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hKc := isCompact_Icc.of_isClosed_subset hK Set.inter_subset_left
  have hKne : (Set.Icc a b ∩ (fun x => |f x - p.eval x|) ⁻¹'
      {minimaxError f (Set.Icc a b) n}).Nonempty := by
    -- otherwise the maximum of `|f - p|` on `[a, b]` is an admissible error below `E_n`
    by_contra hne
    have hIcc : (Set.Icc a b).Nonempty := Set.nonempty_iff_ne_empty.2 fun h0 =>
      hE.not_ge (minimaxError_le_of_isUniformApproxOn hp le_rfl fun x hx => by simp [h0] at hx)
    obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hIcc he
    have hlt : |f x₀ - p.eval x₀| < minimaxError f (Set.Icc a b) n :=
      lt_of_le_of_ne (by rw [abs_sub_comm, ← Real.dist_eq]; exact hbest x₀ hx₀)
        fun h => hne ⟨x₀, hx₀, h⟩
    have h2 := minimaxError_le_of_isUniformApproxOn hp (abs_nonneg (f x₀ - p.eval x₀))
      fun x hx => by rw [Real.dist_eq, abs_sub_comm]; exact hmax hx
    linarith
  exact hKc.exists_isLeast hKne

/-- The descent step: a best approximation $p$ with positive error admits no correction $q$ of
degree at most $n$ with the sign of $f - p$ at every extremal point of $[a, b]$. -/
private theorem not_forall_mul_pos_of_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n))
    (hE : 0 < minimaxError f (Set.Icc a b) n) {q : ℝ[X]} (hq : q.degree ≤ n) :
    ¬ ∀ x ∈ Set.Icc a b, |f x - p.eval x| = minimaxError f (Set.Icc a b) n →
      0 < (f x - p.eval x) * q.eval x := by
  intro hsign
  have : CompactSpace (Set.Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  set E := minimaxError f (Set.Icc a b) n
  let g : C(Set.Icc a b, ℝ) :=
    ⟨fun x : Set.Icc a b => f x - p.eval (x : ℝ),
      (hf.sub (Polynomial.continuous p).continuousOn).domRestrict⟩
  let h : C(Set.Icc a b, ℝ) := q.toContinuousMapOn (Set.Icc a b)
  have hgE : ‖g‖ = E := by
    refine le_antisymm ((ContinuousMap.norm_le g hE.le).mpr fun x => ?_)
      (minimaxError_le_of_isUniformApproxOn hp (norm_nonneg g) fun x hx => ?_)
    · change |f x - p.eval (x : ℝ)| ≤ E
      rw [abs_sub_comm]
      exact hbest x x.2
    · rw [Real.dist_eq, abs_sub_comm]
      exact g.norm_coe_le_norm ⟨x, hx⟩
  obtain ⟨t, ht, htlt⟩ := ContinuousMap.exists_pos_norm_sub_smul_lt g h (by rwa [hgE])
    (fun x hx => hsign x x.2 (by rw [← hgE]; exact hx))
  have hdeg : (p + t • q).degree ≤ n :=
    (degree_add_le _ _).trans (max_le hp ((degree_smul_le _ _).trans hq))
  have herr : Metric.IsUniformApproxOn (fun x => (p + t • q).eval x) f (Set.Icc a b)
      ‖g - t • h‖ := fun x hx => by
    have h1 := (g - t • h).norm_coe_le_norm ⟨x, hx⟩
    have e : (g - t • h) ⟨x, hx⟩ = f x - (p.eval x + t * q.eval x) := by
      change f x - p.eval x - t * q.eval x = f x - (p.eval x + t * q.eval x)
      ring
    rw [e, Real.norm_eq_abs] at h1
    rw [Real.dist_eq, abs_sub_comm]
    dsimp only
    rw [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
    exact h1
  linarith [minimaxError_le_of_isUniformApproxOn hdeg (norm_nonneg _) herr]

/-- **Chebyshev's equioscillation theorem, necessity.** Let $a < b$, $f$ continuous on
$[a, b]$, and $p$ a real polynomial of degree at most $n$ with
$\lvert f - p \rvert \le E_n(f; [a, b])$ on $[a, b]$ (a best approximation). Then $f - p$
alternates on $[a, b]$ at $n + 2$ points with level $E_n(f; [a, b])$: it equioscillates
(`AlternatesOn.exists_eq_of_abs_le`). [Trefethen2019, Theorem 10.1].
Result: equioscillation -/
theorem alternatesOn_of_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n)) :
    AlternatesOn (fun x => f x - p.eval x) (Set.Icc a b) (n + 2)
      (minimaxError f (Set.Icc a b) n) := by
  rcases (minimaxError_nonneg f _ n).eq_or_lt with hE | hE
  · have hz : ∀ x ∈ Set.Icc a b, f x - p.eval x = 0 := fun x hx => by
      have h0 : dist (p.eval x) (f x) ≤ 0 := (hbest x hx).trans_eq hE.symm
      exact sub_eq_zero.mpr (dist_le_zero.mp h0).symm
    rw [← hE]
    exact alternatesOn_Icc_zero_of_eq_zero hab (n + 2) hz
  · obtain ⟨c, hc⟩ := exists_isLeast_abs_sub_eval_eq_minimaxError hf hp hbest hE
    rcases exists_degree_le_or_alternatesOn n
        (e := fun x => f x - p.eval x) (a := c) (b := b)
        ((hf.sub p.continuousOn).mono (Set.Icc_subset_Icc_left hc.1.1.1)) hE hc.1.1.2 hc.1.2
      with ⟨q, hq, hqs, -⟩ | halt
    · exfalso
      exact not_forall_mul_pos_of_isUniformApproxOn_minimaxError hf hp hbest hE hq
        (fun x hx hxe => hqs x ⟨hc.2 ⟨hx, hxe⟩, hx.2⟩ hxe)
    · refine halt.mono (fun x hx => ?_) le_rfl
      exact ⟨hc.1.1.1.trans hx.1.1, hx.1.2⟩

/-- **Chebyshev's equioscillation theorem.** Let $a < b$, $f$ continuous on $[a, b]$ and $p$ a
real polynomial of degree at most $n$. Then $p$ is a best approximation,
$\lvert f - p \rvert \le E_n(f; [a, b])$ on $[a, b]$, if and only if for some $\varepsilon$,
$\lvert f - p \rvert \le \varepsilon$ on $[a, b]$ and $f - p$ alternates at $n + 2$ points of
$[a, b]$ with level $\varepsilon$ (and then $\varepsilon = E_n(f; [a, b])$).
[Trefethen2019, Theorem 10.1].
Result: equioscillation -/
theorem isUniformApproxOn_minimaxError_iff_exists_alternatesOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n) :
    Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
        (minimaxError f (Set.Icc a b) n) ↔
      ∃ ε : ℝ, Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b) ε ∧
        AlternatesOn (fun x => f x - p.eval x) (Set.Icc a b) (n + 2) ε := by
  constructor
  · intro h
    exact ⟨_, h, alternatesOn_of_isUniformApproxOn_minimaxError hab hf hp h⟩
  · rintro ⟨ε, hε, halt⟩
    rw [halt.minimaxError_eq hp hε]
    exact hε

/-- **The best approximation is unique**: for $a < b$ and $f$ continuous on $[a, b]$, two real
polynomials $p, q$ of degree at most $n$ that are both within $E_n(f; [a, b])$ of $f$ on
$[a, b]$ are equal. [Trefethen2019, Theorem 10.1].
Result: best-approximation-uniqueness -/
theorem eq_of_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p q : ℝ[X]} (hp : p.degree ≤ n)
    (hq : q.degree ≤ n)
    (hpb : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n))
    (hqb : Metric.IsUniformApproxOn (fun x => q.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n)) : p = q := by
  have hdeg : ((1 / 2 : ℝ) • (p + q)).degree ≤ n :=
    (Polynomial.degree_smul_le _ _).trans ((Polynomial.degree_add_le _ _).trans (max_le hp hq))
  have hev : ∀ x, ((1 / 2 : ℝ) • (p + q)).eval x = 1 / 2 * (p.eval x + q.eval x) := by
    intro x
    simp only [Polynomial.eval_smul, Polynomial.eval_add, smul_eq_mul]
  have hrb : Metric.IsUniformApproxOn (fun x => ((1 / 2 : ℝ) • (p + q)).eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n) := by
    intro x hx
    have h1 := hpb x hx
    have h2 := hqb x hx
    simp only [Real.dist_eq, abs_le, hev] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have halt := alternatesOn_of_isUniformApproxOn_minimaxError hab hf hdeg hrb
  have hb : ∀ x ∈ Set.Icc a b,
      |f x - ((1 / 2 : ℝ) • (p + q)).eval x| ≤ minimaxError f (Set.Icc a b) n := by
    intro x hx
    rw [abs_sub_comm, ← Real.dist_eq]
    exact hrb x hx
  obtain ⟨x, hxm, hxmem, σ, hσ, hxeq⟩ := halt.exists_eq_of_abs_le hb
  have hpq : ∀ i : Fin (n + 2), p.eval (x i) = q.eval (x i) := by
    -- at the extremal points of the midpoint both errors are extremal with the same sign
    intro i
    have hi := hxeq i
    have h1 := hpb (x i) (hxmem i)
    have h2 := hqb (x i) (hxmem i)
    rw [Real.dist_eq, abs_le] at h1 h2
    rw [hev] at hi
    rcases hσ with rfl | rfl <;> rcases neg_one_pow_eq_or ℝ (i : ℕ) with h | h <;>
      rw [h] at hi <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine Polynomial.eq_of_degree_sub_lt_of_eval_index_eq Finset.univ
    (fun i _ j _ hij => hxm.injective hij) ?_ (fun i _ => hpq i)
  refine lt_of_le_of_lt ((Polynomial.degree_sub_le p q).trans (max_le hp hq)) ?_
  rw [Finset.card_univ, Fintype.card_fin]
  exact_mod_cast (by omega : n < n + 2)

/-- **The best approximation interpolates**: for $a < b$, $f$ continuous on $[a, b]$ and $p$ a
best approximation of degree at most $n$, there are $n + 1$ distinct points of $(a, b)$ at which
$p = f$; $p$ is the Lagrange interpolant of $f$ there (`Lagrange.eq_interpolate_of_eval_eq`).
[Trefethen2019, Theorem 10.1]. The intermediate value theorem between consecutive extrema gives
the interpolation points; there on $[-1, 1]$.
Result: best-approximant-interpolates -/
theorem exists_eval_eq_of_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n)) :
    ∃ t : Finset ℝ, t.card = n + 1 ∧ (t : Set ℝ) ⊆ Set.Ioo a b ∧ ∀ x ∈ t, p.eval x = f x := by
  have key : ∃ c : Fin (n + 1) → ℝ, StrictMono c ∧ (∀ i, c i ∈ Set.Ioo a b) ∧
      ∀ i, p.eval (c i) = f (c i) := by
    rcases (minimaxError_nonneg f (Set.Icc a b) n).eq_or_lt with hE | hE
    · -- `f = p` on `[a, b]`: any `n + 1` interior points
      obtain ⟨c, hc, hcs⟩ := exists_strictMono_mem_Ioo hab (n + 1)
      exact ⟨c, hc, hcs, fun i =>
        dist_le_zero.mp ((hbest _ (Set.Ioo_subset_Icc_self (hcs i))).trans_eq hE.symm)⟩
    · obtain ⟨x, hxmono, hxmem, σ, hσ, hx⟩ := alternatesOn_iff.mp
        (alternatesOn_of_isUniformApproxOn_minimaxError hab hf hp hbest)
      -- `f - p` changes sign between consecutive points of the equioscillation
      have hsign := mul_neg_of_pos_mul_neg_one_pow (u := fun i => f (x i) - p.eval (x i)) hσ
        fun i => hE.trans_le (hx i)
      have hf' : ContinuousOn (fun x => f x - p.eval x) (Set.Icc (x 0) (x (Fin.last (n + 1)))) :=
        (hf.sub p.continuousOn).mono (Set.Icc_subset_Icc (hxmem 0).1 (hxmem _).2)
      obtain ⟨c, hcmono, hcspec⟩ := exists_strictMono_eq_zero_of_mul_neg hxmono hf' hsign
      refine ⟨c, hcmono, fun i => ?_, fun i => ?_⟩
      · obtain ⟨h1, h2⟩ := hcspec i
        exact ⟨lt_of_le_of_lt (hxmem _).1 h1.1, lt_of_lt_of_le h1.2 (hxmem _).2⟩
      · linarith [(hcspec i).2]
  obtain ⟨c, hcm, hcin, hceq⟩ := key
  refine ⟨Finset.univ.image c, by simp [Finset.card_image_of_injective _ hcm.injective], ?_,
    by simpa using hceq⟩
  simpa [Set.range_subset_iff] using hcin

/-! ### The chosen best approximation on an interval -/

/-- **The chosen best approximation equioscillates**: for $a < b$ and $f$ continuous on $[a, b]$,
$f - \mathrm{minimaxPoly}\ f\ [a, b]\ n$ alternates on $[a, b]$ at $n + 2$ points with level
$E_n(f; [a, b])$. [Trefethen2019, Theorem 10.1].
Result: equioscillation -/
theorem alternatesOn_minimaxPoly {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (n : ℕ) :
    AlternatesOn (fun x => f x - (minimaxPoly f (Set.Icc a b) n).eval x) (Set.Icc a b) (n + 2)
      (minimaxError f (Set.Icc a b) n) :=
  alternatesOn_of_isUniformApproxOn_minimaxError hab hf (degree_minimaxPoly_le f _ n)
    (isUniformApproxOn_minimaxPoly isCompact_Icc hf n)

/-- **Every best approximation is the chosen one**: for $a < b$, $f$ continuous on $[a, b]$ and
$p$ a real polynomial of degree at most $n$ with $\lvert f - p \rvert \le E_n(f; [a, b])$ on
$[a, b]$, $p = \mathrm{minimaxPoly}\ f\ [a, b]\ n$. [Trefethen2019, Theorem 10.1].
Result: best-approximation-uniqueness -/
theorem eq_minimaxPoly_of_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n)) : p = minimaxPoly f (Set.Icc a b) n :=
  eq_of_isUniformApproxOn_minimaxError hab hf hp (degree_minimaxPoly_le f _ n) hbest
    (isUniformApproxOn_minimaxPoly isCompact_Icc hf n)

/-! ### The Chebyshev example -/

/-- **$T_n$ alternates at $n + 1$ points**: the Chebyshev polynomial $T_n$ alternates on
$[-1, 1]$ at $n + 1$ points with level $1$, at the extrema $\cos(j\pi/n)$ in increasing order.
[Trefethen2019, Ch. 3]. -/
theorem alternatesOn_eval_T_real (n : ℕ) :
    AlternatesOn (fun x => (Chebyshev.T ℝ (n : ℤ)).eval x) (Set.Icc (-1) 1) (n + 1) 1 := by
  rw [alternatesOn_iff]
  refine ⟨fun i => Polynomial.Chebyshev.node n (n - (i : ℕ)), ?_, ?_, (-1) ^ n, ?_, ?_⟩
  · intro i j hij
    exact Polynomial.Chebyshev.node_lt (Nat.sub_le n _)
      (by have := Fin.lt_def.mp hij; have := j.isLt; omega)
  · intro i
    exact Polynomial.Chebyshev.node_mem_Icc
  · exact neg_one_pow_eq_or ℝ n
  · intro i
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    change 1 ≤ (-1) ^ n * (-1) ^ (i : ℕ) * eval (Polynomial.Chebyshev.node n (n - (i : ℕ)))
      (Polynomial.Chebyshev.T ℝ (n : ℤ))
    rw [Polynomial.Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr (Nat.sub_le n _))]
    rw [← pow_add, ← pow_add]
    have e : n + (i : ℕ) + (n - (i : ℕ)) = 2 * n := by omega
    rw [e, pow_mul]
    norm_num

/-- **The minimax error of $x^{n + 1}$**: on $[-1, 1]$, the best approximation of $x^{n + 1}$ by
polynomials of degree at most $n$ has error $E_n(x^{n + 1}; [-1, 1]) = 2^{-n}$, attained by
$x^{n + 1} - 2^{-n}T_{n + 1}$; equivalently, $2^{-n}T_{n + 1}$ is the monic polynomial of degree
$n + 1$ of least uniform norm on $[-1, 1]$. [GolubMeurant2010, §2.5.1, Theorem 2.15];
[Trefethen2019, Ch. 10].
Result: chebyshev-monic-minimal -/
theorem minimaxError_pow_Icc_neg_one_one (n : ℕ) :
    minimaxError (fun x => x ^ (n + 1)) (Set.Icc (-1) 1) n = ((2 : ℝ) ^ n)⁻¹ := by
  have hc0 : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have hTlead : (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).leadingCoeff = 2 ^ n := by
    rw [Chebyshev.leadingCoeff_T]
    simp; omega
  have hTdeg : (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).natDegree = n + 1 := by
    rw [Chebyshev.natDegree_T]
    rfl
  have hT0 : Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ) ≠ 0 := fun h => by
    rw [h, leadingCoeff_zero] at hTlead
    exact pow_ne_zero n two_ne_zero hTlead.symm
  -- the error of `p = X^(n+1) - 2^(-n) T_(n+1)` is `2^(-n) T_(n+1)`
  have hfun (x : ℝ) : x ^ (n + 1) - (X ^ (n + 1) - C ((2 : ℝ) ^ n)⁻¹ *
      Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x =
      ((2 : ℝ) ^ n)⁻¹ * (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x := by
    simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C]
    ring
  have hdeg : (X ^ (n + 1) - C ((2 : ℝ) ^ n)⁻¹ *
      Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).degree ≤ (n : WithBot ℕ) := by
    have hq : (C ((2 : ℝ) ^ n)⁻¹ * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).degree =
        ((n + 1 : ℕ) : WithBot ℕ) := by
      rw [degree_C_mul hc0.ne', degree_eq_natDegree hT0, hTdeg]
    have hlc : (X ^ (n + 1) : ℝ[X]).leadingCoeff =
        (C ((2 : ℝ) ^ n)⁻¹ * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).leadingCoeff := by
      rw [leadingCoeff_X_pow, leadingCoeff_mul, leadingCoeff_C, hTlead]
      exact (inv_mul_cancel₀ (by positivity)).symm
    have hlt := degree_sub_lt_left (by rw [degree_X_pow, hq]) (pow_ne_zero _ X_ne_zero) hlc
    rw [degree_X_pow] at hlt
    exact Order.le_of_lt_succ hlt
  have halt : AlternatesOn (fun x : ℝ => x ^ (n + 1) - (X ^ (n + 1) - C ((2 : ℝ) ^ n)⁻¹ *
      Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x) (Set.Icc (-1) 1) (n + 2) ((2 : ℝ) ^ n)⁻¹ := by
    simp only [hfun]
    obtain ⟨x, hx, hxs, σ, hσ, h⟩ := alternatesOn_eval_T_real (n + 1)
    refine ⟨x, hx, hxs, σ, hσ, fun i => ?_⟩
    have := mul_le_mul_of_nonneg_left (h i) hc0.le
    linarith
  have hbound : Metric.IsUniformApproxOn
      (fun x => (X ^ (n + 1) - C ((2 : ℝ) ^ n)⁻¹ * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x)
      (fun x => x ^ (n + 1)) (Set.Icc (-1) 1) ((2 : ℝ) ^ n)⁻¹ := by
    intro x hx
    rw [Real.dist_eq, abs_sub_comm, hfun, abs_mul, abs_of_pos hc0]
    exact mul_le_of_le_one_right hc0.le (abs_le.mpr (Chebyshev.eval_T_real_mem_Icc _ hx))
  exact halt.minimaxError_eq hdeg hbound

end NLAlib
