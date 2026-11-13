/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.ContinuousMap.Polynomial
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import NLAlib.ForMathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The minimax error of polynomial approximation

The best uniform error $E_n(f; s)$ of approximating a real function $f$ on a set
$s \subseteq \mathbb{R}$ by real polynomials of degree at most $n$. For $s$ compact and $f$
continuous on $s$ a best approximant of degree at most $n$ exists, so $E_n(f; s)$ is a minimum;
$E_n$ is nonnegative, antitone in $n$, monotone in $s$, invariant under adding a polynomial of
degree at most $n$, absolutely homogeneous, subadditive and invariant under affine changes of
variable, and tends to $0$ on an interval (Weierstrass).

## Main definitions

* `NLAlib.minimaxError`: $E_n(f; s)$.
* `NLAlib.minimaxPoly`: a best approximation of degree at most $n$, chosen; on an interval, with
  $f$ continuous, the best approximation.

## Main results

* `NLAlib.minimaxError_le_of_isUniformApproxOn`: every approximant bounds $E_n$.
* `NLAlib.exists_degree_le_isUniformApproxOn_minimaxError`: a best approximant exists.
* `NLAlib.isLeast_minimaxError`, `NLAlib.minimaxError_eq_infDist`: $E_n$ as a minimum and as
  Mathlib's distance to the restricted polynomials in `C(s, ℝ)`.
* `NLAlib.degree_minimaxPoly_le`, `NLAlib.isUniformApproxOn_minimaxPoly`: the chosen best
  approximation `NLAlib.minimaxPoly`.
* `NLAlib.antitone_minimaxError`, `NLAlib.minimaxError_le_minimaxError_of_subset`,
  `NLAlib.minimaxError_add_eval`, `NLAlib.minimaxError_const_mul`, `NLAlib.minimaxError_add_le`:
  the algebra of $E_n$.
* `NLAlib.minimaxError_comp_mul_add`, `NLAlib.minimaxError_comp_Icc_neg_one_one`: affine
  invariance and the change of interval to $[-1, 1]$.
* `NLAlib.tendsto_minimaxError_atTop`: $E_n(f; [a, b]) \to 0$.
-/

@[expose] public section

open Polynomial
open scoped Topology

namespace NLAlib

/-- The **minimax error** of $f$ on $s$ at degree $n$,
$$E_n(f; s) := \inf\bigl\{\varepsilon : \exists p \in \mathbb{R}[x],\ \deg p \le n,\
\lvert f(x) - p(x) \rvert \le \varepsilon \text{ for all } x \in s\bigr\},$$
the error of the best uniform approximation of $f$ on $s$ by real polynomials of degree at most
$n$, through the library's uniform-approximation interface `Metric.IsUniformApproxOn`.
Junk values: $0$ when no polynomial of degree at most $n$ is within a finite distance of $f$ on
$s$ (the set is empty; for example $f$ unbounded on a bounded $s$), and $0$ for $s = \emptyset$
(the set is all of $\mathbb{R}$). It is meaningful whenever some polynomial of degree at most $n$
is within a finite distance of $f$ on $s$, in particular for $s$ compact and $f$ continuous on
$s$, where the infimum is attained. [Trefethen2019, Ch. 10]; [Rivlin1981, Ch. 1]. -/
noncomputable def minimaxError (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) : ℝ :=
  sInf {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
    Metric.IsUniformApproxOn (fun x => p.eval x) f s ε}

open Classical in
/-- A **best approximation** of $f$ on $s$ by real polynomials of degree at most $n$: some $p$
with $\deg p \le n$ and $\lvert f(x) - p(x) \rvert \le E_n(f; s)$ for all $x \in s$, chosen.
It exists for $s$ compact and $f$ continuous on $s$; on an interval $[a, b]$, $a < b$, it is the
unique best approximation (`NLAlib.eq_minimaxPoly_of_isUniformApproxOn_minimaxError`), so the
choice is canonical there. Junk value: $0$ when no best approximation of degree at most $n$
exists. Its degree is at most $n$ in every case. [Trefethen2019, Ch. 10]; [Rivlin1981, Ch. 1]. -/
noncomputable def minimaxPoly (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) : ℝ[X] :=
  if h : ∃ p : ℝ[X], p.degree ≤ n ∧
      Metric.IsUniformApproxOn (fun x => p.eval x) f s (minimaxError f s n) then
    h.choose
  else 0

/-! ### Bounds and existence -/

/-- On the empty set every error is admissible, so the minimax error is the junk value $0$. -/
private theorem minimaxError_empty (f : ℝ → ℝ) (n : ℕ) : minimaxError f ∅ n = 0 := by
  unfold minimaxError
  convert Real.sInf_univ
  exact Set.eq_univ_of_forall fun ε => ⟨0, by simp, fun x hx => absurd hx (Set.notMem_empty x)⟩

/-- The minimax error is nonnegative: $0 \le E_n(f; s)$, for every $f$, $s$ and $n$ (the junk
values are $0$). -/
theorem minimaxError_nonneg (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) : 0 ≤ minimaxError f s n := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact (minimaxError_empty f n).ge
  · exact Real.sInf_nonneg fun ε ⟨_, _, hpε⟩ => hpε.nonneg hs

/-- Every approximant bounds the minimax error: if $\deg p \le n$ and
$\lvert f(x) - p(x) \rvert \le \varepsilon$ on $s$ with $0 \le \varepsilon$, then
$E_n(f; s) \le \varepsilon$. The form in which a constructive approximation theorem (Jackson,
Bernstein ellipse, Chebyshev) bounds $E_n$. -/
theorem minimaxError_le_of_isUniformApproxOn {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {p : ℝ[X]}
    (hp : p.degree ≤ n) {ε : ℝ} (hε₀ : 0 ≤ ε)
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f s ε) : minimaxError f s n ≤ ε := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact (minimaxError_empty f n).trans_le hε₀
  · exact csInf_le ⟨0, fun _ ⟨_, _, h⟩ => h.nonneg hne⟩ ⟨p, hp, hε⟩

/-- **A best approximation exists**: for $s$ compact and $f$ continuous on $s$ there is a real
polynomial $p$ of degree at most $n$ with $\lvert f(x) - p(x) \rvert \le E_n(f; s)$ on $s$.
This is how a bound stated for an arbitrary approximant is restated with $E_n$.
[Trefethen2019, Theorem 10.1]; there on $[-1, 1]$ or an
interval, here on any compact set, the empty set included.
Result: best-approximation-existence -/
theorem exists_degree_le_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {s : Set ℝ}
    (hs : IsCompact s) (hf : ContinuousOn f s) (n : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ n ∧
      Metric.IsUniformApproxOn (fun x => p.eval x) f s (minimaxError f s n) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by simp, fun x hx => absurd hx (Set.notMem_empty x)⟩
  have := isCompact_iff_compactSpace.mp hs
  let g : C(s, ℝ) := ⟨s.domRestrict f, continuousOn_iff_continuous_domRestrict.mp hf⟩
  let P : Submodule ℝ C(s, ℝ) := (degreeLE ℝ n).map (toContinuousMapOnAlgHom s).toLinearMap
  have : FiniteDimensional ℝ (degreeLE ℝ n) := by
    rw [← degreeLT_succ_eq_degreeLE]
    exact LinearEquiv.finiteDimensional (degreeLTEquiv ℝ (n + 1)).symm
  have hpt (q : ℝ[X]) (z : s) :
      dist (g z) (toContinuousMapOnAlgHom s q z) = dist (f z) (q.eval z) := by
    simp [g, Real.dist_eq]
  -- the pointwise error of `q` is at most the distance from `g` to its restriction
  have hle (q : ℝ[X]) : Metric.IsUniformApproxOn (fun x => q.eval x) f s
      (dist g (toContinuousMapOnAlgHom s q)) := fun x hx => by
    rw [dist_comm, ← hpt q ⟨x, hx⟩]
    exact ContinuousMap.dist_apply_le_dist (f := g) (g := toContinuousMapOnAlgHom s q) ⟨x, hx⟩
  obtain ⟨y, hyP, hy⟩ := Submodule.exists_infDist_eq_dist P g
  obtain ⟨p, hpn, rfl⟩ := Submodule.mem_map.mp hyP
  -- the nearest point attains the infimum
  have hleast : IsLeast {ε : ℝ | ∃ q : ℝ[X], q.degree ≤ n ∧
      Metric.IsUniformApproxOn (fun x => q.eval x) f s ε}
      (dist g (toContinuousMapOnAlgHom s p)) := by
    refine ⟨⟨p, mem_degreeLE.mp hpn, hle p⟩, ?_⟩
    rintro ε ⟨q, hqn, hq⟩
    calc dist g (toContinuousMapOnAlgHom s p) = Metric.infDist g (P : Set C(s, ℝ)) := hy.symm
      _ ≤ dist g (toContinuousMapOnAlgHom s q) :=
        Metric.infDist_le_dist_of_mem (Submodule.mem_map_of_mem (mem_degreeLE.mpr hqn))
      _ ≤ ε := (ContinuousMap.dist_le (hq.nonneg hne)).mpr fun z => by
          rw [hpt q z, dist_comm]; exact hq z z.2
  refine ⟨p, mem_degreeLE.mp hpn, ?_⟩
  rw [show minimaxError f s n = _ from hleast.csInf_eq]
  exact hle p

/-- The minimax error is a minimum: for $s$ compact and nonempty and $f$ continuous on $s$,
$E_n(f; s)$ is the least $\varepsilon$ such that some real polynomial of degree at most $n$ is
within $\varepsilon$ of $f$ on $s$. [Trefethen2019, Ch. 10]. -/
theorem isLeast_minimaxError {f : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s) (hne : s.Nonempty)
    (hf : ContinuousOn f s) (n : ℕ) :
    IsLeast {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
      Metric.IsUniformApproxOn (fun x => p.eval x) f s ε} (minimaxError f s n) := by
  refine ⟨exists_degree_le_isUniformApproxOn_minimaxError hs hf n, ?_⟩
  rintro ε ⟨p, hp, hε⟩
  exact minimaxError_le_of_isUniformApproxOn hp (hε.nonneg hne) hε

/-- The bridge to Mathlib's distance: for compact $s$ and $g \in C(s, \mathbb{R})$ agreeing with
$f$ on $s$, $E_n(f; s)$ is the distance in $C(s, \mathbb{R})$ from $g$ to the restrictions of the
real polynomials of degree at most $n$. -/
theorem minimaxError_eq_infDist {s : Set ℝ} [CompactSpace s] {f : ℝ → ℝ} (g : C(s, ℝ))
    (hg : ∀ x : s, g x = f x) (n : ℕ) :
    minimaxError f s n = Metric.infDist g
      ((degreeLE ℝ n).map (toContinuousMapOnAlgHom s).toLinearMap : Set C(s, ℝ)) := by
  have hmem : ∀ p : ℝ[X], p.degree ≤ n →
      p.toContinuousMapOn s ∈ ((degreeLE ℝ n).map (toContinuousMapOnAlgHom s).toLinearMap :
        Set C(s, ℝ)) := by
    intro p hp
    exact Submodule.mem_map_of_mem (mem_degreeLE.mpr hp)
  have hPne : (((degreeLE ℝ n).map (toContinuousMapOnAlgHom s).toLinearMap :
      Submodule ℝ C(s, ℝ)) : Set C(s, ℝ)).Nonempty :=
    ⟨_, hmem 0 (by simp)⟩
  have hf : ContinuousOn f s := continuousOn_iff_continuous_domRestrict.mpr <| by
    rw [show s.domRestrict f = g from funext fun x => (hg x).symm]
    exact g.continuous
  apply le_antisymm
  · refine (Metric.le_infDist hPne).mpr fun y hy => ?_
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hy
    refine minimaxError_le_of_isUniformApproxOn (mem_degreeLE.mp hq) dist_nonneg fun x hx => ?_
    simpa [hg, dist_comm] using
      ContinuousMap.dist_apply_le_dist (f := g) (g := toContinuousMapOnAlgHom s q) ⟨x, hx⟩
  · obtain ⟨p, hp, hpε⟩ := exists_degree_le_isUniformApproxOn_minimaxError
      (isCompact_iff_compactSpace.mpr inferInstance) hf n
    refine (Metric.infDist_le_dist_of_mem (hmem p hp)).trans
      ((ContinuousMap.dist_le (minimaxError_nonneg f s n)).mpr fun x => ?_)
    simpa [hg, dist_comm] using hpε x x.2

/-! ### The chosen best approximation -/

/-- The chosen best approximation has degree at most $n$:
$\deg(\mathrm{minimaxPoly}\ f\ s\ n) \le n$, for every $f$, $s$ and $n$ (the junk value is $0$). -/
theorem degree_minimaxPoly_le (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) :
    (minimaxPoly f s n).degree ≤ n := by
  unfold minimaxPoly
  split_ifs with h
  · exact h.choose_spec.1
  · simp

/-- The chosen best approximation attains the minimax error: for $s$ compact and $f$
continuous on $s$, $\lvert f(x) - \mathrm{minimaxPoly}\ f\ s\ n\ (x) \rvert \le E_n(f; s)$ for
all $x \in s$. -/
theorem isUniformApproxOn_minimaxPoly {f : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) (n : ℕ) :
    Metric.IsUniformApproxOn (fun x => (minimaxPoly f s n).eval x) f s
      (minimaxError f s n) := by
  have h := exists_degree_le_isUniformApproxOn_minimaxError hs hf n
  unfold minimaxPoly
  rw [dif_pos h]
  exact h.choose_spec.2

/-! ### The algebra of the minimax error -/

/-- The minimax error is antitone in the degree: for $s$ compact and $f$ continuous on $s$,
$E_m(f; s) \ge E_n(f; s)$ for $m \le n$. -/
theorem antitone_minimaxError {f : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) : Antitone (minimaxError f s) := by
  intro m n hmn
  obtain ⟨p, hp, hpx⟩ := exists_degree_le_isUniformApproxOn_minimaxError hs hf m
  exact minimaxError_le_of_isUniformApproxOn (hp.trans (by exact_mod_cast hmn))
    (minimaxError_nonneg f s m) hpx

/-- The minimax error is monotone in the set: for $t$ compact, $f$ continuous on $t$ and
$s \subseteq t$, $E_n(f; s) \le E_n(f; t)$. -/
theorem minimaxError_le_minimaxError_of_subset {f : ℝ → ℝ} {s t : Set ℝ} (ht : IsCompact t)
    (hf : ContinuousOn f t) (hst : s ⊆ t) (n : ℕ) :
    minimaxError f s n ≤ minimaxError f t n := by
  obtain ⟨p, hp, hε⟩ := exists_degree_le_isUniformApproxOn_minimaxError ht hf n
  exact minimaxError_le_of_isUniformApproxOn hp (minimaxError_nonneg f t n) (hε.mono_set hst)

/-- Adding a polynomial of degree at most $n$ does not change the minimax error:
$E_n(f + q; s) = E_n(f; s)$ for $\deg q \le n$, for every $f$ and $s$.
This follows from the best-approximation definition in [Trefethen2019, Chapter 10]. -/
theorem minimaxError_add_eval (f : ℝ → ℝ) (s : Set ℝ) {n : ℕ} {q : ℝ[X]} (hq : q.degree ≤ n) :
    minimaxError (fun x => f x + q.eval x) s n = minimaxError f s n := by
  unfold minimaxError
  congr 1
  ext ε
  constructor
  · rintro ⟨p, hp, hε⟩
    refine ⟨p - q, (degree_sub_le _ _).trans (max_le hp hq), fun x hx => (hε x hx).trans_eq' ?_⟩
    simp only [Real.dist_eq, eval_sub]
    congr 1; ring
  · rintro ⟨p, hp, hε⟩
    exact ⟨p + q, (degree_add_le _ _).trans (max_le hp hq), fun x hx => by
      simpa only [eval_add, dist_add_right] using hε x hx⟩

/-- The minimax error is absolutely homogeneous: $E_n(cf; s) = \lvert c \rvert E_n(f; s)$, for
every $c$, $f$, $s$ and $n$ (junk values included). This follows from the best-approximation
definition in [Trefethen2019, Chapter 10]. -/
theorem minimaxError_const_mul (c : ℝ) (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) :
    minimaxError (fun x => c * f x) s n = |c| * minimaxError f s n := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : minimaxError (fun x => (0 : ℝ) * f x) s n = 0 :=
      le_antisymm
        (minimaxError_le_of_isUniformApproxOn (p := 0) (by simp) le_rfl
          (fun x _ => by simp))
        (minimaxError_nonneg _ _ _)
    rw [h0, abs_zero, zero_mul]
  · open scoped Pointwise in
    have hS : {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
        Metric.IsUniformApproxOn (fun x => p.eval x) (fun x => c * f x) s ε} =
        |c| • {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
        Metric.IsUniformApproxOn (fun x => p.eval x) f s ε} := by
      ext ε
      simp only [Set.mem_smul_set, Set.mem_ofPred_eq, smul_eq_mul, Metric.IsUniformApproxOn,
        Real.dist_eq]
      constructor
      · rintro ⟨p, hp, hε⟩
        refine ⟨|c|⁻¹ * ε, ⟨C c⁻¹ * p, by rw [degree_C_mul (inv_ne_zero hc)]; exact hp, ?_⟩,
          mul_inv_cancel_left₀ (abs_ne_zero.mpr hc) ε⟩
        intro x hx
        rw [eval_mul, eval_C, show c⁻¹ * p.eval x - f x = c⁻¹ * (p.eval x - c * f x) by
          field_simp, abs_mul, abs_inv]
        gcongr
        exact hε x hx
      · rintro ⟨η, ⟨p, hp, hη⟩, rfl⟩
        refine ⟨C c * p, by rw [degree_C_mul hc]; exact hp, ?_⟩
        intro x hx
        rw [eval_mul, eval_C, ← mul_sub, abs_mul]
        gcongr
        exact hη x hx
    unfold minimaxError
    rw [hS, Real.sInf_smul_of_nonneg (abs_nonneg c), smul_eq_mul]

/-- The minimax error is subadditive: for $s$ compact and $f, g$ continuous on $s$,
$E_n(f + g; s) \le E_n(f; s) + E_n(g; s)$. This follows from the best-approximation definition in
[Trefethen2019, Chapter 10]. -/
theorem minimaxError_add_le {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (n : ℕ) :
    minimaxError (fun x => f x + g x) s n ≤ minimaxError f s n + minimaxError g s n := by
  obtain ⟨p, hp, hpε⟩ := exists_degree_le_isUniformApproxOn_minimaxError hs hf n
  obtain ⟨q, hq, hqε⟩ := exists_degree_le_isUniformApproxOn_minimaxError hs hg n
  refine minimaxError_le_of_isUniformApproxOn (p := p + q)
    ((degree_add_le _ _).trans (max_le hp hq))
    (add_nonneg (minimaxError_nonneg _ _ _) (minimaxError_nonneg _ _ _)) ?_
  intro x hx
  have h1 := hpε x hx
  have h2 := hqε x hx
  simp only [Polynomial.eval_add]
  calc |p.eval x + q.eval x - (f x + g x)|
      = |(p.eval x - f x) + (q.eval x - g x)| := by congr 1; ring
    _ ≤ |p.eval x - f x| + |q.eval x - g x| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- **Affine invariance of the minimax error**: for $\alpha \ne 0$,
$E_n\bigl(f(\alpha\,\cdot + \beta); \{t : \alpha t + \beta \in s\}\bigr) = E_n(f; s)$, for every
$f$ and $s$. [Trefethen2019, Ch. 10]. -/
theorem minimaxError_comp_mul_add (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) {α : ℝ} (hα : α ≠ 0)
    (β : ℝ) :
    minimaxError (fun t => f (α * t + β)) ((fun t => α * t + β) ⁻¹' s) n =
      minimaxError f s n := by
  have hdeg : ∀ (p L : ℝ[X]), p.degree ≤ n → L.natDegree ≤ 1 → (p.comp L).degree ≤ n := by
    intro p L hp hL
    exact degree_le_of_natDegree_le (natDegree_comp_le.trans
      ((Nat.mul_le_mul (natDegree_le_of_degree_le hp) hL).trans_eq (mul_one n)))
  unfold minimaxError
  congr 1
  ext ε
  constructor
  · rintro ⟨q, hq, hε⟩
    refine ⟨q.comp (C α⁻¹ * X - C (α⁻¹ * β)), hdeg _ _ hq ?_, fun y hy => ?_⟩
    · compute_degree!
    · have e2 : α * (α⁻¹ * y - α⁻¹ * β) + β = y := by field_simp; ring
      simpa only [eval_comp, eval_sub, eval_mul, eval_C, eval_X, e2] using
        hε (α⁻¹ * y - α⁻¹ * β) (by rwa [Set.mem_preimage, e2])
  · rintro ⟨p, hp, hε⟩
    refine ⟨p.comp (C α * X + C β), hdeg _ _ hp ?_, fun t ht => ?_⟩
    · compute_degree!
    · simpa only [eval_comp, eval_add, eval_mul, eval_C, eval_X] using hε _ ht

/-- **Change of interval**: for $a < b$, pulling $f$ back from $[a, b]$ to $[-1, 1]$ by
$t \mapsto ((b - a)t + b + a)/2$, the map used by the Chebyshev and Bernstein-ellipse
approximations, preserves the minimax error. [Trefethen2019, Ch. 10]. -/
theorem minimaxError_comp_Icc_neg_one_one (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (n : ℕ) :
    minimaxError (fun t => f (((b - a) * t + b + a) / 2)) (Set.Icc (-1) 1) n =
      minimaxError f (Set.Icc a b) n := by
  have hpos : 0 < (b - a) / 2 := by linarith
  have h := minimaxError_comp_mul_add f (Set.Icc a b) n hpos.ne' ((b + a) / 2)
  have hf : (fun t => f (((b - a) * t + b + a) / 2)) =
      fun t => f ((b - a) / 2 * t + (b + a) / 2) := by
    funext t
    congr 1
    ring
  have hs : (fun t : ℝ => (b - a) / 2 * t + (b + a) / 2) ⁻¹' Set.Icc a b = Set.Icc (-1) 1 := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> intro <;> constructor <;> nlinarith
  rw [hf, ← hs]
  exact h

/-- **The minimax error tends to zero** on an interval: for $f$ continuous on $[a, b]$,
$E_n(f; [a, b]) \to 0$ as $n \to \infty$ (Weierstrass). [Trefethen2019, Ch. 6]. -/
theorem tendsto_minimaxError_atTop {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Set.Icc a b)) :
    Filter.Tendsto (minimaxError f (Set.Icc a b)) Filter.atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf (ε / 2) (by linarith)
  refine ⟨p.natDegree, fun n hn => ?_⟩
  have hdeg : p.degree ≤ n := Polynomial.degree_le_natDegree.trans (by exact_mod_cast hn)
  have hunif : Metric.IsUniformApproxOn (fun x => eval x p) f (Set.Icc a b) (ε / 2) :=
    fun x hx => by rw [Real.dist_eq]; exact (hp x hx).le
  have hle := minimaxError_le_of_isUniformApproxOn hdeg (by linarith) hunif
  have hnn := minimaxError_nonneg f (Set.Icc a b) n
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

end NLAlib
