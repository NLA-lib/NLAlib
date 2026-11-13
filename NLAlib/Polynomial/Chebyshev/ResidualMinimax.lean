/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Chebyshev.Residual
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Sion

/-!
# The residual minimax value on a finite set

On a finite nonempty set $s \subset \mathbb{R}$ the residual minimax value
$E = \mathsf{residualMinimax}(s, q) = \min_p\max_{x \in s}\lvert p(x) \rvert$ (real $p$,
$\deg p \le q$, $p(0) = 1$) is also a weighted least-squares value: there are probability
weights $w$ on $s$ such that $\sum_{x \in s} w_x\lvert p(x) \rvert^2 \ge E^2$ for every residual
polynomial $p$, over $\mathbb{R}$ or $\mathbb{C}$. Since
$\sum_x w_x\lvert p(x) \rvert^2 \le \max_x\lvert p(x) \rvert^2$ always, $E^2$ is the largest
value over probability weights of the weighted least-squares minimum: the discrete minimax
duality behind Greenbaum's theorem that the spectrum-minimax bounds for CG and MINRES are
attained (`NLAlib.Krylov.LinearSystems.WorstCase`).

The proof is Mathlib's Sion minimax theorem (`Sion.minimax`) for
$(w, v) \mapsto -\sum_x w_x v_x^2$ on the standard simplex (compact, the function linear in
$w$) times the value vectors $v = (p(x))_{x \in s}$ of residual polynomials (convex, the
function concave in $v$), followed by attainment of the outer maximum on the compact simplex.
No alternation theorem is needed, and none would apply in general: $x, x^2, \dots, x^q$ is not
a Haar system on a set containing points on both sides of $0$, which is the MINRES case.

The definition `residualMinimax` stays in `NLAlib.Polynomial.Chebyshev.Residual`, so that
Mathlib's Sion file is not imported by the CG files.

## Main results

* `NLAlib.exists_residualMinimax_sq_le_sum_mul_norm_sq`: the dual weights.
-/

@[expose] public section

open Polynomial Finset

namespace NLAlib

/-- The value vectors $(p(x))_{x \in s}$ of the real residual polynomials of degree at most $q$.
Proof-local. -/
private def residualValues (s : Finset ℝ) (q : ℕ) : Set (↥s → ℝ) :=
  {v | ∃ p : ℝ[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧ v = fun x : ↥s => p.eval (x : ℝ)}

/-- The weighted least-squares minimum $\inf_v\sum_x w_x v_x^2$ over the residual value
vectors. Proof-local. -/
private noncomputable def weightedResidualMin (s : Finset ℝ) (q : ℕ) (w : ↥s → ℝ) : ℝ :=
  ⨅ v : residualValues s q, ∑ i, w i * (v : ↥s → ℝ) i ^ 2

/-- The constant residual polynomial $1$ has degree at most $q$. -/
private theorem degree_one_le_natCast (q : ℕ) : (1 : ℝ[X]).degree ≤ q :=
  degree_one_le.trans (by exact_mod_cast Nat.zero_le q)

/-- The value vector of the constant residual polynomial $1$. -/
private theorem one_mem_residualValues (s : Finset ℝ) (q : ℕ) :
    (fun _ : ↥s => (1 : ℝ)) ∈ residualValues s q :=
  ⟨1, degree_one_le_natCast q, eval_one, by simp only [eval_one]⟩

/-- The residual value vectors form a convex set: a convex combination of residual polynomials
of degree at most $q$ is one. -/
private theorem convex_residualValues (s : Finset ℝ) (q : ℕ) :
    Convex ℝ (residualValues s q) := by
  rintro _ ⟨p₁, hp₁, hp₁₀, rfl⟩ _ ⟨p₂, hp₂, hp₂₀, rfl⟩ a b - - hab
  refine ⟨a • p₁ + b • p₂, (degree_add_le _ _).trans (max_le ((degree_smul_le _ _).trans hp₁)
    ((degree_smul_le _ _).trans hp₂)), ?_, ?_⟩
  · rw [eval_add, eval_smul, eval_smul, hp₁₀, hp₂₀, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      hab]
  · funext x
    simp only [Pi.add_apply, Pi.smul_apply, eval_add, eval_smul]

/-- The supremum over the simplex of $\sum_i w_i v_i^2$ is $\max_i v_i^2$: every value is at
most the maximum, and the vertex `Pi.single i 1` at a maximising $i$ attains it. -/
private theorem isLUB_sum_mul_sq_stdSimplex {s : Finset ℝ} (hs : s.Nonempty) (v : ↥s → ℝ) :
    IsLUB ((fun w : ↥s → ℝ => ∑ i, w i * v i ^ 2) '' stdSimplex ℝ ↥s) (⨆ i, v i ^ 2) := by
  have : Nonempty ↥s := hs.to_subtype
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    calc ∑ i, w i * v i ^ 2 ≤ ∑ i, w i * ⨆ j, v j ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (le_ciSup (f := fun j => v j ^ 2) (Set.finite_range _).bddAbove i) (hw.1 i)
      _ = ⨆ j, v j ^ 2 := by rw [← Finset.sum_mul, hw.2, one_mul]
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun j => v j ^ 2)
    rw [← hi]
    refine hb ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, ?_⟩
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]

/-- The infimum over residual value vectors of $\max_i v_i^2$ is
$\mathsf{residualMinimax}(s, q)^2$. -/
private theorem isGLB_iSup_sq_residualValues {s : Finset ℝ} (hs : s.Nonempty) (q : ℕ) :
    IsGLB ((fun v : ↥s → ℝ => ⨆ i, v i ^ 2) '' residualValues s q) (residualMinimax s q ^ 2) := by
  have : Nonempty ↥s := hs.to_subtype
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨_, ⟨p, hp, hp₀, rfl⟩, rfl⟩
    have h0 : 0 ≤ ⨆ i : ↥s, p.eval (i : ℝ) ^ 2 := Real.iSup_nonneg fun _ => sq_nonneg _
    have hE := residualMinimax_le (s := (s : Set ℝ)) hp hp₀ (Real.sqrt_nonneg _) fun x hx =>
      Real.le_sqrt_of_sq_le (by
        rw [sq_abs]
        exact le_ciSup (f := fun i : ↥s => p.eval (i : ℝ) ^ 2) (Set.finite_range _).bddAbove
          ⟨x, hx⟩)
    calc residualMinimax s q ^ 2 ≤ Real.sqrt (⨆ i : ↥s, p.eval (i : ℝ) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (residualMinimax_nonneg _ _) hE 2
      _ = _ := Real.sq_sqrt h0
  · rcases lt_or_ge b 0 with hb0 | hb0
    · exact hb0.le.trans (sq_nonneg _)
    have hsq : Real.sqrt b ≤ residualMinimax s q := by
      refine le_residualMinimax fun p η hp hp₀ hη0 hη =>
        Real.sqrt_le_iff.mpr ⟨hη0, ?_⟩
      refine (hb ⟨_, ⟨p, hp, hp₀, rfl⟩, rfl⟩).trans (ciSup_le fun i => ?_)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hη i i.2) 2
    calc b = Real.sqrt b ^ 2 := (Real.sq_sqrt hb0).symm
      _ ≤ residualMinimax s q ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2

/-- Negating a function turns a greatest lower bound of its image into a least upper bound. -/
private theorem isLUB_image_neg {α : Type*} {g : α → ℝ} {S : Set α} {a : ℝ}
    (h : IsGLB (g '' S) a) : IsLUB ((fun x => -g x) '' S) (-a) :=
  ⟨by rintro _ ⟨x, hx, rfl⟩; exact neg_le_neg (h.1 ⟨x, hx, rfl⟩),
    fun b hb => neg_le.mpr (h.2 fun _ ⟨x, hx, hgx⟩ => hgx ▸ neg_le.mp (hb ⟨x, hx, rfl⟩))⟩

/-- Negating a function turns a least upper bound of its image into a greatest lower bound. -/
private theorem isGLB_image_neg {α : Type*} {g : α → ℝ} {S : Set α} {a : ℝ}
    (h : IsLUB (g '' S) a) : IsGLB ((fun x => -g x) '' S) (-a) :=
  ⟨by rintro _ ⟨x, hx, rfl⟩; exact neg_le_neg (h.1 ⟨x, hx, rfl⟩),
    fun b hb => le_neg.mpr (h.2 fun _ ⟨x, hx, hgx⟩ => hgx ▸ le_neg.mp (hb ⟨x, hx, rfl⟩))⟩

/-- For nonnegative weights the weighted least-squares minimum is the greatest lower bound of the
weighted sums over the residual value vectors. -/
private theorem isGLB_weightedResidualMin (s : Finset ℝ) (q : ℕ) {w : ↥s → ℝ}
    (hw : ∀ i, 0 ≤ w i) :
    IsGLB ((fun v : ↥s → ℝ => ∑ i, w i * v i ^ 2) '' residualValues s q)
      (weightedResidualMin s q w) := by
  have : Nonempty (residualValues s q) := ⟨⟨_, one_mem_residualValues s q⟩⟩
  rw [Set.image_eq_range]
  exact isGLB_ciInf ⟨0, by
    rintro _ ⟨v, rfl⟩
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)⟩

/-- **Sion's theorem applied**: the supremum over the simplex of the weighted least-squares
minimum is $\mathsf{residualMinimax}(s, q)^2$, by `Sion.minimax` for
$(w, v) \mapsto -\sum_i w_i v_i^2$ on the simplex times the residual value vectors. -/
private theorem isLUB_weightedResidualMin {s : Finset ℝ} (hs : s.Nonempty) (q : ℕ) :
    IsLUB (weightedResidualMin s q '' stdSimplex ℝ ↥s) (residualMinimax s q ^ 2) := by
  have : Nonempty ↥s := hs.to_subtype
  set X := stdSimplex ℝ ↥s
  set Y := residualValues s q
  set f : (↥s → ℝ) → (↥s → ℝ) → ℝ := fun w v => -∑ i, w i * v i ^ 2 with hf
  have hcont : ∀ v : ↥s → ℝ, Continuous fun w : ↥s → ℝ => f w v := fun v => by
    simp only [hf]; fun_prop
  have hcont' : ∀ w : ↥s → ℝ, Continuous fun v : ↥s → ℝ => f w v := fun w => by
    simp only [hf]; fun_prop
  have ne_X : X.Nonempty := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary ↥s)⟩
  -- linear, hence quasiconvex, in the weights
  have hfy' : ∀ v ∈ Y, QuasiconvexOn ℝ X fun w => f w v := fun v _ => by
    refine ConvexOn.quasiconvexOn ⟨convex_stdSimplex ℝ ↥s, fun w₁ _ w₂ _ a b _ _ _ => le_of_eq ?_⟩
    simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_neg, neg_add, mul_assoc]
  -- concave in the values for nonnegative weights
  have hfx' : ∀ w ∈ X, QuasiconcaveOn ℝ Y fun v => f w v := fun w hw => by
    refine ConcaveOn.quasiconcaveOn ⟨convex_residualValues s q, fun v₁ _ v₂ _ a b ha hb hab => ?_⟩
    simp only [hf, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
    rw [mul_neg, mul_neg, ← neg_add, neg_le_neg_iff, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hsq : (a * v₁ i + b * v₂ i) ^ 2 ≤ a * v₁ i ^ 2 + b * v₂ i ^ 2 := by
      have hb' : b = 1 - a := by linarith
      subst hb'
      nlinarith [sq_nonneg (v₁ i - v₂ i), mul_nonneg ha hb]
    calc w i * (a * v₁ i + b * v₂ i) ^ 2 ≤ w i * (a * v₁ i ^ 2 + b * v₂ i ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (hw.1 i)
      _ = a * (w i * v₁ i ^ 2) + b * (w i * v₂ i ^ 2) := by ring
  have hglb : IsGLB ((fun w => -weightedResidualMin s q w) '' X)
      (sInf ((fun w => -weightedResidualMin s q w) '' X)) :=
    Real.isGLB_sInf (ne_X.image _) ⟨-1, by
      rintro _ ⟨w, hw, rfl⟩
      refine neg_le_neg ((isGLB_weightedResidualMin s q hw.1).1
        ⟨_, one_mem_residualValues s q, rfl⟩ |>.trans_eq ?_)
      simp only [one_pow, mul_one]
      exact hw.2⟩
  have key := Sion.minimax ne_X (isCompact_stdSimplex ℝ ↥s)
    (fun v _ => (hcont v).continuousOn.lowerSemicontinuousOn) hfy' (convex_residualValues s q)
    (fun w _ => (hcont' w).continuousOn.upperSemicontinuousOn) hfx' (convex_stdSimplex ℝ ↥s)
    (fun w => -weightedResidualMin s q w)
    (fun w hw => isLUB_image_neg (isGLB_weightedResidualMin s q hw.1))
    _ hglb
    (fun v => -⨆ i, v i ^ 2) (fun v _ => isGLB_image_neg (isLUB_sum_mul_sq_stdSimplex hs v))
    (-(residualMinimax s q ^ 2)) (isLUB_image_neg (isGLB_iSup_sq_residualValues hs q))
  have h := isLUB_image_neg (key ▸ hglb)
  simpa only [neg_neg] using h

/-- **The supremum is attained**: `weightedResidualMin s q` is upper semicontinuous, an infimum
of continuous functions, so it attains its supremum on the compact simplex. -/
private theorem exists_weightedResidualMin_eq {s : Finset ℝ} (hs : s.Nonempty) (q : ℕ) :
    ∃ w ∈ stdSimplex ℝ ↥s, weightedResidualMin s q w = residualMinimax s q ^ 2 := by
  have : Nonempty ↥s := hs.to_subtype
  have husc : UpperSemicontinuousOn (weightedResidualMin s q) (stdSimplex ℝ ↥s) :=
    upperSemicontinuousOn_ciInf (fun w hw => ⟨0, by
        rintro _ ⟨v, rfl⟩
        exact Finset.sum_nonneg fun i _ => mul_nonneg (hw.1 i) (sq_nonneg _)⟩)
      fun v => (by fun_prop : Continuous fun w : ↥s → ℝ =>
        ∑ i, w i * (v : ↥s → ℝ) i ^ 2).continuousOn.upperSemicontinuousOn
  obtain ⟨w, hw, hmax⟩ := husc.exists_isMaxOn
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary ↥s)⟩ (isCompact_stdSimplex ℝ ↥s)
  have hgr : IsGreatest (weightedResidualMin s q '' stdSimplex ℝ ↥s) (weightedResidualMin s q w) :=
    ⟨⟨w, hw, rfl⟩, by rintro _ ⟨w', hw', rfl⟩; exact hmax hw'⟩
  exact ⟨w, hw, hgr.isLUB.unique (isLUB_weightedResidualMin hs q)⟩

/-- **The real part of a residual polynomial**: for $p \in \Bbbk[X]$ with $\deg p \le q$ and
$p(0) = 1$, the polynomial $\sum_k \operatorname{Re}(p_k) X^k$ is a real residual polynomial of
degree at most $q$ with $\lvert(\operatorname{Re} p)(x)\rvert \le \lvert p(x)\rvert$ for real
$x$. -/
private theorem exists_abs_eval_le_norm_eval {𝕜 : Type*} [RCLike 𝕜] {q : ℕ} {p : 𝕜[X]}
    (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) :
    ∃ p' : ℝ[X], p'.degree ≤ q ∧ p'.eval 0 = 1 ∧ ∀ x : ℝ, |p'.eval x| ≤ ‖p.eval (x : 𝕜)‖ := by
  set p' : ℝ[X] := ∑ k ∈ Finset.range (q + 1), monomial k (RCLike.re (p.coeff k))
  have hn : p.natDegree < q + 1 := Nat.lt_succ_of_le (natDegree_le_iff_degree_le.mpr hp)
  have heval : ∀ x : ℝ, p'.eval x = RCLike.re (p.eval (x : 𝕜)) := fun x => by
    rw [eval_eq_sum_range' hn, map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_monomial, ← RCLike.ofReal_pow, RCLike.re_mul_ofReal]
  refine ⟨p', (degree_sum_le _ _).trans (Finset.sup_le fun k hk => (degree_monomial_le _ _).trans
    (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))), ?_, fun x => ?_⟩
  · rw [heval, RCLike.ofReal_zero, hp₀, RCLike.one_re]
  · rw [heval]
    exact RCLike.abs_re_le_norm _

/-- **Discrete minimax duality for residual polynomials**: for a finite nonempty $s \subset
\mathbb{R}$ and every $q$ there are weights $w \ge 0$ on $s$ with $\sum_{x \in s} w_x = 1$ such
that every $p \in \Bbbk[X]$ with $\deg p \le q$ and $p(0) = 1$ has
$$\mathsf{residualMinimax}(s, q)^2 \le \sum_{x \in s} w_x\,\lvert p(x) \rvert^2 \,.$$
Since $\sum_{x \in s} w_x\lvert p(x) \rvert^2 \le \max_{x \in s}\lvert p(x) \rvert^2$, the
weights realise the minimax value as a weighted least-squares value. No hypothesis
$0 \notin s$: if $0 \in s$ the value is $1$ and $w = \delta_0$ works.
[Greenbaum1979, Theorems 1 and 2, pp. 184–186] constructs weights attaining the sharp CG
bound. The weighted finite-set formulation here also allows zero in the set. -/
theorem exists_residualMinimax_sq_le_sum_mul_norm_sq (𝕜 : Type*) [RCLike 𝕜] {s : Finset ℝ}
    (hs : s.Nonempty) (q : ℕ) :
    ∃ w : ℝ → ℝ, (∀ x ∈ s, 0 ≤ w x) ∧ ∑ x ∈ s, w x = 1 ∧
      ∀ p : 𝕜[X], p.degree ≤ q → p.eval 0 = 1 →
        residualMinimax s q ^ 2 ≤ ∑ x ∈ s, w x * ‖p.eval (x : 𝕜)‖ ^ 2 := by
  obtain ⟨w₀, hw₀, hE⟩ := exists_weightedResidualMin_eq hs q
  set w : ℝ → ℝ := fun x => if h : x ∈ s then w₀ ⟨x, h⟩ else 0
  have hw : ∀ i : ↥s, w i = w₀ i := fun i => dif_pos i.2
  refine ⟨w, fun x hx => by simp only [w, dif_pos hx]; exact hw₀.1 _, ?_, fun p hp hp₀ => ?_⟩
  · rw [← Finset.sum_coe_sort s w, Finset.sum_congr rfl fun i _ => hw i, hw₀.2]
  obtain ⟨p', hp', hp'₀, hle⟩ := exists_abs_eval_le_norm_eval hp hp₀
  rw [← hE, ← Finset.sum_coe_sort s fun x => w x * ‖p.eval (x : 𝕜)‖ ^ 2]
  refine ((isGLB_weightedResidualMin s q hw₀.1).1 ⟨_, ⟨p', hp', hp'₀, rfl⟩, rfl⟩).trans
    (Finset.sum_le_sum fun i _ => ?_)
  rw [hw i, ← sq_abs]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hle i) 2) (hw₀.1 i)

end NLAlib
