/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Approximation.MinimaxError
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.OfFn

/-!
# Greedy uniform approximation by odd polynomials

Successive minimax polynomials approximate one on the actual images of the preceding
positive intervals. A Taylor competitor gives a doubly exponential error estimate.
The scalar argument adapts the original NLAlib atlas at commit 77514ce.

## Main results

* `NLAlib.exists_isGreedyOddMinimax`: existence of optimal staged coefficients.
* `NLAlib.IsGreedyOddMinimax.one_sub_le_pow`: the uniform error after a fixed number
  of stages.
-/

@[expose] public section

open Finset Polynomial Set
namespace NLAlib

/-- An odd degree-at-most-`2q+1` update, in its supplied scalar coefficients. -/
noncomputable def oddScalarUpdate (q : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (q + 1), a j * x ^ (2 * j + 1)

/-- The odd update with coefficients of a polynomial of degree at most $q$ sends $x$ to
$x p(x^2)$. Trailing coefficients may vanish. [AmselPerssonMuscoGower2026, Appendix E]. -/
theorem oddScalarUpdate_coeff {q : ℕ} (p : ℝ[X]) (hp : p.natDegree ≤ q) (x : ℝ) :
    oddScalarUpdate q p.coeff x = x * p.eval (x ^ 2) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.mul_sum, oddScalarUpdate]
  apply Finset.sum_congr rfl
  intro j _
  rw [← pow_mul, pow_succ]
  ring

/-- The first $q+1$ supplied coefficients encode the ordinary polynomial in the odd update.
[AmselPerssonMuscoGower2026, Appendix E]. -/
theorem oddScalarUpdate_eq_mul_eval (q : ℕ) (c : ℕ → ℝ) (x : ℝ) :
    oddScalarUpdate q c x = x * (Polynomial.ofFn (q + 1) (fun i => c i)).eval (x ^ 2) := by
  rw [← oddScalarUpdate_coeff _ (Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _))]
  unfold oddScalarUpdate
  exact Finset.sum_congr rfl fun i hi => by rw [ofFn_coeff_eq_val_of_lt _ (mem_range.mp hi)]

/-- The scalar update is continuous everywhere. -/
theorem continuous_oddScalarUpdate (q : ℕ) (a : ℕ → ℝ) : Continuous (oddScalarUpdate q a) := by
  unfold oddScalarUpdate
  fun_prop

/-- Odd updates annihilate a zero singular direction. -/
@[simp] theorem oddScalarUpdate_zero (q : ℕ) (a : ℕ → ℝ) : oddScalarUpdate q a 0 = 0 := by
  simp [oddScalarUpdate]

/-- Oddness is a proved property of the actual coefficient expression. -/
theorem oddScalarUpdate_neg (q : ℕ) (a : ℕ → ℝ) (x : ℝ) :
    oddScalarUpdate q a (-x) = -oddScalarUpdate q a x := by
  simp [oddScalarUpdate, pow_add, pow_mul, Finset.sum_neg_distrib]

/-- Apply the successive coefficient-defined updates, starting from the input. -/
noncomputable def oddScalarComposition (q : ℕ) (a : ℕ → ℕ → ℝ) (x : ℝ) : ℕ → ℝ
  | 0 => x
  | k + 1 => oddScalarUpdate q (a k) (oddScalarComposition q a x k)

/-- Every finite composition is continuous. -/
theorem continuous_oddScalarComposition (q : ℕ) (a : ℕ → ℕ → ℝ) (k : ℕ) :
    Continuous (fun x => oddScalarComposition q a x k) := by
  induction k with
  | zero => exact continuous_id
  | succ k ih => exact (continuous_oddScalarUpdate q (a k)).comp ih

/-- Every finite composition fixes a zero singular direction at zero. -/
@[simp] theorem oddScalarComposition_zero (q : ℕ) (a : ℕ → ℕ → ℝ) (k : ℕ) :
    oddScalarComposition q a 0 k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [oddScalarComposition, ih]


/-- A coefficient-defined odd update as a continuous map on an interval. -/
noncomputable def oddUpdateOn (q : ℕ) (c : ℕ → ℝ) (a b : ℝ) : C(Icc a b, ℝ) :=
  ⟨fun x => oddScalarUpdate q c x, (continuous_oddScalarUpdate q c).comp continuous_subtype_val⟩

/-- The actual uniform error when approximating the constant one. -/
noncomputable def oddUniformError (q : ℕ) (c : ℕ → ℝ) (a b : ℝ) : ℝ :=
  ‖(1 : C(Icc a b, ℝ)) - oddUpdateOn q c a b‖

/-- Genuine minimax optimality among all odd updates of the allowed degree. -/
noncomputable def IsOddMinimaxOn (q : ℕ) (c : ℕ → ℝ) (a b : ℝ) : Prop :=
  ∀ d : ℕ → ℝ, oddUniformError q c a b ≤ oddUniformError q d a b

/-- The uniform error is nonnegative, including degenerate intervals. -/
theorem oddUniformError_nonneg (q : ℕ) (c : ℕ → ℝ) (a b : ℝ) :
    0 ≤ oddUniformError q c a b := norm_nonneg _

/-- The uniform error bounds every actual point of the interval. -/
theorem abs_one_sub_oddScalarUpdate_le (q : ℕ) (c : ℕ → ℝ) (a b x : ℝ)
    (hx : x ∈ Icc a b) : |1 - oddScalarUpdate q c x| ≤ oddUniformError q c a b := by
  exact ((1 : C(Icc a b, ℝ)) - oddUpdateOn q c a b).norm_coe_le_norm ⟨x, hx⟩

/-- Pointwise bounds imply the corresponding uniform bound. -/
theorem oddUniformError_le_of_forall {q : ℕ} {c : ℕ → ℝ} {a b E : ℝ}
    (hE : 0 ≤ E) (h : ∀ x ∈ Icc a b, |1 - oddScalarUpdate q c x| ≤ E) :
    oddUniformError q c a b ≤ E := by
  apply (ContinuousMap.norm_le _ hE).mpr
  intro x
  exact h x x.property

/-- Every compact interval has an actual odd minimax update, including a
singleton interval. The chosen coefficients are ordinary scalar data. -/
theorem exists_isOddMinimaxOn (q : ℕ) (a b : ℝ) : ∃ c : ℕ → ℝ, IsOddMinimaxOn q c a b := by
  let L : (Fin (q + 1) → ℝ) →ₗ[ℝ] C(Icc a b, ℝ) :=
    { toFun := fun c =>
        ⟨fun x => ∑ j : Fin (q + 1), c j * (x : ℝ) ^ (2 * (j : ℕ) + 1), by fun_prop⟩
      map_add' := by
        intro c d
        ext x
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro t c
        ext x
        simp [Finset.mul_sum, mul_assoc] }
  have : FiniteDimensional ℝ (LinearMap.range L) := inferInstance
  obtain ⟨f, hf, hdist⟩ := Submodule.exists_infDist_eq_dist
    (LinearMap.range L) (1 : C(Icc a b, ℝ))
  have hbest := hdist.symm
  rw [dist_eq_norm] at hbest
  obtain ⟨c, rfl⟩ := hf
  let c' : ℕ → ℝ := fun j => if hj : j < q + 1 then c ⟨j, hj⟩ else 0
  have hmap (d : ℕ → ℝ) : L (fun j : Fin (q + 1) => d j) = oddUpdateOn q d a b := by
    ext x
    change (∑ j : Fin (q + 1), d j * (x : ℝ) ^ (2 * (j : ℕ) + 1)) =
      ∑ j ∈ range (q + 1), d j * (x : ℝ) ^ (2 * j + 1)
    simpa only using (Fin.sum_univ_eq_sum_range (fun j => d j * (x : ℝ) ^ (2 * j + 1)) (q + 1))
  have hc : (fun j : Fin (q + 1) => c' j) = c := by
    funext j
    dsimp only [c']
    rw [dif_pos j.isLt]
  refine ⟨c', fun d => ?_⟩
  have hp : oddUpdateOn q c' a b = L c := by rw [← hmap, hc]
  rw [oddUniformError, hp, hbest]
  simpa only [oddUniformError, dist_eq_norm, hmap] using
    (Metric.infDist_le_dist_of_mem (x := (1 : C(Icc a b, ℝ)))
      (show L (fun j : Fin (q + 1) => d j) ∈ LinearMap.range L from ⟨_, rfl⟩))

/-- Scaling all coefficients scales the actual update. -/
private theorem oddScalarUpdate_smul_coeff (q : ℕ) (c : ℕ → ℝ) (t x : ℝ) :
    oddScalarUpdate q (fun j => t * c j) x = t * oddScalarUpdate q c x := by
  simp [oddScalarUpdate, Finset.mul_sum, mul_assoc]

/-- Rescaling input and output stays inside the same odd polynomial class. -/
private theorem oddScalarUpdate_rescale (q : ℕ) (c : ℕ → ℝ) (t b x : ℝ) :
    oddScalarUpdate q (fun j => t * c j / b ^ (2 * j + 1)) x =
      t * oddScalarUpdate q c (x / b) := by
  simp only [oddScalarUpdate, div_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The constant-plus-odd coefficient convention includes every linear update. -/
private theorem oddScalarUpdate_single_zero (q : ℕ) (t x : ℝ) :
    oddScalarUpdate q (Pi.single 0 t) x = t * x := by
  unfold oddScalarUpdate
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0; simp [hj0]
  · simp

/-- Scaling a positive interval to be centered at one has exact uniform
relative-width error. The estimate also holds for singleton intervals. -/
private theorem abs_one_sub_two_div_mul_le {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hx : x ∈ Icc a b) :
    |1 - (2 / (a + b)) * x| ≤ (b - a) / (a + b) := by
  have hs : 0 < a + b := by linarith
  have hlo : 1 - (b - a) / (a + b) = (2 / (a + b)) * a := by field_simp; ring
  have hhi : 1 + (b - a) / (a + b) = (2 / (a + b)) * b := by field_simp; ring
  have hca : (2 / (a + b)) * a ≤ (2 / (a + b)) * x :=
    mul_le_mul_of_nonneg_left hx.1 (by positivity)
  have hcb : (2 / (a + b)) * x ≤ (2 / (a + b)) * b :=
    mul_le_mul_of_nonneg_left hx.2 (by positivity)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Every genuine positive-interval odd minimax error is less than one. -/
private theorem IsOddMinimaxOn.error_lt_one {q : ℕ} {c : ℕ → ℝ} {a b : ℝ}
    (h : IsOddMinimaxOn q c a b) (ha : 0 < a) (hab : a ≤ b) :
    oddUniformError q c a b < 1 := by
  have hs : 0 < a + b := by linarith
  have hr : 0 ≤ (b - a) / (a + b) := div_nonneg (sub_nonneg.mpr hab) hs.le
  have he : oddUniformError q (Pi.single 0 (2 / (a + b))) a b ≤ (b - a) / (a + b) := by
    apply oddUniformError_le_of_forall hr
    intro x hx
    rw [oddScalarUpdate_single_zero]
    exact abs_one_sub_two_div_mul_le ha hab hx
  exact ((h _).trans he).trans_lt ((div_lt_one hs).mpr (by linarith))

/-- Actual minimum and maximum values of a continuous interval update. -/
private theorem exists_oddScalarUpdate_interval_bounds (q : ℕ) (c : ℕ → ℝ) {a b : ℝ}
    (hab : a ≤ b) :
    ∃ m M : ℝ, (∀ x ∈ Icc a b, m ≤ oddScalarUpdate q c x ∧ oddScalarUpdate q c x ≤ M) ∧
      (∃ x ∈ Icc a b, oddScalarUpdate q c x = m) ∧
      (∃ x ∈ Icc a b, oddScalarUpdate q c x = M) := by
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
    (continuous_oddScalarUpdate q c).continuousOn
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab)
    (continuous_oddScalarUpdate q c).continuousOn
  exact ⟨oddScalarUpdate q c x, oddScalarUpdate q c y,
    fun z hz => ⟨hmin hz, hmax hz⟩, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩

/-- A genuine minimax interval image is positive, centered at one, and
its uniform error equals one minus its lower endpoint. No strict-length
assumption is needed; a singleton minimax image is exactly `{1}`. -/
private theorem IsOddMinimaxOn.interval_image_normalized {q : ℕ} {c : ℕ → ℝ} {a b m M : ℝ}
    (h : IsOddMinimaxOn q c a b) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x ∈ Icc a b, m ≤ oddScalarUpdate q c x ∧ oddScalarUpdate q c x ≤ M)
    (hm : ∃ x ∈ Icc a b, oddScalarUpdate q c x = m)
    (hM : ∃ x ∈ Icc a b, oddScalarUpdate q c x = M) :
    0 < m ∧ m ≤ M ∧ m + M = 2 ∧ oddUniformError q c a b = 1 - m := by
  obtain ⟨xm, hxm, hxmval⟩ := hm
  obtain ⟨xM, hxM, hxMval⟩ := hM
  have hem : |1 - m| ≤ oddUniformError q c a b := by
    simpa only [hxmval] using abs_one_sub_oddScalarUpdate_le q c a b xm hxm
  have heM : |1 - M| ≤ oddUniformError q c a b := by
    simpa only [hxMval] using abs_one_sub_oddScalarUpdate_le q c a b xM hxM
  have hE := h.error_lt_one ha hab
  have hmpos : 0 < m := by have hh := (abs_le.mp hem).2; linarith
  have hmM : m ≤ M := by simpa only [hxmval] using (hbounds xm hxm).2
  have hs : 0 < m + M := by linarith
  have hscaled : oddUniformError q (fun j => (2 / (m + M)) * c j) a b ≤
      (M - m) / (m + M) := by
    apply oddUniformError_le_of_forall (div_nonneg (sub_nonneg.mpr hmM) hs.le)
    intro x hx
    rw [oddScalarUpdate_smul_coeff]
    exact abs_one_sub_two_div_mul_le hmpos hmM (hbounds x hx)
  have hratio : oddUniformError q c a b * (m + M) ≤ M - m :=
    (le_div_iff₀ hs).mp ((h _).trans hscaled)
  have hcenter : m + M = 2 := by
    rcases lt_trichotomy (m + M) 2 with hlt | heq | hgt
    · have hlo : 1 - m ≤ oddUniformError q c a b := (le_abs_self _).trans hem
      have hh := mul_le_mul_of_nonneg_right hlo hs.le
      nlinarith
    · exact heq
    · have hhi : M - 1 ≤ oddUniformError q c a b := by
        have hh := (neg_le_abs (1 - M)).trans heM
        linarith
      have hh := mul_le_mul_of_nonneg_right hhi hs.le
      have hMpos : 0 < M := hmpos.trans_le hmM
      nlinarith
  have hnorm : oddUniformError q c a b ≤ 1 - m := by
    apply oddUniformError_le_of_forall (by linarith)
    intro x hx
    obtain ⟨hlo, hhi⟩ := hbounds x hx
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact ⟨hmpos, hmM, hcenter, le_antisymm hnorm ((le_abs_self _).trans hem)⟩

/-- A genuine greedy minimax sequence in the supplied scalar coefficients.
The bounds and their attainment characterize the true extrema of each
continuous interval image. -/
structure IsGreedyOddMinimax (q : ℕ) (ell : ℝ) (c : ℕ → ℕ → ℝ) (l u : ℕ → ℝ) : Prop where
  /-- Initial positive lower endpoint. -/
  lower_zero : l 0 = ell
  /-- Initial upper endpoint is one. -/
  upper_zero : u 0 = 1
  /-- Every update minimizes the uniform error on its current interval. -/
  minimax : ∀ k, IsOddMinimaxOn q (c k) (l k) (u k)
  /-- The image is contained in the next interval. -/
  bounds : ∀ k x, x ∈ Icc (l k) (u k) →
    l (k + 1) ≤ oddScalarUpdate q (c k) x ∧ oddScalarUpdate q (c k) x ≤ u (k + 1)
  /-- The next lower endpoint is attained. -/
  attain_lower : ∀ k, ∃ x ∈ Icc (l k) (u k), oddScalarUpdate q (c k) x = l (k + 1)
  /-- The next upper endpoint is attained. -/
  attain_upper : ∀ k, ∃ x ∈ Icc (l k) (u k), oddScalarUpdate q (c k) x = u (k + 1)

/-- Every successive actual image remains a positive interval, even if
it collapses to the singleton `{1}`. -/
private theorem IsGreedyOddMinimax.positive_intervals {q : ℕ} {ell : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q ell c l u)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (k : ℕ) : 0 < l k ∧ l k ≤ u k := by
  induction k with
  | zero => simpa only [h.lower_zero, h.upper_zero] using And.intro hell hell1
  | succ k ih =>
    have hh := (h.minimax k).interval_image_normalized ih.1 ih.2
      (h.bounds k) (h.attain_lower k) (h.attain_upper k)
    exact ⟨hh.1, hh.2.1⟩

/-- Actual interval images are centered at one; their lower endpoint
therefore records the genuine uniform minimax error. -/
private theorem IsGreedyOddMinimax.normalized_images {q : ℕ} {ell : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q ell c l u)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (k : ℕ) :
    l (k + 1) + u (k + 1) = 2 ∧ oddUniformError q (c k) (l k) (u k) = 1 - l (k + 1) := by
  have hi := h.positive_intervals hell hell1 k
  exact ((h.minimax k).interval_image_normalized hi.1 hi.2
    (h.bounds k) (h.attain_lower k) (h.attain_upper k)).2.2

/-- Every intermediate scalar iterate lies in the actual interval used
by the next minimax problem. -/
theorem IsGreedyOddMinimax.oddScalarComposition_mem_Icc {q : ℕ} {ell : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q ell c l u)
    {x : ℝ} (hx : x ∈ Icc ell 1) (k : ℕ) :
    oddScalarComposition q c x k ∈ Icc (l k) (u k) := by
  induction k with
  | zero => simpa only [oddScalarComposition, h.lower_zero, h.upper_zero] using hx
  | succ k ih => exact h.bounds k _ ih

private abbrev PositiveInterval := {p : ℝ × ℝ // 0 < p.1 ∧ p.1 ≤ p.2}

private structure GreedyOddStep (q : ℕ) (I : PositiveInterval) where
  coefficients : ℕ → ℝ
  next : PositiveInterval
  minimax : IsOddMinimaxOn q coefficients I.val.1 I.val.2
  bounds : ∀ x ∈ Icc I.val.1 I.val.2,
    next.val.1 ≤ oddScalarUpdate q coefficients x ∧ oddScalarUpdate q coefficients x ≤ next.val.2
  attain_lower : ∃ x ∈ Icc I.val.1 I.val.2, oddScalarUpdate q coefficients x = next.val.1
  attain_upper : ∃ x ∈ Icc I.val.1 I.val.2, oddScalarUpdate q coefficients x = next.val.2

private theorem nonempty_greedyOddStep (q : ℕ) (I : PositiveInterval) :
    Nonempty (GreedyOddStep q I) := by
  obtain ⟨c, hc⟩ := exists_isOddMinimaxOn q I.val.1 I.val.2
  obtain ⟨m, M, hb, hm, hM⟩ := exists_oddScalarUpdate_interval_bounds q c I.property.2
  have hn := hc.interval_image_normalized I.property.1 I.property.2 hb hm hM
  exact ⟨⟨c, ⟨(m, M), hn.1, hn.2.1⟩, hc, hb, hm, hM⟩⟩

/-- Actual arbitrary-length greedy minimax sequences exist from every positive
initial interval `[ell,1]`, including the singleton endpoint `ell=1`.
Every recorded interval endpoint is attained by the corresponding actual
coefficient-defined polynomial; no rate certificate is assumed.
[AmselPerssonMuscoGower2026, §3], using finite-dimensional minimax existence. -/
theorem exists_isGreedyOddMinimax (q : ℕ) {ell : ℝ} (hell : 0 < ell) (hell1 : ell ≤ 1) :
    ∃ (c : ℕ → ℕ → ℝ) (l u : ℕ → ℝ), IsGreedyOddMinimax q ell c l u := by
  classical
  let chooseStep : (I : PositiveInterval) → GreedyOddStep q I :=
    fun I => Classical.choice (nonempty_greedyOddStep q I)
  let initial : PositiveInterval := ⟨(ell, 1), hell, hell1⟩
  let intervals : ℕ → PositiveInterval :=
    Nat.rec initial (fun _ I => (chooseStep I).next)
  let c : ℕ → ℕ → ℝ := fun k => (chooseStep (intervals k)).coefficients
  let l : ℕ → ℝ := fun k => (intervals k).val.1
  let u : ℕ → ℝ := fun k => (intervals k).val.2
  refine ⟨c, l, u, ?_⟩
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (chooseStep (intervals k)).minimax
  · intro k x hx
    exact (chooseStep (intervals k)).bounds x hx
  · intro k
    exact (chooseStep (intervals k)).attain_lower
  · intro k
    exact (chooseStep (intervals k)).attain_upper


/-- Finite inverse-square-root Taylor coefficients, given by their recurrence. -/
private noncomputable def polarTaylorCoeff : ℕ → ℝ
  | 0 => 1
  | j + 1 => ((2 * j + 1 : ℕ) : ℝ) / (2 * j + 2 : ℕ) * polarTaylorCoeff j

/-- Every finite inverse-square-root coefficient is strictly positive. -/
private theorem polarTaylorCoeff_pos (j : ℕ) : 0 < polarTaylorCoeff j := by
  induction j with
  | zero => norm_num [polarTaylorCoeff]
  | succ j ih =>
    simp only [polarTaylorCoeff]
    exact mul_pos (div_pos (by positivity) (by positivity)) ih

/-- The coefficient recurrence without division. -/
private theorem polarTaylorCoeff_recurrence (j : ℕ) :
    (2 * (j : ℝ) + 2) * polarTaylorCoeff (j + 1) =
      (2 * (j : ℝ) + 1) * polarTaylorCoeff j := by
  simp only [polarTaylorCoeff, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  field_simp

/-- The finite Taylor polynomial in its nonnegative argument. -/
private noncomputable def polarTaylorSum (q : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ range (q + 1), polarTaylorCoeff j * u ^ j

/-- The actual odd polynomial competitor `x C_q(1-x²)`. -/
private noncomputable def polarTaylorUpdate (q : ℕ) (x : ℝ) : ℝ := x * polarTaylorSum q (1 - x ^ 2)

/-- Endpoint values of the finite competitor. -/
@[simp] private theorem polarTaylorUpdate_zero (q : ℕ) : polarTaylorUpdate q 0 = 0 := by
  simp [polarTaylorUpdate]

@[simp] private theorem polarTaylorUpdate_one (q : ℕ) : polarTaylorUpdate q 1 = 1 := by
  simp only [polarTaylorUpdate, polarTaylorSum, one_pow, sub_self, one_mul]
  rw [Finset.sum_eq_single 0]
  · simp [polarTaylorCoeff]
  · intro j hj hj0
    rw [zero_pow hj0, mul_zero]
  · simp

/-- Adding the last retained term. -/
private theorem polarTaylorUpdate_succ (q : ℕ) (x : ℝ) :
    polarTaylorUpdate (q + 1) x = polarTaylorUpdate q x +
      polarTaylorCoeff (q + 1) * x * (1 - x ^ 2) ^ (q + 1) := by
  simp only [polarTaylorUpdate, polarTaylorSum, Finset.sum_range_succ]
  ring

/-- The derivative telescopes to one nonnegative monomial on `[0,1]`. -/
private theorem hasDerivAt_polarTaylorUpdate (q : ℕ) (x : ℝ) :
    HasDerivAt (polarTaylorUpdate q)
      ((2 * (q : ℝ) + 1) * polarTaylorCoeff q * (1 - x ^ 2) ^ q) x := by
  induction q with
  | zero =>
    have hf : polarTaylorUpdate 0 = id := by
      funext y
      simp [polarTaylorUpdate, polarTaylorSum, polarTaylorCoeff]
    rw [hf]
    simpa [polarTaylorCoeff] using! hasDerivAt_id x
  | succ q ih =>
    have hu : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
      simpa using! (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)
    have ht := (((hasDerivAt_id x).mul (hu.pow (q + 1))).const_mul (polarTaylorCoeff (q + 1)))
    have hh := ih.add ht
    simp only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.add_sub_cancel,
      one_mul] at hh
    have hf : polarTaylorUpdate q + (fun y => polarTaylorCoeff (q + 1) *
        (y * (1 - y ^ 2) ^ (q + 1))) = polarTaylorUpdate (q + 1) := by
      funext y
      change polarTaylorUpdate q y + polarTaylorCoeff (q + 1) *
        (y * (1 - y ^ 2) ^ (q + 1)) = polarTaylorUpdate (q + 1) y
      rw [polarTaylorUpdate_succ]
      ring
    rw [hf] at hh
    convert! hh using 1
    rw [pow_succ]
    push_cast
    have hc := polarTaylorCoeff_recurrence q
    linear_combination (1 - x ^ 2) ^ q * hc

/-- Continuity of the finite competitor follows from its checked derivative. -/
private theorem continuous_polarTaylorUpdate (q : ℕ) : Continuous (polarTaylorUpdate q) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_polarTaylorUpdate q x).continuousAt

/-- The finite Taylor sum is monotone for nonnegative arguments. -/
private theorem polarTaylorSum_monotoneOn (q : ℕ) : MonotoneOn (polarTaylorSum q) (Ici 0) := by
  intro u hu v hv huv
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv j) (polarTaylorCoeff_pos j).le

/-- The Taylor competitor is positive and at most one on the positive
unit interval. -/
private theorem polarTaylorUpdate_pos_le_one (q : ℕ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    0 < polarTaylorUpdate q x ∧ polarTaylorUpdate q x ≤ 1 := by
  have hu : 0 ≤ 1 - x ^ 2 := by nlinarith
  have hs : 1 ≤ polarTaylorSum q (1 - x ^ 2) := by
    calc
      1 = polarTaylorCoeff 0 * (1 - x ^ 2) ^ 0 := by simp [polarTaylorCoeff]
      _ ≤ polarTaylorSum q (1 - x ^ 2) :=
        Finset.single_le_sum (fun j hj => mul_nonneg (polarTaylorCoeff_pos j).le (pow_nonneg hu j))
          (by simp)
  have hmono : MonotoneOn (polarTaylorUpdate q) (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (continuous_polarTaylorUpdate q).continuousOn
    · intro y hy; exact (hasDerivAt_polarTaylorUpdate q y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hasDerivAt_polarTaylorUpdate q y).deriv]
      have hyI : y ∈ Icc (0 : ℝ) 1 := interior_subset hy
      have hnon : 0 ≤ 1 - y ^ 2 := by nlinarith [hyI.1, hyI.2]
      exact mul_nonneg (mul_nonneg (by positivity) (polarTaylorCoeff_pos q).le) (pow_nonneg hnon q)
  refine ⟨mul_pos hx (lt_of_lt_of_le zero_lt_one hs), ?_⟩
  simpa only [polarTaylorUpdate_one] using hmono ⟨hx.le, hx1⟩ (by simp) hx1

/-- The squared finite Taylor competitor loses at most the `(q+1)`st
power of the input squared gap. This is the scalar contraction needed
for the sharp polar minimax iteration rate. -/
private theorem one_sub_pow_le_polarTaylorUpdate_sq (q : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    1 - (1 - x ^ 2) ^ (q + 1) ≤ polarTaylorUpdate q x ^ 2 := by
  let K := (2 * (q : ℝ) + 1) * polarTaylorCoeff q
  let B := fun y : ℝ => K * polarTaylorSum q (1 - y ^ 2) - (q + 1)
  let F := fun y : ℝ => polarTaylorUpdate q y ^ 2 - 1 + (1 - y ^ 2) ^ (q + 1)
  have hK : 0 ≤ K := mul_nonneg (by positivity) (polarTaylorCoeff_pos q).le
  have hB : AntitoneOn B (Icc 0 1) := by
    intro u hu v hv huv
    have hu' : 0 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
    have hv' : 0 ≤ 1 - v ^ 2 := by nlinarith [hv.1, hv.2]
    have he : 1 - v ^ 2 ≤ 1 - u ^ 2 := by nlinarith [hu.1, hv.1]
    dsimp only [B]
    exact sub_le_sub_right (mul_le_mul_of_nonneg_left
      (polarTaylorSum_monotoneOn q hv' hu' he) hK) _
  have hF (y : ℝ) : HasDerivAt F (2 * y * (1 - y ^ 2) ^ q * B y) y := by
    have hu : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * y)) y := by
      simpa using! (hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_id y).pow 2)
    have hh := (((hasDerivAt_polarTaylorUpdate q y).pow 2).sub_const 1).add (hu.pow (q + 1))
    simp only [Pi.pow_apply, Nat.add_sub_cancel] at hh
    convert! hh using 1
    dsimp only [B, K, polarTaylorUpdate]
    rw [pow_succ]
    push_cast
    ring
  have hFcont : Continuous F := continuous_iff_continuousAt.mpr fun y => (hF y).continuousAt
  have hFzero : F 0 = 0 := by simp [F]
  have hFone : F 1 = 0 := by simp [F]
  have hnon : 0 ≤ F x := by
    by_cases hBx : 0 ≤ B x
    · have hm : MonotoneOn F (Icc 0 x) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hFcont.continuousOn
        · intro y hy; exact (hF y).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [(hF y).deriv]
          have hyI : y ∈ Icc (0 : ℝ) x := interior_subset hy
          have hy1 : y ∈ Icc (0 : ℝ) 1 := ⟨hyI.1, hyI.2.trans hx.2⟩
          have hby : 0 ≤ B y := hBx.trans (hB hy1 hx hyI.2)
          have hu : 0 ≤ 1 - y ^ 2 := by nlinarith [hy1.1, hy1.2]
          exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hyI.1) (pow_nonneg hu q)) hby
      have hh := hm ⟨le_rfl, hx.1⟩ ⟨hx.1, le_rfl⟩ hx.1
      rwa [hFzero] at hh
    · have hm : AntitoneOn F (Icc x 1) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc x 1) hFcont.continuousOn
        · intro y hy; exact (hF y).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [(hF y).deriv]
          have hyI : y ∈ Icc x (1 : ℝ) := interior_subset hy
          have hy0 : y ∈ Icc (0 : ℝ) 1 := ⟨hx.1.trans hyI.1, hyI.2⟩
          have hby : B y ≤ 0 := (hB hx hy0 hyI.1).trans (le_of_not_ge hBx)
          have hu : 0 ≤ 1 - y ^ 2 := by nlinarith [hy0.1, hy0.2]
          exact mul_nonpos_of_nonneg_of_nonpos
            (mul_nonneg (mul_nonneg (by norm_num) hy0.1) (pow_nonneg hu q)) hby
      have hh := hm ⟨le_rfl, hx.2⟩ ⟨hx.2, le_rfl⟩ hx.2
      rwa [hFone] at hh
  dsimp only [F] at hnon
  linarith

/-- The finite Taylor competitor as a degree-`q` polynomial in the squared input. -/
private noncomputable def polarTaylorCoefficientPolynomial (q : ℕ) : ℝ[X] :=
  ∑ j ∈ range (q + 1), C (polarTaylorCoeff j) * (1 - X) ^ j

/-- Its degree bound is finite and applies also to `q=0`. -/
private theorem natDegree_polarTaylorCoefficientPolynomial_le (q : ℕ) :
    (polarTaylorCoefficientPolynomial q).natDegree ≤ q := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjq : j ≤ q := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply Polynomial.natDegree_pow_le.trans
  have hd : (1 - X : ℝ[X]).natDegree ≤ 1 := by
    simpa using (Polynomial.natDegree_sub_le (1 : ℝ[X]) X)
  exact (Nat.mul_le_mul_left j hd).trans (by simpa using hjq)

/-- The ordinary coefficients realize the Taylor competitor in exactly the
same coefficient model used by the minimax problem and the matrix algorithm. -/
private theorem oddScalarUpdate_polarTaylor_coeff (q : ℕ) (x : ℝ) :
    oddScalarUpdate q (polarTaylorCoefficientPolynomial q).coeff x = polarTaylorUpdate q x := by
  rw [oddScalarUpdate_coeff _ (natDegree_polarTaylorCoefficientPolynomial_le q)]
  simp [polarTaylorUpdate, polarTaylorCoefficientPolynomial, polarTaylorSum,
    Polynomial.eval_finsetSum]

/-- The finite Taylor competitor is an actual member of the allowed odd
polynomial coefficient class. -/
private theorem exists_oddScalarUpdate_eq_polarTaylorUpdate (q : ℕ) :
    ∃ c : ℕ → ℝ, ∀ x, oddScalarUpdate q c x = polarTaylorUpdate q x :=
  ⟨(polarTaylorCoefficientPolynomial q).coeff, oddScalarUpdate_polarTaylor_coeff q⟩

/-- A genuine admissible odd coefficient competitor with the exact squared-gap
lower envelope on an arbitrary positive interval.
[AmselPerssonMuscoGower2026, Appendix D], using a finite Taylor competitor. -/
private theorem exists_oddScalarUpdate_interval_competitor (q : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ c : ℕ → ℝ, ∀ x ∈ Icc a b,
      Real.sqrt (1 - (1 - (a / b) ^ 2) ^ (q + 1)) ≤ oddScalarUpdate q c x ∧
        oddScalarUpdate q c x ≤ 1 := by
  have hb : 0 < b := ha.trans_le hab
  let d := (polarTaylorCoefficientPolynomial q).coeff
  refine ⟨fun j => d j / b ^ (2 * j + 1), fun x hx => ?_⟩
  have hx0 : 0 < x / b := div_pos (ha.trans_le hx.1) hb
  have hx1 : x / b ≤ 1 := (div_le_one hb).mpr hx.2
  have hp := polarTaylorUpdate_pos_le_one q hx0 hx1
  have ha0 : 0 ≤ a / b := (div_pos ha hb).le
  have halx : a / b ≤ x / b := (div_le_div_iff_of_pos_right hb).mpr hx.1
  have hg : 0 ≤ 1 - (x / b) ^ 2 := by nlinarith
  have hgap : 1 - (x / b) ^ 2 ≤ 1 - (a / b) ^ 2 := by nlinarith
  have hsq := one_sub_pow_le_polarTaylorUpdate_sq q ⟨hx0.le, hx1⟩
  have hpow := pow_le_pow_left₀ hg hgap (q + 1)
  have hlower : 1 - (1 - (a / b) ^ 2) ^ (q + 1) ≤ polarTaylorUpdate q (x / b) ^ 2 := by
    linarith
  have hsqrt : Real.sqrt (1 - (1 - (a / b) ^ 2) ^ (q + 1)) ≤
      polarTaylorUpdate q (x / b) := (Real.sqrt_le_left hp.1.le).mpr hlower
  have he : oddScalarUpdate q (fun j => d j / b ^ (2 * j + 1)) x =
      polarTaylorUpdate q (x / b) := by
    simpa only [one_mul, oddScalarUpdate_polarTaylor_coeff, d] using
      oddScalarUpdate_rescale q d 1 b x
  rw [he]
  exact ⟨hsqrt, hp.2⟩

/-- Positive interval squared-ratio gaps lie in `[0,1)`. -/
private theorem interval_squared_ratio_gap_mem {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 - (a / b) ^ 2 ∈ Ico (0 : ℝ) 1 := by
  have hb : 0 < b := ha.trans_le hab
  have hr : 0 < a / b := div_pos ha hb
  have hr1 : a / b ≤ 1 := (div_le_one hb).mpr hab
  constructor <;> nlinarith

/-- Genuine odd minimax optimality implies the squared-ratio contraction
and a matching bound on the actual uniform error. No recurrence estimate
is assumed in the hypotheses. -/
private theorem IsOddMinimaxOn.squared_ratio_contraction {q : ℕ} {c : ℕ → ℝ} {a b m M : ℝ}
    (h : IsOddMinimaxOn q c a b) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x ∈ Icc a b, m ≤ oddScalarUpdate q c x ∧ oddScalarUpdate q c x ≤ M)
    (hm : ∃ x ∈ Icc a b, oddScalarUpdate q c x = m)
    (hM : ∃ x ∈ Icc a b, oddScalarUpdate q c x = M) :
    1 - (m / M) ^ 2 ≤ (1 - (a / b) ^ 2) ^ (q + 1) ∧
      oddUniformError q c a b ≤ (1 - (a / b) ^ 2) ^ (q + 1) := by
  let D := (1 - (a / b) ^ 2) ^ (q + 1)
  let r := Real.sqrt (1 - D)
  have hd := interval_squared_ratio_gap_mem ha hab
  have hD0 : 0 ≤ D := pow_nonneg hd.1 _
  have hD1 : D < 1 := pow_lt_one₀ hd.1 hd.2 (by omega)
  have hr : 0 < r := Real.sqrt_pos.mpr (by dsimp only [D]; exact sub_pos.mpr hD1)
  have hrsq : r ^ 2 = 1 - D := Real.sq_sqrt (sub_nonneg.mpr hD1.le)
  have hr1 : r ≤ 1 := by nlinarith [hD0]
  obtain ⟨d, hd⟩ := exists_oddScalarUpdate_interval_competitor q ha hab
  have hscaled : oddUniformError q (fun j => (2 / (r + 1)) * d j) a b ≤ (1 - r) / (r + 1) := by
    apply oddUniformError_le_of_forall (div_nonneg (sub_nonneg.mpr hr1) (by positivity))
    intro x hx
    rw [oddScalarUpdate_smul_coeff]
    exact abs_one_sub_two_div_mul_le hr hr1 (hd x hx)
  have hE : oddUniformError q c a b ≤ (1 - r) / (r + 1) := (h _).trans hscaled
  have hE0 := oddUniformError_nonneg q c a b
  have hEmul : oddUniformError q c a b * (r + 1) ≤ 1 - r :=
    (le_div_iff₀ (by positivity : 0 < r + 1)).mp hE
  obtain ⟨hm0, hmM, hcenter, hEnorm⟩ := h.interval_image_normalized ha hab hbounds hm hM
  have hM0 : 0 < M := hm0.trans_le hmM
  have hrmul : r * M ≤ m := by rw [hEnorm] at hEmul; nlinarith
  have hratio : r ≤ m / M := (le_div_iff₀ hM0).mpr hrmul
  have hsquare : r ^ 2 ≤ (m / M) ^ 2 := pow_le_pow_left₀ hr.le hratio 2
  constructor
  · change 1 - (m / M) ^ 2 ≤ D
    nlinarith
  · change oddUniformError q c a b ≤ D
    have hEr : oddUniformError q c a b ≤ 1 - r := by
      nlinarith [mul_nonneg hE0 hr.le]
    nlinarith

/-- The true squared-ratio gaps of every genuine greedy minimax sequence
obey the iterated power estimate. -/
private theorem IsGreedyOddMinimax.squared_ratio_gap_le {q : ℕ} {ell : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q ell c l u)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (k : ℕ) :
    1 - (l k / u k) ^ 2 ≤ (1 - ell ^ 2) ^ ((q + 1) ^ k) := by
  induction k with
  | zero => simp [h.lower_zero, h.upper_zero]
  | succ k ih =>
    have hi := h.positive_intervals hell hell1 k
    have hgap := (interval_squared_ratio_gap_mem hi.1 hi.2).1
    have hc := ((h.minimax k).squared_ratio_contraction hi.1 hi.2
      (h.bounds k) (h.attain_lower k) (h.attain_upper k)).1
    calc
      _ ≤ (1 - (l k / u k) ^ 2) ^ (q + 1) := hc
      _ ≤ ((1 - ell ^ 2) ^ ((q + 1) ^ k)) ^ (q + 1) := pow_le_pow_left₀ hgap ih _
      _ = (1 - ell ^ 2) ^ ((q + 1) ^ (k + 1)) := by rw [← pow_mul, Nat.pow_succ]

/-- The actual per-step uniform error has the final iterated power rate. -/
private theorem IsGreedyOddMinimax.uniform_error_le {q : ℕ} {ell : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q ell c l u)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (k : ℕ) :
    oddUniformError q (c k) (l k) (u k) ≤ (1 - ell ^ 2) ^ ((q + 1) ^ (k + 1)) := by
  have hi := h.positive_intervals hell hell1 k
  have hgap := (interval_squared_ratio_gap_mem hi.1 hi.2).1
  calc
    _ ≤ (1 - (l k / u k) ^ 2) ^ (q + 1) :=
      ((h.minimax k).squared_ratio_contraction hi.1 hi.2
        (h.bounds k) (h.attain_lower k) (h.attain_upper k)).2
    _ ≤ ((1 - ell ^ 2) ^ ((q + 1) ^ k)) ^ (q + 1) :=
      pow_le_pow_left₀ hgap (h.squared_ratio_gap_le hell hell1 k) _
    _ = (1 - ell ^ 2) ^ ((q + 1) ^ (k + 1)) := by rw [← pow_mul, Nat.pow_succ]

/-- On the initial interval the scalar polar error is bounded by the distance from the
current lower endpoint to one. -/
theorem IsGreedyOddMinimax.abs_one_sub_oddScalarComposition_le {q : ℕ} {a : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q a c l u)
    (ha : 0 < a) (ha1 : a ≤ 1) {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ Icc a 1) :
    |1 - oddScalarComposition q c x k| ≤ 1 - l k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simpa only [oddScalarComposition, (h.normalized_images ha ha1 k).2] using
    abs_one_sub_oddScalarUpdate_le q (c k) (l k) (u k) (oddScalarComposition q c x k)
      (h.oddScalarComposition_mem_Icc hx k)

/-- The distance of the lower endpoint to one has the iterated minimax rate. -/
theorem IsGreedyOddMinimax.one_sub_le_pow {q : ℕ} {a : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q a c l u)
    (ha : 0 < a) (ha1 : a ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    1 - l k ≤ (1 - a ^ 2) ^ ((q + 1) ^ k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simpa only [(h.normalized_images ha ha1 k).2] using h.uniform_error_le ha ha1 k

end NLAlib
