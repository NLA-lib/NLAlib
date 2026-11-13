/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# Analytic sums of polynomial root clusters

Contour integrals give local analytic branches of sums of roots enclosed by a fixed circle.
Upstream candidate for Mathlib.

The proofs adapt the original NLAlib atlas at commit `77514ce`.

## Main results

* `Polynomial.analyticAt_sum_filter_roots_upper_of_upperHemicontinuous`.
-/
@[expose] public section

section

attribute [local instance] Classical.propDecidable

open Complex Metric Set Filter

open scoped Topology

namespace circleIntegral
private noncomputable def extendFromSphere {c : ℂ} {r : ℝ} (f : C(sphere c r, ℂ)) (z : ℂ) : ℂ :=
  if hz : z ∈ sphere c r then f ⟨z, hz⟩ else 0

private theorem continuousOn_extendFromSphere {c : ℂ} {r : ℝ}
    (f : C(sphere c r, ℂ)) : ContinuousOn (extendFromSphere f) (sphere c r) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert f.continuous using 1
  ext z
  change extendFromSphere f z = f z
  simp only [extendFromSphere, dif_pos z.property]

/-- Integration along a fixed counterclockwise circle is a continuous complex-linear
functional on its continuous functions. -/
private noncomputable def continuousMapIntegral (c : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    C(sphere c r, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∮ z in C(c, r), extendFromSphere f z
      map_add' := by
        intro f g
        have heq : extendFromSphere (f + g) =
            fun z => extendFromSphere f z + extendFromSphere g z := by
          ext z
          by_cases hz : z ∈ sphere c r
          · simp only [extendFromSphere, dif_pos hz, ContinuousMap.add_apply]
          · simp only [extendFromSphere, dif_neg hz, add_zero]
        rw [heq]
        exact integral_add ((continuousOn_extendFromSphere f).circleIntegrable hr)
          ((continuousOn_extendFromSphere g).circleIntegrable hr)
      map_smul' := by
        intro a f
        have heq : extendFromSphere (a • f) = fun z => a • extendFromSphere f z := by
          ext z
          by_cases hz : z ∈ sphere c r
          · simp only [extendFromSphere, dif_pos hz, ContinuousMap.smul_apply]
          · simp only [extendFromSphere, dif_neg hz, smul_zero]
        rw [heq]
        exact integral_smul a (extendFromSphere f) c r }
    (2 * Real.pi * r) fun f =>
      norm_integral_le_of_norm_le_const hr fun z hz => by
        simpa only [extendFromSphere, dif_pos hz] using f.norm_coe_le_norm ⟨z, hz⟩

/-- The continuous linear circle integral agrees with the ordinary circle integral
of any function whose restriction supplies the bundled continuous map. -/
private theorem continuousMapIntegral_eq {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (f : C(sphere c r, ℂ)) (g : ℂ → ℂ)
    (hg : ∀ z (hz : z ∈ sphere c r), f ⟨z, hz⟩ = g z) :
    continuousMapIntegral c r hr f = ∮ z in C(c, r), g z := by
  apply integral_congr hr
  intro z hz
  simpa only [extendFromSphere, dif_pos hz] using hg z hz

private theorem inverse_apply {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) (hf : IsUnit f) (x : X) :
    (Ring.inverse f) x = (f x)⁻¹ := by
  have hmul := congrArg (fun g : C(X, ℂ) => g x) (Ring.mul_inverse_cancel f hf)
  exact eq_inv_of_mul_eq_one_right hmul

/-- A contour quotient depends analytically on the parameter whenever its two
continuous-function-valued factors do and the denominator has no zero on the fixed
circle. The proof constructs a common nonvanishing neighborhood using openness of units. -/
theorem analyticAt_integral_div {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    {F G : ℂ → C(sphere c r, ℂ)} {u : ℂ}
    (hF : AnalyticAt ℂ F u) (hG : AnalyticAt ℂ G u)
    (hzero : ∀ z, F u z ≠ 0) :
    AnalyticAt ℂ (fun v => ∮ z in C(c, r),
      if hz : z ∈ sphere c r then G v ⟨z, hz⟩ / F v ⟨z, hz⟩ else 0) u := by
  have hunit : IsUnit (F u) := (F u).isUnit_iff_forall_ne_zero.mpr hzero
  have hinv : AnalyticAt ℂ (fun v => Ring.inverse (F v)) u := by
    have hi := analyticAt_inverse (𝕜 := ℂ) hunit.unit
    rw [hunit.unit_spec] at hi
    exact hi.comp hF
  have ha : AnalyticAt ℂ
      (fun v => continuousMapIntegral c r hr (G v * Ring.inverse (F v))) u :=
    ((continuousMapIntegral c r hr).analyticAt
      (G u * Ring.inverse (F u))).comp
        (f := fun v => G v * Ring.inverse (F v)) (hG.mul hinv)
  apply ha.congr
  have hevent : ∀ᶠ v in 𝓝 u, IsUnit (F v) :=
    hF.continuousAt.eventually (Units.isOpen.mem_nhds hunit)
  filter_upwards [hevent] with v hv
  apply continuousMapIntegral_eq hr
  intro z hz
  simp only [dif_pos hz, ContinuousMap.mul_apply, inverse_apply (F v) hv, div_eq_mul_inv]

end circleIntegral

end

section

open Complex Set Metric Filter

open scoped Topology

namespace Complex

/-- A circle tangent to the real axis lies entirely in the open upper
half-plane. The squared-norm criterion also gives an explicit enclosure test. -/
private theorem dist_mul_I_lt_iff {z : ℂ} {r : ℝ} (hr : 0 < r) :
    dist z ((r : ℂ) * I) < r ↔ ‖z‖ ^ 2 < 2 * r * z.im := by
  have heq : dist z ((r : ℂ) * I) ^ 2 = ‖z‖ ^ 2 + r ^ 2 - 2 * r * z.im := by
    simp only [dist_eq_norm, Complex.sq_norm, normSq_apply, sub_re, sub_im,
      mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
    ring
  constructor
  · intro h
    nlinarith [sq_nonneg (‖z‖), dist_nonneg (x := z) (y := (r : ℂ) * I)]
  · intro h
    nlinarith [dist_nonneg (x := z) (y := (r : ℂ) * I)]

/-- Every point of a circle tangent from above has positive imaginary part. -/
private theorem im_pos_of_dist_mul_I_lt {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : dist z ((r : ℂ) * I) < r) : 0 < z.im := by
  have h := (dist_mul_I_lt_iff hr).mp hz
  nlinarith [sq_nonneg ‖z‖]

/-- One tangent circle selects exactly the upper-half-plane points of any
finite set. The real-axis points, if present, lie outside the open circle. -/
private theorem exists_pos_dist_mul_I_lt_iff_im_pos (s : Finset ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ s, dist z ((r : ℂ) * I) < r ↔ 0 < z.im := by
  let f : ℂ → ℝ := fun z => ‖z‖ ^ 2 / (2 * |z.im|)
  let r := 1 + ∑ z ∈ s, f z
  have hf (z : ℂ) : 0 ≤ f z := div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))
  have hsum : 0 ≤ ∑ z ∈ s, f z := Finset.sum_nonneg (fun z _ => hf z)
  have hr : 0 < r := by dsimp [r]; linarith
  refine ⟨r, hr, fun z hz => ⟨im_pos_of_dist_mul_I_lt hr, fun hzim => ?_⟩⟩
  apply (dist_mul_I_lt_iff hr).mpr
  have hterm : f z ≤ ∑ z ∈ s, f z := Finset.single_le_sum (fun z _ => hf z) hz
  have hquot : ‖z‖ ^ 2 / (2 * z.im) < r := by
    have heq : f z = ‖z‖ ^ 2 / (2 * z.im) := by dsimp [f]; rw [abs_of_pos hzim]
    rw [heq] at hterm
    dsimp [r]
    linarith
  have h := (div_lt_iff₀ (by positivity : 0 < 2 * z.im)).mp hquot
  nlinarith

/-- An upper hemicontinuous finite cluster avoiding the real axis has one
locally valid circle selecting precisely its upper points. The same circle
also avoids every nearby cluster point, including repeated spectral roots. -/
private theorem exists_tangent_circle_eventually_mem_iff_im_pos
    {α : Type*} [TopologicalSpace α] {F : α → Set ℂ} {a : α}
    (hF : UpperHemicontinuousAt F a) (hfin : (F a).Finite)
    (hreal : ∀ z ∈ F a, z.im ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ x in 𝓝 a, ∀ z ∈ F x,
      (dist z ((r : ℂ) * I) < r ↔ 0 < z.im) ∧ dist z ((r : ℂ) * I) ≠ r := by
  classical
  obtain ⟨r, hr, hsel⟩ := exists_pos_dist_mul_I_lt_iff_im_pos hfin.toFinset
  let U : Set ℂ := ball ((r : ℂ) * I) r ∪ {z : ℂ | z.im < 0}
  have hopen : IsOpen U := isOpen_ball.union (isOpen_lt continuous_im continuous_const)
  have hcover : F a ⊆ U := by
    intro z hz
    by_cases hpos : 0 < z.im
    · exact Or.inl ((hsel z (hfin.mem_toFinset.mpr hz)).mpr hpos)
    · exact Or.inr (lt_of_le_of_ne (le_of_not_gt hpos) (hreal z hz))
  have hnear : ∀ᶠ x in 𝓝 a, F x ⊆ U := by
    filter_upwards [hF U (hopen.mem_nhdsSet.mpr hcover)] with x hx
    exact subset_of_mem_nhdsSet hx
  refine ⟨r, hr, ?_⟩
  filter_upwards [hnear] with x hx z hz
  have hzU := hx hz
  refine ⟨⟨im_pos_of_dist_mul_I_lt hr, ?_⟩, ?_⟩
  · intro hpos
    rcases hzU with hball | hneg
    · exact hball
    · exact False.elim (not_lt_of_ge hpos.le hneg)
  · intro heq
    rcases hzU with hball | hneg
    · exact ne_of_lt hball heq
    · have him : |z.im - r| ≤ dist z ((r : ℂ) * I) := by
        simpa [dist_eq_norm] using abs_im_le_norm (z - (r : ℂ) * I)
      have habs' := neg_le_abs (z.im - r)
      rw [heq] at him
      change z.im < 0 at hneg
      linarith

end Complex

end

section

attribute [local instance] Classical.propDecidable

open Complex Metric Set

open scoped Interval Topology Polynomial

namespace Polynomial

private theorem sub_ne_zero_on_circle {c w : ℂ} {r : ℝ}
    (hw : dist w c ≠ r) {z : ℂ} (hz : z ∈ sphere c r) : z - w ≠ 0 := by
  intro h
  have hzw : z = w := sub_eq_zero.mp h
  exact hw (hzw ▸ mem_sphere.mp hz)

private theorem circleIntegral_div_sub (c w : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hw : dist w c ≠ r) :
    (∮ z in C(c, r), z / (z - w)) =
      if dist w c < r then (2 * Real.pi * I) * w else 0 := by
  by_cases hinside : dist w c < r
  · rw [if_pos hinside]
    simpa only [div_eq_mul_inv, smul_eq_mul, mul_comm, id_eq] using
      (differentiableOn_id : DifferentiableOn ℂ (fun z : ℂ => z)
        (closedBall c r)).circleIntegral_sub_inv_smul (mem_ball.mpr hinside)
  · rw [if_neg hinside]
    have houtside : r < dist w c := lt_of_le_of_ne (le_of_not_gt hinside) hw.symm
    have hd : DifferentiableOn ℂ (fun z : ℂ => z / (z - w)) (closedBall c r) := by
      intro z hz
      apply DifferentiableAt.differentiableWithinAt
      apply differentiableAt_id.div (differentiableAt_id.sub_const w)
      intro h
      have : z = w := sub_eq_zero.mp h
      subst z
      exact (not_le_of_gt houtside) (mem_closedBall.mp hz)
    exact (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hr

private theorem circleIntegrable_div_sub (c w : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hw : dist w c ≠ r) : CircleIntegrable (fun z : ℂ => z / (z - w)) c r := by
  exact (continuousOn_id.div (continuousOn_id.sub continuousOn_const)
    (fun _ hz => sub_ne_zero_on_circle hw hz)).circleIntegrable hr

private theorem circleIntegrable_multiset_div_sub (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (m : Multiset ℂ) (h : ∀ w ∈ m, dist w c ≠ r) :
    CircleIntegrable (fun z : ℂ => (m.map (fun w => z / (z - w))).sum) c r := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons w m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (circleIntegrable_div_sub c w hr (h w (by simp))).add
      (ih (fun v hv => h v (Multiset.mem_cons_of_mem hv)))

private theorem circleIntegral_multiset_sum (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (m : Multiset ℂ) (h : ∀ w ∈ m, dist w c ≠ r) :
    (∮ z in C(c, r), (m.map (fun w => z / (z - w))).sum) =
      (m.map (fun w => if dist w c < r then (2 * Real.pi * I) * w else 0)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | @cons w m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have hm : ∀ v ∈ m, dist v c ≠ r := fun v hv => h v (Multiset.mem_cons_of_mem hv)
    rw [circleIntegral.integral_add (circleIntegrable_div_sub c w hr (h w (by simp))) ?_,
      circleIntegral_div_sub c w hr (h w (by simp)), ih hm]
    exact circleIntegrable_multiset_div_sub c hr m hm

/-- Integrating a polynomial's weighted logarithmic derivative around a root-free circle
gives the sum of its enclosed roots, retaining algebraic multiplicities. The polynomial
need not be squarefree; roots within the selected cluster may collide. -/
theorem circleIntegral_mul_derivative_div_eq_sum_roots (p : ℂ[X]) (c : ℂ) {r : ℝ}
    (hr : 0 ≤ r) (hp : ∀ z ∈ sphere c r, p.eval z ≠ 0) :
    (∮ z in C(c, r), z * (p.derivative.eval z / p.eval z)) =
      (p.roots.map
        (fun w => if dist w c < r then (2 * Real.pi * I) * w else 0)).sum := by
  rw [circleIntegral.integral_congr hr (fun z hz => ?_)]
  · exact circleIntegral_multiset_sum c hr p.roots (fun w hw => by
      intro heq
      exact hp w (mem_sphere.mpr heq) ((mem_roots (by
        intro hzero
        simp [hzero] at hw)).mp hw))
  · rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero (hp z hz),
      ← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro w _
    simp [div_eq_mul_inv]

/-- The normalized weighted logarithmic derivative gives the enclosed root sum,
with algebraic multiplicities. -/
private theorem two_pi_i_inv_mul_circleIntegral_mul_derivative_div_eq_sum_roots
    (p : ℂ[X]) (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hp : ∀ z ∈ sphere c r, p.eval z ≠ 0) :
    (2 * Real.pi * I : ℂ)⁻¹ *
        (∮ z in C(c, r), z * (p.derivative.eval z / p.eval z)) =
      (p.roots.map (fun w => if dist w c < r then w else 0)).sum := by
  rw [circleIntegral_mul_derivative_div_eq_sum_roots p c hr hp]
  have heq : (p.roots.map
      (fun w => if dist w c < r then (2 * Real.pi * I) * w else 0)).sum =
      (2 * Real.pi * I : ℂ) *
        (p.roots.map (fun w => if dist w c < r then w else 0)).sum := by
    rw [← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro w _
    split_ifs <;> simp
  rw [heq, ← mul_assoc, inv_mul_cancel₀, one_mul]
  simp [Real.pi_ne_zero]
private noncomputable def circleEval (c : ℂ) (r : ℝ) (p : ℂ[X]) : C(sphere c r, ℂ) :=
  ⟨fun z => p.eval z, p.continuous.comp continuous_subtype_val⟩

private theorem circleEval_sum_smul {ι : Type*} [Fintype ι]
    (c : ℂ) (r : ℝ) (a : ι → ℂ) (q : ι → ℂ[X]) :
    circleEval c r (∑ i, a i • q i) = ∑ i, a i • circleEval c r (q i) := by
  ext z
  simp [circleEval, eval_finsetSum]

/-- For a finite family of fixed polynomials with analytic scalar coefficients,
the sum of roots inside any root-free fixed circle depends analytically on the
parameter. No simplicity or distinctness of roots inside the circle is required.
This is the separated-cluster holomorphy step in the planar route to Stahl's theorem. -/
theorem analyticAt_sum_roots_in_circle {ι : Type*} [Fintype ι]
    (q : ι → ℂ[X]) (a : ι → ℂ → ℂ) {u c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (ha : ∀ i, AnalyticAt ℂ (a i) u)
    (hzero : ∀ z ∈ sphere c r, (∑ i, a i u • q i).eval z ≠ 0) :
    AnalyticAt ℂ (fun v => ((∑ i, a i v • q i).roots.map
      (fun w => if dist w c < r then w else 0)).sum) u := by
  let P : ℂ → ℂ[X] := fun v => ∑ i, a i v • q i
  let F : ℂ → C(sphere c r, ℂ) := fun v => circleEval c r (P v)
  let Z : C(sphere c r, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  let G : ℂ → C(sphere c r, ℂ) := fun v => Z * circleEval c r (P v).derivative
  have hF : AnalyticAt ℂ F u := by
    simp only [F, P, circleEval_sum_smul]
    exact Finset.univ.analyticAt_fun_sum fun i _ => (ha i).smul analyticAt_const
  have hG : AnalyticAt ℂ G u := by
    simp only [G, P, derivative_sum, derivative_smul, circleEval_sum_smul]
    exact analyticAt_const.mul
      (Finset.univ.analyticAt_fun_sum fun i _ => (ha i).smul analyticAt_const)
  have hz : ∀ z, F u z ≠ 0 := fun z => hzero z z.property
  have hA := (analyticAt_const (v := (2 * Real.pi * I : ℂ)⁻¹)).mul
    (circleIntegral.analyticAt_integral_div hr hF hG hz)
  apply hA.congr
  have hunit : IsUnit (F u) := (F u).isUnit_iff_forall_ne_zero.mpr hz
  have hevent : ∀ᶠ v in 𝓝 u, IsUnit (F v) :=
    hF.continuousAt.eventually (Units.isOpen.mem_nhds hunit)
  filter_upwards [hevent] with v hv
  have hnonzero : ∀ z ∈ sphere c r, (P v).eval z ≠ 0 :=
    fun z hz => ((F v).isUnit_iff_forall_ne_zero.mp hv) ⟨z, hz⟩
  have heq : (∮ z in C(c, r),
      if hz : z ∈ sphere c r then G v ⟨z, hz⟩ / F v ⟨z, hz⟩ else 0) =
      ∮ z in C(c, r), z * ((P v).derivative.eval z / (P v).eval z) := by
    apply circleIntegral.integral_congr hr
    intro z hz
    simp only [dif_pos hz, G, F, Z, circleEval, ContinuousMap.mul_apply,
      ContinuousMap.coe_mk]
    ring
  simp only [Pi.mul_apply]
  rw [heq]
  exact two_pi_i_inv_mul_circleIntegral_mul_derivative_div_eq_sum_roots (P v) c hr hnonzero

private theorem sum_map_ite_eq_sum_filter (m : Multiset ℂ) (p : ℂ → Prop)
    [DecidablePred p] : (m.map (fun z => if p z then z else 0)).sum = (m.filter p).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons z m ih =>
    by_cases hz : p z <;> simp [hz, ih]

/-- An upper hemicontinuous polynomial root family avoiding the real axis has an
analytic sum of upper-half-plane roots when its coefficients are analytic. Algebraic
multiplicities are retained, and collisions within either half-plane are allowed.
The root-continuity assumption is available for characteristic polynomials from
upper hemicontinuity of the spectrum in a Banach algebra. -/
theorem analyticAt_sum_filter_roots_upper_of_upperHemicontinuous
    {ι : Type*} [Fintype ι] (q : ι → ℂ[X]) (a : ι → ℂ → ℂ) {u : ℂ}
    (ha : ∀ i, AnalyticAt ℂ (a i) u) (hp : (∑ i, a i u • q i) ≠ 0)
    (hroots : UpperHemicontinuousAt
      (fun v => {z | z ∈ (∑ i, a i v • q i).roots}) u)
    (hreal : ∀ z ∈ (∑ i, a i u • q i).roots, z.im ≠ 0) :
    AnalyticAt ℂ (fun v => ((∑ i, a i v • q i).roots.filter
      (fun z => 0 < z.im)).sum) u := by
  obtain ⟨r, hr, hselect⟩ := Complex.exists_tangent_circle_eventually_mem_iff_im_pos
    hroots (Multiset.finite_toSet _) hreal
  have hbase := hselect.self_of_nhds
  have hzero : ∀ z ∈ sphere ((r : ℂ) * I) r,
      (∑ i, a i u • q i).eval z ≠ 0 := by
    intro z hz heval
    have hmem : z ∈ (∑ i, a i u • q i).roots := (mem_roots hp).mpr heval
    exact (hbase z hmem).2 (mem_sphere.mp hz)
  apply (analyticAt_sum_roots_in_circle q a hr.le ha hzero).congr
  filter_upwards [hselect] with v hv
  rw [← sum_map_ite_eq_sum_filter]
  congr 1
  apply Multiset.map_congr rfl
  intro z hz
  simp only [(hv z hz).1]

/-- The sum of the roots strictly in the upper half-plane has nonnegative
imaginary part, with algebraic multiplicities retained. -/
theorem im_sum_filter_roots_upper_nonneg (p : ℂ[X]) :
    0 ≤ ((p.roots.filter (fun z => 0 < z.im)).sum).im := by
  change 0 ≤ Complex.imAddGroupHom ((p.roots.filter (fun z => 0 < z.im)).sum)
  rw [map_multiset_sum]
  apply Multiset.sum_nonneg
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
  exact (Multiset.mem_filter.mp hz).2.le

end Polynomial

end
