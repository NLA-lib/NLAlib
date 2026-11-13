/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import NLAlib.ForMathlib.Topology.MetricSpace.PathSubdivision
public import NLAlib.ForMathlib.Algebra.BigOperators.Grid

/-!
# Transport of primitives along a homotopy

Equality of integrals along homotopic closed curves follows by transporting local primitives
across a finite subdivision [StewartTall2018, Chapter 9]. Upstream candidate for Mathlib.

The proofs adapt the original NLAlib atlas at commit `77514ce`.

## Main results

* `ContinuousMap.Homotopy.integral_eq_of_differentiableOn`: invariance for a continuous
  free homotopy of complex loops.
* `Complex.integral_eq_of_differentiableOn_of_freeHomotopy`: real-parameter form.
-/
@[expose] public section

section

open Set Finset MeasureTheory Metric

open scoped unitInterval

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Primitives $G$ and $H$ with common derivative $g$ have equal increments
$G(b)-G(a)=H(b)-H(a)$ along a path in the intersection of their open domains. The path requires
no differentiability. The domains' intersection need not be connected. -/
theorem sub_eq_sub_of_hasDerivAt_of_path {a b : ℂ} (γ : Path a b)
    {U V : Set ℂ} {G H g : ℂ → E} (hU : IsOpen U) (hV : IsOpen V)
    (hG : ∀ z ∈ U, HasDerivAt G (g z) z)
    (hH : ∀ z ∈ V, HasDerivAt H (g z) z)
    (hγU : ∀ t, γ t ∈ U) (hγV : ∀ t, γ t ∈ V) :
    G b - G a = H b - H a := by
  have hd (z : ℂ) (hz : z ∈ U ∩ V) : HasDerivAt (fun z => G z - H z) 0 z := by
    simpa only [sub_self] using (hG z hz.1).fun_sub (hH z hz.2)
  have hlocal : IsLocallyConstant (fun t : unitInterval => G (γ t) - H (γ t)) := by
    apply IsLocallyConstant.iff_isOpen_fiber.mpr
    intro w
    have ho := (hU.inter hV).isOpen_inter_preimage_of_deriv_eq_zero
      (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hd z hz).deriv) {w}
    have heq : (fun t : unitInterval => G (γ t) - H (γ t)) ⁻¹' {w} =
        γ ⁻¹' ((U ∩ V) ∩ (fun z => G z - H z) ⁻¹' {w}) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff]
      simp only [hγU t, hγV t, true_and]
    rw [heq]
    exact γ.continuous.isOpen_preimage _ ho
  have h := hlocal.apply_eq_of_preconnectedSpace 1 0
  simp only [γ.target, γ.source] at h
  exact sub_eq_sub_iff_sub_eq_sub.mp h

/-- Primitives with common derivative have equal increments from $\gamma(u)$ to $\gamma(v)$
for a continuous parametrization $\gamma$ on $[u,v]$, including $u=v$. -/
theorem sub_eq_sub_of_hasDerivAt_of_continuous
    {γ : ℝ → ℂ} (hγ : Continuous γ) {u v : ℝ} (huv : u ≤ v)
    {U V : Set ℂ} {G H g : ℂ → E} (hU : IsOpen U) (hV : IsOpen V)
    (hG : ∀ z ∈ U, HasDerivAt G (g z) z)
    (hH : ∀ z ∈ V, HasDerivAt H (g z) z)
    (hγU : ∀ t ∈ Icc u v, γ t ∈ U) (hγV : ∀ t ∈ Icc u v, γ t ∈ V) :
    G (γ v) - G (γ u) = H (γ v) - H (γ u) := by
  apply sub_eq_sub_of_hasDerivAt_of_path ((Path.segment u v).map hγ) hU hV hG hH
  · intro t
    apply hγU
    exact (convex_Icc u v).lineMap_mem ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ t.property
  · intro t
    apply hγV
    exact (convex_Icc u v).lineMap_mem ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ t.property

/-- On a subdivision $p_0,\ldots,p_n$, add the change in the local primitive $G_i$
between $\gamma(p_i)$ and $\gamma(p_{i+1})$. -/
private noncomputable def primitiveSubdivisionTransport (γ : ℝ → ℂ) (p : ℕ → ℝ)
    (G : ℕ → ℂ → E) (n : ℕ) : E :=
  ∑ i ∈ range n, (G i (γ (p (i + 1))) - G i (γ (p i)))

/-- If the $i$th subpath stays inside the domain of a primitive $G_i$ of $g$, the
sum of primitive increments equals $\int_\gamma g(z)\,dz$ along a $C^1$ path. -/
private theorem primitiveSubdivisionTransport_eq_curveIntegral_of_hasDerivAt [CompleteSpace E]
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend I)
    {p : ℕ → ℝ} {n : ℕ} {G : ℕ → ℂ → E} {U : ℕ → Set ℂ} {g : ℂ → E}
    (hp : ∀ i < n, p i ≤ p (i + 1)) (hp0 : p 0 = 0) (hpn : p n = 1)
    (hpI : ∀ i ≤ n, p i ∈ I)
    (hG : ∀ i < n, ∀ z ∈ U i, HasDerivAt (G i) (g z) z)
    (hg : ∀ i < n, ContinuousOn g (U i))
    (hγU : ∀ i < n, ∀ t ∈ Icc (p i) (p (i + 1)), γ.extend t ∈ U i) :
    primitiveSubdivisionTransport γ.extend p G n =
      curveIntegral (fun z => (ContinuousLinearMap.id ℂ ℂ).smulRight (g z)) γ := by
  let F := curveIntegralFun (fun z => (ContinuousLinearMap.id ℂ ℂ).smulRight (g z)) γ
  have hcell (i : ℕ) (hi : i < n) :
      IntervalIntegrable F volume (p i) (p (i + 1)) ∧
      (∫ t in (p i)..(p (i + 1)), F t) =
        G i (γ.extend (p (i + 1))) - G i (γ.extend (p i)) := by
    have hpi := hpI i hi.le
    have hpnext := hpI (i + 1) hi
    have hsubset : Icc (p i) (p (i + 1)) ⊆ I :=
      fun t ht => ⟨hpi.1.trans ht.1, ht.2.trans hpnext.2⟩
    have hc : ContinuousOn (fun t => g (γ.extend t)) (Icc (p i) (p (i + 1))) :=
      (hg i hi).comp γ.continuous_extend.continuousOn (hγU i hi)
    have hd : ContinuousOn (fun t => derivWithin γ.extend I t)
        (Icc (p i) (p (i + 1))) :=
      (hγ.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl).mono hsubset
    have hFeq : F = fun t => derivWithin γ.extend I t • g (γ.extend t) := by
      funext t
      simp only [F, curveIntegralFun_def, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply]
    have hF : ContinuousOn F (Icc (p i) (p (i + 1))) := by
      rw [hFeq]
      exact hd.fun_smul hc
    have hint : IntervalIntegrable F volume (p i) (p (i + 1)) :=
      hF.intervalIntegrable_of_Icc (hp i hi)
    refine ⟨hint, ?_⟩
    have hcontG : ContinuousOn (G i) (U i) :=
      fun z hz => (hG i hi z hz).continuousAt.continuousWithinAt
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (hp i hi)
      (hcontG.comp γ.continuous_extend.continuousOn (hγU i hi)) _ hint
    intro r hr
    have hrI : r ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_lt hpi.1 hr.1, lt_of_lt_of_le hr.2 hpnext.2⟩
    have hnhds : I ∈ nhds r := Icc_mem_nhds hrI.1 hrI.2
    have hderγ := (hγ.differentiableOn (by norm_num) r
      (Ioo_subset_Icc_self hrI)).differentiableAt hnhds
    have hDerG := hG i hi (γ.extend r) (hγU i hi r (Ioo_subset_Icc_self hr))
    have hdcomp := (hDerG.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt r hderγ.hasDerivAt
    simpa [F, curveIntegralFun_def, derivWithin_of_mem_nhds hnhds,
      ContinuousLinearMap.smulRight_apply] using hdcomp
  unfold primitiveSubdivisionTransport
  calc
    (∑ i ∈ range n, (G i (γ.extend (p (i + 1))) - G i (γ.extend (p i)))) =
        ∑ i ∈ range n, ∫ t in (p i)..(p (i + 1)), F t := by
      apply sum_congr rfl
      intro i hi
      exact (hcell i (mem_range.mp hi)).2.symm
    _ = ∫ t in (0 : ℝ)..1, F t := by
      simpa only [hp0, hpn] using
        intervalIntegral.sum_integral_adjacent_intervals (fun i hi => (hcell i hi).1)
    _ = curveIntegral (fun z => (ContinuousLinearMap.id ℂ ℂ).smulRight (g z)) γ :=
      (curveIntegral_def _ γ).symm

end Complex

end

section

open Set Finset Metric

open scoped unitInterval

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A square grid subordinate to the open primitive charts of $g$. Each chart
contains the image of its entire closed cell under the homotopy. -/
private structure PrimitiveHomotopyGrid (g : ℂ → E) (ψ : ℝ × ℝ → ℂ) where
  /-- Number of equal subdivisions on each coordinate axis. -/
  size : ℕ
  /-- The grid has at least one cell. -/
  size_pos : 0 < size
  /-- Open neighborhood of the image of each cell. -/
  chart : ℕ → ℕ → Set ℂ
  /-- Local complex primitive on each chart. -/
  primitive : ℕ → ℕ → ℂ → E
  /-- Each chart is open. -/
  isOpen_chart : ∀ i < size, ∀ j < size, IsOpen (chart i j)
  /-- The local primitive has the prescribed complex derivative. -/
  hasDerivAt_primitive : ∀ i < size, ∀ j < size, ∀ z ∈ chart i j,
    HasDerivAt (primitive i j) (g z) z
  /-- The integrand is continuous along each chart. -/
  continuousOn : ∀ i < size, ∀ j < size, ContinuousOn g (chart i j)
  /-- The image of the closed cell lies in its chart. -/
  mapsTo_chart : ∀ i < size, ∀ j < size,
    ∀ t ∈ Icc (((i : ℝ) / size), ((j : ℝ) / size))
      (((i + 1 : ℝ) / size), ((j + 1 : ℝ) / size)), ψ t ∈ chart i j

namespace PrimitiveHomotopyGrid

/-- The increment of the cell primitive along the bottom edge. -/
private noncomputable def bottom {g : ℂ → E} {ψ : ℝ × ℝ → ℂ} (D : PrimitiveHomotopyGrid g ψ)
    (i j : ℕ) : E := D.primitive i j (ψ (((i + 1 : ℝ) / D.size), ((j : ℝ) / D.size))) -
      D.primitive i j (ψ (((i : ℝ) / D.size), ((j : ℝ) / D.size)))

/-- The increment of the cell primitive along the top edge. -/
private noncomputable def top {g : ℂ → E} {ψ : ℝ × ℝ → ℂ} (D : PrimitiveHomotopyGrid g ψ)
    (i j : ℕ) : E := D.primitive i j (ψ (((i + 1 : ℝ) / D.size), ((j + 1 : ℝ) / D.size))) -
      D.primitive i j (ψ (((i : ℝ) / D.size), ((j + 1 : ℝ) / D.size)))

/-- The increment of the cell primitive along the left edge. -/
private noncomputable def left {g : ℂ → E} {ψ : ℝ × ℝ → ℂ} (D : PrimitiveHomotopyGrid g ψ)
    (i j : ℕ) : E := D.primitive i j (ψ (((i : ℝ) / D.size), ((j + 1 : ℝ) / D.size))) -
      D.primitive i j (ψ (((i : ℝ) / D.size), ((j : ℝ) / D.size)))

/-- The increment of the cell primitive along the right edge. -/
private noncomputable def right {g : ℂ → E} {ψ : ℝ × ℝ → ℂ} (D : PrimitiveHomotopyGrid g ψ)
    (i j : ℕ) : E := D.primitive i j (ψ (((i + 1 : ℝ) / D.size), ((j + 1 : ℝ) / D.size))) -
      D.primitive i j (ψ (((i + 1 : ℝ) / D.size), ((j : ℝ) / D.size)))

private theorem node_le_next {g : ℂ → E} {ψ : ℝ × ℝ → ℂ}
    (D : PrimitiveHomotopyGrid g ψ) (i : ℕ) :
    (i : ℝ) / D.size ≤ (i + 1 : ℝ) / D.size :=
  div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg D.size)

/-- Two adjacent horizontal edges agree because their different primitives
have the same derivative along the common edge. -/
private theorem bottom_succ_eq_top {g : ℂ → E} {ψ : ℝ × ℝ → ℂ}
    (D : PrimitiveHomotopyGrid g ψ) (hψ : Continuous ψ) {i j : ℕ}
    (hi : i < D.size) (hj : j + 1 < D.size) : D.bottom i (j + 1) = D.top i j := by
  have h := sub_eq_sub_of_hasDerivAt_of_continuous
    (γ := fun t => ψ (t, ((j + 1 : ℝ) / D.size)))
    (hψ.comp (continuous_id.prodMk continuous_const)) (D.node_le_next i)
    (D.isOpen_chart i hi (j + 1) hj) (D.isOpen_chart i hi j (by omega))
    (D.hasDerivAt_primitive i hi (j + 1) hj) (D.hasDerivAt_primitive i hi j (by omega))
    (fun t ht => D.mapsTo_chart i hi (j + 1) hj (t, ((j + 1 : ℝ) / D.size))
      ⟨⟨ht.1, by simp⟩, ⟨ht.2, by
        simpa only [Nat.cast_add, Nat.cast_one] using D.node_le_next (j + 1)⟩⟩)
    (fun t ht => D.mapsTo_chart i hi j (by omega) (t, ((j + 1 : ℝ) / D.size))
      ⟨⟨ht.1, D.node_le_next j⟩, ⟨ht.2, le_rfl⟩⟩)
  simpa only [bottom, top, Nat.cast_add, Nat.cast_one] using h

/-- Two adjacent vertical edges agree for the same continuous-path primitive
reason, without any differentiability of the square map. -/
private theorem left_succ_eq_right {g : ℂ → E} {ψ : ℝ × ℝ → ℂ}
    (D : PrimitiveHomotopyGrid g ψ) (hψ : Continuous ψ) {i j : ℕ}
    (hi : i + 1 < D.size) (hj : j < D.size) : D.left (i + 1) j = D.right i j := by
  have h := sub_eq_sub_of_hasDerivAt_of_continuous
    (γ := fun t => ψ (((i + 1 : ℝ) / D.size), t))
    (hψ.comp (continuous_const.prodMk continuous_id)) (D.node_le_next j)
    (D.isOpen_chart (i + 1) hi j hj) (D.isOpen_chart i (by omega) j hj)
    (D.hasDerivAt_primitive (i + 1) hi j hj) (D.hasDerivAt_primitive i (by omega) j hj)
    (fun t ht => D.mapsTo_chart (i + 1) hi j hj (((i + 1 : ℝ) / D.size), t)
      ⟨⟨by simp, ht.1⟩, ⟨by
        simpa only [Nat.cast_add, Nat.cast_one] using D.node_le_next (i + 1), ht.2⟩⟩)
    (fun t ht => D.mapsTo_chart i (by omega) j hj (((i + 1 : ℝ) / D.size), t)
      ⟨⟨D.node_le_next i, ht.1⟩, ⟨le_rfl, ht.2⟩⟩)
  simpa only [left, right, Nat.cast_add, Nat.cast_one] using h

/-- The interior edge increments cancel in pairs, leaving the outer
boundary transport of a continuous primitive-charted square. -/
private theorem sum_right_sub_sum_left_eq_sum_top_sub_sum_bottom
    {g : ℂ → E} {ψ : ℝ × ℝ → ℂ} (D : PrimitiveHomotopyGrid g ψ) (hψ : Continuous ψ) :
    (∑ j ∈ range D.size, D.right (D.size - 1) j) - (∑ j ∈ range D.size, D.left 0 j) =
      (∑ i ∈ range D.size, D.top i (D.size - 1)) - (∑ i ∈ range D.size, D.bottom i 0) := by
  apply sum_grid_boundary_eq _ _ _ _ D.size_pos
  · intro i _ j _
    dsimp [bottom, top, left, right]
    abel
  · exact fun _ hi _ hj => D.bottom_succ_eq_top hψ hi hj
  · exact fun _ hi _ hj => D.left_succ_eq_right hψ hi hj

end PrimitiveHomotopyGrid

/-- Every compact continuous square inside an open holomorphy domain has an
finite primitive grid. Its mesh and primitives are derived by compact
Lebesgue subdivision and local convex primitives. -/
private theorem nonempty_primitiveHomotopyGrid_of_differentiableOn [CompleteSpace E]
    {ψ : ℝ × ℝ → ℂ} (hψ : Continuous ψ) {Ω : Set ℂ} {g : ℂ → E}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω)
    (hψΩ : ∀ t ∈ Icc (0 : ℝ × ℝ) 1, ψ t ∈ Ω) :
    Nonempty (PrimitiveHomotopyGrid g ψ) := by
  classical
  have hrad : ∀ z : Ω, ∃ r : ℝ, 0 < r ∧ ball (z : ℂ) r ⊆ Ω :=
    fun z => mem_nhds_iff.mp (hΩ.mem_nhds z.property)
  choose r hr hball using hrad
  let B : Ω → Set ℂ := fun z => ball (z : ℂ) (r z)
  have hprimitive : ∀ z : Ω, ∃ G : ℂ → E, ∀ w ∈ B z, HasDerivAt G (g w) w := by
    intro z
    obtain ⟨G, hG⟩ := (convex_ball (z : ℂ) (r z)).exists_forall_hasDerivWithinAt
      (hg.mono (hball z))
    exact ⟨G, fun w hw => (hG w hw).hasDerivAt (isOpen_ball.mem_nhds hw)⟩
  choose G hG using hprimitive
  have hcover : ψ '' Icc (0 : ℝ × ℝ) 1 ⊆ ⋃ z : Ω, B z := by
    rintro z ⟨t, ht, rfl⟩
    apply mem_iUnion.mpr
    exact ⟨⟨ψ t, hψΩ t ht⟩, mem_ball_self (hr _)⟩
  obtain ⟨n, hn, hmesh⟩ := exists_uniform_grid_subordinate_open_cover ψ hψ B
    (fun _ => isOpen_ball) hcover
  choose J hJ using hmesh
  let K : ℕ → ℕ → Ω := fun i j =>
    if hi : i < n then if hj : j < n then J i hi j hj else J 0 hn 0 hn else J 0 hn 0 hn
  refine ⟨⟨n, hn, fun i j => B (K i j), fun i j => G (K i j),
    fun _ _ _ _ => isOpen_ball, fun i _ j _ => hG (K i j),
    fun i _ j _ => hg.continuousOn.mono (hball (K i j)), ?_⟩⟩
  intro i hi j hj
  simpa only [K, dif_pos hi, dif_pos hj] using hJ i hi j hj

end Complex

end

section

open Set Finset MeasureTheory

open scoped unitInterval

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem PrimitiveHomotopyGrid.top_eq_bottom_of_periodic
    {g : ℂ → E} {ψ : ℝ × ℝ → ℂ} (D : PrimitiveHomotopyGrid g ψ) (hψ : Continuous ψ)
    (hloop : ∀ t ∈ Icc (0 : ℝ) 1, ψ (t, 0) = ψ (t, 1))
    (hlast : D.size - 1 < D.size) (hlastnode : (((D.size - 1 : ℕ) : ℝ) + 1) / D.size = 1)
    (hnode : ∀ (i : ℕ), i ≤ D.size → (i : ℝ) / D.size ∈ Icc (0 : ℝ) 1)
    (hcellI : ∀ (i : ℕ), i < D.size → ∀ {t : ℝ},
      t ∈ Icc ((i : ℝ) / D.size) ((i + 1 : ℝ) / D.size) → t ∈ Icc (0 : ℝ) 1)
    (hp : ∀ (i : ℕ), i < D.size → (i : ℝ) / D.size ≤ ((i + 1 : ℕ) : ℝ) / D.size)
    (i : ℕ) (hi : i < D.size) :
    D.top i (D.size - 1) = D.bottom i 0 := by
  have h := sub_eq_sub_of_hasDerivAt_of_continuous
    (γ := fun t => ψ (t, 0)) (hψ.comp (continuous_id.prodMk continuous_const))
    (hp i hi) (D.isOpen_chart i hi _ hlast) (D.isOpen_chart i hi 0 D.size_pos)
    (D.hasDerivAt_primitive i hi _ hlast) (D.hasDerivAt_primitive i hi 0 D.size_pos)
    (fun t ht => by
      have ht' : t ∈ Icc ((i : ℝ) / D.size) ((i + 1 : ℝ) / D.size) := by
        simpa only [Nat.cast_add, Nat.cast_one] using ht
      rw [hloop t (hcellI i hi ht')]
      apply D.mapsTo_chart i hi _ hlast
      exact ⟨⟨ht'.1, (hnode _ hlast.le).2⟩, ⟨ht'.2, hlastnode.symm.le⟩⟩)
    (fun t ht => by
      apply D.mapsTo_chart i hi 0 D.size_pos
      exact ⟨⟨ht.1, by simp⟩, ⟨by simpa only [Nat.cast_add, Nat.cast_one] using ht.2,
        by positivity⟩⟩)
  have hnext := hnode (i + 1) hi
  have hcur := hnode i hi.le
  have hnext' : (i + 1 : ℝ) / D.size ∈ Icc (0 : ℝ) 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hnext
  simpa only [PrimitiveHomotopyGrid.top, PrimitiveHomotopyGrid.bottom,
    Nat.cast_zero, zero_div, hlastnode, Nat.cast_add, Nat.cast_one,
    ← hloop _ hnext', ← hloop _ hcur] using h

private theorem PrimitiveHomotopyGrid.integral_eq [CompleteSpace E]
    {a b : ℂ} (γ₀ : Path a a) (γ₁ : Path b b)
    {ψ : ℝ × ℝ → ℂ} (hψ : Continuous ψ) {g : ℂ → E} (D : PrimitiveHomotopyGrid g ψ)
    (hleft : ∀ t ∈ Icc (0 : ℝ) 1, γ₀.extend t = ψ (0, t))
    (hright : ∀ t ∈ Icc (0 : ℝ) 1, γ₁.extend t = ψ (1, t))
    (hloop : ∀ t ∈ Icc (0 : ℝ) 1, ψ (t, 0) = ψ (t, 1))
    (hγ₀ : ContDiffOn ℝ 1 γ₀.extend I) (hγ₁ : ContDiffOn ℝ 1 γ₁.extend I) :
    curveIntegral (fun z => (ContinuousLinearMap.id ℂ ℂ).smulRight (g z)) γ₀ =
      curveIntegral (fun z => (ContinuousLinearMap.id ℂ ℂ).smulRight (g z)) γ₁ := by
  classical
  have hn : 0 < (D.size : ℝ) := by exact_mod_cast D.size_pos
  have hlast : D.size - 1 < D.size := Nat.sub_lt D.size_pos Nat.one_pos
  have hlastadd : D.size - 1 + 1 = D.size := Nat.sub_add_cancel (Nat.succ_le_of_lt D.size_pos)
  have hend : ((D.size - 1 : ℕ) : ℝ) + 1 = D.size := by exact_mod_cast hlastadd
  have hlastnode : (((D.size - 1 : ℕ) : ℝ) + 1) / D.size = 1 := by
    rw [hend, div_self hn.ne']
  have hnode (i : ℕ) (hi : i ≤ D.size) : (i : ℝ) / D.size ∈ Icc (0 : ℝ) 1 :=
    Nat.cast_div_mem_Icc D.size_pos hi
  have hcellI (i : ℕ) (hi : i < D.size) {t : ℝ}
      (ht : t ∈ Icc ((i : ℝ) / D.size) ((i + 1 : ℝ) / D.size)) : t ∈ Icc (0 : ℝ) 1 := by
    have hnext : (i + 1 : ℝ) / D.size ∈ Icc (0 : ℝ) 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hnode (i + 1) hi
    exact ⟨(hnode i hi.le).1.trans ht.1, ht.2.trans hnext.2⟩
  have hp (i : ℕ) (_hi : i < D.size) :
      (i : ℝ) / D.size ≤ ((i + 1 : ℕ) : ℝ) / D.size := by
    apply div_le_div_of_nonneg_right _ hn.le
    exact_mod_cast Nat.le_succ i
  have hleftChart : ∀ j < D.size,
      ∀ t ∈ Icc ((j : ℝ) / D.size) (((j + 1 : ℕ) : ℝ) / D.size),
        γ₀.extend t ∈ D.chart 0 j := by
    intro j hj t ht
    have ht' : t ∈ Icc ((j : ℝ) / D.size) ((j + 1 : ℝ) / D.size) := by
      simpa only [Nat.cast_add, Nat.cast_one] using ht
    rw [hleft t (hcellI j hj ht')]
    apply D.mapsTo_chart 0 D.size_pos j hj
    exact ⟨⟨by simp, ht'.1⟩, ⟨by positivity, ht'.2⟩⟩
  have hrightChart : ∀ j < D.size,
      ∀ t ∈ Icc ((j : ℝ) / D.size) (((j + 1 : ℕ) : ℝ) / D.size),
        γ₁.extend t ∈ D.chart (D.size - 1) j := by
    intro j hj t ht
    have ht' : t ∈ Icc ((j : ℝ) / D.size) ((j + 1 : ℝ) / D.size) := by
      simpa only [Nat.cast_add, Nat.cast_one] using ht
    rw [hright t (hcellI j hj ht')]
    apply D.mapsTo_chart _ hlast j hj
    exact ⟨⟨(hnode _ hlast.le).2, ht'.1⟩, ⟨hlastnode.symm.le, ht'.2⟩⟩
  have hL := primitiveSubdivisionTransport_eq_curveIntegral_of_hasDerivAt γ₀ hγ₀
    hp (by simp) (by simp [D.size_pos.ne']) hnode
    (fun j hj => D.hasDerivAt_primitive 0 D.size_pos j hj)
    (fun j hj => D.continuousOn 0 D.size_pos j hj) hleftChart
  have hR := primitiveSubdivisionTransport_eq_curveIntegral_of_hasDerivAt γ₁ hγ₁
    hp (by simp) (by simp [D.size_pos.ne']) hnode
    (fun j hj => D.hasDerivAt_primitive _ hlast j hj)
    (fun j hj => D.continuousOn _ hlast j hj) hrightChart
  have hsumL : (∑ j ∈ range D.size, D.left 0 j) =
      curveIntegral (fun z => (ContinuousLinearMap.id ℂ ℂ).smulRight (g z)) γ₀ := by
    rw [← hL]
    unfold primitiveSubdivisionTransport
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have hnext := hnode (j + 1) hj'
    simp only [PrimitiveHomotopyGrid.left, Nat.cast_zero, zero_div]
    rw [hleft _ hnext, hleft _ (hnode j hj'.le)]
    simp only [Nat.cast_add, Nat.cast_one]
  have hsumR : (∑ j ∈ range D.size, D.right (D.size - 1) j) =
      curveIntegral (fun z => (ContinuousLinearMap.id ℂ ℂ).smulRight (g z)) γ₁ := by
    rw [← hR]
    unfold primitiveSubdivisionTransport
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have hnext := hnode (j + 1) hj'
    simp only [PrimitiveHomotopyGrid.right, hlastnode]
    rw [hright _ hnext, hright _ (hnode j hj'.le)]
    simp only [Nat.cast_add, Nat.cast_one]
  have htopBottom := D.top_eq_bottom_of_periodic hψ hloop hlast hlastnode hnode hcellI hp
  have hboundary := D.sum_right_sub_sum_left_eq_sum_top_sub_sum_bottom hψ
  have hsum : (∑ i ∈ range D.size, D.top i (D.size - 1)) =
      ∑ i ∈ range D.size, D.bottom i 0 := by
    exact sum_congr rfl (fun i hi => htopBottom i (mem_range.mp hi))
  rw [hsum, sub_self, hsumL, hsumR] at hboundary
  exact (sub_eq_zero.mp hboundary).symm

/-- A continuous free homotopy through closed curves in an open holomorphy domain preserves
the integral of $g(z)\,dz$ when both end curves are continuously differentiable.
The target is a complex Banach space. For the scalar case see [StewartTall2018, Chapter 9]. -/
theorem _root_.ContinuousMap.Homotopy.integral_eq_of_differentiableOn [CompleteSpace E]
    {a b : ℂ} {γ₀ : Path a a} {γ₁ : Path b b}
    (H : (γ₀ : C(I, ℂ)).Homotopy γ₁) {Ω : Set ℂ} {g : ℂ → E}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω)
    (himage : ∀ p, H p ∈ Ω) (hloop : ∀ t : I, H (t, 0) = H (t, 1))
    (hγ₀ : ContDiffOn ℝ 1 γ₀.extend I) (hγ₁ : ContDiffOn ℝ 1 γ₁.extend I) :
    curveIntegral (fun z => (ContinuousLinearMap.id ℂ ℂ).smulRight (g z)) γ₀ =
      curveIntegral (fun z => (ContinuousLinearMap.id ℂ ℂ).smulRight (g z)) γ₁ := by
  let ψ (p : ℝ × ℝ) : ℂ :=
    H (projIcc 0 1 zero_le_one p.1, projIcc 0 1 zero_le_one p.2)
  have hψ : Continuous ψ := H.continuous_toFun.comp
    (continuous_projIcc.prodMap continuous_projIcc)
  let D := Classical.choice (nonempty_primitiveHomotopyGrid_of_differentiableOn
    hψ hΩ hg (fun p _ => himage _))
  apply D.integral_eq γ₀ γ₁ hψ _ _ _ hγ₀ hγ₁
  · intro t _
    simp [ψ, Path.extend, Set.IccExtend]
  · intro t _
    simp [ψ, Path.extend, Set.IccExtend]
  · intro t _
    simpa [ψ] using hloop (projIcc 0 1 zero_le_one t)

/-- A continuous real parametrization of a homotopy gives equal contour integrals when its
horizontal slices close up and its two end loops are continuously differentiable.
The contour integrals of $g(z)\,dz$ on the two end loops agree [StewartTall2018, Chapter 9]. -/
theorem integral_eq_of_differentiableOn_of_freeHomotopy
    {a b : ℂ} (γ₀ : Path a a) (γ₁ : Path b b)
    {ψ : ℝ × ℝ → ℂ} (hψ : Continuous ψ) {Ω : Set ℂ} {g : ℂ → ℂ}
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω)
    (hψΩ : ∀ t ∈ Icc (0 : ℝ × ℝ) 1, ψ t ∈ Ω)
    (hleft : ∀ t ∈ Icc (0 : ℝ) 1, γ₀.extend t = ψ (0, t))
    (hright : ∀ t ∈ Icc (0 : ℝ) 1, γ₁.extend t = ψ (1, t))
    (hloop : ∀ t ∈ Icc (0 : ℝ) 1, ψ (t, 0) = ψ (t, 1))
    (hγ₀ : ContDiffOn ℝ 1 γ₀.extend I) (hγ₁ : ContDiffOn ℝ 1 γ₁.extend I) :
    curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ₀ =
      curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ) γ₁ := by
  let H : (γ₀ : C(I, ℂ)).Homotopy γ₁ :=
    { toFun := fun p => ψ (p.1, p.2)
      continuous_toFun := hψ.comp (continuous_subtype_val.prodMap continuous_subtype_val)
      map_zero_left := fun t => by simpa using (hleft t t.property).symm
      map_one_left := fun t => by simpa using (hright t t.property).symm }
  have heq := H.integral_eq_of_differentiableOn hΩ hg
    (fun p => hψΩ _ ⟨⟨p.1.property.1, p.2.property.1⟩, ⟨p.1.property.2, p.2.property.2⟩⟩)
    (fun t => hloop t t.property) hγ₀ hγ₁
  have hω (z : ℂ) : (ContinuousLinearMap.id ℂ ℂ).smulRight (g z) =
      g z • ContinuousLinearMap.id ℂ ℂ := by
    apply ContinuousLinearMap.ext
    intro v
    simp [mul_comm]
  simpa only [hω] using heq

end Complex

end
