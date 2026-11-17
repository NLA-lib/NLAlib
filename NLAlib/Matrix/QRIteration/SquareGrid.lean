/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.Strategy

/-!
# Separation and size of the square grid

The square grid `NLAlib.squareGrid c R ε` of the exceptional shifts covers the disk
$\mathbb{D}(c, R)$ at distance $\varepsilon R$ (`NLAlib.exists_mem_squareGrid_norm_sub_le`). Its
spacing is $2R/m$ with $m = \lceil\sqrt2/\varepsilon\rceil$, at least
$2\varepsilon R/(\sqrt2 + \varepsilon)$, so for $\varepsilon \le 1/2$ distinct grid points are at
distance at least $0.99\,\varepsilon R$, the separation a random translate of a net needs. The
grid restricted to the disk $\mathbb{D}(c, (1 + \varepsilon)R)$ still covers $\mathbb{D}(c, R)$
at distance $\varepsilon R$ and has at most $9/\varepsilon^2$ points.
[BanksGarzaVargasSrivastava2021, proof of Lemma 4.7] uses a maximal $\varepsilon R$-separated
subset of the disk instead of a grid.

## Main results

* `NLAlib.squareGrid_pairwise_separated`: distinct grid points are $0.99\,\varepsilon R$ apart.
* `NLAlib.exists_mem_filter_squareGrid_norm_sub_le`: the restricted grid covers the disk.
* `NLAlib.card_filter_squareGrid_le`: the restricted grid has at most $9/\varepsilon^2$ points.
* `NLAlib.length_squareGrid_mul_sq_le`: the whole grid has at most
  $(\sqrt2 + 2\varepsilon)^2/\varepsilon^2$ points.
* `NLAlib.squareGrid_mul_eq_map`: the grid of radius $tR$ is the grid of radius $R$ around $0$,
  scaled by $t$ and translated by the centre.
-/

@[expose] public section

namespace NLAlib

/-- The number of grid lines, $m = \lceil\sqrt2/\varepsilon\rceil$, is positive and less than
$\sqrt2/\varepsilon + 1$. -/
private theorem ceil_sqrt_two_div_bounds {ε : ℝ} (hε : 0 < ε) :
    (1 : ℝ) ≤ ⌈Real.sqrt 2 / ε⌉₊ ∧ (⌈Real.sqrt 2 / ε⌉₊ : ℝ) < Real.sqrt 2 / ε + 1 := by
  have hs0 : 0 < Real.sqrt 2 / ε := by positivity
  refine ⟨?_, Nat.ceil_lt_add_one hs0.le⟩
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hs0).ne'

/-- Distinct points of the square grid are separated: for $R \ge 0$ and
$0 < \varepsilon \le 1/2$, two distinct points $a \ne b$ of `NLAlib.squareGrid c R ε` have
$\lvert a - b\rvert \ge 0.99\,\varepsilon R$. -/
theorem squareGrid_pairwise_separated (c : ℂ) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    ∀ a ∈ squareGrid c R ε, ∀ b ∈ squareGrid c R ε, a ≠ b → 0.99 * (ε * R) ≤ ‖a - b‖ := by
  obtain ⟨hm1, hmlt⟩ := ceil_sqrt_two_div_bounds hε
  set m : ℕ := ⌈Real.sqrt 2 / ε⌉₊
  have hm0 : (0 : ℝ) < m := by linarith
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs15 : Real.sqrt 2 < 1.4143 := by nlinarith [Real.sqrt_nonneg 2]
  -- the spacing `2R/m` is at least `0.99εR`
  have hsp : 0.99 * (ε * R) ≤ 2 * R / m := by
    have hmε : (m : ℝ) * ε < Real.sqrt 2 + ε := by
      have := mul_lt_mul_of_pos_right hmlt hε
      rwa [add_mul, div_mul_cancel₀ _ hε.ne', one_mul] at this
    rw [le_div_iff₀ hm0]
    nlinarith [mul_le_mul_of_nonneg_right hmε.le (mul_nonneg hR (by norm_num : (0 : ℝ) ≤ 0.99))]
  -- one coordinate of distinct grid indices differs by at least one step
  have hstep : ∀ i i' : ℕ, i ≠ i' →
      2 * R / m ≤ |R * (2 * (i : ℝ) / m - 1) - R * (2 * (i' : ℝ) / m - 1)| := by
    intro i i' hii
    have h1 : (1 : ℝ) ≤ |(i : ℝ) - i'| := by
      rcases Nat.lt_or_gt_of_ne hii with h | h
      · have : (i : ℝ) + 1 ≤ i' := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      · have : (i' : ℝ) + 1 ≤ i := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
    have he : R * (2 * (i : ℝ) / m - 1) - R * (2 * (i' : ℝ) / m - 1) =
        2 * R / m * ((i : ℝ) - i') := by field_simp; ring
    rw [he, abs_mul, abs_of_nonneg (by positivity)]
    exact le_mul_of_one_le_right (by positivity) h1
  intro a ha b hb hab
  unfold squareGrid at ha hb
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at ha hb
  obtain ⟨i, -, j, -, rfl⟩ := ha
  obtain ⟨i', -, j', -, rfl⟩ := hb
  refine hsp.trans ?_
  by_cases hii : i = i'
  · have hjj : j ≠ j' := fun h => hab (by rw [hii, h])
    refine (hstep j j' hjj).trans ?_
    refine le_of_eq_of_le ?_ (Complex.abs_im_le_norm _)
    simp [Complex.mul_im, m]
  · refine (hstep i i' hii).trans ?_
    refine le_of_eq_of_le ?_ (Complex.abs_re_le_norm _)
    simp [Complex.mul_re, m]

/-- The square grid restricted to the enlarged disk covers the disk: for $R \ge 0$,
$\varepsilon > 0$ and $\lvert z - c\rvert \le R$, some point $s$ of `NLAlib.squareGrid c R ε`
with $\lvert s - c\rvert \le (1 + \varepsilon)R$ has $\lvert z - s\rvert \le \varepsilon R$. -/
theorem exists_mem_filter_squareGrid_norm_sub_le {c z : ℂ} {R ε : ℝ} (hR : 0 ≤ R)
    (hε : 0 < ε) (hz : ‖z - c‖ ≤ R) :
    ∃ s ∈ (squareGrid c R ε).toFinset.filter (fun s => ‖s - c‖ ≤ (1 + ε) * R),
      ‖z - s‖ ≤ ε * R := by
  obtain ⟨s, hs, hzs⟩ := exists_mem_squareGrid_norm_sub_le hR hε hz
  refine ⟨s, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hs, ?_⟩, hzs⟩
  calc ‖s - c‖ = ‖(z - c) - (z - s)‖ := by ring_nf
    _ ≤ ‖z - c‖ + ‖z - s‖ := norm_sub_le _ _
    _ ≤ (1 + ε) * R := by linarith

/-- The size of the restricted square grid: for $0 < \varepsilon \le 1/2$, the points $s$ of
`NLAlib.squareGrid c R ε` with $\lvert s - c\rvert \le (1 + \varepsilon)R$ are at most
$9/\varepsilon^2$. -/
theorem card_filter_squareGrid_le (c : ℂ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (((squareGrid c R ε).toFinset.filter (fun s => ‖s - c‖ ≤ (1 + ε) * R)).card : ℝ) ≤
      9 / ε ^ 2 := by
  have hlen :
      (squareGrid c R ε).length = (⌈Real.sqrt 2 / ε⌉₊ + 1) * (⌈Real.sqrt 2 / ε⌉₊ + 1) := by
    simp [squareGrid, List.length_flatMap, List.length_map, List.length_range]
  have hcard : ((squareGrid c R ε).toFinset.filter (fun s => ‖s - c‖ ≤ (1 + ε) * R)).card ≤
      (squareGrid c R ε).length :=
    (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)
  have hcard' : (((squareGrid c R ε).toFinset.filter (fun s => ‖s - c‖ ≤ (1 + ε) * R)).card : ℝ)
      ≤ ((⌈Real.sqrt 2 / ε⌉₊ : ℝ) + 1) * ((⌈Real.sqrt 2 / ε⌉₊ : ℝ) + 1) := by
    rw [hlen] at hcard; exact_mod_cast hcard
  refine hcard'.trans ?_
  obtain ⟨-, hmlt⟩ := ceil_sqrt_two_div_bounds hε
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs15 : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [Real.sqrt_nonneg 2]
  have hmε : ((⌈Real.sqrt 2 / ε⌉₊ : ℝ) + 1) * ε ≤ 3 := by
    have := mul_lt_mul_of_pos_right hmlt hε
    rw [add_mul, div_mul_cancel₀ _ hε.ne', one_mul] at this
    nlinarith
  have h0 : 0 ≤ ((⌈Real.sqrt 2 / ε⌉₊ : ℝ) + 1) * ε := by positivity
  rw [le_div_iff₀ (by positivity)]
  nlinarith [pow_le_pow_left₀ h0 hmε 2]

/-- The size of the square grid: for $\varepsilon > 0$, `NLAlib.squareGrid c R ε` has at most
$(\sqrt2 + 2\varepsilon)^2/\varepsilon^2$ points. -/
theorem length_squareGrid_mul_sq_le (c : ℂ) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ((squareGrid c R ε).length : ℝ) * ε ^ 2 ≤ (Real.sqrt 2 + 2 * ε) ^ 2 := by
  have hlen :
      (squareGrid c R ε).length = (⌈Real.sqrt 2 / ε⌉₊ + 1) * (⌈Real.sqrt 2 / ε⌉₊ + 1) := by
    simp [squareGrid, List.length_flatMap, List.length_map, List.length_range]
  rw [hlen]
  push_cast
  obtain ⟨-, hmlt⟩ := ceil_sqrt_two_div_bounds hε
  have hmε : ((⌈Real.sqrt 2 / ε⌉₊ : ℝ) + 1) * ε ≤ Real.sqrt 2 + 2 * ε := by
    have := mul_lt_mul_of_pos_right hmlt hε
    rw [add_mul, div_mul_cancel₀ _ hε.ne', one_mul] at this
    nlinarith
  have h0 : 0 ≤ ((⌈Real.sqrt 2 / ε⌉₊ : ℝ) + 1) * ε := by positivity
  nlinarith [pow_le_pow_left₀ h0 hmε 2]

/-- The square grid scales with its radius: the grid of centre $c$ and radius $tR$ is the
grid of centre $0$ and radius $R$, each point $g$ mapped to $c + tg$. -/
theorem squareGrid_mul_eq_map (c : ℂ) (t R ε : ℝ) :
    squareGrid c (t * R) ε = (squareGrid 0 R ε).map fun g => c + (t : ℂ) * g := by
  unfold squareGrid
  simp only [List.map_flatMap, List.map_map]
  refine List.flatMap_congr fun i _ => List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply, zero_add]
  push_cast
  ring

/-- A finite net for a complex disk: for $R>0$ and $0<r\le R$, some finite set covers the
closed disk of radius $R$ around $c$ at distance $r/2$ and has cardinality times $r^2$ at most
$36R^2$. The square-grid estimate underlying
[BanksGarzaVargasSrivastava2021, proof of Lemma 4.7]. -/
theorem exists_finset_card_mul_sq_le_and_forall_norm_sub_le (c : ℂ) {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ R) :
    ∃ Z : Finset ℂ, (Z.card : ℝ) * r ^ 2 ≤ 36 * R ^ 2 ∧
      ∀ z : ℂ, ‖z - c‖ ≤ R → ∃ y ∈ Z, ‖z - y‖ ≤ r / 2 := by
  classical
  let ε := r / (2 * R)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε2 : ε ≤ 1 / 2 := by
    dsimp [ε]
    rw [div_le_iff₀ (by positivity : 0 < 2 * R)]
    linarith
  let Z := (squareGrid c R ε).toFinset
  refine ⟨Z, ?_, ?_⟩
  · have hc : (Z.card : ℝ) ≤ (squareGrid c R ε).length := by
      exact_mod_cast (List.toFinset_card_le (squareGrid c R ε))
    have hlen := length_squareGrid_mul_sq_le c R hε
    have hsqrt : √2 ≤ (2 : ℝ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have h9 : (Z.card : ℝ) * ε ^ 2 ≤ 9 := by
      have hh : (√2 + 2 * ε) ^ 2 ≤ 9 := by
        nlinarith [Real.sqrt_nonneg 2]
      exact ((mul_le_mul_of_nonneg_right hc (sq_nonneg ε)).trans hlen).trans hh
    calc
      (Z.card : ℝ) * r ^ 2 = ((Z.card : ℝ) * ε ^ 2) * (4 * R ^ 2) := by
        dsimp [ε]
        field_simp
        ring
      _ ≤ 9 * (4 * R ^ 2) := mul_le_mul_of_nonneg_right h9 (by positivity)
      _ = _ := by ring
  · intro z hz
    obtain ⟨y, hy, hzy⟩ := exists_mem_squareGrid_norm_sub_le hR.le hε hz
    refine ⟨y, List.mem_toFinset.mpr hy, hzy.trans_eq ?_⟩
    dsimp [ε]
    field_simp

end NLAlib
