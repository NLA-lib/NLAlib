/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.SpectralBisection.Split

/-!
# The children of a node of spectral bisection

A child of a node of
`NLAlib.eighChild` carries the machine's next window and tolerance (`NLAlib.eighNextParams`),
whose rounding is bounded here, and the children of a node with a good sample keep the node
invariant: a Hermitian matrix with $\|\mathbf{A}'\|_2 \le R'$ ([Shah2024, proof of Lemma 4.1]).

## Main results

* `NLAlib.le_eq_false_and_le_and_eq_of_eighChild_eq_some`: the parameters of a child.
* `NLAlib.FloatMachine.IsAccurate.dec_eighNextParams_le`: the rounded next window and tolerance.
* `NLAlib.FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_isEighNodeBudget`: the child
  invariant.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- The parameters of a child: a child $y$ of a node $x$ (`NLAlib.eighChild`) exists only when
$x$ is internal, $k \ge 2$ and the machine's leaf test $R \le \mathrm{fl}(\varepsilon R_0)$
fails; it has size at most $x$'s, and
carries the next window and tolerance of `NLAlib.eighNextParams` and the depth counter
$\ell + 1$. -/
theorem le_eq_false_and_le_and_eq_of_eighChild_eq_some {F Su Sg : Type*} [Inhabited Sg]
    {M : FloatMachine F Su Sg} {N signFuel : ℕ} {R₀ β : F} {x y : EighNode F}
    {smp : EighSample Su Sg N} {b : Bool} (h : eighChild M N signFuel R₀ β x smp b = some y) :
    2 ≤ x.k ∧ M.le x.R (M.mul x.ε R₀) = false ∧ y.k ≤ x.k ∧
      y.R = (eighNextParams M x.R x.ε x.ℓ).1 ∧ y.ε = (eighNextParams M x.R x.ε x.ℓ).2 ∧
      y.ℓ = x.ℓ + 1 := by
  unfold eighChild eighStep at h
  by_cases h1 : x.k ≤ 1
  · simp [h1] at h
  by_cases h2 : M.le x.R (M.mul x.ε R₀) = true
  · simp [h1, h2] at h
  simp only [h1, h2, if_false] at h
  split_ifs at h <;> dsimp only at h <;> (try split_ifs at h) <;> cases h <;>
    exact ⟨by omega, by simpa using h2, by dsimp only; omega, rfl, rfl, rfl⟩

/-- The real arithmetic of the next window of `NLAlib.eighNextParams`. -/
private lemma le_of_isRoundingOf_eighNextParams_fst {u τ Ω m t L a1 a2 c p1 r : ℝ}
    (hu : 0 ≤ u) (hum : 500 * m * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1) (hm : 20 ≤ m)
    (hmΩ : 2 * m ≤ Ω) (hr : 0 ≤ r) (hrΩ : r ≤ Ω)
    (ht : IsRoundingOf u τ Ω 2 t) (hL : IsRoundingOf u τ Ω m L)
    (ha1 : t ≠ 0 → IsRoundingOf u τ Ω (1 / t) a1) (ha2 : L ≠ 0 → IsRoundingOf u τ Ω (t / L) a2)
    (hc : IsRoundingOf u τ Ω (a1 + a2) c) (hp1 : IsRoundingOf u τ Ω (c * r) p1) :
    p1 ≤ (1 / 2 + 2 / m) * (1 + 22 * u) * r + u * τ := by
  have rnd : ∀ {a z : ℝ}, IsRoundingOf u τ Ω a z → 0 ≤ a → a ≤ Ω →
      a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) :=
    fun h ha0 ha => le_and_le_of_isRoundingOf h ha0 ha hu hτ₀
  have hm0 : 0 < m := by linarith
  obtain ⟨w, hw_def⟩ : ∃ w, w = 1 / m := ⟨_, rfl⟩
  have hwm : w * m = 1 := by rw [hw_def]; field_simp
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw20 : w ≤ 1 / 20 := by rw [hw_def, div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have hu' : u ≤ w / 500 := by
    have h := mul_le_mul_of_nonneg_left hum hw0.le
    have h' : w * (500 * m * u) = 500 * u * (w * m) := by ring
    rw [h', hwm] at h; linarith
  have hu1 : u ≤ 1 / 10000 := by linarith
  have huτ : u * τ ≤ u := mul_le_of_le_one_right hu hτ
  have huτ0 : 0 ≤ u * τ := mul_nonneg hu hτ₀
  have huu : u * u ≤ u / 10000 := by have := mul_le_mul_of_nonneg_left hu1 hu; linarith
  have huu0 : 0 ≤ u * u := mul_nonneg hu hu
  have huw' : u * w ≤ u / 20 := by have := mul_le_mul_of_nonneg_left hw20 hu; linarith
  have huw0 : 0 ≤ u * w := mul_nonneg hu hw0.le
  have hum1 : u * (w * m) = u := by rw [hwm, mul_one]
  have hum' : u * m ≤ 1 / 500 := by
    have := mul_le_mul_of_nonneg_right hu' hm0.le
    have h2 : w / 500 * m = (w * m) / 500 := by ring
    rw [h2, hwm] at this; linarith
  have hwuτ : w * (u * τ) ≤ u * τ := mul_le_of_le_one_left huτ0 (by linarith)
  -- the stored `2` and `ℓ`
  obtain ⟨ht1, ht2⟩ := rnd ht (by norm_num) (by linarith)
  obtain ⟨hL1, hL2⟩ := rnd hL hm0.le (by linarith)
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  have hwL1 : 1 - 2 * u ≤ w * L := by
    have := mul_le_mul_of_nonneg_left hL1 hw0.le; linarith
  have hwL2 : w * L ≤ 1 + 2 * u := by
    have := mul_le_mul_of_nonneg_left hL2 hw0.le; linarith
  -- `fl(1/2)`
  have hit1 : 1 / t ≤ 1 / 2 + u := by
    rw [div_le_iff₀ ht0]
    have := mul_le_mul_of_nonneg_left (by linarith : 2 - 3 * u ≤ t) (by linarith : 0 ≤ 1 / 2 + u)
    linarith
  have hit2 : 1 / 2 - u ≤ 1 / t := by
    rw [le_div_iff₀ ht0]
    have := mul_le_mul_of_nonneg_left (by linarith : t ≤ 2 + 3 * u) (by linarith : 0 ≤ 1 / 2 - u)
    linarith
  obtain ⟨ha11, ha12⟩ := rnd (ha1 ht0.ne') (one_div_nonneg.mpr ht0.le) (by linarith)
  have hut := mul_le_mul_of_nonneg_left hit1 hu
  have hA1 : a1 ≤ 1 / 2 + 3 * u := by linarith
  have hA1' : 1 / 2 - 3 * u ≤ a1 := by linarith
  -- `fl(2/ℓ)`
  have hq1 : t / L ≤ (2 + 8 * u) * w := by
    rw [div_le_iff₀ hL0, mul_assoc]
    have := mul_le_mul_of_nonneg_left hwL1 (by linarith : 0 ≤ 2 + 8 * u)
    linarith
  have hq0 : 0 ≤ t / L := div_nonneg ht0.le hL0.le
  have hq5 : t / L ≤ 1 / 5 := by linarith
  obtain ⟨ha21, ha22⟩ := rnd (ha2 hL0.ne') hq0 (by linarith)
  have huq := mul_le_mul_of_nonneg_left hq5 hu
  have huq0 := mul_nonneg hu hq0
  have hA2 : a2 ≤ 2 * w + 2 * u := by linarith
  have hA2' : -2 * u ≤ a2 := by linarith
  -- `fl(fl(1/2) + fl(2/ℓ))`
  obtain ⟨hc1, hc2⟩ := rnd hc (by linarith) (by linarith)
  have huS := mul_le_mul_of_nonneg_left (by linarith : a1 + a2 ≤ 61 / 100) hu
  have huS0 := mul_nonneg hu (by linarith : (0 : ℝ) ≤ a1 + a2)
  have hC : c ≤ (1 / 2 + 2 * w) * (1 + 14 * u) := by linarith
  have hC0 : 0 ≤ c := by linarith
  have hC1 : c ≤ 1 := by linarith
  obtain ⟨-, hp⟩ := rnd hp1 (mul_nonneg hC0 hr) (by linarith [mul_le_of_le_one_left hr hC1])
  have hK : 0 ≤ (1 / 2 + 2 * w) * r := mul_nonneg (by linarith) hr
  have h22 : (1 + 14 * u) * (1 + u) ≤ 1 + 22 * u := by linarith
  have hcr : c * r ≤ (1 / 2 + 2 * w) * (1 + 14 * u) * r := mul_le_mul_of_nonneg_right hC hr
  have h1 := mul_le_mul_of_nonneg_right hcr (by linarith : (0 : ℝ) ≤ 1 + u)
  have h2 := mul_le_mul_of_nonneg_left h22 hK
  have : (2 : ℝ) / m = 2 * w := by rw [hw_def]; ring
  rw [this]
  linarith

/-- The real arithmetic of the next tolerance of `NLAlib.eighNextParams`. -/
private lemma le_and_le_of_isRoundingOf_eighNextParams_snd {u τ Ω m L e1 d p2 e : ℝ}
    (hu : 0 ≤ u) (hum : 500 * m * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1) (hm : 20 ≤ m)
    (hmΩ : 2 * m ≤ Ω) (he : 0 ≤ e) (he₁ : e ≤ 1) (hL : IsRoundingOf u τ Ω m L)
    (he1 : L ≠ 0 → IsRoundingOf u τ Ω (1 / L) e1) (hd : IsRoundingOf u τ Ω (1 - e1) d)
    (hp2 : IsRoundingOf u τ Ω (d * e) p2) :
    (1 - 1 / m) * (1 - 9 * u) * e - u * τ ≤ p2 ∧ p2 ≤ (1 - 1 / m) * e + 7 * u * e + u * τ := by
  have rnd : ∀ {a z : ℝ}, IsRoundingOf u τ Ω a z → 0 ≤ a → a ≤ Ω →
      a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) :=
    fun h ha0 ha => le_and_le_of_isRoundingOf h ha0 ha hu hτ₀
  have hm0 : 0 < m := by linarith
  obtain ⟨w, hw_def⟩ : ∃ w, w = 1 / m := ⟨_, rfl⟩
  have hwm : w * m = 1 := by rw [hw_def]; field_simp
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw20 : w ≤ 1 / 20 := by rw [hw_def, div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have hu' : u ≤ w / 500 := by
    have h := mul_le_mul_of_nonneg_left hum hw0.le
    have h' : w * (500 * m * u) = 500 * u * (w * m) := by ring
    rw [h', hwm] at h; linarith
  have hu1 : u ≤ 1 / 10000 := by linarith
  have huτ : u * τ ≤ u := mul_le_of_le_one_right hu hτ
  have huτ0 : 0 ≤ u * τ := mul_nonneg hu hτ₀
  have huu : u * u ≤ u / 10000 := by have := mul_le_mul_of_nonneg_left hu1 hu; linarith
  have huu0 : 0 ≤ u * u := mul_nonneg hu hu
  have huw' : u * w ≤ u / 20 := by have := mul_le_mul_of_nonneg_left hw20 hu; linarith
  have huw0 : 0 ≤ u * w := mul_nonneg hu hw0.le
  have hum1 : u * (w * m) = u := by rw [hwm, mul_one]
  have hum' : u * m ≤ 1 / 500 := by
    have := mul_le_mul_of_nonneg_right hu' hm0.le
    have h2 : w / 500 * m = (w * m) / 500 := by ring
    rw [h2, hwm] at this; linarith
  have hwuτ : w * (u * τ) ≤ u * τ := mul_le_of_le_one_left huτ0 (by linarith)
  -- the stored `2` and `ℓ`
  obtain ⟨hL1, hL2⟩ := rnd hL hm0.le (by linarith)
  have hL0 : 0 < L := by linarith
  have hwL1 : 1 - 2 * u ≤ w * L := by
    have := mul_le_mul_of_nonneg_left hL1 hw0.le; linarith
  have hwL2 : w * L ≤ 1 + 2 * u := by
    have := mul_le_mul_of_nonneg_left hL2 hw0.le; linarith
  -- `fl(1/ℓ)` and `fl(1 - fl(1/ℓ))`
  have hiL1 : 1 / L ≤ (1 + 3 * u) * w := by
    rw [div_le_iff₀ hL0, mul_assoc]
    have := mul_le_mul_of_nonneg_left hwL1 (by linarith : 0 ≤ 1 + 3 * u)
    linarith
  have hiL2 : (1 - 3 * u) * w ≤ 1 / L := by
    rw [le_div_iff₀ hL0, mul_assoc]
    have := mul_le_mul_of_nonneg_left hwL2 (by linarith : 0 ≤ 1 - 3 * u)
    linarith
  have hiL0 : 0 ≤ 1 / L := one_div_nonneg.mpr hL0.le
  have hiL10 : 1 / L ≤ 1 / 10 := by linarith
  obtain ⟨he11, he12⟩ := rnd (he1 hL0.ne') hiL0 (by linarith)
  have huL := mul_le_mul_of_nonneg_left hiL10 hu
  have huL0 := mul_nonneg hu hiL0
  have hE1 : e1 ≤ w + 2 * u := by linarith
  have hE1' : w - 2 * u ≤ e1 := by linarith
  obtain ⟨hd1, hd2⟩ := rnd hd (by linarith) (by linarith)
  have hue := mul_le_mul_of_nonneg_left (by linarith : 1 - e1 ≤ 1 - w + 2 * u) hu
  have hue' := mul_le_mul_of_nonneg_left (by linarith : 1 - w - 2 * u ≤ 1 - e1) hu
  have hD : (1 - w) * (1 - 5 * u) ≤ d := by linarith
  have hD' : d ≤ 1 - w + 5 * u := by linarith
  have hD0 : 0 ≤ d := by linarith
  have hD1 : d ≤ 1 := by linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨hp, -⟩ := rnd hp2 (mul_nonneg hD0 he) (by linarith [mul_le_one₀ hD1 he he₁])
    have hde : (1 - w) * (1 - 5 * u) * e ≤ d * e := mul_le_mul_of_nonneg_right hD he
    have h9 : (1 - w) * (1 - 9 * u) ≤ (1 - w) * ((1 - 5 * u) * (1 - u)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h1 := mul_le_mul_of_nonneg_right hde (by linarith : (0 : ℝ) ≤ 1 - u)
    have h2 := mul_le_mul_of_nonneg_right h9 he
    rw [← hw_def]
    linarith
  · obtain ⟨-, hp⟩ := rnd hp2 (mul_nonneg hD0 he) (by linarith [mul_le_one₀ hD1 he he₁])
    have hde : d * e ≤ (1 - w + 5 * u) * e := mul_le_mul_of_nonneg_right hD' he
    have hkey : (1 - w + 5 * u) * (1 + u) ≤ 1 - w + 7 * u := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hde (by linarith : (0 : ℝ) ≤ 1 + u)
    have h2 := mul_le_mul_of_nonneg_right hkey he
    rw [← hw_def]
    linarith

/-- The rounded next window and tolerance: for stored $0 \le R \le \Omega$ and
$0 \le \varepsilon \le 1$, a depth counter $m \ge 20$ with $500mu \le 1$, $2m \le \Omega$ and
$0 \le \tau \le 1$, the machine's next window and tolerance (`NLAlib.eighNextParams`) satisfy
$R' \le (1/2 + 2/m)(1 + 22u)R + u\tau$ and
$(1 - 1/m)(1 - 9u)\varepsilon - u\tau \le \varepsilon' \le (1 - 1/m)\varepsilon + 7u\varepsilon +
u\tau$. -/
theorem FloatMachine.IsAccurate.dec_eighNextParams_le {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    {R ε : F} {m : ℕ} (hu : 0 ≤ u) (hum : 500 * (m : ℝ) * u ≤ 1) (hτ₀ : 0 ≤ τ) (hτ : τ ≤ 1)
    (hm : 20 ≤ m) (hmΩ : 2 * (m : ℝ) ≤ Ω) (hR : 0 ≤ dec R) (hRΩ : dec R ≤ Ω) (hε : 0 ≤ dec ε)
    (hε₁ : dec ε ≤ 1) :
    dec (eighNextParams M R ε m).1 ≤ (1 / 2 + 2 / m) * (1 + 22 * u) * dec R + u * τ ∧
    (1 - 1 / m) * (1 - 9 * u) * dec ε - u * τ ≤ dec (eighNextParams M R ε m).2 ∧
    dec (eighNextParams M R ε m).2 ≤ (1 - 1 / m) * dec ε + 7 * u * dec ε + u * τ := by
  have h2 := hM.ofNat 2
  push_cast at h2
  have hm' : (20 : ℝ) ≤ m := by exact_mod_cast hm
  exact ⟨le_of_isRoundingOf_eighNextParams_fst hu hum hτ₀ hτ hm' hmΩ hR hRΩ h2 (hM.ofNat m)
    (fun h => hM.dec_one ▸ hM.div _ _ h) (fun h => hM.div _ _ h) (hM.add _ _) (hM.mul _ _),
    le_and_le_of_isRoundingOf_eighNextParams_snd hu hum hτ₀ hτ hm' hmΩ hε hε₁ (hM.ofNat m)
    (fun h => hM.dec_one ▸ hM.div _ _ h) (hM.dec_one ▸ hM.sub _ _) (hM.mul _ _)⟩

/-- The real arithmetic of the lower bound on the next window. -/
private theorem le_of_isRoundingOf_eighNextParams_fst_of_le {u τ Ω m t L a1 a2 c p r : ℝ}
    (hu : 0 ≤ u) (hum : u * m ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 8) (hm : 20 ≤ m)
    (hrτ : 7 * τ ≤ r) (hΩ : 2 * r + 2 * m + 4 ≤ Ω)
    (ht : IsRoundingOf u τ Ω 2 t) (hL : IsRoundingOf u τ Ω m L)
    (ha1 : t ≠ 0 → IsRoundingOf u τ Ω (1 / t) a1) (ha2 : L ≠ 0 → IsRoundingOf u τ Ω (t / L) a2)
    (hc : IsRoundingOf u τ Ω (a1 + a2) c) (hp : IsRoundingOf u τ Ω (c * r) p) :
    (1 / 2 + 2 / m) * r - 4 * u * r ≤ p := by
  have rnd : ∀ {a z : ℝ}, IsRoundingOf u τ Ω a z → 0 ≤ a → a ≤ Ω →
      a - u * (a + τ) ≤ z ∧ z ≤ a + u * (a + τ) :=
    fun h ha0 ha => le_and_le_of_isRoundingOf h ha0 ha hu hτ₀
  have hm0 : 0 < m := by linarith
  obtain ⟨w, hw_def⟩ : ∃ w, w = 1 / m := ⟨_, rfl⟩
  have hwm : w * m = 1 := by rw [hw_def]; field_simp
  have hw0 : 0 < w := by rw [hw_def]; positivity
  have hw20 : w ≤ 1 / 20 := by rw [hw_def, div_le_div_iff₀ hm0 (by norm_num)]; linarith
  have hu20 := mul_le_mul_of_nonneg_left hm hu
  have hu1 : u ≤ 1 / 20000 := by linarith
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  have huu := mul_nonneg hu hu
  have hr0 : 0 ≤ r := by linarith
  -- the stored `2` and `ℓ`
  obtain ⟨ht1, ht2⟩ := rnd ht (by norm_num) (by linarith)
  obtain ⟨hL1, hL2⟩ := rnd hL hm0.le (by linarith)
  have ht0 : 0 < t := by linarith
  have hL0 : 0 < L := by linarith
  have ht2' : t ≤ 2 + 2.125 * u := by linarith
  -- `fl(1/fl(2))`
  have hit1 : 1 / 2 - 0.6 * u ≤ 1 / t := by
    rw [le_div_iff₀ ht0]
    have := mul_le_mul_of_nonneg_left ht2' (by linarith : (0 : ℝ) ≤ 1 / 2 - 0.6 * u)
    linarith
  have hit2 : 1 / t ≤ 0.51 := by rw [div_le_iff₀ ht0]; linarith
  obtain ⟨hA1, -⟩ := rnd (ha1 ht0.ne') (by positivity) (by linarith)
  have := mul_le_mul_of_nonneg_left hit2 hu
  -- `fl(fl(2)/fl(ℓ))`
  have hq1 : 2 * w - 5 * u * w ≤ t / L := by
    rw [le_div_iff₀ hL0]
    have h0 : 0 ≤ w * (2 - 5 * u) := mul_nonneg hw0.le (by linarith)
    have := mul_le_mul_of_nonneg_left hL2 h0
    have e : w * (2 - 5 * u) * (m + u * (m + τ)) =
        (2 - 5 * u) * (1 + u) + w * (2 - 5 * u) * (u * τ) := by
      linear_combination (2 - 5 * u) * (1 + u) * hwm
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτ1 hu) h0
    have := mul_le_mul_of_nonneg_right hw20 (by linarith : (0 : ℝ) ≤ 2 - 5 * u)
    have := mul_nonneg hw0.le hu
    nlinarith
  have hq2 : t / L ≤ 0.11 := by rw [div_le_iff₀ hL0]; linarith
  obtain ⟨hA2, -⟩ := rnd (ha2 hL0.ne') (by positivity) (by linarith)
  have := mul_le_mul_of_nonneg_left hq2 hu
  have := mul_le_mul_of_nonneg_left hw20 hu
  -- `fl(a1 + a2)`
  have ha1u : a1 ≤ 0.52 := by
    obtain ⟨-, h⟩ := rnd (ha1 ht0.ne') (by positivity) (by linarith); linarith
  have ha2u : a2 ≤ 0.12 := by
    obtain ⟨-, h⟩ := rnd (ha2 hL0.ne') (by positivity) (by linarith); linarith
  obtain ⟨hC, hC'⟩ := rnd hc (by linarith) (by linarith)
  have := mul_le_mul_of_nonneg_left (by linarith : a1 + a2 ≤ 0.65) hu
  have hC1 : 1 / 2 + 2 * w - 2.55 * u ≤ c := by linarith
  have hC2 : c ≤ 0.66 := by linarith
  -- `fl(c r)`
  have hcr0 : 0 ≤ c * r := mul_nonneg (by linarith) hr0
  have hcr1 : c * r ≤ 0.66 * r := mul_le_mul_of_nonneg_right hC2 hr0
  obtain ⟨hP, -⟩ := rnd hp hcr0 (by linarith)
  have := mul_le_mul_of_nonneg_right hC1 hr0
  have := mul_le_mul_of_nonneg_left hcr1 hu
  have := mul_le_mul_of_nonneg_left hrτ hu
  have := mul_nonneg hu hr0
  have e2 : 2 / m = 2 * w := by rw [hw_def]; ring
  rw [e2]
  linarith

/-- The stored next window is at least $(1/2 + 2/\ell)R - 4uR$. -/
private theorem FloatMachine.IsAccurate.le_dec_eighNextParams_fst {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (R e : F) {ℓ : ℕ} (hu : 0 ≤ u)
    (huℓ : u * ℓ ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 8) (hℓ : 20 ≤ ℓ)
    (hRτ : 7 * τ ≤ dec R) (hΩ : 2 * dec R + 2 * ℓ + 4 ≤ Ω) :
    (1 / 2 + 2 / (ℓ : ℝ)) * dec R - 4 * u * dec R ≤ dec (eighNextParams M R e ℓ).1 := by
  have h2 := hM.ofNat 2
  push_cast at h2
  exact le_of_isRoundingOf_eighNextParams_fst_of_le hu huℓ hτ₀ hτ1 (by exact_mod_cast hℓ) hRτ hΩ
    h2 (hM.ofNat ℓ) (fun h => hM.dec_one ▸ hM.div _ _ h) (fun h => hM.div _ _ h) (hM.add _ _)
    (hM.mul _ _)

/-- A Hermitian matrix between $a\mathbf{I}$ and $b\mathbf{I}$ is within $m$ of $c\mathbf{I}$ when
$b - c \le m$ and $c - a \le m$. -/
private theorem specNorm_sub_smul_one_le_of_le_of_le {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) {a b c m : ℝ} (h₁ : a • (1 : Matrix n n ℂ) ≤ X)
    (h₂ : X ≤ b • (1 : Matrix n n ℂ)) (hb : b - c ≤ m) (ha : c - a ≤ m) (hm : 0 ≤ m) :
    specNorm (X - c • (1 : Matrix n n ℂ)) ≤ m := by
  refine (hX.sub (isHermitian_real_smul_one c)).specNorm_le_of_le_smul_one hm ?_ ?_
  · have h := (smul_one_le_smul_one (n := n) (𝕜 := ℂ) (by linarith : c - m ≤ a)).trans h₁
    rw [sub_smul] at h
    rw [le_sub_iff_add_le]
    simpa [neg_add_eq_sub] using h
  · have h := h₂.trans (smul_one_le_smul_one (n := n) (𝕜 := ℂ) (by linarith : b ≤ m + c))
    rwa [add_smul, ← sub_le_iff_le_add] at h

/-- A Hermitian matrix with spectrum in $[a, b]$ lies between $a\mathbf{I}$ and $b\mathbf{I}$. -/
private theorem smul_one_le_and_le_smul_one_of_spectrum_subset {n : Type*} [Fintype n]
    [DecidableEq n] {X : Matrix n n ℂ} (hX : X.IsHermitian) {a b : ℝ}
    (h : spectrum ℝ X ⊆ Set.Icc a b) :
    a • (1 : Matrix n n ℂ) ≤ X ∧ X ≤ b • (1 : Matrix n n ℂ) := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
    exact ⟨le_of_eq (Subsingleton.elim _ _), le_of_eq (Subsingleton.elim _ _)⟩
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n := ⟨Fintype.card n - 1, by omega⟩
    exact ⟨(smul_one_le_smul_one (h (hX.eigenvalue_mem_spectrum (by omega : k < _))).1).trans
      (hX.eigenvalue_last_smul_one_le hk), hX.le_eigenvalue_zero_smul_one.trans
        (smul_one_le_smul_one (h (hX.eigenvalue_mem_spectrum h0)).2)⟩

open scoped ComplexOrder in
/-- All eigenvalues above $c$: $c\mathbf{I} \preceq \mathbf{X}$ when $i_+(\mathbf{X} -
c\mathbf{I})$ is the size. -/
private theorem smul_one_le_of_inertiaPos_eq_card {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) {c : ℝ}
    (h : inertiaPos (X - c • (1 : Matrix n n ℂ)) = Fintype.card n) :
    c • (1 : Matrix n n ℂ) ≤ X :=
  Matrix.le_iff.mpr ((hX.sub (isHermitian_real_smul_one _)).posDef_iff_inertiaPos_eq_card.mpr
    h).posSemidef

/-- No eigenvalue above $c$: $\mathbf{X} \preceq c\mathbf{I}$ when $i_+(\mathbf{X} - c\mathbf{I})
= 0$. -/
private theorem le_smul_one_of_inertiaPos_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian) {c : ℝ} (hn : 0 < Fintype.card n)
    (h : inertiaPos (X - c • (1 : Matrix n n ℂ)) = 0) :
    X ≤ c • (1 : Matrix n n ℂ) := by
  have hB : (X - c • (1 : Matrix n n ℂ)).IsHermitian := hX.sub (isHermitian_real_smul_one _)
  have hpos : ¬ 0 < inertiaPos (X - c • (1 : Matrix n n ℂ)) := by rw [h]; exact lt_irrefl 0
  rw [hB.lt_inertiaPos_iff] at hpos
  have h0 := hB.le_eigenvalue_zero_smul_one.trans (smul_one_le_smul_one (n := n) (𝕜 := ℂ)
    (le_of_not_gt fun hc => hpos ⟨hn, hc⟩))
  rw [zero_smul] at h0
  exact sub_nonpos.mp h0

/-- The deflation accuracy $\eta = (1 - 1/\ell)\varepsilon/(5\ell)$ has
$0 \le \eta\ell \le 1/40$. -/
private theorem eta_mul_le {ε : ℝ} {ℓ : ℕ} (hℓ : 20 ≤ ℓ) (hε : 0 < ε) (hε₁ : ε ≤ 1 / 8) :
    0 ≤ (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) ∧ (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) * ℓ ≤ 1 / 40 := by
  have hℓ' : (20 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have h1 : 1 / (ℓ : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h0 : 0 ≤ 1 / (ℓ : ℝ) := by positivity
  refine ⟨div_nonneg (mul_nonneg (by linarith) hε.le) (by positivity), ?_⟩
  rw [show (1 - 1 / (ℓ : ℝ)) * ε / (5 * ℓ) * ℓ = (1 - 1 / (ℓ : ℝ)) * ε / 5 by field_simp]
  linarith [mul_le_mul_of_nonneg_right (by linarith : 1 - 1 / (ℓ : ℝ) ≤ 1) hε.le]

/-- A shift child: the stored $\mathrm{fl}(\mathbf{A} - s\mathbf{I})$, for
$\|\mathbf{A} - s\mathbf{I}\|_2 \le m \le \Omega$ and $m + u(m + \tau) \le r$, is Hermitian with
norm at most $r$. -/
private theorem FloatMachine.IsAccurate.isHermitian_and_specNorm_decodeMatrix_hermShift_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k : ℕ} {A : Matrix (Fin k) (Fin k) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian) (hu : 0 ≤ u) {s : F} {m r : ℝ} (hτ₀ : 0 ≤ τ)
    (hs : specNorm (decodeMatrix dec A - dec s • (1 : Matrix (Fin k) (Fin k) ℂ)) ≤ m)
    (hΩ : m ≤ Ω) (hr : m + u * (m + τ) ≤ r) :
    (decodeMatrix dec (M.hermShift A s)).IsHermitian ∧
      specNorm (decodeMatrix dec (M.hermShift A s)) ≤ r := by
  refine ⟨hM.isHermitian_decodeMatrix_hermFrom _ _, ?_⟩
  have hS := (hM.specNorm_sub_decodeMatrix_hermShift_le hu hA s (hs.trans hΩ)).trans
    (mul_le_mul_of_nonneg_left (max_le_add_of_nonneg (specNorm_nonneg _) hτ₀) hu)
  have htri := specNorm_sub_le (decodeMatrix dec A - dec s • (1 : Matrix (Fin k) (Fin k) ℂ))
    ((decodeMatrix dec A - dec s • (1 : Matrix (Fin k) (Fin k) ℂ)) -
      decodeMatrix dec (M.hermShift A s))
  rw [sub_sub_cancel] at htri
  nlinarith [mul_le_mul_of_nonneg_left hs hu]

/-- A split child: a matrix within $\gamma$ of the shifted compression
$\mathbf{W}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}}\mathbf{X}\mathbf{V}\mathbf{W} - c\mathbf{I}$
($\mathbf{W}$ unitary), when the compression $\mathbf{V}^{\mathsf{H}}\mathbf{X}\mathbf{V}$ has
spectrum in $[a, b]$ with $b - c, c - a \le m$, has norm at most $m + \gamma$. -/
private theorem specNorm_le_of_spectrum_subset_of_specNorm_sub_le {k r : ℕ}
    {X : Matrix (Fin k) (Fin k) ℂ} (hX : X.IsHermitian) {V : Matrix (Fin k) (Fin r) ℂ}
    {W : Matrix (Fin r) (Fin r) ℂ} (hW : HasOrthonormalCols W) {a b c m γ : ℝ}
    (hspec : spectrum ℝ (Vᴴ * X * V) ⊆ Set.Icc a b) (hb : b - c ≤ m) (ha : c - a ≤ m)
    (hm : 0 ≤ m) {Y : Matrix (Fin r) (Fin r) ℂ}
    (hY : specNorm (Y - (Wᴴ * (Vᴴ * X * V) * W - c • (1 : Matrix (Fin r) (Fin r) ℂ))) ≤ γ) :
    specNorm Y ≤ m + γ := by
  have hC : (Vᴴ * X * V).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul V hX
  obtain ⟨hlo, hhi⟩ := smul_one_le_and_le_smul_one_of_spectrum_subset hC hspec
  have hWC : specNorm (Wᴴ * (Vᴴ * X * V) * W - c • (1 : Matrix (Fin r) (Fin r) ℂ)) ≤ m := by
    rw [show Wᴴ * (Vᴴ * X * V) * W - c • (1 : Matrix (Fin r) (Fin r) ℂ) =
        Wᴴ * (Vᴴ * X * V - c • (1 : Matrix (Fin r) (Fin r) ℂ)) * W by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        show Wᴴ * W = 1 from hW]]
    exact (hW.specNorm_conjTranspose_mul_mul_le _).trans
      (specNorm_sub_smul_one_le_of_le_of_le hC hlo hhi hb ha hm)
  have h := specNorm_add_le (Wᴴ * (Vᴴ * X * V) * W - c • (1 : Matrix (Fin r) (Fin r) ℂ))
    (Y - (Wᴴ * (Vᴴ * X * V) * W - c • (1 : Matrix (Fin r) (Fin r) ℂ)))
  rw [add_sub_cancel] at h
  linarith

/-! ### Generic node lemmas for a precision budget -/

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
  {N signFuel : ℕ} {R₀ β : F} {w x t : ℝ} {y : EighNode F}

/-- The scalar facts of a node budget: $k^2u \le 10^{-5}$, $k\tau \le 1/4$, $u\ell \le 10^{-5}$
and $t \ge 2$, for $k \ge 1$. -/
private theorem FloatMachine.IsEighNodeBudget.scalars
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk : 1 ≤ y.k) :
    (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 ∧ (y.k : ℝ) * τ ≤ 1 / 4 ∧ u * y.ℓ ≤ 1 / 100000 ∧
      2 ≤ t := by
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hsk : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hs2 : 1 ≤ √(2 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have ht : 2 ≤ t := by nlinarith [hB.le_t]
  have hu := hB.nonneg_u
  have hβ := hB.pos_β
  -- `2048 k ⋅ 20 u ≤ β` from the stopping condition
  have hku : 40960 * (y.k * u) ≤ dec β := by
    have := mul_le_mul_of_nonneg_right (by linarith [hB.nonneg_μM] :
      (20 : ℝ) ≤ 4 * μM y.k + 10 + 10 * √(y.k : ℝ))
      (mul_nonneg (by linarith : (0 : ℝ) ≤ y.k + 1) hu)
    linarith [hB.mul_le_dec_β hk]
  have hkβ := hB.mul_β_le
  refine ⟨by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ y.k) hu], ?_, ?_, ht⟩
  · have := hB.τ_le.trans ((min_le_left _ _).trans hB.x_le)
    nlinarith [mul_le_mul_of_nonneg_left hsk (mul_nonneg (by linarith : (0 : ℝ) ≤ y.k) hB.nonneg_τ)]
  · have hℓ : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
    have h4 : 4 ≤ 2 * t / x := by rw [le_div_iff₀ hB.pos_x]; nlinarith [hB.x_le, hB.pos_x]
    have hη : (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) * y.ℓ ≤ 1 / 40 := by
      rw [show (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) * y.ℓ =
        (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / 5 by field_simp]
      have : 0 ≤ 1 / (y.ℓ : ℝ) := by positivity
      nlinarith [hB.ε_le, hB.pos_ε]
    have h1 := mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_right h4 hβ.le)
      hB.defl_tol) (by linarith : (0 : ℝ) ≤ y.ℓ)
    nlinarith [mul_le_mul_of_nonneg_right hk1 (mul_nonneg hu (by linarith : (0 : ℝ) ≤ y.ℓ))]

/-- The scalar budget of a child under a node budget: with $D = R/\ell$, the stored half window
$h = \mathrm{fl}(R/\mathrm{fl}(2))$ and $m = R/2 + D + 1.5uR$, $\lvert h - R/2\rvert \le 1.5uR$
and the next window $R'$ is at least $m + u(m + \tau)$ and $m + (2 + 2\eta)R\eta$, and
$m \le \Omega$, when $k \ge 2$ and the leaf test fails. -/
private theorem FloatMachine.IsAccurate.child_numerics_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk : 2 ≤ y.k)
    (hint : M.le y.R (M.mul y.ε R₀) = false) :
    |dec (M.div y.R (M.ofNat 2)) - dec y.R / 2| ≤ 3 * u * (dec y.R / 2) ∧
      dec y.R / 2 + dec y.R / y.ℓ + 1.5 * (u * dec y.R) + u * (dec y.R / 2 + dec y.R / y.ℓ +
        1.5 * (u * dec y.R) + τ) ≤ dec (eighNextParams M y.R y.ε y.ℓ).1 ∧
      dec y.R / 2 + dec y.R / y.ℓ + 1.5 * (u * dec y.R) +
        (2 + 2 * ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) * dec y.R *
          ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)) ≤ dec (eighNextParams M y.R y.ε y.ℓ).1 ∧
      dec y.R / 2 + dec y.R / y.ℓ + 1.5 * (u * dec y.R) ≤ Ω := by
  have hℓ := hB.twenty_le
  have hε := hB.pos_ε
  have hε₁ := hB.ε_le
  have hR₀ := hB.pos_R₀
  have hw := hB.pos_w
  have hwR := hB.w_le
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hτ := hB.τ_le
  have hΩ := hB.Ω_le
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hℓ
  obtain ⟨-, hkτ, huℓ, ht2⟩ := hB.scalars (by omega)
  obtain ⟨hη0, hηℓ⟩ := eta_mul_le hℓ hε hε₁
  have hk2 : (2 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hu1 : u ≤ 1 / 1000 := by linarith [mul_le_mul_of_nonneg_left hℓ' hu]
  have hτ1 : τ ≤ 1 / 8 := by linarith [mul_le_mul_of_nonneg_right hk2 hτ₀]
  have hR0 : 0 < dec y.R := hw.trans_le hwR
  have hRτ : 7 * τ ≤ dec y.R := by
    have h2 := mul_le_mul hk2 (Real.one_le_sqrt.mpr (by linarith : (1 : ℝ) ≤ y.k)) zero_le_one
      (by linarith)
    have := hM.mul_sub_lt_of_le_eq_false hu hτ₀ hε.le hR₀.le
      (by linarith [mul_le_mul_of_nonneg_right hε₁ hR₀.le]) hint
    linarith [hτ.trans (min_le_right _ _), mul_le_mul_of_nonneg_left h2 hτ₀,
      mul_le_mul_of_nonneg_right hu1 (mul_pos hε hR₀).le, mul_le_mul_of_nonneg_right hu1 hτ₀]
  have hR' := hM.le_dec_eighNextParams_fst y.R y.ε hu (by linarith) hτ₀ hτ1 hℓ hRτ (by linarith)
  have hhalf := hM.abs_dec_div_ofNat_two_sub_le (R := y.R) hu hu1 hτ₀ hτ1 (by linarith)
    (by linarith) (by linarith)
  set D := dec y.R / y.ℓ with hD
  have hD0 : 0 ≤ D := by positivity
  have hDℓ : D * y.ℓ = dec y.R := by rw [hD]; field_simp
  have hD20 : D ≤ dec y.R / 20 := by linarith [mul_le_mul_of_nonneg_left hℓ' hD0]
  have huR : u * dec y.R ≤ D / 100000 := by
    have := mul_le_mul_of_nonneg_right huℓ hD0
    rw [mul_assoc, mul_comm (y.ℓ : ℝ) D, hDℓ] at this
    linarith
  have huR0 : 0 ≤ u * dec y.R := mul_nonneg hu hR0.le
  rw [show (1 / 2 + 2 / (y.ℓ : ℝ)) * dec y.R = dec y.R / 2 + 2 * D by rw [hD]; ring] at hR'
  set m := dec y.R / 2 + D + 1.5 * (u * dec y.R) with hm
  have hm1 : m ≤ 0.6 * dec y.R := by linarith
  have hr : m + u * (m + τ) ≤ dec (eighNextParams M y.R y.ε y.ℓ).1 := by
    linarith [mul_le_mul_of_nonneg_left hm1 hu, mul_le_mul_of_nonneg_left hRτ hu]
  set η := (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) with hη
  have hηR : (2 + 2 * η) * dec y.R * η ≤ D / 19 := by
    have hη1 : η ≤ 1 / 800 := by linarith [mul_le_mul_of_nonneg_left hℓ' hη0]
    rw [show (2 + 2 * η) * dec y.R * η = (2 + 2 * η) * (η * y.ℓ) * D by rw [← hDℓ]; ring]
    have := mul_le_mul (by linarith : 2 + 2 * η ≤ 2.0025) hηℓ (by positivity) (by norm_num)
    linarith [mul_le_mul_of_nonneg_right this hD0]
  exact ⟨hhalf, hr, by linarith, by linarith⟩

/-- **Child invariant under a node budget**: with budget `NLAlib.FloatMachine.IsEighNodeBudget` and
a good sample (`NLAlib.IsEighGoodSample` with parameters $(w, x, t)$), every child
has a Hermitian matrix of norm at most its window. [Shah2024, proof of Lemma 4.1]. -/
theorem FloatMachine.IsAccurate.isHermitian_and_specNorm_le_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    {smp : EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w x t y smp)
    {b : Bool} {y' : EighNode F} (hy' : eighChild M N signFuel R₀ β y smp b = some y') :
    (decodeMatrix dec y'.A).IsHermitian ∧ specNorm (decodeMatrix dec y'.A) ≤ dec y'.R := by
  have hk : 2 ≤ y.k := by
    by_contra hk
    simp [eighChild, eighStep, show y.k ≤ 1 by omega] at hy'
  have hint := (le_eq_false_and_le_and_eq_of_eighChild_eq_some hy').2.1
  obtain ⟨⟨hv, hI⟩, -⟩ := hgood hk hint
  obtain ⟨hhalf, hr, hrη, hmΩ⟩ := hM.child_numerics_of_isEighNodeBudget hB hk hint
  have hkp := hM.min_toNat_eq_inertiaPos_of_isEighNodeBudget hB hk hint hv hI
  have hA := hB.isHermitian
  have hR := hB.specNorm_le
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  set X := decodeMatrix dec y.A with hX
  set D := dec y.R / y.ℓ with hD
  set h := dec (M.div y.R (M.ofNat 2)) with hh
  set m := dec y.R / 2 + D + 1.5 * (u * dec y.R) with hm
  set η := (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) with hη
  have hR0 : 0 ≤ dec y.R := (specNorm_nonneg _).trans hR
  have hD0 : 0 ≤ D := div_nonneg hR0 (Nat.cast_nonneg _)
  have hc'1 : -D ≤ D * smp.1 := by linarith [mul_le_mul_of_nonneg_left hv.1 hD0]
  have hc'2 : D * smp.1 ≤ D := by linarith [mul_le_mul_of_nonneg_left hv.2 hD0]
  have huR0 : 0 ≤ u * dec y.R := mul_nonneg hu hR0
  obtain ⟨hh1, hh2⟩ := abs_le.mp hhalf
  have hm0 : 0 ≤ m := by linarith
  have hXR : X ≤ dec y.R • (1 : Matrix (Fin y.k) (Fin y.k) ℂ) := hA.le_smul_one_of_specNorm_le hR
  have hXR' : (-dec y.R) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ) ≤ X := by
    rw [neg_smul]; exact hA.neg_smul_one_le_of_specNorm_le hR
  have hshift := fun (s : F) (hs : specNorm (X - dec s • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) ≤ m) =>
    hM.isHermitian_and_specNorm_decodeMatrix_hermShift_le hA hu hτ₀ hs hmΩ hr
  unfold eighChild eighStep at hy'
  rw [if_neg (by omega), if_neg (by simp [hint])] at hy'
  dsimp only at hy'
  split_ifs at hy' with h1 h2 h3 h4
  · -- the shift child on the positive side
    simp only [h2, if_true, Option.some.injEq] at hy'
    subst hy'
    rw [hkp] at h1
    exact hshift _ (specNorm_sub_smul_one_le_of_le_of_le hA
      (smul_one_le_of_inertiaPos_eq_card hA (by rw [Fintype.card_fin]; exact h1)) hXR
      (by linarith) (by linarith) hm0)
  · simp [h2] at hy'
  · simp [h4] at hy'
  · -- the shift child on the negative side
    simp only [show b = false by simpa using h4, if_true, Option.some.injEq] at hy'
    subst hy'
    rw [hkp] at h3
    refine hshift _ (specNorm_sub_smul_one_le_of_le_of_le hA hXR'
      (le_smul_one_of_inertiaPos_eq_zero hA (by rw [Fintype.card_fin]; omega) h3) ?_ ?_ hm0) <;>
      rw [hM.dec_neg] <;> linarith
  all_goals
    obtain ⟨-, hP, hQ⟩ := hM.exists_hasOrthonormalCols_specNorm_sub_le_of_isEighNodeBudget hB hgood
      (by
        unfold eighStep
        rw [if_neg (by omega), if_neg (by simp [hint])]
        dsimp only
        rw [if_neg h1, if_neg h3])
    rw [← hη, ← hX, ← hD, ← hh] at hP hQ
    simp only [Option.some.injEq] at hy'
    subst hy'
    refine ⟨hM.isHermitian_decodeMatrix_hermFrom _ _, ?_⟩
  · -- the split child on the positive side
    obtain ⟨V, hV, -, hspec, W, hW, -, hAp⟩ := hP
    exact (specNorm_le_of_spectrum_subset_of_specNorm_sub_le hA hW hspec (by linarith)
      (by linarith) hm0 hAp).trans (by linarith)
  · -- the split child on the negative side
    obtain ⟨V, hV, -, hspec, W, hW, -, hAm⟩ := hQ
    rw [← sub_neg_eq_add, ← neg_smul] at hAm
    exact (specNorm_le_of_spectrum_subset_of_specNorm_sub_le hA hW hspec (by linarith)
      (by linarith) hm0 hAm).trans (by linarith)

end NLAlib
