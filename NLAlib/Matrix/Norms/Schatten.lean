/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import NLAlib.Matrix.Norms.Nuclear

/-!
# Schatten norms

The Schatten `q`-norm `NLAlib.schattenNorm q A` of a matrix is the `ℓ^q` norm of its singular
values, for `q : ℝ≥0∞`. The cases `q = 1`, `q = 2` and `q = ⊤` are the nuclear, Frobenius and
spectral norms. It is defined as Mathlib's `PiLp` norm of the vector of the first
`min (card m) (card n)` singular values, so `q = ⊤` needs no separate definition, and the
degenerate `q = 0` gives the rank.

Statements that hold for every exponent take `q` alone; homogeneity, definiteness and the
comparisons need `q ≠ 0`; the triangle inequality needs `1 ≤ q`, as an explicit hypothesis.
Natural exponents have their own power-sum and trace forms, with `ℕ` powers, in
`NLAlib.Matrix.Norms.SchattenPowers`.

## Main definitions

* `NLAlib.schattenNorm`: the Schatten `q`-norm.

## Main results

* `NLAlib.schattenNorm_one`, `NLAlib.schattenNorm_two`, `NLAlib.schattenNorm_top`: the nuclear,
  Frobenius and spectral norms.
* `NLAlib.schattenNorm_eq_sum_rpow`: the formula for finite positive `q`.
* `NLAlib.schattenNorm_congr`, `NLAlib.schattenNorm_le_mul_of_singularValues_le`: Schatten norms
  depend only on the singular values, monotonically, across shapes.
* `NLAlib.schattenNorm_add_le`: the triangle inequality for `1 ≤ q`.
* `NLAlib.schattenNorm_anti`, `NLAlib.schattenNorm_le_rank_rpow_mul_schattenNorm`: comparison
  between exponents.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-- The **Schatten `q`-norm**: the `ℓ^q` norm of the singular values, for `q : ℝ≥0∞`.
For `q = 1`, `2`, `⊤` it is the nuclear, Frobenius and spectral norm; it is a norm for `1 ≤ q`.
For `q = 0` it is the rank, following Mathlib's convention for `ℓ^0`.
[HornJohnson2013, §7.4.7]; [Bhatia1997, §IV.2]. Port of `NLAlib.schattenNorm`, with the arguments
in the other order. -/
noncomputable def schattenNorm (q : ℝ≥0∞) (A : Matrix m n 𝕜) : ℝ :=
  ‖(WithLp.toLp q fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues A i :
    PiLp q fun _ : Fin (min (Fintype.card m) (Fintype.card n)) => ℝ)‖

/-! ### Special exponents -/

/-- The Schatten `∞`-norm is the spectral norm. Port of `NLAlib.schattenNorm_top`. -/
@[simp]
theorem schattenNorm_top (A : Matrix m n 𝕜) : schattenNorm ⊤ A = specNorm A := by
  rw [schattenNorm, PiLp.norm_toLp]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (specNorm_nonneg A)).mpr fun i => ?_) ?_
  · rw [Real.norm_of_nonneg (singularValues_nonneg A i)]
    exact singularValues_le_specNorm A i
  · rw [← singularValues_zero_eq_specNorm]
    rcases Nat.eq_zero_or_pos (min (Fintype.card m) (Fintype.card n)) with h | h
    · rw [(singularValues_eq_zero_iff A).mpr
        ((le_min A.rank_le_card_height A.rank_le_card_width).trans h.le)]
      exact norm_nonneg _
    · exact (Real.norm_of_nonneg (singularValues_nonneg A 0)).symm.le.trans
        (norm_le_pi_norm (fun i : Fin _ => singularValues A i) ⟨0, h⟩)

/-- The Schatten `0`-"norm" is the rank. -/
theorem schattenNorm_zero_eq_rank (A : Matrix m n 𝕜) : schattenNorm 0 A = A.rank := by
  classical
  rw [schattenNorm, PiLp.norm_eq_card, Set.Finite.toFinset_ofPred]
  have h : ∀ i : Fin (min (Fintype.card m) (Fintype.card n)),
      ‖singularValues A i‖ ≠ 0 ↔ (i : ℕ) < A.rank := fun i => by
    rw [Ne, norm_eq_zero, singularValues_eq_zero_iff, not_le]
  simp only [h, Fin.card_filter_val_lt,
    min_eq_right (le_min A.rank_le_card_height A.rank_le_card_width)]

/-- The sum of a fixed nonzero power of the singular values may stop at the rank. -/
private theorem sum_range_singularValues_rpow (A : Matrix m n 𝕜) {t : ℝ} (ht : t ≠ 0) {N : ℕ}
    (hN : A.rank ≤ N) :
    ∑ i ∈ Finset.range N, singularValues A i ^ t =
      ∑ i ∈ Finset.range A.rank, singularValues A i ^ t :=
  (Finset.sum_subset (Finset.range_mono hN) fun i _ hi => by
    rw [(singularValues_eq_zero_iff A).mpr (not_lt.mp fun h => hi (Finset.mem_range.mpr h)),
      Real.zero_rpow ht]).symm

/-- **The Schatten norm as a power sum.** For `0 < q < ∞` and any `N` at least the rank,
`‖A‖_q = (∑ i < N, σ_i ^ q) ^ (1 / q)`.
Port of `NLAlib.schattenNormReal_eq_sum_range_rpow_of_min_le` and
`NLAlib.schattenNormReal_eq_sum_rank_rpow`. -/
theorem schattenNorm_eq_sum_rpow {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ⊤) (A : Matrix m n 𝕜) {N : ℕ}
    (hN : A.rank ≤ N) :
    schattenNorm q A = (∑ i ∈ Finset.range N, singularValues A i ^ q.toReal) ^ q.toReal⁻¹ := by
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [sum_range_singularValues_rpow A hq'.ne' hN, ← sum_range_singularValues_rpow A hq'.ne'
    (le_min A.rank_le_card_height A.rank_le_card_width), schattenNorm, PiLp.norm_eq_sum hq',
    one_div, ← Fin.sum_univ_eq_sum_range fun i => singularValues A i ^ q.toReal]
  simp only [Real.norm_of_nonneg (singularValues_nonneg A _)]

/-- The `q`-th power of the Schatten `q`-norm is the sum of the `q`-th powers of the singular
values. -/
theorem schattenNorm_rpow {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ⊤) (A : Matrix m n 𝕜) {N : ℕ}
    (hN : A.rank ≤ N) :
    schattenNorm q A ^ q.toReal = ∑ i ∈ Finset.range N, singularValues A i ^ q.toReal := by
  rw [schattenNorm_eq_sum_rpow hq0 hq A hN]
  exact Real.rpow_inv_rpow (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (singularValues_nonneg A i) _) (ENNReal.toReal_pos hq0 hq).ne'

/-- The Schatten `1`-norm is the nuclear norm. Port of `NLAlib.schattenNorm_one`. -/
@[simp]
theorem schattenNorm_one (A : Matrix m n 𝕜) : schattenNorm 1 A = nuclearNorm A := by
  rw [schattenNorm_eq_sum_rpow one_ne_zero ENNReal.one_ne_top A
    (le_min A.rank_le_card_height A.rank_le_card_width), ENNReal.toReal_one, inv_one,
    Real.rpow_one, nuclearNorm]
  simp only [Real.rpow_one]

/-- The Schatten `2`-norm is the Frobenius norm. Port of `NLAlib.schattenNorm_two`, there over
`ℝ`. -/
@[simp]
theorem schattenNorm_two (A : Matrix m n 𝕜) : schattenNorm 2 A = frobNorm A := by
  rw [schattenNorm_eq_sum_rpow two_ne_zero ENNReal.ofNat_ne_top A le_rfl, ENNReal.toReal_ofNat]
  simp only [Real.rpow_two]
  rw [← frobNorm_sq_eq_sum_range_singularValues_sq A le_rfl, ← Real.rpow_two,
    Real.rpow_rpow_inv (frobNorm_nonneg A) two_ne_zero]

/-- Schatten norms are nonnegative. Port of `NLAlib.schattenNorm_nonneg`. -/
theorem schattenNorm_nonneg (q : ℝ≥0∞) (A : Matrix m n 𝕜) : 0 ≤ schattenNorm q A := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [schattenNorm_zero_eq_rank]
    exact Nat.cast_nonneg _
  rcases eq_or_ne q ⊤ with rfl | hq
  · rw [schattenNorm_top]
    exact specNorm_nonneg A
  · rw [schattenNorm_eq_sum_rpow hq0 hq A le_rfl]
    exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (singularValues_nonneg A i) _) _

/-! ### Norm properties -/

/-- The spectral norm is at most every Schatten norm with a finite nonzero exponent. -/
private theorem specNorm_le_schattenNorm_of_ne_top {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ⊤)
    (A : Matrix m n 𝕜) : specNorm A ≤ schattenNorm q A := by
  rw [← Real.rpow_le_rpow_iff (specNorm_nonneg A) (schattenNorm_nonneg q A)
    (ENNReal.toReal_pos hq0 hq), schattenNorm_rpow hq0 hq A (le_max_right 1 A.rank),
    ← singularValues_zero_eq_specNorm]
  exact Finset.single_le_sum (f := fun i => singularValues A i ^ q.toReal)
    (fun i _ => Real.rpow_nonneg (singularValues_nonneg A i) _)
    (Finset.mem_range.mpr (zero_lt_one.trans_le (le_max_left 1 A.rank)))

/-- Schatten norms of the zero matrix vanish. -/
@[simp]
theorem schattenNorm_zero (q : ℝ≥0∞) : schattenNorm q (0 : Matrix m n 𝕜) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [schattenNorm_zero_eq_rank, Matrix.rank_zero, Nat.cast_zero]
  rcases eq_or_ne q ⊤ with rfl | hq
  · rw [schattenNorm_top, specNorm_zero]
  · rw [schattenNorm_eq_sum_rpow hq0 hq 0 (N := 0) (by rw [Matrix.rank_zero]),
      Finset.sum_range_zero, Real.zero_rpow (inv_ne_zero (ENNReal.toReal_pos hq0 hq).ne')]

/-- Schatten norms are definite. Port of `NLAlib.schattenNorm_eq_zero_iff`. -/
@[simp]
theorem schattenNorm_eq_zero_iff (q : ℝ≥0∞) {A : Matrix m n 𝕜} : schattenNorm q A = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, schattenNorm_zero]⟩
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [schattenNorm_zero_eq_rank, Nat.cast_eq_zero] at h
    exact Matrix.rank_eq_zero.mp h
  rcases eq_or_ne q ⊤ with rfl | hq
  · rw [schattenNorm_top] at h
    exact specNorm_eq_zero_iff.mp h
  · exact specNorm_eq_zero_iff.mp (le_antisymm
      ((specNorm_le_schattenNorm_of_ne_top hq0 hq A).trans_eq h) (specNorm_nonneg A))

/-- A termwise bound `σ_i(A) ≤ c σ_i(B)` on the singular values gives `‖A‖_q ≤ c ‖B‖_q`, for
`q ≠ 0`. The shapes may differ. -/
theorem schattenNorm_le_mul_of_singularValues_le {q : ℝ≥0∞} (hq : q ≠ 0)
    {A : Matrix m n 𝕜} {B : Matrix l p 𝕜} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, singularValues A i ≤ c * singularValues B i) :
    schattenNorm q A ≤ c * schattenNorm q B := by
  rcases eq_or_ne q ⊤ with rfl | hq'
  · rw [schattenNorm_top, schattenNorm_top, ← singularValues_zero_eq_specNorm,
      ← singularValues_zero_eq_specNorm]
    exact h 0
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos hq hq'
  rw [← Real.rpow_le_rpow_iff (schattenNorm_nonneg q A)
    (mul_nonneg hc (schattenNorm_nonneg q B)) hq0, Real.mul_rpow hc (schattenNorm_nonneg q B),
    schattenNorm_rpow hq hq' A (le_max_left A.rank B.rank),
    schattenNorm_rpow hq hq' B (le_max_right A.rank B.rank), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Real.mul_rpow hc (singularValues_nonneg B i)]
  exact Real.rpow_le_rpow (singularValues_nonneg A i) (h i) hq0.le

/-- Matrices with the same singular values have the same Schatten norms, whatever their shapes. -/
theorem schattenNorm_congr {A : Matrix m n 𝕜} {B : Matrix l p 𝕜}
    (h : singularValues A = singularValues B) (q : ℝ≥0∞) : schattenNorm q A = schattenNorm q B := by
  rcases eq_or_ne q 0 with rfl | hq
  · have hr : A.rank = B.rank := le_antisymm
      ((singularValues_eq_zero_iff A).mp (h ▸ (singularValues_eq_zero_iff B).mpr le_rfl))
      ((singularValues_eq_zero_iff B).mp (h ▸ (singularValues_eq_zero_iff A).mpr le_rfl))
    rw [schattenNorm_zero_eq_rank, schattenNorm_zero_eq_rank, hr]
  · exact le_antisymm
      ((schattenNorm_le_mul_of_singularValues_le hq zero_le_one fun i => by
        rw [h, one_mul]).trans_eq (one_mul _))
      ((schattenNorm_le_mul_of_singularValues_le hq zero_le_one fun i => by
        rw [h, one_mul]).trans_eq (one_mul _))

/-- Schatten norms are absolutely homogeneous, for `q ≠ 0`.
Port of `NLAlib.schattenNorm_smul`. -/
theorem schattenNorm_smul {q : ℝ≥0∞} (hq : q ≠ 0) (c : 𝕜) (A : Matrix m n 𝕜) :
    schattenNorm q (c • A) = ‖c‖ * schattenNorm q A := by
  refine le_antisymm (schattenNorm_le_mul_of_singularValues_le hq (norm_nonneg c) fun i =>
    (singularValues_smul c A i).le) ?_
  rcases eq_or_ne c 0 with rfl | hc
  · rw [norm_zero, zero_mul]
    exact schattenNorm_nonneg _ _
  · have h := schattenNorm_le_mul_of_singularValues_le (A := A) (B := c • A) (c := ‖c‖⁻¹) hq
      (inv_nonneg.mpr (norm_nonneg c)) fun i => by
        rw [singularValues_smul, inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hc)]
    rwa [← div_eq_inv_mul, le_div_iff₀' (norm_pos_iff.mpr hc)] at h

/-- Schatten norms are even. -/
@[simp]
theorem schattenNorm_neg (q : ℝ≥0∞) (A : Matrix m n 𝕜) :
    schattenNorm q (-A) = schattenNorm q A := by
  exact schattenNorm_congr (singularValues_neg A) q

/-- Schatten norms are invariant under the conjugate transpose. -/
@[simp]
theorem schattenNorm_conjTranspose (q : ℝ≥0∞) (A : Matrix m n 𝕜) :
    schattenNorm q Aᴴ = schattenNorm q A := by
  exact schattenNorm_congr (singularValues_conjTranspose A) q

/-- Schatten norms are invariant under the transpose. Port of `NLAlib.schattenNorm_transpose`. -/
@[simp]
theorem schattenNorm_transpose (q : ℝ≥0∞) (A : Matrix m n 𝕜) :
    schattenNorm q Aᵀ = schattenNorm q A := by
  exact schattenNorm_congr (singularValues_transpose A) q

/-- Schatten norms are invariant under relabelling rows and columns.
Port of `NLAlib.schattenNormReal_reindex`. -/
@[simp]
theorem schattenNorm_submatrix_equiv (q : ℝ≥0∞) (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    schattenNorm q (A.submatrix e₁ e₂) = schattenNorm q A := by
  exact schattenNorm_congr (singularValues_submatrix_equiv A e₁ e₂) q

/-- Schatten norms are invariant under left multiplication by a matrix with orthonormal columns.
Port of `NLAlib.schattenNorm_orthogonal_mul`. -/
theorem HasOrthonormalCols.schattenNorm_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (q : ℝ≥0∞) (A : Matrix m n 𝕜) :
    schattenNorm q (Q * A) = schattenNorm q A := by
  exact schattenNorm_congr (hQ.singularValues_mul_left A) q

/-- Schatten norms are invariant under right multiplication by the conjugate transpose of a
matrix with orthonormal columns. Port of `NLAlib.schattenNorm_mul_orthogonal`. -/
theorem HasOrthonormalCols.schattenNorm_mul_conjTranspose_right [DecidableEq n]
    {Q : Matrix p n 𝕜} (hQ : HasOrthonormalCols Q) (q : ℝ≥0∞) (A : Matrix m n 𝕜) :
    schattenNorm q (A * Qᴴ) = schattenNorm q A := by
  exact schattenNorm_congr (hQ.singularValues_mul_conjTranspose_right A) q

/-- The positive part raised to a nonnegative power is monotone. -/
private theorem monotone_max_zero_rpow {t : ℝ} (ht : 0 ≤ t) :
    Monotone fun u : ℝ => max u 0 ^ t :=
  fun _ _ huv => Real.rpow_le_rpow (le_max_right _ _) (max_le_max_right 0 huv) ht

/-- The positive part raised to a power at least one is convex. -/
private theorem convexOn_max_zero_rpow {t : ℝ} (ht : 1 ≤ t) :
    ConvexOn ℝ Set.univ fun u : ℝ => max u 0 ^ t := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have h : max (a * x + b * y) 0 ≤ a * max x 0 + b * max y 0 :=
    max_le (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb))
      (add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _)))
  exact (Real.rpow_le_rpow (le_max_right _ _) h (zero_le_one.trans ht)).trans
    ((convexOn_rpow ht).2 (le_max_right x 0) (le_max_right y 0) ha hb hab)

/-- **The triangle inequality for Schatten norms**, `1 ≤ q`.
[Bhatia1997, §IV.2]. Port of `NLAlib.schattenNorm_add_le`, there over `ℝ`.
Result: schatten-norm -/
theorem schattenNorm_add_le {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix m n 𝕜) :
    schattenNorm q (A + B) ≤ schattenNorm q A + schattenNorm q B := by
  rcases eq_or_ne q ⊤ with rfl | hq'
  · simp only [schattenNorm_top]
    exact specNorm_add_le A B
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have ht : 1 ≤ q.toReal := (ENNReal.toReal_mono hq' hq).trans_eq' ENNReal.toReal_one.symm
  have hN : ∀ C : Matrix m n 𝕜, C.rank ≤ min (Fintype.card m) (Fintype.card n) := fun C =>
    le_min C.rank_le_card_height C.rank_le_card_width
  have hmaj : WeaklyMajorized
      (fun i : Fin (min (Fintype.card m) (Fintype.card n)) => singularValues (A + B) i)
      (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
        singularValues A i + singularValues B i) := by
    refine (weaklyMajorized_fin_iff_sum_range_le (f := singularValues (A + B))
      (g := fun i => singularValues A i + singularValues B i)
      ((singularValues_antitone _).antitoneOn _)
      (((singularValues_antitone A).add (singularValues_antitone B)).antitoneOn _)).mpr
      fun k _ => ?_
    rw [Finset.sum_add_distrib]
    exact kyFanNorm_add_le k A B
  have hsum := hmaj.sum_monotone_convex_le (monotone_max_zero_rpow (zero_le_one.trans ht))
    (convexOn_max_zero_rpow ht)
  simp only [max_eq_left (singularValues_nonneg _ _),
    max_eq_left (add_nonneg (singularValues_nonneg A _) (singularValues_nonneg B _))] at hsum
  rw [Fin.sum_univ_eq_sum_range fun i => singularValues (A + B) i ^ q.toReal,
    Fin.sum_univ_eq_sum_range fun i => (singularValues A i + singularValues B i) ^ q.toReal]
    at hsum
  rw [schattenNorm_eq_sum_rpow hq0 hq' _ (hN _), schattenNorm_eq_sum_rpow hq0 hq' _ (hN A),
    schattenNorm_eq_sum_rpow hq0 hq' _ (hN B), ← one_div]
  exact (Real.rpow_le_rpow (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (singularValues_nonneg _ i) _) hsum (by positivity)).trans
    (Real.Lp_add_le_of_nonneg _ ht (fun i _ => singularValues_nonneg A i)
      fun i _ => singularValues_nonneg B i)

/-- The reverse triangle inequality for Schatten norms, `1 ≤ q`. -/
theorem abs_schattenNorm_sub_schattenNorm_le {q : ℝ≥0∞} (hq : 1 ≤ q) (A B : Matrix m n 𝕜) :
    |schattenNorm q A - schattenNorm q B| ≤ schattenNorm q (A - B) := by
  have h1 := schattenNorm_add_le hq (A - B) B
  have h2 := schattenNorm_add_le hq (B - A) A
  rw [sub_add_cancel] at h1 h2
  rw [← neg_sub A B, schattenNorm_neg] at h2
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-! ### Comparison between exponents -/

/-- Schatten norms decrease in the exponent.
Port of `NLAlib.schattenNorm_le_of_le`, there over `ℝ` for `1 ≤ q`. -/
theorem schattenNorm_anti {q r : ℝ≥0∞} (hq : q ≠ 0) (h : q ≤ r) (A : Matrix m n 𝕜) :
    schattenNorm r A ≤ schattenNorm q A := by
  rcases eq_or_ne q ⊤ with rfl | hq'
  · rw [top_le_iff.mp h]
  rcases eq_or_ne r ⊤ with rfl | hr'
  · rw [schattenNorm_top]
    exact specNorm_le_schattenNorm_of_ne_top hq hq' A
  have hr : r ≠ 0 := ((pos_iff_ne_zero.mpr hq).trans_le h).ne'
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos hq hq'
  have hqr : 0 ≤ r.toReal - q.toReal := sub_nonneg.mpr (ENNReal.toReal_mono hr' h)
  rw [← Real.rpow_le_rpow_iff (schattenNorm_nonneg r A) (schattenNorm_nonneg q A)
    (ENNReal.toReal_pos hr hr'), schattenNorm_rpow hr hr' A le_rfl]
  calc ∑ i ∈ Finset.range A.rank, singularValues A i ^ r.toReal
      ≤ ∑ i ∈ Finset.range A.rank,
          schattenNorm q A ^ (r.toReal - q.toReal) * singularValues A i ^ q.toReal := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi : singularValues A i ≤ schattenNorm q A :=
          (singularValues_le_specNorm A i).trans (specNorm_le_schattenNorm_of_ne_top hq hq' A)
        calc singularValues A i ^ r.toReal
            = singularValues A i ^ (r.toReal - q.toReal) * singularValues A i ^ q.toReal := by
              rw [← Real.rpow_add_of_nonneg (singularValues_nonneg A i) hqr hq0.le,
                sub_add_cancel]
          _ ≤ schattenNorm q A ^ (r.toReal - q.toReal) * singularValues A i ^ q.toReal :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (singularValues_nonneg A i) hi hqr)
                (Real.rpow_nonneg (singularValues_nonneg A i) _)
    _ = schattenNorm q A ^ r.toReal := by
        rw [← Finset.mul_sum, ← schattenNorm_rpow hq hq' A le_rfl,
          ← Real.rpow_add_of_nonneg (schattenNorm_nonneg q A) hqr hq0.le, sub_add_cancel]

/-- The spectral norm is at most every Schatten norm with `q ≠ 0`.
Port of `NLAlib.specNorm_le_schattenNormReal`. -/
theorem specNorm_le_schattenNorm {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m n 𝕜) :
    specNorm A ≤ schattenNorm q A := by
  rw [← schattenNorm_top]
  exact schattenNorm_anti hq le_top A

/-- The comparison of a Schatten norm of finite exponent with the spectral norm. -/
private theorem schattenNorm_le_rank_rpow_mul_specNorm_of_ne_top {q : ℝ≥0∞} (hq : q ≠ 0)
    (hq' : q ≠ ⊤) (A : Matrix m n 𝕜) :
    schattenNorm q A ≤ (A.rank : ℝ) ^ q.toReal⁻¹ * specNorm A := by
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos hq hq'
  have hk : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
  rw [← Real.rpow_le_rpow_iff (schattenNorm_nonneg q A)
    (mul_nonneg (Real.rpow_nonneg hk _) (specNorm_nonneg A)) hq0,
    Real.mul_rpow (Real.rpow_nonneg hk _) (specNorm_nonneg A), Real.rpow_inv_rpow hk hq0.ne',
    schattenNorm_rpow hq hq' A le_rfl]
  calc ∑ i ∈ Finset.range A.rank, singularValues A i ^ q.toReal
      ≤ ∑ _i ∈ Finset.range A.rank, specNorm A ^ q.toReal :=
        Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (singularValues_nonneg A i)
          (singularValues_le_specNorm A i) hq0.le
    _ = (A.rank : ℝ) * specNorm A ^ q.toReal := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Comparison in the other direction, with the rank: for `q ≤ r`,
`‖A‖_q ≤ rank(A) ^ (1/q - 1/r) ‖A‖_r`.
Port of `NLAlib.schattenNorm_le_rank_rpow_mul`, there over `ℝ` for `1 ≤ q`. -/
theorem schattenNorm_le_rank_rpow_mul_schattenNorm {q r : ℝ≥0∞} (hq : q ≠ 0) (h : q ≤ r)
    (A : Matrix m n 𝕜) :
    schattenNorm q A ≤ (A.rank : ℝ) ^ (q.toReal⁻¹ - r.toReal⁻¹) * schattenNorm r A := by
  rcases eq_or_ne q ⊤ with rfl | hq'
  · rw [top_le_iff.mp h, sub_self, Real.rpow_zero, one_mul]
  rcases eq_or_ne r ⊤ with rfl | hr'
  · rw [ENNReal.toReal_top, inv_zero, sub_zero, schattenNorm_top]
    exact schattenNorm_le_rank_rpow_mul_specNorm_of_ne_top hq hq' A
  have hr : r ≠ 0 := ((pos_iff_ne_zero.mpr hq).trans_le h).ne'
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos hq hq'
  have hr0 : 0 < r.toReal := ENNReal.toReal_pos hr hr'
  have hk : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
  have h1 := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (Finset.range A.rank)
    (p := r.toReal / q.toReal) (f := fun i => singularValues A i ^ q.toReal)
    ((one_le_div hq0).mpr (ENNReal.toReal_mono hr' h))
    fun i _ => Real.rpow_nonneg (singularValues_nonneg A i) _
  have h2 : q.toReal * (r.toReal / q.toReal) = r.toReal := by field_simp
  have h3 : (q.toReal⁻¹ - r.toReal⁻¹) * r.toReal = r.toReal / q.toReal - 1 := by field_simp
  rw [← schattenNorm_rpow hq hq' A le_rfl, ← Real.rpow_mul (schattenNorm_nonneg q A), h2,
    Finset.card_range] at h1
  rw [← Real.rpow_le_rpow_iff (schattenNorm_nonneg q A)
    (mul_nonneg (Real.rpow_nonneg hk _) (schattenNorm_nonneg r A)) hr0,
    Real.mul_rpow (Real.rpow_nonneg hk _) (schattenNorm_nonneg r A), ← Real.rpow_mul hk, h3,
    schattenNorm_rpow hr hr' A le_rfl]
  refine h1.trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Real.rpow_mul (singularValues_nonneg A i), h2]

/-- `‖A‖_q ≤ rank(A) ^ (1/q) ‖A‖₂`.
Port of `NLAlib.schattenNormReal_le_rank_rpow_mul_specNorm`. -/
theorem schattenNorm_le_rank_rpow_mul_specNorm {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m n 𝕜) :
    schattenNorm q A ≤ (A.rank : ℝ) ^ q.toReal⁻¹ * specNorm A := by
  have h := schattenNorm_le_rank_rpow_mul_schattenNorm hq le_top A
  rwa [ENNReal.toReal_top, inv_zero, sub_zero, schattenNorm_top] at h

/-! ### Products with a spectral-norm factor -/

/-- `‖A B‖_q ≤ ‖A‖₂ ‖B‖_q`.
Port of `NLAlib.schattenNormReal_mul_le_specNorm_mul`, there over `ℝ`. -/
theorem schattenNorm_mul_le_specNorm_mul {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m p 𝕜)
    (B : Matrix p n 𝕜) : schattenNorm q (A * B) ≤ specNorm A * schattenNorm q B := by
  exact schattenNorm_le_mul_of_singularValues_le hq (specNorm_nonneg A) fun i =>
    singularValues_mul_le_specNorm_mul A B i

/-- `‖A B‖_q ≤ ‖A‖_q ‖B‖₂`.
Port of `NLAlib.schattenNormReal_mul_le_mul_specNorm`, there over `ℝ`. -/
theorem schattenNorm_mul_le_mul_specNorm {q : ℝ≥0∞} (hq : q ≠ 0) (A : Matrix m p 𝕜)
    (B : Matrix p n 𝕜) : schattenNorm q (A * B) ≤ schattenNorm q A * specNorm B := by
  rw [mul_comm]
  exact schattenNorm_le_mul_of_singularValues_le hq (specNorm_nonneg B) fun i =>
    (singularValues_mul_le_mul_specNorm A B i).trans_eq (mul_comm _ _)

end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `NLAlib.schattenNorm q A` is nonnegative. -/
@[positivity NLAlib.schattenNorm _ _]
meta def evalSchattenNorm : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    let pf ← mkAppM ``NLAlib.schattenNorm_nonneg #[e.appFn!.appArg!, e.appArg!]
    pure (.nonnegative pf)

end Mathlib.Meta.Positivity
