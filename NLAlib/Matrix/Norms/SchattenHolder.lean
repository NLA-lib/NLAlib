/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.ENNReal.Holder
public import NLAlib.Matrix.Majorization.Horn
public import NLAlib.Matrix.Norms.Schatten

/-!
# Hölder's inequality and duality for Schatten norms

For exponents with `1/q + 1/r = 1/s`, `‖A B‖_s ≤ ‖A‖_q ‖B‖_r`; for conjugate exponents,
`|tr (Aᴴ B)| ≤ ‖A‖_q ‖B‖_r`, with equality attained, so the Schatten `q`-norm is the dual of the
Schatten `r`-norm under the Frobenius inner product. Exponent relations are Mathlib's
`ENNReal.HolderTriple` and `ENNReal.HolderConjugate`.

## Main results

* `NLAlib.schattenNorm_mul_le`: Hölder's inequality for products.
* `NLAlib.norm_trace_conjTranspose_mul_le_schattenNorm_mul`: Hölder's inequality for the trace.
* `NLAlib.isGreatest_frobInner_schattenNorm`: duality.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-- **Hölder's inequality for Schatten norms.** If `1/q + 1/r = 1/s` with `q, r ≠ 0`, then
`‖A B‖_s ≤ ‖A‖_q ‖B‖_r`.
[HornJohnson1991, Theorem 3.3.14]; [Bhatia1997, Exercise IV.2.7].
Port of `NLAlib.schattenNorm_mul_le_mul`, there over `ℝ` for exponents at least one.
Result: schatten-holder -/
theorem schattenNorm_mul_le {q r s : ℝ≥0∞} [ENNReal.HolderTriple q r s] (hq : q ≠ 0)
    (hr : r ≠ 0) (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    schattenNorm s (A * B) ≤ schattenNorm q A * schattenNorm r B := by
  rcases eq_or_ne q ⊤ with rfl | hq'
  · obtain rfl : r = s := ENNReal.HolderTriple.unique ⊤ r r s
    rw [schattenNorm_top]
    exact schattenNorm_mul_le_specNorm_mul hr A B
  rcases eq_or_ne r ⊤ with rfl | hr'
  · obtain rfl : q = s := ENNReal.HolderTriple.unique q ⊤ q s
    rw [schattenNorm_top]
    exact schattenNorm_mul_le_mul_specNorm hq A B
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos hq hq'
  have hr0 : 0 < r.toReal := ENNReal.toReal_pos hr hr'
  have hT : q.toReal.HolderTriple r.toReal s.toReal := ENNReal.HolderTriple.toReal s hq0 hr0
  obtain ⟨hs, hs'⟩ := ENNReal.toReal_pos_iff.mp hT.pos'
  have hNA : A.rank ≤ max (A * B).rank (max A.rank B.rank) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hNB : B.rank ≤ max (A * B).rank (max A.rank B.rank) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hA : schattenNorm q A ^ s.toReal =
      (∑ i ∈ Finset.range (max (A * B).rank (max A.rank B.rank)),
        singularValues A i ^ q.toReal) ^ (s.toReal / q.toReal) := by
    rw [← schattenNorm_rpow hq hq' A hNA, ← Real.rpow_mul (schattenNorm_nonneg q A),
      mul_div_cancel₀ _ hq0.ne']
  have hB : schattenNorm r B ^ s.toReal =
      (∑ i ∈ Finset.range (max (A * B).rank (max A.rank B.rank)),
        singularValues B i ^ r.toReal) ^ (s.toReal / r.toReal) := by
    rw [← schattenNorm_rpow hr hr' B hNB, ← Real.rpow_mul (schattenNorm_nonneg r B),
      mul_div_cancel₀ _ hr0.ne']
  rw [← Real.rpow_le_rpow_iff (schattenNorm_nonneg s _)
    (mul_nonneg (schattenNorm_nonneg q A) (schattenNorm_nonneg r B)) hT.pos',
    schattenNorm_rpow hs.ne' hs'.ne (A * B) (le_max_left _ _),
    Real.mul_rpow (schattenNorm_nonneg q A) (schattenNorm_nonneg r B), hA, hB]
  exact (sum_range_singularValues_mul_rpow_le A B _ hT.pos').trans
    (Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg _ hT (fun i _ => singularValues_nonneg A i)
      fun i _ => singularValues_nonneg B i)

/-- **Hölder's inequality for the trace.** For conjugate exponents,
`|tr (Aᴴ B)| ≤ ‖A‖_q ‖B‖_r`.
[Bhatia1997, Corollary IV.2.6].
Port of `NLAlib.abs_frobInner_le_schattenNorm_mul`, there over `ℝ` for the real part.
Result: schatten-holder -/
theorem norm_trace_conjTranspose_mul_le_schattenNorm_mul {q r : ℝ≥0∞}
    [ENNReal.HolderConjugate q r] (A B : Matrix m n 𝕜) :
    ‖(Aᴴ * B).trace‖ ≤ schattenNorm q A * schattenNorm r B := by
  rcases eq_or_ne q ⊤ with rfl | hq'
  · obtain rfl : r = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ r).mp rfl
    have h := norm_trace_conjTranspose_mul_le_nuclearNorm_mul_specNorm B A
    rwa [show Bᴴ * A = (Aᴴ * B)ᴴ by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose],
      Matrix.trace_conjTranspose, norm_star, mul_comm, ← schattenNorm_top,
      ← schattenNorm_one] at h
  rcases eq_or_ne r ⊤ with rfl | hr'
  · obtain rfl : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ q).mp rfl
    rw [schattenNorm_top, schattenNorm_one]
    exact norm_trace_conjTranspose_mul_le_nuclearNorm_mul_specNorm A B
  have hN : ∀ C : Matrix m n 𝕜, C.rank ≤ min (Fintype.card m) (Fintype.card n) := fun C =>
    le_min C.rank_le_card_height C.rank_le_card_width
  refine (norm_trace_conjTranspose_mul_le_sum_singularValues_mul A B).trans ?_
  rw [schattenNorm_eq_sum_rpow (ENNReal.HolderConjugate.ne_zero q r) hq' A (hN A),
    schattenNorm_eq_sum_rpow (ENNReal.HolderConjugate.ne_zero r q) hr' B (hN B), ← one_div,
    ← one_div]
  exact Real.inner_le_Lp_mul_Lq_of_nonneg _ (ENNReal.HolderConjugate.toReal_of_ne_top hq' hr')
    (fun i _ => singularValues_nonneg A i) fun i _ => singularValues_nonneg B i

/-- Hölder's inequality for the trace of a product `A * B` with `B` of the transposed shape. -/
theorem norm_trace_mul_le_schattenNorm_mul {q r : ℝ≥0∞} [ENNReal.HolderConjugate q r]
    (A : Matrix m n 𝕜) (B : Matrix n m 𝕜) :
    ‖(A * B).trace‖ ≤ schattenNorm q A * schattenNorm r B := by
  have h := norm_trace_conjTranspose_mul_le_schattenNorm_mul (q := q) (r := r) Aᴴ B
  rwa [Matrix.conjTranspose_conjTranspose, schattenNorm_conjTranspose] at h

/-- Hölder's inequality for the Frobenius inner product: `|⟨A, B⟩_F| ≤ ‖A‖_q ‖B‖_r`.
Port of `NLAlib.abs_frobInner_le_schattenNorm_mul`, there over `ℝ`. -/
theorem abs_frobInner_le_schattenNorm_mul {q r : ℝ≥0∞} [ENNReal.HolderConjugate q r]
    (A B : Matrix m n 𝕜) : |frobInner A B| ≤ schattenNorm q A * schattenNorm r B := by
  exact (RCLike.abs_re_le_norm _).trans (norm_trace_conjTranspose_mul_le_schattenNorm_mul A B)

/-- Attainment in Hölder's inequality for finite conjugate exponents: with a thin singular value
decomposition `A = U diag(σ) Vᴴ`, the matrix `U diag(σ_i^(q-1) / ‖A‖_q^(q-1)) Vᴴ` has Schatten
`r`-norm one and pairs with `A` to `‖A‖_q`. -/
private theorem exists_schattenNorm_le_one_frobInner_eq_of_ne_top {q r : ℝ≥0∞}
    [ENNReal.HolderConjugate q r] (hq : q ≠ ⊤) (hr : r ≠ ⊤) (A : Matrix m n 𝕜) :
    ∃ B : Matrix m n 𝕜, schattenNorm r B ≤ 1 ∧ frobInner A B = schattenNorm q A := by
  classical
  rcases eq_or_ne A 0 with rfl | hA
  · exact ⟨0, (schattenNorm_zero r).trans_le zero_le_one,
      (frobInner_zero_left 0).trans (schattenNorm_zero q).symm⟩
  have hpq : q.toReal.HolderConjugate r.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hq hr
  have hq0 : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q r
  have hN : ∀ C : Matrix m n 𝕜, C.rank ≤ min (Fintype.card m) (Fintype.card n) := fun C =>
    le_min C.rank_le_card_height C.rank_le_card_width
  obtain ⟨U, V, hSVD⟩ := exists_isSVD A (hN A) (min_le_left _ _) (min_le_right _ _)
  have hc : 0 < schattenNorm q A :=
    (schattenNorm_nonneg q A).lt_of_ne' (mt (schattenNorm_eq_zero_iff q).mp hA)
  have hσ : ∀ i, 0 ≤ singularValues A i := singularValues_nonneg A
  obtain ⟨d, hd⟩ : ∃ d : Fin (min (Fintype.card m) (Fintype.card n)) → ℝ, ∀ i, d i =
      singularValues A i ^ (q.toReal - 1) / schattenNorm q A ^ (q.toReal - 1) :=
    ⟨_, fun _ => rfl⟩
  have hd0 : ∀ i, 0 ≤ d i := fun i => by
    rw [hd]
    exact div_nonneg (Real.rpow_nonneg (hσ i) _) (Real.rpow_nonneg hc.le _)
  have hda : Antitone d := fun i j hij => by
    rw [hd, hd]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (hσ j)
      (singularValues_antitone A (Fin.le_iff_val_le_val.mp hij)) hpq.sub_one_pos.le)
      (Real.rpow_nonneg hc.le _)
  have hB : IsSVD (U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Vᴴ) U d V :=
    ⟨hSVD.hasOrthonormalCols_left, hSVD.hasOrthonormalCols_right, hd0, rfl⟩
  have hsum : ∑ i : Fin (min (Fintype.card m) (Fintype.card n)),
      singularValues A i ^ q.toReal = schattenNorm q A ^ q.toReal := by
    rw [Fin.sum_univ_eq_sum_range fun i => singularValues A i ^ q.toReal,
      ← schattenNorm_rpow hq0 hq A (hN A)]
  refine ⟨U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Vᴴ, le_of_eq ?_, ?_⟩
  · have hi : ∀ i : Fin (min (Fintype.card m) (Fintype.card n)),
        singularValues (U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Vᴴ) i ^ r.toReal =
          singularValues A i ^ q.toReal / schattenNorm q A ^ q.toReal := fun i => by
      rw [hB.singularValues_eq hda i, hd, Real.div_rpow (Real.rpow_nonneg (hσ i) _)
        (Real.rpow_nonneg hc.le _), ← Real.rpow_mul (hσ i), ← Real.rpow_mul hc.le,
        hpq.sub_one_mul_conj]
    rw [schattenNorm_eq_sum_rpow (ENNReal.HolderConjugate.ne_zero r q) hr _ (hN _),
      ← Fin.sum_univ_eq_sum_range fun i =>
        singularValues (U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Vᴴ) i ^ r.toReal,
      Finset.sum_congr rfl fun i _ => hi i, ← Finset.sum_div, hsum,
      div_self (Real.rpow_pos_of_pos hc _).ne', Real.one_rpow]
  · have hi : ∀ i : Fin (min (Fintype.card m) (Fintype.card n)), singularValues A i * d i =
        singularValues A i ^ q.toReal / schattenNorm q A ^ (q.toReal - 1) := fun i => by
      rw [hd, ← mul_div_assoc]
      congr 1
      nth_rewrite 1 [← Real.rpow_one (singularValues A i)]
      rw [← Real.rpow_add_of_nonneg (hσ i) zero_le_one hpq.sub_one_pos.le, add_sub_cancel]
    rw [hSVD.frobInner_eq hB, Finset.sum_congr rfl fun i _ => hi i, ← Finset.sum_div, hsum,
      Real.rpow_sub_one hc.ne']
    exact div_div_cancel₀ (Real.rpow_pos_of_pos hc _).ne'

/-- Equality in Hölder's inequality is attained: there is `B` in the unit ball of the Schatten
`r`-norm with `⟨A, B⟩_F = ‖A‖_q`.
Port of `NLAlib.exists_schattenNorm_le_one_frobInner_eq`, there over `ℝ`. -/
theorem exists_schattenNorm_le_one_frobInner_eq {q r : ℝ≥0∞} [ENNReal.HolderConjugate q r]
    (A : Matrix m n 𝕜) :
    ∃ B : Matrix m n 𝕜, schattenNorm r B ≤ 1 ∧ frobInner A B = schattenNorm q A := by
  rcases eq_or_ne q ⊤ with rfl | hq
  · obtain rfl : r = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ r).mp rfl
    simp only [schattenNorm_top, schattenNorm_one]
    exact (isGreatest_frobInner_specNorm A).1
  rcases eq_or_ne r ⊤ with rfl | hr
  · obtain rfl : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ q).mp rfl
    simp only [schattenNorm_top, schattenNorm_one]
    exact exists_specNorm_le_one_frobInner_eq_nuclearNorm A
  · exact exists_schattenNorm_le_one_frobInner_eq_of_ne_top hq hr A

/-- **Duality of Schatten norms.** For conjugate exponents, the Schatten `q`-norm is the largest
Frobenius inner product with a matrix in the unit ball of the Schatten `r`-norm.
[Bhatia1997, §IV.2]. Port of `NLAlib.isGreatest_schattenNorm_frobInner`, there over `ℝ`.
Result: schatten-duality -/
theorem isGreatest_frobInner_schattenNorm {q r : ℝ≥0∞} [ENNReal.HolderConjugate q r]
    (A : Matrix m n 𝕜) :
    IsGreatest ((fun B : Matrix m n 𝕜 => frobInner A B) '' {B | schattenNorm r B ≤ 1})
      (schattenNorm q A) := by
  refine ⟨exists_schattenNorm_le_one_frobInner_eq A, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  exact (le_abs_self _).trans ((abs_frobInner_le_schattenNorm_mul A B).trans
    (mul_le_of_le_one_right (schattenNorm_nonneg q A) hB))

end NLAlib
