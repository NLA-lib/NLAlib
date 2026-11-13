/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Matrix.Order
public import NLAlib.Matrix.Norms.Frobenius
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# Capacity of a positive matrix map

Capacity is the infimum of the normalized determinant objective. Invertible input and output
scalings multiply it by squared determinant moduli.

## Main results

* `NLAlib.operatorCapacity_congruence_scaling`.
* `NLAlib.krausMap`.
-/
@[expose] public section

open Matrix

open scoped ComplexOrder

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive real rescaling factor that normalizes a complex positive definite matrix
to determinant one: the inverse of the `card n`-th determinant root of the real part
of the determinant. -/
private noncomputable def detNormalizeScaling (X : Matrix n n ℂ) : ℝ :=
  (X.det.re ^ (1 / (Fintype.card n : ℝ)))⁻¹

/-- The rescaling factor in `detNormalizeScaling` is positive. -/
private theorem _root_.Matrix.PosDef.detNormalizeScaling_pos {X : Matrix n n ℂ} (hX : X.PosDef) :
    0 < detNormalizeScaling X := by
  unfold detNormalizeScaling
  exact inv_pos.mpr (Real.rpow_pos_of_pos (Complex.pos_iff.mp hX.det_pos).1 _)

private theorem det_normalize_scaling_pow_card (X : Matrix n n ℂ) (hX : X.PosDef)
    (hN : 0 < Fintype.card n) :
    detNormalizeScaling X ^ Fintype.card n = (X.det.re)⁻¹ := by
  have hre_pos : 0 < X.det.re := (Complex.pos_iff.mp hX.det_pos).1
  have hN_ne : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  unfold detNormalizeScaling
  rw [inv_pow]
  congr 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hre_pos.le]
  rw [one_div_mul_cancel hN_ne, Real.rpow_one]

/-- Rescaling a complex positive definite matrix by `detNormalizeScaling` yields
determinant exactly one. -/
private theorem _root_.Matrix.PosDef.det_smul_detNormalizeScaling_eq_one
    {X : Matrix n n ℂ} (hX : X.PosDef)
    (hN : 0 < Fintype.card n) :
    (detNormalizeScaling X • X).det = 1 := by
  have hre_pos : 0 < X.det.re := (Complex.pos_iff.mp hX.det_pos).1
  have hpow_card : detNormalizeScaling X ^ Fintype.card n = (X.det.re)⁻¹ :=
    det_normalize_scaling_pow_card X hX hN
  have hre_smul (r : ℝ) (z : ℂ) : (r • z).re = r * z.re := by
    rw [Algebra.smul_def]
    exact Complex.re_ofReal_mul r z
  have him_smul (r : ℝ) (z : ℂ) : (r • z).im = r * z.im := by
    rw [Algebra.smul_def]
    exact Complex.im_ofReal_mul r z
  apply Complex.ext
  · rw [Matrix.det_smul_of_tower, hpow_card, hre_smul]
    rw [inv_mul_cancel₀ (ne_of_gt hre_pos)]
    rfl
  · rw [Matrix.det_smul_of_tower, hpow_card, him_smul]
    rw [(Complex.pos_iff.mp hX.det_pos).2.symm]
    simp

/-- Normalization bridge for determinant-ratio objectives: for every positive definite
`X` and every `ℝ`-linear map `T`, there is a determinant-one positive definite matrix
`Y` (namely `detNormalizeScaling X • X`) with
`(T Y).det.re = (T X).det.re / X.det.re`. -/
private theorem _root_.Matrix.PosDef.exists_det_eq_one_re_det_map_eq_div
    {X : Matrix n n ℂ} (hX : X.PosDef)
    (hN : 0 < Fintype.card n) (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) :
    ∃ Y, Y.PosDef ∧ Y.det = 1 ∧ (T Y).det.re = (T X).det.re / X.det.re := by
  refine ⟨detNormalizeScaling X • X, ?_, ?_, ?_⟩
  · exact hX.smul (hX.detNormalizeScaling_pos)
  · exact hX.det_smul_detNormalizeScaling_eq_one hN
  · have hpow_card : detNormalizeScaling X ^ Fintype.card n = (X.det.re)⁻¹ :=
      det_normalize_scaling_pow_card X hX hN
    have hre_smul (r : ℝ) (z : ℂ) : (r • z).re = r * z.re := by
      rw [Algebra.smul_def]
      exact Complex.re_ofReal_mul r z
    rw [T.map_smul]
    rw [Matrix.det_smul_of_tower]
    rw [hpow_card, hre_smul]
    rw [div_eq_inv_mul, mul_comm]

/-- The set of attainable real determinant-ratio objectives over positive definite
matrices equals the set of attainable objectives over determinant-one matrices.
The forward direction reads the ratio off a determinant-one witness; the backward
direction restores determinant one by rescaling. -/
private theorem detRatio_attainable_sets_eq (hN : 0 < Fintype.card n)
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) :
    {d : ℝ | ∃ X, X.PosDef ∧ X.det = 1 ∧ d = (T X).det.re} =
      {d : ℝ | ∃ X, X.PosDef ∧ d = (T X).det.re / X.det.re} := by
  ext d
  constructor
  · rintro ⟨X, hX, hXdet, rfl⟩
    refine ⟨X, hX, ?_⟩
    have hXdet_re : X.det.re = 1 := by rw [hXdet]; simp
    rw [hXdet_re]
    simp
  · rintro ⟨X, hX, hd⟩
    rcases hX.exists_det_eq_one_re_det_map_eq_div hN T with ⟨Y, hY, hYdet, hYT⟩
    refine ⟨Y, hY, hYdet, ?_⟩
    rw [hd, hYT]


end NLAlib

open scoped ComplexOrder MatrixOrder ComplexConjugate

open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The operator capacity of a real-linear map `T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ`:
the infimum of `(T X).det.re` over positive definite `X` with determinant `1`.
The objective set is always nonempty. For maps preserving positive semidefiniteness,
it is bounded below by zero; `sInf` is otherwise the total real infimum operation. -/
noncomputable def operatorCapacity (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) : ℝ :=
  sInf {d : ℝ | ∃ X : Matrix n n ℂ, X.PosDef ∧ X.det = 1 ∧ d = (T X).det.re}

/-- The objective set of `operatorCapacity` is nonempty: `X = 1` is positive definite with
determinant `1`. -/
theorem operatorCapacity_attainable_nonempty (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) :
    ({d : ℝ | ∃ X : Matrix n n ℂ, X.PosDef ∧ X.det = 1 ∧ d = (T X).det.re}).Nonempty := by
  refine ⟨(T (1 : Matrix n n ℂ)).det.re, 1, Matrix.PosDef.one, Matrix.det_one, rfl⟩

/-- Under the positivity hypothesis `hT`, the objective set of `operatorCapacity` is bounded
below by `0`. -/
theorem operatorCapacity_attainable_bddBelow
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef) :
    BddBelow {d : ℝ | ∃ X : Matrix n n ℂ, X.PosDef ∧ X.det = 1 ∧ d = (T X).det.re} := by
  refine ⟨0, ?_⟩
  rintro d ⟨X, hX, -, rfl⟩
  exact (Complex.nonneg_iff.mp (Matrix.PosSemidef.det_nonneg (hT X hX.posSemidef))).1

/-- `operatorCapacity` is nonnegative under the positivity hypothesis `hT`. -/
theorem operatorCapacity_nonneg (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef) :
    0 ≤ operatorCapacity T := by
  unfold operatorCapacity
  exact le_csInf (operatorCapacity_attainable_nonempty T)
    (by
      rintro d ⟨X, hX, -, rfl⟩
      exact (Complex.nonneg_iff.mp (Matrix.PosSemidef.det_nonneg (hT X hX.posSemidef))).1)

/-- The capacity is the infimum of the determinant-ratio objective
`(T X).det.re / X.det.re` over all positive definite $\mathbf{X}$. -/
theorem operatorCapacity_eq_sInf_ratio (hN : 0 < Fintype.card n)
    (T : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ) :
    operatorCapacity T =
      sInf {d : ℝ | ∃ X : Matrix n n ℂ, X.PosDef ∧ d = (T X).det.re / X.det.re} := by
  unfold operatorCapacity
  rw [detRatio_attainable_sets_eq hN T]

/-- Determinant of a matrix congruence: `det (U * X * U†) = det U * det X * star (det U)`. -/
private theorem det_congr_mul_conjTranspose (U X : Matrix n n ℂ) :
    (U * X * U.conjTranspose).det = det U * X.det * star (det U) := by
  calc
    (U * X * U.conjTranspose).det = det (U * X) * det (U.conjTranspose) := by
      rw [Matrix.det_mul]
    _ = det U * X.det * star (det U) := by
      rw [Matrix.det_mul, Matrix.det_conjTranspose]

/-- The determinant of a congruence by `U` is `Complex.normSq (det U)` times the determinant
(the scalar `Complex.normSq (det U)` is real, coerced to `ℂ`). -/
private theorem det_congr_mul_conjTranspose_normSq (U X : Matrix n n ℂ) :
    (U * X * U.conjTranspose).det = (Complex.normSq (det U) : ℂ) * X.det := by
  rw [det_congr_mul_conjTranspose]
  have hns : (Complex.normSq (det U) : ℂ) = (starRingEnd ℂ) (det U) * det U :=
    Complex.normSq_eq_conj_mul_self
  rw [hns]
  simp_rw [Complex.star_def]
  ring

/-- Congruence multiplies the real determinant by the squared modulus of the basis determinant. -/
private theorem det_re_congr_mul_conjTranspose_normSq (U X : Matrix n n ℂ) :
    (U * X * U.conjTranspose).det.re = Complex.normSq (det U) * X.det.re := by
  rw [det_congr_mul_conjTranspose_normSq U X]
  exact Complex.re_ofReal_mul (Complex.normSq (det U)) X.det

/-- Under the pointwise congruence identity `S X = B * T (C * X * C†) * B†`, the real part
of the determinant of `S X` is `normSq (det B)` times that of `T (C * X * C†)`. -/
private theorem re_det_map_congr (T S : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (B C : Matrix n n ℂ) (hS : ∀ X, S X = B * T (C * X * C.conjTranspose) * B.conjTranspose)
    (X : Matrix n n ℂ) :
    (S X).det.re = Complex.normSq (det B) * (T (C * X * C.conjTranspose)).det.re := by
  calc
    (S X).det.re = (B * T (C * X * C.conjTranspose) * B.conjTranspose).det.re := by
      rw [hS X]
    _ = (det B * (T (C * X * C.conjTranspose)).det * star (det B)).re := by
      congr 1
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    _ = ((Complex.normSq (det B) : ℂ) * (T (C * X * C.conjTranspose)).det).re := by
      congr 1
      have hns : (Complex.normSq (det B) : ℂ) = (starRingEnd ℂ) (det B) * det B :=
        Complex.normSq_eq_conj_mul_self
      rw [hns]
      simp_rw [Complex.star_def]
      ring
    _ = Complex.normSq (det B) * (T (C * X * C.conjTranspose)).det.re := by
      exact Complex.re_ofReal_mul (Complex.normSq (det B)) (T (C * X * C.conjTranspose)).det

/-- Normalized determinant-ratio identity for the forward congruence: for positive definite
`X`, writing `Y = C * X * C†`,

`(S X).det.re / X.det.re = normSq (det B) * normSq (det C) * ((T Y).det.re / Y.det.re)`.
-/
private theorem ratio_eq_scaled (B C X : Matrix n n ℂ)
    (T S : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hC : IsUnit C)
    (hS : ∀ X, S X = B * T (C * X * C.conjTranspose) * B.conjTranspose)
    (hX : X.PosDef) :
    (S X).det.re / X.det.re =
      (Complex.normSq (det B) * Complex.normSq (det C)) *
        ((T (C * X * C.conjTranspose)).det.re / (C * X * C.conjTranspose).det.re) := by
  have hCdet_ne : det C ≠ 0 := (Matrix.isUnit_iff_isUnit_det C).mp hC |>.ne_zero
  have hCnsq_pos : 0 < Complex.normSq (det C) := Complex.normSq_pos.2 hCdet_ne
  have hCnsq_ne : Complex.normSq (det C) ≠ 0 := ne_of_gt hCnsq_pos
  have hXdet_re_pos : 0 < X.det.re := (Complex.pos_iff.mp hX.det_pos).1
  have hXdet_re_ne : X.det.re ≠ 0 := ne_of_gt hXdet_re_pos
  have hYdet := det_re_congr_mul_conjTranspose_normSq C X
  have hYdet_re_ne : (C * X * C.conjTranspose).det.re ≠ 0 := by
    rw [hYdet]
    exact ne_of_gt (mul_pos hCnsq_pos hXdet_re_pos)
  have hv : (S X).det.re = Complex.normSq (det B) * (T (C * X * C.conjTranspose)).det.re :=
    re_det_map_congr T S B C hS X
  calc
    (S X).det.re / X.det.re
        = (Complex.normSq (det B) * (T (C * X * C.conjTranspose)).det.re) / X.det.re := by
          rw [hv]
    _ = Complex.normSq (det B) * ((T (C * X * C.conjTranspose)).det.re / X.det.re) := by
          ring
    _ = Complex.normSq (det B) * (Complex.normSq (det C) *
          ((T (C * X * C.conjTranspose)).det.re / (C * X * C.conjTranspose).det.re)) := by
          rw [hYdet]
          have hfrac :
              (T (C * X * C.conjTranspose)).det.re / X.det.re =
                Complex.normSq (det C) *
                  ((T (C * X * C.conjTranspose)).det.re /
                    (Complex.normSq (det C) * X.det.re)) := by
            field_simp [hXdet_re_ne, hCnsq_ne]
          rw [hfrac]
    _ = (Complex.normSq (det B) * Complex.normSq (det C)) *
          ((T (C * X * C.conjTranspose)).det.re / (C * X * C.conjTranspose).det.re) := by
          ring

/-- Normalized determinant-ratio identity for the inverse congruence: for positive definite
`Y` and `X = C⁻¹ * Y * (C⁻¹)†`,

`normSq (det B) * normSq (det C) * ((T Y).det.re / Y.det.re) = (S X).det.re / X.det.re`.
-/
private theorem ratio_eq_scaled_preimage (B C Y : Matrix n n ℂ)
    (T S : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hC : IsUnit C)
    (hS : ∀ X, S X = B * T (C * X * C.conjTranspose) * B.conjTranspose)
    (hY : Y.PosDef) :
    (Complex.normSq (det B) * Complex.normSq (det C)) * ((T Y).det.re / Y.det.re) =
      (S (C⁻¹ * Y * (C⁻¹).conjTranspose)).det.re /
        (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re := by
  have hCdet_ne : det C ≠ 0 := (Matrix.isUnit_iff_isUnit_det C).mp hC |>.ne_zero
  have hCnsq_pos : 0 < Complex.normSq (det C) := Complex.normSq_pos.2 hCdet_ne
  have hCnsq_ne : Complex.normSq (det C) ≠ 0 := ne_of_gt hCnsq_pos
  have hCinv : IsUnit C⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 hC
  have hX : (C⁻¹ * Y * (C⁻¹).conjTranspose).PosDef := by
    simpa [Matrix.star_eq_conjTranspose] using (hCinv.posDef_star_right_conjugate_iff).mpr hY
  have hXdet_re_pos : 0 < (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re :=
    (Complex.pos_iff.mp hX.det_pos).1
  have hXdet_re_ne : (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re ≠ 0 := ne_of_gt hXdet_re_pos
  have hCong : C * (C⁻¹ * Y * (C⁻¹).conjTranspose) * C.conjTranspose = Y := by
    have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC
    calc
      C * (C⁻¹ * Y * (C⁻¹).conjTranspose) * C.conjTranspose
          = (C * C⁻¹) * Y * ((C⁻¹).conjTranspose * C.conjTranspose) := by
            simp [Matrix.mul_assoc]
      _ = (C * C⁻¹) * Y * (C * C⁻¹).conjTranspose := by
            rw [← Matrix.conjTranspose_mul]
      _ = Y := by
            rw [Matrix.mul_nonsing_inv C hCdet]
            simp
  have hYdet : Y.det.re = Complex.normSq (det C) * (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re := by
    calc
      Y.det.re = (C * (C⁻¹ * Y * (C⁻¹).conjTranspose) * C.conjTranspose).det.re := by
        conv_lhs => rw [← hCong]
      _ = Complex.normSq (det C) * (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re :=
        det_re_congr_mul_conjTranspose_normSq C (C⁻¹ * Y * (C⁻¹).conjTranspose)
  have hYdet_re_ne : Y.det.re ≠ 0 := by
    rw [hYdet]
    exact ne_of_gt (mul_pos hCnsq_pos hXdet_re_pos)
  have hv : (S (C⁻¹ * Y * (C⁻¹).conjTranspose)).det.re =
      Complex.normSq (det B) * (T Y).det.re := by
    rw [re_det_map_congr T S B C hS (C⁻¹ * Y * (C⁻¹).conjTranspose)]
    rw [hCong]
  calc
    (Complex.normSq (det B) * Complex.normSq (det C)) * ((T Y).det.re / Y.det.re)
        = Complex.normSq (det B) * (Complex.normSq (det C) * ((T Y).det.re / Y.det.re)) := by
          ring
    _ = Complex.normSq (det B) * ((T Y).det.re / (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re) := by
          have hfrac :
              Complex.normSq (det C) * ((T Y).det.re / Y.det.re) =
                (T Y).det.re / (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re := by
            rw [hYdet]
            field_simp [hXdet_re_ne, hYdet_re_ne, hCnsq_ne]
          rw [hfrac]
    _ = (Complex.normSq (det B) * (T Y).det.re) / (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re := by
          ring
    _ = (S (C⁻¹ * Y * (C⁻¹).conjTranspose)).det.re /
          (C⁻¹ * Y * (C⁻¹).conjTranspose).det.re := by
          rw [hv]

/-- **Operator capacity under invertible scaling.** For a positive real-linear map on
complex $n$ by $n$ matrices, $n>0$, scale the map $\Phi$ by invertible matrices
$\mathbf{B},\mathbf{C}$ to obtain
$$\Psi(\mathbf{X})=\mathbf{B}\Phi(\mathbf{C}\mathbf{X}\mathbf{C}^{\mathsf{H}})
\mathbf{B}^{\mathsf{H}}.$$
Then $\operatorname{cap}(\Psi)=\lvert\det\mathbf{B}\rvert^2
\lvert\det\mathbf{C}\rvert^2\operatorname{cap}(\Phi)$.
This includes maps of zero capacity. [GargGurvitsOliveiraWigderson2015, Proposition 2.7],
extended from completely positive maps to positive real-linear maps.
Result: operator-capacity-scaling-identities -/
theorem operatorCapacity_congruence_scaling (hN : 0 < Fintype.card n)
    (T S : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
    (hT : ∀ X, X.PosSemidef → (T X).PosSemidef)
    (B C : Matrix n n ℂ) (hB : IsUnit B) (hC : IsUnit C)
    (hS : ∀ X, S X = B * T (C * X * C.conjTranspose) * B.conjTranspose) :
    operatorCapacity S = Complex.normSq (det B) * Complex.normSq (det C) * operatorCapacity T := by
  let A : Set ℝ := {d | ∃ X : Matrix n n ℂ, X.PosDef ∧ d = (T X).det.re / X.det.re}
  let A' : Set ℝ := {d | ∃ X : Matrix n n ℂ, X.PosDef ∧ d = (S X).det.re / X.det.re}
  let a : ℝ := Complex.normSq (det B) * Complex.normSq (det C)
  have hBdet_ne : det B ≠ 0 := (Matrix.isUnit_iff_isUnit_det B).mp hB |>.ne_zero
  have hCdet_ne : det C ≠ 0 := (Matrix.isUnit_iff_isUnit_det C).mp hC |>.ne_zero
  have ha_pos : 0 < a := by
    exact mul_pos (Complex.normSq_pos.2 hBdet_ne) (Complex.normSq_pos.2 hCdet_ne)
  let e : ℝ ≃o ℝ := OrderIso.mulLeft₀ a ha_pos
  have hTcap : operatorCapacity T = sInf A := by
    rw [operatorCapacity_eq_sInf_ratio hN T]
  have hScap : operatorCapacity S = sInf A' := by
    rw [operatorCapacity_eq_sInf_ratio hN S]
  have hAne : A.Nonempty := by
    refine ⟨((T (1 : Matrix n n ℂ)).det.re / ((1 : Matrix n n ℂ).det.re)),
      1, Matrix.PosDef.one, rfl⟩
  have hAbdd : BddBelow A := by
    refine ⟨0, ?_⟩
    rintro d ⟨X, hX, rfl⟩
    exact div_nonneg
      ((Complex.nonneg_iff.mp (Matrix.PosSemidef.det_nonneg (hT X hX.posSemidef))).1)
      ((Complex.pos_iff.mp hX.det_pos).1).le
  have hA'_eq : A' = e '' A := by
    ext d
    constructor
    · rintro ⟨X, hX, hd⟩
      refine ⟨(T (C * X * C.conjTranspose)).det.re / (C * X * C.conjTranspose).det.re,
          ⟨C * X * C.conjTranspose, ?_, rfl⟩, ?_⟩
      · simpa [Matrix.star_eq_conjTranspose] using (hC.posDef_star_right_conjugate_iff).mpr hX
      · dsimp [e]
        rw [hd]
        exact (ratio_eq_scaled B C X T S hC hS hX).symm
    · intro hmem
      rcases hmem with ⟨y, ⟨hy, hed⟩⟩
      rcases hy with ⟨Y, hY, rfl⟩
      let X : Matrix n n ℂ := C⁻¹ * Y * (C⁻¹).conjTranspose
      have hX : X.PosDef := by
        have hCinv : IsUnit C⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 hC
        dsimp [X]
        simpa [Matrix.star_eq_conjTranspose] using (hCinv.posDef_star_right_conjugate_iff).mpr hY
      refine ⟨X, hX, ?_⟩
      rw [← hed]
      dsimp [e, X]
      exact ratio_eq_scaled_preimage B C Y T S hC hS hY
  have hes : e (sInf A) = sInf (e '' A) := e.map_csInf' hAne hAbdd
  calc
    operatorCapacity S = sInf A' := hScap
    _ = sInf (e '' A) := by rw [hA'_eq]
    _ = e (sInf A) := hes.symm
    _ = a * sInf A := by simp [e]
    _ = Complex.normSq (det B) * Complex.normSq (det C) * operatorCapacity T := by
      rw [← hTcap]
      try dsimp [a]
      try ring

/-- The finite Kraus form `X ↦ ∑ i, A i * X * (A i)†` for a family `A` of complex square
matrices, viewed as a real-linear endomorphism of `Matrix n n ℂ`.  This is the standard
finite-dimensional example of a completely positive map used in the operator scaling
literature. -/
noncomputable def krausMap {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ where
  toFun X := ∑ i, A i * X * (A i).conjTranspose
  map_add' X Y := by
    ext i j
    simp [Finset.sum_add_distrib, Matrix.add_mul, Matrix.mul_add]
  map_smul' c X := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [Matrix.mul_smul, Matrix.smul_mul]
      simp)

omit [DecidableEq n] in
/-- Evaluation of `krausMap`. -/
theorem krausMap_apply {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    krausMap A X = ∑ i, A i * X * (A i).conjTranspose :=
  rfl

omit [DecidableEq n] in
/-- Positivity bridge for the finite Kraus form: if `X` is positive semidefinite, then so is
`krausMap A X`. -/
theorem krausMap_posSemidef {ι : Type*} [Fintype ι] (A : ι → Matrix n n ℂ)
    (X : Matrix n n ℂ) (hX : X.PosSemidef) :
    (krausMap A X).PosSemidef := by
  rw [krausMap_apply]
  exact Matrix.posSemidef_sum Finset.univ (fun i _ => by
    simpa using (hX.conjTranspose_mul_mul_same (A i).conjTranspose))

/-- The operator capacity of a finite Kraus map is well-defined and nonnegative: the
positivity bridge `krausMap_posSemidef` supplies the hypothesis of `operatorCapacity_nonneg`.
-/
theorem operatorCapacity_krausMap_nonneg {ι : Type*} [Fintype ι]
    (A : ι → Matrix n n ℂ) :
    0 ≤ operatorCapacity (krausMap A) := by
  exact operatorCapacity_nonneg (krausMap A) (krausMap_posSemidef A)

end NLAlib
