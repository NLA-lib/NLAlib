/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.QR

/-!
# Householder reflectors and Householder QR

The Householder reflector of a vector `v` is `1 - (2 / ‖v‖²) v vᴴ`: Hermitian, unitary, an
involution, with `v ↦ -v` and the orthogonal complement of `v` fixed. For every vector `x` and
coordinate `i₀` there is a reflector sending `x` to a multiple of the coordinate vector `e_{i₀}`;
`NLAlib.householderVector` is the numerically stable choice of `v`.

Householder QR applies such reflectors to clear the columns of a matrix below the diagonal. It is
defined for matrices indexed by `Fin m` and `Fin n` and never breaks down.

## Main definitions

* `NLAlib.householder`: the reflector of a vector (the identity for the zero vector).
* `NLAlib.householderVector`: the vector whose reflector sends `x` to a multiple of `e_{i₀}`.
* `NLAlib.householderQ`, `NLAlib.householderR`: the factors computed by Householder QR.

## Main results

* `NLAlib.isHermitian_householder`, `NLAlib.householder_mul_self`,
  `NLAlib.hasOrthonormalCols_householder`, `NLAlib.det_householder`.
* `NLAlib.householder_mulVec_householderVector`: the reflector clears a vector.
* `NLAlib.householderQ_mul_householderR`, `NLAlib.hasOrthonormalCols_householderQ`,
  `NLAlib.isUpperTrapezoidal_householderR`: Householder QR computes the full factorization.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] [DecidableEq m]

/-! ### Reflectors -/

/-- The **Householder reflector** of `v`: `1 - (2 / ‖v‖²) v vᴴ`. For `v = 0` it is the identity.
[GolubVanLoan2013, §5.1.2]; [TrefethenBau1997, Lecture 10].
Port of `NLAlib.householder`, there over `ℝ`. -/
noncomputable def householder (v : m → 𝕜) : Matrix m m 𝕜 :=
  1 - ((2 / ‖WithLp.toLp 2 v‖ ^ 2 : ℝ) : 𝕜) • Matrix.vecMulVec v (star v)

/-- A real scalar is fixed by `star`. -/
private theorem star_ofReal (r : ℝ) : star (r : 𝕜) = r := by
  rw [← starRingEnd_apply, RCLike.conj_ofReal]

/-- The reflector of the zero vector is the identity. Port of `NLAlib.householder_zero`. -/
@[simp]
theorem householder_zero : householder (0 : m → 𝕜) = 1 := by
  rw [householder, Matrix.zero_vecMulVec, smul_zero, sub_zero]

/-- The action of a reflector: `H x = x - (2 vᴴx / ‖v‖²) v`.
Port of `NLAlib.householder_mulVec`. -/
theorem householder_mulVec (v x : m → 𝕜) :
    householder v *ᵥ x = x - ((2 / ‖WithLp.toLp 2 v‖ ^ 2 : ℝ) : 𝕜) • (star v ⬝ᵥ x) • v := by
  rw [householder, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul]

/-- A reflector is Hermitian. Port of `NLAlib.householder_transpose`. -/
theorem isHermitian_householder (v : m → 𝕜) : (householder v).IsHermitian := by
  rw [Matrix.IsHermitian, householder, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec, star_star, star_ofReal]

private theorem two_div_mul_two_div_mul (t : ℝ) : 2 / t * (2 / t) * t = 2 * (2 / t) := by
  by_cases ht : t = 0
  · rw [ht, div_zero, mul_zero, mul_zero]
  · field_simp

/-- A reflector is an involution. Port of `NLAlib.householder_mul_self`. -/
@[simp]
theorem householder_mul_self (v : m → 𝕜) : householder v * householder v = 1 := by
  unfold householder
  set t : ℝ := ‖WithLp.toLp 2 v‖ ^ 2 with ht
  have hP : Matrix.vecMulVec v (star v) * Matrix.vecMulVec v (star v) =
      (t : 𝕜) • Matrix.vecMulVec v (star v) := by
    rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul,
      EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq]
  have hc : ((2 / t : ℝ) : 𝕜) * ((2 / t : ℝ) : 𝕜) * (t : 𝕜) = 2 * ((2 / t : ℝ) : 𝕜) := by
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul, two_div_mul_two_div_mul, RCLike.ofReal_mul,
      RCLike.ofReal_ofNat]
  rw [sub_mul, mul_sub, mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_smul, hP, smul_smul, smul_smul, hc]
  module

/-- A reflector is unitary. Port of `NLAlib.hasOrthonormalCols_householder`. -/
theorem hasOrthonormalCols_householder (v : m → 𝕜) : HasOrthonormalCols (householder v) := by
  rw [HasOrthonormalCols, (isHermitian_householder v).eq, householder_mul_self]

omit [DecidableEq m] in
private theorem norm_toLp_sq_ne_zero {v : m → 𝕜} (hv : v ≠ 0) : ‖WithLp.toLp 2 v‖ ^ 2 ≠ 0 :=
  pow_ne_zero 2 (norm_ne_zero_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hv))

/-- A reflector negates its vector. Port of `NLAlib.householder_mulVec_self`. -/
theorem householder_mulVec_self (v : m → 𝕜) : householder v *ᵥ v = -v := by
  rw [householder_mulVec, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, smul_smul,
    ← RCLike.ofReal_mul]
  by_cases hv : v = 0
  · rw [hv, smul_zero, sub_zero, neg_zero]
  · rw [div_mul_cancel₀ _ (norm_toLp_sq_ne_zero hv), RCLike.ofReal_ofNat, two_smul]
    abel

/-- A reflector fixes the vectors orthogonal to its vector.
Port of `NLAlib.householder_mulVec_of_dotProduct_eq_zero`. -/
theorem householder_mulVec_of_dotProduct_eq_zero {v w : m → 𝕜} (h : star v ⬝ᵥ w = 0) :
    householder v *ᵥ w = w := by
  rw [householder_mulVec, h, zero_smul, smul_zero, sub_zero]

/-- The reflector depends only on the direction of its vector. -/
theorem householder_smul {c : 𝕜} (hc : c ≠ 0) (v : m → 𝕜) :
    householder (c • v) = householder v := by
  have hn : ‖WithLp.toLp 2 (c • v)‖ ^ 2 = ‖WithLp.toLp 2 v‖ ^ 2 * ‖c‖ ^ 2 := by
    rw [WithLp.toLp_smul, norm_smul, mul_pow, mul_comm]
  have hcc : c * star c = ((‖c‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.star_def, RCLike.mul_conj, RCLike.ofReal_pow]
  rw [householder, householder, hn, star_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul,
    smul_smul, smul_smul, mul_assoc, hcc, ← RCLike.ofReal_mul, ← div_div,
    div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))]

/-- The determinant of a reflector of a nonzero vector is `-1`. -/
theorem det_householder {v : m → 𝕜} (hv : v ≠ 0) : (householder v).det = -1 := by
  rw [householder, sub_eq_add_neg, ← neg_smul, ← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
    EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, smul_eq_mul, neg_mul,
    ← RCLike.ofReal_mul, div_mul_cancel₀ _ (norm_toLp_sq_ne_zero hv), RCLike.ofReal_ofNat]
  norm_num

/-! ### Clearing a vector -/

/-- The **Householder vector** of `x` at the coordinate `i₀`: `x + phase(x i₀) ‖x‖ e_{i₀}`, with
`phase z = z / ‖z‖` and `phase 0 = 1`. The sign avoids cancellation.
[GolubVanLoan2013, §5.1.3]. Port of `NLAlib.householderVector`, there over `ℝ`. -/
noncomputable def householderVector (x : m → 𝕜) (i₀ : m) : m → 𝕜 :=
  x + ((if x i₀ = 0 then 1 else x i₀ / (‖x i₀‖ : 𝕜)) * (‖WithLp.toLp 2 x‖ : 𝕜)) • Pi.single i₀ 1

/-- The phase factor of the Householder vector has modulus one. -/
private theorem norm_phase (z : 𝕜) : ‖if z = 0 then 1 else z / (‖z‖ : 𝕜)‖ = 1 := by
  split_ifs with h
  · exact norm_one
  · rw [norm_div, RCLike.norm_ofReal, abs_norm, div_self (norm_ne_zero_iff.mpr h)]

/-- The conjugate phase of `z` times `z` is the modulus of `z`. -/
private theorem star_phase_mul (z : 𝕜) :
    star (if z = 0 then 1 else z / (‖z‖ : 𝕜)) * z = (‖z‖ : 𝕜) := by
  split_ifs with h
  · rw [h, mul_zero, norm_zero, RCLike.ofReal_zero]
  · have hz : (‖z‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)
    rw [star_div₀, star_ofReal, div_mul_eq_mul_div, RCLike.star_def, RCLike.conj_mul, pow_two,
      mul_div_assoc, div_self hz, mul_one]

/-- **The Householder reflector clears a vector**: `H x = x - v`, a multiple of `e_{i₀}`.
Port of `NLAlib.householder_mulVec_householderVector`. -/
theorem householder_mulVec_householderVector (x : m → 𝕜) (i₀ : m) :
    householder (householderVector x i₀) *ᵥ x = x - householderVector x i₀ := by
  set v := householderVector x i₀ with hv
  set p : 𝕜 := if x i₀ = 0 then 1 else x i₀ / (‖x i₀‖ : 𝕜) with hp
  set ν : ℝ := ‖WithLp.toLp 2 x‖ with hν
  have hve : v = x + (p * (ν : 𝕜)) • Pi.single i₀ 1 := rfl
  have hxx : star x ⬝ᵥ x = (ν : 𝕜) ^ 2 := by
    rw [EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, RCLike.ofReal_pow]
  have hp1 : star p * p = 1 := by
    rw [RCLike.star_def, RCLike.conj_mul, norm_phase, RCLike.ofReal_one, one_pow]
  have hp2 : star p * x i₀ = (‖x i₀‖ : 𝕜) := star_phase_mul _
  have hp3 : p * star (x i₀) = (‖x i₀‖ : 𝕜) := by
    rw [← star_ofReal (𝕜 := 𝕜) ‖x i₀‖, ← hp2, star_mul', star_star]
  have hsv : star v = star x + (star p * (ν : 𝕜)) • Pi.single i₀ 1 := by
    rw [hve, star_add, star_smul, star_mul', star_ofReal, ← Pi.single_star, star_one]
  have hvx : star v ⬝ᵥ x = (ν : 𝕜) ^ 2 + (ν : 𝕜) * (‖x i₀‖ : 𝕜) := by
    rw [hsv, add_dotProduct, smul_dotProduct, single_dotProduct, hxx, one_mul, smul_eq_mul]
    linear_combination (ν : 𝕜) * hp2
  have hvi : star v i₀ = star (x i₀) + star p * (ν : 𝕜) := by
    rw [hsv, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Pi.star_apply]
  have hvv : star v ⬝ᵥ v = 2 * (star v ⬝ᵥ x) := by
    have h : star v ⬝ᵥ v = star v ⬝ᵥ (x + (p * (ν : 𝕜)) • Pi.single i₀ 1) := by rw [← hve]
    rw [h, dotProduct_add, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, hvi, hvx]
    linear_combination (ν : 𝕜) * hp3 + (ν : 𝕜) ^ 2 * hp1
  have hN : star v ⬝ᵥ v = ((‖WithLp.toLp 2 v‖ ^ 2 : ℝ) : 𝕜) :=
    EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq v
  rw [householder_mulVec]
  by_cases hv0 : v = 0
  · rw [hv0, smul_zero, smul_zero]
  · have hne : ((‖WithLp.toLp 2 v‖ ^ 2 : ℝ) : 𝕜) ≠ 0 :=
      RCLike.ofReal_ne_zero.mpr (norm_toLp_sq_ne_zero hv0)
    have hs : star v ⬝ᵥ x ≠ 0 := by
      intro h
      rw [← hN, hvv, h, mul_zero] at hne
      exact hne rfl
    have hcoef : ((2 / ‖WithLp.toLp 2 v‖ ^ 2 : ℝ) : 𝕜) * (star v ⬝ᵥ x) = 1 := by
      rw [RCLike.ofReal_div, RCLike.ofReal_ofNat, ← hN, hvv]
      field_simp
    rw [smul_smul, hcoef, one_smul]

/-- The cleared vector vanishes away from the chosen coordinate. -/
theorem householder_mulVec_householderVector_apply_of_ne (x : m → 𝕜) {i₀ i : m} (hi : i ≠ i₀) :
    (householder (householderVector x i₀) *ᵥ x) i = 0 := by
  rw [householder_mulVec_householderVector, householderVector, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero, add_zero, sub_self]

/-- The cleared vector has the norm of `x` in the chosen coordinate. -/
theorem norm_householder_mulVec_householderVector_apply (x : m → 𝕜) (i₀ : m) :
    ‖(householder (householderVector x i₀) *ᵥ x) i₀‖ = ‖WithLp.toLp 2 x‖ := by
  rw [householder_mulVec_householderVector, householderVector, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, Pi.single_eq_same, sub_add_cancel_left, norm_neg, smul_eq_mul, mul_one,
    norm_mul, norm_phase, one_mul, RCLike.norm_ofReal, abs_norm]

/-! ### Householder QR -/

section QR

variable {m n : ℕ}

/-- The reflector of step `k` of Householder QR: it clears column `k` of `W` below the diagonal
and fixes the first `k` coordinates. Beyond the size of the matrix it is the identity. -/
noncomputable def householderStep (W : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) :
    Matrix (Fin m) (Fin m) 𝕜 :=
  if h : k < m ∧ k < n then
    householder (householderVector (fun i => if k ≤ (i : ℕ) then W i ⟨k, h.2⟩ else 0) ⟨k, h.1⟩)
  else 1

/-- The state of Householder QR after `k` steps: the accumulated unitary factor and the partially
triangularised matrix. -/
noncomputable def householderState (A : Matrix (Fin m) (Fin n) 𝕜) :
    ℕ → Matrix (Fin m) (Fin m) 𝕜 × Matrix (Fin m) (Fin n) 𝕜
  | 0 => (1, A)
  | k + 1 =>
      ((householderState A k).1 * householderStep (householderState A k).2 k,
        householderStep (householderState A k).2 k * (householderState A k).2)

/-- The unitary factor of Householder QR. Port of `NLAlib.householderQ`, there over `ℝ`. -/
noncomputable def householderQ (A : Matrix (Fin m) (Fin n) 𝕜) : Matrix (Fin m) (Fin m) 𝕜 :=
  (householderState A n).1

/-- The upper trapezoidal factor of Householder QR. Port of `NLAlib.householderR`. -/
noncomputable def householderR (A : Matrix (Fin m) (Fin n) 𝕜) : Matrix (Fin m) (Fin n) 𝕜 :=
  (householderState A n).2

private theorem householderStep_mul_self (W : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) :
    householderStep W k * householderStep W k = 1 := by
  unfold householderStep
  split_ifs
  · exact householder_mul_self _
  · exact Matrix.one_mul 1

private theorem hasOrthonormalCols_householderStep (W : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) :
    HasOrthonormalCols (householderStep W k) := by
  unfold householderStep
  split_ifs
  · exact hasOrthonormalCols_householder _
  · exact hasOrthonormalCols_one

private theorem hasOrthonormalCols_householderState_fst (A : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) :
    HasOrthonormalCols (householderState A k).1 := by
  induction k with
  | zero => exact hasOrthonormalCols_one
  | succ k ih => exact ih.mul (hasOrthonormalCols_householderStep _ k)

private theorem householderState_fst_mul_snd (A : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ) :
    (householderState A k).1 * (householderState A k).2 = A := by
  induction k with
  | zero => exact Matrix.one_mul A
  | succ k ih =>
    rw [householderState, Matrix.mul_assoc, ← Matrix.mul_assoc (householderStep _ k),
      householderStep_mul_self, Matrix.one_mul, ih]

/-- One step of Householder QR keeps the columns already cleared and clears the next one: the
reflector of step `k` fixes every vector supported on the first `k` coordinates. -/
private theorem householderStep_mul_apply_eq_zero {W : Matrix (Fin m) (Fin n) 𝕜} {k : ℕ}
    (hW : ∀ (i : Fin m) (j : Fin n), (j : ℕ) < k → (j : ℕ) < (i : ℕ) → W i j = 0)
    {i : Fin m} {j : Fin n} (hjk : (j : ℕ) < k + 1) (hji : (j : ℕ) < (i : ℕ)) :
    (householderStep W k * W) i j = 0 := by
  by_cases h : k < m ∧ k < n
  swap
  · rw [householderStep, dif_neg h, Matrix.one_mul]
    refine hW i j ?_ hji
    by_contra hjk'
    exact h ⟨by omega, by omega⟩
  rw [householderStep, dif_pos h]
  set x : Fin m → 𝕜 := fun l => if k ≤ (l : ℕ) then W l ⟨k, h.2⟩ else 0 with hx
  set v := householderVector x ⟨k, h.1⟩ with hv
  have hv0 : ∀ l : Fin m, (l : ℕ) < k → v l = 0 := by
    intro l hl
    have hne : l ≠ ⟨k, h.1⟩ := fun e => hl.ne (congrArg Fin.val e)
    rw [hv, householderVector, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero,
      add_zero, hx]
    exact if_neg (not_le.mpr hl)
  have hfix : ∀ w : Fin m → 𝕜, (∀ l : Fin m, k ≤ (l : ℕ) → w l = 0) →
      householder v *ᵥ w = w := by
    intro w hw
    refine householder_mulVec_of_dotProduct_eq_zero (Finset.sum_eq_zero fun l _ => ?_)
    by_cases hl : k ≤ (l : ℕ)
    · rw [hw l hl, mul_zero]
    · rw [Pi.star_apply, hv0 l (not_le.mp hl), star_zero, zero_mul]
  change (householder v *ᵥ fun l => W l j) i = 0
  rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hjk' | hjk'
  · rw [hfix _ fun l hl => hW l j hjk' (hjk'.trans_le hl)]
    exact hW i j hjk' hji
  · have hj : j = ⟨k, h.2⟩ := Fin.ext hjk'
    have hcol : (fun l => W l j) = x + fun l : Fin m => if k ≤ (l : ℕ) then 0 else W l j := by
      ext l
      rw [Pi.add_apply, hj]
      by_cases hl : k ≤ (l : ℕ)
      · simp only [hx, if_pos hl, add_zero]
      · simp only [hx, if_neg hl, zero_add]
    have hi : i ≠ ⟨k, h.1⟩ := fun e => (hjk' ▸ hji).ne' (congrArg Fin.val e)
    rw [hcol, Matrix.mulVec_add, hfix _ fun l hl => if_pos hl, Pi.add_apply,
      householder_mulVec_householderVector_apply_of_ne x hi, zero_add]
    exact if_pos (hjk' ▸ hji).le

/-- After `k` steps of Householder QR the first `k` columns vanish below the diagonal. -/
private theorem householderState_snd_apply_eq_zero (A : Matrix (Fin m) (Fin n) 𝕜) (k : ℕ)
    (i : Fin m) (j : Fin n) (hjk : (j : ℕ) < k) (hji : (j : ℕ) < (i : ℕ)) :
    (householderState A k).2 i j = 0 := by
  induction k generalizing i j with
  | zero => exact absurd hjk (Nat.not_lt_zero _)
  | succ k ih => exact householderStep_mul_apply_eq_zero ih hjk hji

/-- The unitary factor of Householder QR is unitary.
Port of `NLAlib.hasOrthonormalCols_householderQ`. -/
theorem hasOrthonormalCols_householderQ (A : Matrix (Fin m) (Fin n) 𝕜) :
    HasOrthonormalCols (householderQ A) := by
  exact hasOrthonormalCols_householderState_fst A n

/-- Householder QR factors the matrix. Port of `NLAlib.householderQ_mul_householderR`. -/
theorem householderQ_mul_householderR (A : Matrix (Fin m) (Fin n) 𝕜) :
    householderQ A * householderR A = A := by
  exact householderState_fst_mul_snd A n

/-- **The second factor of Householder QR is upper trapezoidal.**
[TrefethenBau1997, Lecture 10]. Port of `NLAlib.isUpperTrapezoidal_householderR`. -/
theorem isUpperTrapezoidal_householderR (A : Matrix (Fin m) (Fin n) 𝕜) :
    IsUpperTrapezoidal (householderR A) := by
  exact fun i j hji => householderState_snd_apply_eq_zero A n i j j.2 hji

/-- Householder QR gives the thin QR factorization of a tall matrix.
Port of `NLAlib.isQR_householderQR`. -/
theorem isQR_householder (A : Matrix (Fin m) (Fin n) 𝕜) (h : n ≤ m) :
    IsQR A ((householderQ A).submatrix id (Fin.castLE h))
      ((householderR A).submatrix (Fin.castLE h) id) := by
  exact isQR_submatrix_castLE (hasOrthonormalCols_householderQ A)
    (isUpperTrapezoidal_householderR A) (householderQ_mul_householderR A).symm h

end QR

end NLAlib
