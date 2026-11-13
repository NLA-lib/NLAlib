/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Math.Recurrence

/-!
# Initialized prefixes of the Lanczos recurrence

The basis prefix retains columns through the current state. The coefficient prefix retains
completed diagonal coefficients, coupling coefficients through the current state, and the input
norm. Unwritten entries are zero. These total functions describe initialized program outputs,
including successful early exit when the current vector becomes zero.

## Main results

* `NLAlib.Krylov.Lanczos.basisValue_succ` describes one basis-column update.
* `NLAlib.Krylov.Lanczos.coeffValue_succ` describes the two coefficient updates.
* `NLAlib.Krylov.Lanczos.basisValue_eq_of_cur_beta_zero` identifies a stopped prefix with
  the full basis output.
* `NLAlib.Krylov.Lanczos.coeffValue_eq_of_cur_beta_zero` identifies its full coefficients.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open scoped Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- The Lanczos basis columns already initialized at the current step; later columns are zero.
[Paige1972, §2]. -/
noncomputable def basisValue (A : Matrix n n 𝕜) (b : n → 𝕜) (done j : ℕ) : n → 𝕜 :=
  if j ≤ done then (lanczosState A b j).cur else 0

/-- Packed Lanczos coefficients: diagonal coefficients, couplings including the initial zero,
then the input norm. Unwritten entries and entries beyond this layout are zero.
[Paige1972, §2]. -/
noncomputable def coeffValue (A : Matrix n n 𝕜) (b : n → 𝕜)
    (cap done i : ℕ) : ℝ :=
  if i < cap then (if i < done then lanczosAlpha A (lanczosState A b i) else 0)
  else if i ≤ 2 * cap then (if i - cap ≤ done then (lanczosState A b (i - cap)).beta else 0)
  else if i = 2 * cap + 1 then ‖WithLp.toLp 2 b‖ else 0

/-- A normalized Lanczos step is zero exactly when its computed coupling is zero.
[Paige1972, §2]. -/
theorem lanczosStep_cur_eq_zero_iff_beta_eq_zero (A : Matrix n n 𝕜)
    (s : LanczosState 𝕜 n) :
    (lanczosStep A s).cur = 0 ↔ (lanczosStep A s).beta = 0 := by
  simp only [lanczosStep, smul_eq_zero, RCLike.ofReal_eq_zero, inv_eq_zero,
    norm_eq_zero, WithLp.toLp_eq_zero, or_self]

/-- The initial normalized vector is zero exactly when the input is zero.
[Saad2011, §6.6]. -/
theorem lanczosState_zero_cur_eq_zero_iff (A : Matrix n n 𝕜) (b : n → 𝕜) :
    (lanczosState A b 0).cur = 0 ↔ b = 0 := by
  simp only [lanczosState, smul_eq_zero, RCLike.ofReal_eq_zero, inv_eq_zero,
    norm_eq_zero, WithLp.toLp_eq_zero, or_self]

/-- Every Lanczos coupling is nonnegative, including the initial zero.
[Paige1972, §2]. -/
theorem lanczosState_beta_nonneg (A : Matrix n n 𝕜) (b : n → 𝕜) (j : ℕ) :
    0 ≤ (lanczosState A b j).beta := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact norm_nonneg _

/-- A zero current recurrence vector has zero coupling, at initialization and every later step.
[Paige1972, §2]. -/
theorem lanczosState_beta_eq_zero_of_cur_eq_zero (A : Matrix n n 𝕜) (b : n → 𝕜)
    {j : ℕ} (hc : (lanczosState A b j).cur = 0) :
    (lanczosState A b j).beta = 0 := by
  cases j with
  | zero => rfl
  | succ j => exact (lanczosStep_cur_eq_zero_iff_beta_eq_zero A _).mp hc

/-- An initialized basis column has its recurrence value. [Paige1972, §2]. -/
theorem basisValue_of_le (A : Matrix n n 𝕜) (b : n → 𝕜) {done j : ℕ}
    (hj : j ≤ done) : basisValue A b done j = (lanczosState A b j).cur := by
  simp only [basisValue, if_pos hj]

/-- A future basis column is zero. [Paige1972, §2]. -/
theorem basisValue_of_lt (A : Matrix n n 𝕜) (b : n → 𝕜) {done j : ℕ}
    (hj : done < j) : basisValue A b done j = 0 := by
  simp only [basisValue, if_neg (not_le.mpr hj)]

/-- Before the first round only the initial basis column is initialized.
[Saad2011, §6.6]. -/
theorem basisValue_zero (A : Matrix n n 𝕜) (b : n → 𝕜) (j : ℕ) :
    basisValue A b 0 j = if j = 0 then (lanczosState A b 0).cur else 0 := by
  by_cases hj : j = 0
  · subst j; simp [basisValue]
  · simp only [basisValue, if_neg hj, if_neg (by omega : ¬j ≤ 0)]

/-- The diagonal segment stores exactly the completed coefficients. [Paige1972, §2]. -/
theorem coeffValue_alpha (A : Matrix n n 𝕜) (b : n → 𝕜) {cap done j : ℕ}
    (hj : j < cap) :
    coeffValue A b cap done j =
      if j < done then lanczosAlpha A (lanczosState A b j) else 0 := by
  simp only [coeffValue, if_pos hj]

/-- The coupling segment includes the current state coupling and the initial zero.
[Paige1972, §2]. -/
theorem coeffValue_beta (A : Matrix n n 𝕜) (b : n → 𝕜) {cap done j : ℕ}
    (hj : j ≤ cap) :
    coeffValue A b cap done (cap + j) =
      if j ≤ done then (lanczosState A b j).beta else 0 := by
  simp only [coeffValue, if_neg (by omega : ¬cap + j < cap),
    if_pos (by omega : cap + j ≤ 2 * cap), Nat.add_sub_cancel_left]

/-- The final layout cell always contains the input norm. [Saad2011, §6.6]. -/
theorem coeffValue_norm (A : Matrix n n 𝕜) (b : n → 𝕜) (cap done : ℕ) :
    coeffValue A b cap done (2 * cap + 1) = ‖WithLp.toLp 2 b‖ := by
  simp only [coeffValue, if_neg (by omega : ¬2 * cap + 1 < cap),
    if_neg (by omega : ¬2 * cap + 1 ≤ 2 * cap), ite_true]

/-- Cells beyond the coefficient layout are zero. [Paige1972, §2]. -/
theorem coeffValue_of_lt (A : Matrix n n 𝕜) (b : n → 𝕜) {cap done i : ℕ}
    (hi : 2 * cap + 1 < i) : coeffValue A b cap done i = 0 := by
  simp only [coeffValue, if_neg (by omega : ¬i < cap),
    if_neg (by omega : ¬i ≤ 2 * cap), if_neg (by omega : i ≠ 2 * cap + 1)]

/-- Initially only the input norm is nonzero in the coefficient output.
[Saad2011, §6.6]. -/
theorem coeffValue_zero (A : Matrix n n 𝕜) (b : n → 𝕜) (cap i : ℕ) :
    coeffValue A b cap 0 i = if i = 2 * cap + 1 then ‖WithLp.toLp 2 b‖ else 0 := by
  by_cases hi : i < cap
  · simp only [coeffValue, if_pos hi, Nat.not_lt_zero, ↓reduceIte,
      if_neg (by omega : i ≠ 2 * cap + 1)]
  · by_cases hi' : i ≤ 2 * cap
    · by_cases hz : i - cap ≤ 0
      · have he : i - cap = 0 := by omega
        simp only [coeffValue, if_neg hi, if_pos hi', he, lanczosState, ite_self,
          if_neg (by omega : i ≠ 2 * cap + 1)]
      · simp only [coeffValue, if_neg hi, if_pos hi', if_neg hz,
          if_neg (by omega : i ≠ 2 * cap + 1)]
    · simp only [coeffValue, if_neg hi, if_neg hi']

/-- Advancing one round changes just the next basis column. [Paige1972, §2]. -/
theorem basisValue_succ (A : Matrix n n 𝕜) (b : n → 𝕜) (done j : ℕ) :
    basisValue A b (done + 1) j =
      if j = done + 1 then (lanczosState A b (done + 1)).cur else basisValue A b done j := by
  by_cases he : j = done + 1
  · subst j; simp only [basisValue, le_refl, ↓reduceIte]
  · have hh : (j ≤ done + 1) = (j ≤ done) := propext (by omega)
    simp only [basisValue, if_neg he, hh]

/-- Advancing below the cap writes the next diagonal and next coupling cells only.
[Paige1972, §2]. -/
theorem coeffValue_succ (A : Matrix n n 𝕜) (b : n → 𝕜) {cap done : ℕ}
    (hd : done < cap) (i : ℕ) :
    coeffValue A b cap (done + 1) i =
      if i = done then lanczosAlpha A (lanczosState A b done)
      else if i = cap + done + 1 then (lanczosState A b (done + 1)).beta
      else coeffValue A b cap done i := by
  by_cases ha : i = done
  · subst i
    simp only [coeffValue, if_pos hd, Nat.lt_succ_self, ↓reduceIte]
  · by_cases hb : i = cap + done + 1
    · subst i
      have hsub : cap + done + 1 - cap = done + 1 := by omega
      simp only [coeffValue, if_neg (by omega : ¬cap + done + 1 < cap),
        if_pos (by omega : cap + done + 1 ≤ 2 * cap), hsub, le_refl, ↓reduceIte,
        if_neg (by omega : cap + done + 1 ≠ done)]
    · have halpha : (i < done + 1) = (i < done) := propext (by omega)
      have hbeta : i ≤ 2 * cap → ¬i < cap →
          (i - cap ≤ done + 1) = (i - cap ≤ done) := by
        intro hi hi'
        apply propext
        omega
      by_cases hi : i < cap
      · simp only [coeffValue, if_pos hi, if_neg ha, if_neg hb, halpha]
      · by_cases hi' : i ≤ 2 * cap
        · simp only [coeffValue, if_neg hi, if_pos hi', if_neg ha, if_neg hb,
            hbeta hi' hi]
        · simp only [coeffValue, if_neg hi, if_neg hi', if_neg ha, if_neg hb]

/-- Stopping at a zero-current, zero-coupling state leaves exactly the full basis values
through any later cap. [Paige1972, §2]. -/
theorem basisValue_eq_of_cur_beta_zero (A : Matrix n n 𝕜) (b : n → 𝕜)
    {done cap : ℕ} (hd : done ≤ cap) (hc : (lanczosState A b done).cur = 0)
    (hb : (lanczosState A b done).beta = 0) (j : ℕ) :
    basisValue A b done j = basisValue A b cap j := by
  by_cases hj : j ≤ done
  · simp only [basisValue, if_pos hj, if_pos (hj.trans hd)]
  · by_cases hj' : j ≤ cap
    · have hz := lanczosState_cur_beta_zero_of_le A b (by omega : done ≤ j) hc hb
      simp only [basisValue, if_neg hj, if_pos hj', hz.1]
    · simp only [basisValue, if_neg hj, if_neg hj']

/-- Stopping at a zero-current, zero-coupling state leaves exactly the full coefficient
layout. No Hermitian hypothesis is needed. [Paige1972, §2]. -/
theorem coeffValue_eq_of_cur_beta_zero (A : Matrix n n 𝕜) (b : n → 𝕜)
    {done cap : ℕ} (hc : (lanczosState A b done).cur = 0)
    (hb : (lanczosState A b done).beta = 0) (i : ℕ) :
    coeffValue A b cap done i = coeffValue A b cap cap i := by
  by_cases hi : i < cap
  · rw [coeffValue_alpha A b hi, coeffValue_alpha A b hi, if_pos hi]
    by_cases hid : i < done
    · rw [if_pos hid]
    · have hz := lanczosState_cur_beta_zero_of_le A b (by omega : done ≤ i) hc hb
      rw [if_neg hid, lanczosAlpha_eq_zero_of_cur_eq_zero A _ hz.1]
  · by_cases hi' : i ≤ 2 * cap
    · have hsub : i - cap ≤ cap := by omega
      simp only [coeffValue, if_neg hi, if_pos hi', if_pos hsub]
      by_cases hid : i - cap ≤ done
      · rw [if_pos hid]
      · have hz := lanczosState_cur_beta_zero_of_le A b (by omega : done ≤ i - cap) hc hb
        rw [if_neg hid, hz.2]
    · simp only [coeffValue, if_neg hi, if_neg hi']

end NLAlib.Krylov.Lanczos
