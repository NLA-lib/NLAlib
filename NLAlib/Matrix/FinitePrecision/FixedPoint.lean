/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.ArithmeticError
public import Mathlib.Data.Rat.Floor

/-!
# Checked floor rounding on a finite fixed-point grid

Bounded integer words are encoded injectively into a finite set. Rational values round
down and reject an out-of-range result. A positive scale gives an absolute error at most
one grid spacing and guarantees rounding succeeds throughout the closed decoded interval.
This policy is separate from nearest rounding with saturation.

## Main results

* `NLAlib.Computation.FixedPoint.toFin_injective` supplies the finite encoding.
* `NLAlib.Computation.abs_sub_fixedPointDecode_le_of_fixedPointRound` bounds rounding error.
* `NLAlib.Computation.fixedPointRound_exists_of_abs_le` guarantees in-range rounding.
-/

@[expose] public section

namespace NLAlib.Computation

/-- Integer fixed-point words in the symmetric range $[-\mathit{limit},\mathit{limit}]$.
The scale is supplied by the arithmetic interpretation, not stored in each word. -/
abbrev FixedPoint (limit : ℕ) := {w : ℤ // |w| ≤ (limit : ℤ)}

/-- Encode a bounded signed integer by its offset from the lower endpoint. -/
def FixedPoint.toFin {limit : ℕ} (w : FixedPoint limit) : Fin (2 * limit + 1) :=
  ⟨(w.val + (limit : ℤ)).toNat, by have hw := abs_le.mp w.property; omega⟩

/-- Distinct fixed-point words have distinct finite encodings. -/
theorem FixedPoint.toFin_injective {limit : ℕ} :
    Function.Injective (@FixedPoint.toFin limit) := by
  intro x y h
  apply Subtype.ext
  have hx := abs_le.mp x.property
  have hy := abs_le.mp y.property
  have hval := congrArg Fin.val h
  dsimp only [FixedPoint.toFin] at hval
  omega

/-- A fixed-point word decodes to its signed integer value divided by the scale.
At scale zero the value is the real division junk value zero; accuracy requires positive scale. -/
noncomputable def fixedPointDecode (scale : ℕ) {limit : ℕ} (w : FixedPoint limit) : ℝ :=
  (w.val : ℝ) / (scale : ℝ)

/-- Store an integer if it lies in the fixed-point carrier; reject an out-of-range integer. -/
def fixedPointPack (limit : ℕ) (m : ℤ) : Option (FixedPoint limit) :=
  if h : |m| ≤ (limit : ℤ) then some ⟨m, h⟩ else none

/-- Round a rational down to the fixed-point grid and reject a rounded out-of-range word. -/
def fixedPointRound (scale limit : ℕ) (a : ℚ) : Option (FixedPoint limit) :=
  fixedPointPack limit ⌊a * (scale : ℚ)⌋

/-- A successful checked integer store retains exactly the supplied integer. -/
theorem val_eq_of_fixedPointPack {limit : ℕ} {m : ℤ} {w : FixedPoint limit}
    (h : fixedPointPack limit m = some w) : w.val = m := by
  unfold fixedPointPack at h
  split_ifs at h
  · cases h
    rfl

/-- Successful rational rounding stores its integer floor on the scaled grid. -/
theorem val_eq_floor_of_fixedPointRound {scale limit : ℕ} {a : ℚ} {w : FixedPoint limit}
    (h : fixedPointRound scale limit a = some w) : w.val = ⌊a * (scale : ℚ)⌋ :=
  val_eq_of_fixedPointPack h

/-- Rounding down on a positive-scale grid has absolute error at most one grid spacing. -/
theorem abs_sub_fixedPointDecode_le_of_fixedPointRound {scale limit : ℕ} {a : ℚ}
    {w : FixedPoint limit}
    (hscale : 0 < scale) (h : fixedPointRound scale limit a = some w) :
    |(a : ℝ) - fixedPointDecode scale w| ≤ 1 / (scale : ℝ) := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hlo : (⌊a * (scale : ℚ)⌋ : ℝ) ≤ (a : ℝ) * scale := by
    exact_mod_cast (Int.floor_le (a * (scale : ℚ)))
  have hhi : (a : ℝ) * scale < (⌊a * (scale : ℚ)⌋ : ℝ) + 1 := by
    exact_mod_cast (Int.lt_floor_add_one (a * (scale : ℚ)))
  rw [fixedPointDecode, val_eq_floor_of_fixedPointRound h]
  have hnonneg : 0 ≤ (a : ℝ) - (⌊a * (scale : ℚ)⌋ : ℝ) / scale :=
    sub_nonneg.mpr ((div_le_iff₀ hs).2 hlo)
  rw [abs_of_nonneg hnonneg]
  apply (le_div_iff₀ hs).2
  have heq : ((a : ℝ) - (⌊a * (scale : ℚ)⌋ : ℝ) / scale) * scale =
      (a : ℝ) * scale - (⌊a * (scale : ℚ)⌋ : ℝ) := by
    field_simp
  rw [heq]
  linarith

/-- A checked integer store succeeds when its decoded value is in the fixed-point interval. -/
theorem fixedPointPack_exists_of_abs_div_le {scale limit : ℕ} {m : ℤ}
    (hscale : 0 < scale)
    (h : |(m : ℝ) / (scale : ℝ)| ≤ (limit : ℝ) / (scale : ℝ)) :
    ∃ w, fixedPointPack limit m = some w := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
  rw [abs_div, abs_of_pos hs] at h
  have hm : |m| ≤ (limit : ℤ) := by
    exact_mod_cast (div_le_div_iff_of_pos_right hs).mp h
  exact ⟨⟨m, hm⟩, by simp only [fixedPointPack, hm, ↓reduceDIte]⟩

/-- Rounding succeeds for every rational exact value in the closed representable interval. -/
theorem fixedPointRound_exists_of_abs_le {scale limit : ℕ} {a : ℚ}
    (hscale : 0 < scale) (h : |(a : ℝ)| ≤ (limit : ℝ) / (scale : ℝ)) :
    ∃ w, fixedPointRound scale limit a = some w := by
  have hs : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hr : |(a : ℝ) * scale| ≤ (limit : ℝ) := by
    rw [abs_mul, abs_of_pos hs]
    exact (le_div_iff₀ hs).mp h
  have hl : -(limit : ℚ) ≤ a * (scale : ℚ) := by
    exact_mod_cast (abs_le.mp hr).1
  have hu : a * (scale : ℚ) ≤ (limit : ℚ) := by
    exact_mod_cast (abs_le.mp hr).2
  have hlo : -(limit : ℤ) ≤ ⌊a * (scale : ℚ)⌋ := Int.le_floor.mpr hl
  have hhi : ⌊a * (scale : ℚ)⌋ ≤ (limit : ℤ) := by
    exact_mod_cast (Int.floor_le (a * (scale : ℚ))).trans hu
  have hm : |⌊a * (scale : ℚ)⌋| ≤ (limit : ℤ) := abs_le.mpr ⟨hlo, hhi⟩
  exact ⟨⟨_, hm⟩, by simp only [fixedPointRound, fixedPointPack, hm, ↓reduceDIte]⟩

end NLAlib.Computation
