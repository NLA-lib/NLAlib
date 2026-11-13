/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Mixed
public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Finite fixed-point arithmetic as a BLAS model

Words are bounded integers decoded at a positive integer scale. Arithmetic rounds to the
nearest grid point, then saturates at the two finite endpoints. The mixed accuracy guarantee
is proved only inside the declared range; saturation outside it is specified separately.
The absolute allowance is half a grid spacing, including underflow to zero.

This is a mathematical finite-format witness for the Ops core, not native IEEE arithmetic.
Its BLAS consequences reuse the existing programs and the generic mixed-error proofs.

## Main results

* `NLAlib.Ops.Examples.FixedPoint.finite_word`: the carrier is finite.
* `NLAlib.Ops.Examples.FixedPoint.mixedModel_machine`: the finite arithmetic accuracy model.
* `NLAlib.Ops.Examples.FixedPoint.exists_scalar_model`: joint finite-word realization.
* `NLAlib.Ops.Examples.FixedPoint.isAxpyMixedErr_axpyF`: finite-word BLAS error bound.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.FixedPoint

/-- A signed integer word with closed finite endpoints. -/
structure Word (bound : ℕ) where
  /-- Integer stored by the word. -/
  val : ℤ
  /-- Lower endpoint. -/
  lower : -(bound : ℤ) ≤ val
  /-- Upper endpoint. -/
  upper : val ≤ bound

/-- Every format includes zero. -/
instance (bound : ℕ) : Inhabited (Word bound) := ⟨⟨0, by omega, by omega⟩⟩

/-- There are finitely many signed words, independently of their arithmetic interpretation. -/
theorem finite_word (bound : ℕ) : Finite (Word bound) := by
  let f : Word bound → {z : ℤ // z ∈ Set.Icc (-(bound : ℤ)) bound} :=
    fun w => ⟨w.val, w.lower, w.upper⟩
  let := (Set.finite_Icc (-(bound : ℤ)) (bound : ℤ)).to_subtype
  exact Finite.of_injective f fun a b h => by
    cases a
    cases b
    cases congrArg Subtype.val h
    rfl

/-- Decode a word using the supplied number of grid steps per unit. -/
noncomputable def decode (scale : ℕ) {bound : ℕ} (w : Word bound) : ℝ := w.val / (scale : ℝ)

/-- Nearest integer rounding followed by saturation to the word's closed finite interval. -/
noncomputable def roundedWord (bound : ℕ) (x : ℝ) : Word bound :=
  ⟨max (-(bound : ℤ)) (min (bound : ℤ) (round x)), le_max_left _ _,
    max_le (by omega) (min_le_left _ _)⟩

/-- Saturation is inactive when the exact target is in the integer interval. -/
theorem val_roundedWord_of_abs_le {bound : ℕ} {x : ℝ} (hx : |x| ≤ bound) :
    (roundedWord bound x).val = round x := by
  have hlo : -(bound : ℤ) ≤ round x := by
    rw [round_eq, Int.le_floor]
    push_cast
    linarith [(abs_le.mp hx).1]
  have hhi : round x ≤ (bound : ℤ) := by
    rw [round_eq, Int.floor_le_iff]
    push_cast
    linarith [(abs_le.mp hx).2]
  exact max_eq_right (hlo.trans_eq (min_eq_right hhi).symm) |>.trans (min_eq_right hhi)

/-- Quantize a real target on the scaled grid, with a specified saturation policy. -/
noncomputable def quantize (bound scale : ℕ) (x : ℝ) : Word bound :=
  roundedWord bound ((scale : ℝ) * x)

/-- In-range quantization has absolute error at most half a grid spacing. -/
theorem abs_decode_quantize_sub_le (bound scale : ℕ) (hs : 0 < scale) {x : ℝ}
    (hx : |x| ≤ (bound : ℝ) / scale) :
    |decode scale (quantize bound scale x) - x| ≤ (1 / 2 : ℝ) / scale := by
  have hs' : 0 < (scale : ℝ) := by exact_mod_cast hs
  have ht : |(scale : ℝ) * x| ≤ bound := by
    rw [abs_mul, abs_of_pos hs']
    nlinarith [(le_div_iff₀ hs').mp hx]
  have hv := val_roundedWord_of_abs_le ht
  have he : decode scale (quantize bound scale x) - x =
      ((round ((scale : ℝ) * x) : ℝ) - (scale : ℝ) * x) / scale := by
    simp only [decode, quantize, hv]
    field_simp [hs'.ne']
  rw [he, abs_div, abs_of_pos hs']
  exact div_le_div_of_nonneg_right (by simpa only [abs_sub_comm] using
    (abs_sub_round ((scale : ℝ) * x))) hs'.le

/-- Rounded finite fixed-point operations; negation is exact. -/
noncomputable def machine (bound scale : ℕ) : Machine (Word bound) where
  lit q := quantize bound scale q
  add a b := quantize bound scale (decode scale a + decode scale b)
  sub a b := quantize bound scale (decode scale a - decode scale b)
  mul a b := quantize bound scale (decode scale a * decode scale b)
  div a b := quantize bound scale (decode scale a / decode scale b)
  neg a := ⟨-a.val, by have := a.upper; omega, by have := a.lower; omega⟩
  sqrt a := quantize bound scale (Real.sqrt (decode scale a))

/-- The numerical model is realized on a finite carrier. Relative allowance is zero and the
absolute allowance is half a grid spacing. The input scale is positive. -/
theorem mixedModel_machine (bound scale : ℕ) (hs : 0 < scale) :
    MixedModel 0 ((1 / 2 : ℝ) / scale) (decode scale) (machine bound scale)
      (fun x => |x| ≤ (bound : ℝ) / scale) where
  roundoff_nonneg := le_rfl
  absolute_nonneg := by positivity
  lit q h := by simpa [machine] using abs_decode_quantize_sub_le bound scale hs h
  add a b h := by simpa [machine] using abs_decode_quantize_sub_le bound scale hs h
  sub a b h := by simpa [machine] using abs_decode_quantize_sub_le bound scale hs h
  mul a b h := by simpa [machine] using abs_decode_quantize_sub_le bound scale hs h
  div a b _ h := by simpa [machine] using abs_decode_quantize_sub_le bound scale hs h
  neg a := by
    change ((-a.val : ℤ) : ℝ) / scale = -(a.val / (scale : ℝ))
    rw [Int.cast_neg, neg_div]
  sqrt a _ h := by
    simpa [machine, Real.sqrt_nonneg] using abs_decode_quantize_sub_le bound scale hs h

/-- The same finite machine and scalar interpreter jointly satisfy their contracts. -/
theorem exists_scalar_model (bound scale : ℕ) (hs : 0 < scale) :
    ∃ I : Interp ScalarOp Empty (Word bound), IsScalar (machine bound scale) I ∧
      MixedModel 0 ((1 / 2 : ℝ) / scale) (decode scale) (machine bound scale)
        (fun x => |x| ≤ (bound : ℝ) / scale) :=
  ⟨Interp.ofFns (machine bound scale).fn,
    isScalar_ofFns _ _ (fun _ => rfl), mixedModel_machine bound scale hs⟩

/-- AXPY on any admitted finite vectors inherits the generic error bound. -/
theorem isAxpyMixedErr_axpyF (bound scale : ℕ) (hs : 0 < scale) (a : Word bound)
    (x y : ℕ → Word bound) (n : ℕ)
    (h : AxpySafe (decode scale) (machine bound scale)
      (fun z => |z| ≤ (bound : ℝ) / scale) n a x y) :
    IsAxpyMixedErr (decode scale) 0 (1 / (scale : ℝ)) n a x y
      (vec (axpyF (machine bound scale) a x y n)) := by
  have he : 2 * ((1 / 2 : ℝ) / scale) = 1 / (scale : ℝ) := by ring
  simpa only [add_zero, zero_add, one_pow, sub_self, he] using
    Ops.isAxpyMixedErr_axpyF (mixedModel_machine bound scale hs) a x y n h

/-- Scaling on admitted finite vectors also reuses the generic numerical proof. -/
theorem isScalMixedErr_scalF (bound scale : ℕ) (hs : 0 < scale) (a : Word bound)
    (x : ℕ → Word bound) (n : ℕ)
    (h : ScalSafe (decode scale) (fun z => |z| ≤ (bound : ℝ) / scale) n a x) :
    IsScalMixedErr (decode scale) 0 ((1 / 2 : ℝ) / scale) n a x
      (vec (scalF (machine bound scale) a x n)) :=
  Ops.isScalMixedErr_scalF (mixedModel_machine bound scale hs) a x n h

/-- On actual finite words, the existing axpy loop stores the admitted mixed-error output.
There is no assumed scalar-model witness: the interpretation and numerical model are supplied. -/
theorem wp_axpyLoop (bound scale : ℕ) (hs : 0 < scale)
    {τ : Tape (Word bound)} {n : ℕ} {al x y : ℕ × ℕ} {m : Mem (Word bound)}
    {a : Word bound} {xs ys : List (Word bound)}
    (hal : al.1 ≠ y.1) (hxy : x.1 ≠ y.1) (hl : m.Live [al, x, y])
    (ha : m.store.get al.1 al.2 = some a) (hx : m.store.readBlock x.1 x.2 n = some xs)
    (hy : m.store.readBlock y.1 y.2 n = some ys)
    (h : AxpySafe (decode scale) (machine bound scale)
      (fun z => |z| ≤ (bound : ℝ) / scale) n a (vec xs) (vec ys)) :
    Wp .total (Interp.ofFns (machine bound scale).fn : Interp ScalarOp Empty (Word bound))
      τ axpyLoop.body (Env.frame [n] [al, x, y, y])
      (fun m' => m'.pos = m.pos ∧ ∃ zs, m'.store.readBlock y.1 y.2 n = some zs ∧
        IsAxpyMixedErr (decode scale) 0 (1 / (scale : ℝ)) n a (vec xs) (vec ys) (vec zs))
      m := by
  have he : 2 * ((1 / 2 : ℝ) / scale) = 1 / (scale : ℝ) := by ring
  simpa only [add_zero, zero_add, one_pow, sub_self, he] using
    wp_axpyLoop_mixed
      (isScalar_ofFns (machine bound scale) (machine bound scale).fn (fun _ => rfl))
      (mixedModel_machine bound scale hs) hal hxy hl ha hx hy h

/-- Nonempty admitted domains at every vector length: zero data need no range margin. -/
theorem axpySafe_zero (bound scale n : ℕ) :
    AxpySafe (decode scale) (machine bound scale)
      (fun z => |z| ≤ (bound : ℝ) / scale) n default
      (fun _ => default) (fun _ => default) := by
  intro i _
  have hq : decode scale (quantize bound scale 0) = 0 := by
    simp [decode, quantize, roundedWord]
  have hz : decode scale (default : Word bound) = 0 := by
    change ((0 : ℤ) : ℝ) / scale = 0
    simp only [Int.cast_zero, zero_div]
  have hb : (0 : ℝ) ≤ (bound : ℝ) / scale :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  constructor
  · simpa only [hz, zero_mul, abs_zero] using hb
  · change |decode scale default + decode scale (quantize bound scale
      (decode scale default * decode scale default))| ≤ _
    simpa only [hz, zero_mul, zero_add, hq, abs_zero] using hb

/-- A finite format that underflows cannot satisfy the relative-only standard model with
unit roundoff below one, even though its guarded mixed model is realized. -/
theorem not_stdModel_machine {u : ℝ} (hu : u < 1) :
    ¬ StdModel u (decode 2) (machine 8 2) := by
  intro h
  have he := h.lit (1 / 8)
  norm_num [machine, decode, quantize, roundedWord, round_eq] at he
  linarith

/-- A product on the half-unit grid really rounds: one half squared becomes one half. -/
example : decode 2 ((machine 8 2).mul ⟨1, by omega, by omega⟩
    ⟨1, by omega, by omega⟩) = 1 / 2 := by
  norm_num [machine, decode, quantize, roundedWord, round_eq]

/-- A small nonzero exact target underflows to zero. The absolute error term is necessary. -/
example : decode 2 (quantize 8 2 (1 / 8)) = 0 := by
  norm_num [decode, quantize, roundedWord, round_eq]

/-- The specified saturation outside the admitted range is observable, not silently exact. -/
example : decode 2 (quantize 8 2 5) = 4 := by
  norm_num [decode, quantize, roundedWord, round_eq]

/-- A safe final ideal result does not justify an overflowing intermediate product:
2*3-3=3 is in range, but saturation changes the computed result to 1. -/
example :
    let a : Word 8 := ⟨4, by omega, by omega⟩
    let x : Word 8 := ⟨6, by omega, by omega⟩
    let y : Word 8 := ⟨-6, by omega, by omega⟩
    |decode 2 y + decode 2 a * decode 2 x| ≤ 4 ∧
      ¬ (|decode 2 a * decode 2 x| ≤ 4) ∧
      |decode 2 ((machine 8 2).add y ((machine 8 2).mul a x)) -
        (decode 2 y + decode 2 a * decode 2 x)| > 1 / 2 := by
  norm_num [machine, decode, quantize, roundedWord, round_eq]

end NLAlib.Ops.Examples.FixedPoint
