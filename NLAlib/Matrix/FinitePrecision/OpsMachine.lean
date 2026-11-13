/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Machine
public import NLAlib.Ops.Catalog.Index

/-!
# Mathematical matrix machines from Ops scalar arithmetic

The existing matrix accuracy analysis uses a mathematical machine of scalar functions and
matrix routines. An Ops machine supplies those same functions. This adapter reuses that pure
analysis without importing or relating two program evaluators. Samplers and matrix routines
are explicit parameters, and exactness of literal one is an additional numerical hypothesis.

## Main results

* `NLAlib.Ops.Machine.toFloatMachine` exposes the same scalar functions to matrix mathematics.
* `NLAlib.Ops.StdModel.isArithAccurate_toFloatMachine` transfers standard-model bounds to the
  existing arithmetic accuracy interface, with zero underflow floor and any range bound.
-/

@[expose] public section

namespace NLAlib

namespace Ops.Machine

variable {K Su Sg : Type}

open Classical in
/-- A mathematical matrix machine using exactly the given Ops scalar functions. The natural
conversion is the decoded floor; negative words yield zero in this total mathematical function.
Actual program index queries retain their separate failure and bound checks. -/
noncomputable def toFloatMachine (M : Ops.Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → Su → K) (normal : Sg → K × K) : FloatMachine K Su Sg where
  zero := M.lit 0
  one := M.lit 1
  ofNat n := M.lit (n : ℚ)
  add := M.add
  sub := M.sub
  mul := M.mul
  div := M.div
  neg := M.neg
  le x y := decide (dec x ≤ dec y)
  toNat x := ⌊dec x⌋₊
  mm := mm
  qr := qr
  unif := unif
  normal := normal

end Ops.Machine

namespace Ops.StdModel

variable {K : Type} {M : Ops.Machine K} {dec : K → ℝ} {u Ω : ℝ}

/-- The unbounded-exponent standard model implies the existing matrix arithmetic contract at
floor zero, for any range. Literal one must decode exactly, and the supplied multiplication
routine satisfies its own numerical contract. No QR or sampler accuracy is inferred. -/
theorem isArithAccurate_toFloatMachine (h : Ops.StdModel u dec M)
    (hone : dec (M.lit 1) = 1) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (unif : K → ℝ → K) (normal : ℂ → K × K) (μ : ℕ → ℝ)
    (hmm : IsMatMulErr (decodeComplex dec) u 0 Ω μ mm) :
    (M.toFloatMachine dec mm qr unif normal).IsArithAccurate dec u 0 Ω μ where
  dec_zero := h.zero
  dec_one := hone
  ofNat n _ := by
    simpa only [Ops.Machine.toFloatMachine, Rat.cast_natCast,
      max_eq_left (abs_nonneg (n : ℝ)), abs_sub_comm] using h.lit (n : ℚ)
  add x y _ := by
    simpa only [Ops.Machine.toFloatMachine, max_eq_left (abs_nonneg (dec x + dec y)),
      abs_sub_comm] using h.add x y
  sub x y _ := by
    simpa only [Ops.Machine.toFloatMachine, max_eq_left (abs_nonneg (dec x - dec y)),
      abs_sub_comm] using h.sub x y
  mul x y _ := by
    simpa only [Ops.Machine.toFloatMachine, max_eq_left (abs_nonneg (dec x * dec y)),
      abs_sub_comm] using h.mul x y
  div x y hy _ := by
    simpa only [Ops.Machine.toFloatMachine, max_eq_left (abs_nonneg (dec x / dec y)),
      abs_sub_comm] using h.div x y hy
  dec_neg := h.neg
  le_iff x y := by simp [Ops.Machine.toFloatMachine]
  toNat_eq _ := rfl
  isMatMulErr := hmm

end Ops.StdModel

end NLAlib
