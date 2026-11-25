/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.DenseInputs

/-!
# Declared matrix inputs for clipped blocked factorizations

Dimensions are matrix order, a positive symbolic block size, and its exact ceiling block
count. The only semantic datum is the original real matrix; output buffers are blank
capacity. There is an admitted input at every valid dimension tuple, including order zero,
nondividing panels and blocks larger than the order. No computed factor or execution trace
occurs in the domain.

## Main results

* `NLAlib.DenseFactorization.blockedLuInputs`: the original nonzero Gaussian-pivot domain.
* `NLAlib.DenseFactorization.blockedSpdInputs`: the positive-definite blocked domain.
-/

@[expose] public section

namespace NLAlib.DenseFactorization

open Ops

/-- Extend an order-indexed matrix domain with positive block size and exact ceiling count.
The source codec and blank output slots are unchanged. -/
def blockedMatrixInputs (lengths : List (ℕ → ℕ))
    (accepts : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ → Prop)
    (inhabited : ∀ n, ∃ A, accepts n A) : Inputs ℝ 3 (lengths.length + 1) where
  valid d := 0 < d 1 ∧ d 2 = (d 0 + d 1 - 1) / d 1
  In d := (matrixInputs lengths accepts inhabited).In (fun _ => d 0)
  accepts d := (matrixInputs lengths accepts inhabited).accepts (fun _ => d 0)
  slot d := (matrixInputs lengths accepts inhabited).slot (fun _ => d 0)
  faithful d := (matrixInputs lengths accepts inhabited).faithful (fun _ => d 0)
  admitted := ⟨![0, 1, 0], by simp⟩
  inhabited d _ := inhabited (d 0)

/-- One matrix and two blank square factors, with nonzero original Gaussian pivots and valid
positive block controls. In particular the empty matrix is admitted with block count zero. -/
def blockedLuInputs : Inputs ℝ 3 3 :=
  blockedMatrixInputs [fun n => n * n, fun n => n * n]
    (fun n A => ∀ k : Fin n, gaussState A k.val k k ≠ 0)
    (fun n => ⟨1, fun k => ne_of_gt
      ((Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef).gaussState_apply_self_pos k)⟩)

/-- One positive-definite source matrix and one blank square factor, with positive symbolic
block size and its exact ceiling block count. -/
def blockedSpdInputs : Inputs ℝ 3 2 :=
  blockedMatrixInputs [fun n => n * n] (fun _ A => A.PosDef)
    (fun _ => ⟨1, Matrix.PosDef.one⟩)

/-- The blocked LU caller retains three full square matrices, including both blank outputs. -/
theorem bytes_blockedLuInputs (d : Fin 3 → ℕ) :
    blockedLuInputs.bytes d = 3 * d 0 * d 0 := by
  simp [blockedLuInputs, blockedMatrixInputs, matrixInputs, Inputs.bytes, List.ofFn_succ,
    Codec.matrix, EntryCodec.scalar, Slot.len, Nat.mul_assoc]
  omega

/-- The blocked Cholesky caller retains its source and the complete blank square output. -/
theorem bytes_blockedSpdInputs (d : Fin 3 → ℕ) :
    blockedSpdInputs.bytes d = 2 * d 0 * d 0 := by
  simp [blockedSpdInputs, blockedMatrixInputs, matrixInputs, Inputs.bytes, List.ofFn_succ,
    Codec.matrix, EntryCodec.scalar, Slot.len, Nat.mul_assoc]
  omega

end NLAlib.DenseFactorization
