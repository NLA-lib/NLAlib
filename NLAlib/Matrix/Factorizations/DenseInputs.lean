/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.RoutineProblem
public import NLAlib.Matrix.Factorizations.GaussState

/-!
# Declared matrix inputs for dense factorizations

The only semantic input is a real square matrix. Its source buffer contains the existing
column-major scalar codec; factor and pivot-log buffers are uninitialized capacity. All
orders, including zero, are admitted. The acceptance conditions are mathematical properties
of the source matrix, never computed traces or assumed successful runs.

## Main results

* `NLAlib.DenseFactorization.luInputs`: the canonical nonzero-pivot LU domain.
* `NLAlib.DenseFactorization.rowPivotInputs`: the common all-input partial/scaled domain.
* `NLAlib.DenseFactorization.completePivotInputs`: the two-log all-input domain.
* `NLAlib.DenseFactorization.spdInputs`, `NLAlib.DenseFactorization.psdInputs` and
  `NLAlib.DenseFactorization.ldlInputs`: the square-root and diagonal-factor domains.
-/

@[expose] public section

namespace NLAlib.DenseFactorization

open Ops

/-- A single column-major matrix source and a fixed list of blank output capacities. The
admitted matrices are exactly `accepts`; the witness condition admits every matrix order. -/
def matrixInputs (lengths : List (ℕ → ℕ))
    (accepts : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ → Prop)
    (inhabited : ∀ n, ∃ A, accepts n A) : Inputs ℝ 1 (lengths.length + 1) where
  valid _ := True
  In d := Matrix (Fin (d 0)) (Fin (d 0)) ℝ
  accepts d := accepts (d 0)
  slot d := Fin.cases (.stored (Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)) id)
    (fun i => .blank (lengths.get i (d 0)))
  faithful d x y _ h := by
    have h0 := h 0
    change some ((Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)).encode x) =
      some ((Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)).encode y) at h0
    exact (Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)).encode_injective
      (Option.some.inj h0)
  admitted := ⟨fun _ => 0, trivial⟩
  inhabited d _ := inhabited (d 0)

/-- The canonical-pivot LU problem: the matrix is stored, two square factors are blank, and
all canonical elimination pivots must be nonzero. -/
def luInputs : Inputs ℝ 1 3 :=
  matrixInputs [fun n => n * n, fun n => n * n]
    (fun n A => ∀ k : Fin n, gaussState A k.val k k ≠ 0)
    (fun n => ⟨1, fun k => ne_of_gt
      ((Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef).gaussState_apply_self_pos k)⟩)

/-- Every real square matrix is admitted for partial or fixed-original-scale pivoting. The
blank outputs are two square factors and one absolute row-swap log. -/
def rowPivotInputs : Inputs ℝ 1 4 :=
  matrixInputs [fun n => n * n, fun n => n * n, id]
    (fun _ _ => True) (fun _ => ⟨0, trivial⟩)

/-- Every real square matrix is admitted for independent row/column pivoting. The blank
outputs are two square factors followed by the absolute row and column swap logs. -/
def completePivotInputs : Inputs ℝ 1 5 :=
  matrixInputs [fun n => n * n, fun n => n * n, id, id]
    (fun _ _ => True) (fun _ => ⟨0, trivial⟩)

/-- Positive-definite matrices with one blank square Cholesky factor. -/
def spdInputs : Inputs ℝ 1 2 :=
  matrixInputs [fun n => n * n] (fun _ A => A.PosDef)
    (fun _ => ⟨1, Matrix.PosDef.one⟩)

/-- Positive-semidefinite matrices, including singular ones, with one blank square factor. -/
def psdInputs : Inputs ℝ 1 2 :=
  matrixInputs [fun n => n * n] (fun _ A => A.PosSemidef)
    (fun _ => ⟨1, Matrix.PosDef.one.posSemidef⟩)

/-- Hermitian matrices with nonzero canonical elimination pivots. The blank outputs are the
unit lower factor and its scalar pivot diagonal; indefinite matrices are included. -/
def ldlInputs : Inputs ℝ 1 3 :=
  matrixInputs [fun n => n * n, id]
    (fun n A => A.IsHermitian ∧ ∀ k : Fin n, gaussState A k.val k k ≠ 0)
    (fun n => ⟨1, Matrix.PosDef.one.isHermitian, fun k => ne_of_gt
      ((Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef).gaussState_apply_self_pos k)⟩)

/-- The declared LU source and two blank square factors, including every uninitialized output
cell. -/
theorem bytes_luInputs (d : Fin 1 → ℕ) : luInputs.bytes d = 3 * d 0 * d 0 := by
  simp [luInputs, matrixInputs, Inputs.bytes, List.ofFn_succ, Codec.matrix,
    EntryCodec.scalar, Slot.len, Nat.mul_assoc]
  omega

/-- The declared row-pivot source, square factors and row log, including every uninitialized
output cell. -/
theorem bytes_rowPivotInputs (d : Fin 1 → ℕ) : rowPivotInputs.bytes d = 3 * d 0 * d 0 + d 0 := by
  simp [rowPivotInputs, matrixInputs, Inputs.bytes, List.ofFn_succ, Codec.matrix,
    EntryCodec.scalar, Slot.len, Nat.mul_assoc]
  omega

/-- The declared complete-pivot source, square factors and two logs, including every
uninitialized output cell. -/
theorem bytes_completePivotInputs (d :
    Fin 1 → ℕ) : completePivotInputs.bytes d = 3 * d 0 * d 0 + 2 * d 0 := by
  simp [completePivotInputs, matrixInputs, Inputs.bytes, List.ofFn_succ, Codec.matrix,
    EntryCodec.scalar, Slot.len, Nat.mul_assoc]
  omega

/-- The declared SPD source and blank square factor, including every uninitialized output cell. -/
theorem bytes_spdInputs (d : Fin 1 → ℕ) : spdInputs.bytes d = 2 * d 0 * d 0 := by
  simp [spdInputs, matrixInputs, Inputs.bytes, List.ofFn_succ, Codec.matrix,
    EntryCodec.scalar, Slot.len, Nat.mul_assoc]
  omega

/-- The declared PSD source and blank square factor, including every uninitialized output cell. -/
theorem bytes_psdInputs (d : Fin 1 → ℕ) : psdInputs.bytes d = 2 * d 0 * d 0 := by
  simp [psdInputs, matrixInputs, Inputs.bytes, List.ofFn_succ, Codec.matrix,
    EntryCodec.scalar, Slot.len, Nat.mul_assoc]
  omega

/-- The declared LDL source, square factor and scalar diagonal, including every uninitialized
output cell. -/
theorem bytes_ldlInputs (d : Fin 1 → ℕ) : ldlInputs.bytes d = 2 * d 0 * d 0 + d 0 := by
  simp [ldlInputs, matrixInputs, Inputs.bytes, List.ofFn_succ, Codec.matrix,
    EntryCodec.scalar, Slot.len, Nat.mul_assoc]
  omega

end NLAlib.DenseFactorization
