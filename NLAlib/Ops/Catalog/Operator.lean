/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import NLAlib.Ops.Catalog.Scalar

/-!
# Catalog: matrix-vector products

`NLAlib.Ops.OperatorOp.matvec [m, n] [x] [y]` applies a fixed `m × n` matrix to an input
block of length `n` and writes an output block of length `m` in a different buffer.

## Main results

* `NLAlib.Ops.IsExactMatvec` specifies the exact decoded product.
* `NLAlib.Ops.exists_isExactMatvec` witnesses the contract over the real numbers for every
  rectangular matrix, including matrices with no rows or no columns.
-/

@[expose] public section

namespace NLAlib.Ops

/-- Operations that apply a linear operator. -/
inductive OperatorOp where
  /-- `matvec [m, n] [x] [y]` applies the operator to an `n`-vector, producing an `m`-vector. -/
  | matvec
  deriving DecidableEq

variable {K Op Tst : Type} [Inhabited K]

/-- A block of `n` words, decoded as a vector. -/
def decv (dec : K → ℝ) (n : ℕ) (xs : List K) : Fin n → ℝ := fun i => dec (vec xs i)

/-- Decoding the list of entries of a real vector recovers that vector. -/
theorem decv_ofFn {n : ℕ} (v : Fin n → ℝ) : decv id n (List.ofFn v) = v :=
  funext fun i => by simp [decv, vec, List.getD_eq_getElem?_getD]

/-- The dimensions match the matrix and input and output use different buffers. -/
@[admNF] def MatvecOperands (m n : ℕ) : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => d = [m, n] ∧ ∀ x ∈ ins, ∀ y ∈ outs, x.1 ≠ y.1

/-- The output decodes to the matrix-vector product of the decoded input. -/
@[simps (attr := storeNF)]
def matvecRel (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BlockRel K where
  nd := 2
  inLens d := [d.getD 1 0]
  outLens d := [d.headD 0]
  rel _ X _ Y := match X, Y with
    | [xs], [ys] => decv dec m ys = A.mulVec (decv dec n xs)
    | _, _ => False

/-- The matrix-vector operation meets its exact contract. -/
def IsExactMatvec [Has OperatorOp Op] (dec : K → ℝ) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (I : Interp Op Tst K) : Prop :=
  I.Meets .total (Has.inj OperatorOp.matvec) ((matvecRel dec A).spec (MatvecOperands m n))

/-- The block function for the exact real matrix-vector product. -/
noncomputable def exactMatvecFn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BlockFn ℝ :=
  .of1 2 (·.getD 1 0) (·.headD 0) fun d xs =>
    if d = [m, n] then some (List.ofFn (A.mulVec (decv id n xs))) else none

/-- Interpreting an operation as the exact real product meets the relational contract. -/
theorem Interp.IsFn.meets_matvec {I : Interp Op Tst ℝ} {o : Op} {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} (h : I.IsFn .total o (exactMatvecFn A) AnyOperands) :
    I.Meets .total o ((matvecRel id A).spec (MatvecOperands m n)) := by
  refine h.meets_rel (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) ?_
  intro d w X μ ins outs hnd hw hadm hr hdom
  obtain ⟨rfl, -⟩ := hadm
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hr
  exact ⟨[List.ofFn (A.mulVec (decv id n xs))], by simp [exactMatvecFn, BlockFn.of1],
    by simp [matvecRel], decv_ofFn _⟩

/-- The exact real product realizes the matrix-vector contract at every pair of dimensions. -/
theorem exists_isExactMatvec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ I : Interp OperatorOp Tst ℝ, IsExactMatvec id A I := by
  let F : OperatorOp → BlockFn ℝ := fun _ => exactMatvecFn A
  exact ⟨Interp.ofFns F, (Interp.ofFns_isFn F .total .matvec AnyOperands).meets_matvec⟩

omit [Inhabited K] in
/-- Exact real scalar arithmetic and the rectangular matrix-vector contract can be realized
jointly on any signature where their operation groups are apart. -/
theorem exists_isScalar_isExactMatvec [Has ScalarOp Op] [Has OperatorOp Op]
    [Apart ScalarOp OperatorOp Op] {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ I : Interp Op Tst ℝ, IsScalar exactMachine I ∧ IsExactMatvec id A I := by
  let F : Op → BlockFn ℝ := fun o =>
    match Has.proj (G := ScalarOp) o with
    | some a => exactMachine.fn a
    | none => exactMatvecFn A
  have hS : IsScalar exactMachine (Interp.ofFns F : Interp Op Tst ℝ) :=
    isScalar_ofFns _ _ fun a => by simp [F]
  have hA := Interp.ofFns_isFn (Tst := Tst) F .total (Has.inj OperatorOp.matvec) AnyOperands
  have hf : F (Has.inj OperatorOp.matvec) = exactMatvecFn A := by simp [F]
  rw [hf] at hA
  exact ⟨Interp.ofFns F, hS, hA.meets_matvec⟩

end NLAlib.Ops
