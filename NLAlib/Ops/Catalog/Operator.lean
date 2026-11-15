/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.InnerProductSpace.PiL2
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

open scoped Matrix

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

/-- Re-encoding a decoded real block of the declared length recovers its actual words. -/
theorem ofFn_decv {n : ℕ} {xs : List ℝ} (hx : xs.length = n) :
    List.ofFn (decv id n xs) = xs := by
  apply List.ext_getElem
  · simpa using hx.symm
  · intro i hi hi'
    simp [decv, vec, List.getD_eq_getElem?_getD, hi']

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

/-- Matrix-vector error bounded in Euclidean norm by an absolute operator allowance.
The allowance may include matrix norms chosen by the mathematical application. -/
@[simps (attr := storeNF)]
def matvecErrorRel (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (delta : ℝ) : BlockRel K where
  nd := 2
  inLens d := [d.getD 1 0]
  outLens d := [d.headD 0]
  rel _ X _ Y := match X, Y with
    | [xs], [ys] => ‖WithLp.toLp 2 (A *ᵥ decv dec n xs - decv dec m ys)‖ ≤
        delta * ‖WithLp.toLp 2 (decv dec n xs)‖
    | _, _ => False

/-- A rounded matrix-vector call satisfies its normwise error contract on every input block. -/
def IsMatvec [Has OperatorOp Op] (dec : K → ℝ) {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (delta : ℝ) (I : Interp Op Tst K) : Prop :=
  I.Meets .total (Has.inj OperatorOp.matvec)
    ((matvecErrorRel dec A delta).spec (MatvecOperands m n))

/-- An exact matvec satisfies every nonnegative normwise error allowance. -/
theorem IsExactMatvec.isMatvec [Has OperatorOp Op] {dec : K → ℝ} {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {I : Interp Op Tst K} (h : IsExactMatvec dec A I)
    {delta : ℝ} (hd : 0 ≤ delta) : IsMatvec dec A delta I := by
  refine h.mono (fun _ _ _ _ _ hp => hp) ?_
  rintro d ins outs τ μ μ' _ ⟨xs, hr, hz, ys, hlen, hrel, rfl⟩
  refine ⟨xs, hr, hz, ys, hlen, ?_, rfl⟩
  cases xs with
  | nil => simp [matvecRel] at hrel
  | cons x xs => cases xs with
    | cons _ _ => simp [matvecRel] at hrel
    | nil => cases ys with
      | nil => simp [matvecRel] at hrel
      | cons y ys => cases ys with
        | cons _ _ => simp [matvecRel] at hrel
        | nil =>
          change ‖WithLp.toLp 2 (A *ᵥ decv dec n x - decv dec m y)‖ ≤ _
          rw [show decv dec m y = A *ᵥ decv dec n x from hrel]
          simpa only [sub_self, WithLp.toLp_zero, norm_zero] using
            mul_nonneg hd (norm_nonneg (WithLp.toLp 2 (decv dec n x)))

/-- Widening a matvec error allowance preserves its declared contract. -/
theorem IsMatvec.mono [Has OperatorOp Op] {dec : K → ℝ} {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {I : Interp Op Tst K} {delta delta' : ℝ}
    (h : IsMatvec dec A delta I) (hd : delta ≤ delta') : IsMatvec dec A delta' I := by
  refine Interp.Meets.mono h (fun _ _ _ _ _ hp => hp) ?_
  rintro d ins outs τ μ μ' _ ⟨xs, hr, hz, ys, hlen, hrel, rfl⟩
  refine ⟨xs, hr, hz, ys, hlen, ?_, rfl⟩
  cases xs with
  | nil => simp [matvecErrorRel] at hrel
  | cons x xs => cases xs with
    | cons _ _ => simp [matvecErrorRel] at hrel
    | nil => cases ys with
      | nil => simp [matvecErrorRel] at hrel
      | cons y ys => cases ys with
        | cons _ _ => simp [matvecErrorRel] at hrel
        | nil => exact hrel.trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))

/-- Decoding a list made from a word vector commutes with its componentwise decoding. -/
theorem decv_ofFn_decode {n : ℕ} (dec : K → ℝ) (v : Fin n → K) :
    decv dec n (List.ofFn v) = fun i => dec (v i) := by
  funext i
  simp [decv, vec, List.getD_eq_getElem?_getD]

/-- A matrix-vector kernel on word vectors, exposed as the core's block-function primitive. -/
def matvecFn {m n : ℕ} (kernel : (Fin n → K) → Fin m → K) : BlockFn K :=
  .of1 2 (·.getD 1 0) (·.headD 0) fun d xs =>
    if d = [m, n] then some (List.ofFn (kernel (fun i => vec xs i))) else none

/-- A proved word-kernel accuracy bound supplies the declared rounded matvec contract.
No memory/execution theorem is required from the backend author. -/
theorem Interp.IsFn.meets_matvec_error_of_admission {I : Interp Op Tst K} {o : Op} {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {dec : K → ℝ} {delta : ℝ}
    {kernel : (Fin n → K) → Fin m → K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    (h : I.IsFn .total o (matvecFn kernel) adm)
    (hadm : ∀ d ins outs, MatvecOperands m n d ins outs → adm d ins outs)
    (hk : ∀ v : Fin n → K,
      ‖WithLp.toLp 2 (A *ᵥ (fun i => dec (v i)) - (fun i => dec (kernel v i)))‖ ≤
        delta * ‖WithLp.toLp 2 (fun i => dec (v i))‖) :
    I.Meets .total o ((matvecErrorRel dec A delta).spec (MatvecOperands m n)) := by
  refine h.meets_rel hadm rfl rfl (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) ?_
  intro d w X μ ins outs hnd hw hadm hr hdom
  rcases hadm with ⟨rfl, _⟩
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hr
  refine ⟨[List.ofFn (kernel (fun i => vec xs i))], by simp [matvecFn, BlockFn.of1],
    by simp [matvecErrorRel], ?_⟩
  change ‖WithLp.toLp 2 (A *ᵥ decv dec n xs -
    decv dec m (List.ofFn (kernel (fun i => vec xs i))))‖ ≤
      delta * ‖WithLp.toLp 2 (decv dec n xs)‖
  rw [decv_ofFn_decode]
  exact hk (fun i => vec xs i)

/-- A word-kernel accuracy bound transfers a functional primitive with unrestricted operand
admission to the shaped rounded matrix-vector contract. -/
theorem Interp.IsFn.meets_matvec_error {I : Interp Op Tst K} {o : Op} {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {dec : K → ℝ} {delta : ℝ}
    {kernel : (Fin n → K) → Fin m → K}
    (h : I.IsFn .total o (matvecFn kernel) AnyOperands)
    (hk : ∀ v : Fin n → K,
      ‖WithLp.toLp 2 (A *ᵥ (fun i => dec (v i)) - (fun i => dec (kernel v i)))‖ ≤
        delta * ‖WithLp.toLp 2 (fun i => dec (v i))‖) :
    I.Meets .total o ((matvecErrorRel dec A delta).spec (MatvecOperands m n)) :=
  h.meets_matvec_error_of_admission (fun _ _ _ _ => trivial) hk

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
/-- Any real scalar machine and the exact rectangular matrix-vector contract can be realized
jointly on any signature where their operation groups are apart. -/
theorem exists_isScalar_isExactMatvec_ofMachine [Has ScalarOp Op] [Has OperatorOp Op]
    [Apart ScalarOp OperatorOp Op] (M : Machine ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ I : Interp Op Tst ℝ, IsScalar M I ∧ IsExactMatvec id A I := by
  let F : Op → BlockFn ℝ := fun o =>
    match Has.proj (G := ScalarOp) o with
    | some a => M.fn a
    | none => exactMatvecFn A
  have hS : IsScalar M (Interp.ofFns F : Interp Op Tst ℝ) :=
    isScalar_ofFns _ _ fun a => by simp [F]
  have hA := Interp.ofFns_isFn (Tst := Tst) F .total (Has.inj OperatorOp.matvec) AnyOperands
  have hf : F (Has.inj OperatorOp.matvec) = exactMatvecFn A := by simp [F]
  rw [hf] at hA
  exact ⟨Interp.ofFns F, hS, hA.meets_matvec⟩


omit [Inhabited K] in
/-- Exact real scalar arithmetic and the rectangular matrix-vector contract can be realized
jointly on any signature where their operation groups are apart. -/
theorem exists_isScalar_isExactMatvec [Has ScalarOp Op] [Has OperatorOp Op]
    [Apart ScalarOp OperatorOp Op] {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ I : Interp Op Tst ℝ, IsScalar exactMachine I ∧ IsExactMatvec id A I :=
  exists_isScalar_isExactMatvec_ofMachine exactMachine A

end NLAlib.Ops
