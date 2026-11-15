/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Operator

/-!
# Catalog: products with a matrix and with its adjoint

`NLAlib.Ops.OperatorPairOp.matvec [m, n] [x] [y]` applies a fixed `m × n` matrix to an input
block of length `n` and writes an output block of length `m` in a different buffer.
`NLAlib.Ops.OperatorPairOp.rmatvec [n, m] [x] [y]` applies its adjoint to an input block of
length `m` and writes an output block of length `n` in a different buffer. The dimensions of
`rmatvec` are those of the adjoint, so both operations have the operand shape and the admission
of `NLAlib.Ops.OperatorOp.matvec`, and their contracts are the relations
`NLAlib.Ops.matvecRel` and `NLAlib.Ops.matvecErrorRel` at the matrix and at its adjoint.

The pair is a separate group of operations: a program names the two products as two distinct
operations, and no model, profile or certificate of `NLAlib.Ops.OperatorOp` changes.

## Main definitions

* `NLAlib.Ops.OperatorPairOp`: the two operations.
* `NLAlib.Ops.IsExactMatvecPair`: both products are exact.
* `NLAlib.Ops.IsMatvecPair`: both products meet a normwise error allowance.

## Main results

* `NLAlib.Ops.Interp.Meets.matvecErrorRel_of_matvecRel`,
  `NLAlib.Ops.Interp.Meets.matvecErrorRel_mono`: the exact contract of one product gives every
  rounded one, and a rounded one is monotone in its allowance, for any operation name.
* `NLAlib.Ops.IsExactMatvecPair.isMatvecPair`, `NLAlib.Ops.IsMatvecPair.mono`: the same for the
  pair.
* `NLAlib.Ops.exists_isExactMatvecPair`: the exact real products realize the pair of contracts
  for every rectangular matrix.
-/

@[expose] public section

namespace NLAlib.Ops

open scoped Matrix

/-- Operations that apply a linear operator and its adjoint. -/
inductive OperatorPairOp where
  /-- `matvec [m, n] [x] [y]` applies the operator to an `n`-vector, producing an `m`-vector. -/
  | matvec
  /-- `rmatvec [n, m] [x] [y]` applies the adjoint of the operator to an `m`-vector, producing
  an `n`-vector. The dimensions are those of the adjoint. -/
  | rmatvec
  deriving DecidableEq

variable {K Op Tst : Type} [Inhabited K]

/-- An operation that meets the exact contract of the product with $\mathbf{A}$ meets the rounded
contract of that product at every allowance $\delta \ge 0$. -/
theorem Interp.Meets.matvecErrorRel_of_matvecRel {dec : K → ℝ} {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {I : Interp Op Tst K} {o : Op}
    (h : I.Meets .total o ((matvecRel dec A).spec (MatvecOperands m n)))
    {delta : ℝ} (hd : 0 ≤ delta) :
    I.Meets .total o ((matvecErrorRel dec A delta).spec (MatvecOperands m n)) := by
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

/-- An operation that meets the rounded contract of the product with $\mathbf{A}$ at the
allowance $\delta$ meets it at every allowance $\delta' \ge \delta$. -/
theorem Interp.Meets.matvecErrorRel_mono {dec : K → ℝ} {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {I : Interp Op Tst K} {o : Op} {delta delta' : ℝ}
    (h : I.Meets .total o ((matvecErrorRel dec A delta).spec (MatvecOperands m n)))
    (hd : delta ≤ delta') :
    I.Meets .total o ((matvecErrorRel dec A delta').spec (MatvecOperands m n)) := by
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

variable [Has OperatorPairOp Op]

/-- Both products meet their exact contracts: `matvec` is the product with $\mathbf{A}$ and
`rmatvec` the product with $\mathbf{A}^{\mathsf{H}}$, each with the relation and the admission of
the single product. -/
def IsExactMatvecPair (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (I : Interp Op Tst K) : Prop :=
  I.Meets .total (Has.inj OperatorPairOp.matvec) ((matvecRel dec A).spec (MatvecOperands m n)) ∧
    I.Meets .total (Has.inj OperatorPairOp.rmatvec)
      ((matvecRel dec Aᴴ).spec (MatvecOperands n m))

/-- Both products meet a normwise error contract on every input block: the error of `matvec` is
at most $\delta$ times the Euclidean norm of its input, and the error of `rmatvec` (the product
with $\mathbf{A}^{\mathsf{H}}$) at most $\delta'$ times the Euclidean norm of its input. The
allowances may include matrix norms chosen by the mathematical application. -/
def IsMatvecPair (dec : K → ℝ) {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (delta delta' : ℝ)
    (I : Interp Op Tst K) : Prop :=
  I.Meets .total (Has.inj OperatorPairOp.matvec)
      ((matvecErrorRel dec A delta).spec (MatvecOperands m n)) ∧
    I.Meets .total (Has.inj OperatorPairOp.rmatvec)
      ((matvecErrorRel dec Aᴴ delta').spec (MatvecOperands n m))

/-- The exact contract of the product with $\mathbf{A}$. -/
theorem IsExactMatvecPair.matvec {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Interp Op Tst K} (h : IsExactMatvecPair dec A I) :
    I.Meets .total (Has.inj OperatorPairOp.matvec) ((matvecRel dec A).spec (MatvecOperands m n)) :=
  h.1

/-- The exact contract of the product with $\mathbf{A}^{\mathsf{H}}$. -/
theorem IsExactMatvecPair.rmatvec {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Interp Op Tst K} (h : IsExactMatvecPair dec A I) :
    I.Meets .total (Has.inj OperatorPairOp.rmatvec)
      ((matvecRel dec Aᴴ).spec (MatvecOperands n m)) :=
  h.2

/-- The rounded contract of the product with $\mathbf{A}$. -/
theorem IsMatvecPair.matvec {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {delta delta' : ℝ} {I : Interp Op Tst K} (h : IsMatvecPair dec A delta delta' I) :
    I.Meets .total (Has.inj OperatorPairOp.matvec)
      ((matvecErrorRel dec A delta).spec (MatvecOperands m n)) :=
  h.1

/-- The rounded contract of the product with $\mathbf{A}^{\mathsf{H}}$. -/
theorem IsMatvecPair.rmatvec {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {delta delta' : ℝ} {I : Interp Op Tst K} (h : IsMatvecPair dec A delta delta' I) :
    I.Meets .total (Has.inj OperatorPairOp.rmatvec)
      ((matvecErrorRel dec Aᴴ delta').spec (MatvecOperands n m)) :=
  h.2

/-- An exact pair of products satisfies every pair of nonnegative normwise error allowances. -/
theorem IsExactMatvecPair.isMatvecPair {dec : K → ℝ} {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} {I : Interp Op Tst K} (h : IsExactMatvecPair dec A I)
    {delta delta' : ℝ} (hd : 0 ≤ delta) (hd' : 0 ≤ delta') :
    IsMatvecPair dec A delta delta' I :=
  ⟨h.1.matvecErrorRel_of_matvecRel hd, h.2.matvecErrorRel_of_matvecRel hd'⟩

/-- Widening the two error allowances preserves the declared pair of contracts. -/
theorem IsMatvecPair.mono {dec : K → ℝ} {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {I : Interp Op Tst K} {delta delta' eta eta' : ℝ} (h : IsMatvecPair dec A delta delta' I)
    (hd : delta ≤ eta) (hd' : delta' ≤ eta') : IsMatvecPair dec A eta eta' I :=
  ⟨h.1.matvecErrorRel_mono hd, h.2.matvecErrorRel_mono hd'⟩

/-- The block functions of the exact real products with $\mathbf{A}$ and with
$\mathbf{A}^{\mathsf{H}}$. -/
noncomputable def exactMatvecPairFn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    OperatorPairOp → BlockFn ℝ
  | .matvec => exactMatvecFn A
  | .rmatvec => exactMatvecFn Aᴴ

omit [Has OperatorPairOp Op] [Inhabited K] in
/-- The exact real products realize the pair of contracts at every pair of dimensions, including
matrices with no rows or no columns. -/
theorem exists_isExactMatvecPair {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ I : Interp OperatorPairOp Tst ℝ, IsExactMatvecPair id A I :=
  ⟨Interp.ofFns (exactMatvecPairFn A),
    (Interp.ofFns_isFn (exactMatvecPairFn A) .total .matvec AnyOperands).meets_matvec,
    (Interp.ofFns_isFn (exactMatvecPairFn A) .total .rmatvec AnyOperands).meets_matvec⟩

end NLAlib.Ops
