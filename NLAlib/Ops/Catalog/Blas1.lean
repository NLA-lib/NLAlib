/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.Scalar

/-!
# Catalog: level-1 vector operations

The group `NLAlib.Ops.Blas1Op`: `sum`, `dot`, `axpy`, `nrm2`, `scal`, `copy`, on contiguous
blocks. Each has an error predicate on decoded values (mathematics: `NLAlib.Ops.IsSumErr`,
`NLAlib.Ops.IsDotErr`, `NLAlib.Ops.IsAxpyErr`, `NLAlib.Ops.IsNrm2Err`, `NLAlib.Ops.IsScalErr`) and
a relational contract in operand form (`NLAlib.Ops.sumRel`, …). The accuracy parameters are one
record `NLAlib.Ops.Blas1Err`; the contract set is `NLAlib.Ops.IsBlas1 dec ε ok`, where `ok n`
says which vector lengths the contracts cover (all of them for a loop; those within the depth
budget for a recursive implementation).

An algorithm states its theorem against `IsBlas1` (and `IsScalar` if it calls scalar
operations), never against an implementation.
-/

@[expose] public section

namespace NLAlib.Ops

/-- The level-1 vector operations. -/
inductive Blas1Op where
  /-- `sum [n] [x] [z]`: the sum of a block of length `n`, in the cell `z`. -/
  | sum
  /-- `dot [n] [x, y] [z]`: the dot product of two blocks of length `n`, in the cell `z`. -/
  | dot
  /-- `axpy [n] [α, x, y] [y]`: `y := y + α x` on blocks of length `n`, in place. -/
  | axpy
  /-- `nrm2 [n] [x] [z]`: the Euclidean norm of a block of length `n`, in the cell `z`. -/
  | nrm2
  /-- `scal [n] [α, x] [x]`: `x := x / α` on a block of length `n`, in place. -/
  | scal
  /-- `copy [n] [x] [y]`: `y := x` on blocks of length `n`. -/
  | copy
  deriving DecidableEq

variable {K Op Tst : Type}

/-! ### Mathematics: the error predicates -/

/-- `v` is the sum of `x` up to the relative error `e`. -/
def IsSumErr (dec : K → ℝ) (e : ℝ) (n : ℕ) (x : ℕ → K) (v : K) : Prop :=
  |dec v - ∑ k ∈ Finset.range n, dec (x k)| ≤ e * ∑ k ∈ Finset.range n, |dec (x k)|

/-- `v` is the dot product of `x` and `y` up to the relative error `e`. -/
def IsDotErr (dec : K → ℝ) (e : ℝ) (n : ℕ) (x y : ℕ → K) (v : K) : Prop :=
  |dec v - ∑ k ∈ Finset.range n, dec (x k) * dec (y k)| ≤
    e * ∑ k ∈ Finset.range n, |dec (x k) * dec (y k)|

/-- `z` is `y + α x` up to the componentwise relative error `e`. -/
def IsAxpyErr (dec : K → ℝ) (e : ℝ) (n : ℕ) (al : K) (x y z : ℕ → K) : Prop :=
  ∀ i < n, |dec (z i) - (dec (y i) + dec al * dec (x i))| ≤
    e * (|dec (y i)| + |dec al * dec (x i)|)

/-- `ν` is the Euclidean norm of `x`: a square root, up to `es`, of a sum of squares `σ` computed
up to `ed`. -/
def IsNrm2Err (dec : K → ℝ) (ed es : ℝ) (n : ℕ) (x : ℕ → K) (ν : K) : Prop :=
  ∃ σ, IsDotErr dec ed n x x σ ∧ (0 ≤ dec σ → |dec ν - √(dec σ)| ≤ es * √(dec σ))

/-- `z` is `x / α` up to the componentwise relative error `e`. -/
def IsScalErr (dec : K → ℝ) (e : ℝ) (n : ℕ) (al : K) (x z : ℕ → K) : Prop :=
  ∀ i < n, |dec (z i) - dec (x i) / dec al| ≤ e * |dec (x i) / dec al|

theorem IsDotErr.congr {dec : K → ℝ} {e : ℝ} {n : ℕ} {a b a' b' : ℕ → K} {v : K}
    (h : IsDotErr dec e n a b v) (ha : ∀ i < n, a i = a' i) (hb : ∀ i < n, b i = b' i) :
    IsDotErr dec e n a' b' v := by
  have h1 : ∀ i ∈ Finset.range n, dec (a i) * dec (b i) = dec (a' i) * dec (b' i) :=
    fun i hi => by rw [ha i (Finset.mem_range.mp hi), hb i (Finset.mem_range.mp hi)]
  have h2 : ∀ i ∈ Finset.range n, |dec (a i) * dec (b i)| = |dec (a' i) * dec (b' i)| :=
    fun i hi => by rw [h1 i hi]
  unfold IsDotErr at h ⊢
  rwa [← Finset.sum_congr rfl h1, ← Finset.sum_congr rfl h2]

theorem IsAxpyErr.congr {dec : K → ℝ} {e : ℝ} {n : ℕ} {al : K} {x y z x' y' z' : ℕ → K}
    (h : IsAxpyErr dec e n al x y z) (hx : ∀ i < n, x i = x' i) (hy : ∀ i < n, y i = y' i)
    (hz : ∀ i < n, z i = z' i) : IsAxpyErr dec e n al x' y' z' := by
  intro i hi
  rw [← hx i hi, ← hy i hi, ← hz i hi]
  exact h i hi

/-! ### Contracts -/

/-- Admitted operands of an operation that writes a result apart from its inputs: the length is
covered and the inputs are in other buffers than the output. -/
def OutApart (ok : ℕ → Prop) : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop :=
  fun d ins z => ok (d.headD 0) ∧ ∀ a ∈ ins, a.1 ≠ z.1

/-- Admitted operands of an operation that updates its last input in place: the length is
covered, the last input is the output, the others are in other buffers. -/
def InPlace (ok : ℕ → Prop) : List ℕ → List (ℕ × ℕ) → ℕ × ℕ → Prop :=
  fun d ins z => ok (d.headD 0) ∧ ∃ pre, ins = pre ++ [z] ∧ ∀ a ∈ pre, a.1 ≠ z.1

variable [Inhabited K]

/-- `sum`: one block of length `n` to one cell. -/
def sumRel (dec : K → ℝ) (e : ℕ → ℝ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0]
  outLen _ := 1
  rel d X ys := match X, ys with
    | [xs], [v] => IsSumErr dec (e (d.headD 0)) (d.headD 0) (vec xs) v
    | _, _ => False

/-- `dot`: two blocks of length `n` to one cell. -/
def dotRel (dec : K → ℝ) (e : ℕ → ℝ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0, d.headD 0]
  outLen _ := 1
  rel d X ys := match X, ys with
    | [xs, zs], [v] => IsDotErr dec (e (d.headD 0)) (d.headD 0) (vec xs) (vec zs) v
    | _, _ => False

/-- `axpy`: a cell and two blocks of length `n` to the second block. -/
def axpyRel (dec : K → ℝ) (e : ℝ) : BlockRel K where
  nd := 1
  inLens d := [1, d.headD 0, d.headD 0]
  outLen d := d.headD 0
  rel d X zs := match X with
    | [[a], xs, ys] => IsAxpyErr dec e (d.headD 0) a (vec xs) (vec ys) (vec zs)
    | _ => False

/-- `nrm2`: one block of length `n` to one cell. -/
def nrm2Rel (dec : K → ℝ) (ed : ℕ → ℝ) (es : ℝ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0]
  outLen _ := 1
  rel d X ys := match X, ys with
    | [xs], [v] => IsNrm2Err dec (ed (d.headD 0)) es (d.headD 0) (vec xs) v
    | _, _ => False

/-- `scal`: a cell and a block of length `n` to the block. -/
def scalRel (dec : K → ℝ) (e : ℝ) : BlockRel K where
  nd := 1
  inLens d := [1, d.headD 0]
  outLen d := d.headD 0
  rel d X zs := match X with
    | [[a], xs] => IsScalErr dec e (d.headD 0) a (vec xs) (vec zs)
    | _ => False

omit [Inhabited K] in
/-- `copy`: a block of length `n` to a block; exact. -/
def copyRel : BlockRel K where
  nd := 1
  inLens d := [d.headD 0]
  outLen d := d.headD 0
  rel _ X zs := X = [zs]

omit [Inhabited K] in
@[storeNF] theorem headD_singleton (n d : ℕ) : [n].headD d = n := rfl

@[storeNF] theorem sumRel_inLens (dec : K → ℝ) (e : ℕ → ℝ) (d : List ℕ) :
    (sumRel dec e).inLens d = [d.headD 0] := rfl

@[storeNF] theorem dotRel_inLens (dec : K → ℝ) (e : ℕ → ℝ) (d : List ℕ) :
    (dotRel dec e).inLens d = [d.headD 0, d.headD 0] := rfl

@[storeNF] theorem axpyRel_inLens (dec : K → ℝ) (e : ℝ) (d : List ℕ) :
    (axpyRel dec e).inLens d = [1, d.headD 0, d.headD 0] := rfl

@[storeNF] theorem axpyRel_outLen (dec : K → ℝ) (e : ℝ) (d : List ℕ) :
    (axpyRel dec e).outLen d = d.headD 0 := rfl

@[storeNF] theorem nrm2Rel_inLens (dec : K → ℝ) (ed : ℕ → ℝ) (es : ℝ) (d : List ℕ) :
    (nrm2Rel dec ed es).inLens d = [d.headD 0] := rfl

@[storeNF] theorem scalRel_inLens (dec : K → ℝ) (e : ℝ) (d : List ℕ) :
    (scalRel dec e).inLens d = [1, d.headD 0] := rfl

@[storeNF] theorem scalRel_outLen (dec : K → ℝ) (e : ℝ) (d : List ℕ) :
    (scalRel dec e).outLen d = d.headD 0 := rfl

omit [Inhabited K] in
@[storeNF] theorem copyRel_inLens (d : List ℕ) : (copyRel (K := K)).inLens d = [d.headD 0] := rfl

omit [Inhabited K] in
@[storeNF] theorem copyRel_outLen (d : List ℕ) : (copyRel (K := K)).outLen d = d.headD 0 := rfl

/-- **The accuracy parameters of the level-1 operations.** -/
structure Blas1Err where
  /-- `sum`: relative to the sum of absolute values, as a function of the length. -/
  sum : ℕ → ℝ
  /-- `dot`: relative to `|x|ᵀ|y|`, as a function of the length. -/
  dot : ℕ → ℝ
  /-- `axpy`: componentwise. -/
  axpy : ℝ
  /-- The square root in `nrm2`. -/
  sqrt : ℝ
  /-- `scal`: componentwise. -/
  scal : ℝ

/-- **The contracts of the level-1 operations** at the accuracy parameters `ε`, for the vector
lengths `ok`. -/
structure IsBlas1 [Has Blas1Op Op] (dec : K → ℝ) (ε : Blas1Err) (ok : ℕ → Prop)
    (J : Interp Op Tst K) : Prop where
  /-- `sum`. -/
  sum : J.Meets .total (Has.inj Blas1Op.sum) ((sumRel dec ε.sum).spec (OutApart ok))
  /-- `dot`. -/
  dot : J.Meets .total (Has.inj Blas1Op.dot) ((dotRel dec ε.dot).spec (OutApart ok))
  /-- `axpy`. -/
  axpy : J.Meets .total (Has.inj Blas1Op.axpy) ((axpyRel dec ε.axpy).spec (InPlace ok))
  /-- `nrm2`. -/
  nrm2 : J.Meets .total (Has.inj Blas1Op.nrm2) ((nrm2Rel dec ε.dot ε.sqrt).spec (OutApart ok))
  /-- `scal`. -/
  scal : J.Meets .total (Has.inj Blas1Op.scal) ((scalRel dec ε.scal).spec (InPlace ok))
  /-- `copy`. -/
  copy : J.Meets .total (Has.inj Blas1Op.copy) ((copyRel (K := K)).spec (OutApart ok))

/-- The contract of `sum` alone: what the other level-1 operations are implemented over. -/
def IsSum [Has Blas1Op Op] (dec : K → ℝ) (e : ℕ → ℝ) (ok : ℕ → Prop) (J : Interp Op Tst K) :
    Prop :=
  J.Meets .total (Has.inj Blas1Op.sum) ((sumRel dec e).spec (OutApart ok))

end NLAlib.Ops
