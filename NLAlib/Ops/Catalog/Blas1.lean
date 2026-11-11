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

## Main results

* `NLAlib.Ops.IsBlas1`: the contract set of the level-1 operations.
* `NLAlib.Ops.IsExactBlas1`: the same operations with exact decoded equations.
* `NLAlib.Ops.IsDotErr.congr`, `NLAlib.Ops.IsAxpyErr.congr`: the error predicates read their
  vectors only below the length.
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

/-- `z` is `x / α` up to the componentwise relative error `e`, when `α` is not zero. Nothing is
said of a division by zero. -/
def IsScalErr (dec : K → ℝ) (e : ℝ) (n : ℕ) (al : K) (x z : ℕ → K) : Prop :=
  dec al ≠ 0 → ∀ i < n, |dec (z i) - dec (x i) / dec al| ≤ e * |dec (x i) / dec al|

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
covered and the inputs are in other buffers than the outputs. -/
@[admNF] def OutApart (ok : ℕ → Prop) : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => ok (d.headD 0) ∧ ∀ a ∈ ins, ∀ z ∈ outs, a.1 ≠ z.1

/-- Admitted operands of an operation that updates its last input in place: the length is
covered, the output is the last input, the other inputs are in other buffers. -/
@[admNF] def InPlace (ok : ℕ → Prop) : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => ok (d.headD 0) ∧ outs = ins.getLast?.toList ∧
    ∀ a ∈ ins.dropLast, ∀ z ∈ outs, a.1 ≠ z.1

variable [Inhabited K]

/-- `sum`: one block of length `n` to one cell. -/
@[simps (attr := storeNF)]
def sumRel (dec : K → ℝ) (e : ℕ → ℝ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0]
  outLens _ := [1]
  rel d X _ ys := match X, ys with
    | [xs], [[v]] => IsSumErr dec (e (d.headD 0)) (d.headD 0) (vec xs) v
    | _, _ => False

/-- `dot`: two blocks of length `n` to one cell. -/
@[simps (attr := storeNF)]
def dotRel (dec : K → ℝ) (e : ℕ → ℝ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0, d.headD 0]
  outLens _ := [1]
  rel d X _ ys := match X, ys with
    | [xs, zs], [[v]] => IsDotErr dec (e (d.headD 0)) (d.headD 0) (vec xs) (vec zs) v
    | _, _ => False

/-- `axpy`: a cell and two blocks of length `n` to the second block. -/
@[simps (attr := storeNF)]
def axpyRel (dec : K → ℝ) (e : ℝ) : BlockRel K where
  nd := 1
  inLens d := [1, d.headD 0, d.headD 0]
  outLens d := [d.headD 0]
  rel d X _ ys := match X, ys with
    | [[a], xs, ys], [zs] => IsAxpyErr dec e (d.headD 0) a (vec xs) (vec ys) (vec zs)
    | _, _ => False

/-- `nrm2`: one block of length `n` to one cell. -/
@[simps (attr := storeNF)]
def nrm2Rel (dec : K → ℝ) (ed : ℕ → ℝ) (es : ℝ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0]
  outLens _ := [1]
  rel d X _ ys := match X, ys with
    | [xs], [[v]] => IsNrm2Err dec (ed (d.headD 0)) es (d.headD 0) (vec xs) v
    | _, _ => False

/-- `scal`: a cell and a block of length `n` to the block. -/
@[simps (attr := storeNF)]
def scalRel (dec : K → ℝ) (e : ℝ) : BlockRel K where
  nd := 1
  inLens d := [1, d.headD 0]
  outLens d := [d.headD 0]
  rel d X _ ys := match X, ys with
    | [[a], xs], [zs] => IsScalErr dec e (d.headD 0) a (vec xs) (vec zs)
    | _, _ => False

omit [Inhabited K] in
/-- `copy`: a block of length `n` to a block; exact. -/
@[simps (attr := storeNF)]
def copyRel : BlockRel K where
  nd := 1
  inLens d := [d.headD 0]
  outLens d := [d.headD 0]
  rel _ X _ ys := ys = X

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

/-! ### Exact contracts -/

/-- `sum` computes the sum of the decoded entries. -/
@[simps (attr := storeNF)]
def sumExactRel (dec : K → ℝ) : BlockRel K :=
  { sumRel dec (fun _ => 0) with
    rel := fun d X _ Y => match X, Y with
      | [xs], [[v]] => dec v = ∑ i ∈ Finset.range (d.headD 0), dec (vec xs i)
      | _, _ => False }

/-- `dot` computes the dot product of the decoded blocks. -/
@[simps (attr := storeNF)]
def dotExactRel (dec : K → ℝ) : BlockRel K :=
  { dotRel dec (fun _ => 0) with
    rel := fun d X _ Y => match X, Y with
      | [xs, ys], [[v]] =>
        dec v = ∑ i ∈ Finset.range (d.headD 0), dec (vec xs i) * dec (vec ys i)
      | _, _ => False }

/-- `axpy` computes the decoded update `y + a x`. -/
@[simps (attr := storeNF)]
def axpyExactRel (dec : K → ℝ) : BlockRel K :=
  { axpyRel dec 0 with
    rel := fun d X _ Y => match X, Y with
      | [[a], xs, ys], [zs] =>
        ∀ i < d.headD 0, dec (vec zs i) = dec (vec ys i) + dec a * dec (vec xs i)
      | _, _ => False }

/-- `nrm2` computes the Euclidean norm of the decoded block. -/
@[simps (attr := storeNF)]
def nrm2ExactRel (dec : K → ℝ) : BlockRel K :=
  { nrm2Rel dec (fun _ => 0) 0 with
    rel := fun d X _ Y => match X, Y with
      | [xs], [[v]] => dec v = √(∑ i ∈ Finset.range (d.headD 0), dec (vec xs i) ^ 2)
      | _, _ => False }

/-- `scal` divides each decoded entry by the decoded divisor when that divisor is nonzero. -/
@[simps (attr := storeNF)]
def scalExactRel (dec : K → ℝ) : BlockRel K :=
  { scalRel dec 0 with
    rel := fun d X _ Y => match X, Y with
      | [[a], xs], [zs] =>
        dec a ≠ 0 → ∀ i < d.headD 0, dec (vec zs i) = dec (vec xs i) / dec a
      | _, _ => False }

/-- **Exact BLAS1 contracts**: the level-1 operations compute their exact decoded values at the
admitted lengths. -/
structure IsExactBlas1 [Has Blas1Op Op] (dec : K → ℝ) (ok : ℕ → Prop)
    (J : Interp Op Tst K) : Prop where
  /-- `sum`. -/
  sum : J.Meets .total (Has.inj Blas1Op.sum) ((sumExactRel dec).spec (OutApart ok))
  /-- `dot`. -/
  dot : J.Meets .total (Has.inj Blas1Op.dot) ((dotExactRel dec).spec (OutApart ok))
  /-- `axpy`. -/
  axpy : J.Meets .total (Has.inj Blas1Op.axpy) ((axpyExactRel dec).spec (InPlace ok))
  /-- `nrm2`. -/
  nrm2 : J.Meets .total (Has.inj Blas1Op.nrm2) ((nrm2ExactRel dec).spec (OutApart ok))
  /-- `scal`. -/
  scal : J.Meets .total (Has.inj Blas1Op.scal) ((scalExactRel dec).spec (InPlace ok))
  /-- `copy`. -/
  copy : J.Meets .total (Has.inj Blas1Op.copy) ((copyRel (K := K)).spec (OutApart ok))

omit [Inhabited K] in
private theorem meets_replace_rel {J : Interp Op Tst K} {o : Op} {R : BlockRel K}
    {adm : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop}
    {rel : List ℕ → List (List K) → List K → List (List K) → Prop}
    (h : J.Meets .total o (R.spec adm))
    (hrel : ∀ d X w Y, R.rel d X w Y → rel d X w Y) :
    J.Meets .total o ({ R with rel := rel }.spec adm) := by
  refine h.mono (fun _ _ _ _ _ hp => hp) ?_
  intro d ins outs τ m m' _ hpost
  obtain ⟨X, hread, hroom, Y, hlen, hR, hm⟩ := hpost
  exact ⟨X, hread, hroom, Y, hlen, hrel _ _ _ _ hR, hm⟩

/-- Level-1 operations whose error bounds are zero satisfy the exact contracts. -/
theorem IsBlas1.toExact [Has Blas1Op Op] {dec : K → ℝ} {ok : ℕ → Prop}
    {J : Interp Op Tst K} (h : IsBlas1 dec ⟨fun _ => 0, fun _ => 0, 0, 0, 0⟩ ok J) :
    IsExactBlas1 dec ok J := by
  refine ⟨?_, ?_, ?_, ?_, ?_, h.copy⟩
  · refine meets_replace_rel (rel := (sumExactRel dec).rel) h.sum ?_
    intro d X w Y hrel
    simp only [sumRel_rel] at hrel
    split at hrel
    · simpa [sumExactRel, IsSumErr, sub_eq_zero] using hrel
    · contradiction
  · refine meets_replace_rel (rel := (dotExactRel dec).rel) h.dot ?_
    intro d X w Y hrel
    simp only [dotRel_rel] at hrel
    split at hrel
    · simpa [dotExactRel, IsDotErr, sub_eq_zero] using hrel
    · contradiction
  · refine meets_replace_rel (rel := (axpyExactRel dec).rel) h.axpy ?_
    intro d X w Y hrel
    simp only [axpyRel_rel] at hrel
    split at hrel
    · simpa [axpyExactRel, IsAxpyErr, sub_eq_zero] using hrel
    · contradiction
  · refine meets_replace_rel (rel := (nrm2ExactRel dec).rel) h.nrm2 ?_
    intro d X w Y hrel
    simp only [nrm2Rel_rel] at hrel
    split at hrel
    · rename_i xs v
      obtain ⟨σ, hσ, hν⟩ := hrel
      have hs : dec σ = ∑ i ∈ Finset.range (d.headD 0), dec (vec xs i) ^ 2 := by
        simpa [IsDotErr, sub_eq_zero, pow_two] using hσ
      have hnonneg : 0 ≤ dec σ := by
        rw [hs]
        exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      simpa [nrm2ExactRel, sub_eq_zero, hs] using hν hnonneg
    · contradiction
  · refine meets_replace_rel (rel := (scalExactRel dec).rel) h.scal ?_
    intro d X w Y hrel
    simp only [scalRel_rel] at hrel
    split at hrel
    · simpa [scalExactRel, IsScalErr, sub_eq_zero] using hrel
    · contradiction

end NLAlib.Ops
