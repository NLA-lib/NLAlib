/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LUTriangularPrefix
public import NLAlib.Matrix.Factorizations.LU.StepRelative
public import NLAlib.Matrix.Perturbation.LURoundingPermutations
public import NLAlib.Ops.Logic.IndexLog

/-!
# Stored rounded LU factor prefixes

Actual readable residual and factor blocks carry the pure rounded reconstruction invariant,
initialization zeros in future columns and rows, and committed multiplier bounds. This
storage predicate has no execution witness, computed pivot restriction or selector premise.

## Main results

* `NLAlib.LU.IsRoundedFactorPrefix.initial`: copied input and zero-filled factors.
* `NLAlib.LU.IsRoundedFactorPrefix.of_step`: an actual word step advances the stored prefix.
-/

@[expose] public section

namespace NLAlib.LU

open Ops Computation

variable {K : Type} [Inhabited K] {N : ℕ}

/-- Readable factorization words, rounded reconstruction and initialized future factors.
The bound concerns every row of each committed lower-factor column. -/
def IsRoundedFactorPrefix (dec : K → ℝ) (u quality : ℝ)
    (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) (R L U : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ rs ls us : List K,
    s.readBlock R.1 R.2 (N * N) = some rs ∧
    s.readBlock L.1 L.2 (N * N) = some ls ∧
    s.readBlock U.1 U.2 (N * N) = some us ∧
    (u < 1 → IsLURoundingPrefix u k A (decodeMatrix dec N N rs)
      (decodeMatrix dec N N ls) (decodeMatrix dec N N us)) ∧
    IsLUTriangularPrefix k (decodeMatrix dec N N ls) (decodeMatrix dec N N us) ∧
    (∀ i j : Fin N, k ≤ j.val → decodeMatrix dec N N ls i j = 0) ∧
    (∀ i j : Fin N, k ≤ i.val → decodeMatrix dec N N us i j = 0) ∧
    ∀ i j : Fin N, j.val < k → |decodeMatrix dec N N ls i j| ≤ (1 + u) / quality

/-- Copying the source and filling both factors with literal zeros initializes the rounded
storage predicate. Exact zero decoding suffices, with arbitrary future pivot behavior. -/
theorem IsRoundedFactorPrefix.initial {M : Machine K} {dec : K → ℝ} {u quality : ℝ}
    (hzero : dec (M.lit 0) = 0) {R L U : ℕ × ℕ} {s : Store K} {as : List K}
    (hR : s.readBlock R.1 R.2 (N * N) = some as)
    (hL : s.readBlock L.1 L.2 (N * N) = some (List.replicate (N * N) (M.lit 0)))
    (hU : s.readBlock U.1 U.2 (N * N) = some (List.replicate (N * N) (M.lit 0))) :
    IsRoundedFactorPrefix dec u quality (decodeMatrix dec N N as) 0 R L U s := by
  have hzeros : decodeMatrix dec N N (List.replicate (N * N) (M.lit 0)) = 0 := by
    ext i j
    rw [decodeMatrix_apply]
    simpa only [Matrix.zero_apply, vec, List.getD_replicate (α := K) (x := M.lit 0)
      (h := Idx.add_lt_mul j.isLt i.isLt)] using hzero
  refine ⟨as, _, _, hR, hL, hU, fun _ => IsLURoundingPrefix.initial u _ _ _,
    IsLUTriangularPrefix.initial _ _, ?_, ?_, ?_⟩
  · intro i j _
    rw [hzeros]
    rfl
  · intro i j _
    rw [hzeros]
    rfl
  · intro i j hj
    exact (Nat.not_lt_zero _ hj).elim

/-- Actual factor words after a zero-safe step extend rounded reconstruction, future zeros
and multiplier bounds. The local zero-column premise follows from the pivot quality. -/
theorem IsRoundedFactorPrefix.of_step {M : Machine K} {dec : K → ℝ} {u quality : ℝ}
    (hM : StdModel u dec M) (hu : 0 ≤ u) (hone : dec (M.lit 1) = 1)
    (hquality : 0 < quality) (hquality₁ : quality ≤ 1)
    {A : Matrix (Fin N) (Fin N) ℝ} (k : Fin N) {R L U : ℕ × ℕ} {s : Store K}
    {rs ls us rs' ls' us' : List K} {τ : Tape K}
    (hpost : (stepSpec M dec).post [N, k.val] τ [rs, ls, us] [rs', ls', us'])
    (hprefix : u < 1 → IsLURoundingPrefix u k.val A (decodeMatrix dec N N rs)
      (decodeMatrix dec N N ls) (decodeMatrix dec N N us))
    (hshape : IsLUTriangularPrefix k.val (decodeMatrix dec N N ls) (decodeMatrix dec N N us))
    (hL : ∀ i j : Fin N, k.val ≤ j.val → decodeMatrix dec N N ls i j = 0)
    (hU : ∀ i j : Fin N, k.val ≤ i.val → decodeMatrix dec N N us i j = 0)
    (hbound : ∀ i j : Fin N, j.val < k.val →
      |decodeMatrix dec N N ls i j| ≤ (1 + u) / quality)
    (hchoice : ∀ i : Fin N, k ≤ i → quality * |decodeMatrix dec N N rs i k| ≤
      |decodeMatrix dec N N rs k k|)
    (hR' : s.readBlock R.1 R.2 (N * N) = some rs')
    (hL' : s.readBlock L.1 L.2 (N * N) = some ls')
    (hU' : s.readBlock U.1 U.2 (N * N) = some us') :
    IsRoundedFactorPrefix dec u quality A (k.val + 1) R L U s := by
  have hLk : ∀ i : Fin N, i < k → decodeMatrix dec N N ls i k = 0 :=
    fun i _ => hL i k le_rfl
  have hUk : ∀ j : Fin N, j < k → decodeMatrix dec N N us k j = 0 :=
    fun j _ => hU k j le_rfl
  have hzeroCol (hp : decodeMatrix dec N N rs k k = 0) (i : Fin N) (hi : k ≤ i) :
      decodeMatrix dec N N rs i k = 0 := by
    have hh := hchoice i hi
    rw [hp, abs_zero] at hh
    have ha : |decodeMatrix dec N N rs i k| = 0 := by
      apply le_antisymm _ (abs_nonneg _)
      exact (mul_le_mul_iff_left₀ hquality).mp (by nlinarith [hh])
    exact abs_eq_zero.mp ha
  have hfuture := materializeColumnSpec_future k hpost.1 hL hU
  obtain ⟨hLower, hUpper, hvzero, hvdiag, -⟩ :=
    materializeColumnSpec_relative hM hu hone k hpost.1 hLk hUk
  have hshape' : IsLUTriangularPrefix (k.val + 1)
      (decodeMatrix dec N N ls') (decodeMatrix dec N N us') := by
    rw [hLower, hUpper]
    exact hshape.succ k rfl _ _ hvzero hvdiag (fun j hj => if_pos hj)
  exact ⟨rs', ls', us', hR', hL', hU',
    (fun hu1 => stepSpec_rounding hM hu hu1 hone A k hpost (hprefix hu1) hLk hUk hzeroCol), hshape',
    hfuture.1, hfuture.2,
    abs_decodeMatrix_le_of_materializeColumnSpec hM hu hone hquality hquality₁ k hpost.1
      hLk hbound hchoice⟩

end NLAlib.LU
