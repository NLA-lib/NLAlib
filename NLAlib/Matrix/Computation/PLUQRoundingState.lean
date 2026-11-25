/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQFrames
public import NLAlib.Matrix.Computation.PLURoundingState
public import NLAlib.Matrix.Perturbation.LURoundingPermutations
public import NLAlib.Matrix.Perturbation.LURoundingPrefix

/-!
# Stored prefixes of rounded complete-pivoted LU

The stored invariant uses the actual decoded residual and factors and the exact recorded row
and column choices. Committed factor entries satisfy their triangular shape and multiplier bound.
When
the unit roundoff is below one, the same actual values also satisfy the pure rounding prefix.

## Main definitions

* `NLAlib.Computation.PLUQRounding.State`: actual stored values and their rounded prefix.

## Main results

* `NLAlib.Computation.PLUQRounding.State.zero`: initialization of the prefix.
-/

@[expose] public section

namespace NLAlib.Computation.PLUQRounding

variable {P K : Type} [DecidableEq P] {N : ℕ}

/-- A stored prefix of the actual rounded complete-pivoted driver. No retired residual entry
is assumed zero. The conditional numerical prefix permits success and shape guarantees at
any unit roundoff, while the backward-error conclusion requires roundoff below one. -/
structure State (dec : P → K → ℝ) (u : ℝ) (base : Store P K) (tag : P)
    (A : Matrix (Fin N) (Fin N) ℝ) (S L U Hr Hc lo uo hro hco k : ℕ) (s : Store P K) : Prop where
  /-- Complete mutable-block footprint. -/
  frame : PLUQ.Frame base N S L U Hr Hc lo uo hro hco s
  /-- Actual values, committed shape and multipliers, numerical prefix and written log. -/
  values : ∃ (rows cols : Fin N → Fin N) (R F G : Matrix (Fin N) (Fin N) ℝ),
    HoldsDecoded s dec tag S 0 R ∧ HoldsDecoded s dec tag L lo F ∧
    HoldsDecoded s dec tag U uo G ∧
    (∀ i j, j.val < k → i < j → F i j = 0) ∧
    (∀ j, j.val < k → F j j = 1) ∧
    (∀ i j, i.val < k → j < i → G i j = 0) ∧
    (∀ i j, j.val < k → |F i j| ≤ 1 + u) ∧
    (u < 1 → IsLURoundingPrefix u k
      (A.submatrix (luPivotPermutation rows k) (luPivotPermutation cols k)) R F G) ∧
    (∀ j : Fin N, j.val < k → ∃ w, s.read tag Hr (hro + j) = some w ∧
      dec tag w = (rows j).val ∧ j ≤ rows j) ∧
    (∀ j : Fin N, j.val < k → ∃ w, s.read tag Hc (hco + j) = some w ∧
      dec tag w = (cols j).val ∧ j ≤ cols j)

/-- Copied input and initialized zero factors establish the empty stored prefix; the pivot
log is not read before the first selection writes it. -/
theorem State.zero {dec : P → K → ℝ} {u : ℝ} {base s : Store P K} {tag : P}
    {A : Matrix (Fin N) (Fin N) ℝ} {S L U Hr Hc lo uo hro hco : ℕ}
    (hf : PLUQ.Frame base N S L U Hr Hc lo uo hro hco s)
    (hS : HoldsDecoded s dec tag S 0 A)
    (hL : HoldsDecoded s dec tag L lo (0 : Matrix (Fin N) (Fin N) ℝ))
    (hU : HoldsDecoded s dec tag U uo (0 : Matrix (Fin N) (Fin N) ℝ)) :
    State dec u base tag A S L U Hr Hc lo uo hro hco 0 s := by
  refine ⟨hf, id, id, A, 0, 0, hS, hL, hU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ hj; exact (Nat.not_lt_zero _ hj).elim
  · intro _ hj; exact (Nat.not_lt_zero _ hj).elim
  · intro _ _ hi; exact (Nat.not_lt_zero _ hi).elim
  · intro _ _ hj; exact (Nat.not_lt_zero _ hj).elim
  · intro _
    have he : A.submatrix (luPivotPermutation id 0) (luPivotPermutation id 0) = A := by
      ext i j
      simp only [luPivotPermutation_zero, Matrix.submatrix_apply, Equiv.refl_apply]
    rw [he]
    exact IsLURoundingPrefix.initial u A 0 0
  · intro _ hj; exact (Nat.not_lt_zero _ hj).elim
  · intro _ hj; exact (Nat.not_lt_zero _ hj).elim

/-- The completed zero-dimensional state needs no initialized buffers or valid handles. -/
theorem State.empty (dec : P → K → ℝ) (u : ℝ) (base : Store P K) (tag : P)
    (A : Matrix (Fin N) (Fin N) ℝ) (S L U Hr Hc lo uo hro hco : ℕ) (hN : N = 0) :
    State dec u base tag A S L U Hr Hc lo uo hro hco N base := by
  subst N
  exact State.zero (PLUQ.Frame.refl base 0 S L U Hr Hc lo uo hro hco)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)


end NLAlib.Computation.PLUQRounding
