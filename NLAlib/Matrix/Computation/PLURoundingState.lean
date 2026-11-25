/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLURoundingInitialize
public import NLAlib.Matrix.Perturbation.LURoundingPrefix

/-!
# Stored prefixes of rounded partial-pivoted LU

The stored invariant uses the actual decoded residual and factors and the exact recorded row
choices. Committed factor entries satisfy their triangular shape and multiplier bound. When
the unit roundoff is below one, the same actual values also satisfy the pure rounding prefix.

## Main definitions

* `NLAlib.Computation.PLURounding.State`: actual stored values and their rounded prefix.

## Main results

* `NLAlib.Computation.PLURounding.State.zero`: initialization of the prefix.
-/

@[expose] public section

namespace NLAlib.Computation.PLURounding

variable {P K : Type} [DecidableEq P] {N : ℕ}

/-- A stored prefix of the actual rounded partial-pivoted driver. No retired residual entry
is assumed zero. The conditional numerical prefix permits success and shape guarantees at
any unit roundoff, while the backward-error conclusion requires roundoff below one. -/
structure State (dec : P → K → ℝ) (u : ℝ) (base : Store P K) (tag : P)
    (A : Matrix (Fin N) (Fin N) ℝ) (S L U H lo uo ho k : ℕ) (s : Store P K) : Prop where
  /-- Complete mutable-block footprint. -/
  frame : PLU.Frame base N S L U H lo uo ho s
  /-- Actual values, committed shape and multipliers, numerical prefix and written log. -/
  values : ∃ (history : Fin N → Fin N) (R F G : Matrix (Fin N) (Fin N) ℝ),
    HoldsDecoded s dec tag S 0 R ∧ HoldsDecoded s dec tag L lo F ∧
    HoldsDecoded s dec tag U uo G ∧
    (∀ i j, j.val < k → i < j → F i j = 0) ∧
    (∀ j, j.val < k → F j j = 1) ∧
    (∀ i j, i.val < k → j < i → G i j = 0) ∧
    (∀ i j, j.val < k → |F i j| ≤ 1 + u) ∧
    (u < 1 → IsLURoundingPrefix u k (A.submatrix (luPivotPermutation history k) id) R F G) ∧
    (∀ j : Fin N, j.val < k → ∃ w, s.read tag H (ho + j) = some w ∧
      dec tag w = (history j).val ∧ j ≤ history j)

/-- Copied input and initialized zero factors establish the empty stored prefix; the pivot
log is not read before the first selection writes it. -/
theorem State.zero {dec : P → K → ℝ} {u : ℝ} {base s : Store P K} {tag : P}
    {A : Matrix (Fin N) (Fin N) ℝ} {S L U H lo uo ho : ℕ}
    (hf : PLU.Frame base N S L U H lo uo ho s)
    (hS : HoldsDecoded s dec tag S 0 A)
    (hL : HoldsDecoded s dec tag L lo (0 : Matrix (Fin N) (Fin N) ℝ))
    (hU : HoldsDecoded s dec tag U uo (0 : Matrix (Fin N) (Fin N) ℝ)) :
    State dec u base tag A S L U H lo uo ho 0 s := by
  refine ⟨hf, id, A, 0, 0, hS, hL, hU, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ hj; exact (Nat.not_lt_zero _ hj).elim
  · intro _ hj; exact (Nat.not_lt_zero _ hj).elim
  · intro _ _ hi; exact (Nat.not_lt_zero _ hi).elim
  · intro _ _ hj; exact (Nat.not_lt_zero _ hj).elim
  · intro _
    have he : A.submatrix (luPivotPermutation id 0) id = A := by
      ext i j
      simp only [luPivotPermutation_zero, Matrix.submatrix_apply, Equiv.refl_apply, id_eq]
    rw [he]
    exact IsLURoundingPrefix.initial u A 0 0
  · intro _ hj; exact (Nat.not_lt_zero _ hj).elim

/-- The completed zero-dimensional state needs no initialized buffers or valid handles. -/
theorem State.empty (dec : P → K → ℝ) (u : ℝ) (base : Store P K) (tag : P)
    (A : Matrix (Fin N) (Fin N) ℝ) (S L U H lo uo ho : ℕ) (hN : N = 0) :
    State dec u base tag A S L U H lo uo ho N base := by
  subst N
  exact State.zero (PLU.Frame.refl base 0 S L U H lo uo ho)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

/-- One maximal pivot and the actual rounded division witnesses bound every new lower-column
entry by $1+u$, including exact structural zeros and the unit diagonal. -/
theorem abs_column_le_one_add {u : ℝ} (hu : 0 ≤ u) (R : Matrix (Fin N) (Fin N) ℝ)
    (r : Fin N) (v : Fin N → ℝ) (hv0 : ∀ i, i < r → v i = 0) (hv1 : v r = 1)
    (hvrel : ∀ i, r < i → RelErr u (R i r / R r r) (v i))
    (hmax : ∀ i, r ≤ i → |R i r| ≤ |R r r|) : ∀ i, |v i| ≤ 1 + u := by
  intro i
  rcases lt_trichotomy i r with hir | rfl | hri
  · rw [hv0 i hir, abs_zero]; linarith
  · rw [hv1, abs_one]; linarith
  · exact abs_le_one_add_of_relErr_div (hvrel i hri) (hmax i hri.le)

/-- Active row exchange followed by one materialized column and row advances the committed
triangular shapes, exact unit diagonal and uniform lower multiplier bound. -/
theorem shape_update {k : ℕ} {u : ℝ} (F G : Matrix (Fin N) (Fin N) ℝ)
    (r chosen : Fin N) (hr : r.val = k) (hc : r ≤ chosen) (v row : Fin N → ℝ)
    (hlower : ∀ i j, j.val < k → i < j → F i j = 0)
    (hdiag : ∀ j, j.val < k → F j j = 1)
    (hupper : ∀ i j, i.val < k → j < i → G i j = 0)
    (hbound : ∀ i j, j.val < k → |F i j| ≤ 1 + u)
    (hv0 : ∀ i, i < r → v i = 0) (hv1 : v r = 1)
    (hrow : ∀ j, j < r → row j = 0) (hvbound : ∀ i, |v i| ≤ 1 + u) :
    let F' := (F.submatrix (Equiv.swap r chosen) id).updateCol r v
    let G' := G.updateRow r row
    (∀ i j, j.val < k + 1 → i < j → F' i j = 0) ∧
    (∀ j, j.val < k + 1 → F' j j = 1) ∧
    (∀ i j, i.val < k + 1 → j < i → G' i j = 0) ∧
    (∀ i j, j.val < k + 1 → |F' i j| ≤ 1 + u) := by
  have hfix : ∀ i : Fin N, i.val < k → Equiv.swap r chosen i = i := by
    intro i hi
    exact Fin.swap_apply_of_lt_of_le r chosen hc i (by omega)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hj hij
    by_cases hjr : j = r
    · subst j; simpa only [Matrix.updateCol_self] using hv0 i hij
    · rw [Matrix.updateCol_ne hjr, Matrix.submatrix_apply, id_eq, hfix i (by
        have := i.isLt; change i.val < j.val at hij; omega)]
      exact hlower i j (by have hne : j.val ≠ r.val := fun h => hjr (Fin.ext h); omega) hij
  · intro j hj
    by_cases hjr : j = r
    · subst j; simpa only [Matrix.updateCol_self] using hv1
    · have hjk : j.val < k := by
        have hne : j.val ≠ r.val := fun h => hjr (Fin.ext h)
        omega
      rw [Matrix.updateCol_ne hjr, Matrix.submatrix_apply, id_eq, hfix j hjk]
      exact hdiag j hjk
  · intro i j hi hji
    by_cases hir : i = r
    · subst i; simpa only [Matrix.updateRow_self] using hrow j hji
    · rw [Matrix.updateRow_ne hir]
      exact hupper i j (by have hne : i.val ≠ r.val := fun h => hir (Fin.ext h); omega) hji
  · intro i j hj
    by_cases hjr : j = r
    · subst j; simpa only [Matrix.updateCol_self] using hvbound i
    · rw [Matrix.updateCol_ne hjr]
      exact hbound _ j (by have hne : j.val ≠ r.val := fun h => hjr (Fin.ext h); omega)

end NLAlib.Computation.PLURounding
