/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PivotedCholeskyFrames
public import NLAlib.Matrix.Factorizations.CholeskyPivoting

/-!
# Stored symmetric Cholesky prefixes

The actual history determines one permutation for both input axes. The residual is total
Gaussian elimination on that input, and completed factor columns are canonical.

## Main results

* `NLAlib.Computation.PivotedCholesky.State.zero`: copied input and zero factor initialization.
* `NLAlib.Computation.PivotedCholesky.State.writeBlocks_pop`: final factor and actual log writes.
-/

@[expose] public section

namespace NLAlib.Computation.PivotedCholesky

variable {P : Type} [DecidableEq P] {N : ℕ}

/-- Actual factorization prefix, including the symmetric permutation decoded from the
stored absolute current-position indices. Future factor columns are initialized words. -/
structure State (base : Store P ℝ) (tag : P) (A : Matrix (Fin N) (Fin N) ℝ)
    (R L H lo ho k : ℕ) (s : Store P ℝ) : Prop where
  /-- The residual, factor and history footprint uses coincident lower/upper frame slots. -/
  frame : PLU.Frame base N R L L H lo lo ho s
  /-- Initialized residual/factor and actual committed history with canonical factor prefix. -/
  values : ∃ (p : Fin N → Fin N) (F : Matrix (Fin N) (Fin N) ℝ),
    Holds s tag R 0
      (gaussState (A.submatrix (luPivotPermutation p k) (luPivotPermutation p k)) k) ∧
    Holds s tag L lo F ∧
    (∀ i j : Fin N, j.val < k → F i j =
      choleskyLower (A.submatrix (luPivotPermutation p k) (luPivotPermutation p k)) i j) ∧
    (∀ j : Fin N, j.val < k → s.read tag H (ho + j) = some ((p j).val : ℝ) ∧ j ≤ p j)

/-- Copying the matrix and initializing all factor entries establishes the empty prefix. -/
theorem State.zero {base s : Store P ℝ} {tag : P} {A : Matrix (Fin N) (Fin N) ℝ}
    {R L H lo ho : ℕ} (hf : PLU.Frame base N R L L H lo lo ho s)
    (hR : Holds s tag R 0 A) (hL : Holds s tag L lo (0 : Matrix (Fin N) (Fin N) ℝ)) :
    State base tag A R L H lo ho 0 s := by
  refine ⟨hf, id, 0, ?_, hL, ?_, ?_⟩
  · intro i j
    simpa only [gaussState_zero, luPivotPermutation_zero, Matrix.submatrix_apply,
      Equiv.refl_apply] using hR i j
  · intro _ _ hj; exact (Nat.not_lt_zero _ hj).elim
  · intro _ hj; exact (Nat.not_lt_zero _ hj).elim

/-- An empty-dimensional prefix is complete without initialized cells or valid handles. -/
theorem State.empty (base : Store P ℝ) (tag : P) (A : Matrix (Fin N) (Fin N) ℝ)
    (R L H lo ho : ℕ) (hN : N = 0) : State base tag A R L H lo ho N base := by
  subst N
  refine ⟨PLU.Frame.refl base 0 R L L H lo lo ho, id, 0, ?_, ?_, ?_, ?_⟩
  all_goals intro i; exact Fin.elim0 i

/-- A completed prefix determines the canonical factor and recorded pivot log after
releasing residual scratch. Input storage may overlap either output. -/
theorem State.writeBlocks_pop {initial final : Store P ℝ} {tag : P}
    {A : Matrix (Fin N) (Fin N) ℝ} {L H lo ho : ℕ}
    (hs : State (initial.push (tag, Array.replicate (N * N) none)) tag A
      initial.size L H lo ho N final)
    (hLcap : Writable initial tag L lo (N * N)) (hHcap : Writable initial tag H ho N)
    (hLH : L ≠ H) :
    ∃ p : Fin N → Fin N,
      initial.writeBlocks tag [(L, lo, N * N), (H, ho, N)]
        [flatten (choleskyLower (A.submatrix (luPivotPermutation p N) (luPivotPermutation p N))),
          Array.ofFn (fun j => ((p j).val : ℝ))] = some final.pop ∧
      (∀ j, j ≤ p j) ∧
      Holds final.pop tag L lo
        (choleskyLower (A.submatrix (luPivotPermutation p N) (luPivotPermutation p N))) ∧
      (∀ j : Fin N, Store.read final.pop tag H (ho + j) = some ((p j).val : ℝ)) := by
  obtain ⟨p, F, -, hF, hprefix, hlog⟩ := hs.values
  have hFeq : F = choleskyLower
      (A.submatrix (luPivotPermutation p N) (luPivotPermutation p N)) := by
    ext i j
    exact hprefix i j j.isLt
  have hsize : final.size = initial.size + 1 := by
    simpa only [Store.size_shape, Array.size_push] using congrArg Array.size hs.frame.shape
  have hFpop : Holds final.pop tag L lo F := fun i j => by
    have hLb := hLcap.lt_size (Nat.mul_pos (Nat.zero_lt_of_lt i.isLt)
      (Nat.zero_lt_of_lt i.isLt))
    rw [Store.read_pop_of_lt (by omega)]
    exact hF i j
  have hHpop : ∀ j : Fin N, Store.read final.pop tag H (ho + j) =
      some ((p j).val : ℝ) := by
    intro j
    have hHb := hHcap.lt_size (Nat.zero_lt_of_lt j.isLt)
    rw [Store.read_pop_of_lt (by omega)]
    exact (hlog j j.isLt).1
  have hshape : Store.shape final.pop = initial.shape := by
    rw [Store.shape_pop, hs.frame.shape]
    simp only [Store.shape, Array.map_push, Array.pop_push]
  have hw := writeBlocks_factor F p hLH hshape hFpop hHpop
    (fun q b i hbL hbH => by
      by_cases hb : b < initial.size
      · rw [Store.read_pop_of_lt (by omega),
          hs.frame.outside q b i (Or.inl (by omega)) hbL hbL hbH,
          Store.read_push_of_lt hb]
      · exact (Store.read_eq_none_of_size_le (s := final.pop)
          (by simp only [Array.size_pop]; omega)).trans
          (Store.read_eq_none_of_size_le (s := initial) (by omega)).symm)
  exact ⟨p, hFeq ▸ hw, fun j => (hlog j j.isLt).2, hFeq ▸ hFpop, hHpop⟩

end NLAlib.Computation.PivotedCholesky
