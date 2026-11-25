/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.GroupTheory.Perm.Fin
public import NLAlib.Matrix.Computation.PLUFrames
public import NLAlib.Matrix.Factorizations.LUPivoting
public import NLAlib.Matrix.Factorizations.LUGeneral

/-!
# Prefixes of stored partial-pivoted LU

The stored invariant links the recorded pivot indices to their actual row permutation, the
residual to total Gaussian elimination and the completed factor columns and rows to the
canonical factors of the currently permuted input. Earlier pivots remain maximal in absolute
value; zero pivots are admitted throughout.

## Main definitions

* `NLAlib.Computation.PLU.State`: the stored elimination prefix and pivot log.

## Main results

* `NLAlib.Computation.PLU.submatrix_luPivotPermutation_update`: one recorded swap updates
  the permuted input.
* `NLAlib.Computation.PLU.prefix_update`: completed factors and maximal pivots advance together.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation.PLU

variable {P : Type} [DecidableEq P] {N : ℕ}

/-- The execution state after $k$ partial-pivoted elimination steps. Completed log entries
decode the actual row permutation, the residual is total Gaussian elimination on that
permuted input, and completed factor columns and rows are canonical. Every earlier pivot
is largest in absolute value among the entries below it. Factor entries not yet committed
are initialized but otherwise unrestricted. -/
structure State (base : Store P ℝ) (tag : P) (A : Matrix (Fin N) (Fin N) ℝ)
    (S L U H lo uo ho k : ℕ) (s : Store P ℝ) : Prop where
  /-- The complete storage frame of the four mutable blocks. -/
  frame : Frame base N S L U H lo uo ho s
  /-- Actual stored values, their canonical completed prefixes and the recorded permutation. -/
  values : ∃ (p : Fin N → Fin N) (F G : Matrix (Fin N) (Fin N) ℝ),
    Holds s tag S 0 (gaussState (A.submatrix (luPivotPermutation p k) id) k) ∧
    Holds s tag L lo F ∧ Holds s tag U uo G ∧
    (∀ i j : Fin N, j.val < k → F i j = luLower (A.submatrix (luPivotPermutation p k) id) i j) ∧
    (∀ i j : Fin N, i.val < k → G i j = luUpper (A.submatrix (luPivotPermutation p k) id) i j) ∧
    (∀ j i : Fin N, j.val < k → j ≤ i →
      |gaussState (A.submatrix (luPivotPermutation p k) id) j i j| ≤
        |gaussState (A.submatrix (luPivotPermutation p k) id) j j j|) ∧
    (∀ j : Fin N, j.val < k →
      s.read tag H (ho + j) = some ((p j).val : ℝ) ∧ j ≤ p j)

/-- Initialization with the copied input and two zero matrices establishes the empty prefix.
No pivot-log cell is read before the first actual selection writes it. -/
theorem State.zero {base s : Store P ℝ} {tag : P} {A : Matrix (Fin N) (Fin N) ℝ}
    {S L U H lo uo ho : ℕ} (hf : Frame base N S L U H lo uo ho s)
    (hS : Holds s tag S 0 A) (hL : Holds s tag L lo (0 : Matrix (Fin N) (Fin N) ℝ))
    (hU : Holds s tag U uo (0 : Matrix (Fin N) (Fin N) ℝ)) :
    State base tag A S L U H lo uo ho 0 s := by
  refine ⟨hf, id, 0, 0, ?_, hL, hU, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [gaussState_zero, luPivotPermutation_zero, Matrix.submatrix_apply,
      Equiv.refl_apply, id_eq] using hS i j
  · intro _ _ hj
    exact (Nat.not_lt_zero _ hj).elim
  · intro _ _ hi
    exact (Nat.not_lt_zero _ hi).elim
  · intro _ _ hj
    exact (Nat.not_lt_zero _ hj).elim
  · intro _ hj
    exact (Nat.not_lt_zero _ hj).elim

/-- The completed empty-dimensional prefix requires no initialized storage or valid handles. -/
theorem State.empty (base : Store P ℝ) (tag : P) (A : Matrix (Fin N) (Fin N) ℝ)
    (S L U H lo uo ho : ℕ) (hN : N = 0) : State base tag A S L U H lo uo ho N base := by
  subst N
  refine ⟨Frame.refl base 0 S L U H lo uo ho, id, 0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro i; exact Fin.elim0 i

/-- Recording the chosen absolute row index composes its swap on the current row positions.
The decoded permutation maps current row positions to original row indices. -/
theorem submatrix_luPivotPermutation_update {α : Type*} (A : Matrix (Fin N) (Fin N) α)
    (p : Fin N → Fin N) (k r : Fin N) :
    A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1)) id =
      (A.submatrix (luPivotPermutation p k.val) id).submatrix (Equiv.swap k r) id := by
  rw [luPivotPermutation_update]
  ext i j
  rfl

/-- A recorded active-row swap, one canonical factor column and row, and its maximal pivot
advance both factor prefixes and the complete earlier maximal-pivot property. This includes
zero pivots; the total lower-column formula uses division by zero equal to zero. -/
theorem prefix_update {𝕜 : Type*} [RCLike 𝕜] (A : Matrix (Fin N) (Fin N) 𝕜)
    (p : Fin N → Fin N) (k r : Fin N) (hkr : k ≤ r) (F G : Matrix (Fin N) (Fin N) 𝕜)
    (hF : ∀ i j : Fin N, j.val < k.val →
      F i j = luLower (A.submatrix (luPivotPermutation p k.val) id) i j)
    (hG : ∀ i j : Fin N, i.val < k.val →
      G i j = luUpper (A.submatrix (luPivotPermutation p k.val) id) i j)
    (hmax : ∀ j i : Fin N, j.val < k.val → j ≤ i →
      ‖gaussState (A.submatrix (luPivotPermutation p k.val) id) j i j‖ ≤
        ‖gaussState (A.submatrix (luPivotPermutation p k.val) id) j j j‖)
    (hpivot : ∀ i : Fin N, k ≤ i →
      ‖gaussState (A.submatrix (luPivotPermutation p k.val) id) k i k‖ ≤
        ‖gaussState (A.submatrix (luPivotPermutation p k.val) id) k r k‖) :
    let B := A.submatrix (luPivotPermutation p k.val) id
    let B' := A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1)) id
    let R := (gaussState B k.val).submatrix (Equiv.swap k r) id
    let F' := (F.submatrix (Equiv.swap k r) id).updateCol k
      (fun i => if i < k then 0 else if i = k then 1 else R i k / R k k)
    let G' := G.updateRow k (fun j => if j < k then 0 else R k j)
    (∀ i j : Fin N, j.val < k.val + 1 → F' i j = luLower B' i j) ∧
    (∀ i j : Fin N, i.val < k.val + 1 → G' i j = luUpper B' i j) ∧
    (∀ j i : Fin N, j.val < k.val + 1 → j ≤ i →
      ‖gaussState B' j i j‖ ≤ ‖gaussState B' j j j‖) := by
  let B := A.submatrix (luPivotPermutation p k.val) id
  let τ := Equiv.swap k r
  have hfix : ∀ i : Fin N, i.val < k.val → τ i = i := Fin.swap_apply_of_lt_of_le k r hkr
  have hR : gaussState (A.submatrix
      (luPivotPermutation (Function.update p k r) (k.val + 1)) id) k.val =
      (gaussState B k.val).submatrix τ id := by
    rw [submatrix_luPivotPermutation_update]
    exact gaussState_submatrix_left B τ k.val hfix
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj
    by_cases hjk : j = k
    · subst j
      rw [Matrix.updateCol_self]
      rw [luLower, Matrix.of_apply, hR]
      rcases lt_trichotomy i k with hi | rfl | hi
      · simp only [hi, hi.not_gt, hi.ne, if_true, if_false]
      · simp only [lt_self_iff_false, if_false, if_true]
      · simp only [hi, hi.not_gt, hi.ne', if_true, if_false, B, τ]
    · rw [Matrix.updateCol_ne hjk]
      have hj' : j.val < k.val := by
        have hne : j.val ≠ k.val := fun heq => hjk (Fin.ext heq)
        omega
      rw [Matrix.submatrix_apply, id_eq, hF (τ i) j hj', submatrix_luPivotPermutation_update]
      exact (luLower_submatrix_left_apply B τ k.val hfix i j hj').symm
  · intro i j hi
    by_cases hik : i = k
    · subst i
      rw [Matrix.updateRow_self, luUpper, Matrix.of_apply, hR]
      by_cases hj : j < k
      · simp only [hj, not_le_of_gt hj, if_true, if_false]
      · simp only [hj, not_lt.mp hj, if_true, if_false, B, τ]
    · rw [Matrix.updateRow_ne hik]
      have hi' : i.val < k.val := by
        have hne : i.val ≠ k.val := fun heq => hik (Fin.ext heq)
        omega
      rw [hG i j hi', submatrix_luPivotPermutation_update]
      exact (luUpper_submatrix_left_apply B τ k.val hfix i j hi').symm
  · intro j i hj hji
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · rw [submatrix_luPivotPermutation_update]
      exact forall_weight_gaussState_le_submatrix_left (fun x => ‖x‖) B τ k.val hfix
        hmax j i hj hji
    · have hjk : j = k := Fin.ext hj
      subst j
      rw [hR]
      simpa only [B, τ, Matrix.submatrix_apply, id_eq, Equiv.swap_apply_left] using
        hpivot (τ i) (Fin.le_swap_apply_of_le k r hkr i hji)

/-- A completed stored prefix, after releasing its residual workspace, writes the two
canonical factors and its actual recorded pivot log. Earlier maximal pivots yield an exact
factorization even on singular inputs, and every multiplier has magnitude at most one. -/
theorem State.writeBlocks_pop {initial final : Store P ℝ} {tag : P}
    {A : Matrix (Fin N) (Fin N) ℝ} {L U H lo uo ho : ℕ}
    (hs : State (initial.push (tag, Array.replicate (N * N) none)) tag A
      initial.size L U H lo uo ho N final)
    (hLcap : Writable initial tag L lo (N * N)) (hUcap : Writable initial tag U uo (N * N))
    (hHcap : Writable initial tag H ho N) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H) :
    ∃ p : Fin N → Fin N,
      initial.writeBlocks tag [(L, lo, N * N), (U, uo, N * N), (H, ho, N)]
        [flatten (luLower (A.submatrix (luPivotPermutation p N) id)),
          flatten (luUpper (A.submatrix (luPivotPermutation p N) id)),
          Array.ofFn (fun j => ((p j).val : ℝ))] = some final.pop ∧
      (∀ j, j ≤ p j) ∧
      IsLU (A.submatrix (luPivotPermutation p N) id)
        (luLower (A.submatrix (luPivotPermutation p N) id))
        (luUpper (A.submatrix (luPivotPermutation p N) id)) ∧
      (∀ i j, |luLower (A.submatrix (luPivotPermutation p N) id) i j| ≤ 1) ∧
      Holds final.pop tag L lo (luLower (A.submatrix (luPivotPermutation p N) id)) ∧
      Holds final.pop tag U uo (luUpper (A.submatrix (luPivotPermutation p N) id)) ∧
      (∀ j : Fin N, Store.read final.pop tag H (ho + j) = some ((p j).val : ℝ)) := by
  obtain ⟨p, F, G, -, hF, hG, hFpref, hGpref, hmax, hlog⟩ := hs.values
  have hFeq : F = luLower (A.submatrix (luPivotPermutation p N) id) := by
    ext i j
    exact hFpref i j j.isLt
  have hGeq : G = luUpper (A.submatrix (luPivotPermutation p N) id) := by
    ext i j
    exact hGpref i j i.isLt
  have hsize : final.size = initial.size + 1 := by
    simpa only [Store.size_shape, Array.size_push] using congrArg Array.size hs.frame.shape
  have hLb : 0 < N → L < initial.size := fun hN => hLcap.lt_size (Nat.mul_pos hN hN)
  have hUb : 0 < N → U < initial.size := fun hN => hUcap.lt_size (Nat.mul_pos hN hN)
  have hHb : 0 < N → H < initial.size := fun hN => hHcap.lt_size hN
  have hFpop : Holds final.pop tag L lo F := fun i j => by
    rw [Store.read_pop_of_lt (by have := hLb (Nat.zero_lt_of_lt i.isLt); omega)]
    exact hF i j
  have hGpop : Holds final.pop tag U uo G := fun i j => by
    rw [Store.read_pop_of_lt (by have := hUb (Nat.zero_lt_of_lt i.isLt); omega)]
    exact hG i j
  have hHpop : ∀ j : Fin N, Store.read final.pop tag H (ho + j) = some ((p j).val : ℝ) :=
    fun j => by
    rw [Store.read_pop_of_lt (by have := hHb (Nat.zero_lt_of_lt j.isLt); omega)]
    exact (hlog j j.isLt).1
  have hshape : Store.shape final.pop = initial.shape := by
    rw [Store.shape_pop, hs.frame.shape]
    simp only [Store.shape, Array.map_push, Array.pop_push]
  have hwrite := writeBlocks_factors_history (initial := initial) (final := final.pop)
    F G (fun j => ((p j).val : ℝ)) hLU hLH hUH
    hshape hFpop hGpop hHpop (fun q b i hbL hbU hbH => by
      by_cases hb : b < initial.size
      · rw [Store.read_pop_of_lt (by omega),
          hs.frame.outside q b i (Or.inl (by omega)) hbL hbU hbH,
          Store.read_push_of_lt hb]
      · exact (Store.read_eq_none_of_size_le (s := final.pop)
          (by simp only [Array.size_pop]; omega)).trans
          (Store.read_eq_none_of_size_le (s := initial) (by omega)).symm)
  have hmax' : ∀ j i : Fin N, j ≤ i →
      ‖gaussState (A.submatrix (luPivotPermutation p N) id) j i j‖ ≤
        ‖gaussState (A.submatrix (luPivotPermutation p N) id) j j j‖ := by
    intro j i hji
    simpa only [Real.norm_eq_abs] using hmax j i j.isLt hji
  refine ⟨p, ?_, fun j => (hlog j j.isLt).2,
    isLU_luLower_luUpper_of_forall_norm_le hmax', (fun i j => ?_), ?_, ?_, hHpop⟩
  · simpa only [hFeq, hGeq] using hwrite
  · simpa only [Real.norm_eq_abs] using norm_luLower_apply_le_one hmax' i j
  · simpa only [hFeq] using hFpop
  · simpa only [hGeq] using hGpop

end NLAlib.Computation.PLU
