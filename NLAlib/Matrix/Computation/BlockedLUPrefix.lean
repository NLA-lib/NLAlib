/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PanelSchurUpdate
public import NLAlib.Matrix.Computation.PLUFrames
public import NLAlib.Matrix.Computation.LU

/-!
# Stored canonical prefixes for blocked LU

The committed factor columns and rows are canonical. The residual is supplied explicitly:
inside a panel it is the deferred panel state, and between panels it is full Gaussian
elimination. Both actual loop invariants share this concrete stored prefix.

## Main definitions

* `NLAlib.Computation.BlockedLU.State`: stored residual, factor prefixes and complete frame.

## Main results

* `NLAlib.Computation.BlockedLU.State.zero`: initialized empty factor prefix.
* `NLAlib.Computation.BlockedLU.State.writeBlocks_pop`: actual completed factor outputs.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation.BlockedLU

variable {P : Type} [DecidableEq P] {N : ℕ}

/-- A stored unpivoted factor prefix with its current residual. The existing four-window
frame is instantiated with its fourth window inside the scoped residual buffer; it permits
no additional external writes. Factor entries not yet committed are unrestricted. -/
structure State (base : Store P ℝ) (p : P) (A : Matrix (Fin N) (Fin N) ℝ)
    (S L U lo uo k : ℕ) (residual : Matrix (Fin N) (Fin N) ℝ) (s : Store P ℝ) : Prop where
  /-- Residual and factor windows form the complete external store footprint. -/
  frame : PLU.Frame base N S L U S lo uo 0 s
  /-- Actual stored values and their canonical completed factor prefixes. -/
  values : ∃ F G : Matrix (Fin N) (Fin N) ℝ,
    Holds s p S 0 residual ∧ Holds s p L lo F ∧ Holds s p U uo G ∧
    (∀ i j : Fin N, j.val < k → F i j = luLower A i j) ∧
    (∀ i j : Fin N, i.val < k → G i j = luUpper A i j)

/-- A copied input and two zero factor matrices establish the empty committed prefix. -/
theorem State.zero {base s : Store P ℝ} {p : P} {A : Matrix (Fin N) (Fin N) ℝ}
    {S L U lo uo : ℕ} (hf : PLU.Frame base N S L U S lo uo 0 s)
    (hS : Holds s p S 0 A) (hL : Holds s p L lo (0 : Matrix (Fin N) (Fin N) ℝ))
    (hU : Holds s p U uo (0 : Matrix (Fin N) (Fin N) ℝ)) :
    State base p A S L U lo uo 0 A s := by
  refine ⟨hf, 0, 0, hS, hL, hU, ?_, ?_⟩
  · intro _ _ hj; exact (Nat.not_lt_zero _ hj).elim
  · intro _ _ hi; exact (Nat.not_lt_zero _ hi).elim

/-- Empty matrices need no initialized cells or valid handles to form their completed prefix. -/
theorem State.empty (base : Store P ℝ) (p : P) (A residual : Matrix (Fin N) (Fin N) ℝ)
    (S L U lo uo : ℕ) (hN : N = 0) :
    State base p A S L U lo uo N residual base := by
  subst N
  refine ⟨PLU.Frame.refl base 0 S L U S lo uo 0, 0, 0, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro i; exact Fin.elim0 i

/-- Completed factor prefixes, after releasing the residual buffer, give precisely their two
original-store writes and their stored canonical values. No source separation is required:
initialization may have copied an input that overlaps either factor window. -/
theorem State.writeBlocks_pop {initial final : Store P ℝ} {p : P}
    {A residual : Matrix (Fin N) (Fin N) ℝ} {L U lo uo : ℕ}
    (hs : State (initial.push (p, Array.replicate (N * N) none)) p A
      initial.size L U lo uo N residual final)
    (hLcap : Writable initial p L lo (N * N)) (hUcap : Writable initial p U uo (N * N))
    (hLU : L ≠ U) :
    initial.writeBlocks p [(L, lo, N * N), (U, uo, N * N)]
      [flatten (luLower A), flatten (luUpper A)] = some final.pop ∧
      Holds final.pop p L lo (luLower A) ∧ Holds final.pop p U uo (luUpper A) := by
  obtain ⟨F, G, _, hF, hG, hFp, hGp⟩ := hs.values
  have hFeq : F = luLower A := by ext i j; exact hFp i j j.isLt
  have hGeq : G = luUpper A := by ext i j; exact hGp i j i.isLt
  have hsize : final.size = initial.size + 1 := by
    simpa only [Store.size_shape, Array.size_push] using congrArg Array.size hs.frame.shape
  have hLb : 0 < N → L < initial.size := fun hN => hLcap.lt_size (Nat.mul_pos hN hN)
  have hUb : 0 < N → U < initial.size := fun hN => hUcap.lt_size (Nat.mul_pos hN hN)
  have hFpop : Holds final.pop p L lo F := fun i j => by
    rw [Store.read_pop_of_lt (by have := hLb (Nat.zero_lt_of_lt i.isLt); omega)]
    exact hF i j
  have hGpop : Holds final.pop p U uo G := fun i j => by
    rw [Store.read_pop_of_lt (by have := hUb (Nat.zero_lt_of_lt i.isLt); omega)]
    exact hG i j
  have hshape : Store.shape final.pop = initial.shape := by
    rw [Store.shape_pop, hs.frame.shape]
    simp only [Store.shape, Array.map_push, Array.pop_push]
  have hw := writeBlocks_factors hLU hshape hFpop hGpop (fun q b t hbL hbU => by
    by_cases hb : b < initial.size
    · rw [Store.read_pop_of_lt (by omega),
        hs.frame.outside q b t (Or.inl (by omega)) hbL hbU (Or.inl (by omega)),
        Store.read_push_of_lt hb]
    · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
        Store.read_eq_none_of_size_le (by omega)])
  simpa only [hFeq, hGeq] using And.intro hw (And.intro hFpop hGpop)

end NLAlib.Computation.BlockedLU
