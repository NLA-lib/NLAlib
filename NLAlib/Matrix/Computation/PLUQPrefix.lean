/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQFrames
public import NLAlib.Matrix.Factorizations.LUQualityPivoting

/-!
# Prefixes of stored complete-pivoted LU

The residual follows the two actual recorded permutation prefixes. Completed lower columns
and upper rows are canonical for the currently permuted input. Each earlier pivot satisfies the
policy's quantitative column quality, so all-input singular factorization remains justified.

## Main definitions

* `NLAlib.Computation.PLUQ.State`: complete-pivoted elimination and both recorded histories.

## Main results

* `NLAlib.Computation.PLUQ.prefix_update`: both factor prefixes and maximal pivots advance.
-/

@[expose] public section

namespace NLAlib.Computation.PLUQ

variable {P : Type} [DecidableEq P] {N : ℕ}

/-- The complete stored prefix links both actual log prefixes to the current row and column
permutations, its total Gaussian residual, canonical committed factor prefixes and earlier
quantitative column quality. A fixed-column policy carries its actual identity log prefix.
Uncommitted factor entries are initialized without extra constraints. -/
structure State (base : Store P ℝ) (tag : P) (A : Matrix (Fin N) (Fin N) ℝ)
    (S L U Hr Hc lo uo hro hco k : ℕ) (s : Store P ℝ)
    (α : ℝ := 1) (fixedColumns : Bool := false) : Prop where
  /-- The residual, factor and two-log write footprint. -/
  frame : Frame base N S L U Hr Hc lo uo hro hco s
  /-- Stored operands and actual history prefixes, with canonical and maximality properties. -/
  values : ∃ (p q : Fin N → Fin N) (F G : Matrix (Fin N) (Fin N) ℝ),
    Holds s tag S 0 (gaussState (A.submatrix (luPivotPermutation p k)
      (luPivotPermutation q k)) k) ∧ Holds s tag L lo F ∧ Holds s tag U uo G ∧
    (∀ i j : Fin N, j.val < k →
      F i j = luLower (A.submatrix (luPivotPermutation p k) (luPivotPermutation q k)) i j) ∧
    (∀ i j : Fin N, i.val < k →
      G i j = luUpper (A.submatrix (luPivotPermutation p k) (luPivotPermutation q k)) i j) ∧
    (∀ t i : Fin N, t.val < k → t ≤ i →
      α * |gaussState (A.submatrix (luPivotPermutation p k) (luPivotPermutation q k)) t i t| ≤
        |gaussState (A.submatrix (luPivotPermutation p k) (luPivotPermutation q k)) t t t|) ∧
    (∀ j : Fin N, j.val < k →
      s.read tag Hr (hro + j) = some ((p j).val : ℝ) ∧ j ≤ p j) ∧
    (∀ j : Fin N, j.val < k →
      s.read tag Hc (hco + j) = some ((q j).val : ℝ) ∧ j ≤ q j ∧
        (fixedColumns = true → q j = j))

/-- Copying the source and initializing both factors establishes the empty history prefix. -/
theorem State.zero {base s : Store P ℝ} {tag : P} {A : Matrix (Fin N) (Fin N) ℝ}
    {S L U Hr Hc lo uo hro hco : ℕ}
    (hf : Frame base N S L U Hr Hc lo uo hro hco s) (hS : Holds s tag S 0 A)
    (hL : Holds s tag L lo (0 : Matrix (Fin N) (Fin N) ℝ))
    (hU : Holds s tag U uo (0 : Matrix (Fin N) (Fin N) ℝ))
    (α : ℝ := 1) (fixedColumns : Bool := false) :
    State base tag A S L U Hr Hc lo uo hro hco 0 s α fixedColumns := by
  refine ⟨hf, id, id, 0, 0, ?_, hL, hU, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa only [gaussState_zero, luPivotPermutation_zero, Matrix.submatrix_apply,
      Equiv.refl_apply] using hS i j
  · intro _ _ hj; exact (Nat.not_lt_zero _ hj).elim
  · intro _ _ hi; exact (Nat.not_lt_zero _ hi).elim
  · intro _ _ ht; exact (Nat.not_lt_zero _ ht).elim
  · intro _ hj; exact (Nat.not_lt_zero _ hj).elim
  · intro _ hj; exact (Nat.not_lt_zero _ hj).elim

/-- An empty matrix has a completed prefix without initialized data or valid handles. -/
theorem State.empty (base : Store P ℝ) (tag : P) (A : Matrix (Fin N) (Fin N) ℝ)
    (S L U Hr Hc lo uo hro hco : ℕ) (hN : N = 0)
    (α : ℝ := 1) (fixedColumns : Bool := false) :
    State base tag A S L U Hr Hc lo uo hro hco N base α fixedColumns := by
  subst N
  refine ⟨Frame.refl base 0 S L U Hr Hc lo uo hro hco, id, id, 0, 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro i; exact Fin.elim0 i

/-- Updating both actual pivot logs composes their current-position swaps independently. -/
theorem submatrix_luPivotPermutation_update {α : Type*} (A : Matrix (Fin N) (Fin N) α)
    (p q : Fin N → Fin N) (k r c : Fin N) :
    A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1))
      (luPivotPermutation (Function.update q k c) (k.val + 1)) =
      (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)).submatrix
        (Equiv.swap k r) (Equiv.swap k c) := by
  exact NLAlib.submatrix_luPivotPermutation_update A p q k r c

/-- An actual complete pivot and the total column/Schur materialization advance both factor
prefixes and all earlier complete maxima. Zero pivots and singular inputs are admitted. -/
theorem prefix_update {𝕜 : Type*} [RCLike 𝕜] (A : Matrix (Fin N) (Fin N) 𝕜)
    (p q : Fin N → Fin N) (k r c : Fin N) (hkr : k ≤ r) (hkc : k ≤ c)
    (F G : Matrix (Fin N) (Fin N) 𝕜)
    (hF : ∀ i j : Fin N, j.val < k.val →
      F i j = luLower (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) i j)
    (hG : ∀ i j : Fin N, i.val < k.val →
      G i j = luUpper (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) i j)
    (hmax : ∀ t i j : Fin N, t.val < k.val → t ≤ i → t ≤ j →
      ‖gaussState (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) t i j‖ ≤
        ‖gaussState (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) t t t‖)
    (hpivot : ∀ i j : Fin N, k ≤ i → k ≤ j →
      ‖gaussState (A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)) k i j‖ ≤
        ‖gaussState (A.submatrix (luPivotPermutation p k.val)
          (luPivotPermutation q k.val)) k r c‖) :
    let B := A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)
    let B' := A.submatrix (luPivotPermutation (Function.update p k r) (k.val + 1))
      (luPivotPermutation (Function.update q k c) (k.val + 1))
    let R := (gaussState B k.val).submatrix (Equiv.swap k r) (Equiv.swap k c)
    let F' := (F.submatrix (Equiv.swap k r) id).updateCol k
      (fun i => if i < k then 0 else if i = k then 1 else R i k / R k k)
    let G' := (G.submatrix id (Equiv.swap k c)).updateRow k
      (fun j => if j < k then 0 else R k j)
    (∀ i j : Fin N, j.val < k.val + 1 → F' i j = luLower B' i j) ∧
    (∀ i j : Fin N, i.val < k.val + 1 → G' i j = luUpper B' i j) ∧
    (∀ t i j : Fin N, t.val < k.val + 1 → t ≤ i → t ≤ j →
      ‖gaussState B' t i j‖ ≤ ‖gaussState B' t t t‖) := by
  let B := A.submatrix (luPivotPermutation p k.val) (luPivotPermutation q k.val)
  let ρ := Equiv.swap k r
  let κ := Equiv.swap k c
  have hρ : ∀ i : Fin N, i.val < k.val → ρ i = i := Fin.swap_apply_of_lt_of_le k r hkr
  have hκ : ∀ j : Fin N, j.val < k.val → κ j = j := Fin.swap_apply_of_lt_of_le k c hkc
  have hR : gaussState (A.submatrix
      (luPivotPermutation (Function.update p k r) (k.val + 1))
      (luPivotPermutation (Function.update q k c) (k.val + 1))) k.val =
      (gaussState B k.val).submatrix ρ κ := by
    rw [submatrix_luPivotPermutation_update]
    exact gaussState_submatrix_left_right B ρ κ k.val hρ hκ
  obtain ⟨hFnew, hGnew⟩ := forall_luLower_luUpper_eq_of_update A p q k r c hkr hkc F G hF hG
  dsimp only
  refine ⟨hFnew, hGnew, ?_⟩
  intro t i j ht hti htj
  rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | ht
  · rw [submatrix_luPivotPermutation_update]
    exact forall_weight_gaussState_le_submatrix_left_right (fun x => ‖x‖) B ρ κ k.val
      hρ hκ hmax t i j ht hti htj
  · have htk : t = k := Fin.ext ht
    subst t
    rw [hR]
    simpa only [B, ρ, κ, Matrix.submatrix_apply, Equiv.swap_apply_left] using
      hpivot (ρ i) (κ j) (Fin.le_swap_apply_of_le k r hkr i hti)
        (Fin.le_swap_apply_of_le k c hkc j htj)


/-- A completed stored prefix, after releasing its residual workspace, writes the two
canonical factors and both actual recorded pivot logs. Earlier positive-quality pivots yield
an exact factorization even on singular inputs, and every multiplier is bounded by reciprocal
quality. A fixed-column policy also yields the actual identity column log. -/
theorem State.writeBlocks_pop {initial final : Store P ℝ} {tag : P}
    {A : Matrix (Fin N) (Fin N) ℝ} {L U Hr Hc lo uo hro hco : ℕ}
    {α : ℝ} {fixedColumns : Bool} (hα : 0 < α) (hα₁ : α ≤ 1)
    (hs : State (initial.push (tag, Array.replicate (N * N) none)) tag A
      initial.size L U Hr Hc lo uo hro hco N final α fixedColumns)
    (hLcap : Writable initial tag L lo (N * N)) (hUcap : Writable initial tag U uo (N * N))
    (hRcap : Writable initial tag Hr hro N) (hCcap : Writable initial tag Hc hco N)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc) :
    ∃ p q : Fin N → Fin N,
      initial.writeBlocks tag [(L, lo, N * N), (U, uo, N * N), (Hr, hro, N), (Hc, hco, N)]
        [flatten (luLower (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))),
          flatten (luUpper (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))),
          Array.ofFn (fun j => ((p j).val : ℝ)),
          Array.ofFn (fun j => ((q j).val : ℝ))] = some final.pop ∧
      (∀ j, j ≤ p j) ∧ (∀ j, j ≤ q j) ∧
      IsLU (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))
        (luLower (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N)))
        (luUpper (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))) ∧
      (∀ i j, |luLower (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N)) i j| ≤ α⁻¹) ∧
      Holds final.pop tag L lo
        (luLower (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))) ∧
      Holds final.pop tag U uo
        (luUpper (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))) ∧
      (∀ j : Fin N, Store.read final.pop tag Hr (hro + j) = some ((p j).val : ℝ)) ∧
      (∀ j : Fin N, Store.read final.pop tag Hc (hco + j) = some ((q j).val : ℝ)) ∧
      (fixedColumns = true → ∀ j, q j = j) := by
  obtain ⟨p, q, F, G, -, hF, hG, hFpref, hGpref, hmax, hlogR, hlogC⟩ := hs.values
  have hFeq : F = luLower (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N)) := by
    ext i j
    exact hFpref i j j.isLt
  have hGeq : G = luUpper (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N)) := by
    ext i j
    exact hGpref i j i.isLt
  have hsize : final.size = initial.size + 1 := by
    simpa only [Store.size_shape, Array.size_push] using congrArg Array.size hs.frame.shape
  have hLb : 0 < N → L < initial.size := fun hN => hLcap.lt_size (Nat.mul_pos hN hN)
  have hUb : 0 < N → U < initial.size := fun hN => hUcap.lt_size (Nat.mul_pos hN hN)
  have hRb : 0 < N → Hr < initial.size := fun hN => hRcap.lt_size hN
  have hCb : 0 < N → Hc < initial.size := fun hN => hCcap.lt_size hN
  have hFpop : Holds final.pop tag L lo F := fun i j => by
    rw [Store.read_pop_of_lt (by have := hLb (Nat.zero_lt_of_lt i.isLt); omega)]
    exact hF i j
  have hGpop : Holds final.pop tag U uo G := fun i j => by
    rw [Store.read_pop_of_lt (by have := hUb (Nat.zero_lt_of_lt i.isLt); omega)]
    exact hG i j
  have hRpop : ∀ j : Fin N, Store.read final.pop tag Hr (hro + j) = some ((p j).val : ℝ) := by
    intro j
    rw [Store.read_pop_of_lt (by have := hRb (Nat.zero_lt_of_lt j.isLt); omega)]
    exact (hlogR j j.isLt).1
  have hCpop : ∀ j : Fin N, Store.read final.pop tag Hc (hco + j) = some ((q j).val : ℝ) := by
    intro j
    rw [Store.read_pop_of_lt (by have := hCb (Nat.zero_lt_of_lt j.isLt); omega)]
    exact (hlogC j j.isLt).1
  have hshape : Store.shape final.pop = initial.shape := by
    rw [Store.shape_pop, hs.frame.shape]
    simp only [Store.shape, Array.map_push, Array.pop_push]
  have hwrite := writeBlocks_factors_histories (initial := initial) (final := final.pop)
    F G (fun j => ((p j).val : ℝ)) (fun j => ((q j).val : ℝ)) hLU hLR hLC hUR hUC hRC
    hshape hFpop hGpop hRpop hCpop (fun prec b i hbL hbU hbR hbC => by
      by_cases hb : b < initial.size
      · rw [Store.read_pop_of_lt (by omega),
          hs.frame.outside prec b i (Or.inl (by omega)) hbL hbU hbR hbC,
          Store.read_push_of_lt hb]
      · exact (Store.read_eq_none_of_size_le (s := final.pop)
          (by simp only [Array.size_pop]; omega)).trans
          (Store.read_eq_none_of_size_le (s := initial) (by omega)).symm)
  have hmax' : ∀ j i : Fin N, j ≤ i →
      α * ‖gaussState (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N)) j i j‖ ≤
        ‖gaussState (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N)) j j j‖ := by
    intro j i hji
    simpa only [Real.norm_eq_abs] using hmax j i j.isLt hji
  refine ⟨p, q, ?_, (fun j => (hlogR j j.isLt).2), (fun j => (hlogC j j.isLt).2.1),
    isLU_luLower_luUpper_of_forall_mul_norm_le hα hmax', (fun i j => ?_), ?_, ?_,
    hRpop, hCpop, fun hfixed j => (hlogC j j.isLt).2.2 hfixed⟩
  · simpa only [hFeq, hGeq] using hwrite
  · simpa only [Real.norm_eq_abs] using norm_luLower_apply_le_inv hα hα₁ hmax' i j
  · simpa only [hFeq] using hFpop
  · simpa only [hGeq] using hGpop

end NLAlib.Computation.PLUQ
