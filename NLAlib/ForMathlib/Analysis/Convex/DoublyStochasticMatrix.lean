/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Tactic.GCongr
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.Birkhoff
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Balanced submatrices and products

A quantitative Hall argument extracts a scaled doubly stochastic submatrix and controls the
product of its row averages. Upstream candidate for Mathlib.

## Main results

* `Matrix.exists_smul_doublyStochastic_le_of_col_sum_one`.
-/
@[expose] public section

open scoped BigOperators

namespace Matrix

universe u

variable {n : Type u}

private theorem sq_le_card_mul_sum_sq_of_deficiency [Fintype n]
    (C : Matrix n n ℝ) (t : ℝ) (ht : 0 ≤ t) (S N : Finset n) (hSN : N.card < S.card)
    (hSle : (S.card : ℝ) * t ≤ ∑ j ∈ N, (∑ i : n, C i j)) :
    t ^ 2 ≤ (Fintype.card n : ℝ) * ∑ j : n, ((∑ i : n, C i j) - t) ^ 2 := by
  classical
  let e : n → ℝ := fun j => (∑ i : n, C i j) - t
  have hE : t ≤ ∑ j ∈ N, e j := by
    have h1 : (S.card : ℝ) * t ≤ ∑ j ∈ N, (e j + t) := by
      calc
        (S.card : ℝ) * t ≤ ∑ j ∈ N, (∑ i : n, C i j) := hSle
        _ = ∑ j ∈ N, (e j + t) := by
          apply Finset.sum_congr rfl
          intro j _
          dsimp [e]
          ring
    have h2 : (∑ j ∈ N, (e j + t)) = (∑ j ∈ N, e j) + (N.card : ℝ) * t := by
      rw [Finset.sum_add_distrib]
      simp
    have h3 : (S.card : ℝ) * t - (N.card : ℝ) * t ≤ ∑ j ∈ N, e j := by
      linarith
    have hd : (N.card : ℝ) + 1 ≤ S.card := by exact_mod_cast hSN
    linarith [mul_le_mul_of_nonneg_right hd ht]
  have hsq : t ^ 2 ≤ (∑ j ∈ N, e j) ^ 2 := pow_le_pow_left₀ ht hE 2
  have hcs : (∑ j ∈ N, e j) ^ 2 ≤ (N.card : ℝ) * ∑ j ∈ N, e j ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq N (fun _ => (1 : ℝ)) e
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using h
  have hsqN : (∑ j ∈ N, e j ^ 2) ≤ ∑ j : n, e j ^ 2 := by
    simpa using
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ N)
        (fun j _ _ => sq_nonneg _))
  have hNle0 : (N.card : ℝ) ≤ ((Finset.univ : Finset n).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card (Finset.subset_univ N))
  have hNle : (N.card : ℝ) ≤ (Fintype.card n : ℝ) := by
    simpa using hNle0
  calc
    t ^ 2 ≤ (∑ j ∈ N, e j) ^ 2 := hsq
    _ ≤ (N.card : ℝ) * ∑ j ∈ N, e j ^ 2 := hcs
    _ ≤ (N.card : ℝ) * ∑ j : n, e j ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsqN (Nat.cast_nonneg _)
    _ ≤ (Fintype.card n : ℝ) * ∑ j : n, e j ^ 2 := by
      exact mul_le_mul_of_nonneg_right hNle (Finset.sum_nonneg (fun j _ => sq_nonneg _))
    _ = (Fintype.card n : ℝ) * ∑ j : n, ((∑ i : n, C i j) - t) ^ 2 := by
      simp [e]

/-- If a nonnegative matrix with common row sum $t\ge0$ has no supported
permutation, its squared column deviations satisfy this dimension-multiplied
lower bound. Source: the residual step of GGOW, arXiv:1511.03730v4, Claim 3.3,
proved here using Hall's theorem and finite Cauchy–Schwarz. -/
theorem sq_le_card_mul_sum_sq_column_sub_of_no_perm_pos [Fintype n]
    (C : Matrix n n ℝ) (t : ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (ht : 0 ≤ t)
    (hrow : ∀ i, (∑ j : n, C i j) = t)
    (hno : ¬ ∃ σ : Equiv.Perm n, ∀ i, 0 < C i (σ i)) :
    t ^ 2 ≤ (Fintype.card n : ℝ) *
      ∑ j : n, ((∑ i : n, C i j) - t) ^ 2 := by
  classical
  let r : n → n → Prop := fun i j => 0 < C i j
  -- Hall: if every subset had a large enough neighbour set we would get a
  -- strictly positive row permutation, contradicting `hno`.
  have hhall : ¬ (∀ S : Finset n,
      S.card ≤ (Finset.univ.filter (fun j => ∃ i ∈ S, r i j)).card) := by
    intro hall
    have hinj : ∃ f : n → n, Function.Injective f ∧ ∀ i, r i (f i) :=
      (Fintype.all_card_le_filter_rel_iff_exists_injective r).mp hall
    rcases hinj with ⟨f, hfinj, hf⟩
    have hbij : Function.Bijective f := hfinj.bijective_of_finite
    refine hno ⟨Equiv.ofBijective f hbij, ?_⟩
    intro i
    exact hf i
  push Not at hhall
  rcases hhall with ⟨S, hS⟩
  let N : Finset n := Finset.univ.filter (fun j => ∃ i ∈ S, r i j)
  have hSN : N.card < S.card := by
    simpa [N] using hS
  -- Nonnegativity: entries of the rows of `S` outside the neighbour set vanish.
  have hC_zero {i j : n} (hi : i ∈ S) (hj : j ∉ N) : C i j = 0 := by
    have hnot : ¬ ∃ i ∈ S, 0 < C i j := by
      intro h
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
    have hle : C i j ≤ 0 := by
      by_contra hgt
      exact hnot ⟨i, hi, lt_of_not_ge hgt⟩
    exact le_antisymm hle (hC i j)
  -- Hence the row sum `t` is already achieved on `N`.
  have hrow_N (i : n) (hi : i ∈ S) : (∑ j ∈ N, C i j) = t := by
    have hsum : (∑ j ∈ N, C i j) = ∑ j ∈ Finset.univ, C i j :=
      Finset.sum_subset (Finset.subset_univ N) (fun j _ hjn => hC_zero hi hjn)
    simpa using hsum.trans (by simpa using hrow i)
  have hsumSN : (∑ i ∈ S, ∑ j ∈ N, C i j) = S.card * t := by
    calc
      (∑ i ∈ S, ∑ j ∈ N, C i j) = ∑ i ∈ S, t := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hrow_N i hi
      _ = S.card * t := by simp
  -- Column sums over `N` dominate the mass already counted on `S`.
  have hcol_le (j : n) : (∑ i ∈ S, C i j) ≤ ∑ i : n, C i j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) ?_
    intro i _ _
    exact hC i j
  have hSle : (S.card : ℝ) * t ≤ ∑ j ∈ N, (∑ i : n, C i j) := by
    calc
      (S.card : ℝ) * t = ∑ j ∈ N, (∑ i ∈ S, C i j) := by
        rw [← hsumSN]
        exact Finset.sum_comm
      _ ≤ ∑ j ∈ N, (∑ i : n, C i j) := by
        exact Finset.sum_le_sum (fun j _ => hcol_le j)
  exact sq_le_card_mul_sum_sq_of_deficiency C t ht S N hSN hSle

/-- A nonnegative row-stochastic matrix whose dimension-multiplied squared
column defect is less than one has a permutation selecting positive entries
in every row. This is the contrapositive of the weighted Hall bound at `t = 1`. -/
theorem exists_perm_pos_of_card_mul_sum_sq_column_sub_lt_one [Fintype n]
    (C : Matrix n n ℝ)
    (hC : ∀ i j, 0 ≤ C i j)
    (hrow : ∀ i, (∑ j : n, C i j) = 1)
    (herr : (Fintype.card n : ℝ) *
      ∑ j : n, ((∑ i : n, C i j) - 1) ^ 2 < 1) :
    ∃ σ : Equiv.Perm n, ∀ i, 0 < C i (σ i) := by
  classical
  by_contra hno
  have hle := sq_le_card_mul_sum_sq_column_sub_of_no_perm_pos C 1 hC zero_le_one hrow hno
  have hle' : (1 : ℝ) ≤ (Fintype.card n : ℝ) *
      ∑ j : n, ((∑ i : n, C i j) - 1) ^ 2 := by
    simpa using hle
  linarith
/-- A nonnegative column-stochastic matrix whose dimension-multiplied squared
row defect is less than one has a permutation selecting positive entries
in every row. Apply the row-stochastic result to the transpose and invert
its supported permutation. -/
theorem exists_perm_pos_of_card_mul_sum_sq_row_sub_lt_one [Fintype n]
    (C : Matrix n n ℝ)
    (hC : ∀ i j, 0 ≤ C i j)
    (hcol : ∀ j, (∑ i : n, C i j) = 1)
    (herr : (Fintype.card n : ℝ) *
      ∑ j : n, ((∑ i : n, C j i) - 1) ^ 2 < 1) :
    ∃ σ : Equiv.Perm n, ∀ i, 0 < C i (σ i) := by
  classical
  obtain ⟨τ, hτ⟩ := exists_perm_pos_of_card_mul_sum_sq_column_sub_lt_one (Matrix.transpose C)
    (by intro i j; simpa using hC j i)
    (by intro i; simpa using hcol i)
    (by simpa [Matrix.transpose_apply] using herr)
  refine ⟨τ.symm, ?_⟩
  intro i
  have hi := hτ (τ.symm i)
  simpa using hi

end Matrix

open scoped Matrix

open Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
omit [DecidableEq n] in
/-- A common-row-sum nonnegative matrix has a balanced nonnegative part
whose residual has no permutation of positive entries. The extracted part
has a common row and column sum between zero and the original row sum.
Source: GGOW, arXiv:1511.03730v4, Claim 3.3. -/
theorem exists_balanced_le_with_no_perm_pos (C : Matrix n n ℝ) (s : ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hs : 0 ≤ s) (hrow : ∀ i, ∑ j, C i j = s) :
    ∃ (D : Matrix n n ℝ) (a : ℝ), 0 ≤ a ∧ a ≤ s ∧
      (∀ i j, 0 ≤ D i j) ∧ (∀ i, ∑ j, D i j = a) ∧
      (∀ j, ∑ i, D i j = a) ∧ (∀ i j, D i j ≤ C i j) ∧
      ¬ ∃ σ : Equiv.Perm n, ∀ i, 0 < (C - D) i (σ i) := by
  classical
  set d : ℕ := #{ij : n × n | C ij.1 ij.2 ≠ 0} with hd
  clear_value d
  induction d using Nat.strongRecOn generalizing C s with
  | ind d ih =>
    by_cases hp : ∃ σ : Equiv.Perm n, ∀ i, 0 < C i (σ i)
    · obtain ⟨σ, hσ⟩ := hp
      obtain ⟨i, _, hi⟩ := exists_min_image univ (fun i => C i (σ i)) univ_nonempty
      let t := C i (σ i)
      let P := σ.permMatrix ℝ
      let N := C - t • P
      have ht : 0 < t := hσ i
      have hmin (j : n) : t ≤ C j (σ j) := hi j (mem_univ j)
      have hts : t ≤ s := by
        rw [← hrow i]
        exact single_le_sum (fun j _ => hC i j) (mem_univ _)
      have hP := mem_doublyStochastic_iff_sum.mp
        (permMatrix_mem_doublyStochastic (σ := σ) (R := ℝ))
      have hN (j k : n) : 0 ≤ N j k := by
        dsimp [N, P]
        simp only [Option.mem_def, Option.some.injEq]
        split_ifs with hjk
        · subst k
          simpa using sub_nonneg.mpr (hmin j)
        · simpa using hC j k
      have hNrow (j : n) : ∑ k, N j k = s - t := by
        simp only [N, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          sum_sub_distrib, ← mul_sum]
        rw [hrow j, hP.2.1 j, mul_one]
      have hdN : #{ij : n × n | N ij.1 ij.2 ≠ 0} < d := by
        rw [hd]
        apply card_lt_card
        apply ssubset_iff_subset_ne.mpr
        refine ⟨?_, ?_⟩
        · intro jk hjk
          simp only [mem_filter_univ] at hjk ⊢
          intro hzero
          have hNzero : N jk.1 jk.2 = 0 := by
            have hPzero : P jk.1 jk.2 = 0 := by
              dsimp [P]
              simp only [Option.mem_def, Option.some.injEq, ite_eq_right_iff, one_ne_zero,
                imp_false]
              intro heq
              exact (hσ jk.1).ne' (by simpa [heq] using hzero)
            simp [N, hzero, hPzero]
          exact hjk hNzero
        · intro heq
          have hmem : (i, σ i) ∈ ({ij : n × n | C ij.1 ij.2 ≠ 0} : Finset (n × n)) := by
            simp [ht.ne', ← show t = C i (σ i) from rfl]
          have hmemN := (Finset.ext_iff.mp heq (i, σ i)).mpr hmem
          simp [N, P, t, Equiv.toPEquiv_apply] at hmemN
      obtain ⟨D, a, ha, has, hD, hDr, hDc, hDN, hno⟩ :=
        ih _ hdN N (s - t) hN (sub_nonneg.mpr hts) hNrow rfl
      refine ⟨t • P + D, t + a, add_nonneg ht.le ha, by linarith, ?_, ?_, ?_, ?_, ?_⟩
      · intro j k
        exact add_nonneg (mul_nonneg ht.le (hP.1 j k)) (hD j k)
      · intro j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          sum_add_distrib, ← mul_sum]
        rw [hP.2.1 j, hDr j, mul_one]
      · intro k
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          sum_add_distrib, ← mul_sum]
        rw [hP.2.2 k, hDc k, mul_one]
      · intro j k
        have h := hDN j k
        change D j k ≤ C j k - t * P j k at h
        change t * P j k + D j k ≤ C j k
        linarith
      · have hres : C - (t • P + D) = N - D := by
          ext j k
          simp only [N, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
          ring
        rw [hres]
        exact hno
    · exact ⟨0, 0, le_rfl, hs, by simp, by simp, by simp, by simpa using hC,
        by simpa using hp⟩

/-- A nonnegative row-stochastic matrix contains a scalar multiple of a
doubly stochastic matrix. The scalar is at least one minus the square root
of the dimension times the squared column-sum defect. This is GGOW,
arXiv:1511.03730v4, Claim 3.3, including a possibly zero extracted part. -/
theorem exists_smul_doublyStochastic_le_of_row_sum_one (C : Matrix n n ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hrow : ∀ i, ∑ j, C i j = 1) :
    ∃ (B : Matrix n n ℝ) (a : ℝ), B ∈ doublyStochastic ℝ n ∧
      0 ≤ a ∧ a ≤ 1 ∧
      1 - Real.sqrt ((Fintype.card n : ℝ) * ∑ j, ((∑ i, C i j) - 1) ^ 2) ≤ a ∧
      ∀ i j, a * B i j ≤ C i j := by
  obtain ⟨D, a, ha, ha1, hD, hDr, hDc, hDC, hno⟩ :=
    exists_balanced_le_with_no_perm_pos C 1 hC zero_le_one hrow
  have hresrow (i : n) : ∑ j, (C - D) i j = 1 - a := by
    simp only [Matrix.sub_apply, sum_sub_distrib, hrow i, hDr i]
  have hHall := sq_le_card_mul_sum_sq_column_sub_of_no_perm_pos
    (C - D) (1 - a) (fun i j => sub_nonneg.mpr (hDC i j))
    (sub_nonneg.mpr ha1) hresrow hno
  have heq (j : n) : (∑ i, (C - D) i j) - (1 - a) = (∑ i, C i j) - 1 := by
    simp only [Matrix.sub_apply, sum_sub_distrib, hDc j]
    ring
  simp_rw [heq] at hHall
  have herr : 0 ≤ (Fintype.card n : ℝ) * ∑ j, ((∑ i, C i j) - 1) ^ 2 :=
    mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)
  have hroot := Real.sq_sqrt herr
  have hroot0 := Real.sqrt_nonneg ((Fintype.card n : ℝ) * ∑ j, ((∑ i, C i j) - 1) ^ 2)
  have hbound : 1 - Real.sqrt ((Fintype.card n : ℝ) * ∑ j, ((∑ i, C i j) - 1) ^ 2) ≤ a := by
    nlinarith
  obtain ⟨B, hB, hDB⟩ := (exists_mem_doublyStochastic_eq_smul_iff ha).mpr ⟨hD, hDr, hDc⟩
  refine ⟨B, a, hB, ha, ha1, hbound, ?_⟩
  intro i j
  simpa only [hDB, Matrix.smul_apply, smul_eq_mul] using hDC i j

/-- The column-stochastic version of finite balanced extraction, with the
defect measured in the row sums. Transposition preserves double stochasticity.
Source: GGOW, arXiv:1511.03730v4, Claim 3.3 in transposed orientation. -/
theorem exists_smul_doublyStochastic_le_of_col_sum_one (C : Matrix n n ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hcol : ∀ j, ∑ i, C i j = 1) :
    ∃ (B : Matrix n n ℝ) (a : ℝ), B ∈ doublyStochastic ℝ n ∧
      0 ≤ a ∧ a ≤ 1 ∧
      1 - Real.sqrt ((Fintype.card n : ℝ) * ∑ i, ((∑ j, C i j) - 1) ^ 2) ≤ a ∧
      ∀ i j, a * B i j ≤ C i j := by
  obtain ⟨B, a, hB, ha, ha1, hbound, hBC⟩ :=
    exists_smul_doublyStochastic_le_of_row_sum_one Cᵀ
      (fun i j => hC j i) hcol
  exact ⟨Bᵀ, a, transpose_mem_doublyStochastic_iff.mpr hB,
    ha, ha1, hbound, fun i j => hBC j i⟩

end Matrix

open scoped Matrix

open Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A doubly stochastic matrix increases the product of positive
coordinates, by rowwise weighted AM--GM and the column-sum identity.
This is the scalar product inequality used in GGOW, Lemma 3.2. -/
theorem prod_le_prod_mulVec_of_mem_doublyStochastic {B : Matrix n n ℝ}
    (hB : B ∈ doublyStochastic ℝ n) (x : n → ℝ) (hx : ∀ j, 0 < x j) :
    (∏ j, x j) ≤ ∏ i, (B *ᵥ x) i := by
  have hrow (i : n) : (∏ j, x j ^ B i j) ≤ (B *ᵥ x) i := by
    exact Real.geom_mean_le_arith_mean_weighted univ (B i) x
      (fun j _ => nonneg_of_mem_doublyStochastic hB)
      (sum_row_of_mem_doublyStochastic hB i) (fun j _ => (hx j).le)
  calc
    (∏ j, x j) = ∏ i, ∏ j, x j ^ B i j := by
      rw [prod_comm]
      apply prod_congr rfl
      intro j _
      rw [← Real.rpow_sum_of_pos (hx j), sum_col_of_mem_doublyStochastic hB j]
      exact (Real.rpow_one _).symm
    _ ≤ ∏ i, (B *ᵥ x) i :=
      prod_le_prod (fun i _ => prod_nonneg fun j _ => Real.rpow_nonneg (hx j).le _)
        (fun i _ => hrow i)

/-- If a nonnegative matrix dominates a nonnegative multiple of a doubly
stochastic matrix, its coordinate product dominates the corresponding
power of that multiple times the original product. -/
theorem mul_prod_le_prod_mulVec_of_doublyStochastic_le {C B : Matrix n n ℝ}
    (hB : B ∈ doublyStochastic ℝ n) {a : ℝ} (ha : 0 ≤ a)
    (hBC : ∀ i j, a * B i j ≤ C i j) (x : n → ℝ) (hx : ∀ j, 0 < x j) :
    a ^ Fintype.card n * (∏ j, x j) ≤ ∏ i, (C *ᵥ x) i := by
  have hBx (i : n) : 0 ≤ (B *ᵥ x) i :=
    sum_nonneg fun j _ => mul_nonneg (nonneg_of_mem_doublyStochastic hB) (hx j).le
  have hmul (i : n) : a * (B *ᵥ x) i ≤ (C *ᵥ x) i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply sum_le_sum
    intro j _
    calc
      a * (B i j * x j) = (a * B i j) * x j := (mul_assoc _ _ _).symm
      _ ≤ C i j * x j := mul_le_mul_of_nonneg_right (hBC i j) (hx j).le
  calc
    a ^ Fintype.card n * (∏ j, x j) ≤ a ^ Fintype.card n * (∏ i, (B *ᵥ x) i) :=
      mul_le_mul_of_nonneg_left (prod_le_prod_mulVec_of_mem_doublyStochastic hB x hx)
        (pow_nonneg ha _)
    _ = ∏ i, a * (B *ᵥ x) i := by rw [prod_mul_distrib]; simp
    _ ≤ ∏ i, (C *ᵥ x) i :=
      prod_le_prod (fun i _ => mul_nonneg ha (hBx i)) (fun i _ => hmul i)
omit [DecidableEq n] in
/-- A column-stochastic nonnegative matrix with squared row-sum defect
at most $\varepsilon\le 1/(n+1)$ has the product lower bound
`(1 - sqrt (card n * ε)) ^ card n`. This is GGOW, arXiv:1511.03730v4,
Lemma 3.2 in the orientation used by Lemma 3.4. -/
theorem mul_prod_le_prod_mulVec_of_col_sum_one (C : Matrix n n ℝ)
    (hC : ∀ i j, 0 ≤ C i j) (hcol : ∀ j, ∑ i, C i j = 1)
    {ε : ℝ} (hε : ∑ i, ((∑ j, C i j) - 1) ^ 2 ≤ ε)
    (hεsmall : ε ≤ 1 / ((Fintype.card n : ℝ) + 1))
    (x : n → ℝ) (hx : ∀ j, 0 < x j) :
    (1 - Real.sqrt ((Fintype.card n : ℝ) * ε)) ^ Fintype.card n *
      (∏ j, x j) ≤ ∏ i, (C *ᵥ x) i := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  have hε0 : 0 ≤ ε := (sum_nonneg fun _ _ => sq_nonneg _).trans hε
  have hn0 : (0 : ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
  have hεbound := (le_div_iff₀ (show (0 : ℝ) < (Fintype.card n : ℝ) + 1 by positivity)).mp hεsmall
  have hsmall : (Fintype.card n : ℝ) * ε ≤ 1 := by nlinarith
  have hbase : 0 ≤ 1 - Real.sqrt ((Fintype.card n : ℝ) * ε) :=
    sub_nonneg.mpr (Real.sqrt_le_one.mpr hsmall)
  obtain ⟨B, a, hB, ha, _, hbound, hBC⟩ :=
    exists_smul_doublyStochastic_le_of_col_sum_one C hC hcol
  have hbasea : 1 - Real.sqrt ((Fintype.card n : ℝ) * ε) ≤ a := by
    have hroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hε hn0)
    linarith
  calc
    _ ≤ a ^ Fintype.card n * (∏ j, x j) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbase hbasea _)
        (prod_nonneg fun j _ => (hx j).le)
    _ ≤ _ := mul_prod_le_prod_mulVec_of_doublyStochastic_le hB ha hBC x hx

omit [DecidableEq n] in
/-- A nonnegative matrix with a supported permutation cannot reduce the
number of nonzero coordinates of a nonnegative vector. Each positive
coordinate is sent through its matched positive matrix entry. -/
theorem card_nonzero_le_card_nonzero_mulVec_of_perm_pos
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (C : Matrix n n R)
    (hC : ∀ i j, 0 ≤ C i j) (σ : Equiv.Perm n) (hσ : ∀ i, 0 < C i (σ i))
    (x : n → R) (hx : ∀ j, 0 ≤ x j) :
    Fintype.card {j // x j ≠ 0} ≤ Fintype.card {i // (C *ᵥ x) i ≠ 0} := by
  classical
  let f : {j // x j ≠ 0} → {i // (C *ᵥ x) i ≠ 0} := fun j =>
    ⟨σ.symm j, by
      have hxpos : 0 < x j := lt_of_le_of_ne (hx j) j.property.symm
      have hterm : 0 < C (σ.symm j) (σ (σ.symm j)) * x (σ (σ.symm j)) :=
        mul_pos (hσ _) (by simpa only [Equiv.apply_symm_apply] using hxpos)
      have hle : C (σ.symm j) (σ (σ.symm j)) * x (σ (σ.symm j)) ≤
          (C *ᵥ x) (σ.symm j) := by
        change _ ≤ ∑ k, C (σ.symm j) k * x k
        exact Finset.single_le_sum
          (fun k _ => mul_nonneg (hC (σ.symm j) k) (hx k))
          (Finset.mem_univ (σ (σ.symm j)))
      exact (hterm.trans_le hle).ne'⟩
  apply Fintype.card_le_of_injective f
  intro a b hab
  apply Subtype.ext
  apply σ.symm.injective
  exact congrArg Subtype.val hab


end Matrix
