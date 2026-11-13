/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Tape
public import NLAlib.Eigensolvers.SpectralBisectionSamples

/-!
# Lazy sampling for spectral bisection

On the ideal tape of law `NLAlib.Computation.tapeLaw`, the tree of ideal samples of a spectral
bisection run (`NLAlib.eighIdealTree`) is independent with law `NLAlib.eighSampleLaw` at every path:
the positions a node reads are decided by earlier samples and are disjoint from every other node's.

## Main results

* `NLAlib.iIndepFun_eighIdealTree`: lazy sampling.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped Matrix

namespace NLAlib

open Computation

/-! ### The tree of ideal samples, one level at a time -/

section Tree

variable {F : Type*} (M : FloatMachine F ℝ ℂ) (N signFuel D : ℕ) (R₀ β : F)

/-- The children of a possible node under a sample. -/
private def eighKids (xo : Option (EighNode F)) (s : EighSample ℝ ℂ N) :
    Option (EighNode F) × Option (EighNode F) :=
  (xo.bind fun x => eighChild M N signFuel R₀ β x s true,
    xo.bind fun x => eighChild M N signFuel R₀ β x s false)

/-- The slot of the child on side `b`, for the children `c` of a node at slot `lo`. -/
private def eighKidSlot (lo : ℕ) (c : Option (EighNode F) × Option (EighNode F)) (b : Bool) : ℕ :=
  if b then lo else lo + (c.1.map EighNode.k).getD 0

/-- The child on side `b`. -/
private def eighKid (c : Option (EighNode F) × Option (EighNode F)) (b : Bool) :
    Option (EighNode F) :=
  if b then c.1 else c.2

/-- Below no node the tree does not depend on the slot. -/
private lemma eighIdealTree_none_slot (ξ : Dist → ℕ → ℝ) (a : List Bool) :
    ∀ (d lo lo' : ℕ) (pre : List Bool),
      eighIdealTree M N signFuel D R₀ β ξ d lo none pre a =
        eighIdealTree M N signFuel D R₀ β ξ d lo' none pre a := by
  induction a with
  | nil => intro d lo lo' pre; simp only [eighIdealTree, Option.map_none, eighIdealSample]
  | cons b a ih => intro d lo lo' pre; simp only [eighIdealTree]; exact ih _ _ _ _

/-- The tree one level down: the subtree on side `b` is the tree of the child on side `b` at
its slot. -/
private lemma eighIdealTree_cons (ξ : Dist → ℕ → ℝ) (d lo : ℕ) (xo : Option (EighNode F))
    (pre : List Bool) (b : Bool) (a : List Bool) :
    eighIdealTree M N signFuel D R₀ β ξ d lo xo pre (b :: a) =
      eighIdealTree M N signFuel D R₀ β ξ (d + 1)
        (eighKidSlot lo (eighKids M N signFuel R₀ β xo
          (eighIdealSample ξ N D d lo (xo.map EighNode.k) pre)) b)
        (eighKid (eighKids M N signFuel R₀ β xo
          (eighIdealSample ξ N D d lo (xo.map EighNode.k) pre)) b) (pre ++ [b]) a := by
  cases xo with
  | none => cases b <;> simp [eighIdealTree, eighKids, eighKidSlot, eighKid]
  | some x =>
    simp only [eighIdealTree, eighKids, eighKidSlot, eighKid, Option.bind_some, Option.map_some]
    unfold eighChild
    generalize eighStep M N signFuel R₀ β x.A x.R x.ε x.ℓ
      (eighIdealSample ξ N D d lo (some x.k) pre) = st
    cases st with
    | leaf U e => cases b <;> simp
    | shift b' A' σ =>
      cases b <;> cases b' <;> simp only [Bool.false_eq_true, if_false, if_true, Option.map_some,
        Option.getD_some, Option.map_none, Option.getD_none, add_zero, reduceCtorEq]
      exact eighIdealTree_none_slot M N signFuel D R₀ β ξ a _ _ _ _
    | split kp hkp Qp Qm Ap Am σ => cases b <;> simp

end Tree

/-! ### The positions a node reads -/

section Positions

/-- The uniform position of the seed of a node of size `ko` at slot `lo` of depth `d`, reached by
the path `pre`: its static position below the depth budget, and a fresh one otherwise. -/
private def eighRootU (N D d lo : ℕ) (ko : Option ℕ) (pre : List Bool) : ℕ :=
  match ko with
  | some _ => if d < D then N * d + lo else N * D + Encodable.encode pre
  | none => N * D + Encodable.encode pre

/-- The complex Gaussian position of entry $(i, j)$ of the test matrix on side `b` of a node. -/
private def eighRootZ (N D d lo : ℕ) (ko : Option ℕ) (pre : List Bool) (b : Bool)
    (i j : Fin N) : ℕ :=
  match ko with
  | some k =>
    if d < D ∧ (i : ℕ) < k ∧ (j : ℕ) < k then
      2 * (N * N) * d + N * (2 * (lo + j) + if b then 0 else 1) + i
    else 2 * (N * N) * D + Encodable.encode (pre, b, (i : ℕ), (j : ℕ))
  | none => 2 * (N * N) * D + Encodable.encode (pre, b, (i : ℕ), (j : ℕ))

private lemma eighIdealSample_eq_eighReadSample (ξ : Dist → ℕ → ℝ) (N D d lo : ℕ)
    (ko : Option ℕ) (pre : List Bool) :
    eighIdealSample ξ N D d lo ko pre =
      eighReadSample N (eighRootU N D d lo ko pre) (eighRootZ N D d lo ko pre) ξ := by
  cases ko with
  | none => rfl
  | some k =>
    unfold eighIdealSample eighReadSample eighRootU eighRootZ
    by_cases hd : d < D
    · simp only [hd, if_true, true_and]
      congr 1
      funext b
      ext i j
      simp only [Matrix.of_apply]
      split_ifs <;> rfl
    · simp only [hd, if_false, false_and]

/-- The fresh uniform positions of the paths through `pre`. -/
private def eighFreshU (N D : ℕ) (pre : List Bool) : Set ℕ :=
  {r | ∃ a, pre <+: a ∧ r = N * D + Encodable.encode a}

/-- The fresh complex Gaussian positions of the paths through `pre`. -/
private def eighFreshZ (N D : ℕ) (pre : List Bool) : Set ℕ :=
  {z | ∃ (a : List Bool) (b : Bool) (i j : ℕ), pre <+: a ∧
    z = 2 * (N * N) * D + Encodable.encode (a, b, i, j)}

/-- The uniform positions the subtree of a node of size `ko` at slot `lo` of depth `d` may read:
its own seed, the static seeds of its range at the depths below, and the fresh positions of the
paths through `pre`. -/
private def eighRegionU (N D d lo : ℕ) (ko : Option ℕ) (pre : List Bool) : Set ℕ :=
  {r | ∃ k, ko = some k ∧ ∃ d' j, d ≤ d' ∧ d' < D ∧ ((d' = d ∧ j = lo) ∨ (lo ≤ j ∧ j < lo + k)) ∧
    r = N * d' + j} ∪ eighFreshU N D pre

/-- The complex Gaussian positions the subtree of a node may read. -/
private def eighRegionZ (N D d lo : ℕ) (ko : Option ℕ) (pre : List Bool) : Set ℕ :=
  {z | ∃ k, ko = some k ∧ ∃ d' j s i, d ≤ d' ∧ d' < D ∧ lo ≤ j ∧ j < lo + k ∧ s < 2 ∧ i < N ∧
    z = 2 * (N * N) * d' + N * (2 * j + s) + i} ∪ eighFreshZ N D pre

/-- A node of size `ko` at slot `lo` lies inside the root range. -/
private def EighInv (N lo : ℕ) (ko : Option ℕ) : Prop := ∀ k, ko = some k → lo + k ≤ N

/-- A child of size `ko'` at slot `lo'` fits in the range of its parent of size `ko` at slot `lo`,
and is not empty. -/
private def EighFits (lo : ℕ) (ko : Option ℕ) (lo' : ℕ) (ko' : Option ℕ) : Prop :=
  ∀ k', ko' = some k' → 1 ≤ k' ∧ ∃ k, ko = some k ∧ lo ≤ lo' ∧ lo' + k' ≤ lo + k

private lemma eq_of_mul_add_eq_of_lt {N d₁ d₂ j₁ j₂ : ℕ} (h₁ : j₁ < N) (h₂ : j₂ < N)
    (h : N * d₁ + j₁ = N * d₂ + j₂) : d₁ = d₂ ∧ j₁ = j₂ := by
  have := (Nat.add_mul_eq_add_mul_iff_of_lt (j := d₁) (j' := d₂) h₁ h₂).mp (by omega)
  exact ⟨this.2, this.1⟩

private lemma mul_add_lt_mul_of_lt {N d D j : ℕ} (hj : j < N) (hd : d < D) : N * d + j < N * D :=
  calc N * d + j < N * (d + 1) := by rw [mul_add, mul_one]; omega
    _ ≤ N * D := Nat.mul_le_mul_left _ hd

private lemma mul_add_le_mul_of_le {N d D j : ℕ} (hj : j ≤ N) (hd : d < D) : N * d + j ≤ N * D :=
  calc N * d + j ≤ N * (d + 1) := by rw [mul_add, mul_one]; omega
    _ ≤ N * D := Nat.mul_le_mul_left _ hd

private lemma gaussPos_eq (N d j s i : ℕ) :
    2 * (N * N) * d + N * (2 * j + s) + i = 2 * N * (N * d + j) + (N * s + i) := by ring

private lemma gaussPos_inj {N d₁ d₂ j₁ j₂ s₁ s₂ i₁ i₂ : ℕ} (hj₁ : j₁ < N) (hj₂ : j₂ < N)
    (hs₁ : s₁ < 2) (hs₂ : s₂ < 2) (hi₁ : i₁ < N) (hi₂ : i₂ < N)
    (h : 2 * (N * N) * d₁ + N * (2 * j₁ + s₁) + i₁ = 2 * (N * N) * d₂ + N * (2 * j₂ + s₂) + i₂) :
    d₁ = d₂ ∧ j₁ = j₂ ∧ s₁ = s₂ ∧ i₁ = i₂ := by
  rw [gaussPos_eq, gaussPos_eq] at h
  have hl₁ : N * s₁ + i₁ < 2 * N := by interval_cases s₁ <;> omega
  have hl₂ : N * s₂ + i₂ < 2 * N := by interval_cases s₂ <;> omega
  obtain ⟨hc, hr⟩ := eq_of_mul_add_eq_of_lt hl₁ hl₂ h
  obtain ⟨hd, hj⟩ := eq_of_mul_add_eq_of_lt hj₁ hj₂ hc
  obtain ⟨hs, hi⟩ := eq_of_mul_add_eq_of_lt hi₁ hi₂ hr
  exact ⟨hd, hj, hs, hi⟩

private lemma gaussPos_lt {N d D j s i : ℕ} (hj : j < N) (hd : d < D) (hs : s < 2) (hi : i < N) :
    2 * (N * N) * d + N * (2 * j + s) + i < 2 * (N * N) * D := by
  rw [gaussPos_eq]
  have h1 := mul_add_lt_mul_of_lt hj hd
  have hl : N * s + i < 2 * N := by interval_cases s <;> omega
  calc 2 * N * (N * d + j) + (N * s + i) < 2 * N * (N * d + j) + 2 * N := by omega
    _ = 2 * N * (N * d + j + 1) := by ring
    _ ≤ 2 * N * (N * D) := Nat.mul_le_mul_left _ h1
    _ = 2 * (N * N) * D := by ring

private lemma encode_ne_zero_of_ne_nil {a : List Bool} (h : a ≠ []) : Encodable.encode a ≠ 0 := by
  cases a with
  | nil => exact absurd rfl h
  | cons b a => simp [Encodable.encode_list_cons]

private lemma encode_fst_eq {a a' : List Bool} {b b' : Bool} {i j i' j' : ℕ}
    (h : Encodable.encode (a, b, i, j) = Encodable.encode (a', b', i', j')) : a = a' :=
  (Prod.ext_iff.mp (Encodable.encode_injective h)).1

private lemma prefix_of_append_prefix {pre a : List Bool} {b : Bool} (h : pre ++ [b] <+: a) :
    pre <+: a :=
  (List.prefix_append pre [b]).trans h

private lemma length_lt_of_append_prefix {pre a : List Bool} {b : Bool} (h : pre ++ [b] <+: a) :
    pre.length < a.length := by
  have := h.length_le
  simp only [List.length_append, List.length_singleton] at this
  omega

private lemma not_append_prefix_both {pre a : List Bool} (h₁ : pre ++ [true] <+: a)
    (h₂ : pre ++ [false] <+: a) : False := by
  have h := (List.prefix_of_prefix_length_le h₁ h₂ (by simp)).eq_of_length (by simp)
  simp at h

variable {N D d lo lo' : ℕ} {ko ko' : Option ℕ} {pre : List Bool} {b : Bool}

private lemma side_lt_two (b : Bool) : (if b then 0 else 1 : ℕ) < 2 := by cases b <;> simp

private lemma eighRootU_mem : eighRootU N D d lo ko pre ∈ eighRegionU N D d lo ko pre := by
  cases ko with
  | none => exact Or.inr ⟨pre, List.prefix_refl _, rfl⟩
  | some k =>
    simp only [eighRootU]
    split_ifs with hd
    · exact Or.inl ⟨k, rfl, d, lo, le_rfl, hd, Or.inl ⟨rfl, rfl⟩, rfl⟩
    · exact Or.inr ⟨pre, List.prefix_refl _, rfl⟩

private lemma eighRootZ_mem (b : Bool) (i j : Fin N) :
    eighRootZ N D d lo ko pre b i j ∈ eighRegionZ N D d lo ko pre := by
  cases ko with
  | none => exact Or.inr ⟨pre, b, i, j, List.prefix_refl _, rfl⟩
  | some k =>
    simp only [eighRootZ]
    by_cases h : d < D ∧ (i : ℕ) < k ∧ (j : ℕ) < k
    · rw [if_pos h]
      exact Or.inl ⟨k, rfl, d, lo + j, _, i, le_rfl, h.1, by omega, by omega,
        side_lt_two b, i.2, rfl⟩
    · rw [if_neg h]
      exact Or.inr ⟨pre, b, i, j, List.prefix_refl _, rfl⟩

private lemma eighRegionU_subset (hF : EighFits lo ko lo' ko') :
    eighRegionU N D (d + 1) lo' ko' (pre ++ [b]) ⊆ eighRegionU N D d lo ko pre := by
  rintro r (⟨k', hk', d', j, hd1, hd2, hj, rfl⟩ | ⟨a, ha, rfl⟩)
  · obtain ⟨h1, k, hk, hlo, hhi⟩ := hF k' hk'
    exact Or.inl ⟨k, hk, d', j, by omega, hd2, Or.inr (by omega), rfl⟩
  · exact Or.inr ⟨a, prefix_of_append_prefix ha, rfl⟩

private lemma eighRegionZ_subset (hF : EighFits lo ko lo' ko') :
    eighRegionZ N D (d + 1) lo' ko' (pre ++ [b]) ⊆ eighRegionZ N D d lo ko pre := by
  rintro z (⟨k', hk', d', j, s, i, hd1, hd2, hj1, hj2, hs, hi, rfl⟩ | ⟨a, b', i, j, ha, rfl⟩)
  · obtain ⟨h1, k, hk, hlo, hhi⟩ := hF k' hk'
    exact Or.inl ⟨k, hk, d', j, s, i, by omega, hd2, by omega, by omega, hs, hi, rfl⟩
  · exact Or.inr ⟨a, b', i, j, prefix_of_append_prefix ha, rfl⟩

private lemma eighRootU_not_mem (hI : EighInv N lo ko) (hF : EighFits lo ko lo' ko') :
    eighRootU N D d lo ko pre ∉ eighRegionU N D (d + 1) lo' ko' (pre ++ [b]) := by
  rintro (⟨k', hk', d', j, hd1, hd2, hj, h⟩ | ⟨a, ha, h⟩)
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF k' hk'
    have hk := hI k rfl
    have hjN : j < N := by omega
    simp only [eighRootU] at h
    split_ifs at h with hd
    · have := (eq_of_mul_add_eq_of_lt (by omega) hjN h).1
      omega
    · have := mul_add_lt_mul_of_lt hjN hd2
      omega
  · have hne : a ≠ [] := by
      intro h'
      have := length_lt_of_append_prefix ha
      simp [h'] at this
    have he := encode_ne_zero_of_ne_nil hne
    cases ko with
    | none =>
      simp only [eighRootU, add_right_inj] at h
      have := length_lt_of_append_prefix ha
      rw [Encodable.encode_injective h] at this
      omega
    | some k =>
      simp only [eighRootU] at h
      split_ifs at h with hd
      · have := mul_add_le_mul_of_le (N := N) (j := lo) (by have := hI k rfl; omega) hd
        omega
      · simp only [add_right_inj] at h
        have := length_lt_of_append_prefix ha
        rw [Encodable.encode_injective h] at this
        omega

private lemma eighRootZ_not_mem (hI : EighInv N lo ko) (hF : EighFits lo ko lo' ko') (b' : Bool)
    (i j : Fin N) :
    eighRootZ N D d lo ko pre b' i j ∉ eighRegionZ N D (d + 1) lo' ko' (pre ++ [b]) := by
  rintro (⟨k', hk', d', j', s, i', hd1, hd2, hj1, hj2, hs, hi, h⟩ | ⟨a, b'', i', j', ha, h⟩)
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF k' hk'
    have hk := hI k rfl
    simp only [eighRootZ] at h
    by_cases hc : d < D ∧ (i : ℕ) < k ∧ (j : ℕ) < k
    · rw [if_pos hc] at h
      have := (gaussPos_inj (by omega) (by omega) (side_lt_two b') hs i.2 hi h).1
      omega
    · rw [if_neg hc] at h
      have := gaussPos_lt (N := N) (j := j') (by omega) hd2 hs hi
      omega
  · cases ko with
    | none =>
      simp only [eighRootZ, add_right_inj] at h
      have := length_lt_of_append_prefix ha
      rw [encode_fst_eq h] at this
      omega
    | some k =>
      have hk := hI k rfl
      simp only [eighRootZ] at h
      by_cases hc : d < D ∧ (i : ℕ) < k ∧ (j : ℕ) < k
      · rw [if_pos hc] at h
        have := gaussPos_lt (N := N) (j := lo + j) (by omega) hc.1 (side_lt_two b') i.2
        omega
      · rw [if_neg hc] at h
        simp only [add_right_inj] at h
        have := length_lt_of_append_prefix ha
        rw [encode_fst_eq h] at this
        omega

private lemma disjoint_eighRegionU {lo₁ lo₂ : ℕ} {ko₁ ko₂ : Option ℕ} (hI : EighInv N lo ko)
    (hF₁ : EighFits lo ko lo₁ ko₁) (hF₂ : EighFits lo ko lo₂ ko₂)
    (hS : ∀ k₁ k₂, ko₁ = some k₁ → ko₂ = some k₂ → lo₁ + k₁ ≤ lo₂) :
    Disjoint (eighRegionU N D (d + 1) lo₁ ko₁ (pre ++ [true]))
      (eighRegionU N D (d + 1) lo₂ ko₂ (pre ++ [false])) := by
  rw [Set.disjoint_left]
  rintro r (⟨k₁, hk₁, d₁, j₁, -, hd₁, hj₁, rfl⟩ | ⟨a₁, ha₁, rfl⟩)
    (⟨k₂, hk₂, d₂, j₂, -, hd₂, hj₂, h⟩ | ⟨a₂, ha₂, h⟩)
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF₁ k₁ hk₁
    obtain ⟨h1', k', hk', hlo', hhi'⟩ := hF₂ k₂ hk₂
    cases hk'
    have hk := hI k rfl
    have := hS k₁ k₂ hk₁ hk₂
    have := (eq_of_mul_add_eq_of_lt (by omega) (by omega) h).2
    omega
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF₁ k₁ hk₁
    have := mul_add_lt_mul_of_lt (N := N) (j := j₁) (by have := hI k rfl; omega) hd₁
    omega
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF₂ k₂ hk₂
    have := mul_add_lt_mul_of_lt (N := N) (j := j₂) (by have := hI k rfl; omega) hd₂
    omega
  · simp only [add_right_inj] at h
    rw [Encodable.encode_injective h] at ha₁
    exact not_append_prefix_both ha₁ ha₂

private lemma disjoint_eighRegionZ {lo₁ lo₂ : ℕ} {ko₁ ko₂ : Option ℕ} (hI : EighInv N lo ko)
    (hF₁ : EighFits lo ko lo₁ ko₁) (hF₂ : EighFits lo ko lo₂ ko₂)
    (hS : ∀ k₁ k₂, ko₁ = some k₁ → ko₂ = some k₂ → lo₁ + k₁ ≤ lo₂) :
    Disjoint (eighRegionZ N D (d + 1) lo₁ ko₁ (pre ++ [true]))
      (eighRegionZ N D (d + 1) lo₂ ko₂ (pre ++ [false])) := by
  rw [Set.disjoint_left]
  rintro z (⟨k₁, hk₁, d₁, j₁, s₁, i₁, -, hd₁, hj₁, hj₁', hs₁, hi₁, rfl⟩ |
      ⟨a₁, b₁, i₁, j₁, ha₁, rfl⟩)
    (⟨k₂, hk₂, d₂, j₂, s₂, i₂, -, hd₂, hj₂, hj₂', hs₂, hi₂, h⟩ | ⟨a₂, b₂, i₂, j₂, ha₂, h⟩)
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF₁ k₁ hk₁
    obtain ⟨h1', k', hk', hlo', hhi'⟩ := hF₂ k₂ hk₂
    cases hk'
    have hk := hI k rfl
    have := hS k₁ k₂ hk₁ hk₂
    have := (gaussPos_inj (by omega) (by omega) hs₁ hs₂ hi₁ hi₂ h).2.1
    omega
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF₁ k₁ hk₁
    have := gaussPos_lt (N := N) (j := j₁) (by have := hI k rfl; omega) hd₁ hs₁ hi₁
    omega
  · obtain ⟨h1, k, rfl, hlo, hhi⟩ := hF₂ k₂ hk₂
    have := gaussPos_lt (N := N) (j := j₂) (by have := hI k rfl; omega) hd₂ hs₂ hi₂
    omega
  · simp only [add_right_inj] at h
    rw [encode_fst_eq h] at ha₁
    exact not_append_prefix_both ha₁ ha₂

private lemma injective_eighRootZ (hI : EighInv N lo ko) :
    Function.Injective fun p : Bool × Fin N × Fin N =>
      eighRootZ N D d lo ko pre p.1 p.2.1 p.2.2 := by
  rintro ⟨b₁, i₁, j₁⟩ ⟨b₂, i₂, j₂⟩ h
  dsimp only at h
  have hfresh : ∀ {b₁ b₂ : Bool} {i₁ j₁ i₂ j₂ : Fin N},
      2 * (N * N) * D + Encodable.encode (pre, b₁, (i₁ : ℕ), (j₁ : ℕ)) =
        2 * (N * N) * D + Encodable.encode (pre, b₂, (i₂ : ℕ), (j₂ : ℕ)) →
      (b₁, i₁, j₁) = (b₂, i₂, j₂) := by
    intro b₁ b₂ i₁ j₁ i₂ j₂ h
    simp only [add_right_inj] at h
    have := Encodable.encode_injective h
    simp only [Prod.mk.injEq] at this ⊢
    exact ⟨this.2.1, Fin.ext this.2.2.1, Fin.ext this.2.2.2⟩
  cases ko with
  | none => exact hfresh h
  | some k =>
    have hk := hI k rfl
    simp only [eighRootZ] at h
    by_cases hc₁ : d < D ∧ (i₁ : ℕ) < k ∧ (j₁ : ℕ) < k
    · rw [if_pos hc₁] at h
      by_cases hc₂ : d < D ∧ (i₂ : ℕ) < k ∧ (j₂ : ℕ) < k
      · rw [if_pos hc₂] at h
        obtain ⟨-, hj, hs, hi⟩ := gaussPos_inj (by omega) (by omega) (side_lt_two b₁)
          (side_lt_two b₂) i₁.2 i₂.2 h
        have hb : b₁ = b₂ := by cases b₁ <;> cases b₂ <;> first | rfl | simp at hs
        rw [hb, Fin.ext hi, Fin.ext (by omega : (j₁ : ℕ) = j₂)]
      · rw [if_neg hc₂] at h
        have := gaussPos_lt (N := N) (j := lo + j₁) (by omega) hc₁.1 (side_lt_two b₁) i₁.2
        omega
    · rw [if_neg hc₁] at h
      by_cases hc₂ : d < D ∧ (i₂ : ℕ) < k ∧ (j₂ : ℕ) < k
      · rw [if_pos hc₂] at h
        have := gaussPos_lt (N := N) (j := lo + j₂) (by omega) hc₂.1 (side_lt_two b₂) i₂.2
        omega
      · rw [if_neg hc₂] at h
        exact hfresh h

end Positions

/-! ### The σ-algebras of the positions -/

/-- The tape coordinates at the uniform positions `U` and at the Gaussian words of the complex
positions `Z`. -/
private def tapeLift (U Z : Set ℕ) : Set (Dist × ℕ) :=
  {p | (p.1 = .uniform ∧ p.2 ∈ U) ∨ (p.1 = .gaussian ∧ p.2 / 2 ∈ Z)}

private lemma tapeLift_mono {U U' Z Z' : Set ℕ} (hU : U ⊆ U') (hZ : Z ⊆ Z') :
    tapeLift U Z ⊆ tapeLift U' Z' := by
  rintro p (⟨h1, h2⟩ | ⟨h1, h2⟩)
  exacts [Or.inl ⟨h1, hU h2⟩, Or.inr ⟨h1, hZ h2⟩]

private lemma disjoint_tapeLift {U U' Z Z' : Set ℕ} (hU : Disjoint U U') (hZ : Disjoint Z Z') :
    Disjoint (tapeLift U Z) (tapeLift U' Z') := by
  rw [Set.disjoint_left]
  rintro p (⟨h1, h2⟩ | ⟨h1, h2⟩) (⟨h1', h2'⟩ | ⟨h1', h2'⟩)
  · exact Set.disjoint_left.mp hU h2 h2'
  · rw [h1] at h1'; cases h1'
  · rw [h1] at h1'; cases h1'
  · exact Set.disjoint_left.mp hZ h2 h2'

/-- A sample read at positions inside `U` and `Z` is measurable for the coordinates there. -/
private lemma measurable_eighReadSample {N u : ℕ} {z : Bool → Fin N → Fin N → ℕ} {U Z : Set ℕ}
    (hu : u ∈ U) (hz : ∀ b i j, z b i j ∈ Z) :
    Measurable[tapeSigma (tapeLift U Z)] (eighReadSample N u z) := by
  have hc : ∀ p ∈ tapeLift U Z,
      Measurable[tapeSigma (tapeLift U Z)] fun ξ : Dist → ℕ → ℝ => ξ p.1 p.2 :=
    fun p hp => measurable_tapeSigma_apply hp
  have hpi : ∀ {δ : Type} {X : δ → Type} [∀ a, MeasurableSpace (X a)]
      (f : (Dist → ℕ → ℝ) → ∀ a, X a), (∀ a, Measurable[tapeSigma (tapeLift U Z)] fun c => f c a) →
      Measurable[tapeSigma (tapeLift U Z)] f :=
    fun f hf => @measurable_pi_lambda _ _ _ (tapeSigma (tapeLift U Z)) _ f hf
  refine Measurable.prodMk (hc (.uniform, u) (Or.inl ⟨rfl, hu⟩)) ?_
  refine hpi _ fun b => hpi _ fun i => hpi _ fun j => ?_
  refine measurable_complex_mk ((hc (.gaussian, 2 * z b i j) (Or.inr ⟨rfl, ?_⟩)).div_const _)
    ((hc (.gaussian, 2 * z b i j + 1) (Or.inr ⟨rfl, ?_⟩)).div_const _)
  · rw [show 2 * z b i j / 2 = z b i j by omega]; exact hz b i j
  · rw [show (2 * z b i j + 1) / 2 = z b i j by omega]; exact hz b i j

section Regions

variable {N D d lo : ℕ} {ko : Option ℕ} {pre : List Bool}

/-- The coordinates the subtree of a node may read. -/
private def eighRegion (N D d lo : ℕ) (ko : Option ℕ) (pre : List Bool) : Set (Dist × ℕ) :=
  tapeLift (eighRegionU N D d lo ko pre) (eighRegionZ N D d lo ko pre)

/-- The coordinates the sample of a node reads. -/
private def eighRootPos (N D d lo : ℕ) (ko : Option ℕ) (pre : List Bool) : Set (Dist × ℕ) :=
  tapeLift {eighRootU N D d lo ko pre}
    (Set.range fun p : Bool × Fin N × Fin N => eighRootZ N D d lo ko pre p.1 p.2.1 p.2.2)

private lemma measurable_eighIdealSample :
    Measurable[tapeSigma (eighRootPos N D d lo ko pre)]
      fun ξ => eighIdealSample ξ N D d lo ko pre := by
  simp only [eighIdealSample_eq_eighReadSample]
  exact measurable_eighReadSample (U := {eighRootU N D d lo ko pre})
    (Z := Set.range fun p : Bool × Fin N × Fin N => eighRootZ N D d lo ko pre p.1 p.2.1 p.2.2)
    (Set.mem_singleton _) fun b i j => ⟨(b, i, j), rfl⟩

private lemma eighRootPos_subset : eighRootPos N D d lo ko pre ⊆ eighRegion N D d lo ko pre :=
  tapeLift_mono (Set.singleton_subset_iff.mpr eighRootU_mem)
    (Set.range_subset_iff.mpr fun p => eighRootZ_mem p.1 p.2.1 p.2.2)

private lemma disjoint_eighRootPos {lo' : ℕ} {ko' : Option ℕ} {b : Bool} (hI : EighInv N lo ko)
    (hF : EighFits lo ko lo' ko') :
    Disjoint (eighRootPos N D d lo ko pre) (eighRegion N D (d + 1) lo' ko' (pre ++ [b])) := by
  refine disjoint_tapeLift (Set.disjoint_singleton_left.mpr (eighRootU_not_mem hI hF)) ?_
  rw [Set.disjoint_left]
  rintro _ ⟨p, rfl⟩
  exact eighRootZ_not_mem hI hF p.1 p.2.1 p.2.2

private lemma eighRegion_subset {lo' : ℕ} {ko' : Option ℕ} {b : Bool}
    (hF : EighFits lo ko lo' ko') :
    eighRegion N D (d + 1) lo' ko' (pre ++ [b]) ⊆ eighRegion N D d lo ko pre :=
  tapeLift_mono (eighRegionU_subset hF) (eighRegionZ_subset hF)

private lemma disjoint_eighRegion {lo₁ lo₂ : ℕ} {ko₁ ko₂ : Option ℕ} (hI : EighInv N lo ko)
    (hF₁ : EighFits lo ko lo₁ ko₁) (hF₂ : EighFits lo ko lo₂ ko₂)
    (hS : ∀ k₁ k₂, ko₁ = some k₁ → ko₂ = some k₂ → lo₁ + k₁ ≤ lo₂) :
    Disjoint (eighRegion N D (d + 1) lo₁ ko₁ (pre ++ [true]))
      (eighRegion N D (d + 1) lo₂ ko₂ (pre ++ [false])) :=
  disjoint_tapeLift (disjoint_eighRegionU hI hF₁ hF₂ hS) (disjoint_eighRegionZ hI hF₁ hF₂ hS)

end Regions

section Kids

variable {F : Type*} (M : FloatMachine F ℝ ℂ) (N signFuel : ℕ) (R₀ β : F)

/-- The children of a node fit in its range, are inside the root range, and the positive child
lies left of the negative one. -/
private lemma eighKids_spec {lo : ℕ} {xo : Option (EighNode F)}
    (hI : EighInv N lo (xo.map EighNode.k)) (s : EighSample ℝ ℂ N) :
    (∀ b, EighFits lo (xo.map EighNode.k)
        (eighKidSlot lo (eighKids M N signFuel R₀ β xo s) b)
        ((eighKid (eighKids M N signFuel R₀ β xo s) b).map EighNode.k) ∧
      EighInv N (eighKidSlot lo (eighKids M N signFuel R₀ β xo s) b)
        ((eighKid (eighKids M N signFuel R₀ β xo s) b).map EighNode.k)) ∧
    ∀ k₁ k₂, (eighKid (eighKids M N signFuel R₀ β xo s) true).map EighNode.k = some k₁ →
      (eighKid (eighKids M N signFuel R₀ β xo s) false).map EighNode.k = some k₂ →
      eighKidSlot lo (eighKids M N signFuel R₀ β xo s) true + k₁ ≤
        eighKidSlot lo (eighKids M N signFuel R₀ β xo s) false := by
  cases xo with
  | none =>
    simp [eighKids, eighKid, eighKidSlot, EighFits, EighInv]
  | some x =>
    have hx := hI x.k rfl
    rcases eighChild_cases M N signFuel R₀ β x s with
      ⟨h1, h2⟩ | ⟨y, h1, h2, hy, hk⟩ | ⟨y, h1, h2, hy, hk⟩ | ⟨y, y', h1, h2, hy, hy', hk⟩ <;>
    · refine ⟨fun b => ?_, ?_⟩
      · cases b <;> simp [eighKids, eighKid, eighKidSlot, h1, h2, EighFits, EighInv] <;> omega
      · simp [eighKids, eighKid, eighKidSlot, h1, h2]

private lemma eighNodeAt_singleton (x : EighNode F) (b : Bool) (s : EighSample ℝ ℂ N) :
    eighNodeAt M N signFuel R₀ β [b] x (fun _ => s) = eighChild M N signFuel R₀ β x s b := by
  simp [eighNodeAt]

private lemma countable_range_eighKids (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalc : (Set.range M.normal).Countable) (xo : Option (EighNode F)) :
    (Set.range (eighKids M N signFuel R₀ β xo)).Countable := by
  cases xo with
  | none =>
    refine (Set.countable_singleton (none, none)).mono ?_
    rintro _ ⟨s, rfl⟩
    rfl
  | some x =>
    have h : ∀ b, (Set.range fun s : EighSample ℝ ℂ N =>
        eighChild M N signFuel R₀ β x s b).Countable :=
      fun b => (countable_range_eighNodeAt hunifc hnormalc N signFuel R₀ β [b] x).mono (by
        rintro _ ⟨s, rfl⟩
        exact ⟨fun _ => s, eighNodeAt_singleton M N signFuel R₀ β x b s⟩)
    refine ((h true).prod (h false)).mono ?_
    rintro _ ⟨s, rfl⟩
    exact ⟨⟨s, rfl⟩, ⟨s, rfl⟩⟩

private lemma measurableSet_eighKids_preimage (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (xo : Option (EighNode F)) (c : Option (EighNode F) × Option (EighNode F)) :
    MeasurableSet (eighKids M N signFuel R₀ β xo ⁻¹' {c}) := by
  cases xo with
  | none => exact MeasurableSet.const ((none, none) = c)
  | some x =>
    have h : ∀ b y, MeasurableSet {s : EighSample ℝ ℂ N | eighChild M N signFuel R₀ β x s b = y} :=
      fun b y => by
        have := measurableSet_eighNodeAt_eq hunifm hunifc hnormalm hnormalc (N := N)
          (signFuel := signFuel) (R₀ := R₀) (β := β) (ζ := fun _ s => s)
          (fun _ => measurable_id) [b] x y
        simpa only [eighNodeAt_singleton] using this
    have : eighKids M N signFuel R₀ β (some x) ⁻¹' {c} =
        {s | eighChild M N signFuel R₀ β x s true = c.1} ∩
          {s | eighChild M N signFuel R₀ β x s false = c.2} := by
      ext s
      simp [eighKids, Prod.ext_iff]
    rw [this]
    exact (h true c.1).inter (h false c.2)

end Kids

/-! ### Lazy sampling -/

/-- A map that is chosen among countably many measurable maps by a function with measurable fibres
is measurable. -/
private lemma measurable_of_countable_cases {α β γ : Type*} {m : MeasurableSpace α}
    [MeasurableSpace γ] {κ : α → β} {g : β → α → γ} (hc : (Set.range κ).Countable)
    (hκ : ∀ c, MeasurableSet[m] (κ ⁻¹' {c})) (hg : ∀ c ∈ Set.range κ, Measurable[m] (g c)) :
    Measurable[m] fun x => g (κ x) x := by
  intro B hB
  have : (fun x => g (κ x) x) ⁻¹' B = ⋃ c ∈ Set.range κ, κ ⁻¹' {c} ∩ g c ⁻¹' B := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff,
      Set.mem_range, exists_prop]
    exact ⟨fun h => ⟨κ x, ⟨x, rfl⟩, rfl, h⟩, fun ⟨c, _, hc, h⟩ => hc ▸ h⟩
  rw [this]
  exact MeasurableSet.biUnion hc fun c hc' => (hκ c).inter (hg c hc' hB)

/-- A product over a finite set of paths: the empty path, then the paths through each side. -/
private lemma prod_eq_mul_prod_preimage_cons {β : Type*} [CommMonoid β] (S : Finset (List Bool))
    (g : List Bool → β) :
    ∏ a ∈ S, g a = (if [] ∈ S then g [] else 1) *
      ((∏ a ∈ S.preimage (List.cons true) List.cons_injective.injOn, g (true :: a)) *
        ∏ a ∈ S.preimage (List.cons false) List.cons_injective.injOn, g (false :: a)) := by
  have hside : ∀ b : Bool, ∏ a ∈ S.preimage (List.cons b) List.cons_injective.injOn, g (b :: a) =
      ∏ a ∈ S, if a.head? = some b then g a else 1 := by
    intro b
    rw [← Finset.prod_preimage (List.cons b) S List.cons_injective.injOn]
    · simp
    · intro x _ hx
      rw [if_neg]
      rintro h
      cases x with
      | nil => simp at h
      | cons c l =>
        simp only [List.head?_cons, Option.some.injEq] at h
        exact hx ⟨l, by rw [h]⟩
  have hnil : (if [] ∈ S then g [] else 1) = ∏ a ∈ S, if a = [] then g a else 1 := by
    rw [Finset.prod_ite_eq']
  rw [hside, hside, hnil, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rcases a with _ | ⟨_ | _, l⟩ <;> simp

/-- Splitting an event by the countably many values of a function with measurable fibres. -/
private lemma tsum_measure_preimage_inter_fibre {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace γ] (μ : Measure α) {f : α → γ} (hf : Measurable f) {κ : γ → β}
    (hc : (Set.range κ).Countable) (hκ : ∀ c, MeasurableSet (κ ⁻¹' {c})) {B : Set γ}
    (hB : MeasurableSet B) :
    ∑' c : Set.range κ, μ (f ⁻¹' (κ ⁻¹' {c.1} ∩ B)) = μ (f ⁻¹' B) := by
  rw [← measure_biUnion hc (fun c₁ _ c₂ _ hne => Set.disjoint_left.mpr fun x h₁ h₂ =>
      hne (h₁.1.symm.trans h₂.1)) fun c _ => hf ((hκ c).inter hB)]
  congr 1
  ext x
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff,
    Set.mem_range, exists_prop]
  exact ⟨fun ⟨_, _, _, h⟩ => h, fun h => ⟨_, ⟨_, rfl⟩, rfl, h⟩⟩

section Lazy

variable {F : Type*} (M : FloatMachine F ℝ ℂ) (N signFuel D : ℕ) (R₀ β : F)
  (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
  (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
  (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)

include hunifm hunifc hnormalm hnormalc in
/-- The subtree of a node is measurable for the coordinates it may read. -/
private lemma measurable_eighIdealTree (a : List Bool) :
    ∀ (d lo : ℕ) (xo : Option (EighNode F)) (pre : List Bool),
      EighInv N lo (xo.map EighNode.k) →
      Measurable[tapeSigma (eighRegion N D d lo (xo.map EighNode.k) pre)]
        fun ξ => eighIdealTree M N signFuel D R₀ β ξ d lo xo pre a := by
  induction a with
  | nil =>
    intro d lo xo pre _
    simp only [eighIdealTree, eighIdealSample_eq_eighReadSample]
    exact measurable_eighReadSample eighRootU_mem fun b i j => eighRootZ_mem b i j
  | cons b a ih =>
    intro d lo xo pre hI
    simp only [eighIdealTree_cons]
    have hs₀ : Measurable[tapeSigma (eighRegion N D d lo (xo.map EighNode.k) pre)]
        fun ξ => eighIdealSample ξ N D d lo (xo.map EighNode.k) pre := by
      exact measurable_eighIdealSample.mono (tapeSigma_mono eighRootPos_subset) le_rfl
    refine measurable_of_countable_cases
      (κ := fun ξ => eighKids M N signFuel R₀ β xo
        (eighIdealSample ξ N D d lo (xo.map EighNode.k) pre))
      (g := fun c ξ => eighIdealTree M N signFuel D R₀ β ξ (d + 1) (eighKidSlot lo c b)
        (eighKid c b) (pre ++ [b]) a) ?_ ?_ ?_
    · exact (countable_range_eighKids M N signFuel R₀ β hunifc hnormalc xo).mono
        (Set.range_comp_subset_range
          (fun ξ : Dist → ℕ → ℝ => eighIdealSample ξ N D d lo (xo.map EighNode.k) pre)
          (eighKids M N signFuel R₀ β xo))
    · exact fun c => hs₀ (measurableSet_eighKids_preimage M N signFuel R₀ β hunifm hunifc hnormalm
        hnormalc xo c)
    · rintro _ ⟨ξ, rfl⟩
      obtain ⟨hk, -⟩ := eighKids_spec M N signFuel R₀ β hI
        (eighIdealSample ξ N D d lo (xo.map EighNode.k) pre)
      exact (ih _ _ _ _ (hk b).2).mono (tapeSigma_mono (eighRegion_subset (hk b).1)) le_rfl

/-- The event that the sample of a node lies in `B` and gives the children `c`. -/
private def eighRootEvent (d lo : ℕ) (xo : Option (EighNode F)) (pre : List Bool)
    (B : Set (EighSample ℝ ℂ N)) (c : Option (EighNode F) × Option (EighNode F)) :
    Set (Dist → ℕ → ℝ) :=
  (fun ξ => eighIdealSample ξ N D d lo (xo.map EighNode.k) pre) ⁻¹'
    (eighKids M N signFuel R₀ β xo ⁻¹' {c} ∩ B)

/-- The event that the samples of the subtree of the child on side `b`, of the children `c`, lie
in the sets `A` at the paths through `b` of `S`. -/
private def eighKidEvent (d lo : ℕ) (pre : List Bool) (S : Finset (List Bool))
    (A : List Bool → Set (EighSample ℝ ℂ N)) (c : Option (EighNode F) × Option (EighNode F))
    (b : Bool) : Set (Dist → ℕ → ℝ) :=
  ⋂ a ∈ S.preimage (List.cons b) List.cons_injective.injOn,
    (fun ξ => eighIdealTree M N signFuel D R₀ β ξ (d + 1) (eighKidSlot lo c b) (eighKid c b)
      (pre ++ [b]) a) ⁻¹' A (b :: a)

/-- The event of the samples of a tree at the paths of `S`, split by the children of its node. -/
private lemma inter_iInter_eighIdealTree_eq (d lo : ℕ) (xo : Option (EighNode F))
    (pre : List Bool) (S : Finset (List Bool)) (A : List Bool → Set (EighSample ℝ ℂ N))
    (G : Set (Dist → ℕ → ℝ)) :
    G ∩ ⋂ a ∈ S, (fun ξ => eighIdealTree M N signFuel D R₀ β ξ d lo xo pre a) ⁻¹' A a =
      ⋃ c ∈ Set.range (eighKids M N signFuel R₀ β xo),
        ((G ∩ eighRootEvent M N signFuel D R₀ β d lo xo pre
            (if [] ∈ S then A [] else Set.univ) c) ∩
          eighKidEvent M N signFuel D R₀ β d lo pre S A c false) ∩
        eighKidEvent M N signFuel D R₀ β d lo pre S A c true := by
  ext ξ
  simp only [eighRootEvent, eighKidEvent, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
    Set.mem_iUnion, Set.mem_range, exists_prop, Set.mem_singleton_iff, Finset.mem_preimage]
  constructor
  · rintro ⟨hGξ, hall⟩
    refine ⟨_, ⟨_, rfl⟩, ⟨⟨hGξ, rfl, ?_⟩, fun a ha => ?_⟩, fun a ha => ?_⟩
    · split_ifs with h
      · exact hall [] h
      · trivial
    · have := hall _ ha
      rwa [eighIdealTree_cons] at this
    · have := hall _ ha
      rwa [eighIdealTree_cons] at this
  · rintro ⟨c, -, ⟨⟨hGξ, hc, hB⟩, hf⟩, ht⟩
    refine ⟨hGξ, fun a ha => ?_⟩
    rcases a with _ | ⟨b, a⟩
    · rw [if_pos ha] at hB
      exact hB
    · rw [eighIdealTree_cons, hc]
      cases b
      · exact hf a ha
      · exact ht a ha

include hunifm hunifc hnormalm hnormalc in
/-- One piece of the event: given the product formula for the two children (the induction
hypothesis), the probability that `G`, the sample of the node in `B₀` with children `c`, and the
events of the two subtrees all hold is the product. -/
private lemma measure_eighRootEvent_inter_eighKidEvent {d lo : ℕ} {xo : Option (EighNode F)}
    {pre : List Bool} (hI : EighInv N lo (xo.map EighNode.k)) (s : EighSample ℝ ℂ N)
    {S : Finset (List Bool)} {A : List Bool → Set (EighSample ℝ ℂ N)}
    (hA : ∀ a, MeasurableSet (A a)) {G : Set (Dist → ℕ → ℝ)}
    (hG : MeasurableSet[tapeSigma (eighRegion N D d lo (xo.map EighNode.k) pre)ᶜ] G)
    {B₀ : Set (EighSample ℝ ℂ N)} (hB₀ : MeasurableSet B₀)
    (hkid : ∀ b G', MeasurableSet[tapeSigma (eighRegion N D (d + 1)
          (eighKidSlot lo (eighKids M N signFuel R₀ β xo s) b)
          ((eighKid (eighKids M N signFuel R₀ β xo s) b).map EighNode.k) (pre ++ [b]))ᶜ] G' →
        tapeLaw (G' ∩ eighKidEvent M N signFuel D R₀ β d lo pre S A
          (eighKids M N signFuel R₀ β xo s) b) =
        tapeLaw G' * ∏ a ∈ S.preimage (List.cons b) List.cons_injective.injOn,
          eighSampleLaw N (A (b :: a))) :
    tapeLaw (((G ∩ eighRootEvent M N signFuel D R₀ β d lo xo pre B₀
        (eighKids M N signFuel R₀ β xo s)) ∩
        eighKidEvent M N signFuel D R₀ β d lo pre S A (eighKids M N signFuel R₀ β xo s) false) ∩
        eighKidEvent M N signFuel D R₀ β d lo pre S A (eighKids M N signFuel R₀ β xo s) true) =
      tapeLaw G * tapeLaw (eighRootEvent M N signFuel D R₀ β d lo xo pre B₀
          (eighKids M N signFuel R₀ β xo s)) *
        ((∏ a ∈ S.preimage (List.cons true) List.cons_injective.injOn,
            eighSampleLaw N (A (true :: a))) *
          ∏ a ∈ S.preimage (List.cons false) List.cons_injective.injOn,
            eighSampleLaw N (A (false :: a))) := by
  obtain ⟨hk, hslot⟩ := eighKids_spec M N signFuel R₀ β hI s
  have hKm : MeasurableSet[tapeSigma (eighRootPos N D d lo (xo.map EighNode.k) pre)]
      (eighRootEvent M N signFuel D R₀ β d lo xo pre B₀ (eighKids M N signFuel R₀ β xo s)) :=
    measurable_eighIdealSample ((measurableSet_eighKids_preimage M N signFuel R₀ β hunifm hunifc
      hnormalm hnormalc xo _).inter hB₀)
  have hEm : MeasurableSet[tapeSigma (eighRegion N D (d + 1)
      (eighKidSlot lo (eighKids M N signFuel R₀ β xo s) false)
      ((eighKid (eighKids M N signFuel R₀ β xo s) false).map EighNode.k) (pre ++ [false]))]
      (eighKidEvent M N signFuel D R₀ β d lo pre S A (eighKids M N signFuel R₀ β xo s) false) :=
    Finset.measurableSet_biInter _ fun a _ =>
      measurable_eighIdealTree M N signFuel D R₀ β hunifm hunifc hnormalm hnormalc a _ _ _ _
        (hk false).2 (hA _)
  have hdisj := disjoint_eighRegion (D := D) (d := d) (pre := pre) hI (hk true).1 (hk false).1
    hslot
  have hGt := tapeSigma_mono (Set.compl_subset_compl.mpr (eighRegion_subset (D := D) (d := d)
    (pre := pre) (b := true) (hk true).1)) _ hG
  have hGf := tapeSigma_mono (Set.compl_subset_compl.mpr (eighRegion_subset (D := D) (d := d)
    (pre := pre) (b := false) (hk false).1)) _ hG
  have hKt := tapeSigma_mono (disjoint_eighRootPos (D := D) (d := d) (pre := pre) (b := true)
    hI (hk true).1).subset_compl_right _ hKm
  have hKf := tapeSigma_mono (disjoint_eighRootPos (D := D) (d := d) (pre := pre) (b := false)
    hI (hk false).1).subset_compl_right _ hKm
  rw [hkid true _ ((hGt.inter hKt).inter (tapeSigma_mono hdisj.subset_compl_left _ hEm)),
    hkid false _ (hGf.inter hKf),
    (Indep_iff _ _ _).mp (indep_tapeSigma (Set.disjoint_compl_left_iff_subset.mpr
      eighRootPos_subset)) _ _ hG hKm]
  ring

include hunifm hunifc hnormalm hnormalc in
/-- Lazy sampling, the induction: for a node inside the root range, an event `G` of the
coordinates outside the region of its subtree, and finitely many paths of length below `L`, the
probability that `G` holds and the subtree's samples at the paths lie in measurable sets is the
probability of `G` times the product of their `NLAlib.eighSampleLaw` masses. -/
private lemma measure_inter_iInter_eighIdealTree (L : ℕ) :
    ∀ (d lo : ℕ) (xo : Option (EighNode F)) (pre : List Bool),
      EighInv N lo (xo.map EighNode.k) →
      ∀ (S : Finset (List Bool)), (∀ a ∈ S, a.length < L) →
      ∀ (A : List Bool → Set (EighSample ℝ ℂ N)), (∀ a, MeasurableSet (A a)) →
      ∀ G, MeasurableSet[tapeSigma (eighRegion N D d lo (xo.map EighNode.k) pre)ᶜ] G →
        tapeLaw (G ∩ ⋂ a ∈ S,
            (fun ξ => eighIdealTree M N signFuel D R₀ β ξ d lo xo pre a) ⁻¹' A a) =
          tapeLaw G * ∏ a ∈ S, eighSampleLaw N (A a) := by
  induction L with
  | zero =>
    intro d lo xo pre _ S hS A _ G _
    have : S = ∅ := Finset.eq_empty_of_forall_notMem fun a ha => by have := hS a ha; omega
    subst this
    simp
  | succ L ih =>
    intro d lo xo pre hI S hS A hA G hG
    -- the sample of the node, its law, and the children it gives
    have hs₀m := measurable_eighIdealSample (N := N) (D := D) (d := d) (lo := lo)
      (ko := xo.map EighNode.k) (pre := pre)
    have hs₀law : HasLaw (fun ξ => eighIdealSample ξ N D d lo (xo.map EighNode.k) pre)
        (eighSampleLaw N) tapeLaw := by
      simp only [eighIdealSample_eq_eighReadSample]
      exact hasLaw_eighReadSample N _ _ (injective_eighRootZ hI)
    have hC := countable_range_eighKids M N signFuel R₀ β hunifc hnormalc xo
    have hκm := measurableSet_eighKids_preimage M N signFuel R₀ β hunifm hunifc hnormalm hnormalc
      xo
    set B₀ : Set (EighSample ℝ ℂ N) := if [] ∈ S then A [] else Set.univ with hB₀def
    have hB₀ : MeasurableSet B₀ := by
      rw [hB₀def]; split_ifs; exacts [hA [], MeasurableSet.univ]
    have hKm : ∀ c, MeasurableSet[tapeSigma (eighRootPos N D d lo (xo.map EighNode.k) pre)]
        (eighRootEvent M N signFuel D R₀ β d lo xo pre B₀ c) :=
      fun c => hs₀m ((hκm c).inter hB₀)
    -- each piece: independence of the node's sample from `G`, then the two children
    have hpiece : ∀ c ∈ Set.range (eighKids M N signFuel R₀ β xo),
        tapeLaw (((G ∩ eighRootEvent M N signFuel D R₀ β d lo xo pre B₀ c) ∩
            eighKidEvent M N signFuel D R₀ β d lo pre S A c false) ∩
            eighKidEvent M N signFuel D R₀ β d lo pre S A c true) =
          tapeLaw G * tapeLaw (eighRootEvent M N signFuel D R₀ β d lo xo pre B₀ c) *
            ((∏ a ∈ S.preimage (List.cons true) List.cons_injective.injOn,
                eighSampleLaw N (A (true :: a))) *
              ∏ a ∈ S.preimage (List.cons false) List.cons_injective.injOn,
                eighSampleLaw N (A (false :: a))) := by
      rintro _ ⟨s, rfl⟩
      refine measure_eighRootEvent_inter_eighKidEvent M N signFuel D R₀ β hunifm hunifc hnormalm
        hnormalc hI s hA hG hB₀ fun b G' hG' => ih _ _ _ _ ((eighKids_spec M N signFuel R₀ β hI
          s).1 b).2 _ (fun a ha => ?_) (fun a => A (b :: a)) (fun a => hA _) G' hG'
      have := hS _ (Finset.mem_preimage.mp ha)
      simp only [List.length_cons] at this
      omega
    -- the sum over the children
    have hs₀m' := hs₀m.mono (tapeSigma_le _) le_rfl
    have hKsum : ∑' c : Set.range (eighKids M N signFuel R₀ β xo),
        tapeLaw (eighRootEvent M N signFuel D R₀ β d lo xo pre B₀ c) =
          if [] ∈ S then eighSampleLaw N (A []) else 1 := by
      rw [show (fun c : Set.range (eighKids M N signFuel R₀ β xo) =>
          tapeLaw (eighRootEvent M N signFuel D R₀ β d lo xo pre B₀ c)) =
          fun c => tapeLaw ((fun ξ => eighIdealSample ξ N D d lo (xo.map EighNode.k) pre) ⁻¹'
            (eighKids M N signFuel R₀ β xo ⁻¹' {c.1} ∩ B₀)) from rfl,
        tsum_measure_preimage_inter_fibre tapeLaw hs₀m' hC hκm hB₀,
        ← Measure.map_apply hs₀m' hB₀, hs₀law.map_eq, hB₀def]
      split_ifs
      · rfl
      · rw [← hs₀law.map_eq, Measure.map_apply hs₀m' MeasurableSet.univ, Set.preimage_univ,
          measure_univ]
    rw [inter_iInter_eighIdealTree_eq, measure_biUnion hC ?_ ?_,
      tsum_congr fun (c : Set.range (eighKids M N signFuel R₀ β xo)) => hpiece c.1 c.2,
      ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hKsum,
      prod_eq_mul_prod_preimage_cons S, mul_assoc]
    · intro c₁ _ c₂ _ hne
      refine Set.disjoint_left.mpr fun ξ h₁ h₂ => hne ?_
      exact h₁.1.1.2.1.symm.trans h₂.1.1.2.1
    · rintro _ ⟨s, rfl⟩
      obtain ⟨hk, -⟩ := eighKids_spec M N signFuel R₀ β hI s
      refine (((tapeSigma_le _ _ hG).inter (tapeSigma_le _ _ (hKm _))).inter ?_).inter ?_ <;>
      exact Finset.measurableSet_biInter _ fun a _ => (measurable_eighIdealTree M N signFuel D R₀ β
        hunifm hunifc hnormalm hnormalc a _ _ _ _ (hk _).2).mono (tapeSigma_le _) le_rfl (hA _)

end Lazy

/-- Lazy sampling: on an ideal tape $\xi$ of law `NLAlib.Computation.tapeLaw`, for a machine
over ideal samples whose samplers have measurable fibres and countable ranges, the tree of ideal
samples of `NLAlib.eighIdealTree` from a node of size at most $N$ at slot $0$ of depth $0$ is
independent, with law `NLAlib.eighSampleLaw` $N$ at every path. The positions a node reads are a
function of the samples of the nodes above it, and they are disjoint from the positions of every
other node (static positions of distinct slots of one depth, of distinct depths, and positions
beyond the program's draws indexed by the path). Nothing in Mathlib is a precedent. No printed
source. -/
theorem iIndepFun_eighIdealTree {F : Type*} (M : FloatMachine F ℝ ℂ)
    (hunifm : ∀ c z, MeasurableSet (M.unif c ⁻¹' {z}))
    (hunifc : ∀ c, (Set.range (M.unif c)).Countable)
    (hnormalm : ∀ z, MeasurableSet (M.normal ⁻¹' {z})) (hnormalc : (Set.range M.normal).Countable)
    (N signFuel D : ℕ) (R₀ β : F) (x : EighNode F) (hx : x.k ≤ N) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ξ : Ω → Dist → ℕ → ℝ} (hξ : HasLaw ξ tapeLaw μ) :
    iIndepFun (fun a ω => eighIdealTree M N signFuel D R₀ β (ξ ω) 0 0 (some x) [] a) μ ∧
      ∀ a, HasLaw (fun ω => eighIdealTree M N signFuel D R₀ β (ξ ω) 0 0 (some x) [] a)
        (eighSampleLaw N) μ := by
  have hI : EighInv N 0 ((some x).map EighNode.k) := fun k hk => by
    simp only [Option.map_some, Option.some.injEq] at hk
    omega
  have hTm : ∀ a, Measurable fun θ => eighIdealTree M N signFuel D R₀ β θ 0 0 (some x) [] a :=
    fun a => (measurable_eighIdealTree M N signFuel D R₀ β hunifm hunifc hnormalm hnormalc a 0 0
      (some x) [] hI).mono (tapeSigma_le _) le_rfl
  -- the product formula on the canonical space
  have key : ∀ (S : Finset (List Bool)) (A : List Bool → Set (EighSample ℝ ℂ N)),
      (∀ a, MeasurableSet (A a)) →
      tapeLaw (⋂ a ∈ S, (fun θ => eighIdealTree M N signFuel D R₀ β θ 0 0 (some x) [] a) ⁻¹' A a) =
        ∏ a ∈ S, eighSampleLaw N (A a) := by
    intro S A hA
    have := measure_inter_iInter_eighIdealTree M N signFuel D R₀ β hunifm hunifc hnormalm hnormalc
      (S.sup List.length + 1) 0 0 (some x) [] hI S
      (fun a ha => Nat.lt_succ_of_le (Finset.le_sup (f := List.length) ha)) A hA Set.univ
      MeasurableSet.univ
    simpa only [Set.univ_inter, measure_univ, one_mul] using this
  have hlaw : ∀ a, HasLaw (fun ω => eighIdealTree M N signFuel D R₀ β (ξ ω) 0 0 (some x) [] a)
      (eighSampleLaw N) μ := by
    intro a
    refine (HasLaw.mk (hTm a).aemeasurable ?_).comp hξ
    ext B hB
    rw [Measure.map_apply (hTm a) hB]
    simpa using key {a} (fun _ => B) fun _ => hB
  refine ⟨?_, hlaw⟩
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  classical
  set A : List Bool → Set (EighSample ℝ ℂ N) := fun a => if a ∈ S then sets a else Set.univ
    with hAdef
  have hA : ∀ a, MeasurableSet (A a) := fun a => by
    rw [hAdef]; dsimp only; split_ifs with h; exacts [hsets a h, MeasurableSet.univ]
  have hAS : ∀ a ∈ S, A a = sets a := fun a ha => by rw [hAdef]; dsimp only; rw [if_pos ha]
  have hpre : ∀ B, MeasurableSet B → μ (ξ ⁻¹' B) = tapeLaw B := fun B hB => by
    rw [← hξ.map_eq, Measure.map_apply_of_aemeasurable hξ.aemeasurable hB]
  calc μ (⋂ a ∈ S, (fun ω => eighIdealTree M N signFuel D R₀ β (ξ ω) 0 0 (some x) [] a) ⁻¹'
          sets a)
      = μ (ξ ⁻¹' ⋂ a ∈ S,
          (fun θ => eighIdealTree M N signFuel D R₀ β θ 0 0 (some x) [] a) ⁻¹' A a) := by
        congr 1
        ext ω
        simp only [Set.mem_iInter, Set.mem_preimage]
        exact forall₂_congr fun a ha => by rw [hAS a ha]
    _ = ∏ a ∈ S, eighSampleLaw N (A a) := by
        rw [hpre _ (Finset.measurableSet_biInter _ fun a _ => hTm a (hA a)), key S A hA]
    _ = _ := by
        refine Finset.prod_congr rfl fun a ha => ?_
        rw [hAS a ha, ← (hlaw a).map_eq,
          Measure.map_apply_of_aemeasurable (hlaw a).aemeasurable (hsets a ha)]

end NLAlib
