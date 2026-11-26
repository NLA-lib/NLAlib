/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Rounding
public import NLAlib.Matrix.Perturbation.LUErr

/-!
# Rounded LU factor prefixes

The active residual and committed factor columns and rows reconstruct the permuted input
through products of actual scalar rounding factors. Only committed diagonal entries are one;
retired residual entries need not vanish. A completed prefix yields componentwise LU backward
error with the factor count of the stored saved-pivot implementation.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main definitions

* `NLAlib.IsLURoundingPrefix`: a concrete active residual and factor-prefix identity.

## Main results

* `NLAlib.IsLURoundingPrefix.initial`: the empty prefix.
* `NLAlib.IsLURoundingPrefix.submatrix_left`: transport under active-row permutation.
* `NLAlib.IsLURoundingPrefix.step_of_ne_zero`: a rounded nonzero-pivot step.
* `NLAlib.IsLURoundingPrefix.step_of_eq_zero`: a skipped zero-column step.
* `NLAlib.IsLURoundingPrefix.isLUErr`: the completed factorization backward-error bound.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation

variable {N k : ℕ} {u : ℝ}
    {B S L U : Matrix (Fin N) (Fin N) ℝ}

/-- A rounded LU prefix: committed columns of the lower factor have zeros above the diagonal
and unit diagonal, and committed upper rows have zeros to the left. The input is the sum of
an active residual with a length-$k$ rounding product and the first $k$ factor products, whose
coefficient for column $t$ has length $t+5$. Only active residual coefficients are constrained.
This records the stored saved-pivot arithmetic, including its rounded minus-one literal and
separate lower-column divisions. [Higham2002, §9.3]. -/
structure IsLURoundingPrefix (u : ℝ) (k : ℕ)
    (B S L U : Matrix (Fin N) (Fin N) ℝ) : Prop where
  /-- A prefix does not exceed the matrix dimension. -/
  le_dim : k ≤ N
  /-- Committed lower columns vanish above the diagonal. -/
  lower : ∀ i t, t.val < k → i < t → L i t = 0
  /-- Committed lower diagonal entries are one. -/
  diag : ∀ t, t.val < k → L t t = 1
  /-- Committed upper rows vanish to the left of the diagonal. -/
  upper : ∀ t j, t.val < k → j < t → U t j = 0
  /-- Products of scalar rounding factors reconstruct every input entry. -/
  factors : ∃ (θ : Matrix (Fin N) (Fin N) ℝ)
      (η : Fin N → Matrix (Fin N) (Fin N) ℝ),
    (∀ i j, k ≤ i.val → k ≤ j.val → IsRoundingProduct u k (θ i j)) ∧
    (∀ t, t.val < k → ∀ i j, IsRoundingProduct u (t.val + 5) (η t i j)) ∧
    ∀ i j, B i j = (if k ≤ i.val ∧ k ≤ j.val then S i j * (1 + θ i j) else 0) +
      ∑ t ∈ Finset.univ.filter (fun t : Fin N => t.val < k), L i t * U t j * (1 + η t i j)

/-- At the empty prefix, the residual is the input and no factor entry is yet committed.
The initialized factor matrices may be arbitrary. -/
theorem IsLURoundingPrefix.initial (u : ℝ) (B L U : Matrix (Fin N) (Fin N) ℝ) :
    IsLURoundingPrefix u 0 B B L U := by
  refine ⟨Nat.zero_le _, fun _ _ h _ => (Nat.not_lt_zero _ h).elim,
    fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ h _ => (Nat.not_lt_zero _ h).elim,
    0, fun _ => 0, fun _ _ _ _ => isRoundingProduct_zero,
    fun _ h => (Nat.not_lt_zero _ h).elim, ?_⟩
  intro i j
  simp

/-- A row permutation fixing every row before the active suffix transports the input,
residual and lower prefix together, leaving the upper rows unchanged. Rounding coefficients
follow the same rows. No assumption on retired residual entries is needed. -/
theorem IsLURoundingPrefix.submatrix_left (h : IsLURoundingPrefix u k B S L U)
    (τ : Equiv.Perm (Fin N)) (hfix : ∀ i, i.val < k → τ i = i) :
    IsLURoundingPrefix u k (B.submatrix τ id) (S.submatrix τ id) (L.submatrix τ id) U := by
  have hactive (i : Fin N) : k ≤ (τ i).val ↔ k ≤ i.val := by
    constructor
    · intro ht
      by_contra hi
      have hlt : i.val < k := by omega
      rw [hfix i hlt] at ht
      omega
    · intro hi
      by_contra ht
      have hlt : (τ i).val < k := by omega
      have he : τ i = i := τ.injective (hfix (τ i) hlt)
      rw [he] at hlt
      omega
  obtain ⟨θ, η, hθ, hη, heq⟩ := h.factors
  refine ⟨h.le_dim, ?_, ?_, h.upper, fun i j => θ (τ i) j,
    fun t i j => η t (τ i) j, ?_, ?_, ?_⟩
  · intro i t ht hit
    have hi : i.val < k := lt_trans hit ht
    simpa only [Matrix.submatrix_apply, id_eq, hfix i hi] using h.lower i t ht hit
  · intro t ht
    simpa only [Matrix.submatrix_apply, id_eq, hfix t ht] using h.diag t ht
  · intro i j hi hj
    exact hθ (τ i) j ((hactive i).mpr hi) hj
  · intro t ht i j
    exact hη t ht (τ i) j
  · intro i j
    simpa only [Matrix.submatrix_apply, id_eq, hactive] using heq (τ i) j

/-- A completed rounded prefix has unit lower and upper triangular factors and componentwise
backward error bounded by the accumulated factor for $N+4$ operations. No $Nu<1$ hypothesis
is needed for the existing geometric `roundingFactor`; $0\le u<1$ suffices.
[Higham2002, §9.3; CarsonMaShao2026, Lemma 2]. -/
theorem IsLURoundingPrefix.isLUErr (h : IsLURoundingPrefix u N B S L U)
    (hu : 0 ≤ u) (hu1 : u < 1) : IsLUErr (roundingFactor (N + 4) u) B L U := by
  refine ⟨⟨fun i j hij => h.lower i j j.isLt hij, fun i => h.diag i i.isLt⟩,
    fun i j hji => h.upper i j i.isLt hji, ?_⟩
  obtain ⟨θ, η, -, hη, heq⟩ := h.factors
  intro i j
  have hfilter : Finset.univ.filter (fun t : Fin N => t.val < N) = Finset.univ := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_of_true t.isLt trivial
  have hB : B i j = ∑ t, L i t * U t j * (1 + η t i j) := by
    simpa only [not_le.mpr i.isLt, false_and, ↓reduceIte, zero_add, hfilter] using heq i j
  have hd : (B - L * U) i j = ∑ t, L i t * U t j * η t i j := by
    simp only [Matrix.sub_apply, Matrix.mul_apply]
    rw [hB, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hbound (t : Fin N) : |η t i j| ≤ roundingFactor (N + 4) u :=
    ((hη t t.isLt i j).mono hu (by omega)).abs_le hu1
  rw [hd, Real.norm_eq_abs]
  calc
    |∑ t, L i t * U t j * η t i j| ≤ ∑ t, |L i t * U t j * η t i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, roundingFactor (N + 4) u * (|L i t| * |U t j|) := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [abs_mul, mul_comm (roundingFactor (N + 4) u)] using
        mul_le_mul_of_nonneg_left (hbound t) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = roundingFactor (N + 4) u * ∑ t, ‖L i t‖ * ‖U t j‖ := by
      rw [Finset.mul_sum]
      simp only [Real.norm_eq_abs]

private theorem split_schur_product {a x y pivot ell c t q z l θ : ℝ}
    (hu1 : u < 1) (hp : pivot ≠ 0) (hθ : IsRoundingProduct u k θ)
    (hl : RelErr u (x / pivot) l) (hell : RelErr u (-1) ell)
    (hc : RelErr u (ell / pivot) c) (ht : RelErr u (c * y) t)
    (hq : RelErr u (x * t) q) (hz : RelErr u (a + q) z) :
    ∃ θ' η, IsRoundingProduct u (k + 1) θ' ∧ IsRoundingProduct u (k + 5) η ∧
      a * (1 + θ) = z * (1 + θ') + l * y * (1 + η) := by
  obtain ⟨δL, hδL, heL⟩ := hl
  obtain ⟨δ₀, hδ₀, he₀⟩ := hell
  obtain ⟨δ₁, hδ₁, he₁⟩ := hc
  obtain ⟨δ₂, hδ₂, he₂⟩ := ht
  obtain ⟨δ₃, hδ₃, he₃⟩ := hq
  obtain ⟨δ₄, hδ₄, he₄⟩ := hz
  let Q := (1 + δ₀) * (1 + δ₁) * (1 + δ₂) * (1 + δ₃)
  have hQ : IsRoundingProduct u 4 (Q - 1) := by
    convert (((isRoundingProduct_one_of_abs_le hδ₀).mul
      (isRoundingProduct_one_of_abs_le hδ₁)).mul
      (isRoundingProduct_one_of_abs_le hδ₂)).mul
      (isRoundingProduct_one_of_abs_le hδ₃) using 1
    dsimp [Q]
    ring
  let θ' := (1 + θ) / (1 + δ₄) - 1
  let η := (1 + θ) * Q / (1 + δL) - 1
  refine ⟨θ', η, hθ.div (isRoundingProduct_one_of_abs_le hδ₄), ?_, ?_⟩
  · convert (hθ.mul hQ).div (isRoundingProduct_one_of_abs_le hδL) using 1
    dsimp [η]
    ring
  · rw [he₄, he₃, he₂, he₁, he₀, heL]
    dsimp [θ', η, Q]
    have h₄ : 1 + δ₄ ≠ 0 :=
      (neg_lt_iff_pos_add'.mp (abs_lt.mp (hδ₄.trans_lt hu1)).1).ne'
    have hL : 1 + δL ≠ 0 :=
      (neg_lt_iff_pos_add'.mp (abs_lt.mp (hδL.trans_lt hu1)).1).ne'
    field_simp [hp, h₄, hL]
    ring

private theorem step_of_split (h : IsLURoundingPrefix u k B S L U)
    (hk : k < N) (v : Fin N → ℝ) (S' : Matrix (Fin N) (Fin N) ℝ)
    (hvzero : ∀ i, i < ⟨k, hk⟩ → v i = 0) (hvdiag : v ⟨k, hk⟩ = 1)
    (hsplit : ∀ θ : Matrix (Fin N) (Fin N) ℝ,
      (∀ i j, k ≤ i.val → k ≤ j.val → IsRoundingProduct u k (θ i j)) →
      ∀ i j, ∃ θ' η, IsRoundingProduct u (k + 1) θ' ∧
        IsRoundingProduct u (k + 5) η ∧
        (if k ≤ i.val ∧ k ≤ j.val then S i j * (1 + θ i j) else 0) =
        (if k + 1 ≤ i.val ∧ k + 1 ≤ j.val then S' i j * (1 + θ') else 0) +
          v i * (if j < ⟨k, hk⟩ then 0 else S ⟨k, hk⟩ j) * (1 + η)) :
    IsLURoundingPrefix u (k + 1) B S' (L.updateCol ⟨k, hk⟩ v)
      (U.updateRow ⟨k, hk⟩ (fun j => if j < ⟨k, hk⟩ then 0 else S ⟨k, hk⟩ j)) := by
  classical
  let r : Fin N := ⟨k, hk⟩
  let row : Fin N → ℝ := fun j => if j < r then 0 else S r j
  obtain ⟨θ, η, hθ, hη, heq⟩ := h.factors
  choose θ' η' hθ' hη' hentry using hsplit θ hθ
  let ηnew : Fin N → Matrix (Fin N) (Fin N) ℝ :=
    fun t i j => if t = r then η' i j else η t i j
  refine ⟨by omega, ?_, ?_, ?_, θ', ηnew, fun i j _ _ => hθ' i j, ?_, ?_⟩
  · intro i t ht hit
    by_cases htr : t = r
    · subst t
      rw [Matrix.updateCol_self]
      exact hvzero i hit
    · rw [Matrix.updateCol_ne htr]
      exact h.lower i t (by have hne : t.val ≠ k := fun he => htr (Fin.ext he); omega) hit
  · intro t ht
    by_cases htr : t = r
    · subst t
      rw [Matrix.updateCol_self]
      exact hvdiag
    · rw [Matrix.updateCol_ne htr]
      exact h.diag t (by have hne : t.val ≠ k := fun he => htr (Fin.ext he); omega)
  · intro t j ht hjt
    by_cases htr : t = r
    · subst t
      change U.updateRow r row r j = 0
      rw [Matrix.updateRow_self]
      exact if_pos hjt
    · rw [Matrix.updateRow_ne htr]
      exact h.upper t j (by have hne : t.val ≠ k := fun he => htr (Fin.ext he); omega) hjt
  · intro t ht i j
    by_cases htr : t = r
    · subst t
      simpa only [ηnew, ↓reduceIte] using hη' i j
    · have htk : t.val < k := by have hne : t.val ≠ k := fun he => htr (Fin.ext he); omega
      simpa only [ηnew, if_neg htr] using hη t htk i j
  · intro i j
    have hnot : r ∉ Finset.univ.filter (fun t : Fin N => t.val < k) := by simp [r]
    have hfilter : Finset.univ.filter (fun t : Fin N => t.val < k + 1) =
        insert r (Finset.univ.filter (fun t : Fin N => t.val < k)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro ht
        by_cases htk : t.val < k
        · exact Or.inr htk
        · exact Or.inl (Fin.ext (by dsimp [r]; omega))
      · rintro (rfl | ht) <;> dsimp [r] at * <;> omega
    rw [hfilter, Finset.sum_insert hnot]
    have hold : ∑ t ∈ Finset.univ.filter (fun t : Fin N => t.val < k),
        L.updateCol r v i t * U.updateRow r row t j * (1 + ηnew t i j) =
        ∑ t ∈ Finset.univ.filter (fun t : Fin N => t.val < k),
          L i t * U t j * (1 + η t i j) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htr : t ≠ r := by
        intro he
        subst t
        simp [r] at ht
      simp only [Matrix.updateCol_ne htr, Matrix.updateRow_ne htr,
        ηnew, if_neg htr]
    change B i j = _ + (_ + ∑ t ∈ Finset.univ.filter (fun t : Fin N => t.val < k),
      L.updateCol r v i t * U.updateRow r row t j * (1 + ηnew t i j))
    rw [hold, Matrix.updateCol_self, Matrix.updateRow_self]
    simp only [ηnew, ↓reduceIte]
    have hentry' :
        (if k ≤ i.val ∧ k ≤ j.val then S i j * (1 + θ i j) else 0) =
        (if k + 1 ≤ i.val ∧ k + 1 ≤ j.val then S' i j * (1 + θ' i j) else 0) +
          v i * row j * (1 + η' i j) := hentry i j
    rw [heq i j, hentry']
    ring

/-- A nonzero pivot advances a rounded LU prefix using the actual lower-column quotient
errors and saved-pivot Schur primitive errors: rounded minus one, coefficient division, two
multiplications and final addition. The residual gains one factor and the new LU product
has at most $k+5$ factors. Retired residual entries are unrestricted.
[Higham2002, §9.3]. -/
theorem IsLURoundingPrefix.step_of_ne_zero (h : IsLURoundingPrefix u k B S L U)
    (hu : 0 ≤ u) (hu1 : u < 1) (hk : k < N) (v : Fin N → ℝ)
    (S' : Matrix (Fin N) (Fin N) ℝ) (ell c : ℝ) (t : Fin N → ℝ)
    (q : Matrix (Fin N) (Fin N) ℝ)
    (hvzero : ∀ i, i < ⟨k, hk⟩ → v i = 0) (hvdiag : v ⟨k, hk⟩ = 1)
    (hvrel : ∀ i, ⟨k, hk⟩ < i → RelErr u (S i ⟨k, hk⟩ / S ⟨k, hk⟩ ⟨k, hk⟩) (v i))
    (hp : S ⟨k, hk⟩ ⟨k, hk⟩ ≠ 0) (hell : RelErr u (-1) ell)
    (hc : RelErr u (ell / S ⟨k, hk⟩ ⟨k, hk⟩) c)
    (ht : ∀ j, RelErr u (c * S ⟨k, hk⟩ j) (t j))
    (hq : ∀ i j, RelErr u (S i ⟨k, hk⟩ * t j) (q i j))
    (hz : ∀ i j, RelErr u (S i j + q i j) (S' i j)) :
    IsLURoundingPrefix u (k + 1) B S' (L.updateCol ⟨k, hk⟩ v)
      (U.updateRow ⟨k, hk⟩ (fun j => if j < ⟨k, hk⟩ then 0 else S ⟨k, hk⟩ j)) := by
  apply step_of_split h hk v S' hvzero hvdiag
  intro θ hθ i j
  let r : Fin N := ⟨k, hk⟩
  have h0 : IsRoundingProduct u (k + 1) 0 := isRoundingProduct_zero.mono hu (by omega)
  have hη0 : IsRoundingProduct u (k + 5) 0 := isRoundingProduct_zero.mono hu (by omega)
  by_cases hi : i < r
  · refine ⟨0, 0, h0, hη0, ?_⟩
    rw [if_neg (by change i.val < k at hi; omega),
      if_neg (by change i.val < k at hi; omega),
      hvzero i hi]
    ring
  by_cases hj : j < r
  · refine ⟨0, 0, h0, hη0, ?_⟩
    rw [if_neg (by change j.val < k at hj; omega),
      if_neg (by change j.val < k at hj; omega),
      if_pos hj]
    ring
  have hik : k ≤ i.val := le_of_not_gt hi
  have hjk : k ≤ j.val := le_of_not_gt hj
  by_cases hir : i = r
  · subst i
    refine ⟨0, θ r j, h0, (hθ r j (le_refl _) hjk).mono hu (by omega), ?_⟩
    rw [if_pos ⟨le_refl _, hjk⟩, if_neg (by dsimp [r]; omega), hvdiag, if_neg hj]
    ring
  have hri : r < i := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hir)
  by_cases hjr : j = r
  · subst j
    obtain ⟨δ, hδ, hv⟩ := hvrel i hri
    let η := (1 + θ i r) / (1 + δ) - 1
    refine ⟨0, η, h0,
      ((hθ i r hik (le_refl _)).div (isRoundingProduct_one_of_abs_le hδ)).mono hu
        (by omega), ?_⟩
    rw [if_pos ⟨hik, le_refl _⟩, if_neg (by dsimp [r]; omega), if_neg (lt_irrefl r), hv]
    dsimp [η]
    have hδ0 : 1 + δ ≠ 0 :=
      (neg_lt_iff_pos_add'.mp (abs_lt.mp (hδ.trans_lt hu1)).1).ne'
    field_simp [hp, hδ0]
    ring
  have hi1 : k + 1 ≤ i.val := by change k < i.val at hri; omega
  have hj1 : k + 1 ≤ j.val := by
    have hval : j.val ≠ k := fun he => hjr (Fin.ext he)
    omega
  obtain ⟨θ', η, hθ', hη, heq⟩ := split_schur_product hu1 hp (hθ i j hik hjk)
    (hvrel i hri) hell hc (ht j) (hq i j) (hz i j)
  refine ⟨θ', η, hθ', hη, ?_⟩
  rw [if_pos ⟨hik, hjk⟩, if_pos ⟨hi1, hj1⟩, if_neg hj]
  exact heq

/-- A zero active pivot with an entirely zero active column advances the factor prefix while
leaving the residual unchanged. Total quotient errors give exactly zero lower multipliers;
no inversion, nonzero-pivot premise or upper bound on roundoff is required.
[Higham2002, §9.3]. -/
theorem IsLURoundingPrefix.step_of_eq_zero (h : IsLURoundingPrefix u k B S L U)
    (hu : 0 ≤ u) (hk : k < N) (v : Fin N → ℝ)
    (hvzero : ∀ i, i < ⟨k, hk⟩ → v i = 0) (hvdiag : v ⟨k, hk⟩ = 1)
    (hvrel : ∀ i, ⟨k, hk⟩ < i → RelErr u (S i ⟨k, hk⟩ / S ⟨k, hk⟩ ⟨k, hk⟩) (v i))
    (hp : S ⟨k, hk⟩ ⟨k, hk⟩ = 0)
    (hcol : ∀ i, ⟨k, hk⟩ ≤ i → S i ⟨k, hk⟩ = 0) :
    IsLURoundingPrefix u (k + 1) B S (L.updateCol ⟨k, hk⟩ v)
      (U.updateRow ⟨k, hk⟩ (fun j => if j < ⟨k, hk⟩ then 0 else S ⟨k, hk⟩ j)) := by
  apply step_of_split h hk v S hvzero hvdiag
  intro θ hθ i j
  let r : Fin N := ⟨k, hk⟩
  have h0 : IsRoundingProduct u (k + 1) 0 := isRoundingProduct_zero.mono hu (by omega)
  have hη0 : IsRoundingProduct u (k + 5) 0 := isRoundingProduct_zero.mono hu (by omega)
  by_cases hi : i < r
  · refine ⟨0, 0, h0, hη0, ?_⟩
    rw [if_neg (by change i.val < k at hi; omega),
      if_neg (by change i.val < k at hi; omega),
      hvzero i hi]
    ring
  by_cases hj : j < r
  · refine ⟨0, 0, h0, hη0, ?_⟩
    rw [if_neg (by change j.val < k at hj; omega),
      if_neg (by change j.val < k at hj; omega),
      if_pos hj]
    ring
  have hik : k ≤ i.val := le_of_not_gt hi
  have hjk : k ≤ j.val := le_of_not_gt hj
  by_cases hir : i = r
  · subst i
    refine ⟨0, θ r j, h0, (hθ r j (le_refl _) hjk).mono hu (by omega), ?_⟩
    rw [if_pos ⟨le_refl _, hjk⟩, if_neg (by dsimp [r]; omega), hvdiag, if_neg hj]
    ring
  have hri : r < i := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hir)
  have hvi : v i = 0 := by
    obtain ⟨δ, -, he⟩ := hvrel i hri
    simpa only [hp, div_zero, zero_mul] using he
  by_cases hjr : j = r
  · subst j
    refine ⟨0, 0, h0, hη0, ?_⟩
    rw [if_pos ⟨hik, le_refl _⟩, if_neg (by dsimp [r]; omega), hcol i (le_of_lt hri), hvi]
    ring
  have hi1 : k + 1 ≤ i.val := by change k < i.val at hri; omega
  have hj1 : k + 1 ≤ j.val := by
    have hval : j.val ≠ k := fun he => hjr (Fin.ext he)
    omega
  refine ⟨θ i j, 0, (hθ i j hik hjk).mono hu (by omega), hη0, ?_⟩
  rw [if_pos ⟨hik, hjk⟩, if_pos ⟨hi1, hj1⟩, hvi]
  ring

end NLAlib
