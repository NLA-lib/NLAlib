/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Givens
public import NLAlib.Matrix.Factorizations.Householder

/-!
# Hessenberg and tridiagonal form

A matrix indexed by `Fin` is upper Hessenberg if it vanishes below the first subdiagonal, and
tridiagonal if it vanishes outside the three central diagonals. Every square matrix is unitarily
similar to an upper Hessenberg matrix, and every Hermitian matrix to a tridiagonal one, by a
unitary matrix that fixes the first coordinate vector. The QR iteration preserves both forms, and
an unreduced Hessenberg form is determined by the first column of the unitary factor up to
unimodular scaling (the implicit Q theorem).

The Hessenberg predicate is stated for rectangular matrices, since the Arnoldi process produces
`(k + 1) × k` Hessenberg matrices.

## Main definitions

* `NLAlib.IsUpperHessenberg`, `NLAlib.IsTridiagonal`.

## Main results

* `NLAlib.exists_isUpperHessenberg_conjTranspose_mul_mul`: reduction to Hessenberg form.
* `Matrix.IsHermitian.exists_isTridiagonal_conjTranspose_mul_mul`: reduction to tridiagonal form.
* `NLAlib.IsUpperHessenberg.exists_isQR`: a Hessenberg matrix has a QR factorization with
  Hessenberg `Q`, so `R Q` is again Hessenberg.
* `NLAlib.exists_eq_mul_diagonal_of_isUpperHessenberg`: the implicit Q theorem.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {R : Type*} {m n : ℕ}

/-! ### The predicates -/

/-- A matrix indexed by `Fin m` and `Fin n` is **upper Hessenberg** if its entries below the first
subdiagonal vanish. [GolubVanLoan2013, §7.4]. Port of `NLAlib.IsUpperHessenberg`, there for
square real matrices. -/
def IsUpperHessenberg [Zero R] (H : Matrix (Fin m) (Fin n) R) : Prop :=
  ∀ (i : Fin m) (j : Fin n), (j : ℕ) + 1 < (i : ℕ) → H i j = 0

/-- A square matrix indexed by `Fin n` is **tridiagonal** if its entries outside the main
diagonal and the two adjacent ones vanish. Port of `NLAlib.IsTridiagonal`. -/
def IsTridiagonal [Zero R] (T : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j : Fin n, (i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ) → T i j = 0

/-- An upper trapezoidal matrix is upper Hessenberg.
Port of `NLAlib.isUpperHessenberg_of_isUpperTriangular`. -/
theorem IsUpperTrapezoidal.isUpperHessenberg [Zero R] {A : Matrix (Fin m) (Fin n) R}
    (hA : IsUpperTrapezoidal A) : IsUpperHessenberg A := by
  exact fun i j hij => hA i j (by omega)

/-- An upper triangular matrix is upper Hessenberg. -/
theorem _root_.Matrix.IsUpperTriangular.isUpperHessenberg [Zero R]
    {A : Matrix (Fin n) (Fin n) R} (hA : A.IsUpperTriangular) : IsUpperHessenberg A := by
  exact fun i j hij => hA (show j < i from Fin.lt_def.mpr (by omega))

/-- A tridiagonal matrix is upper Hessenberg. -/
theorem IsTridiagonal.isUpperHessenberg [Zero R] {T : Matrix (Fin n) (Fin n) R}
    (hT : IsTridiagonal T) : IsUpperHessenberg T := by
  exact fun i j hij => hT i j (Or.inr hij)

/-- A matrix is tridiagonal exactly when it and its transpose are upper Hessenberg. -/
theorem isTridiagonal_iff [Zero R] {T : Matrix (Fin n) (Fin n) R} :
    IsTridiagonal T ↔ IsUpperHessenberg T ∧ IsUpperHessenberg Tᵀ := by
  refine ⟨fun h => ⟨h.isUpperHessenberg, fun i j hij => h j i (Or.inl hij)⟩, fun h i j hij => ?_⟩
  rcases hij with hij | hij
  · exact h.2 j i hij
  · exact h.1 i j hij

/-- A Hermitian upper Hessenberg matrix is tridiagonal.
Port of `NLAlib.IsUpperHessenberg.isTridiagonal_of_isHermitian`. -/
theorem IsUpperHessenberg.isTridiagonal {H : Matrix (Fin n) (Fin n) 𝕜}
    (hH : IsUpperHessenberg H) (h : H.IsHermitian) : IsTridiagonal H := by
  refine isTridiagonal_iff.mpr ⟨hH, fun i j hij => ?_⟩
  rw [Matrix.transpose_apply, ← h.apply j i, hH i j hij, star_zero]

/-- An upper Hessenberg matrix times an upper triangular one is upper Hessenberg.
Port of `NLAlib.IsUpperHessenberg.mul_isUpperTriangular`. -/
theorem IsUpperHessenberg.mul_isUpperTriangular [NonUnitalNonAssocSemiring R]
    {H : Matrix (Fin m) (Fin n) R} {U : Matrix (Fin n) (Fin n) R} (hH : IsUpperHessenberg H)
    (hU : U.IsUpperTriangular) : IsUpperHessenberg (H * U) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) + 1 < i
  · rw [hH i k hk, zero_mul]
  · rw [hU (show j < k from Fin.lt_def.mpr (by omega)), mul_zero]

/-- An upper triangular matrix times an upper Hessenberg one is upper Hessenberg.
Port of `NLAlib.IsUpperHessenberg.isUpperTriangular_mul`. -/
theorem IsUpperHessenberg.isUpperTriangular_mul [NonUnitalNonAssocSemiring R]
    {U : Matrix (Fin m) (Fin m) R} {H : Matrix (Fin m) (Fin n) R} (hU : U.IsUpperTriangular)
    (hH : IsUpperHessenberg H) : IsUpperHessenberg (U * H) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) < i
  · rw [hU (show k < i from Fin.lt_def.mpr hk), zero_mul]
  · rw [hH k j (by omega), mul_zero]

/-- A shift of an upper Hessenberg matrix is upper Hessenberg.
Port of `NLAlib.IsUpperHessenberg.sub_smul_one`. -/
theorem IsUpperHessenberg.sub_smul_one [Ring R] {H : Matrix (Fin n) (Fin n) R}
    (hH : IsUpperHessenberg H) (μ : R) : IsUpperHessenberg (H - μ • (1 : Matrix _ _ R)) := by
  intro i j hij
  have hne : i ≠ j := fun h => by subst h; omega
  rw [Matrix.sub_apply, Matrix.smul_apply, hH i j hij, Matrix.one_apply_ne hne, smul_zero,
    sub_zero]

/-! ### Reduction -/

/-- A Hermitian unitary matrix that fixes the first `p` coordinate vectors and clears a vector
below coordinate `p`. -/
private theorem exists_reflector (x : Fin n → 𝕜) (p : ℕ) :
    ∃ P : Matrix (Fin n) (Fin n) 𝕜, P.IsHermitian ∧ P * P = 1 ∧
      (∀ i j : Fin n, (j : ℕ) < p → P i j = (1 : Matrix (Fin n) (Fin n) 𝕜) i j) ∧
      ∀ i : Fin n, p < (i : ℕ) → (P *ᵥ x) i = 0 := by
  by_cases h : p < n
  swap
  · exact ⟨1, Matrix.isHermitian_one, Matrix.one_mul 1, fun _ _ _ => rfl,
      fun i hi => absurd (hi.trans i.2) h⟩
  set y : Fin n → 𝕜 := fun l => if p ≤ (l : ℕ) then x l else 0 with hy
  set z : Fin n → 𝕜 := fun l => if p ≤ (l : ℕ) then 0 else x l with hz
  set v := householderVector y ⟨p, h⟩ with hv
  have hv0 : ∀ l : Fin n, (l : ℕ) < p → v l = 0 := by
    intro l hl
    have hne : l ≠ ⟨p, h⟩ := fun e => hl.ne (congrArg Fin.val e)
    rw [hv, householderVector, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero,
      add_zero, hy]
    exact if_neg (not_le.mpr hl)
  refine ⟨householder v, isHermitian_householder v, householder_mul_self v, fun i j hj => ?_,
    fun i hi => ?_⟩
  · rw [householder, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      hv0 j hj, star_zero, mul_zero, smul_zero, sub_zero]
  · have hx : x = y + z := by
      ext l
      by_cases hl : p ≤ (l : ℕ)
      · simp only [hy, hz, Pi.add_apply, if_pos hl, add_zero]
      · simp only [hy, hz, Pi.add_apply, if_neg hl, zero_add]
    have hfix : householder v *ᵥ z = z := by
      refine householder_mulVec_of_dotProduct_eq_zero (Finset.sum_eq_zero fun l _ => ?_)
      by_cases hl : p ≤ (l : ℕ)
      · simp only [hz, if_pos hl, mul_zero]
      · rw [Pi.star_apply, hv0 l (not_le.mp hl), star_zero, zero_mul]
    have hi' : i ≠ ⟨p, h⟩ := fun e => hi.ne' (congrArg Fin.val e)
    rw [hx, Matrix.mulVec_add, hfix, Pi.add_apply,
      householder_mulVec_householderVector_apply_of_ne y hi', zero_add]
    exact if_pos hi.le

/-- The state of the reduction to Hessenberg form after `k` reflectors: the first `k` columns
are in Hessenberg form. -/
private theorem exists_hessenberg_state (A : Matrix (Fin n) (Fin n) 𝕜) (k : ℕ) :
    ∃ Q : Matrix (Fin n) (Fin n) 𝕜, HasOrthonormalCols Q ∧
      (∀ i j : Fin n, (j : ℕ) < k → (j : ℕ) + 1 < (i : ℕ) → (Qᴴ * A * Q) i j = 0) ∧
      ∀ i : Fin n, (i : ℕ) = 0 → Q.col i = Pi.single i 1 := by
  induction k with
  | zero =>
    exact ⟨1, hasOrthonormalCols_one, fun i j hj => absurd hj (Nat.not_lt_zero _),
      fun i _ => (Matrix.mulVec_single_one 1 i).symm.trans (Matrix.one_mulVec _)⟩
  | succ k ih =>
    obtain ⟨Q, hQ, hW, hcol⟩ := ih
    obtain ⟨P, hPH, hPP, hP1, hPx⟩ := exists_reflector
      (fun l : Fin n => if h : k < n then (Qᴴ * A * Q) l ⟨k, h⟩ else 0) (k + 1)
    have hPo : HasOrthonormalCols P := by rw [HasOrthonormalCols, hPH.eq, hPP]
    have hmulP : ∀ (M : Matrix (Fin n) (Fin n) 𝕜) (i j : Fin n), (j : ℕ) < k + 1 →
        (M * P) i j = M i j := by
      intro M i j hj
      rw [Matrix.mul_apply]
      simp only [hP1 _ j hj]
      rw [← Matrix.mul_apply, Matrix.mul_one]
    refine ⟨Q * P, hQ.mul hPo, fun i j hj hji => ?_, fun i hi => ?_⟩
    · have hE : (Q * P)ᴴ * A * (Q * P) = P * (Qᴴ * A * Q) * P := by
        rw [Matrix.conjTranspose_mul, hPH.eq]
        simp only [Matrix.mul_assoc]
      rw [hE, hmulP _ i j hj]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
      · have hsum : (P * (Qᴴ * A * Q)) i j =
            ((1 : Matrix (Fin n) (Fin n) 𝕜) * (Qᴴ * A * Q)) i j := by
          rw [Matrix.mul_apply, Matrix.mul_apply]
          refine Finset.sum_congr rfl fun l _ => ?_
          by_cases hl : (l : ℕ) < k + 1
          · rw [hP1 i l hl]
          · rw [hW l j hjk (by omega), mul_zero, mul_zero]
        rw [hsum, Matrix.one_mul]
        exact hW i j hjk hji
      · have hkn : k < n := hjk ▸ j.2
        have hjeq : j = ⟨k, hkn⟩ := Fin.ext hjk
        have h := hPx i (by omega)
        simp only [dif_pos hkn] at h
        rw [hjeq]
        exact h
    · ext l
      rw [Matrix.col_apply, hmulP Q l i (by omega)]
      exact congrFun (hcol i hi) l

/-- **Reduction to Hessenberg form.** Every square matrix is unitarily similar to an upper
Hessenberg matrix, by a unitary matrix whose first column is the first coordinate vector.
[GolubVanLoan2013, §7.4.3]; [HornJohnson2013, §2.5].
Port of `NLAlib.exists_isHessenbergForm`, which the prototype leaves unproved.
Result: hessenberg-reduction -/
theorem exists_isUpperHessenberg_conjTranspose_mul_mul (A : Matrix (Fin n) (Fin n) 𝕜) :
    ∃ Q : Matrix (Fin n) (Fin n) 𝕜, HasOrthonormalCols Q ∧ IsUpperHessenberg (Qᴴ * A * Q) ∧
      ∀ i : Fin n, (i : ℕ) = 0 → Q.col i = Pi.single i 1 := by
  obtain ⟨Q, hQ, hW, hcol⟩ := exists_hessenberg_state A n
  exact ⟨Q, hQ, fun i j hij => hW i j j.2 hij, hcol⟩

/-- **Reduction to tridiagonal form.** Every Hermitian matrix is unitarily similar to a
Hermitian tridiagonal matrix. [GolubVanLoan2013, §8.3.1].
Port of `NLAlib.IsHessenbergForm.isTridiagonal`. -/
theorem _root_.Matrix.IsHermitian.exists_isTridiagonal_conjTranspose_mul_mul
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    ∃ Q : Matrix (Fin n) (Fin n) 𝕜, HasOrthonormalCols Q ∧ IsTridiagonal (Qᴴ * A * Q) ∧
      ∀ i : Fin n, (i : ℕ) = 0 → Q.col i = Pi.single i 1 := by
  obtain ⟨Q, hQ, hH, hcol⟩ := exists_isUpperHessenberg_conjTranspose_mul_mul A
  exact ⟨Q, hQ, hH.isTridiagonal (Matrix.isHermitian_conjTranspose_mul_mul Q hA), hcol⟩

/-! ### The QR iteration -/

/-- The state of the QR factorization of a Hessenberg matrix by Givens rotations after `k`
rotations: `S` is the conjugate transpose of the accumulated unitary factor, the first `k`
columns of `R` are triangular, and the rows of `S` beyond row `k` are those of the identity. -/
private theorem exists_givens_state {H : Matrix (Fin n) (Fin n) 𝕜} (hH : IsUpperHessenberg H)
    (k : ℕ) :
    ∃ S R : Matrix (Fin n) (Fin n) 𝕜, HasOrthonormalCols S ∧ S * H = R ∧ IsUpperHessenberg R ∧
      (∀ i j : Fin n, (j : ℕ) < k → j < i → R i j = 0) ∧
      (∀ i j : Fin n, (i : ℕ) + 1 < (j : ℕ) → S i j = 0) ∧
      ∀ i j : Fin n, k < (i : ℕ) → S i j = (1 : Matrix (Fin n) (Fin n) 𝕜) i j := by
  induction k with
  | zero =>
    exact ⟨1, H, hasOrthonormalCols_one, Matrix.one_mul H, hH,
      fun _ _ hj => absurd hj (Nat.not_lt_zero _),
      fun i j hij => Matrix.one_apply_ne fun e => by subst e; omega, fun _ _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨S, R, hS, hSH, hR, hRk, hSl, hS1⟩ := ih
    by_cases hk : k + 1 < n
    swap
    · refine ⟨S, R, hS, hSH, hR, fun i j hj hji => hRk i j ?_ hji, hSl,
        fun i j hi => hS1 i j (by omega)⟩
      have := i.2
      have := Fin.lt_def.mp hji
      omega
    set a : Fin n := ⟨k, by omega⟩ with ha
    set b : Fin n := ⟨k + 1, hk⟩ with hb
    have hab : a ≠ b := fun e => by simpa [ha, hb] using congrArg Fin.val e
    obtain ⟨c, s, hcs, hz, -⟩ := exists_givens_mulVec_apply_eq_zero hab fun l => R l a
    have hne : ∀ i : Fin n, (i : ℕ) ≠ k → (i : ℕ) ≠ k + 1 → i ≠ a ∧ i ≠ b :=
      fun i h1 h2 => ⟨fun e => h1 (congrArg Fin.val e), fun e => h2 (congrArg Fin.val e)⟩
    have hRa : ∀ j : Fin n, (j : ℕ) < k → R a j = 0 := fun j hj => hRk a j hj (Fin.lt_def.mpr hj)
    have hRb : ∀ j : Fin n, (j : ℕ) < k → R b j = 0 := fun j hj => hR b j (by simpa [hb] using hj)
    have hSa : ∀ j : Fin n, k + 1 < (j : ℕ) → S a j = 0 := fun j hj => hSl a j hj
    have hSb : ∀ j : Fin n, k + 1 < (j : ℕ) → S b j = 0 := fun j hj => by
      rw [hS1 b j (Nat.lt_succ_self k), Matrix.one_apply_ne fun e => hj.ne (congrArg Fin.val e)]
    have hGa : ∀ (M : Matrix (Fin n) (Fin n) 𝕜) (j : Fin n), M a j = 0 → M b j = 0 →
        (givens a b c s * M) a j = 0 := fun M j h1 h2 => by
      rw [givens_mul_apply_left hab, h1, h2, mul_zero, mul_zero, add_zero]
    have hGb : ∀ (M : Matrix (Fin n) (Fin n) 𝕜) (j : Fin n), M a j = 0 → M b j = 0 →
        (givens a b c s * M) b j = 0 := fun M j h1 h2 => by
      rw [givens_mul_apply_right hab, h1, h2, mul_zero, mul_zero, add_zero]
    refine ⟨givens a b c s * S, givens a b c s * R, (hasOrthonormalCols_givens hab hcs).mul hS,
      by rw [Matrix.mul_assoc, hSH], fun i j hij => ?_, fun i j hj hji => ?_, fun i j hij => ?_,
      fun i j hi => ?_⟩
    · by_cases hia : (i : ℕ) = k
      · rw [show i = a from Fin.ext hia]
        exact hGa R j (hRa j (by omega)) (hRb j (by omega))
      by_cases hib : (i : ℕ) = k + 1
      · rw [show i = b from Fin.ext hib]
        exact hGb R j (hRa j (by omega)) (hRb j (by omega))
      rw [givens_mul_apply_of_ne (hne i hia hib).1 (hne i hia hib).2]
      exact hR i j hij
    · have hji' := Fin.lt_def.mp hji
      by_cases hia : (i : ℕ) = k
      · rw [show i = a from Fin.ext hia]
        exact hGa R j (hRa j (by omega)) (hRb j (by omega))
      by_cases hib : (i : ℕ) = k + 1
      · rw [show i = b from Fin.ext hib]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
        · exact hGb R j (hRa j hjk) (hRb j hjk)
        · rw [show j = a from Fin.ext hjk]
          exact hz
      rw [givens_mul_apply_of_ne (hne i hia hib).1 (hne i hia hib).2]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
      · exact hRk i j hjk hji
      · exact hR i j (by omega)
    · by_cases hia : (i : ℕ) = k
      · rw [show i = a from Fin.ext hia]
        exact hGa S j (hSa j (by omega)) (hSb j (by omega))
      by_cases hib : (i : ℕ) = k + 1
      · rw [show i = b from Fin.ext hib]
        exact hGb S j (hSa j (by omega)) (hSb j (by omega))
      rw [givens_mul_apply_of_ne (hne i hia hib).1 (hne i hia hib).2]
      exact hSl i j hij
    · rw [givens_mul_apply_of_ne (hne i (by omega) (by omega)).1 (hne i (by omega) (by omega)).2]
      exact hS1 i j (by omega)

/-- **A Hessenberg matrix has a QR factorization with a Hessenberg unitary factor.** No rank
assumption is made.
[GolubVanLoan2013, §5.2.5]. Port of `NLAlib.isQR_givensQR` with
`NLAlib.isUpperHessenberg_givensQR_fst`, which the prototype leaves unproved. -/
theorem IsUpperHessenberg.exists_isQR {H : Matrix (Fin n) (Fin n) 𝕜}
    (hH : IsUpperHessenberg H) : ∃ Q R, IsQR H Q R ∧ IsUpperHessenberg Q := by
  obtain ⟨S, R, hS, hSH, -, hRk, hSl, -⟩ := exists_givens_state hH n
  refine ⟨Sᴴ, R, ⟨?_, hS.conjTranspose, fun i j hji => hRk i j j.2 hji⟩, fun i j hij => ?_⟩
  · rw [← hSH, ← Matrix.mul_assoc, hS.conjTranspose_mul_self, Matrix.one_mul]
  · rw [Matrix.conjTranspose_apply, hSl j i hij, star_zero]

/-- A step of the QR iteration with a Hessenberg unitary factor keeps the Hessenberg form.
Port of `NLAlib.isUpperHessenberg_givensQR_snd_mul_fst`. -/
theorem IsQR.isUpperHessenberg_mul {H Q R : Matrix (Fin n) (Fin n) 𝕜} (h : IsQR H Q R)
    (hQ : IsUpperHessenberg Q) : IsUpperHessenberg (R * Q) := by
  exact hQ.isUpperTriangular_mul h.isUpperTriangular

/-- For a nonsingular Hessenberg matrix the unitary factor of any QR factorization is
Hessenberg. Port of `NLAlib.isUpperHessenberg_mul_of_isQR`. -/
theorem IsQR.isUpperHessenberg_of_isUpperHessenberg {H Q R : Matrix (Fin n) (Fin n) 𝕜}
    (h : IsQR H Q R) (hH : IsUpperHessenberg H) (hR : ∀ i, R i i ≠ 0) :
    IsUpperHessenberg Q := by
  have hu : IsUnit R.det := h.isUpperTriangular.isUnit_det_iff.mpr fun i => (hR i).isUnit
  have hQ : Q = H * R⁻¹ := by
    rw [h.eq_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  rw [hQ]
  exact hH.mul_isUpperTriangular h.isUpperTriangular.inv

/-- **The QR iteration preserves tridiagonal Hermitian matrices.** That `H` is tridiagonal is not
a hypothesis: it follows from `H = Q R` being Hermitian with `Q` upper Hessenberg.
[GolubVanLoan2013, §8.3.3]. Port of `NLAlib.isTridiagonal_mul_of_isQR`. -/
theorem IsQR.isTridiagonal_mul {H Q R : Matrix (Fin n) (Fin n) 𝕜} (h : IsQR H Q R)
    (hH : H.IsHermitian) (hQ : IsUpperHessenberg Q) : IsTridiagonal (R * Q) := by
  exact (h.isUpperHessenberg_mul hQ).isTridiagonal (h.isHermitian_mul hH)

/-! ### The implicit Q theorem -/

/-- The change of basis between two Hessenberg forms with the same first column, the first of
them unreduced, is upper triangular. -/
private theorem isUpperTriangular_of_mul_eq_mul {H₁ H₂ V : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜}
    (hH₁ : IsUpperHessenberg H₁) (hH₂ : IsUpperHessenberg H₂) (hHV : H₂ * V = V * H₁)
    (hV0 : ∀ i : Fin (n + 1), i ≠ 0 → V i 0 = 0)
    (hsub : ∀ i j : Fin (n + 1), (i : ℕ) = j + 1 → H₁ i j ≠ 0) : V.IsUpperTriangular := by
  have key : ∀ (j : ℕ) (i c : Fin (n + 1)), (c : ℕ) ≤ j → c < i → V i c = 0 := by
    intro j
    induction j with
    | zero =>
      intro i c hc hci
      obtain rfl : c = 0 := Fin.ext (Nat.le_zero.mp hc)
      exact hV0 i hci.ne'
    | succ j ih =>
      intro i c hc hci
      have hci' := Fin.lt_def.mp hci
      rcases Nat.lt_or_ge (c : ℕ) (j + 1) with h | h
      · exact ih i c (by omega) hci
      have hcj : (c : ℕ) = j + 1 := le_antisymm hc h
      have hjn : j < n + 1 := by have := c.2; omega
      have h1 : (H₂ * V) i ⟨j, hjn⟩ = (V * H₁) i ⟨j, hjn⟩ := by rw [hHV]
      rw [Matrix.mul_apply, Matrix.mul_apply] at h1
      have hL : ∑ l, H₂ i l * V l ⟨j, hjn⟩ = 0 := by
        refine Finset.sum_eq_zero fun l _ => ?_
        by_cases hl : (l : ℕ) ≤ j
        · rw [hH₂ i l (by omega), zero_mul]
        · rw [ih l ⟨j, hjn⟩ le_rfl (Fin.lt_def.mpr (not_le.mp hl)), mul_zero]
      have hR : ∑ l, V i l * H₁ l ⟨j, hjn⟩ = V i c * H₁ c ⟨j, hjn⟩ := by
        refine Finset.sum_eq_single c (fun l _ hlc => ?_) fun h => absurd (Finset.mem_univ _) h
        by_cases hl : (l : ℕ) ≤ j
        · rw [ih i l hl (Fin.lt_def.mpr (by omega)), zero_mul]
        · have hlc' : (l : ℕ) ≠ c := fun e => hlc (Fin.ext e)
          rw [hH₁ l ⟨j, hjn⟩ (by simp only; omega), mul_zero]
      rw [hL, hR] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_right (hsub c ⟨j, hjn⟩ hcj)
  exact fun i c hci => key c i c le_rfl hci

/-- **The implicit Q theorem.** If `Q₁ᴴ A Q₁ = H₁` and `Q₂ᴴ A Q₂ = H₂` are upper Hessenberg with
`Q₁`, `Q₂` unitary with the same first column, and the subdiagonal of `H₁` has no zero, then
`Q₂ = Q₁ D` and `H₂ = Dᴴ H₁ D` for a diagonal `D` of unit modulus with first entry one.
[GolubVanLoan2013, Theorem 7.4.2].
Port of `NLAlib.IsHessenbergForm.exists_sign`, which the prototype leaves unproved.
Result: implicit-q -/
theorem exists_eq_mul_diagonal_of_isUpperHessenberg {A Q₁ Q₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜}
    (hQ₁ : HasOrthonormalCols Q₁) (hQ₂ : HasOrthonormalCols Q₂)
    (hH₁ : IsUpperHessenberg (Q₁ᴴ * A * Q₁)) (hH₂ : IsUpperHessenberg (Q₂ᴴ * A * Q₂))
    (hcol : Q₁.col 0 = Q₂.col 0)
    (hsub : ∀ i j : Fin (n + 1), (i : ℕ) = j + 1 → (Q₁ᴴ * A * Q₁) i j ≠ 0) :
    ∃ d : Fin (n + 1) → 𝕜, (∀ i, ‖d i‖ = 1) ∧ d 0 = 1 ∧ Q₂ = Q₁ * Matrix.diagonal d ∧
      Q₂ᴴ * A * Q₂ = Matrix.diagonal (star d) * (Q₁ᴴ * A * Q₁) * Matrix.diagonal d := by
  have hQ₁' : Q₁ * Q₁ᴴ = 1 := hQ₁.mul_conjTranspose_self
  have hQ₂' : Q₂ * Q₂ᴴ = 1 := hQ₂.mul_conjTranspose_self
  have hVo : HasOrthonormalCols (Q₂ᴴ * Q₁) := hQ₂.conjTranspose.mul hQ₁
  have hHV : Q₂ᴴ * A * Q₂ * (Q₂ᴴ * Q₁) = Q₂ᴴ * Q₁ * (Q₁ᴴ * A * Q₁) := by
    calc Q₂ᴴ * A * Q₂ * (Q₂ᴴ * Q₁) = Q₂ᴴ * A * (Q₂ * Q₂ᴴ) * Q₁ := by
          simp only [Matrix.mul_assoc]
      _ = Q₂ᴴ * (Q₁ * Q₁ᴴ) * A * Q₁ := by rw [hQ₂', hQ₁', Matrix.mul_one, Matrix.mul_one]
      _ = Q₂ᴴ * Q₁ * (Q₁ᴴ * A * Q₁) := by simp only [Matrix.mul_assoc]
  have hV0 : ∀ i : Fin (n + 1),
      (Q₂ᴴ * Q₁) i 0 = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜) i 0 := by
    intro i
    rw [← hQ₂.conjTranspose_mul_self, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [show Q₁ l 0 = Q₂ l 0 from congrFun hcol l]
  have hU : (Q₂ᴴ * Q₁).IsUpperTriangular :=
    isUpperTriangular_of_mul_eq_mul hH₁ hH₂ hHV
      (fun i hi => by rw [hV0 i, Matrix.one_apply_ne hi]) hsub
  have hL : (Q₂ᴴ * Q₁).IsLowerTriangular := by
    have h := hU.inv
    rw [hVo.inv_eq] at h
    intro i j hij
    have h2 := h (i := j) (j := i) hij
    rwa [Matrix.conjTranspose_apply, star_eq_zero] at h2
  have hD := eq_diagonal_of_isLowerTriangular_of_isUpperTriangular hL hU
  set e : Fin (n + 1) → 𝕜 := fun i => (Q₂ᴴ * Q₁) i i with he
  have hee : ∀ i, star (e i) * e i = 1 := by
    intro i
    have h := congrFun (congrFun hVo.conjTranspose_mul_self i) i
    rw [hD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] at h
    exact h
  have hQ₂e : Q₂ = Q₁ * Matrix.diagonal (star e) := by
    rw [← Matrix.diagonal_conjTranspose, ← hD, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, hQ₁', Matrix.one_mul]
  refine ⟨star e, fun i => ?_, ?_, hQ₂e, ?_⟩
  · have h := congrArg norm (hee i)
    rw [norm_mul, norm_star, norm_one] at h
    rw [Pi.star_apply, norm_star]
    nlinarith [norm_nonneg (e i)]
  · rw [Pi.star_apply, he]
    simp only [hV0 0, Matrix.one_apply_eq, star_one]
  · rw [star_star, ← Matrix.diagonal_conjTranspose e, ← hD, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, ← hHV]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q₁, hQ₁', Matrix.one_mul, hQ₂.conjTranspose_mul_self, Matrix.mul_one]

end NLAlib
