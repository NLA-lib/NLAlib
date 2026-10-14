/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.Simultaneous
public import NLAlib.Matrix.Spectral.QuasiTriangular

/-!
# The real Schur form

A real square matrix is orthogonally similar to an upper quasi-triangular matrix: block upper
triangular with diagonal blocks of size one and two, the blocks of size two having a pair of complex
conjugate eigenvalues. A real normal matrix is orthogonally similar to a direct sum of real scalars
and scaled rotations (for a skew-symmetric matrix the scalars vanish, for an orthogonal matrix the
blocks are `±1` and rotations). A pair of real matrices is reduced by two orthogonal matrices to an
upper quasi-triangular and an upper triangular matrix.

The three theorems are proved by the same deflation: a real matrix has an invariant subspace of
dimension one or two, spanned by the real and imaginary parts of a complex eigenvector, whose
phase is chosen so that the two parts are orthogonal.

## Main definitions

* `NLAlib.IsRealSchurForm`: upper quasi-triangular with standardised blocks of size two.

## Main results

* `NLAlib.exists_hasOrthonormalCols_isRealSchurForm`: the real Schur form.
* `NLAlib.exists_hasOrthonormalCols_isRealSchurForm_of_isStarNormal`: real normal matrices.
* `NLAlib.exists_hasOrthonormalCols_isUpperQuasiTriangular_isUpperTriangular`: the real QZ
  decomposition.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {R : Type*} {k : ℕ}

/-- A real matrix is in **real Schur form** if it is upper quasi-triangular and each diagonal
block of size two has equal diagonal entries and off-diagonal entries of opposite sign, so that
its eigenvalues are a pair of non-real complex conjugates. [HornJohnson2013, Theorem 2.3.4].
Port of `NLAlib.IsRealSchurForm`. -/
def IsRealSchurForm (T : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  IsUpperQuasiTriangular T ∧
    ∀ i j : Fin k, (j : ℕ) + 1 = (i : ℕ) → T i j ≠ 0 → T i i = T j j ∧ T j i * T i j < 0

/-! ### Blocks indexed by `Fin (p + q)` -/

/-- The matrix with blocks `S`, `C`, `D`, `T`, indexed by `Fin (p + q)`. -/
private def finBlocks {p q : ℕ} (S : Matrix (Fin p) (Fin p) R) (C : Matrix (Fin p) (Fin q) R)
    (D : Matrix (Fin q) (Fin p) R) (T : Matrix (Fin q) (Fin q) R) :
    Matrix (Fin (p + q)) (Fin (p + q)) R :=
  (Matrix.fromBlocks S C D T).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- The matrix with columns those of `Q₁` followed by those of `Q₂`, indexed by `Fin (p + q)`. -/
private def finCols {m : Type*} {p q : ℕ} (Q₁ : Matrix m (Fin p) R) (Q₂ : Matrix m (Fin q) R) :
    Matrix m (Fin (p + q)) R :=
  (Matrix.fromCols Q₁ Q₂).submatrix id finSumFinEquiv.symm

section finBlocks

variable {p q : ℕ} {S : Matrix (Fin p) (Fin p) R} {C : Matrix (Fin p) (Fin q) R}
  {D : Matrix (Fin q) (Fin p) R} {T : Matrix (Fin q) (Fin q) R}

private theorem finBlocks_castAdd_castAdd (i j : Fin p) :
    finBlocks S C D T (Fin.castAdd q i) (Fin.castAdd q j) = S i j := by
  simp [finBlocks]

private theorem finBlocks_castAdd_natAdd (i : Fin p) (j : Fin q) :
    finBlocks S C D T (Fin.castAdd q i) (Fin.natAdd p j) = C i j := by
  simp [finBlocks]

private theorem finBlocks_natAdd_castAdd (i : Fin q) (j : Fin p) :
    finBlocks S C D T (Fin.natAdd p i) (Fin.castAdd q j) = D i j := by
  simp [finBlocks]

private theorem finBlocks_natAdd_natAdd (i j : Fin q) :
    finBlocks S C D T (Fin.natAdd p i) (Fin.natAdd p j) = T i j := by
  simp [finBlocks]

end finBlocks

private theorem isRealSchurForm_finBlocks {p q : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    {T : Matrix (Fin q) (Fin q) ℝ} (C : Matrix (Fin p) (Fin q) ℝ) (hS : IsRealSchurForm S)
    (hT : IsRealSchurForm T) : IsRealSchurForm (finBlocks S C 0 T) := by
  refine ⟨hS.1.submatrix_fromBlocks hT.1 C, fun i j => ?_⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro h hne
  · simp only [finBlocks_castAdd_castAdd] at hne ⊢
    exact hS.2 i j (by simpa only [Fin.val_castAdd] using h) hne
  · have := i.isLt
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h
    omega
  · exact absurd (by rw [finBlocks_natAdd_castAdd, Matrix.zero_apply]) hne
  · simp only [finBlocks_natAdd_natAdd] at hne ⊢
    exact hT.2 i j (by simp only [Fin.val_natAdd] at h; omega) hne

/-! ### Deflation -/

section finCols

variable {m : Type*} [Fintype m] {p q : ℕ}

private theorem hasOrthonormalCols_finCols {Q₁ : Matrix m (Fin p) ℝ} {Q₂ : Matrix m (Fin q) ℝ}
    (hQ : HasOrthonormalCols (Matrix.fromCols Q₁ Q₂)) {Q' : Matrix (Fin q) (Fin q) ℝ}
    (hQ' : HasOrthonormalCols Q') : HasOrthonormalCols (finCols Q₁ (Q₂ * Q')) := by
  obtain ⟨h₁, h₂, h₁₂⟩ := hasOrthonormalCols_fromCols_iff.mp hQ
  have h : HasOrthonormalCols (Matrix.fromCols Q₁ (Q₂ * Q')) :=
    hasOrthonormalCols_fromCols_iff.mpr ⟨h₁, h₂.mul hQ', by rw [← Matrix.mul_assoc, h₁₂,
      Matrix.zero_mul]⟩
  exact h.submatrix (Equiv.refl m) finSumFinEquiv.symm.injective

/-- Deflation: if `M * Z₁ = Q₁ * S` then in bases extending `Q₁` and `Z₁` the matrix `M` is
block upper triangular with leading block `S`. -/
private theorem conjTranspose_finCols_mul_mul_finCols {Q₁ Z₁ : Matrix m (Fin p) ℝ}
    {Q₂ : Matrix m (Fin q) ℝ} (hQ : HasOrthonormalCols (Matrix.fromCols Q₁ Q₂))
    {M : Matrix m m ℝ} {S : Matrix (Fin p) (Fin p) ℝ} (h : M * Z₁ = Q₁ * S)
    (Z₂ : Matrix m (Fin q) ℝ) (Q' Z' : Matrix (Fin q) (Fin q) ℝ) :
    (finCols Q₁ (Q₂ * Q'))ᴴ * M * finCols Z₁ (Z₂ * Z') =
      finBlocks S (Q₁ᴴ * M * (Z₂ * Z')) 0 (Q'ᴴ * (Q₂ᴴ * M * Z₂) * Z') := by
  obtain ⟨h₁, -, h₁₂⟩ := hasOrthonormalCols_fromCols_iff.mp hQ
  have h₂₁ : Q₂ᴴ * Q₁ = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose Q₁, ← Matrix.conjTranspose_mul, h₁₂,
      Matrix.conjTranspose_zero]
  have hblocks : (Matrix.fromCols Q₁ (Q₂ * Q'))ᴴ * M * Matrix.fromCols Z₁ (Z₂ * Z') =
      Matrix.fromBlocks S (Q₁ᴴ * M * (Z₂ * Z')) 0 (Q'ᴴ * (Q₂ᴴ * M * Z₂) * Z') := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols]
    congr 1
    · rw [Matrix.mul_assoc, h, h₁.conjTranspose_mul_cancel_left]
    · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, h, Matrix.mul_assoc Q'ᴴ,
        ← Matrix.mul_assoc Q₂ᴴ, h₂₁, Matrix.zero_mul, Matrix.mul_zero]
    · simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [finBlocks, ← hblocks]
  rfl

end finCols

/-! ### An invariant subspace of dimension one or two -/

/-- Real and imaginary parts of a complex eigenvector, with the phase chosen so that they are
orthogonal: `A (x + i y) = (a + i b) (x + i y)`. -/
private theorem exists_mulVec_eq_smul_sub_smul {n : Type*} [Fintype n] [Nonempty n]
    (A : Matrix n n ℝ) :
    ∃ (a b : ℝ) (x y : n → ℝ), (x ≠ 0 ∨ y ≠ 0) ∧ x ⬝ᵥ y = 0 ∧
      A *ᵥ x = a • x - b • y ∧ A *ᵥ y = b • x + a • y := by
  classical
  obtain ⟨z, d, hz, hd⟩ := exists_mulVec_eq_smul_of_pairwise_commute
    (fun _ : Unit => complexify A) (Subsingleton.pairwise)
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℂ, c ≠ 0 ∧ (c ^ 2 * ∑ i, z i ^ 2).im = 0 := by
    by_cases hw : ∑ i, z i ^ 2 = 0
    · exact ⟨1, one_ne_zero, by rw [hw, mul_zero, Complex.zero_im]⟩
    · obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (starRingEnd ℂ (∑ i, z i ^ 2)) two_pos
      refine ⟨c, fun h => hw ?_, ?_⟩
      · rw [h, zero_pow two_ne_zero] at hc
        exact (map_eq_zero _).mp hc.symm
      · rw [hc, mul_comm, Complex.mul_conj]
        exact Complex.ofReal_im _
  set w : n → ℂ := fun i => c * z i with hw
  have hAw : complexify A *ᵥ w = d () • w := by
    rw [show w = c • z from rfl, Matrix.mulVec_smul, hd, smul_comm]
  have hre (v : n → ℂ) (i : n) : (A *ᵥ fun j => (v j).re) i = ((complexify A *ᵥ v) i).re := by
    simp only [Matrix.mulVec, dotProduct, complexify_apply, Complex.re_sum, Complex.mul_re,
      RCLike.re_toComplex, RCLike.im_toComplex, RCLike.re_to_real, RCLike.im_to_real, zero_mul,
      sub_zero]
  have him (v : n → ℂ) (i : n) : (A *ᵥ fun j => (v j).im) i = ((complexify A *ᵥ v) i).im := by
    simp only [Matrix.mulVec, dotProduct, complexify_apply, Complex.im_sum, Complex.mul_im,
      RCLike.re_toComplex, RCLike.im_toComplex, RCLike.re_to_real, RCLike.im_to_real, zero_mul,
      add_zero]
  refine ⟨(d ()).re, (d ()).im, fun i => (w i).re, fun i => (w i).im, ?_, ?_, ?_, ?_⟩
  · by_contra h
    rw [not_or, not_not, not_not] at h
    refine hz (funext fun i => ?_)
    have hwi : w i = 0 := Complex.ext (congrFun h.1 i) (congrFun h.2 i)
    exact (mul_eq_zero.mp hwi).resolve_left hc0
  · have h2 : (c ^ 2 * ∑ i, z i ^ 2).im = 2 * ∑ i, (w i).re * (w i).im := by
      rw [Finset.mul_sum, Complex.im_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_pow, sq, Complex.mul_im]
      ring
    rw [hc] at h2
    change ∑ i, (w i).re * (w i).im = 0
    linarith
  · ext i
    rw [hre w i, hAw]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.mul_re]
  · ext i
    rw [him w i, hAw]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.mul_im]
    ring

private theorem exists_smul_dotProduct_smul_eq_one {n : Type*} [Fintype n] {w : n → ℝ}
    (hw : w ≠ 0) : ∃ s : ℝ, 0 < s ∧ (s • w) ⬝ᵥ (s • w) = 1 := by
  have hpos : 0 < w ⬝ᵥ w :=
    lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (w i))
      (fun h => hw (dotProduct_self_eq_zero.mp h.symm))
  refine ⟨(√(w ⬝ᵥ w))⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hpos), ?_⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
    Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']

/-- A matrix with prescribed orthonormal columns. -/
private theorem hasOrthonormalCols_transpose_of {m : Type*} [Fintype m] {p : ℕ}
    {c : Fin p → m → ℝ} (h : ∀ i j, c i ⬝ᵥ c j = if i = j then 1 else 0) :
    HasOrthonormalCols (Matrix.of c)ᵀ := by
  rw [hasOrthonormalCols_iff]
  ext i j
  rw [Matrix.one_apply, ← h i j, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by
    rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.transpose_apply,
      Matrix.of_apply, Matrix.of_apply, star_trivial]

private theorem mul_transpose_of_eq {m : Type*} [Fintype m] {p : ℕ} {A : Matrix m m ℝ}
    {c e : Fin p → m → ℝ} {S : Matrix (Fin p) (Fin p) ℝ}
    (h : ∀ j, A *ᵥ c j = ∑ l, S l j • e l) : A * (Matrix.of c)ᵀ = (Matrix.of e)ᵀ * S := by
  ext i j
  have hj := congrFun (h j) i
  rw [Finset.sum_apply] at hj
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Eq.trans ?_ (hj.trans (Finset.sum_congr rfl fun l _ => ?_))
  · rfl
  · rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    rfl

/-- The step of the real Schur form: an invariant subspace of dimension one or two with an
orthonormal basis in which the matrix is in real Schur form. -/
private theorem exists_mul_eq_mul_isRealSchurForm (hk : 0 < k) (A : Matrix (Fin k) (Fin k) ℝ) :
    ∃ (p : ℕ) (V : Matrix (Fin k) (Fin p) ℝ) (B : Matrix (Fin p) (Fin p) ℝ),
      0 < p ∧ p ≤ 2 ∧ HasOrthonormalCols V ∧ A * V = V * B ∧ IsRealSchurForm B := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨a, b, x, y, hxy, horth, hx, hy⟩ := exists_mulVec_eq_smul_sub_smul A
  by_cases hb : b = 0
  · obtain ⟨w, hw0, hw⟩ : ∃ w : Fin k → ℝ, w ≠ 0 ∧ A *ᵥ w = a • w := by
      rcases hxy with h | h
      · exact ⟨x, h, by rw [hx, hb, zero_smul, sub_zero]⟩
      · exact ⟨y, h, by rw [hy, hb, zero_smul, zero_add]⟩
    obtain ⟨s, -, hs⟩ := exists_smul_dotProduct_smul_eq_one hw0
    refine ⟨1, (Matrix.of ![s • w])ᵀ, Matrix.of ![![a]], one_pos, one_le_two,
      hasOrthonormalCols_transpose_of fun i j => ?_, mul_transpose_of_eq fun j => ?_,
      ⟨isUpperQuasiTriangular_of_le_two one_le_two _, fun i j h => ?_⟩⟩
    · rw [Fin.eq_zero i, Fin.eq_zero j, if_pos rfl]
      exact hs
    · rw [Fin.eq_zero j, Fin.sum_univ_one]
      change A *ᵥ (s • w) = a • s • w
      rw [Matrix.mulVec_smul, hw, smul_comm]
    · have := i.isLt
      omega
  · have hx0 : x ≠ 0 := by
      rintro rfl
      rw [Matrix.mulVec_zero, smul_zero, zero_sub, eq_comm, neg_eq_zero, smul_eq_zero] at hx
      exact hxy.elim (fun h => h rfl) (fun h => h (hx.resolve_left hb))
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [Matrix.mulVec_zero, smul_zero, add_zero, eq_comm, smul_eq_zero] at hy
      exact hx0 (hy.resolve_left hb)
    obtain ⟨s, hs0, hs⟩ := exists_smul_dotProduct_smul_eq_one hx0
    obtain ⟨t, ht0, ht⟩ := exists_smul_dotProduct_smul_eq_one hy0
    refine ⟨2, (Matrix.of ![s • x, t • y])ᵀ, Matrix.of ![![a, b * t / s], ![-(b * s / t), a]],
      two_pos, le_rfl, hasOrthonormalCols_transpose_of fun i j => ?_,
      mul_transpose_of_eq fun j => ?_,
      ⟨isUpperQuasiTriangular_of_le_two le_rfl _, fun i j h _ => ?_⟩⟩
    · have hst : (s • x) ⬝ᵥ (t • y) = 0 := by
        rw [smul_dotProduct, dotProduct_smul, horth, smul_zero, smul_zero]
      fin_cases i <;> fin_cases j
      · exact hs
      · exact hst
      · exact (dotProduct_comm _ _).trans hst
      · exact ht
    · fin_cases j
      · change A *ᵥ (s • x) = ∑ l : Fin 2,
          Matrix.of ![![a, b * t / s], ![-(b * s / t), a]] l 0 • ![s • x, t • y] l
        rw [Fin.sum_univ_two, Matrix.mulVec_smul, hx]
        ext i
        simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one]
        field_simp
        ring
      · change A *ᵥ (t • y) = ∑ l : Fin 2,
          Matrix.of ![![a, b * t / s], ![-(b * s / t), a]] l 1 • ![s • x, t • y] l
        rw [Fin.sum_univ_two, Matrix.mulVec_smul, hy]
        ext i
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one]
        field_simp
    · have hi : i = 1 := Fin.ext (by have := i.isLt; simp only [Fin.val_one]; omega)
      have hj : j = 0 := Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)
      subst hi hj
      refine ⟨rfl, ?_⟩
      change b * t / s * -(b * s / t) < 0
      have : b * t / s * -(b * s / t) = -(b ^ 2) := by
        field_simp
      rw [this]
      exact neg_lt_zero.mpr (by positivity)

/-! ### Real Schur and real normal forms -/

private theorem isStarNormal_conjTranspose_mul_mul {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] {W : Matrix m n ℝ} (h : W * Wᴴ = 1) {A : Matrix m m ℝ}
    (hA : IsStarNormal A) : IsStarNormal (Wᴴ * A * W) := by
  have hA' : Aᴴ * A = A * Aᴴ := hA.star_comm_self.eq
  rw [isStarNormal_iff, commute_iff_eq, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc Wᴴ * (Aᴴ * W) * (Wᴴ * A * W) = Wᴴ * (Aᴴ * (W * Wᴴ) * A) * W := by
        simp only [Matrix.mul_assoc]
    _ = Wᴴ * (A * (W * Wᴴ) * Aᴴ) * W := by rw [h, Matrix.mul_one, Matrix.mul_one, hA']
    _ = Wᴴ * A * W * (Wᴴ * (Aᴴ * W)) := by simp only [Matrix.mul_assoc]

private theorem isStarNormal_of_finBlocks {p q : ℕ} {S : Matrix (Fin p) (Fin p) ℝ}
    {C : Matrix (Fin p) (Fin q) ℝ} {D : Matrix (Fin q) (Fin p) ℝ} {T : Matrix (Fin q) (Fin q) ℝ}
    (h : IsStarNormal (finBlocks S C D T)) : IsStarNormal (Matrix.fromBlocks S C D T) := by
  have h1 := h.star_comm_self.eq
  rw [Matrix.star_eq_conjTranspose, finBlocks, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv] at h1
  exact ⟨(Matrix.reindex finSumFinEquiv finSumFinEquiv).injective h1⟩

/-- The diagonal blocks of a normal block diagonal matrix are normal. -/
private theorem isStarNormal_of_fromBlocks_zero {m n : Type*} [Fintype m] [Fintype n]
    {S : Matrix m m ℝ} {T : Matrix n n ℝ} (h : IsStarNormal (Matrix.fromBlocks S 0 0 T)) :
    IsStarNormal S ∧ IsStarNormal T := by
  have h1 := h.star_comm_self.eq
  rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h1
  have h2 := Matrix.fromBlocks_inj.mp h1
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add] at h2
  exact ⟨⟨h2.1⟩, ⟨h2.2.2.2⟩⟩

/-- A normal matrix of size at most two in real Schur form is antisymmetric off the diagonal. -/
private theorem apply_eq_neg_of_isRealSchurForm {p : ℕ} (hp : p ≤ 2)
    {B : Matrix (Fin p) (Fin p) ℝ} (hB : IsRealSchurForm B) (hN : IsStarNormal B) :
    ∀ i j, i ≠ j → B i j = -B j i := by
  interval_cases p
  · exact fun i => i.elim0
  · exact fun i j hij => absurd (Subsingleton.elim i j) hij
  · have h := congrFun (congrFun hN.star_comm_self.eq 0) 0
    simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, star_trivial] at h
    have key : B 0 1 = -B 1 0 := by
      by_cases h10 : B 1 0 = 0
      · have : B 0 1 * B 0 1 = 0 := by rw [h10] at h; linarith
        rw [h10, neg_zero]
        exact mul_self_eq_zero.mp this
      · have hlt := (hB.2 1 0 rfl h10).2
        have hne : B 0 1 - B 1 0 ≠ 0 := fun h0 => by
          rw [sub_eq_zero] at h0
          rw [h0] at hlt
          exact absurd hlt (not_lt.mpr (mul_self_nonneg _))
        have hz : (B 0 1 - B 1 0) * (B 0 1 + B 1 0) = 0 := by linarith
        exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hz).resolve_left hne)
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact key
    · exact (neg_eq_iff_eq_neg.mpr key).symm
    · exact absurd rfl hij

/-- The real Schur form together with the real normal form, by deflation of an invariant
subspace of dimension one or two. -/
private theorem exists_isRealSchurForm_conjTranspose_mul_mul (k : ℕ) :
    ∀ A : Matrix (Fin k) (Fin k) ℝ, ∃ Q : Matrix (Fin k) (Fin k) ℝ, HasOrthonormalCols Q ∧
      IsRealSchurForm (Qᴴ * A * Q) ∧
      (IsStarNormal A → ∀ i j, i ≠ j → (Qᴴ * A * Q) i j = -(Qᴴ * A * Q) j i) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro A
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, hasOrthonormalCols_one,
        ⟨⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩, fun _ i => i.elim0⟩
    obtain ⟨p, V, B, hp0, hp2, hV, hAV, hB⟩ := exists_mul_eq_mul_isRealSchurForm hk A
    obtain ⟨q, rfl⟩ : ∃ q, k = p + q :=
      Nat.exists_eq_add_of_le (by simpa only [Fintype.card_fin] using hV.card_le)
    obtain ⟨V₂, hW⟩ := hV.exists_fromCols (p := Fin q) (by simp only [Fintype.card_fin])
    obtain ⟨Q', hQ', hT', hN'⟩ := ih q (by omega) (V₂ᴴ * A * V₂)
    have hQ := hasOrthonormalCols_finCols hW hQ'
    have hblock := conjTranspose_finCols_mul_mul_finCols hW hAV V₂ Q' Q'
    refine ⟨finCols V (V₂ * Q'), hQ, ?_, fun hA => ?_⟩
    · rw [hblock]
      exact isRealSchurForm_finBlocks _ hB hT'
    · have hN := isStarNormal_conjTranspose_mul_mul hQ.mul_conjTranspose_self hA
      rw [hblock] at hN ⊢
      have hC : Vᴴ * A * (V₂ * Q') = 0 :=
        eq_zero_of_isStarNormal_fromBlocks (isStarNormal_of_finBlocks hN)
      rw [hC] at hN ⊢
      obtain ⟨hBn, hTn⟩ := isStarNormal_of_fromBlocks_zero (isStarNormal_of_finBlocks hN)
      have hA' : IsStarNormal (V₂ᴴ * A * V₂) := by
        have h := isStarNormal_conjTranspose_mul_mul (W := Q'ᴴ)
          (by rw [Matrix.conjTranspose_conjTranspose]; exact hQ'.conjTranspose_mul_self) hTn
        rwa [Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
          hQ'.mul_conjTranspose_self, Matrix.one_mul, Matrix.mul_assoc,
          hQ'.mul_conjTranspose_self, Matrix.mul_one] at h
      have h1 := apply_eq_neg_of_isRealSchurForm hp2 hB hBn
      have h2 := hN' hA'
      intro i j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro hij
      · rw [finBlocks_castAdd_castAdd, finBlocks_castAdd_castAdd]
        exact h1 i j fun h => hij (by rw [h])
      · rw [finBlocks_castAdd_natAdd, finBlocks_natAdd_castAdd, Matrix.zero_apply,
          Matrix.zero_apply, neg_zero]
      · rw [finBlocks_castAdd_natAdd, finBlocks_natAdd_castAdd, Matrix.zero_apply,
          Matrix.zero_apply, neg_zero]
      · rw [finBlocks_natAdd_natAdd, finBlocks_natAdd_natAdd]
        exact h2 i j fun h => hij (by rw [h])

/-- **The real Schur form.** Every real square matrix is orthogonally similar to a matrix in real
Schur form. [HornJohnson2013, Theorem 2.3.4]; [GolubVanLoan2013, Theorem 7.4.1].
Port of `NLAlib.exists_orthogonal_real_schur`.
Result: real-schur -/
theorem exists_hasOrthonormalCols_isRealSchurForm (A : Matrix (Fin k) (Fin k) ℝ) :
    ∃ Q T : Matrix (Fin k) (Fin k) ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᴴ ∧
      IsRealSchurForm T := by
  obtain ⟨Q, hQ, hT, -⟩ := exists_isRealSchurForm_conjTranspose_mul_mul k A
  exact ⟨Q, Qᴴ * A * Q, hQ, hQ.eq_mul_mul_conjTranspose_iff.mpr rfl, hT⟩

/-- **The real normal form.** Every real normal matrix is orthogonally similar to a direct sum of
real scalars and blocks `[[a, b], [-b, a]]`. [HornJohnson2013, Theorem 2.5.8].
Port of `NLAlib.exists_orthogonal_real_normal_form`. -/
theorem exists_hasOrthonormalCols_isRealSchurForm_of_isStarNormal
    {A : Matrix (Fin k) (Fin k) ℝ} (hA : IsStarNormal A) :
    ∃ Q T : Matrix (Fin k) (Fin k) ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᴴ ∧
      IsRealSchurForm T ∧ ∀ i j, i ≠ j → T i j = -T j i := by
  obtain ⟨Q, hQ, hT, hN⟩ := exists_isRealSchurForm_conjTranspose_mul_mul k A
  exact ⟨Q, Qᴴ * A * Q, hQ, hQ.eq_mul_mul_conjTranspose_iff.mpr rfl, hT, hN hA⟩

/-! ### The real QZ decomposition -/

/-- The step of the real QZ decomposition: a pair of subspaces of dimension one or two, with
orthonormal bases `Z₁` and `Q₁`, such that both matrices map the first into the second. -/
private theorem exists_mul_eq_mul_isUpperTriangular (hk : 0 < k)
    (A B : Matrix (Fin k) (Fin k) ℝ) :
    ∃ (p : ℕ) (Q₁ Z₁ : Matrix (Fin k) (Fin p) ℝ) (S R : Matrix (Fin p) (Fin p) ℝ),
      0 < p ∧ p ≤ 2 ∧ HasOrthonormalCols Q₁ ∧ HasOrthonormalCols Z₁ ∧ A * Z₁ = Q₁ * S ∧
      B * Z₁ = Q₁ * R ∧ R.IsUpperTriangular := by
  by_cases hB : IsUnit B.det
  · obtain ⟨p, V, K, hp0, hp2, hV, hMV, -⟩ := exists_mul_eq_mul_isRealSchurForm hk (B⁻¹ * A)
    obtain ⟨Q₁, R, hQR, -⟩ :=
      exists_isQR (B * V) (by simpa only [Fintype.card_fin] using hV.card_le)
    refine ⟨p, Q₁, V, R * K, R, hp0, hp2, hQR.hasOrthonormalCols, hV, ?_, hQR.eq_mul,
      hQR.isUpperTriangular⟩
    rw [← Matrix.mul_assoc, ← hQR.eq_mul, Matrix.mul_assoc B V K, ← hMV, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv B hB, Matrix.one_mul]
  · have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
      (by rwa [isUnit_iff_ne_zero, not_not] at hB)
    obtain ⟨s, -, hs⟩ := exists_smul_dotProduct_smul_eq_one hz0
    obtain ⟨u, c, hu, hAu⟩ : ∃ (u : Fin k → ℝ) (c : ℝ), u ⬝ᵥ u = 1 ∧ A *ᵥ (s • z) = c • u := by
      by_cases hw : A *ᵥ (s • z) = 0
      · exact ⟨Pi.single ⟨0, hk⟩ 1, 0, by rw [single_dotProduct, Pi.single_eq_same, one_mul],
          by rw [hw, zero_smul]⟩
      · obtain ⟨t, ht0, ht⟩ := exists_smul_dotProduct_smul_eq_one hw
        exact ⟨t • A *ᵥ (s • z), t⁻¹, ht, by rw [smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]⟩
    refine ⟨1, (Matrix.of ![u])ᵀ, (Matrix.of ![s • z])ᵀ, Matrix.of ![![c]], 0, one_pos,
      one_le_two, hasOrthonormalCols_transpose_of fun i j => ?_,
      hasOrthonormalCols_transpose_of fun i j => ?_, mul_transpose_of_eq fun j => ?_,
      mul_transpose_of_eq fun j => ?_, Matrix.blockTriangular_zero⟩
    · rw [Fin.eq_zero i, Fin.eq_zero j, if_pos rfl]
      exact hu
    · rw [Fin.eq_zero i, Fin.eq_zero j, if_pos rfl]
      exact hs
    · rw [Fin.eq_zero j, Fin.sum_univ_one]
      exact hAu
    · rw [Fin.eq_zero j, Fin.sum_univ_one]
      change B *ᵥ (s • z) = (0 : ℝ) • u
      rw [Matrix.mulVec_smul, hz, smul_zero, zero_smul]

/-- **The real QZ decomposition.** Every pair of real square matrices is reduced by two
orthogonal matrices to an upper quasi-triangular and an upper triangular matrix.
[GolubVanLoan2013, Theorem 7.7.2]. Port of `NLAlib.exists_orthogonal_qz_triangularization`. -/
theorem exists_hasOrthonormalCols_isUpperQuasiTriangular_isUpperTriangular
    (A B : Matrix (Fin k) (Fin k) ℝ) :
    ∃ Q Z : Matrix (Fin k) (Fin k) ℝ, HasOrthonormalCols Q ∧ HasOrthonormalCols Z ∧
      IsUpperQuasiTriangular (Qᴴ * A * Z) ∧ (Qᴴ * B * Z).IsUpperTriangular := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, 1, hasOrthonormalCols_one, hasOrthonormalCols_one,
        ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩
    obtain ⟨p, Q₁, Z₁, S, R, hp0, hp2, hQ₁, hZ₁, hA, hB, hR⟩ :=
      exists_mul_eq_mul_isUpperTriangular hk A B
    obtain ⟨q, rfl⟩ : ∃ q, k = p + q :=
      Nat.exists_eq_add_of_le (by simpa only [Fintype.card_fin] using hQ₁.card_le)
    obtain ⟨Q₂, hQ⟩ := hQ₁.exists_fromCols (p := Fin q) (by simp only [Fintype.card_fin])
    obtain ⟨Z₂, hZ⟩ := hZ₁.exists_fromCols (p := Fin q) (by simp only [Fintype.card_fin])
    obtain ⟨Q', Z', hQ', hZ', hTA, hTB⟩ := ih q (by omega) (Q₂ᴴ * A * Z₂) (Q₂ᴴ * B * Z₂)
    refine ⟨finCols Q₁ (Q₂ * Q'), finCols Z₁ (Z₂ * Z'), hasOrthonormalCols_finCols hQ hQ',
      hasOrthonormalCols_finCols hZ hZ', ?_, ?_⟩
    · rw [conjTranspose_finCols_mul_mul_finCols hQ hA Z₂ Q' Z']
      exact (isUpperQuasiTriangular_of_le_two hp2 S).submatrix_fromBlocks hTA _
    · rw [conjTranspose_finCols_mul_mul_finCols hQ hB Z₂ Q' Z']
      exact hR.submatrix_fromBlocks hTB _

end NLAlib
