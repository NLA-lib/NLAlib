/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.BasisExtension

/-!
# Exact column-wise two-pass classical Gram–Schmidt extends a basis

Column-wise classical Gram–Schmidt with two passes reduces column $c$ of a block $\mathbf{W}$
against the stored basis $\mathbf{Q}$ and the new columns $\mathbf{q}'_{c'}$, $c' < c$, twice, and
normalizes the result, writing a zero column when the result is zero. The recursion over the
columns is written as matrix identities: the coefficients against the earlier new columns are the
strictly upper triangular part of $\mathbf{Q}'^{\mathsf{H}}\mathbf{W}$. The result is an exact
extension `NLAlib.IsBasisExtension` of $\mathbf{Q}$ by $\mathbf{W}$ for an arbitrary basis
$\mathbf{Q}$; only the orthonormality clause of the contract uses the orthonormality of
$\mathbf{Q}$ on its support. Design: `docs/design/LowRank-BlockLanczos.md` §3.5.

## Main definitions

* `NLAlib.strictUpper`: the strictly upper triangular part of a square matrix.
* `NLAlib.colsBefore`: the columns before a given one, the others replaced by zero.

## Main results

* `NLAlib.blockTriangular_strictUpper`, `NLAlib.mul_strictUpper_col`: the strictly upper
  triangular part is upper triangular, and its product with a block uses the earlier columns.
* `NLAlib.col_colsBefore_of_lt`, `NLAlib.col_colsBefore_of_not_lt`,
  `NLAlib.mul_col_eq_of_blockTriangular`: the columns before a given one, and a column of the
  product with an upper triangular matrix.
* `NLAlib.col_sub_mul_sub_mul_strictUpper`,
  `NLAlib.col_sub_mul_conjTranspose_mul_sub_mul_strictUpper`: one column of a classical pass.
* `NLAlib.conjTranspose_mulVec_sub_mulVec_eq_zero`, `NLAlib.gramDefect_eq_zero_of_col_eq`: an
  exact pass against a partial isometry, and one more orthonormal column.
* `NLAlib.isBasisExtension_of_two_passes`: exact column-wise classical Gram–Schmidt with two
  passes and the zero guard is an exact extension of the basis.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m : Type*} {b : ℕ}

/-- The strictly upper triangular part of a square matrix $\mathbf{A}$: the entry $(i, j)$ is
$a_{ij}$ for $i < j$ and $0$ otherwise. -/
def strictUpper (A : Matrix (Fin b) (Fin b) 𝕜) : Matrix (Fin b) (Fin b) 𝕜 :=
  Matrix.of fun i j => if i < j then A i j else 0

/-- The columns of $\mathbf{Q}'$ before column $c$: column $c'$ is $\mathbf{q}'_{c'}$ for
$c' < c$ and zero otherwise. The zero columns change neither the column space nor the Gram defect
on the support. -/
def colsBefore (Q' : Matrix m (Fin b) 𝕜) (c : Fin b) : Matrix m (Fin b) 𝕜 :=
  Matrix.of fun i c' => if c' < c then Q' i c' else 0

/-- The strictly upper triangular part of a square matrix is upper triangular. -/
theorem blockTriangular_strictUpper (A : Matrix (Fin b) (Fin b) 𝕜) :
    (strictUpper A).BlockTriangular id := by
  intro i j hij
  have hji : ¬ i < j := not_lt.2 (le_of_lt hij)
  simp [strictUpper, hji]

/-- Column $c$ of the product of a block $\mathbf{Q}'$ with the strictly upper triangular part
$\mathbf{S}$ of a square matrix $\mathbf{A}$ combines the columns of $\mathbf{Q}'$ before $c$
only: $(\mathbf{Q}'\mathbf{S})_c = \mathbf{Q}'_{<c}\,\mathbf{a}_c$, where $\mathbf{Q}'_{<c}$ is
$\mathbf{Q}'$ with the columns $c' \ge c$ replaced by zero and $\mathbf{a}_c$ is column $c$ of
$\mathbf{A}$. -/
theorem mul_strictUpper_col (Q' : Matrix m (Fin b) 𝕜) (A : Matrix (Fin b) (Fin b) 𝕜)
    (c : Fin b) : (Q' * strictUpper A).col c = colsBefore Q' c *ᵥ A.col c := by
  funext i
  simp only [Matrix.col_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, strictUpper,
    colsBefore, Matrix.of_apply]
  refine Finset.sum_congr rfl fun c' _ => ?_
  by_cases h : c' < c <;> simp [h]

/-- Column $c'$ of $\mathbf{Q}'_{<c}$, the matrix $\mathbf{Q}'$ with the columns $c'' \ge c$
replaced by zero, is column $c'$ of $\mathbf{Q}'$ for $c' < c$. -/
theorem col_colsBefore_of_lt (Q' : Matrix m (Fin b) 𝕜) {c c' : Fin b} (h : c' < c) :
    (colsBefore Q' c).col c' = Q'.col c' := by
  funext i
  simp [colsBefore, Matrix.col_apply, h]

/-- Column $c'$ of $\mathbf{Q}'_{<c}$, the matrix $\mathbf{Q}'$ with the columns $c'' \ge c$
replaced by zero, is zero for $c' \ge c$. -/
theorem col_colsBefore_of_not_lt (Q' : Matrix m (Fin b) 𝕜) {c c' : Fin b} (h : ¬ c' < c) :
    (colsBefore Q' c).col c' = 0 := by
  funext i
  simp [colsBefore, Matrix.col_apply, h]

/-- Column $c$ of the product of a block $\mathbf{Q}'$ with an upper triangular matrix
$\mathbf{R}$ splits into the earlier columns and the diagonal term:
$(\mathbf{Q}'\mathbf{R})_c = \mathbf{Q}'_{<c}\,\mathbf{s}_c + r_{cc}\mathbf{q}'_c$, where
$\mathbf{Q}'_{<c}$ is $\mathbf{Q}'$ with the columns $c' \ge c$ replaced by zero and
$\mathbf{s}_c$ is column $c$ of the strictly upper triangular part of $\mathbf{R}$. -/
theorem mul_col_eq_of_blockTriangular (Q' : Matrix m (Fin b) 𝕜) {R : Matrix (Fin b) (Fin b) 𝕜}
    (hR : R.BlockTriangular id) (c : Fin b) :
    (Q' * R).col c = colsBefore Q' c *ᵥ (strictUpper R).col c + R c c • Q'.col c := by
  funext i
  simp only [Matrix.col_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, strictUpper,
    colsBefore, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hsingle : R c c * Q' i c = ∑ c', if c' = c then R c' c * Q' i c' else 0 := by simp
  rw [hsingle, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rcases lt_trichotomy c' c with h | rfl | h
  · simp [h, h.ne]
  · simp [mul_comm]
  · simp [hR h, h.ne', lt_asymm h]

/-- Column $c$ of one classical pass with given coefficients: for a block $\mathbf{A}$,
coefficients $\mathbf{H}$ and a square matrix $\mathbf{B}$ with strictly upper triangular part
$\operatorname{su}(\mathbf{B})$,
$(\mathbf{A} - \mathbf{Q}\mathbf{H} - \mathbf{Q}'\operatorname{su}(\mathbf{B}))_c =
\mathbf{a}_c - \mathbf{Q}\mathbf{h}_c - \mathbf{Q}'_{<c}\,\mathbf{b}_c$, where $\mathbf{Q}'_{<c}$
is $\mathbf{Q}'$ with the columns $c' \ge c$ replaced by zero. -/
theorem col_sub_mul_sub_mul_strictUpper {κ : Type*} [Fintype κ] (Q : Matrix m κ 𝕜)
    (A Q' : Matrix m (Fin b) 𝕜) (H : Matrix κ (Fin b) 𝕜) (B : Matrix (Fin b) (Fin b) 𝕜)
    (c : Fin b) : (A - Q * H - Q' * strictUpper B).col c =
      A.col c - Q *ᵥ H.col c - colsBefore Q' c *ᵥ B.col c := by
  rw [← mul_strictUpper_col]
  rfl

/-- Column $c$ of one exact classical pass is the projection of column $c$ of the input: for a
block $\mathbf{A}$ and $\mathbf{V}_c = [\mathbf{Q}, \mathbf{Q}'_{<c}]$, where $\mathbf{Q}'_{<c}$
is $\mathbf{Q}'$ with the columns $c' \ge c$ replaced by zero and $\operatorname{su}$ is the
strictly upper triangular part,
$(\mathbf{A} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{A} -
\mathbf{Q}'\operatorname{su}(\mathbf{Q}'^{\mathsf{H}}\mathbf{A}))_c =
\mathbf{a}_c - \mathbf{V}_c\mathbf{V}_c^{\mathsf{H}}\mathbf{a}_c$. -/
theorem col_sub_mul_conjTranspose_mul_sub_mul_strictUpper [Fintype m] {κ : Type*} [Fintype κ]
    (Q : Matrix m κ 𝕜) (A Q' : Matrix m (Fin b) 𝕜) (c : Fin b) :
    (A - Q * (Qᴴ * A) - Q' * strictUpper (Q'ᴴ * A)).col c =
      A.col c - Matrix.fromCols Q (colsBefore Q' c) *ᵥ
        ((Matrix.fromCols Q (colsBefore Q' c))ᴴ *ᵥ A.col c) := by
  have h2 : colsBefore Q' c *ᵥ (Q'ᴴ * A).col c =
      colsBefore Q' c *ᵥ ((colsBefore Q' c)ᴴ *ᵥ A.col c) := by
    funext i
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun c' _ => ?_
    by_cases h : c' < c <;>
      simp [colsBefore, h, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.col_apply]
  have h3 : Matrix.fromCols Q (colsBefore Q' c) *ᵥ
      ((Matrix.fromCols Q (colsBefore Q' c))ᴴ *ᵥ A.col c) =
      Q *ᵥ (Qᴴ * A).col c + colsBefore Q' c *ᵥ ((colsBefore Q' c)ᴴ *ᵥ A.col c) := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mulVec,
      Matrix.fromCols_mulVec_sumElim]
    rfl
  rw [col_sub_mul_sub_mul_strictUpper, h2, h3, sub_sub]

/-- One exact classical pass against a partial isometry leaves a vector orthogonal to it: if
the Gram defect on the support of $\mathbf{V}$ vanishes then
$\mathbf{V}^{\mathsf{H}}(\mathbf{x} - \mathbf{V}\mathbf{V}^{\mathsf{H}}\mathbf{x}) = \mathbf{0}$
for every $\mathbf{x}$. -/
theorem conjTranspose_mulVec_sub_mulVec_eq_zero [Fintype m] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {V : Matrix m ι 𝕜} (hV : gramDefect V = 0) (x : m → 𝕜) :
    Vᴴ *ᵥ (x - V *ᵥ (Vᴴ *ᵥ x)) = 0 := by
  have hP : Vᴴ * V * Vᴴ = Vᴴ := by
    have h := congrArg Matrix.conjTranspose (mul_conjTranspose_mul_self_of_gramDefect_eq_zero hV)
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc] at h
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP, sub_self]

/-- Replacing one column of a matrix with zero Gram defect on the support by a vector that is
zero or of norm one, and orthogonal to the columns, keeps the Gram defect zero. Let the Gram
defect on the support of $\mathbf{V}$ vanish and let $\mathbf{V}'$ have the columns of
$\mathbf{V}$ except column $j$, which is $\mathbf{q}$ with
$\mathbf{V}^{\mathsf{H}}\mathbf{q} = \mathbf{0}$ and $\mathbf{q} = \mathbf{0}$ or
$\mathbf{q}^{\mathsf{H}}\mathbf{q} = 1$. Then the Gram defect on the support of $\mathbf{V}'$
vanishes. -/
theorem gramDefect_eq_zero_of_col_eq [Fintype m] {ι : Type*} [DecidableEq ι]
    {V V' : Matrix m ι 𝕜} (hV : gramDefect V = 0) (j : ι)
    (hne : ∀ i, i ≠ j → V'.col i = V.col i) (horth : Vᴴ *ᵥ V'.col j = 0)
    (hn : V'.col j = 0 ∨ star (V'.col j) ⬝ᵥ V'.col j = 1) : gramDefect V' = 0 := by
  have hent : ∀ (A : Matrix m ι 𝕜) (i k : ι), (Aᴴ * A) i k = star (A.col i) ⬝ᵥ A.col k :=
    fun _ _ _ => rfl
  have key1 : ∀ i, i ≠ j → gramDefect V' i j = 0 := by
    intro i hi
    have h1 : (V'ᴴ * V') i j = (Vᴴ *ᵥ V'.col j) i := by
      rw [hent, hne i hi]
      rfl
    rw [gramDefect, Matrix.sub_apply, Matrix.diagonal_apply_ne _ hi, sub_zero, h1, horth]
    rfl
  have key2 : gramDefect V' j j = 0 := by
    rcases hn with h0 | h1
    · exact gramDefect_apply_of_col_eq_zero_right h0 j
    · have hne0 : V'.col j ≠ 0 := by
        intro h0
        rw [h0] at h1
        simp at h1
      rw [gramDefect, Matrix.sub_apply, Matrix.diagonal_apply_eq, colSupport_of_col_ne_zero hne0,
        hent, h1, sub_self]
  have key3 : ∀ i k, i ≠ j → k ≠ j → gramDefect V' i k = 0 := by
    intro i k hi hk
    have h0 : gramDefect V i k = 0 := by
      rw [hV]
      rfl
    have hs : colSupport V' i = colSupport V i := by
      unfold colSupport
      rw [hne i hi]
    rw [← h0]
    simp only [gramDefect, Matrix.sub_apply, Matrix.diagonal_apply, hent, hne i hi, hne k hk, hs]
  ext i k
  rw [Matrix.zero_apply]
  by_cases hk : k = j
  · by_cases hi : i = j
    · rw [hk, hi]
      exact key2
    · rw [hk]
      exact key1 i hi
  · by_cases hi : i = j
    · rw [← (isHermitian_gramDefect V').apply, hi, key1 k hk, star_zero]
    · exact key3 i k hi hk

/-- A vector scaled by the inverse of its norm is zero or has norm one. -/
private theorem normalized_eq_zero_or [Fintype m] (w : m → 𝕜) :
    ((‖WithLp.toLp 2 w‖⁻¹ : ℝ) : 𝕜) • w = 0 ∨
      star (((‖WithLp.toLp 2 w‖⁻¹ : ℝ) : 𝕜) • w) ⬝ᵥ (((‖WithLp.toLp 2 w‖⁻¹ : ℝ) : 𝕜) • w) = 1 := by
  by_cases hw : w = 0
  · exact Or.inl (by rw [hw, smul_zero])
  · right
    have hpos : 0 < ‖WithLp.toLp 2 w‖ :=
      norm_pos_iff.2 fun h => hw (by simpa using congrArg WithLp.ofLp h)
    have hα : star ((‖WithLp.toLp 2 w‖⁻¹ : ℝ) : 𝕜) = ((‖WithLp.toLp 2 w‖⁻¹ : ℝ) : 𝕜) :=
      RCLike.conj_ofReal _
    have hr : ‖WithLp.toLp 2 w‖⁻¹ * ‖WithLp.toLp 2 w‖⁻¹ * ‖WithLp.toLp 2 w‖ ^ 2 = 1 := by
      field_simp
    rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, hα, ← RCLike.ofReal_mul,
      ← RCLike.ofReal_mul, hr, RCLike.ofReal_one]

/-- A vector whose multiple by the inverse of its norm is zero has norm zero. -/
private theorem norm_eq_zero_of_normalized_eq_zero [Fintype m] {w : m → 𝕜}
    (h : ((‖WithLp.toLp 2 w‖⁻¹ : ℝ) : 𝕜) • w = 0) : ‖WithLp.toLp 2 w‖ = 0 := by
  rcases smul_eq_zero.1 h with h | h
  · exact inv_eq_zero.1 (RCLike.ofReal_eq_zero.1 h)
  · rw [h, WithLp.toLp_zero, norm_zero]

/-- A block whose columns are the normalized columns of `W₂` gives back `W₂` when its columns
are scaled by the norms. -/
private theorem eq_mul_diagonal_norm [Fintype m] {W₂ Q' : Matrix m (Fin b) 𝕜}
    (hQ' : ∀ c, Q'.col c = ((‖WithLp.toLp 2 (W₂.col c)‖⁻¹ : ℝ) : 𝕜) • W₂.col c) :
    W₂ = Q' * Matrix.diagonal fun c => ((‖WithLp.toLp 2 (W₂.col c)‖ : ℝ) : 𝕜) := by
  ext i c
  rw [Matrix.mul_diagonal]
  have h : Q' i c = ((‖WithLp.toLp 2 (W₂.col c)‖⁻¹ : ℝ) : 𝕜) * W₂ i c := congrFun (hQ' c) i
  by_cases h0 : W₂.col c = 0
  · rw [show W₂ i c = 0 from congrFun h0 i, h0]
    simp
  · have hpos : 0 < ‖WithLp.toLp 2 (W₂.col c)‖ :=
      norm_pos_iff.2 fun h => h0 (by simpa using congrArg WithLp.ofLp h)
    rw [h, mul_right_comm, ← RCLike.ofReal_mul, inv_mul_cancel₀ hpos.ne', RCLike.ofReal_one,
      one_mul]

/-- Row `j` of `Qᴴ * X` vanishes when column `j` of `Q` does. -/
private theorem conjTranspose_mul_row_eq_zero [Fintype m] {ι κ : Type*} {Q : Matrix m ι 𝕜}
    {j : ι} (h : Q.col j = 0) (X : Matrix m κ 𝕜) : (Qᴴ * X) j = 0 := by
  funext c
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, show ∀ i, Q i j = 0 from congrFun h]

/-- A zero column of the input of one exact classical pass gives a zero column of its output. -/
private theorem col_pass_eq_zero [Fintype m] {κ : Type*} [Fintype κ] (Q : Matrix m κ 𝕜)
    {A : Matrix m (Fin b) 𝕜} (Q' : Matrix m (Fin b) 𝕜) {c : Fin b} (h : A.col c = 0) :
    (A - Q * (Qᴴ * A) - Q' * strictUpper (Q'ᴴ * A)).col c = 0 := by
  have h1 : (Qᴴ * A).col c = 0 := by
    change Qᴴ *ᵥ A.col c = 0
    rw [h, Matrix.mulVec_zero]
  have h2 : (Q'ᴴ * A).col c = 0 := by
    change Q'ᴴ *ᵥ A.col c = 0
    rw [h, Matrix.mulVec_zero]
  rw [col_sub_mul_sub_mul_strictUpper, h, h1, h2, Matrix.mulVec_zero, Matrix.mulVec_zero,
    sub_zero, sub_zero]

/-- A product `colsBefore Q' c *ᵥ y` lies in a submodule containing the columns of `Q'` before
`c`. -/
private theorem colsBefore_mulVec_mem {S : Submodule 𝕜 (m → 𝕜)} {Q' : Matrix m (Fin b) 𝕜}
    {c : Fin b} (h : ∀ c' < c, Q'.col c' ∈ S) (y : Fin b → 𝕜) : colsBefore Q' c *ᵥ y ∈ S := by
  have hsum : colsBefore Q' c *ᵥ y = ∑ c', y c' • (colsBefore Q' c).col c' := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, Matrix.col_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hsum]
  refine Submodule.sum_mem _ fun c' _ => S.smul_mem _ ?_
  by_cases hc : c' < c
  · rw [col_colsBefore_of_lt Q' hc]
    exact h c' hc
  · rw [col_colsBefore_of_not_lt Q' hc]
    exact S.zero_mem

section TwoPasses

variable {n k : ℕ} {Q : Matrix (Fin n) (Fin k) 𝕜} {W Q' W₁ W₂ : Matrix (Fin n) (Fin b) 𝕜}
  {H₁ H₂ : Matrix (Fin k) (Fin b) 𝕜} {R₁ R₂ : Matrix (Fin b) (Fin b) 𝕜}

/-- The columns of the new block of two classical passes lie in every submodule that contains
the range of `Q` and the columns of `W`. -/
private theorem col_mem_of_two_passes (hR₁ : R₁ = strictUpper (Q'ᴴ * W))
    (hW₁ : W₁ = W - Q * H₁ - Q' * R₁) (hR₂ : R₂ = strictUpper (Q'ᴴ * W₁))
    (hW₂ : W₂ = W₁ - Q * H₂ - Q' * R₂)
    (hQ' : ∀ c, Q'.col c = ((‖WithLp.toLp 2 (W₂.col c)‖⁻¹ : ℝ) : 𝕜) • W₂.col c)
    {S : Submodule 𝕜 (Fin n → 𝕜)} (hS : ∀ x, Q *ᵥ x ∈ S) (hW : ∀ c, W.col c ∈ S) (c : Fin b) :
    Q'.col c ∈ S := by
  have key : ∀ (N : ℕ) (c : Fin b), (c : ℕ) = N → Q'.col c ∈ S := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro c hc
      have hprev : ∀ c' < c, Q'.col c' ∈ S := fun c' h =>
        ih c' (by rw [← hc]; exact Fin.lt_def.1 h) c' rfl
      have h1 : W₁.col c ∈ S := by
        rw [hW₁, hR₁, col_sub_mul_sub_mul_strictUpper]
        exact S.sub_mem (S.sub_mem (hW c) (hS _)) (colsBefore_mulVec_mem hprev _)
      have h2 : W₂.col c ∈ S := by
        rw [hW₂, hR₂, col_sub_mul_sub_mul_strictUpper]
        exact S.sub_mem (S.sub_mem h1 (hS _)) (colsBefore_mulVec_mem hprev _)
      rw [hQ' c]
      exact S.smul_mem _ h2
  exact key c c rfl

/-- The new block of two classical passes is a combination of the old basis and the input. -/
private theorem exists_eq_mul_add_mul_of_two_passes (hR₁ : R₁ = strictUpper (Q'ᴴ * W))
    (hW₁ : W₁ = W - Q * H₁ - Q' * R₁) (hR₂ : R₂ = strictUpper (Q'ᴴ * W₁))
    (hW₂ : W₂ = W₁ - Q * H₂ - Q' * R₂)
    (hQ' : ∀ c, Q'.col c = ((‖WithLp.toLp 2 (W₂.col c)‖⁻¹ : ℝ) : 𝕜) • W₂.col c) :
    ∃ (M : Matrix (Fin k) (Fin b) 𝕜) (T : Matrix (Fin b) (Fin b) 𝕜), Q' = Q * M + W * T := by
  have hle : LinearMap.range Q'.mulVecLin ≤ LinearMap.range (Matrix.fromCols Q W).mulVecLin := by
    rw [Matrix.range_mulVecLin Q']
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    refine col_mem_of_two_passes hR₁ hW₁ hR₂ hW₂ hQ' (fun x => ?_) (fun c => ?_) c
    · exact ⟨Sum.elim x 0, by
        rw [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_zero, add_zero]⟩
    · exact ⟨Sum.elim 0 (Pi.single c 1), by
        rw [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_zero, zero_add,
          Matrix.mulVec_single_one]⟩
  obtain ⟨C, hC⟩ := range_le_iff_exists_mul.1 hle
  refine ⟨C.toRows₁, C.toRows₂, ?_⟩
  rw [← Matrix.fromCols_mul_fromRows, Matrix.fromRows_toRows]
  exact hC

/-- The second exact pass and the normalization keep the nonzero columns orthonormal. -/
private theorem gramDefect_fromCols_eq_zero_of_two_passes (hH₂ : H₂ = Qᴴ * W₁)
    (hR₂ : R₂ = strictUpper (Q'ᴴ * W₁)) (hW₂ : W₂ = W₁ - Q * H₂ - Q' * R₂)
    (hQ' : ∀ c, Q'.col c = ((‖WithLp.toLp 2 (W₂.col c)‖⁻¹ : ℝ) : 𝕜) • W₂.col c)
    (hQ : gramDefect Q = 0) : gramDefect (Matrix.fromCols Q Q') = 0 := by
  have key : ∀ N, N ≤ b → ∀ X : Matrix (Fin n) (Fin b) 𝕜,
      (∀ c' : Fin b, (c' : ℕ) < N → X.col c' = Q'.col c') →
      (∀ c' : Fin b, N ≤ (c' : ℕ) → X.col c' = 0) → gramDefect (Matrix.fromCols Q X) = 0 := by
    intro N
    induction N with
    | zero =>
      intro _ X _ h0
      have hX : X = 0 := by
        ext i c'
        exact congrFun (h0 c' (Nat.zero_le _)) i
      have hg : gramDefect (0 : Matrix (Fin n) (Fin b) 𝕜) = 0 := by
        ext i j
        exact gramDefect_apply_of_col_eq_zero_right
          (Q := (0 : Matrix (Fin n) (Fin b) 𝕜)) (j := j) rfl i
      rw [hX, gramDefect_fromCols, hQ, hg, Matrix.mul_zero, Matrix.conjTranspose_zero,
        Matrix.zero_mul, Matrix.fromBlocks_zero]
    | succ N ih =>
      intro hN X h1 h0
      obtain ⟨c, hc⟩ : ∃ c : Fin b, (c : ℕ) = N := ⟨⟨N, hN⟩, rfl⟩
      have hV := ih (by omega) (colsBefore Q' c)
        (fun c' h => col_colsBefore_of_lt Q' (Fin.lt_def.2 (by rw [hc]; exact h)))
        (fun c' h => col_colsBefore_of_not_lt Q' fun hlt => by
          have := Fin.lt_def.1 hlt
          omega)
      have hXc : X.col c = Q'.col c := h1 c (by omega)
      have horth : (Matrix.fromCols Q (colsBefore Q' c))ᴴ *ᵥ Q'.col c = 0 := by
        rw [hQ' c, Matrix.mulVec_smul, hW₂, hR₂, hH₂,
          col_sub_mul_conjTranspose_mul_sub_mul_strictUpper,
          conjTranspose_mulVec_sub_mulVec_eq_zero hV, smul_zero]
      refine gramDefect_eq_zero_of_col_eq hV (Sum.inr c) ?_ ?_ ?_
      · rintro (i | c') hi
        · rfl
        · change X.col c' = (colsBefore Q' c).col c'
          have hne : c' ≠ c := fun h => hi (by rw [h])
          rcases lt_or_gt_of_ne hne with h | h
          · rw [col_colsBefore_of_lt Q' h]
            exact h1 c' (by have := Fin.lt_def.1 h; omega)
          · rw [col_colsBefore_of_not_lt Q' (not_lt.2 h.le)]
            exact h0 c' (by have := Fin.lt_def.1 h; omega)
      · change (Matrix.fromCols Q (colsBefore Q' c))ᴴ *ᵥ X.col c = 0
        rw [hXc]
        exact horth
      · change X.col c = 0 ∨ star (X.col c) ⬝ᵥ X.col c = 1
        rw [hXc, hQ' c]
        exact normalized_eq_zero_or _
  exact key b le_rfl Q' (fun _ _ => rfl) fun c' h => absurd c'.2 (not_lt.2 h)

end TwoPasses

/-- **Exact column-wise classical Gram–Schmidt with two passes extends a basis.** Let
$\mathbf{Q}$ be an arbitrary basis, $\mathbf{W}$ a block of $b$ columns, and write
$\operatorname{su}(\mathbf{A})$ for the strictly upper triangular part of $\mathbf{A}$. Let
$\mathbf{H}_1 = \mathbf{Q}^{\mathsf{H}}\mathbf{W}$,
$\mathbf{R}_1 = \operatorname{su}(\mathbf{Q}'^{\mathsf{H}}\mathbf{W})$,
$\mathbf{W}_1 = \mathbf{W} - \mathbf{Q}\mathbf{H}_1 - \mathbf{Q}'\mathbf{R}_1$ be the first pass,
$\mathbf{H}_2 = \mathbf{Q}^{\mathsf{H}}\mathbf{W}_1$,
$\mathbf{R}_2 = \operatorname{su}(\mathbf{Q}'^{\mathsf{H}}\mathbf{W}_1)$,
$\mathbf{W}_2 = \mathbf{W}_1 - \mathbf{Q}\mathbf{H}_2 - \mathbf{Q}'\mathbf{R}_2$ the second, and
let column $c$ of $\mathbf{Q}'$ be $\|\mathbf{w}\|^{-1}\mathbf{w}$ with $\mathbf{w}$ column $c$ of
$\mathbf{W}_2$ (the zero column when $\mathbf{w} = \mathbf{0}$). Then $\mathbf{Q}'$ with the
coefficients $\mathbf{H}_1 + \mathbf{H}_2$ and $\mathbf{R}_1 + \mathbf{R}_2 + \mathbf{D}$,
$\mathbf{D}$ the diagonal matrix of the norms of the columns of $\mathbf{W}_2$, is an exact
extension of $\mathbf{Q}$ by $\mathbf{W}$. No hypothesis on $\mathbf{Q}$: the orthonormality of
$\mathbf{Q}$ on its support is used only by the clause that preserves it. No printed source;
`docs/design/LowRank-BlockLanczos.md` §3.5.
Result: cgs2-basis-extension -/
theorem isBasisExtension_of_two_passes {n k : ℕ} {Q : Matrix (Fin n) (Fin k) 𝕜}
    {W Q' W₁ W₂ : Matrix (Fin n) (Fin b) 𝕜} {H₁ H₂ : Matrix (Fin k) (Fin b) 𝕜}
    {R₁ R₂ : Matrix (Fin b) (Fin b) 𝕜}
    (hH₁ : H₁ = Qᴴ * W) (hR₁ : R₁ = strictUpper (Q'ᴴ * W))
    (hW₁ : W₁ = W - Q * H₁ - Q' * R₁)
    (hH₂ : H₂ = Qᴴ * W₁) (hR₂ : R₂ = strictUpper (Q'ᴴ * W₁))
    (hW₂ : W₂ = W₁ - Q * H₂ - Q' * R₂)
    (hQ' : ∀ c, Q'.col c = ((‖WithLp.toLp 2 (W₂.col c)‖⁻¹ : ℝ) : 𝕜) • W₂.col c) :
    IsBasisExtension Q W Q' (H₁ + H₂)
      (R₁ + R₂ + Matrix.diagonal fun c => ((‖WithLp.toLp 2 (W₂.col c)‖ : ℝ) : 𝕜)) := by
  have hD := eq_mul_diagonal_norm hQ'
  have hW : W = W₂ + Q * H₂ + Q' * R₂ + Q * H₁ + Q' * R₁ := by
    rw [hW₂, hW₁]
    abel
  refine ⟨?_, ?_, exists_eq_mul_add_mul_of_two_passes hR₁ hW₁ hR₂ hW₂ hQ', fun c hc => ?_,
    fun j hj => ?_, fun c hc => ?_, gramDefect_fromCols_eq_zero_of_two_passes hH₂ hR₂ hW₂ hQ'⟩
  · rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, ← hD]
    conv_lhs => rw [hW]
    abel
  · rw [hR₁, hR₂]
    exact ((blockTriangular_strictUpper _).add (blockTriangular_strictUpper _)).add
      (Matrix.blockTriangular_diagonal _)
  · have h1 : W₁.col c = 0 := by
      rw [hW₁, hR₁, hH₁]
      exact col_pass_eq_zero Q Q' hc
    have h2 : W₂.col c = 0 := by
      rw [hW₂, hR₂, hH₂]
      exact col_pass_eq_zero Q Q' h1
    rw [hQ' c, h2, smul_zero]
  · change H₁ j + H₂ j = 0
    rw [hH₁, hH₂, conjTranspose_mul_row_eq_zero hj, conjTranspose_mul_row_eq_zero hj, add_zero]
  · have hn : ‖WithLp.toLp 2 (W₂.col c)‖ = 0 :=
      norm_eq_zero_of_normalized_eq_zero ((hQ' c).symm.trans hc)
    have hs : ∀ X : Matrix (Fin n) (Fin b) 𝕜, strictUpper (Q'ᴴ * X) c = 0 := fun X => by
      funext j
      simp [strictUpper, congrFun (conjTranspose_mul_row_eq_zero hc X) j]
    funext j
    rw [hR₁, hR₂, Matrix.add_apply, Matrix.add_apply, congrFun (hs W) j, congrFun (hs W₁) j,
      Matrix.diagonal_apply]
    simp [hn]

end NLAlib
