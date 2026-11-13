/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.Grade
public import NLAlib.Matrix.Factorizations.GramSchmidt
public import NLAlib.Matrix.Factorizations.Hessenberg

/-!
# Graded Krylov bases and the Lanczos basis

An orthonormal basis is graded by the Krylov spaces when its first $j + 1$ columns span
$\mathcal{K}_{j+1}(\mathbf{A}, \mathbf{b})$ for every $j$. The compression
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ to such a basis is upper Hessenberg, and tridiagonal
for Hermitian $\mathbf{A}$; it is always written out, never bundled. The canonical graded basis is
the Gram–Schmidt matrix of the Krylov matrix (the Arnoldi basis; for Hermitian $\mathbf{A}$ the
Lanczos basis). Its columns from the grade on are zero, so it is orthonormal exactly up to the
grade, while its range, the Arnoldi relation and its first coordinate need no hypothesis.

The three-term recurrence that computes this basis for Hermitian $\mathbf{A}$ is in
`NLAlib.Krylov.Processes.LanczosRecurrence`, the modified Gram–Schmidt Arnoldi process that
computes it for every $\mathbf{A}$ in `NLAlib.Krylov.Processes.ArnoldiRecurrence`; the corollary
that Lanczos yields the conjugate gradient iterate is in `NLAlib.Krylov.LinearSystems.CGLanczos`.

## Main definitions

* `NLAlib.IsGradedKrylovBasis`: an orthonormal basis graded by the Krylov spaces.
* `NLAlib.arnoldiMatrix`: the canonical one, `gramSchmidtQ (krylovMatrix A b q)`.

## Main results

* `NLAlib.HasOrthonormalCols.isGradedKrylovBasis_of_forall_col_mem`: the constructor from column
  membership.
* `NLAlib.IsGradedKrylovBasis.isUpperHessenberg`, `NLAlib.IsGradedKrylovBasis.isTridiagonal`.
* `NLAlib.IsGradedKrylovBasis.eq_arnoldiMatrix`: uniqueness under a positive diagonal.
* `NLAlib.HasOrthonormalCols.isGradedKrylovBasis_of_isUnreducedHessenberg`,
  `NLAlib.HasOrthonormalCols.eq_arnoldiMatrix_of_isUpperHessenberg`: the basis of an unreduced
  Hessenberg reduction and its normalization.
* `NLAlib.hasOrthonormalCols_arnoldiMatrix_iff`, `NLAlib.isGradedKrylovBasis_arnoldiMatrix`.
* `NLAlib.conjTranspose_arnoldiMatrix_mulVec_self`: $\mathbf{Q}^{\mathsf{H}}\mathbf{b} =
  \|\mathbf{b}\|\mathbf{e}_0$.
* `NLAlib.mul_arnoldiMatrix`: the Arnoldi relation, for every $q$.
* The columns: `NLAlib.arnoldiMatrix_col_eq_col_last`,
  `NLAlib.star_arnoldiMatrix_col_last_dotProduct_of_ne`,
  `NLAlib.exists_gramSchmidtR_smul_arnoldiMatrix_col_last`,
  `NLAlib.arnoldiMatrix_col_last_eq_zero_iff` (zero exactly from the grade on),
  `NLAlib.norm_arnoldiMatrix_col_last`.
* `NLAlib.arnoldiMatrix_col_succ`: the canonical Arnoldi step.
* `NLAlib.submatrix_conjTranspose_arnoldiMatrix_mul_mul_arnoldiMatrix_castSucc`: the rectangular
  Hessenberg matrix inside the square compression.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- `IsGradedKrylovBasis A b Q`: **$\mathbf{Q}$ is an orthonormal basis graded by the Krylov
spaces**: it has orthonormal columns and, for each $j < q$, its first $j + 1$ columns span
$\mathcal{K}_{j+1}(\mathbf{A}, \mathbf{b})$. Such a basis exists exactly for $q \le \nu$, and it
is unique up to unimodular column scalars; with the diagonal of
$\mathbf{Q}^{\mathsf{H}}\mathbf{K}_q(\mathbf{A}, \mathbf{b})$ real positive it is
`arnoldiMatrix A b q` (`IsGradedKrylovBasis.eq_arnoldiMatrix`). [Saad2003, §6.3]. -/
structure IsGradedKrylovBasis (A : Matrix n n 𝕜) (b : n → 𝕜) {q : ℕ}
    (Q : Matrix n (Fin q) 𝕜) : Prop where
  /-- The columns are orthonormal. -/
  hasOrthonormalCols : HasOrthonormalCols Q
  /-- The first $j + 1$ columns span the Krylov space of dimension $j + 1$. -/
  span_col_image_Iic : ∀ j : Fin q,
    Submodule.span 𝕜 (Q.col '' Set.Iic j) = krylovSpace A b ((j : ℕ) + 1)

variable {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ} {Q : Matrix n (Fin q) 𝕜}

/-- Constructor: orthonormal columns with column $j$ in $\mathcal{K}_{j+1}(\mathbf{A},
\mathbf{b})$ form a graded Krylov basis. -/
theorem HasOrthonormalCols.isGradedKrylovBasis_of_forall_col_mem (hQ : HasOrthonormalCols Q)
    (h : ∀ j : Fin q, Q.col j ∈ krylovSpace A b ((j : ℕ) + 1)) : IsGradedKrylovBasis A b Q := by
  refine ⟨hQ, fun j => ?_⟩
  have hle : Submodule.span 𝕜 (Q.col '' Set.Iic j) ≤ krylovSpace A b ((j : ℕ) + 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact krylovSpace_mono A b (Nat.succ_le_succ (Fin.le_def.mp hi)) (h i)
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  have hli : LinearIndependent 𝕜 Q.col := Matrix.mulVec_injective_iff.mp hQ.mulVec_injective
  have h2 : Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun x : Set.Iic j => Q.col x)) =
      (j : ℕ) + 1 := by
    rw [finrank_span_eq_card (b := fun x : Set.Iic j => Q.col x)
      (hli.comp _ Subtype.val_injective)]
    simp
  rw [finrank_krylovSpace, Set.image_eq_range, h2]
  exact min_le_left _ _

/-- A graded basis spans the Krylov space. -/
theorem IsGradedKrylovBasis.range_eq (hQ : IsGradedKrylovBasis A b Q) :
    LinearMap.range Q.mulVecLin = krylovSpace A b q := by
  cases q with
  | zero =>
    rw [krylovSpace_zero, Matrix.range_mulVecLin, Set.range_eq_empty, Submodule.span_empty]
  | succ q =>
    have h := hQ.span_col_image_Iic (Fin.last q)
    rw [Fin.val_last] at h
    rw [← h, Matrix.range_mulVecLin, ← Set.image_univ]
    congr 2
    exact (Set.eq_univ_of_forall fun i => Set.mem_Iic.mpr (Fin.le_last i)).symm

/-- A graded basis exists only up to the grade. -/
theorem IsGradedKrylovBasis.le_krylovGrade (hQ : IsGradedKrylovBasis A b Q) :
    q ≤ krylovGrade A b := by
  have h := hQ.hasOrthonormalCols.rank_eq
  rw [Matrix.rank, hQ.range_eq, finrank_krylovSpace, Fintype.card_fin] at h
  omega

/-- **The compression to a graded basis is upper Hessenberg.** [Saad2003, §6.3].
Result: arnoldi-hessenberg -/
theorem IsGradedKrylovBasis.isUpperHessenberg (hQ : IsGradedKrylovBasis A b Q) :
    IsUpperHessenberg (Qᴴ * A * Q) := by
  intro i j hij
  rw [conjTranspose_mul_mul_apply]
  have hj : Q.col j ∈ krylovSpace A b ((j : ℕ) + 1) := by
    rw [← hQ.span_col_image_Iic j]
    exact Submodule.subset_span ⟨j, Set.mem_Iic.mpr le_rfl, rfl⟩
  have hAj := mulVec_mem_krylovSpace_succ hj
  have hk : (j : ℕ) + 1 < q := lt_trans hij i.2
  rw [show (j : ℕ) + 1 + 1 = ((⟨(j : ℕ) + 1, hk⟩ : Fin q) : ℕ) + 1 from rfl,
    ← hQ.span_col_image_Iic] at hAj
  refine hQ.hasOrthonormalCols.star_col_dotProduct_eq_zero_of_mem_span ?_ hAj
  rw [Set.mem_Iic, Fin.le_def, not_le]
  exact hij

/-- **For Hermitian $\mathbf{A}$ the compression to a graded basis is tridiagonal**: the Lanczos
matrix $\mathbf{T} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$. [Saad2003, §6.6].
Result: lanczos-tridiagonal -/
theorem IsGradedKrylovBasis.isTridiagonal (hQ : IsGradedKrylovBasis A b Q)
    (hA : A.IsHermitian) : IsTridiagonal (Qᴴ * A * Q) :=
  hQ.isUpperHessenberg.isTridiagonal (Matrix.isHermitian_conjTranspose_mul_mul Q hA)

/-- The **canonical Krylov basis** (the Arnoldi basis; for Hermitian $\mathbf{A}$ the Lanczos
basis): $\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q)$ is the Gram–Schmidt matrix of
$\mathbf{K}_q(\mathbf{A}, \mathbf{b})$. Column $j$ is the same for every $q > j$; columns from
the grade on are zero, so it has orthonormal columns exactly for $q \le \nu$. -/
noncomputable def arnoldiMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) : Matrix n (Fin q) 𝕜 :=
  gramSchmidtQ (krylovMatrix A b q)

/-- The canonical basis $\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q)$ spans the Krylov space,
for every $q$. -/
theorem range_arnoldiMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    LinearMap.range (arnoldiMatrix A b q).mulVecLin = krylovSpace A b q :=
  range_gramSchmidtQ _

/-- The first $q$ columns of a longer canonical basis
$\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q')$ form the shorter one
$\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q)$. -/
theorem arnoldiMatrix_submatrix_castLE (A : Matrix n n 𝕜) (b : n → 𝕜) {q q' : ℕ}
    (h : q ≤ q') : (arnoldiMatrix A b q').submatrix id (Fin.castLE h) = arnoldiMatrix A b q := by
  rw [arnoldiMatrix, arnoldiMatrix, ← gramSchmidtQ_submatrix_castLE, krylovMatrix_submatrix_castLE]

/-- The canonical basis $\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q)$ has orthonormal columns
exactly up to the grade. -/
theorem hasOrthonormalCols_arnoldiMatrix_iff :
    HasOrthonormalCols (arnoldiMatrix A b q) ↔ q ≤ krylovGrade A b := by
  refine ⟨fun h => ?_, fun h => hasOrthonormalCols_gramSchmidtQ
    (krylovMatrix_mulVec_injective_iff.mpr h)⟩
  have h' := h.rank_eq
  rw [Matrix.rank, range_arnoldiMatrix, finrank_krylovSpace, Fintype.card_fin] at h'
  omega

/-- **The canonical basis is graded up to the grade**: for $q \le \nu$, the grade of
$\mathbf{b}$, $\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q)$ has orthonormal columns and,
for each $j < q$, its first $j + 1$ columns span $\mathcal{K}_{j+1}(\mathbf{A}, \mathbf{b})$.
[Saad2003, Proposition 6.4]; stated there for the vectors of the Arnoldi process before it stops,
which are these columns (`mgsArnoldiMatrix_eq_arnoldiMatrix`).
Result: arnoldi-basis -/
theorem isGradedKrylovBasis_arnoldiMatrix (h : q ≤ krylovGrade A b) :
    IsGradedKrylovBasis A b (arnoldiMatrix A b q) := by
  refine HasOrthonormalCols.isGradedKrylovBasis_of_forall_col_mem
    (hasOrthonormalCols_arnoldiMatrix_iff.mpr h)
    fun j => ?_
  have hj : (arnoldiMatrix A b q).col j ∈
      Submodule.span 𝕜 ((arnoldiMatrix A b q).col '' Set.Iic j) :=
    Submodule.subset_span ⟨j, Set.mem_Iic.mpr le_rfl, rfl⟩
  rw [arnoldiMatrix, span_gramSchmidtQ_col_image_Iic] at hj
  refine Submodule.span_le.mpr ?_ hj
  rintro _ ⟨i, hi, rfl⟩
  exact pow_mulVec_mem_krylovSpace A b (Nat.lt_succ_of_le (Fin.le_def.mp hi))

/-- **Uniqueness of the graded basis**: a graded basis whose matrix
$\mathbf{Q}^{\mathsf{H}}\mathbf{K}_q(\mathbf{A}, \mathbf{b})$ has positive diagonal (in the order
of $\Bbbk$, so real positive) is the canonical one: an orthonormal $\mathbf{Q}$ with $q$ columns
whose first $j + 1$ columns span $\mathcal{K}_{j+1}(\mathbf{A}, \mathbf{b})$ for each $j < q$ is
$\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q)$.
Result: arnoldi-basis -/
theorem IsGradedKrylovBasis.eq_arnoldiMatrix (hQ : IsGradedKrylovBasis A b Q)
    (hpos : ∀ j, 0 < (Qᴴ * krylovMatrix A b q) j j) : Q = arnoldiMatrix A b q := by
  have hK : Function.Injective (krylovMatrix A b q).mulVec :=
    krylovMatrix_mulVec_injective_iff.mpr hQ.le_krylovGrade
  have hQR : IsQR (krylovMatrix A b q) Q (Qᴴ * krylovMatrix A b q) := by
    refine ⟨?_, hQ.hasOrthonormalCols, fun i j hij => ?_⟩
    · rw [← Matrix.mul_assoc, ← hQ.hasOrthonormalCols.rangeProjector_eq]
      exact (rangeProjector_mul_eq_self_iff.mpr (hQ.range_eq.symm ▸ le_rfl)).symm
    · have hij' : j < i := hij
      rw [conjTranspose_mul_apply]
      have hj : (krylovMatrix A b q).col j ∈ krylovSpace A b ((j : ℕ) + 1) :=
        pow_mulVec_mem_krylovSpace A b (Nat.lt_succ_self _)
      rw [← hQ.span_col_image_Iic] at hj
      exact hQ.hasOrthonormalCols.star_col_dotProduct_eq_zero_of_mem_span
        (fun h => (not_le.mpr hij') (Set.mem_Iic.mp h)) hj
  exact (hQR.unique (isQR_gramSchmidt hK) hpos (gramSchmidtR_apply_self_pos hK)).1

section Hessenberg

variable {k : ℕ} {A Q H : Matrix (Fin (k + 1)) (Fin (k + 1)) 𝕜}

/-- The first column of the powers of a Hessenberg matrix advances by at most one row
at each step. -/
private theorem IsUpperHessenberg.pow_apply_zero_of_lt (hH : IsUpperHessenberg H) (p : ℕ)
    (i : Fin (k + 1)) (hi : p < i.val) : (H ^ p) i 0 = 0 := by
  induction p generalizing i with
  | zero => exact Matrix.one_apply_ne (fun h => by simp [h] at hi)
  | succ p ih =>
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : p < l.val
    · rw [ih l hl, mul_zero]
    · rw [hH i l (by omega), zero_mul]

/-- On that advancing boundary the entry is multiplied by the next subdiagonal. -/
private theorem IsUpperHessenberg.krylovMatrix_apply_succ (hH : IsUpperHessenberg H) (i : Fin k) :
    krylovMatrix H (Pi.single 0 1) (k + 1) i.succ i.succ =
      H i.succ i.castSucc * krylovMatrix H (Pi.single 0 1) (k + 1) i.castSucc i.castSucc := by
  simp only [krylovMatrix_apply, Matrix.mulVec_single_one, Fin.val_succ, Fin.val_castSucc]
  change (H ^ (i.val + 1)) i.succ 0 = H i.succ i.castSucc * (H ^ i.val) i.castSucc 0
  rw [pow_succ', Matrix.mul_apply]
  refine Finset.sum_eq_single i.castSucc (fun l _ hl => ?_) (by simp)
  by_cases hp : i.val < l.val
  · rw [hH.pow_apply_zero_of_lt _ _ hp, mul_zero]
  · have hne : l.val ≠ i.val := fun h => hl (Fin.ext h)
    rw [hH i.succ l (by simp only [Fin.val_succ]; omega), zero_mul]

private theorem HasOrthonormalCols.isQR_krylovMatrix_of_isUpperHessenberg
    (hQ : HasOrthonormalCols Q) (hH : IsUpperHessenberg (Qᴴ * A * Q)) :
    IsQR (krylovMatrix A (Q.col 0) (k + 1)) Q
      (krylovMatrix (Qᴴ * A * Q) (Pi.single 0 1) (k + 1)) := by
  refine ⟨?_, hQ, fun i j hij => ?_⟩
  · have h := krylovMatrix_mul_mulVec (Qᴴ * A) Q (Pi.single 0 1) (k + 1)
    rwa [← Matrix.mul_assoc Q, hQ.mul_conjTranspose_self, Matrix.one_mul,
      Matrix.mulVec_single_one] at h
  · simp only [krylovMatrix_apply, Matrix.mulVec_single_one]
    exact hH.pow_apply_zero_of_lt _ _ hij

/-- **Krylov spaces of an unreduced Hessenberg reduction.** The first $j+1$ columns of the
unitary factor $\mathbf{Q}$ span the Krylov space generated by its first column for every $j$.
[GolubVanLoan2013, §7.4.3].
Result: unreduced-hessenberg-krylov-basis -/
theorem HasOrthonormalCols.isGradedKrylovBasis_of_isUnreducedHessenberg (hQ : HasOrthonormalCols Q)
    (hH : IsUnreducedHessenberg (Qᴴ * A * Q)) :
    IsGradedKrylovBasis A (Q.col 0) Q := by
  have hQR := hQ.isQR_krylovMatrix_of_isUpperHessenberg hH.isUpperHessenberg
  have hd (j : Fin (k + 1)) : krylovMatrix (Qᴴ * A * Q) (Pi.single 0 1) (k + 1) j j ≠ 0 := by
    induction j using Fin.induction with
    | zero => simp [krylovMatrix_apply]
    | succ i ih =>
      rw [hH.isUpperHessenberg.krylovMatrix_apply_succ]
      exact mul_ne_zero (hH.subdiagonal_ne_zero _ _ rfl) ih
  apply hQ.isGradedKrylovBasis_of_forall_col_mem
  intro j
  have hj : Q.col j ∈ Submodule.span 𝕜 (Q.col '' Set.Iic j) :=
    Submodule.subset_span ⟨j, Set.mem_Iic.mpr le_rfl, rfl⟩
  rw [hQR.span_col_image_Iic (fun i _ => hd i)] at hj
  refine Submodule.span_le.mpr ?_ hj
  rintro _ ⟨i, hi, rfl⟩
  exact pow_mulVec_mem_krylovSpace A (Q.col 0) (Nat.lt_succ_of_le (Fin.le_def.mp hi))

/-- **Arnoldi basis of a Hessenberg reduction.** With positive real subdiagonal entries, the
unitary factor is exactly $\mathsf{arnoldiMatrix}(\mathbf{A},\mathbf{Q}_{:,0},k+1)$.
[GolubVanLoan2013, §7.4.3].
Result: unreduced-hessenberg-krylov-basis -/
theorem HasOrthonormalCols.eq_arnoldiMatrix_of_isUpperHessenberg (hQ : HasOrthonormalCols Q)
    (hH : IsUpperHessenberg (Qᴴ * A * Q))
    (hpos : ∀ i : Fin k, 0 < (Qᴴ * A * Q) i.succ i.castSucc) :
    Q = arnoldiMatrix A (Q.col 0) (k + 1) := by
  have hu := isUnreducedHessenberg_iff.mpr ⟨hH, fun i => (hpos i).ne'⟩
  apply (hQ.isGradedKrylovBasis_of_isUnreducedHessenberg hu).eq_arnoldiMatrix
  rw [(hQ.isQR_krylovMatrix_of_isUpperHessenberg hH).conjTranspose_mul_eq]
  intro j
  induction j using Fin.induction with
  | zero => simp [krylovMatrix_apply]
  | succ i ih =>
    rw [hH.krylovMatrix_apply_succ]
    exact mul_pos (hpos i) ih

end Hessenberg

/-- The canonical basis $\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q + 1)$ sees $\mathbf{b}$
in its first coordinate only:
$\mathbf{Q}^{\mathsf{H}}\mathbf{b} = \|\mathbf{b}\|\mathbf{e}_0$, for every $q$. -/
theorem conjTranspose_arnoldiMatrix_mulVec_self (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    (arnoldiMatrix A b (q + 1))ᴴ *ᵥ b = (‖WithLp.toLp 2 b‖ : 𝕜) • Pi.single 0 1 := by
  have hb : krylovMatrix A b (q + 1) *ᵥ Pi.single 0 1 = b := by
    rw [Matrix.mulVec_single_one]
    ext i
    simp
  have hR : (arnoldiMatrix A b (q + 1))ᴴ *ᵥ b =
      (gramSchmidtR (krylovMatrix A b (q + 1))).col 0 := by
    calc (arnoldiMatrix A b (q + 1))ᴴ *ᵥ b =
        (arnoldiMatrix A b (q + 1))ᴴ *ᵥ (krylovMatrix A b (q + 1) *ᵥ Pi.single 0 1) := by
          rw [hb]
      _ = _ := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
          rfl
  rw [hR]
  ext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
  · rw [Matrix.col_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, gramSchmidtR,
      conjTranspose_mul_apply, ← bot_eq_zero (α := Fin (q + 1)), gramSchmidtQ_col_bot]
    have hcol : (krylovMatrix A b (q + 1)).col ⊥ = b := by
      ext i
      simp [bot_eq_zero (α := Fin (q + 1))]
    rw [hcol, star_smul, smul_dotProduct, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq,
      smul_eq_mul, RCLike.star_def, map_inv₀, RCLike.conj_ofReal]
    rcases eq_or_ne ‖WithLp.toLp 2 b‖ 0 with h | h
    · simp [h]
    · push_cast
      field_simp
  · rw [Matrix.col_apply, Pi.smul_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero k), smul_zero]
    exact isUpperTriangular_gramSchmidtR _ (Fin.succ_pos k)

/-- **The Arnoldi relation**, for every $q$:
$\mathbf{A}\mathbf{Q}_q = \mathbf{Q}_{q+1}(\mathbf{Q}_{q+1}^{\mathsf{H}}\mathbf{A}\mathbf{Q}_q)$
for the canonical bases $\mathbf{Q}_j = \mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, j)$.
[Saad2003, §6.3]. It is (6.7) of [Saad2003, Proposition 6.5], there up to the step where the
process stops.
Result: arnoldi-relation -/
theorem mul_arnoldiMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    A * arnoldiMatrix A b q =
      arnoldiMatrix A b (q + 1) * ((arnoldiMatrix A b (q + 1))ᴴ * A * arnoldiMatrix A b q) := by
  rw [Matrix.mul_assoc _ A, ← Matrix.mul_assoc,
    show arnoldiMatrix A b (q + 1) * (arnoldiMatrix A b (q + 1))ᴴ =
      rangeProjector (krylovMatrix A b (q + 1)) from gramSchmidtQ_mul_conjTranspose _]
  refine (rangeProjector_mul_eq_self_iff.mpr ?_).symm
  rintro _ ⟨c, rfl⟩
  rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
  exact mulVec_mem_krylovSpace_succ (by
    rw [← range_arnoldiMatrix]
    exact ⟨c, rfl⟩)

/-! ### The columns of the canonical basis

Column $j$ of `arnoldiMatrix A b q` is the same for every $q > j$
(`arnoldiMatrix_col_eq_col_last`); every statement below is about
`(arnoldiMatrix A b (j + 1)).col (Fin.last j)`, written $\mathbf{q}_j$, with Gram–Schmidt
coefficient $r_j$ = `gramSchmidtR (krylovMatrix A b (j + 1)) (Fin.last j) (Fin.last j)`. There is
no separate name for the column. -/

section Columns

/-- Column $j$ of the canonical basis $\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q)$ does not
depend on the number of columns $q > j$. -/
theorem arnoldiMatrix_col_eq_col_last (A : Matrix n n 𝕜) (b : n → 𝕜) {q : ℕ} (j : Fin q) :
    (arnoldiMatrix A b q).col j = (arnoldiMatrix A b ((j : ℕ) + 1)).col (Fin.last j) := by
  rw [← arnoldiMatrix_submatrix_castLE A b (Nat.succ_le_of_lt j.2)]
  ext i
  simp only [Matrix.col_apply, Matrix.submatrix_apply, id_eq]
  congr 1

/-- Distinct canonical columns, the last columns of $\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b},
i + 1)$ and $\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, k + 1)$, are orthogonal (each is a unit
vector or zero): $\mathbf{q}_i^{\mathsf{H}}\mathbf{q}_k = 0$ for $i \ne k$. -/
theorem star_arnoldiMatrix_col_last_dotProduct_of_ne (A : Matrix n n 𝕜) (b : n → 𝕜) {i k : ℕ}
    (hik : i ≠ k) :
    star ((arnoldiMatrix A b (i + 1)).col (Fin.last i)) ⬝ᵥ
      (arnoldiMatrix A b (k + 1)).col (Fin.last k) = 0 := by
  have h := congrFun (congrFun (conjTranspose_gramSchmidtQ_mul_self
    (krylovMatrix A b (max i k + 1))) ⟨i, by omega⟩) ⟨k, by omega⟩
  rw [conjTranspose_mul_apply, ← arnoldiMatrix,
    arnoldiMatrix_col_eq_col_last A b (⟨i, by omega⟩ : Fin (max i k + 1)),
    arnoldiMatrix_col_eq_col_last A b (⟨k, by omega⟩ : Fin (max i k + 1)),
    Matrix.diagonal_apply_ne _ (fun h => hik (congrArg Fin.val h))] at h
  exact h

/-- The Gram–Schmidt coefficients of the Krylov matrix against the canonical columns of
$\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, i + 1)$:
$r_{ij} = \mathbf{q}_i^{\mathsf{H}}\mathbf{A}^j\mathbf{b}$. -/
theorem gramSchmidtR_krylovMatrix_apply (A : Matrix n n 𝕜) (b : n → 𝕜) {q : ℕ} (i j : Fin q) :
    gramSchmidtR (krylovMatrix A b q) i j =
      star ((arnoldiMatrix A b ((i : ℕ) + 1)).col (Fin.last i)) ⬝ᵥ (A ^ (j : ℕ) *ᵥ b) := by
  rw [gramSchmidtR, conjTranspose_mul_apply, ← arnoldiMatrix, arnoldiMatrix_col_eq_col_last]
  rfl

/-- Column $j$ of $\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, j + 1)$ lies in
$\mathcal{K}_{j+1}(\mathbf{A}, \mathbf{b})$. -/
theorem arnoldiMatrix_col_last_mem_krylovSpace (A : Matrix n n 𝕜) (b : n → 𝕜) (j : ℕ) :
    (arnoldiMatrix A b (j + 1)).col (Fin.last j) ∈ krylovSpace A b (j + 1) := by
  rw [← range_arnoldiMatrix A b (j + 1)]
  exact ⟨Pi.single (Fin.last j) 1, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one]⟩

/-- The Gram–Schmidt recursion for the canonical columns of
$\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, j + 1)$:
$r_j\mathbf{q}_j = \mathbf{A}^j\mathbf{b} - \mathbf{y}$ for some
$\mathbf{y} \in \mathcal{K}_j(\mathbf{A}, \mathbf{b})$. -/
theorem exists_gramSchmidtR_smul_arnoldiMatrix_col_last (A : Matrix n n 𝕜) (b : n → 𝕜) (j : ℕ) :
    ∃ y ∈ krylovSpace A b j,
      gramSchmidtR (krylovMatrix A b (j + 1)) (Fin.last j) (Fin.last j) •
        (arnoldiMatrix A b (j + 1)).col (Fin.last j) = A ^ j *ᵥ b - y := by
  have h := gramSchmidtR_apply_self_smul_col (krylovMatrix A b (j + 1)) (Fin.last j)
  have hc : (krylovMatrix A b (j + 1)).col (Fin.last j) = A ^ j *ᵥ b := by
    ext i
    rw [Matrix.col_apply, krylovMatrix_apply, Fin.val_last]
  rw [hc, ← arnoldiMatrix] at h
  refine ⟨_, Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_, h⟩
  rw [arnoldiMatrix_col_eq_col_last]
  have hk' := Finset.mem_Iio.mp hk
  rw [Fin.lt_def, Fin.val_last] at hk'
  exact krylovSpace_mono A b hk' (arnoldiMatrix_col_last_mem_krylovSpace A b k)

/-- Column $i$ of $\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, i + 1)$ is orthogonal to
$\mathcal{K}_j(\mathbf{A}, \mathbf{b})$ for $j \le i$. -/
theorem star_arnoldiMatrix_col_last_dotProduct_eq_zero_of_mem (A : Matrix n n 𝕜) (b : n → 𝕜)
    {i j : ℕ} (hij : j ≤ i) {x : n → 𝕜} (hx : x ∈ krylovSpace A b j) :
    star ((arnoldiMatrix A b (i + 1)).col (Fin.last i)) ⬝ᵥ x = 0 := by
  rw [← range_arnoldiMatrix A b j] at hx
  obtain ⟨c, rfl⟩ := hx
  have h0 : star ((arnoldiMatrix A b (i + 1)).col (Fin.last i)) ᵥ* arnoldiMatrix A b j = 0 := by
    funext k
    change star ((arnoldiMatrix A b (i + 1)).col (Fin.last i)) ⬝ᵥ (arnoldiMatrix A b j).col k = 0
    rw [arnoldiMatrix_col_eq_col_last A b k]
    exact star_arnoldiMatrix_col_last_dotProduct_of_ne A b (by omega)
  rw [Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec, h0, zero_dotProduct]

/-- The canonical compression is Hessenberg, entrywise, for the last columns of
$\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, i + 1)$ and $\mathsf{arnoldiMatrix}(\mathbf{A},
\mathbf{b}, j + 1)$: $\mathbf{q}_i^{\mathsf{H}}\mathbf{A}\mathbf{q}_j = 0$ for $j + 1 < i$, for
every $\mathbf{A}$. -/
theorem star_arnoldiMatrix_col_last_dotProduct_mulVec_of_lt (A : Matrix n n 𝕜) (b : n → 𝕜)
    {i j : ℕ} (h : j + 1 < i) :
    star ((arnoldiMatrix A b (i + 1)).col (Fin.last i)) ⬝ᵥ
      (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) = 0 :=
  star_arnoldiMatrix_col_last_dotProduct_eq_zero_of_mem A b (by omega : j + 1 + 1 ≤ i)
    (mulVec_mem_krylovSpace_succ (arnoldiMatrix_col_last_mem_krylovSpace A b j))

/-- The Gram–Schmidt coefficient vanishes exactly from the grade on: $r_j = 0$ iff
$\nu \le j$. -/
theorem gramSchmidtR_krylovMatrix_apply_last_eq_zero_iff {A : Matrix n n 𝕜} {b : n → 𝕜}
    {j : ℕ} :
    gramSchmidtR (krylovMatrix A b (j + 1)) (Fin.last j) (Fin.last j) = 0 ↔
      krylovGrade A b ≤ j := by
  obtain ⟨y, hy, hjy⟩ := exists_gramSchmidtR_smul_arnoldiMatrix_col_last A b j
  rw [krylovGrade_le_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, zero_smul, eq_comm, sub_eq_zero] at hjy
    exact hjy ▸ hy
  · exact (gramSchmidtR_krylovMatrix_apply A b (Fin.last j) (Fin.last j)).trans
      (star_arnoldiMatrix_col_last_dotProduct_eq_zero_of_mem A b le_rfl h)

/-- The canonical column vanishes exactly from the grade on: the last column of
$\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, j + 1)$, $\mathbf{q}_j$, is $\mathbf{0}$ iff
$\nu \le j$. -/
theorem arnoldiMatrix_col_last_eq_zero_iff {A : Matrix n n 𝕜} {b : n → 𝕜} {j : ℕ} :
    (arnoldiMatrix A b (j + 1)).col (Fin.last j) = 0 ↔ krylovGrade A b ≤ j := by
  rw [arnoldiMatrix, gramSchmidtQ_col_eq_zero_iff, gramSchmidtR_krylovMatrix_apply_last_eq_zero_iff]

/-- Below the grade the canonical column of $\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, j + 1)$
is a unit vector: $\|\mathbf{q}_j\| = 1$ for $j < \nu$. -/
theorem norm_arnoldiMatrix_col_last {A : Matrix n n 𝕜} {b : n → 𝕜} {j : ℕ}
    (h : j < krylovGrade A b) :
    ‖WithLp.toLp 2 ((arnoldiMatrix A b (j + 1)).col (Fin.last j))‖ = 1 := by
  have hr : gramSchmidtR (krylovMatrix A b (j + 1)) (Fin.last j) (Fin.last j) ≠ 0 := fun h0 =>
    absurd (gramSchmidtR_krylovMatrix_apply_last_eq_zero_iff.mp h0) (not_le.mpr h)
  have h1 := congrFun (congrFun (conjTranspose_gramSchmidtQ_mul_self
    (krylovMatrix A b (j + 1))) (Fin.last j)) (Fin.last j)
  rw [conjTranspose_mul_apply, Matrix.diagonal_apply_eq, if_neg hr,
    EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, ← RCLike.ofReal_one,
    RCLike.ofReal_inj] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h1

/-- **The canonical Arnoldi step**, for every $\mathbf{A}$ and $j$: with $\mathbf{q}_j$ column
$j$ of the canonical basis $\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, j + 2)$ and
$\mathbf{w} = (\mathbf{I} - \mathbf{P}_{\mathbf{K}_{j+1}})\mathbf{A}\mathbf{q}_j$, column $j + 1$ is
$\mathbf{w}/\|\mathbf{w}\|$ (zero when $\mathbf{w} = \mathbf{0}$, which happens exactly from the
grade on). [Saad2003, §6.3]. -/
theorem arnoldiMatrix_col_succ (A : Matrix n n 𝕜) (b : n → 𝕜) (j : ℕ) :
    (arnoldiMatrix A b (j + 2)).col (Fin.last (j + 1)) =
      (‖WithLp.toLp 2 ((1 - rangeProjector (krylovMatrix A b (j + 1))) *ᵥ
          (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)))‖⁻¹ : 𝕜) •
        ((1 - rangeProjector (krylovMatrix A b (j + 1))) *ᵥ
          (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j))) := by
  change (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)) = _
  -- $\mathbf{I} - \mathbf{P}$ kills the Krylov space
  have hK : ∀ y ∈ krylovSpace A b (j + 1),
      (1 - rangeProjector (krylovMatrix A b (j + 1))) *ᵥ y = 0 := fun y hy => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, rangeProjector_mulVec_eq_self_iff.mpr hy, sub_self]
  by_cases hj : krylovGrade A b ≤ j
  · have hw : (1 - rangeProjector (krylovMatrix A b (j + 1))) *ᵥ
        (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) = 0 := by
      rw [arnoldiMatrix_col_last_eq_zero_iff.mpr hj, Matrix.mulVec_zero, Matrix.mulVec_zero]
    rw [hw, smul_zero]
    exact arnoldiMatrix_col_last_eq_zero_iff.mpr (hj.trans (Nat.le_succ j))
  -- the coefficients $r_j > 0$ and $r_{j+1} \ge 0$ are real
  obtain ⟨ρ, hρ0, hρ⟩ := RCLike.nonneg_iff_exists_ofReal.mp
    (gramSchmidtR_apply_self_nonneg (krylovMatrix A b (j + 1)) (Fin.last j))
  obtain ⟨ρ', hρ'0, hρ'⟩ := RCLike.nonneg_iff_exists_ofReal.mp
    (gramSchmidtR_apply_self_nonneg (krylovMatrix A b (j + 1 + 1)) (Fin.last (j + 1)))
  have hρne : ρ ≠ 0 := fun h0 => hj (gramSchmidtR_krylovMatrix_apply_last_eq_zero_iff.mp
    (by rw [← hρ, h0, RCLike.ofReal_zero]))
  obtain ⟨y, hy, hjy⟩ := exists_gramSchmidtR_smul_arnoldiMatrix_col_last A b j
  obtain ⟨y', hy', hjy'⟩ := exists_gramSchmidtR_smul_arnoldiMatrix_col_last A b (j + 1)
  rw [← hρ] at hjy
  rw [← hρ'] at hjy'
  -- $\mathbf{q}_{j+1}$ is orthogonal to $\mathcal{K}_{j+1}$
  have hQq : (arnoldiMatrix A b (j + 1))ᴴ *ᵥ
      (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)) = 0 := by
    funext i
    change star ((arnoldiMatrix A b (j + 1)).col i) ⬝ᵥ
      (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)) = 0
    rw [arnoldiMatrix_col_eq_col_last A b i]
    exact star_arnoldiMatrix_col_last_dotProduct_of_ne A b (by omega)
  have h1 : (1 - rangeProjector (krylovMatrix A b (j + 1))) *ᵥ
      (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)) =
      (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← gramSchmidtQ_mul_conjTranspose, ← arnoldiMatrix,
      ← Matrix.mulVec_mulVec, hQq, Matrix.mulVec_zero, sub_zero]
  -- $r_j \mathbf{w} = (\mathbf{I} - \mathbf{P})\mathbf{A}^{j+1}\mathbf{b}
  -- = r_{j+1}\mathbf{q}_{j+1}$
  have hu : (ρ : 𝕜) • ((1 - rangeProjector (krylovMatrix A b (j + 1))) *ᵥ
      (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j))) =
      (ρ' : 𝕜) • (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)) := by
    have hpow : A ^ (j + 1) *ᵥ b =
        (ρ' : 𝕜) • (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)) + y' := by
      rw [hjy', sub_add_cancel]
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, hjy, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
      ← pow_succ', Matrix.mulVec_sub, hK _ (mulVec_mem_krylovSpace_succ hy), sub_zero, hpow,
      Matrix.mulVec_add, hK _ hy', add_zero, Matrix.mulVec_smul, h1]
  have hw' : (1 - rangeProjector (krylovMatrix A b (j + 1))) *ᵥ
      (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) =
      ((ρ' / ρ : ℝ) : 𝕜) • (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)) := by
    rw [RCLike.ofReal_div, div_eq_inv_mul, ← smul_smul, ← hu, smul_smul,
      inv_mul_cancel₀ (RCLike.ofReal_ne_zero.mpr hρne), one_smul]
  rw [hw']
  by_cases hj' : krylovGrade A b ≤ j + 1
  · rw [arnoldiMatrix_col_last_eq_zero_iff.mpr hj', smul_zero, smul_zero]
  have hρ'ne : ρ' ≠ 0 := fun h0 => hj' (gramSchmidtR_krylovMatrix_apply_last_eq_zero_iff.mp
    (by rw [← hρ', h0, RCLike.ofReal_zero]))
  have hc : 0 < ρ' / ρ := div_pos (hρ'0.lt_of_ne' hρ'ne) (hρ0.lt_of_ne' hρne)
  rw [WithLp.toLp_smul, norm_smul, norm_arnoldiMatrix_col_last (not_le.mp hj'), mul_one,
    RCLike.norm_ofReal, abs_of_pos hc, smul_smul, ← RCLike.ofReal_inv, ← RCLike.ofReal_mul,
    inv_mul_cancel₀ hc.ne', RCLike.ofReal_one, one_smul]

/-- The rectangular Hessenberg matrix $\underline{\mathbf{H}}_q =
\mathbf{Q}_{q+1}^{\mathsf{H}}\mathbf{A}\mathbf{Q}_q$, with $\mathbf{Q}_m =
\mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, m)$, is the first $q$ columns of the square
compression $\mathbf{Q}_{q+1}^{\mathsf{H}}\mathbf{A}\mathbf{Q}_{q+1}$, so the Lanczos tridiagonal
matrix of size $q + 1$ gives it for Hermitian $\mathbf{A}$. -/
theorem submatrix_conjTranspose_arnoldiMatrix_mul_mul_arnoldiMatrix_castSucc
    (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    ((arnoldiMatrix A b (q + 1))ᴴ * A * arnoldiMatrix A b (q + 1)).submatrix id Fin.castSucc =
      (arnoldiMatrix A b (q + 1))ᴴ * A * arnoldiMatrix A b q := by
  rw [← arnoldiMatrix_submatrix_castLE A b (Nat.le_succ q)]
  ext i j
  rfl

end Columns

end NLAlib
