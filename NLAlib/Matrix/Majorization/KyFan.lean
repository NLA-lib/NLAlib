/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Positivity.Core
public import NLAlib.Matrix.Majorization.Basic
public import NLAlib.Matrix.Spectral.Dilation
public import NLAlib.Matrix.Spectral.Interlacing
public import NLAlib.Matrix.Spectral.SVD
public import NLAlib.Matrix.Spectral.Weyl

/-!
# Ky Fan's maximum principles and the Ky Fan norms

The sum of the $k$ largest eigenvalues of a Hermitian matrix is the largest trace of a
compression to $k$ orthonormal directions, and the sum of the $k$ largest singular values of a
matrix is the largest modulus of $\operatorname{tr}(\mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{V})$
over pairs of $k$ orthonormal directions. Both partial sums are therefore subadditive in the
matrix.

The singular value partial sum is the Ky Fan $k$-norm
$\|\mathbf{A}\|_{(k)} = \sum_{i < k} \sigma_i(\mathbf{A})$, `NLAlib.kyFanNorm`. Eigenvalue partial
sums $\sum_{i < k} \lambda_i(\mathbf{A})$ are written with `Finset.range` and have no name.

## Main definitions

* `NLAlib.kyFanNorm`: the sum of the $k$ largest singular values.

## Main results

* `Matrix.IsHermitian.re_trace_conjTranspose_mul_mul_le_sum_eigenvalue`: Ky Fan's maximum
  principle for eigenvalues, and
  `Matrix.IsHermitian.exists_re_trace_conjTranspose_mul_mul_eq_sum_eigenvalue`: attainment.
* `Matrix.IsHermitian.sum_range_eigenvalue_add_le`: subadditivity of eigenvalue partial sums.
* `Matrix.PosSemidef.sq_max_re_trace_sub_sum_Ico_eigenvalue_le`,
  `Matrix.PosSemidef.rank_le_of_sum_Ico_eigenvalue_eq_zero`: the trace above an eigenvalue tail.
* `NLAlib.norm_trace_conjTranspose_mul_mul_le_kyFanNorm`,
  `NLAlib.re_trace_conjTranspose_mul_mul_le_kyFanNorm`: the principle for singular values.
* `NLAlib.kyFanNorm_add_le`: the triangle inequality of the Ky Fan norms.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-! ### Eigenvalues -/

/-- **Ky Fan's maximum principle.** For Hermitian $\mathbf{A}$ and $\mathbf{Q}$ with orthonormal
columns indexed by $p$, the trace of the compression is at most the sum of the $\lvert p \rvert$
largest eigenvalues:
$$\operatorname{Re} \operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})
  \le \sum_{i < \lvert p \rvert} \lambda_i(\mathbf{A}) \,.$$
[HornJohnson2013, Corollary 4.3.39]; stated there for the smallest eigenvalues and increasing
order.
Result: ky-fan-maximum-principle -/
theorem _root_.Matrix.IsHermitian.re_trace_conjTranspose_mul_mul_le_sum_eigenvalue
    [DecidableEq p] {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n p 𝕜}
    (hQ : HasOrthonormalCols Q) :
    RCLike.re (Qᴴ * A * Q).trace ≤ ∑ i ∈ Finset.range (Fintype.card p), eigenvalue A i := by
  rw [(Matrix.isHermitian_conjTranspose_mul_mul Q hA).re_trace_eq_sum_range_eigenvalue]
  exact Finset.sum_le_sum fun i hi =>
    hA.eigenvalue_conjTranspose_mul_mul_le hQ (Finset.mem_range.mp hi)

/-- **Ky Fan's maximum principle, equality case.** The maximum is attained by the leading
eigenvectors: for Hermitian $\mathbf{A}$ and $k \le \lvert n \rvert$ there is $\mathbf{Q}$ with
$k$ orthonormal columns and
$\operatorname{Re} \operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})
= \sum_{i < k} \lambda_i(\mathbf{A})$.
Result: ky-fan-maximum-principle -/
theorem _root_.Matrix.IsHermitian.exists_re_trace_conjTranspose_mul_mul_eq_sum_eigenvalue
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ} (hk : k ≤ Fintype.card n) :
    ∃ Q : Matrix n (Fin k) 𝕜, HasOrthonormalCols Q ∧
      RCLike.re (Qᴴ * A * Q).trace = ∑ i ∈ Finset.range k, eigenvalue A i := by
  classical
  obtain ⟨U, hU, hAU⟩ := hA.exists_mul_eq_mul_diagonal
  refine ⟨U.submatrix id (Fin.castLE hk),
    hU.submatrix (Equiv.refl n) (Fin.castLE_injective hk), ?_⟩
  rw [conjTranspose_submatrix_mul_mul_submatrix, Matrix.mul_assoc, hAU,
    hU.conjTranspose_mul_cancel_left, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hk),
    Matrix.trace_diagonal, ← Fin.sum_univ_eq_sum_range (fun i => eigenvalue A i) k, map_sum]
  exact Finset.sum_congr rfl fun i _ => RCLike.ofReal_re _

/-- **Ky Fan's minimum principle.** The trace of a compression of a Hermitian $\mathbf{A}$ to
$\lvert p \rvert$ orthonormal directions is at least the sum of the $\lvert p \rvert$ smallest
eigenvalues: with $\lvert p \rvert + d = \lvert n \rvert$,
$$\sum_{d \le i < \lvert n \rvert} \lambda_i(\mathbf{A})
  \le \operatorname{Re} \operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}) \,.$$
[HornJohnson2013, Corollary 4.3.39]. -/
theorem _root_.Matrix.IsHermitian.sum_Ico_eigenvalue_le_re_trace_conjTranspose_mul_mul
    [DecidableEq p] {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Q : Matrix n p 𝕜}
    (hQ : HasOrthonormalCols Q) {d : ℕ} (hd : Fintype.card p + d = Fintype.card n) :
    ∑ i ∈ Finset.Ico d (Fintype.card n), eigenvalue A i ≤ RCLike.re (Qᴴ * A * Q).trace := by
  rw [(Matrix.isHermitian_conjTranspose_mul_mul Q hA).re_trace_eq_sum_range_eigenvalue,
    Finset.sum_Ico_eq_sum_range, show Fintype.card n - d = Fintype.card p by omega]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [add_comm]
  exact hA.eigenvalue_le_eigenvalue_conjTranspose_mul_mul hQ (Finset.mem_range.mp hi) hd

/-- Eigenvalue partial sums stop growing at the size of the matrix:
$\sum_{i < \min(k, \lvert n \rvert)} \lambda_i(\mathbf{A}) = \sum_{i < k} \lambda_i(\mathbf{A})$.
It reduces a statement about the $k$ leading eigenvalues to the case $k \le \lvert n \rvert$. -/
theorem sum_range_min_card_eigenvalue (A : Matrix n n 𝕜) (k : ℕ) :
    ∑ i ∈ Finset.range (min k (Fintype.card n)), eigenvalue A i =
      ∑ i ∈ Finset.range k, eigenvalue A i := by
  refine Finset.sum_subset (Finset.range_mono (min_le_left _ _)) fun i hik hi => ?_
  rw [Finset.mem_range] at hik hi
  exact eigenvalue_of_card_le A (by omega)

/-- **Subadditivity of eigenvalue partial sums.** For Hermitian $\mathbf{A}$ and $\mathbf{B}$ and
every $k$,
$$\sum_{i < k} \lambda_i(\mathbf{A} + \mathbf{B})
  \le \sum_{i < k} \lambda_i(\mathbf{A}) + \sum_{i < k} \lambda_i(\mathbf{B}) \,.$$
[HornJohnson2013, Corollary 4.3.39 and Theorem 4.3.47].
Result: ky-fan-eigenvalue-sums -/
theorem _root_.Matrix.IsHermitian.sum_range_eigenvalue_add_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : ℕ) :
    ∑ i ∈ Finset.range k, eigenvalue (A + B) i ≤
      ∑ i ∈ Finset.range k, eigenvalue A i + ∑ i ∈ Finset.range k, eigenvalue B i := by
  rw [← sum_range_min_card_eigenvalue (A + B), ← sum_range_min_card_eigenvalue A,
    ← sum_range_min_card_eigenvalue B]
  obtain ⟨Q, hQ, hQe⟩ := (hA.add hB).exists_re_trace_conjTranspose_mul_mul_eq_sum_eigenvalue
    (min_le_right k (Fintype.card n))
  have h1 := hA.re_trace_conjTranspose_mul_mul_le_sum_eigenvalue hQ
  have h2 := hB.re_trace_conjTranspose_mul_mul_le_sum_eigenvalue hQ
  rw [Fintype.card_fin] at h1 h2
  rw [← hQe, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, map_add]
  exact add_le_add h1 h2

/-- **Ky Fan's majorization for sums.** The eigenvalues of $\mathbf{A} + \mathbf{B}$ are
majorized by the sums of the sorted eigenvalues of $\mathbf{A}$ and $\mathbf{B}$: for Hermitian
$\mathbf{A}$, $\mathbf{B}$, the vector
$(\lambda_i(\mathbf{A} + \mathbf{B}))_{i < \lvert n \rvert}$ is majorized by
$(\lambda_i(\mathbf{A}) + \lambda_i(\mathbf{B}))_{i < \lvert n \rvert}$.
[HornJohnson2013, Theorem 4.3.47].
Result: ky-fan-eigenvalue-sums -/
theorem _root_.Matrix.IsHermitian.majorized_eigenvalue_add {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    Majorized (fun i : Fin (Fintype.card n) => eigenvalue (A + B) i)
      (fun i : Fin (Fintype.card n) => eigenvalue A i + eigenvalue B i) := by
  refine ⟨?_, ?_⟩
  · refine (weaklyMajorized_fin_iff_sum_range_le (f := eigenvalue (A + B))
      (g := fun i => eigenvalue A i + eigenvalue B i) ?_ ?_).mpr fun k _ => ?_
    · exact fun i _ j hj hij => (hA.add hB).eigenvalue_le_eigenvalue hij hj
    · exact fun i _ j hj hij =>
        add_le_add (hA.eigenvalue_le_eigenvalue hij hj) (hB.eigenvalue_le_eigenvalue hij hj)
    · rw [Finset.sum_add_distrib]
      exact Matrix.IsHermitian.sum_range_eigenvalue_add_le hA hB k
  · rw [Fin.sum_univ_eq_sum_range (fun i => eigenvalue (A + B) i),
      Fin.sum_univ_eq_sum_range (fun i => eigenvalue A i + eigenvalue B i),
      Finset.sum_add_distrib, ← (hA.add hB).re_trace_eq_sum_range_eigenvalue,
      ← hA.re_trace_eq_sum_range_eigenvalue, ← hB.re_trace_eq_sum_range_eigenvalue,
      Matrix.trace_add, map_add]

/-! ### The trace tail -/

open scoped ComplexOrder MatrixOrder in
/-- **The trace above the eigenvalue tail is paid for by the Frobenius norm.** For positive
semidefinite $\mathbf{R}$ with $\mathbf{R} \preceq \mathbf{A}$, and
$\tau = \sum_{r \le i < \lvert n \rvert} \lambda_i(\mathbf{A})$ the sum of the eigenvalues of
$\mathbf{A}$ from index $r$ on (the optimal trace error of a rank-$r$ approximation of
$\mathbf{A}$),
$$\max(\operatorname{tr} \mathbf{R} - \tau, 0)^2 \le r \operatorname{tr}(\mathbf{R}^2) \,,$$
traces through their real parts: by monotonicity of the eigenvalues,
$\operatorname{tr} \mathbf{R} - \tau$ is at most the sum of the $r$ largest eigenvalues of
$\mathbf{R}$, and the Cauchy–Schwarz inequality bounds that sum. This is the step that turns the
expected trace decrease of randomly pivoted Cholesky into its error bound.
[ChenEtAl2025, proof of Theorem 3.1]. -/
theorem _root_.Matrix.PosSemidef.sq_max_re_trace_sub_sum_Ico_eigenvalue_le {A R : Matrix n n 𝕜}
    (hR : R.PosSemidef) (hRA : R ≤ A) (r : ℕ) :
    max (RCLike.re R.trace - ∑ i ∈ Finset.Ico r (Fintype.card n), eigenvalue A i) 0 ^ 2 ≤
      r * RCLike.re (R * R).trace := by
  classical
  set N := Fintype.card n
  set S := (Finset.range N).filter (· < r) with hS
  have hd : ∀ i, 0 ≤ eigenvalue R i := hR.eigenvalue_nonneg
  have hT : (Finset.range N).filter (fun i => ¬ i < r) = Finset.Ico r N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have htr : RCLike.re R.trace =
      ∑ i ∈ S, eigenvalue R i + ∑ i ∈ Finset.Ico r N, eigenvalue R i := by
    rw [hR.isHermitian.re_trace_eq_sum_range_eigenvalue, ← hT,
      Finset.sum_filter_add_sum_filter_not]
  have htail : ∑ i ∈ Finset.Ico r N, eigenvalue R i ≤ ∑ i ∈ Finset.Ico r N, eigenvalue A i :=
    Finset.sum_le_sum fun i _ => eigenvalue_le_eigenvalue_of_le hRA hR.isHermitian i
  have hhead : 0 ≤ ∑ i ∈ S, eigenvalue R i := Finset.sum_nonneg fun i _ => hd i
  have hmax : max (RCLike.re R.trace - ∑ i ∈ Finset.Ico r N, eigenvalue A i) 0 ≤
      ∑ i ∈ S, eigenvalue R i := max_le (by linarith) hhead
  have hcard : (S.card : ℝ) ≤ r := by
    have : S ⊆ Finset.range r := fun i hi => Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    exact_mod_cast (Finset.card_le_card this).trans_eq (Finset.card_range r)
  have hsq : RCLike.re (R * R).trace = ∑ i ∈ Finset.range N, eigenvalue R i ^ 2 := by
    rw [← pow_two, hR.isHermitian.re_trace_pow_eq_sum_range_eigenvalue_pow]
  calc max (RCLike.re R.trace - ∑ i ∈ Finset.Ico r N, eigenvalue A i) 0 ^ 2
      ≤ (∑ i ∈ S, eigenvalue R i) ^ 2 := pow_le_pow_left₀ (le_max_right _ _) hmax 2
    _ ≤ S.card * ∑ i ∈ S, eigenvalue R i ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ r * ∑ i ∈ Finset.range N, eigenvalue R i ^ 2 :=
        mul_le_mul hcard (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ => sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _) r.cast_nonneg
    _ = r * RCLike.re (R * R).trace := by rw [hsq]

open scoped ComplexOrder in
/-- A positive semidefinite matrix whose eigenvalues from index $r$ on sum to zero has rank at
most $r$: if $\sum_{r \le i < \lvert n \rvert} \lambda_i(\mathbf{A}) = 0$ then
$\operatorname{rank} \mathbf{A} \le r$. This is the exact-rank case of the trace-tail bound.
[ChenEtAl2025, Theorem 3.1, exact-rank case]. -/
theorem _root_.Matrix.PosSemidef.rank_le_of_sum_Ico_eigenvalue_eq_zero {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {r : ℕ}
    (h : ∑ i ∈ Finset.Ico r (Fintype.card n), eigenvalue A i = 0) : A.rank ≤ r := by
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => hA.eigenvalue_nonneg i] at h
  rw [hA.isHermitian.rank_eq_card_eigenvalue_ne_zero]
  refine (Finset.card_le_card fun i hi => ?_).trans_eq (Finset.card_range r)
  rw [Finset.mem_filter, Finset.mem_range] at hi
  rw [Finset.mem_range]
  by_contra hir
  exact hi.2 (h i (Finset.mem_Ico.mpr ⟨not_lt.mp hir, hi.1⟩))

/-! ### The Ky Fan norms -/

/-- The **Ky Fan $k$-norm**: the sum of the $k$ largest singular values,
$\|\mathbf{A}\|_{(k)} = \sum_{i < k} \sigma_i(\mathbf{A})$. The Ky Fan $1$-norm is the spectral
norm, and the Ky Fan $k$-norm for $k$ at least the smaller dimension is the nuclear norm.
[HornJohnson2013, §7.4.8]. -/
noncomputable def kyFanNorm (k : ℕ) (A : Matrix m n 𝕜) : ℝ :=
  ∑ i ∈ Finset.range k, singularValues A i

/-- The Ky Fan $k$-norm is the sum of the first $k$ singular values:
$\|\mathbf{A}\|_{(k)} = \sum_{i < k} \sigma_i(\mathbf{A})$. -/
theorem kyFanNorm_eq_sum_range (k : ℕ) (A : Matrix m n 𝕜) :
    kyFanNorm k A = ∑ i ∈ Finset.range k, singularValues A i :=
  rfl

/-- Ky Fan norms are nonnegative: $\|\mathbf{A}\|_{(k)} \ge 0$. -/
theorem kyFanNorm_nonneg (k : ℕ) (A : Matrix m n 𝕜) : 0 ≤ kyFanNorm k A := by
  exact Finset.sum_nonneg fun i _ => singularValues_nonneg A i

/-- The Ky Fan $0$-norm vanishes: $\|\mathbf{A}\|_{(0)} = 0$. -/
@[simp]
theorem kyFanNorm_zero_left (A : Matrix m n 𝕜) : kyFanNorm 0 A = 0 := by
  rw [kyFanNorm, Finset.range_zero, Finset.sum_empty]

/-- The Ky Fan $1$-norm is the spectral norm: $\|\mathbf{A}\|_{(1)} = \|\mathbf{A}\|_2$. -/
@[simp]
theorem kyFanNorm_one (A : Matrix m n 𝕜) : kyFanNorm 1 A = specNorm A := by
  rw [kyFanNorm, Finset.sum_range_one, singularValues_zero_eq_specNorm]

/-- Ky Fan norms increase with $k$: $\|\mathbf{A}\|_{(k)} \le \|\mathbf{A}\|_{(l)}$ for
$k \le l$. -/
@[gcongr]
theorem kyFanNorm_mono_left (A : Matrix m n 𝕜) {k l : ℕ} (h : k ≤ l) :
    kyFanNorm k A ≤ kyFanNorm l A := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun i _ _ =>
    singularValues_nonneg A i

/-- The Ky Fan $k$-norm is at most $k$ times the spectral norm:
$\|\mathbf{A}\|_{(k)} \le k \|\mathbf{A}\|_2$. -/
theorem kyFanNorm_le_mul_specNorm (k : ℕ) (A : Matrix m n 𝕜) :
    kyFanNorm k A ≤ k * specNorm A := by
  have h := Finset.sum_le_card_nsmul (Finset.range k) (singularValues A) (specNorm A)
    fun i _ => singularValues_le_specNorm A i
  rwa [Finset.card_range, nsmul_eq_mul] at h

/-- Ky Fan norms stop growing at the smaller dimension of the matrix:
$\|\mathbf{A}\|_{(\min(k, \lvert m \rvert, \lvert n \rvert))} = \|\mathbf{A}\|_{(k)}$. It reduces
a statement about the Ky Fan $k$-norm to the case where $k$ is at most both dimensions. -/
theorem kyFanNorm_min_card (k : ℕ) (A : Matrix m n 𝕜) :
    kyFanNorm (min k (min (Fintype.card m) (Fintype.card n))) A = kyFanNorm k A := by
  refine Finset.sum_subset (Finset.range_mono (min_le_left _ _)) fun i hik hi => ?_
  rw [Finset.mem_range] at hik hi
  rcases Nat.lt_or_ge i (Fintype.card m) with him | him
  · exact singularValues_of_card_cols_le A (by omega)
  · exact singularValues_of_card_rows_le A him

/-- **Ky Fan's maximum principle for singular values**, real-part form. For $\mathbf{U}$ and
$\mathbf{V}$ with orthonormal columns indexed by $p$,
$\operatorname{Re} \operatorname{tr}(\mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{V})
\le \|\mathbf{A}\|_{(\lvert p \rvert)}$. The proof applies the eigenvalue principle to the
Hermitian dilation, compressed to the columns of
$(1/\sqrt{2}) \begin{bmatrix} \mathbf{U} \\ \mathbf{V} \end{bmatrix}$; the modulus form is
`NLAlib.norm_trace_conjTranspose_mul_mul_le_kyFanNorm`.
[HornJohnson1991, Theorem 3.4.1]. -/
theorem re_trace_conjTranspose_mul_mul_le_kyFanNorm [DecidableEq p] (A : Matrix m n 𝕜)
    {U : Matrix m p 𝕜} {V : Matrix n p 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) :
    RCLike.re (Uᴴ * A * V).trace ≤ kyFanNorm (Fintype.card p) A := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c * c = 2⁻¹ :=
    ⟨(√2)⁻¹, by rw [← mul_inv, Real.mul_self_sqrt zero_le_two]⟩
  have hc' : star (c : 𝕜) * (c : 𝕜) = 2⁻¹ := by
    rw [RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, hc, RCLike.ofReal_inv,
      RCLike.ofReal_ofNat]
  have hW : HasOrthonormalCols ((c : 𝕜) • Matrix.fromRows U V) := by
    rw [HasOrthonormalCols, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hc', Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, hU.conjTranspose_mul_self, hV.conjTranspose_mul_self,
      ← two_smul 𝕜 (1 : Matrix p p 𝕜), smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hD : ((c : 𝕜) • Matrix.fromRows U V)ᴴ * dilation A * ((c : 𝕜) • Matrix.fromRows U V) =
      (2⁻¹ : 𝕜) • ((Uᴴ * A * V)ᴴ + Uᴴ * A * V) := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hc', Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, dilation,
      Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows, Matrix.mul_zero,
      Matrix.mul_zero, zero_add, add_zero, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc Vᴴ]
  have h := (isHermitian_dilation A).re_trace_conjTranspose_mul_mul_le_sum_eigenvalue hW
  rw [hD, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_conjTranspose, smul_eq_mul,
    RCLike.star_def, add_comm, RCLike.add_conj, ← mul_assoc, inv_mul_cancel₀ two_ne_zero,
    one_mul, RCLike.ofReal_re] at h
  refine h.trans_eq (Finset.sum_congr rfl fun i hi => eigenvalue_dilation A ?_)
  exact lt_max_of_lt_left ((Finset.mem_range.mp hi).trans_le hU.card_le)

/-- **Ky Fan's maximum principle for singular values.** For $\mathbf{U}$ and $\mathbf{V}$ with
orthonormal columns indexed by $p$,
$$\lvert \operatorname{tr}(\mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{V}) \rvert
  \le \|\mathbf{A}\|_{(\lvert p \rvert)} \,.$$
[HornJohnson1991, Theorem 3.4.1].
Result: ky-fan-singular-values -/
theorem norm_trace_conjTranspose_mul_mul_le_kyFanNorm [DecidableEq p] (A : Matrix m n 𝕜)
    {U : Matrix m p 𝕜} {V : Matrix n p 𝕜} (hU : HasOrthonormalCols U)
    (hV : HasOrthonormalCols V) :
    ‖(Uᴴ * A * V).trace‖ ≤ kyFanNorm (Fintype.card p) A := by
  obtain ⟨c, hc, hct⟩ := RCLike.exists_norm_eq_mul_self (Uᴴ * A * V).trace
  have hV' : HasOrthonormalCols (c • V) := by
    rw [HasOrthonormalCols, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hV.conjTranspose_mul_self, RCLike.star_def, RCLike.conj_mul, hc,
      RCLike.ofReal_one, one_pow, one_smul]
  have h := re_trace_conjTranspose_mul_mul_le_kyFanNorm A hU hV'
  rwa [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← hct, RCLike.ofReal_re] at h

/-- **Ky Fan's maximum principle for singular values, equality case.** The maximum is attained
by the leading singular vectors, with a real nonnegative trace: for $k$ at most both dimensions
there are $\mathbf{U}$, $\mathbf{V}$ with $k$ orthonormal columns and
$\operatorname{tr}(\mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{V}) = \|\mathbf{A}\|_{(k)}$.
Result: ky-fan-singular-values -/
theorem exists_trace_conjTranspose_mul_mul_eq_kyFanNorm (A : Matrix m n 𝕜) {k : ℕ}
    (hkm : k ≤ Fintype.card m) (hkn : k ≤ Fintype.card n) :
    ∃ (U : Matrix m (Fin k) 𝕜) (V : Matrix n (Fin k) 𝕜), HasOrthonormalCols U ∧
      HasOrthonormalCols V ∧ (Uᴴ * A * V).trace = ((kyFanNorm k A : ℝ) : 𝕜) := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD A (le_min A.rank_le_card_height A.rank_le_card_width)
    (min_le_left _ _) (min_le_right _ _)
  have hk : k ≤ min (Fintype.card m) (Fintype.card n) := le_min hkm hkn
  refine ⟨U.submatrix id (Fin.castLE hk), V.submatrix id (Fin.castLE hk),
    h.hasOrthonormalCols_left.submatrix (Equiv.refl m) (Fin.castLE_injective hk),
    h.hasOrthonormalCols_right.submatrix (Equiv.refl n) (Fin.castLE_injective hk), ?_⟩
  rw [conjTranspose_submatrix_mul_mul_submatrix, h.conjTranspose_mul_mul_eq,
    Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hk), Matrix.trace_diagonal, kyFanNorm,
    ← Fin.sum_univ_eq_sum_range (fun i => singularValues A i) k, RCLike.ofReal_sum]
  rfl

/-- **The triangle inequality of the Ky Fan norms**:
$\|\mathbf{A} + \mathbf{B}\|_{(k)} \le \|\mathbf{A}\|_{(k)} + \|\mathbf{B}\|_{(k)}$, that is,
$$\sum_{i < k} \sigma_i(\mathbf{A} + \mathbf{B})
  \le \sum_{i < k} \sigma_i(\mathbf{A}) + \sum_{i < k} \sigma_i(\mathbf{B}) \,.$$
[HornJohnson1991, Corollary 3.4.3].
Result: ky-fan-singular-values -/
theorem kyFanNorm_add_le (k : ℕ) (A B : Matrix m n 𝕜) :
    kyFanNorm k (A + B) ≤ kyFanNorm k A + kyFanNorm k B := by
  rw [← kyFanNorm_min_card k (A + B), ← kyFanNorm_min_card k A, ← kyFanNorm_min_card k B]
  obtain ⟨U, V, hU, hV, h⟩ := exists_trace_conjTranspose_mul_mul_eq_kyFanNorm (A + B)
    ((min_le_right k _).trans (min_le_left _ _)) ((min_le_right k _).trans (min_le_right _ _))
  have hA := norm_trace_conjTranspose_mul_mul_le_kyFanNorm A hU hV
  have hB := norm_trace_conjTranspose_mul_mul_le_kyFanNorm B hU hV
  rw [Fintype.card_fin] at hA hB
  rw [← abs_of_nonneg (kyFanNorm_nonneg _ (A + B)), ← RCLike.norm_ofReal (K := 𝕜), ← h,
    Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  exact (norm_add_le _ _).trans (add_le_add hA hB)

/-- The Frobenius inner product with a matrix of rank at most $k$ and spectral norm at most one
is at most the Ky Fan $k$-norm: if $\operatorname{rank} \mathbf{P} \le k$ and
$\|\mathbf{P}\|_2 \le 1$, then
$\langle \mathbf{A}, \mathbf{P} \rangle_{\mathsf{F}} \le \|\mathbf{A}\|_{(k)}$. -/
theorem frobInner_le_kyFanNorm_of_rank_le_of_specNorm_le_one (A : Matrix m n 𝕜)
    {P : Matrix m n 𝕜} {k : ℕ} (hP : P.rank ≤ k) (hPn : specNorm P ≤ 1) :
    frobInner A P ≤ kyFanNorm k A := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD P le_rfl P.rank_le_card_height P.rank_le_card_width
  have hsum : frobInner A P =
      ∑ i : Fin P.rank, singularValues P i * RCLike.re ((Uᴴ * A * V) i i) := by
    rw [frobInner_comm, frobInner_eq_re_trace, h.conjTranspose.eq, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc Uᴴ, Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.diagonal_mul, RCLike.re_ofReal_mul]
  let S : Finset (Fin P.rank) := Finset.univ.filter fun i => 0 ≤ RCLike.re ((Uᴴ * A * V) i i)
  have hS : ∑ i ∈ S, RCLike.re ((Uᴴ * A * V) i i) =
      RCLike.re ((U.submatrix id (Subtype.val : S → Fin P.rank))ᴴ * A *
        V.submatrix id (Subtype.val : S → Fin P.rank)).trace := by
    rw [conjTranspose_submatrix_mul_mul_submatrix, Matrix.trace, map_sum,
      ← Finset.sum_coe_sort S]
    rfl
  have hle := norm_trace_conjTranspose_mul_mul_le_kyFanNorm A
    (h.hasOrthonormalCols_left.submatrix (Equiv.refl m)
      (Subtype.val_injective : Function.Injective (Subtype.val : S → Fin P.rank)))
    (h.hasOrthonormalCols_right.submatrix (Equiv.refl n) Subtype.val_injective)
  have hcard : Fintype.card S ≤ k := by
    rw [Fintype.card_coe]
    exact (S.card_le_univ.trans_eq (Fintype.card_fin _)).trans hP
  calc frobInner A P
      = ∑ i : Fin P.rank, singularValues P i * RCLike.re ((Uᴴ * A * V) i i) := hsum
    _ ≤ ∑ i, if 0 ≤ RCLike.re ((Uᴴ * A * V) i i) then RCLike.re ((Uᴴ * A * V) i i) else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with hi
        · exact mul_le_of_le_one_left hi ((singularValues_le_specNorm P i).trans hPn)
        · exact mul_nonpos_of_nonneg_of_nonpos (singularValues_nonneg P i) (not_le.mp hi).le
    _ = ∑ i ∈ S, RCLike.re ((Uᴴ * A * V) i i) := (Finset.sum_filter _ _).symm
    _ ≤ kyFanNorm (Fintype.card S) A := hS ▸ (RCLike.re_le_norm _).trans hle
    _ ≤ kyFanNorm k A := kyFanNorm_mono_left A hcard

end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: the Ky Fan norm `NLAlib.kyFanNorm` is nonnegative. -/
@[positivity NLAlib.kyFanNorm _ _]
meta def evalKyFanNorm : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    -- match the head after `whnfR` instead of reading arguments with `appArg!`, so that an atom
    -- that is a let-bound variable (from `set`) is rejected, never a panic
    match (← whnfR e).getAppFnArgs with
    | (``NLAlib.kyFanNorm, #[_, _, _, _, _, _, a, A]) =>
      pure (.nonnegative (← mkAppM ``NLAlib.kyFanNorm_nonneg #[a, A]))
    | _ => failure

end Mathlib.Meta.Positivity
