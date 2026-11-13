/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.GaugeExamples
public import NLAlib.Matrix.Norms.Schatten
public import NLAlib.Matrix.Spectral.LowRank

/-!
# Unitarily invariant norms

For a symmetric gauge function $\Phi$, `Φ.matrixNorm A`, written $\|\mathbf{A}\|_{\Phi}$, is
$\Phi$ applied to the singular values of $\mathbf{A}$. It is a norm on matrices of every shape,
invariant under multiplication by matrices with orthonormal columns; the Schatten and Ky Fan norms
are the cases `lpGauge q` and `kyFanGauge k`. Results stated for `Φ.matrixNorm` hold for all of
them at once, across shapes: for example
$\|\mathbf{A}\mathbf{B}\|_{\Phi} \le \|\mathbf{A}\|_2 \|\mathbf{B}\|_{\Phi}$, where
$\mathbf{A}\mathbf{B}$ and $\mathbf{B}$ have different shapes.

## Main definitions

* `NLAlib.singularValuesFinsupp`: the singular values as a finitely supported sequence.
* `NLAlib.SymmetricGauge.matrixNorm`: the unitarily invariant norm of a gauge.

## Main results

* `NLAlib.SymmetricGauge.matrixNorm_add_le`: the triangle inequality.
* `NLAlib.SymmetricGauge.matrixNorm_mul_conjTranspose_self`:
  $\|\mathbf{A}\mathbf{A}^{\mathsf{H}}\|_{\Phi} = \|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\Phi}$.
* `NLAlib.SymmetricGauge.matrixNorm_le_of_forall_kyFanNorm_le`,
  `NLAlib.forall_matrixNorm_le_iff_forall_kyFanNorm_le`: Fan dominance.
* `NLAlib.SymmetricGauge.apply_singularValuesFinsupp_sub_le`: Mirsky's theorem.
* `NLAlib.SymmetricGauge.matrixNorm_sub_truncatedSVD_le_of_rank_le`,
  `NLAlib.SymmetricGauge.isLeast_matrixNorm_sub_of_rank_le`: the truncated SVD is a best
  low-rank approximation in every unitarily invariant norm, and its error is the least one.
* `NLAlib.SymmetricGauge.mul_matrixNorm_le_of_sq_smul_one_le`: a factor bounded below cannot
  shrink a unitarily invariant norm by more than its lower bound.
* `NLAlib.SymmetricGauge.matrixNorm_one_sub_rangeProjector_mul_le_of_range_le`: a larger range
  gives a smaller projection residual.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]

/-! ### Singular values as a finitely supported sequence -/

/-- Only finitely many singular values are nonzero. -/
theorem finite_support_singularValues (A : Matrix m n 𝕜) :
    (Function.support (singularValues A)).Finite := by
  refine (Finset.range (Fintype.card m)).finite_toSet.subset fun i hi => ?_
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra h
  exact hi (singularValues_of_card_rows_le A (not_lt.mp h))

/-- The singular values of a matrix as a finitely supported sequence, the argument of a symmetric
gauge function. As a function it is `singularValues A`. It is a cast, used only as the
argument of a gauge, never in a hypothesis or conclusion of its own. -/
noncomputable def singularValuesFinsupp (A : Matrix m n 𝕜) : ℕ →₀ ℝ :=
  Finsupp.ofSupportFinite (singularValues A) (finite_support_singularValues A)

/-- `singularValuesFinsupp A` is `singularValues A` as a function. -/
@[simp]
theorem coe_singularValuesFinsupp (A : Matrix m n 𝕜) :
    ⇑(singularValuesFinsupp A) = singularValues A :=
  rfl

/-- `singularValuesFinsupp` agrees with Mathlib's singular values of the associated linear map
between Euclidean spaces. -/
theorem singularValuesFinsupp_eq_linearMap [DecidableEq n] (A : Matrix m n 𝕜) :
    singularValuesFinsupp A = LinearMap.singularValues A.toEuclideanLin := by
  exact DFunLike.coe_injective (singularValues_eq_linearMap A)

/-- Singular values vanish from the smaller dimension on. -/
private theorem singularValues_of_min_card_le (A : Matrix m n 𝕜) {i : ℕ}
    (hi : min (Fintype.card m) (Fintype.card n) ≤ i) : singularValues A i = 0 := by
  obtain h | h := min_le_iff.mp hi
  · exact singularValues_of_card_rows_le A h
  · exact singularValues_of_card_cols_le A h

/-- A sum of singular values over an index set is at most the Ky Fan norm of that size. -/
private theorem sum_abs_singularValues_le_kyFanNorm (A : Matrix m n 𝕜) (S : Finset ℕ) :
    ∑ i ∈ S, |singularValues A i| ≤ kyFanNorm S.card A := by
  have h := sum_abs_singularValues_sub_le_kyFanNorm_sub A 0 S
  simpa only [singularValues_zero, Pi.zero_apply, sub_zero] using h

/-! ### The norm of a gauge -/

namespace SymmetricGauge

variable (Φ : SymmetricGauge)

/-- The **unitarily invariant norm** $\|\mathbf{A}\|_{\Phi}$ of a symmetric gauge function
$\Phi$: the gauge of the singular values,
$\Phi\bigl(\sigma_0(\mathbf{A}), \sigma_1(\mathbf{A}), \dots\bigr)$.
[HornJohnson2013, Theorem 7.4.7.2] (von Neumann). -/
noncomputable def matrixNorm (A : Matrix m n 𝕜) : ℝ :=
  Φ (singularValuesFinsupp A)

/-- The norm of a gauge is the gauge of the singular values. -/
theorem matrixNorm_def (A : Matrix m n 𝕜) : Φ.matrixNorm A = Φ (singularValuesFinsupp A) :=
  rfl

/-- Matrices with the same singular values have the same norm, whatever their shapes. -/
theorem matrixNorm_congr {A : Matrix m n 𝕜} {B : Matrix l p 𝕜}
    (h : singularValues A = singularValues B) : Φ.matrixNorm A = Φ.matrixNorm B := by
  rw [matrixNorm_def, matrixNorm_def]
  congr 1
  exact DFunLike.coe_injective h

/-- Unitarily invariant norms are nonnegative. -/
theorem matrixNorm_nonneg (A : Matrix m n 𝕜) : 0 ≤ Φ.matrixNorm A := by
  exact apply_nonneg Φ _

/-- The norm of the zero matrix vanishes. -/
@[simp]
theorem matrixNorm_zero : Φ.matrixNorm (0 : Matrix m n 𝕜) = 0 := by
  have h : singularValuesFinsupp (0 : Matrix m n 𝕜) = 0 :=
    DFunLike.coe_injective singularValues_zero
  rw [matrixNorm_def, h, map_zero]

/-- Unitarily invariant norms are definite. -/
@[simp]
theorem matrixNorm_eq_zero_iff {A : Matrix m n 𝕜} : Φ.matrixNorm A = 0 ↔ A = 0 := by
  rw [matrixNorm_def, Φ.eq_zero_iff, ← singularValues_eq_zero, ← coe_singularValuesFinsupp,
    Finsupp.coe_eq_zero]

/-- Unitarily invariant norms are absolutely homogeneous:
$\|c\mathbf{A}\|_{\Phi} = \lvert c \rvert \|\mathbf{A}\|_{\Phi}$. -/
theorem matrixNorm_smul (c : 𝕜) (A : Matrix m n 𝕜) :
    Φ.matrixNorm (c • A) = ‖c‖ * Φ.matrixNorm A := by
  have h : singularValuesFinsupp (c • A) = ‖c‖ • singularValuesFinsupp A := by
    ext i
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact singularValues_smul c A i
  rw [matrixNorm_def, h, map_smul_eq_mul, norm_norm, matrixNorm_def]

/-- Unitarily invariant norms are even. -/
@[simp]
theorem matrixNorm_neg (A : Matrix m n 𝕜) : Φ.matrixNorm (-A) = Φ.matrixNorm A := by
  exact Φ.matrixNorm_congr (singularValues_neg A)

/-- Unitarily invariant norms are invariant under the conjugate transpose. -/
@[simp]
theorem matrixNorm_conjTranspose (A : Matrix m n 𝕜) : Φ.matrixNorm Aᴴ = Φ.matrixNorm A := by
  exact Φ.matrixNorm_congr (singularValues_conjTranspose A)

/-- Unitarily invariant norms are invariant under the transpose. -/
@[simp]
theorem matrixNorm_transpose (A : Matrix m n 𝕜) : Φ.matrixNorm Aᵀ = Φ.matrixNorm A := by
  exact Φ.matrixNorm_congr (singularValues_transpose A)

/-- Unitarily invariant norms are invariant under relabelling rows and columns. -/
@[simp]
theorem matrixNorm_submatrix_equiv (A : Matrix m n 𝕜) (e₁ : l ≃ m) (e₂ : p ≃ n) :
    Φ.matrixNorm (A.submatrix e₁ e₂) = Φ.matrixNorm A := by
  exact Φ.matrixNorm_congr (singularValues_submatrix_equiv A e₁ e₂)

/-- Invariance: left multiplication by a matrix with orthonormal columns preserves the norm.
The factor need not be square. -/
theorem matrixNorm_mul_left_of_hasOrthonormalCols [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) : Φ.matrixNorm (Q * A) = Φ.matrixNorm A := by
  exact Φ.matrixNorm_congr (hQ.singularValues_mul_left A)

/-- Invariance: right multiplication by the conjugate transpose of a matrix with orthonormal
columns preserves the norm. -/
theorem matrixNorm_mul_conjTranspose_right_of_hasOrthonormalCols [DecidableEq n]
    {Q : Matrix p n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    Φ.matrixNorm (A * Qᴴ) = Φ.matrixNorm A := by
  exact Φ.matrixNorm_congr (hQ.singularValues_mul_conjTranspose_right A)

/-- Invariance on a subspace: if $\mathbf{V}$ has orthonormal columns and
$\mathbf{A}\mathbf{V}\mathbf{V}^{\mathsf{H}} = \mathbf{A}$ (the rows of $\mathbf{A}$ lie in
the range of $\mathbf{V}$), then $\|\mathbf{A}\mathbf{V}\|_{\Phi} = \|\mathbf{A}\|_{\Phi}$. -/
theorem matrixNorm_mul_of_mul_mul_conjTranspose_eq [DecidableEq p] {A : Matrix m n 𝕜}
    {V : Matrix n p 𝕜} (hV : HasOrthonormalCols V) (hAV : A * V * Vᴴ = A) :
    Φ.matrixNorm (A * V) = Φ.matrixNorm A := by
  rw [← Φ.matrixNorm_mul_conjTranspose_right_of_hasOrthonormalCols hV (A * V), hAV]

/-- The two Gram matrices have the same norm:
$\|\mathbf{A}\mathbf{A}^{\mathsf{H}}\|_{\Phi} = \|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\Phi}$,
although they have different sizes: both have singular values $\sigma_k(\mathbf{A})^2$. -/
theorem matrixNorm_mul_conjTranspose_self (A : Matrix m n 𝕜) :
    Φ.matrixNorm (A * Aᴴ) = Φ.matrixNorm (Aᴴ * A) := by
  refine Φ.matrixNorm_congr (funext fun k => ?_)
  rw [singularValues_mul_conjTranspose_self, singularValues_conjTranspose_mul_self]

/-! ### Monotonicity, Fan dominance and the triangle inequality -/

/-- A matrix with smaller singular values has a smaller norm. The shapes may differ. -/
theorem matrixNorm_le_of_singularValues_le {A : Matrix m n 𝕜} {B : Matrix l p 𝕜}
    (h : ∀ i, singularValues A i ≤ singularValues B i) : Φ.matrixNorm A ≤ Φ.matrixNorm B := by
  refine Φ.le_of_abs_le fun i => ?_
  rw [coe_singularValuesFinsupp, coe_singularValuesFinsupp,
    abs_of_nonneg (singularValues_nonneg A i), abs_of_nonneg (singularValues_nonneg B i)]
  exact h i

/-- **Fan dominance.** If every Ky Fan norm of $\mathbf{A}$ is at most that of $\mathbf{B}$,
$\|\mathbf{A}\|_{(k)} \le \|\mathbf{B}\|_{(k)}$ for all $k$, then every unitarily invariant norm of
$\mathbf{A}$ is at most that of $\mathbf{B}$: $\|\mathbf{A}\|_{\Phi} \le \|\mathbf{B}\|_{\Phi}$.
The shapes may differ.
[HornJohnson2013, Theorem 7.4.8.4]; [Bhatia1997, Theorem IV.2.2].
Result: fan-dominance -/
theorem matrixNorm_le_of_forall_kyFanNorm_le {A : Matrix m n 𝕜} {B : Matrix l p 𝕜}
    (h : ∀ k, kyFanNorm k A ≤ kyFanNorm k B) : Φ.matrixNorm A ≤ Φ.matrixNorm B := by
  refine Φ.le_of_forall_sum_le (singularValues_antitone B) fun S => ?_
  exact (sum_abs_singularValues_le_kyFanNorm A S).trans (h S.card)

/-- **The triangle inequality** for unitarily invariant norms: for every symmetric gauge $\Phi$
and matrices $\mathbf{A}$, $\mathbf{B}$ of the same shape,
$\|\mathbf{A} + \mathbf{B}\|_{\Phi} \le \|\mathbf{A}\|_{\Phi} + \|\mathbf{B}\|_{\Phi}$, where
$\|\mathbf{A}\|_{\Phi}$ (`Φ.matrixNorm A`) is the gauge of the singular values of $\mathbf{A}$.
[HornJohnson2013, Theorem 7.4.7.2].
Result: unitarily-invariant-norm -/
theorem matrixNorm_add_le (A B : Matrix m n 𝕜) :
    Φ.matrixNorm (A + B) ≤ Φ.matrixNorm A + Φ.matrixNorm B := by
  have h : Φ (singularValuesFinsupp (A + B)) ≤
      Φ (singularValuesFinsupp A + singularValuesFinsupp B) := by
    refine Φ.le_of_forall_sum_le (fun i j hij => ?_) fun S => ?_
    · rw [Finsupp.add_apply, Finsupp.add_apply]
      exact add_le_add (singularValues_antitone A hij) (singularValues_antitone B hij)
    · calc ∑ i ∈ S, |singularValuesFinsupp (A + B) i|
          ≤ kyFanNorm S.card (A + B) := sum_abs_singularValues_le_kyFanNorm (A + B) S
        _ ≤ kyFanNorm S.card A + kyFanNorm S.card B := kyFanNorm_add_le S.card A B
        _ = ∑ i ∈ Finset.range S.card, (singularValuesFinsupp A + singularValuesFinsupp B) i := by
          rw [kyFanNorm_eq_sum_range, kyFanNorm_eq_sum_range, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => (Finsupp.add_apply _ _ i).symm
  exact h.trans (map_add_le_add Φ _ _)

/-- The reverse triangle inequality for unitarily invariant norms:
$\lvert \|\mathbf{A}\|_{\Phi} - \|\mathbf{B}\|_{\Phi} \rvert
\le \|\mathbf{A} - \mathbf{B}\|_{\Phi}$. -/
theorem abs_matrixNorm_sub_matrixNorm_le (A B : Matrix m n 𝕜) :
    |Φ.matrixNorm A - Φ.matrixNorm B| ≤ Φ.matrixNorm (A - B) := by
  rw [abs_sub_le_iff]
  constructor
  · have h := Φ.matrixNorm_add_le (A - B) B
    rw [sub_add_cancel] at h
    linarith
  · have h := Φ.matrixNorm_add_le (B - A) A
    rw [sub_add_cancel, ← neg_sub, matrixNorm_neg] at h
    linarith

/-! ### Products -/

/-- $\|\mathbf{A}\mathbf{B}\|_{\Phi} \le \|\mathbf{A}\|_2 \|\mathbf{B}\|_{\Phi}$ for every
unitarily invariant norm.
[HornJohnson2013, §7.4.9]; [Bhatia1997, Proposition IV.2.4]. -/
theorem matrixNorm_mul_le_specNorm_mul (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    Φ.matrixNorm (A * B) ≤ specNorm A * Φ.matrixNorm B := by
  have h := Φ.matrixNorm_le_of_singularValues_le (A := A * B) (B := (specNorm A : 𝕜) • B)
    fun i => by
      rw [singularValues_smul, RCLike.norm_ofReal, abs_of_nonneg (specNorm_nonneg A)]
      exact singularValues_mul_le_specNorm_mul A B i
  rwa [matrixNorm_smul, RCLike.norm_ofReal, abs_of_nonneg (specNorm_nonneg A)] at h

/-- $\|\mathbf{A}\mathbf{B}\|_{\Phi} \le \|\mathbf{A}\|_{\Phi} \|\mathbf{B}\|_2$ for every
unitarily invariant norm. -/
theorem matrixNorm_mul_le_mul_specNorm (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    Φ.matrixNorm (A * B) ≤ Φ.matrixNorm A * specNorm B := by
  have h := Φ.matrixNorm_le_of_singularValues_le (A := A * B) (B := (specNorm B : 𝕜) • A)
    fun i => by
      rw [singularValues_smul, RCLike.norm_ofReal, abs_of_nonneg (specNorm_nonneg B), mul_comm]
      exact singularValues_mul_le_mul_specNorm A B i
  rwa [matrixNorm_smul, RCLike.norm_ofReal, abs_of_nonneg (specNorm_nonneg B), mul_comm] at h

/-- Multiplying by a star projection on the left does not increase a unitarily invariant norm:
$\|\mathbf{P}\mathbf{A}\|_{\Phi} \le \|\mathbf{A}\|_{\Phi}$. -/
theorem matrixNorm_mul_le_of_isStarProjection {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (A : Matrix m n 𝕜) : Φ.matrixNorm (P * A) ≤ Φ.matrixNorm A := by
  exact Φ.matrixNorm_le_of_singularValues_le (hP.singularValues_mul_le A)

/-- A submatrix selected by injective maps of the row and column indices has a smaller
unitarily invariant norm. -/
theorem matrixNorm_submatrix_le (A : Matrix m n 𝕜) {f : l → m} {g : p → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Φ.matrixNorm (A.submatrix f g) ≤ Φ.matrixNorm A := by
  exact Φ.matrixNorm_le_of_singularValues_le (singularValues_submatrix_le A hf hg)

open scoped MatrixOrder in
/-- A factor $\mathbf{T}$ with $c^2\mathbf{I} \preceq \mathbf{T}^{\mathsf{H}}\mathbf{T}$,
$c \ge 0$, shrinks a unitarily invariant norm by at most $c$:
$c \|\mathbf{X}\|_{\Phi} \le \|\mathbf{T}\mathbf{X}\|_{\Phi}$. The form of
`NLAlib.mul_specNorm_le_of_sq_smul_one_le` for every unitarily invariant norm. -/
theorem mul_matrixNorm_le_of_sq_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {c : ℝ}
    (hc : 0 ≤ c) (h : (c ^ 2) • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) :
    c * Φ.matrixNorm X ≤ Φ.matrixNorm (T * X) := by
  have h' := Φ.matrixNorm_le_of_singularValues_le (A := (c : 𝕜) • X) (B := T * X) fun i => by
    rw [singularValues_smul, RCLike.norm_ofReal, abs_of_nonneg hc,
      ← sq_le_sq₀ (mul_nonneg hc (singularValues_nonneg X i)) (singularValues_nonneg _ i),
      mul_pow]
    exact mul_singularValues_sq_le_of_smul_one_le h X i
  rwa [matrixNorm_smul, RCLike.norm_ofReal, abs_of_nonneg hc] at h'

/-! ### Comparison with the spectral and nuclear norms -/

/-- Every unitarily invariant norm dominates a multiple of the spectral norm:
$\Phi(\mathbf{e}_0) \|\mathbf{A}\|_2 \le \|\mathbf{A}\|_{\Phi}$, with $\mathbf{e}_0$ the first unit
coordinate sequence. -/
theorem apply_single_mul_specNorm_le (A : Matrix m n 𝕜) :
    Φ (Finsupp.single 0 1) * specNorm A ≤ Φ.matrixNorm A := by
  have h := Φ.apply_single_mul_abs_le (singularValuesFinsupp A) 0
  rwa [coe_singularValuesFinsupp, singularValues_zero_eq_specNorm,
    abs_of_nonneg (specNorm_nonneg A)] at h

/-- Every unitarily invariant norm is dominated by a multiple of the nuclear norm:
$\|\mathbf{A}\|_{\Phi} \le \Phi(\mathbf{e}_0) \|\mathbf{A}\|_*$, with $\mathbf{e}_0$ the first unit
coordinate sequence. -/
theorem matrixNorm_le_apply_single_mul_nuclearNorm (A : Matrix m n 𝕜) :
    Φ.matrixNorm A ≤ Φ (Finsupp.single 0 1) * nuclearNorm A := by
  refine (Φ.le_apply_single_mul_sum _).trans_eq ?_
  have hsub : (singularValuesFinsupp A).support ⊆
      Finset.range (min (Fintype.card m) (Fintype.card n)) := fun i hi => by
    rw [Finset.mem_range]
    by_contra hlt
    exact Finsupp.mem_support_iff.mp hi (singularValues_of_min_card_le A (not_lt.mp hlt))
  rw [nuclearNorm, Finset.sum_subset hsub fun i _ hi => by
    rw [Finsupp.notMem_support_iff.mp hi, abs_zero]]
  congr 1
  exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (singularValues_nonneg A i)

/-! ### Perturbation of singular values and low-rank approximation -/

/-- **Mirsky's theorem.** In every unitarily invariant norm, the sorted singular values are
$1$-Lipschitz: the gauge of the difference of the singular value sequences of $\mathbf{A}$ and
$\mathbf{B}$ is at most the norm of $\mathbf{A} - \mathbf{B}$,
$$\Phi\bigl(\sigma_0(\mathbf{A}) - \sigma_0(\mathbf{B}),\,
  \sigma_1(\mathbf{A}) - \sigma_1(\mathbf{B}),\, \dots\bigr)
  \le \|\mathbf{A} - \mathbf{B}\|_{\Phi}\,.$$
[HornJohnson2013, Corollary 7.4.9.3]; [Bhatia1997, Theorem IV.3.4].
Result: mirsky-inequality -/
theorem apply_singularValuesFinsupp_sub_le (A B : Matrix m n 𝕜) :
    Φ (singularValuesFinsupp A - singularValuesFinsupp B) ≤ Φ.matrixNorm (A - B) := by
  refine Φ.le_of_forall_sum_le (singularValues_antitone (A - B)) fun S => ?_
  simp only [Finsupp.sub_apply, coe_singularValuesFinsupp]
  exact sum_abs_singularValues_sub_le_kyFanNorm_sub A B S

/-- **Eckart–Young–Mirsky.** The truncated SVD $\llbracket \mathbf{A} \rrbracket_k$ is a best
approximation of rank at most $k$ in every unitarily invariant norm: for every $\mathbf{B}$ with
$\operatorname{rank} \mathbf{B} \le k$,
$\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\Phi} \le \|\mathbf{A} - \mathbf{B}\|_{\Phi}$.
[HornJohnson2013, §7.4.9]; [Bhatia1997, Exercise IV.3.5]. -/
theorem matrixNorm_sub_truncatedSVD_le_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) : Φ.matrixNorm (A - truncatedSVD A k) ≤ Φ.matrixNorm (A - B) := by
  refine Φ.matrixNorm_le_of_singularValues_le fun i => ?_
  rw [singularValues_sub_truncatedSVD]
  exact singularValues_add_le_singularValues_sub_of_rank_le A hB i

/-- A best approximation of rank at most $r$ exists in every unitarily invariant norm: the
distance to the closed set of matrices of rank at most $r$ is attained, by the truncated SVD:
$\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_r\|_{\Phi}$ is the least value of
$\|\mathbf{A} - \mathbf{B}\|_{\Phi}$ over $\operatorname{rank} \mathbf{B} \le r$. -/
theorem isLeast_matrixNorm_sub_of_rank_le (A : Matrix m n 𝕜) (r : ℕ) :
    IsLeast ((fun B : Matrix m n 𝕜 => Φ.matrixNorm (A - B)) '' {B | B.rank ≤ r})
      (Φ.matrixNorm (A - truncatedSVD A r)) := by
  refine ⟨⟨truncatedSVD A r, rank_truncatedSVD_le A r, rfl⟩, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  exact Φ.matrixNorm_sub_truncatedSVD_le_of_rank_le A hB

end SymmetricGauge

/-! ### Schatten and Ky Fan norms as gauge norms -/

/-- The norm of the $\ell^q$ gauge is the Schatten $q$-norm $\|\mathbf{A}\|_{S_q}$. -/
@[simp]
theorem lpGauge_matrixNorm {q : ℝ≥0∞} [Fact (1 ≤ q)] (A : Matrix m n 𝕜) :
    (lpGauge q).matrixNorm A = schattenNorm q A := by
  rw [SymmetricGauge.matrixNorm_def, schattenNorm]
  exact lpGauge_apply_eq_norm_toLp fun i hi => singularValues_of_min_card_le A hi

/-- The norm of the $\ell^\infty$ gauge is the spectral norm $\|\mathbf{A}\|_2$. -/
theorem lpGauge_top_matrixNorm (A : Matrix m n 𝕜) :
    (lpGauge ⊤).matrixNorm A = specNorm A := by
  rw [lpGauge_matrixNorm, schattenNorm_top]

/-- The norm of the $\ell^2$ gauge is the Frobenius norm $\|\mathbf{A}\|_{\mathsf{F}}$. -/
theorem lpGauge_two_matrixNorm (A : Matrix m n 𝕜) :
    (lpGauge 2).matrixNorm A = frobNorm A := by
  rw [lpGauge_matrixNorm, schattenNorm_two]

/-- The norm of the $\ell^1$ gauge is the nuclear norm $\|\mathbf{A}\|_*$. -/
theorem lpGauge_one_matrixNorm (A : Matrix m n 𝕜) :
    (lpGauge 1).matrixNorm A = nuclearNorm A := by
  rw [lpGauge_matrixNorm, schattenNorm_one]

/-- The norm of the Ky Fan $k$-gauge is the Ky Fan $k$-norm $\|\mathbf{A}\|_{(k)}$. -/
@[simp]
theorem kyFanGauge_matrixNorm {k : ℕ} (hk : k ≠ 0) (A : Matrix m n 𝕜) :
    (kyFanGauge k hk).matrixNorm A = kyFanNorm k A := by
  rw [SymmetricGauge.matrixNorm_def,
    kyFanGauge_apply_of_antitone hk (x := singularValuesFinsupp A) (singularValues_antitone A)]
  rfl

/-- **Fan dominance**, as an equivalence: every unitarily invariant norm of $\mathbf{A}$ is at
most that of $\mathbf{B}$ if and only if every Ky Fan norm of $\mathbf{A}$ is at most that of
$\mathbf{B}$. The shapes may differ. The
Ky Fan norms are unitarily invariant norms (`kyFanGauge_matrixNorm`), which gives one direction;
the other is `SymmetricGauge.matrixNorm_le_of_forall_kyFanNorm_le`.
[HornJohnson2013, Theorem 7.4.8.4].
Result: fan-dominance -/
theorem forall_matrixNorm_le_iff_forall_kyFanNorm_le {A : Matrix m n 𝕜} {B : Matrix l p 𝕜} :
    (∀ Φ : SymmetricGauge, Φ.matrixNorm A ≤ Φ.matrixNorm B) ↔
      ∀ k, kyFanNorm k A ≤ kyFanNorm k B := by
  refine ⟨fun h k => ?_, fun h Φ => Φ.matrixNorm_le_of_forall_kyFanNorm_le h⟩
  obtain rfl | hk := eq_or_ne k 0
  · rw [kyFanNorm_zero_left, kyFanNorm_zero_left]
  · have hk' := h (kyFanGauge k hk)
    rwa [kyFanGauge_matrixNorm, kyFanGauge_matrixNorm] at hk'


/-- **A larger range gives a smaller projection residual**, in every unitarily invariant norm: if
the range of $\mathbf{Y}$ is contained in the range of $\mathbf{B}$ then
$$\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}})\mathbf{A}\|_{\Phi} \le
\|(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{A}\|_{\Phi}\,.$$
[TroppWebber2023, Lemma 5.1]; [HalkoMartinssonTropp2011, Proposition 8.5]; there in the Schatten
and spectral norms. -/
theorem SymmetricGauge.matrixNorm_one_sub_rangeProjector_mul_le_of_range_le (Φ : SymmetricGauge)
    [DecidableEq m] {B : Matrix m p 𝕜} {Y : Matrix m l 𝕜}
    (h : LinearMap.range Y.mulVecLin ≤ LinearMap.range B.mulVecLin) (A : Matrix m n 𝕜) :
    Φ.matrixNorm ((1 - rangeProjector B) * A) ≤ Φ.matrixNorm ((1 - rangeProjector Y) * A) := by
  exact Φ.matrixNorm_le_of_singularValues_le
    (singularValues_one_sub_rangeProjector_mul_le_of_range_le h A)
/-- A function on matrices of one shape is **unitarily invariant** if multiplication by
arbitrary square unitary factors on the left and right preserves its value.
[Bhatia1997, §IV.2]. -/
def IsUnitarilyInvariant [DecidableEq m] [DecidableEq n] (f : Matrix m n 𝕜 → ℝ) : Prop :=
  ∀ (P : Matrix m m 𝕜), HasOrthonormalCols P → ∀ (Q : Matrix n n 𝕜), HasOrthonormalCols Q →
    ∀ A, f (P * A * Qᴴ) = f A

/-- The matrix norm induced by a symmetric gauge is unitarily invariant on each shape. -/
theorem SymmetricGauge.isUnitarilyInvariant_matrixNorm [DecidableEq m] [DecidableEq n]
    (Φ : SymmetricGauge) :
    IsUnitarilyInvariant (Φ.matrixNorm : Matrix m n 𝕜 → ℝ) := by
  intro P hP Q hQ A
  rw [Φ.matrixNorm_mul_conjTranspose_right_of_hasOrthonormalCols hQ,
    Φ.matrixNorm_mul_left_of_hasOrthonormalCols hP]

/-- Every Schatten functional is invariant under unitary changes of coordinates, including
the rank functional at zero and the spectral norm at infinity. [Bhatia1997, §IV.2]. -/
theorem isUnitarilyInvariant_schattenNorm [DecidableEq m] [DecidableEq n] (q : ℝ≥0∞) :
    IsUnitarilyInvariant (schattenNorm q : Matrix m n 𝕜 → ℝ) := by
  intro P hP Q hQ A
  rw [hQ.schattenNorm_mul_conjTranspose_right, hP.schattenNorm_mul_left]

/-- The spectral norm is unitarily invariant. [Bhatia1997, §IV.2]. -/
theorem isUnitarilyInvariant_specNorm [DecidableEq m] [DecidableEq n] :
    IsUnitarilyInvariant (specNorm : Matrix m n 𝕜 → ℝ) := by
  simpa only [show (schattenNorm ⊤ : Matrix m n 𝕜 → ℝ) = specNorm from
    funext schattenNorm_top] using (isUnitarilyInvariant_schattenNorm (𝕜 := 𝕜) (m := m) (n := n) ⊤)

/-- The Frobenius norm is unitarily invariant. [Bhatia1997, §IV.2]. -/
theorem isUnitarilyInvariant_frobNorm [DecidableEq m] [DecidableEq n] :
    IsUnitarilyInvariant (frobNorm : Matrix m n 𝕜 → ℝ) := by
  simpa only [show (schattenNorm 2 : Matrix m n 𝕜 → ℝ) = frobNorm from
    funext schattenNorm_two] using (isUnitarilyInvariant_schattenNorm (𝕜 := 𝕜) (m := m) (n := n) 2)


end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `Φ.matrixNorm A` is nonnegative. -/
@[positivity NLAlib.SymmetricGauge.matrixNorm _ _]
meta def evalSymmetricGaugeMatrixNorm : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    -- match the head after `whnfR` instead of reading arguments with `appArg!`, so that an atom
    -- that is a let-bound variable (from `set`) is rejected, never a panic
    match (← whnfR e).getAppFnArgs with
    | (``NLAlib.SymmetricGauge.matrixNorm, #[_, _, _, _, _, _, a, A]) =>
      pure (.nonnegative (← mkAppM ``NLAlib.SymmetricGauge.matrixNorm_nonneg #[a, A]))
    | _ => failure

end Mathlib.Meta.Positivity
