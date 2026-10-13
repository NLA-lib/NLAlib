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

For a symmetric gauge function `Φ`, `Φ.matrixNorm A` is `Φ` applied to the singular values of
`A`. It is a norm on matrices of every shape, invariant under multiplication by matrices with
orthonormal columns; the Schatten and Ky Fan norms are the cases `lpGauge q` and `kyFanGauge k`.
Results stated for `Φ.matrixNorm` hold for all of them at once, across shapes: for example
`Φ.matrixNorm (A * B) ≤ specNorm A * Φ.matrixNorm B`, where `A * B` and `B` have different shapes.

## Main definitions

* `NLAlib.singularValuesFinsupp`: the singular values as a finitely supported sequence.
* `NLAlib.SymmetricGauge.matrixNorm`: the unitarily invariant norm of a gauge.

## Main results

* `NLAlib.SymmetricGauge.matrixNorm_add_le`: the triangle inequality.
* `NLAlib.SymmetricGauge.matrixNorm_le_of_forall_kyFanNorm_le`,
  `NLAlib.forall_matrixNorm_le_iff_forall_kyFanNorm_le`: Fan dominance.
* `NLAlib.SymmetricGauge.apply_singularValuesFinsupp_sub_le`: Mirsky's theorem.
* `NLAlib.SymmetricGauge.matrixNorm_sub_truncatedSVD_le_of_rank_le`,
  `NLAlib.SymmetricGauge.isLeast_matrixNorm_sub_of_rank_le`: the truncated SVD is a best
  low-rank approximation in every unitarily invariant norm, and its error is the least one.
* `NLAlib.SymmetricGauge.mul_matrixNorm_le_of_sq_smul_one_le`: a factor bounded below cannot
  shrink a unitarily invariant norm by more than its lower bound.
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

/-- The **unitarily invariant norm** of a symmetric gauge function: the gauge of the singular
values. [HornJohnson2013, Theorem 7.4.7.2] (von Neumann).
Port of `NLAlib.SymmetricGauge.matrixValue`, there for one shape over `ℝ`. -/
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

/-- Unitarily invariant norms are definite.
Port of `NLAlib.SymmetricGauge.eq_zero_of_matrixValue_eq_zero`. -/
@[simp]
theorem matrixNorm_eq_zero_iff {A : Matrix m n 𝕜} : Φ.matrixNorm A = 0 ↔ A = 0 := by
  rw [matrixNorm_def, Φ.eq_zero_iff, ← singularValues_eq_zero, ← coe_singularValuesFinsupp,
    Finsupp.coe_eq_zero]

/-- Unitarily invariant norms are absolutely homogeneous.
Port of `NLAlib.SymmetricGauge.matrixValue_smul`. -/
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

/-- **Invariance**: left multiplication by a matrix with orthonormal columns preserves the norm.
The factor need not be square. -/
theorem matrixNorm_mul_left_of_hasOrthonormalCols [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) : Φ.matrixNorm (Q * A) = Φ.matrixNorm A := by
  exact Φ.matrixNorm_congr (hQ.singularValues_mul_left A)

/-- **Invariance**: right multiplication by the conjugate transpose of a matrix with orthonormal
columns preserves the norm. -/
theorem matrixNorm_mul_conjTranspose_right_of_hasOrthonormalCols [DecidableEq n]
    {Q : Matrix p n 𝕜} (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    Φ.matrixNorm (A * Qᴴ) = Φ.matrixNorm A := by
  exact Φ.matrixNorm_congr (hQ.singularValues_mul_conjTranspose_right A)

/-! ### Monotonicity, Fan dominance and the triangle inequality -/

/-- A matrix with smaller singular values has a smaller norm. The shapes may differ. -/
theorem matrixNorm_le_of_singularValues_le {A : Matrix m n 𝕜} {B : Matrix l p 𝕜}
    (h : ∀ i, singularValues A i ≤ singularValues B i) : Φ.matrixNorm A ≤ Φ.matrixNorm B := by
  refine Φ.le_of_abs_le fun i => ?_
  rw [coe_singularValuesFinsupp, coe_singularValuesFinsupp,
    abs_of_nonneg (singularValues_nonneg A i), abs_of_nonneg (singularValues_nonneg B i)]
  exact h i

/-- **Fan dominance.** If every Ky Fan norm of `A` is at most that of `B`, then every unitarily
invariant norm of `A` is at most that of `B`. The shapes may differ.
[HornJohnson2013, Theorem 7.4.8.4]; [Bhatia1997, Theorem IV.2.2].
Port of `NLAlib.forall_invariantNorm_le_iff_weaklyMajorized`, there for one shape over `ℝ`.
Result: fan-dominance -/
theorem matrixNorm_le_of_forall_kyFanNorm_le {A : Matrix m n 𝕜} {B : Matrix l p 𝕜}
    (h : ∀ k, kyFanNorm k A ≤ kyFanNorm k B) : Φ.matrixNorm A ≤ Φ.matrixNorm B := by
  refine Φ.le_of_forall_sum_le (singularValues_antitone B) fun S => ?_
  exact (sum_abs_singularValues_le_kyFanNorm A S).trans (h S.card)

/-- **The triangle inequality** for unitarily invariant norms.
[HornJohnson2013, Theorem 7.4.7.2].
Port of `NLAlib.SymmetricGauge.matrixValue_add_le`, there over `ℝ`.
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

/-- The reverse triangle inequality for unitarily invariant norms. -/
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

/-- `‖A B‖ ≤ ‖A‖₂ ‖B‖` for every unitarily invariant norm.
[HornJohnson2013, §7.4.9]; [Bhatia1997, Proposition IV.2.4]. -/
theorem matrixNorm_mul_le_specNorm_mul (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    Φ.matrixNorm (A * B) ≤ specNorm A * Φ.matrixNorm B := by
  have h := Φ.matrixNorm_le_of_singularValues_le (A := A * B) (B := (specNorm A : 𝕜) • B)
    fun i => by
      rw [singularValues_smul, RCLike.norm_ofReal, abs_of_nonneg (specNorm_nonneg A)]
      exact singularValues_mul_le_specNorm_mul A B i
  rwa [matrixNorm_smul, RCLike.norm_ofReal, abs_of_nonneg (specNorm_nonneg A)] at h

/-- `‖A B‖ ≤ ‖A‖ ‖B‖₂` for every unitarily invariant norm. -/
theorem matrixNorm_mul_le_mul_specNorm (A : Matrix m p 𝕜) (B : Matrix p n 𝕜) :
    Φ.matrixNorm (A * B) ≤ Φ.matrixNorm A * specNorm B := by
  have h := Φ.matrixNorm_le_of_singularValues_le (A := A * B) (B := (specNorm B : 𝕜) • A)
    fun i => by
      rw [singularValues_smul, RCLike.norm_ofReal, abs_of_nonneg (specNorm_nonneg B), mul_comm]
      exact singularValues_mul_le_mul_specNorm A B i
  rwa [matrixNorm_smul, RCLike.norm_ofReal, abs_of_nonneg (specNorm_nonneg B), mul_comm] at h

/-- Multiplying by a star projection on the left does not increase a unitarily invariant norm. -/
theorem matrixNorm_mul_le_of_isStarProjection {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (A : Matrix m n 𝕜) : Φ.matrixNorm (P * A) ≤ Φ.matrixNorm A := by
  exact Φ.matrixNorm_le_of_singularValues_le (hP.singularValues_mul_le A)

/-- A submatrix has a smaller unitarily invariant norm. -/
theorem matrixNorm_submatrix_le (A : Matrix m n 𝕜) {f : l → m} {g : p → n}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Φ.matrixNorm (A.submatrix f g) ≤ Φ.matrixNorm A := by
  exact Φ.matrixNorm_le_of_singularValues_le (singularValues_submatrix_le A hf hg)

open scoped MatrixOrder in
/-- A factor `T` with `c² • 1 ≤ Tᴴ * T`, `c ≥ 0`, shrinks a unitarily invariant norm by at most
`c`: `c * Φ.matrixNorm X ≤ Φ.matrixNorm (T * X)`. The form of
`NLAlib.mul_specNorm_le_of_sq_smul_one_le` for every unitarily invariant norm. -/
theorem mul_matrixNorm_le_of_sq_smul_one_le [DecidableEq m] {T : Matrix l m 𝕜} {c : ℝ}
    (hc : 0 ≤ c) (h : (c ^ 2) • (1 : Matrix m m 𝕜) ≤ Tᴴ * T) (X : Matrix m n 𝕜) :
    c * Φ.matrixNorm X ≤ Φ.matrixNorm (T * X) := by
  have h' := Φ.matrixNorm_le_of_singularValues_le (A := (c : 𝕜) • X) (B := T * X) fun i => by
    rw [singularValues_smul, RCLike.norm_ofReal, abs_of_nonneg hc,
      ← sq_le_sq₀ (mul_nonneg hc (singularValues_nonneg X i)) (singularValues_nonneg _ i),
      mul_pow]
    exact mul_sq_singularValues_le_of_smul_one_le h X i
  rwa [matrixNorm_smul, RCLike.norm_ofReal, abs_of_nonneg hc] at h'

/-! ### Comparison with the spectral and nuclear norms -/

/-- Every unitarily invariant norm dominates a multiple of the spectral norm. -/
theorem apply_single_mul_specNorm_le (A : Matrix m n 𝕜) :
    Φ (Finsupp.single 0 1) * specNorm A ≤ Φ.matrixNorm A := by
  have h := Φ.apply_single_mul_abs_le (singularValuesFinsupp A) 0
  rwa [coe_singularValuesFinsupp, singularValues_zero_eq_specNorm,
    abs_of_nonneg (specNorm_nonneg A)] at h

/-- Every unitarily invariant norm is dominated by a multiple of the nuclear norm. -/
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
`1`-Lipschitz: the gauge of the difference of the singular value sequences of `A` and `B` is at
most the norm of `A - B`.
[HornJohnson2013, Corollary 7.4.9.3]; [Bhatia1997, Theorem IV.3.4].
Port of `NLAlib.invariantNorm_rectangularDiagonal_singularValues_add_sub_le`, there over `ℝ`.
Result: mirsky-inequality -/
theorem apply_singularValuesFinsupp_sub_le (A B : Matrix m n 𝕜) :
    Φ (singularValuesFinsupp A - singularValuesFinsupp B) ≤ Φ.matrixNorm (A - B) := by
  refine Φ.le_of_forall_sum_le (singularValues_antitone (A - B)) fun S => ?_
  simp only [Finsupp.sub_apply, coe_singularValuesFinsupp]
  exact sum_abs_singularValues_sub_le_kyFanNorm_sub A B S

/-- **Eckart–Young–Mirsky.** The truncated SVD is a best approximation of rank at most `k` in
every unitarily invariant norm.
[HornJohnson2013, §7.4.9]; [Bhatia1997, Exercise IV.3.5]. -/
theorem matrixNorm_sub_truncatedSVD_le_of_rank_le (A : Matrix m n 𝕜) {B : Matrix m n 𝕜} {k : ℕ}
    (hB : B.rank ≤ k) : Φ.matrixNorm (A - truncatedSVD A k) ≤ Φ.matrixNorm (A - B) := by
  refine Φ.matrixNorm_le_of_singularValues_le fun i => ?_
  rw [singularValues_sub_truncatedSVD]
  exact singularValues_add_le_singularValues_sub_of_rank_le A hB i

/-- A best approximation of rank at most `r` exists in every unitarily invariant norm: the
distance to the closed set of matrices of rank at most `r` is attained (by the truncated SVD). -/
theorem isLeast_matrixNorm_sub_of_rank_le (A : Matrix m n 𝕜) (r : ℕ) :
    IsLeast ((fun B : Matrix m n 𝕜 => Φ.matrixNorm (A - B)) '' {B | B.rank ≤ r})
      (Φ.matrixNorm (A - truncatedSVD A r)) := by
  refine ⟨⟨truncatedSVD A r, rank_truncatedSVD_le A r, rfl⟩, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  exact Φ.matrixNorm_sub_truncatedSVD_le_of_rank_le A hB

end SymmetricGauge

/-! ### Schatten and Ky Fan norms as gauge norms -/

/-- The norm of the `ℓ^q` gauge is the Schatten `q`-norm.
Port of `NLAlib.schattenInvariantNorm_apply`. -/
@[simp]
theorem lpGauge_matrixNorm {q : ℝ≥0∞} (hq : 1 ≤ q) (A : Matrix m n 𝕜) :
    (lpGauge q hq).matrixNorm A = schattenNorm q A := by
  rw [SymmetricGauge.matrixNorm_def, schattenNorm]
  exact lpGauge_apply_eq_norm_toLp hq fun i hi => singularValues_of_min_card_le A hi

/-- The norm of the `ℓ^∞` gauge is the spectral norm. -/
theorem lpGauge_top_matrixNorm (A : Matrix m n 𝕜) :
    (lpGauge ⊤ le_top).matrixNorm A = specNorm A := by
  rw [lpGauge_matrixNorm, schattenNorm_top]

/-- The norm of the `ℓ^2` gauge is the Frobenius norm. -/
theorem lpGauge_two_matrixNorm (A : Matrix m n 𝕜) :
    (lpGauge 2 one_le_two).matrixNorm A = frobNorm A := by
  rw [lpGauge_matrixNorm, schattenNorm_two]

/-- The norm of the `ℓ^1` gauge is the nuclear norm. -/
theorem lpGauge_one_matrixNorm (A : Matrix m n 𝕜) :
    (lpGauge 1 le_rfl).matrixNorm A = nuclearNorm A := by
  rw [lpGauge_matrixNorm, schattenNorm_one]

/-- The norm of the Ky Fan `k`-gauge is the Ky Fan `k`-norm.
Port of `NLAlib.kyFanInvariantNorm`. -/
@[simp]
theorem kyFanGauge_matrixNorm {k : ℕ} (hk : k ≠ 0) (A : Matrix m n 𝕜) :
    (kyFanGauge k hk).matrixNorm A = kyFanNorm k A := by
  rw [SymmetricGauge.matrixNorm_def,
    kyFanGauge_apply_of_antitone hk (x := singularValuesFinsupp A) (singularValues_antitone A)]
  rfl

/-- **Fan dominance**, as an equivalence: every unitarily invariant norm of `A` is at most that of
`B` if and only if every Ky Fan norm of `A` is at most that of `B`. The shapes may differ. The
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

end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `Φ.matrixNorm A` is nonnegative. -/
@[positivity NLAlib.SymmetricGauge.matrixNorm _ _]
meta def evalSymmetricGaugeMatrixNorm : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    let pf ← mkAppM ``NLAlib.SymmetricGauge.matrixNorm_nonneg #[e.appFn!.appArg!, e.appArg!]
    pure (.nonnegative pf)

end Mathlib.Meta.Positivity
