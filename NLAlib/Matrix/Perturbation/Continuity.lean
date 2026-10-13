/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import NLAlib.Matrix.Majorization.TraceInequalities
public import NLAlib.Matrix.Perturbation.Pseudoinverse

/-!
# Continuity of spectral quantities

Eigenvalues, singular values, the named norms and the optimal low-rank approximation errors are
continuous functions of the matrix; the rank is lower semicontinuous; the pseudoinverse and the
range projector are continuous on each set of matrices of a fixed rank. The quantitative
statements behind these (Weyl, Mirsky, Wedin) are in the earlier files; this file records the
topological consequences in Mathlib's vocabulary, for the product topology on matrices.

## Main results

* `NLAlib.continuous_singularValues`, `NLAlib.continuousOn_eigenvalue`.
* `NLAlib.SymmetricGauge.continuous_matrixNorm`, `NLAlib.continuous_schattenNorm`.
* `NLAlib.SymmetricGauge.abs_matrixNorm_sub_truncatedSVD_sub_le`: the optimal error of rank-`k`
  approximation is `1`-Lipschitz in every unitarily invariant norm.
* `NLAlib.isClosed_setOf_rank_le`, `NLAlib.isOpen_setOf_le_rank`,
  `NLAlib.isOpen_setOf_injective_mulVec`.
* `NLAlib.continuousOn_pinv_setOf_rank_eq`, `NLAlib.continuousOn_rangeProjector_setOf_rank_eq`.
-/

@[expose] public section

open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-! ### Singular values, eigenvalues and norms -/

/-- A real function on a topological group whose increments within `s` are dominated by a
continuous function of the difference vanishing at `0` is continuous on `s`. -/
private theorem continuousOn_of_abs_sub_le {E : Type*} [TopologicalSpace E] [AddGroup E]
    [ContinuousSub E] {s : Set E} {f g : E → ℝ} (hg : Continuous g) (hg0 : g 0 = 0)
    (h : ∀ A ∈ s, ∀ B ∈ s, |f B - f A| ≤ g (B - A)) : ContinuousOn f s := by
  intro A hA
  have h0 : Filter.Tendsto (fun B => g (B - A)) (nhdsWithin A s) (nhds 0) := by
    have h1 : Filter.Tendsto (fun B => g (B - A)) (nhds A) (nhds (g (A - A))) :=
      (hg.comp (continuous_id.sub continuous_const)).tendsto A
    rw [sub_self, hg0] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_ h0
  filter_upwards [self_mem_nhdsWithin] with B hB
  rw [Real.dist_eq]
  exact h A hA B hB

/-- The form of `continuousOn_of_abs_sub_le` on the whole space. -/
private theorem continuous_of_abs_sub_le {E : Type*} [TopologicalSpace E] [AddGroup E]
    [ContinuousSub E] {f g : E → ℝ} (hg : Continuous g) (hg0 : g 0 = 0)
    (h : ∀ A B, |f B - f A| ≤ g (B - A)) : Continuous f :=
  continuousOn_univ.mp (continuousOn_of_abs_sub_le hg hg0 fun A _ B _ => h A B)

/-- Each singular value is a continuous function of the matrix.
Port of `NLAlib.continuous_singularValues_array`. -/
theorem continuous_singularValues (k : ℕ) :
    Continuous fun A : Matrix m n 𝕜 => singularValues A k := by
  exact continuous_of_abs_sub_le continuous_specNorm specNorm_zero fun A B =>
    abs_singularValues_sub_le_specNorm B A k

/-- Each sorted eigenvalue is a continuous function on the Hermitian matrices.
Port of `NLAlib.continuous_eigenvalues₀_pencil`, there along a line. -/
theorem continuousOn_eigenvalue (k : ℕ) :
    ContinuousOn (fun A : Matrix n n 𝕜 => eigenvalue A k) {A | A.IsHermitian} := by
  exact continuousOn_of_abs_sub_le continuous_specNorm specNorm_zero fun A hA B hB =>
    abs_eigenvalue_sub_le hB hA k

/-- Ky Fan norms are continuous. -/
theorem continuous_kyFanNorm (k : ℕ) : Continuous fun A : Matrix m n 𝕜 => kyFanNorm k A := by
  simp only [kyFanNorm_eq_sum_range]
  exact continuous_finsetSum _ fun i _ => continuous_singularValues i

/-- The nuclear norm is continuous. -/
theorem continuous_nuclearNorm : Continuous (nuclearNorm : Matrix m n 𝕜 → ℝ) := by
  unfold nuclearNorm
  exact continuous_finsetSum _ fun i _ => continuous_singularValues i

/-- Every unitarily invariant norm is continuous. -/
theorem SymmetricGauge.continuous_matrixNorm (Φ : SymmetricGauge) :
    Continuous fun A : Matrix m n 𝕜 => Φ.matrixNorm A := by
  refine continuous_of_abs_sub_le (g := fun X => Φ (Finsupp.single 0 1) * nuclearNorm X)
    (continuous_const.mul continuous_nuclearNorm) (by rw [nuclearNorm_zero, mul_zero])
    fun A B => ?_
  exact (Φ.abs_matrixNorm_sub_matrixNorm_le B A).trans
    (Φ.matrixNorm_le_apply_single_mul_nuclearNorm (B - A))

/-- The Schatten `q`-norm is continuous, for `1 ≤ q`: it is the unitarily invariant norm of the
`ℓ^q` gauge. -/
theorem continuous_schattenNorm {q : ℝ≥0∞} (hq : 1 ≤ q) :
    Continuous fun A : Matrix m n 𝕜 => schattenNorm q A := by
  have h := (lpGauge q hq).continuous_matrixNorm (𝕜 := 𝕜) (m := m) (n := n)
  simp only [lpGauge_matrixNorm] at h
  exact h

/-! ### Optimal low-rank approximation errors -/

/-- One half of `SymmetricGauge.abs_matrixNorm_sub_truncatedSVD_sub_le`. -/
private theorem SymmetricGauge.matrixNorm_sub_truncatedSVD_le_add (Φ : SymmetricGauge)
    (A B : Matrix m n 𝕜) (k : ℕ) :
    Φ.matrixNorm (A - truncatedSVD A k) ≤
      Φ.matrixNorm (A - B) + Φ.matrixNorm (B - truncatedSVD B k) := by
  refine (Φ.matrixNorm_sub_truncatedSVD_le_of_rank_le A (rank_truncatedSVD_le B k)).trans ?_
  have h := Φ.matrixNorm_add_le (A - B) (B - truncatedSVD B k)
  rwa [sub_add_sub_cancel] at h

/-- **The optimal error of rank-`k` approximation is `1`-Lipschitz** in every unitarily
invariant norm: `|‖A - A_k‖ - ‖B - B_k‖| ≤ ‖A - B‖`. (In the spectral norm the error is
`singularValues A k` and this is Weyl's inequality.)
Port of `NLAlib.abs_sqrt_bestRankFrobSq_sub_le_frobNorm`, there over `ℝ` in the Frobenius norm. -/
theorem SymmetricGauge.abs_matrixNorm_sub_truncatedSVD_sub_le (Φ : SymmetricGauge)
    (A B : Matrix m n 𝕜) (k : ℕ) :
    |Φ.matrixNorm (A - truncatedSVD A k) - Φ.matrixNorm (B - truncatedSVD B k)| ≤
      Φ.matrixNorm (A - B) := by
  rw [abs_sub_le_iff]
  constructor
  · have h := Φ.matrixNorm_sub_truncatedSVD_le_add A B k
    linarith
  · have h := Φ.matrixNorm_sub_truncatedSVD_le_add B A k
    rw [← neg_sub A B, Φ.matrixNorm_neg] at h
    linarith

/-- The optimal Frobenius error of rank-`k` approximation is `1`-Lipschitz in the Frobenius
norm. Port of `NLAlib.abs_sqrt_bestRankFrobSq_sub_le_frobNorm`. -/
theorem abs_frobNorm_sub_truncatedSVD_sub_le (A B : Matrix m n 𝕜) (k : ℕ) :
    |frobNorm (A - truncatedSVD A k) - frobNorm (B - truncatedSVD B k)| ≤ frobNorm (A - B) := by
  simpa only [lpGauge_two_matrixNorm] using
    (lpGauge 2 one_le_two).abs_matrixNorm_sub_truncatedSVD_sub_le A B k

/-- The optimal error of rank-`k` approximation is continuous, in every unitarily invariant norm.
The truncated SVD itself is not: it jumps where `σ_{k-1} = σ_k`.
Port of `NLAlib.continuous_bestRankFrobSq`. -/
theorem SymmetricGauge.continuous_matrixNorm_sub_truncatedSVD (Φ : SymmetricGauge) (k : ℕ) :
    Continuous fun A : Matrix m n 𝕜 => Φ.matrixNorm (A - truncatedSVD A k) := by
  exact continuous_of_abs_sub_le Φ.continuous_matrixNorm Φ.matrixNorm_zero fun A B =>
    Φ.abs_matrixNorm_sub_truncatedSVD_sub_le B A k

/-! ### Rank -/

omit [Fintype m] in
/-- **The matrices of rank at most `r` form a closed set**: the rank is lower semicontinuous. -/
theorem isClosed_setOf_rank_le [Finite m] (r : ℕ) : IsClosed {A : Matrix m n 𝕜 | A.rank ≤ r} := by
  have := Fintype.ofFinite m
  have h : {A : Matrix m n 𝕜 | A.rank ≤ r} = (fun A => singularValues A r) ⁻¹' {0} := by
    ext A
    exact (singularValues_eq_zero_iff A).symm
  rw [h]
  exact isClosed_singleton.preimage (continuous_singularValues r)

omit [Fintype m] in
/-- **The matrices of rank at least `r` form an open set**: a small perturbation does not lower
the rank. -/
theorem isOpen_setOf_le_rank [Finite m] (r : ℕ) : IsOpen {A : Matrix m n 𝕜 | r ≤ A.rank} := by
  cases r with
  | zero => simp only [Nat.zero_le, Set.ofPred_true, isOpen_univ]
  | succ k =>
    have h : {A : Matrix m n 𝕜 | k + 1 ≤ A.rank} = {A : Matrix m n 𝕜 | A.rank ≤ k}ᶜ := by
      ext A
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le, Nat.lt_iff_add_one_le]
    rw [h]
    exact (isClosed_setOf_rank_le k).isOpen_compl

omit [Fintype m] in
/-- The matrices of full column rank form an open set. -/
theorem isOpen_setOf_injective_mulVec [Finite m] :
    IsOpen {A : Matrix m n 𝕜 | Function.Injective A.mulVec} := by
  classical
  have := Fintype.ofFinite m
  have h : {A : Matrix m n 𝕜 | Function.Injective A.mulVec} =
      (fun A : Matrix m n 𝕜 => (Aᴴ * A).det) ⁻¹' {0}ᶜ := by
    ext A
    change Function.Injective A.mulVec ↔ (Aᴴ * A).det ≠ 0
    rw [← isUnit_conjTranspose_mul_self_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [h]
  exact isOpen_compl_singleton.preimage
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).matrix_det

/-! ### The pseudoinverse and the range projector -/

/-- A family of matrices converges to `M` when the spectral norm of the difference tends to
zero. -/
private theorem tendsto_of_tendsto_specNorm_sub {α : Type*} {F : Filter α}
    {f : α → Matrix m n 𝕜} {M : Matrix m n 𝕜}
    (h : Filter.Tendsto (fun a => specNorm (f a - M)) F (nhds 0)) :
    Filter.Tendsto f F (nhds M) := by
  classical
  open scoped Matrix.Norms.L2Operator in
  exact tendsto_iff_norm_sub_tendsto_zero.mpr h

/-- The spectral distance to a fixed matrix tends to zero at that matrix. -/
private theorem tendsto_specNorm_sub_nhdsWithin (A : Matrix m n 𝕜) (s : Set (Matrix m n 𝕜)) :
    Filter.Tendsto (fun B => specNorm (B - A)) (nhdsWithin A s) (nhds 0) := by
  have h : Filter.Tendsto (fun B => specNorm (B - A)) (nhds A) (nhds (specNorm (A - A))) :=
    (continuous_specNorm.comp (continuous_id.sub continuous_const)).tendsto A
  rw [sub_self, specNorm_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **The pseudoinverse is continuous on each set of matrices of a fixed rank.** It is not
continuous on the whole space. [StewartSun1990, §III.3]; [Wedin1973]. -/
theorem continuousOn_pinv_setOf_rank_eq (r : ℕ) :
    ContinuousOn (pinv : Matrix m n 𝕜 → Matrix n m 𝕜) {A | A.rank = r} := by
  intro A hA
  refine tendsto_of_tendsto_specNorm_sub ?_
  have h0 := tendsto_specNorm_sub_nhdsWithin A {A : Matrix m n 𝕜 | A.rank = r}
  have ha := specNorm_nonneg (pinv A)
  have hsmall : ∀ᶠ B in nhdsWithin A {A : Matrix m n 𝕜 | A.rank = r},
      specNorm (pinv A) * specNorm (B - A) < 1 / 2 := by
    have h1 := h0.const_mul (specNorm (pinv A))
    rw [mul_zero] at h1
    exact h1.eventually (gt_mem_nhds (by norm_num))
  have hlim : Filter.Tendsto
      (fun B => Real.goldenRatio * specNorm (pinv A) * (2 * specNorm (pinv A)) * specNorm (B - A))
      (nhdsWithin A {A : Matrix m n 𝕜 | A.rank = r}) (nhds 0) := by
    have h1 := h0.const_mul (Real.goldenRatio * specNorm (pinv A) * (2 * specNorm (pinv A)))
    rwa [mul_zero] at h1
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => specNorm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin, hsmall] with B hB hBs
  have hrank : A.rank = B.rank := hA.trans hB.symm
  have hpinv : specNorm (pinv B) ≤ 2 * specNorm (pinv A) := by
    refine (specNorm_pinv_le_div_of_rank_eq hrank (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  refine (specNorm_pinv_sub_pinv_le_goldenRatio_mul_of_rank_eq hrank).trans ?_
  gcongr

/-- The range projector is continuous on each set of matrices of a fixed rank. -/
theorem continuousOn_rangeProjector_setOf_rank_eq (r : ℕ) :
    ContinuousOn (fun A : Matrix m n 𝕜 => rangeProjector A) {A | A.rank = r} := by
  intro A hA
  refine tendsto_of_tendsto_specNorm_sub ?_
  have h0 := (tendsto_specNorm_sub_nhdsWithin A {A : Matrix m n 𝕜 | A.rank = r}).const_mul
    (specNorm (pinv A))
  rw [mul_zero] at h0
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => specNorm_nonneg _) ?_ h0
  filter_upwards [self_mem_nhdsWithin] with B hB
  rw [specNorm_sub_comm]
  exact (specNorm_rangeProjector_sub_rangeProjector_le (hA.trans hB.symm)).trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (specNorm_nonneg _))

end NLAlib
