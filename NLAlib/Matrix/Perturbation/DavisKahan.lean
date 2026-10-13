/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.Sylvester
public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Basic.Projector
public import NLAlib.Matrix.Majorization.KyFan

/-!
# The Davis–Kahan `sin Θ` theorems

How far an invariant subspace of a Hermitian matrix is from an approximately invariant subspace,
or from the corresponding invariant subspace of a perturbed matrix.

The basic statement is in residual form. Let `A` be Hermitian with `A * V = V * M` (the columns of
`V` span an invariant subspace, on which `A` acts as `M`), and let `(U, L)` be any pair with `L`
Hermitian. If the spectra of `L` and `M` are separated by `δ`, then
`δ ‖Vᴴ U‖ ≤ ‖Vᴴ (A U - U L)‖`. When `U` and `V` are frames, `Vᴴ * U` has the singular values of
`(1 - P) * Q` for `Q = U Uᴴ` and `1 - P = V Vᴴ`: the sines of the principal angles between the
range of `U` and the orthogonal complement of the range of `V`
(see `NLAlib.Matrix.Subspaces.PrincipalAngles`). The perturbation theorems are corollaries, with
`A U - U L = E U` when `U` is invariant for `A - E`.

With an interval separation the bounds hold in every unitarily invariant norm; with an arbitrary
separation, in the Frobenius norm.

## Main results

* `NLAlib.SymmetricGauge.mul_matrixNorm_conjTranspose_mul_le_of_eigenvalue`: the `sin Θ` theorem
  in residual form, interval separation, every unitarily invariant norm.
* `NLAlib.mul_frobNorm_conjTranspose_mul_le`: arbitrary separation, Frobenius norm.
* `NLAlib.SymmetricGauge.mul_matrixNorm_mul_le_of_mul_mul_le`: the projector form.
* `NLAlib.SymmetricGauge.mul_matrixNorm_one_sub_mul_le_of_add_smul_one_le`: a Ritz pair against a
  leading eigenspace, no complement frame.
* `NLAlib.SymmetricGauge.mul_matrixNorm_one_sub_mul_le_of_eigenvalue_sub`: leading eigenspaces of
  `A` and `A + E`.
* `NLAlib.one_sub_mul_mul_one_sub_le_of_mul_eq_mul_diagonal`,
  `NLAlib.one_sub_mul_mul_one_sub_le_of_smul_one_le`: a Hermitian matrix on the complement of a
  leading invariant subspace, in the Loewner order.

The bounds that involve only the eigenvalue gap of the unperturbed matrix, and the variational
form, are in `NLAlib.Matrix.Perturbation.DavisKahanGap`.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p q : Type*} [Fintype n] [Fintype p] [Fintype q]

/-! ### The residual form -/

/-- If `A` and `M` are Hermitian and `A * V = V * M`, then `Vᴴ * A = M * Vᴴ`. -/
private theorem conjTranspose_mul_eq_of_mul_eq {A : Matrix n n 𝕜} {V : Matrix n q 𝕜}
    {M : Matrix q q 𝕜} (hA : A.IsHermitian) (hM : M.IsHermitian) (hAV : A * V = V * M) :
    Vᴴ * A = M * Vᴴ := by
  have h := congrArg Matrix.conjTranspose hAV
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA.eq, hM.eq] at h

/-- The block on which a Hermitian matrix acts on an invariant frame is Hermitian. -/
private theorem isHermitian_of_mul_eq_mul [DecidableEq q] {A : Matrix n n 𝕜} {V : Matrix n q 𝕜}
    {M : Matrix q q 𝕜} (hA : A.IsHermitian) (hV : HasOrthonormalCols V) (hAV : A * V = V * M) :
    M.IsHermitian := by
  have h : M = Vᴴ * A * V := by
    rw [Matrix.mul_assoc, hAV, ← Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.one_mul]
  rw [h]
  exact Matrix.isHermitian_conjTranspose_mul_mul V hA

/-- The Sylvester identity behind the `sin Θ` theorems: if `A` is Hermitian, `A * V = V * M` and
`M` is Hermitian, then `Vᴴ (A U - U L) = M (Vᴴ U) - (Vᴴ U) L`.
Port of `NLAlib.sylvester_complement_overlap_eq`. -/
theorem conjTranspose_mul_mul_sub_mul_eq {A : Matrix n n 𝕜} {V : Matrix n q 𝕜} {M : Matrix q q 𝕜}
    (hA : A.IsHermitian) (hM : M.IsHermitian) (hAV : A * V = V * M) (U : Matrix n p 𝕜)
    (L : Matrix p p 𝕜) : Vᴴ * (A * U - U * L) = M * (Vᴴ * U) - Vᴴ * U * L := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc, conjTranspose_mul_eq_of_mul_eq hA hM hAV,
    Matrix.mul_assoc, Matrix.mul_assoc]

/-- **The Davis–Kahan `sin Θ` theorem, residual form.** Let `A` be Hermitian with
`A * V = V * M`, `M` Hermitian. If the spectrum of `L` lies in `[a, b]` and every eigenvalue of
`M` lies outside `(a - δ, b + δ)`, then in every unitarily invariant norm
`δ ‖Vᴴ U‖ ≤ ‖Vᴴ (A U - U L)‖`.
[DavisKahan1970]; [Bhatia1997, Theorem VII.3.1]; [StewartSun1990, Theorem V.3.6].
Port of `NLAlib.sinePrincipalAngles_le_compressed_residual_div_of_interval`, there over `ℝ` for
the spectral norm.
Result: davis-kahan -/
theorem SymmetricGauge.mul_matrixNorm_conjTranspose_mul_le_of_eigenvalue [DecidableEq p]
    (Φ : SymmetricGauge) {A : Matrix n n 𝕜} {V : Matrix n q 𝕜} {M : Matrix q q 𝕜}
    (hA : A.IsHermitian) (hM : M.IsHermitian) (hAV : A * V = V * M) {U : Matrix n p 𝕜}
    {L : Matrix p p 𝕜}
    {a b δ : ℝ} (hL₁ : a • (1 : Matrix p p 𝕜) ≤ L) (hL₂ : L ≤ b • (1 : Matrix p p 𝕜))
    (hMsep : ∀ i, i < Fintype.card q → eigenvalue M i ≤ a - δ ∨ b + δ ≤ eigenvalue M i) :
    δ * Φ.matrixNorm (Vᴴ * U) ≤ Φ.matrixNorm (Vᴴ * (A * U - U * L)) := by
  rw [conjTranspose_mul_mul_sub_mul_eq hA hM hAV]
  exact Φ.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_eigenvalue hM hL₁ hL₂ hMsep _

/-- The `sin Θ` theorem in residual form with a one-sided separation: `M ≤ (α - δ) • 1` and
`α • 1 ≤ L`. Port of `NLAlib.sinePrincipalAngles_le_compressed_residual_div_of_one_sided_frames`.
Result: davis-kahan -/
theorem SymmetricGauge.mul_matrixNorm_conjTranspose_mul_le_of_le [DecidableEq p]
    [DecidableEq q] (Φ : SymmetricGauge) {A : Matrix n n 𝕜} {V : Matrix n q 𝕜}
    {M : Matrix q q 𝕜} (hA : A.IsHermitian) (hAV : A * V = V * M) {U : Matrix n p 𝕜}
    {L : Matrix p p 𝕜} {α δ : ℝ}
    (hM : M ≤ (α - δ) • (1 : Matrix q q 𝕜)) (hL : α • (1 : Matrix p p 𝕜) ≤ L) :
    δ * Φ.matrixNorm (Vᴴ * U) ≤ Φ.matrixNorm (Vᴴ * (A * U - U * L)) := by
  rw [conjTranspose_mul_mul_sub_mul_eq hA (isHermitian_of_le_smul_one hM) hAV]
  exact Φ.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_le hM hL _

/-- **The `sin Θ` theorem in the Frobenius norm**, residual form, for an arbitrary separation:
if the eigenvalues of `L` and `M` are pairwise at distance at least `δ`, then
`δ ‖Vᴴ U‖_F ≤ ‖Vᴴ (A U - U L)‖_F`.
[DavisKahan1970]; [StewartSun1990, Theorem V.3.4].
Port of `NLAlib.frobNorm_sinePrincipalAngles_le_compressed_residual_div`, there over `ℝ`.
Result: davis-kahan -/
theorem mul_frobNorm_conjTranspose_mul_le {A : Matrix n n 𝕜} {V : Matrix n q 𝕜}
    {M : Matrix q q 𝕜} (hA : A.IsHermitian) (hM : M.IsHermitian) (hAV : A * V = V * M)
    {U : Matrix n p 𝕜} {L : Matrix p p 𝕜} (hL : L.IsHermitian) {δ : ℝ}
    (hsep : ∀ i, i < Fintype.card q → ∀ j, j < Fintype.card p →
      δ ≤ |eigenvalue M i - eigenvalue L j|) :
    δ * frobNorm (Vᴴ * U) ≤ frobNorm (Vᴴ * (A * U - U * L)) := by
  rw [conjTranspose_mul_mul_sub_mul_eq hA hM hAV]
  exact mul_frobNorm_le_frobNorm_mul_sub_mul hM hL hsep _

/-- **Distance of a vector from an invariant subspace, from its residual.** If `A` is Hermitian,
`A * V = V * M` with `M` Hermitian, and every eigenvalue of `M` is at distance at least `δ` from
`ρ`, then `δ ‖Vᴴ x‖ ≤ ‖Vᴴ (A x - ρ x)‖`. With `V` a frame of the complement of an eigenspace this
bounds the sine of the angle between `x` and the eigenspace by `‖A x - ρ x‖ / δ`.
[Parlett1998, Theorem 11.7.1 context].
Port of `NLAlib.sqrt_complement_eigenvalueProjector_le_residual_div`. -/
theorem mul_norm_conjTranspose_mulVec_le {A : Matrix n n 𝕜} {V : Matrix n q 𝕜} {M : Matrix q q 𝕜}
    (hA : A.IsHermitian) (hM : M.IsHermitian) (hAV : A * V = V * M) {ρ δ : ℝ}
    (hsep : ∀ i, i < Fintype.card q → δ ≤ |eigenvalue M i - ρ|) (x : n → 𝕜) :
    δ * ‖WithLp.toLp 2 (Vᴴ *ᵥ x)‖ ≤ ‖WithLp.toLp 2 (Vᴴ *ᵥ (A *ᵥ x - ρ • x))‖ := by
  classical
  rcases le_or_gt δ 0 with hδ | hδ
  · exact (mul_nonpos_of_nonpos_of_nonneg hδ (norm_nonneg _)).trans (norm_nonneg _)
  have h := hM.sq_smul_one_le_sub_smul_one_conjTranspose_mul_self (s := δ) (c := ρ) hδ.le hsep
  rw [smul_one_le_conjTranspose_mul_self_iff] at h
  have h' := h (Vᴴ *ᵥ x)
  have heq : (M - ρ • (1 : Matrix q q 𝕜)) *ᵥ (Vᴴ *ᵥ x) = Vᴴ *ᵥ (A *ᵥ x - ρ • x) := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, ← conjTranspose_mul_eq_of_mul_eq hA hM hAV,
      ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_smul]
  rw [heq, ← mul_pow] at h'
  exact le_of_sq_le_sq h' (norm_nonneg _)

/-! ### Projector form -/

/-- The Sylvester identity of the projector form: for an orthogonal projector `Q` commuting with
`A`, the matrix `Q A Q + μ (1 - Q)`, which is `A` on the range of `Q` and `μ` on its complement,
satisfies `(Q A Q + μ (1 - Q)) (Q U) - (Q U) L = Q (A U - U L)`. -/
private theorem add_smul_one_sub_mul_mul_sub_mul [DecidableEq n] {A Q : Matrix n n 𝕜}
    (hQ : IsStarProjection Q) (hAQ : A * Q = Q * A) (μ : ℝ) (U : Matrix n p 𝕜)
    (L : Matrix p p 𝕜) :
    (Q * A * Q + μ • (1 - Q)) * (Q * U) - Q * U * L = Q * (A * U - U * L) := by
  have hQAQ : Q * A * Q = Q * A := by
    rw [Matrix.mul_assoc, hAQ, ← Matrix.mul_assoc, hQ.mul_self]
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc Q Q U,
    hQ.mul_self, sub_self, smul_zero, add_zero, ← Matrix.mul_assoc (Q * A * Q) Q U,
    Matrix.mul_assoc (Q * A) Q Q, hQ.mul_self, hQAQ, Matrix.mul_sub, Matrix.mul_assoc,
    Matrix.mul_assoc]

/-- **The `sin Θ` theorem, projector form.** Let `Q` be an orthogonal projector commuting with
`A` (the projector onto an invariant subspace) on whose range `A` is at most `μ`, in the form
`Q A Q ≤ μ • Q`. For any pair `(U, L)` with `(μ + δ) • 1 ≤ L`, in every unitarily invariant norm
`δ ‖Q U‖ ≤ ‖Q (A U - U L)‖`. With `Q = 1 - W Wᴴ` for a frame `W` of the rest of the spectrum,
`Q U` is the distance of the range of `U` from the range of `W`. Only the compression `Q A Q`
enters, and the hypothesis makes it Hermitian, so `A` itself need not be.
[DavisKahan1970]; [Bhatia1997, Theorem VII.3.1].
Result: davis-kahan -/
theorem SymmetricGauge.mul_matrixNorm_mul_le_of_mul_mul_le [DecidableEq p] (Φ : SymmetricGauge)
    {A Q : Matrix n n 𝕜} (hQ : IsStarProjection Q) (hAQ : A * Q = Q * A)
    {μ δ : ℝ} (hQA : Q * A * Q ≤ μ • Q) {U : Matrix n p 𝕜} {L : Matrix p p 𝕜}
    (hL : (μ + δ) • (1 : Matrix p p 𝕜) ≤ L) :
    δ * Φ.matrixNorm (Q * U) ≤ Φ.matrixNorm (Q * (A * U - U * L)) := by
  classical
  have hle : Q * A * Q + μ • (1 - Q) ≤ (μ + δ - δ) • (1 : Matrix n n 𝕜) := by
    rw [add_sub_cancel_right, Matrix.le_iff] at *
    convert hQA using 1
    rw [smul_sub]
    abel
  have h := Φ.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_le hle hL (Q * U)
  rwa [add_smul_one_sub_mul_mul_sub_mul hQ hAQ] at h

/-- The projector form with the invariant subspace above the Ritz block: `μ • Q ≤ Q A Q` and
`L ≤ (μ - δ) • 1`. -/
theorem SymmetricGauge.mul_matrixNorm_mul_le_of_le_mul_mul [DecidableEq p] (Φ : SymmetricGauge)
    {A Q : Matrix n n 𝕜} (hQ : IsStarProjection Q) (hAQ : A * Q = Q * A)
    {μ δ : ℝ} (hQA : μ • Q ≤ Q * A * Q) {U : Matrix n p 𝕜} {L : Matrix p p 𝕜}
    (hL : L ≤ (μ - δ) • (1 : Matrix p p 𝕜)) :
    δ * Φ.matrixNorm (Q * U) ≤ Φ.matrixNorm (Q * (A * U - U * L)) := by
  classical
  have hle : (μ - δ + δ) • (1 : Matrix n n 𝕜) ≤ Q * A * Q + μ • (1 - Q) := by
    rw [sub_add_cancel, Matrix.le_iff] at *
    convert hQA using 1
    rw [smul_sub]
    abel
  have h := Φ.mul_matrixNorm_le_matrixNorm_mul_sub_mul_of_ge hle hL (Q * U)
  rwa [add_smul_one_sub_mul_mul_sub_mul hQ hAQ] at h

/-! ### Leading eigenspaces -/

/-- The projector onto an invariant subspace of a Hermitian matrix commutes with it. -/
theorem HasOrthonormalCols.mul_conjTranspose_commute_of_mul_eq_mul [DecidableEq p]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {W : Matrix n p 𝕜} {M : Matrix p p 𝕜}
    (hW : HasOrthonormalCols W)
    (hAW : A * W = W * M) : A * (W * Wᴴ) = W * Wᴴ * A := by
  have h := conjTranspose_mul_eq_of_mul_eq hA (isHermitian_of_mul_eq_mul hA hW hAW) hAW
  rw [← Matrix.mul_assoc, hAW, Matrix.mul_assoc W Wᴴ A, h, Matrix.mul_assoc]

omit [Fintype p] in
/-- A unit vector orthogonal to the columns of a frame extends the frame by one column. -/
private theorem HasOrthonormalCols.fromCols_replicateCol [DecidableEq p] {W : Matrix n p 𝕜}
    (hW : HasOrthonormalCols W) {x : n → 𝕜} (hx₀ : Wᴴ *ᵥ x = 0)
    (hx : ‖WithLp.toLp 2 x‖ = 1) :
    HasOrthonormalCols (Matrix.fromCols W (Matrix.replicateCol Unit x)) := by
  rw [hasOrthonormalCols_fromCols_iff]
  refine ⟨hW, ?_, ?_⟩
  · rw [hasOrthonormalCols_iff]
    ext i j
    rw [Matrix.conjTranspose_replicateCol, Matrix.replicateRow_mul_replicateCol_apply,
      EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, hx, one_pow, RCLike.ofReal_one,
      Subsingleton.elim i j, Matrix.one_apply_eq]
  · rw [← Matrix.replicateCol_mulVec, hx₀]
    ext i k
    rfl

/-- The trace of the compression of `A` to a frame extended by one column `x` is the trace of
the compression to the frame plus the quadratic form at `x`. -/
private theorem trace_conjTranspose_fromCols_replicateCol_mul_mul (A : Matrix n n 𝕜)
    (W : Matrix n p 𝕜) (x : n → 𝕜) :
    ((Matrix.fromCols W (Matrix.replicateCol Unit x))ᴴ * A *
      Matrix.fromCols W (Matrix.replicateCol Unit x)).trace =
      (Wᴴ * A * W).trace + quadForm A x := by
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul,
    Matrix.fromRows_mul_fromCols]
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂, Finset.univ_unique, Finset.sum_singleton]
  rw [Matrix.conjTranspose_replicateCol, Matrix.mul_assoc _ A (Matrix.replicateCol Unit x),
    ← Matrix.replicateCol_mulVec, Matrix.replicateRow_mul_replicateCol_apply, quadForm_def]

/-- To bound a Hermitian matrix on the orthogonal complement of the range of a frame `W`, it
suffices to bound its quadratic form at the unit vectors orthogonal to the columns of `W`. -/
private theorem one_sub_mul_mul_one_sub_le_of_forall [DecidableEq n] [DecidableEq p]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {W : Matrix n p 𝕜} (hW : HasOrthonormalCols W)
    {c : ℝ}
    (h : ∀ x : n → 𝕜, Wᴴ *ᵥ x = 0 → ‖WithLp.toLp 2 x‖ = 1 → RCLike.re (quadForm A x) ≤ c) :
    (1 - W * Wᴴ) * A * (1 - W * Wᴴ) ≤ c • (1 - W * Wᴴ) := by
  have hQ : IsStarProjection (1 - W * Wᴴ) := hW.isStarProjection_mul_conjTranspose.one_sub
  have e₁ : (1 - W * Wᴴ) * A * (1 - W * Wᴴ) = (1 - W * Wᴴ)ᴴ * A * (1 - W * Wᴴ) := by
    rw [hQ.conjTranspose_eq]
  have e₂ : 1 - W * Wᴴ = (1 - W * Wᴴ)ᴴ * (1 - W * Wᴴ) := by
    rw [hQ.conjTranspose_eq, hQ.mul_self]
  have h₁ : ((1 - W * Wᴴ) * A * (1 - W * Wᴴ)).IsHermitian := by
    rw [e₁]
    exact Matrix.isHermitian_conjTranspose_mul_mul _ hA
  rw [h₁.le_iff_re_quadForm_le (hQ.isHermitian.smul (IsSelfAdjoint.all c))]
  intro z
  have hx₀ : Wᴴ *ᵥ ((1 - W * Wᴴ) *ᵥ z) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
      hW.conjTranspose_mul_self, Matrix.one_mul, sub_self, Matrix.zero_mulVec]
  rw [e₁, quadForm_conjTranspose_mul_mul, RCLike.real_smul_eq_coe_smul (K := 𝕜),
    quadForm_smul_left, RCLike.re_ofReal_mul, e₂, quadForm_conjTranspose_mul_self,
    RCLike.ofReal_re, ← e₂]
  generalize (1 - W * Wᴴ) *ᵥ z = x at hx₀
  by_cases hx : x = 0
  · rw [hx, quadForm_zero_right, map_zero, WithLp.toLp_zero, norm_zero]
    simp
  have ht : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.mpr fun h0 => hx (by simpa using h0)
  have h' := h (((‖WithLp.toLp 2 x‖⁻¹ : ℝ) : 𝕜) • x) (by rw [Matrix.mulVec_smul, hx₀, smul_zero])
    (by rw [WithLp.toLp_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr ht),
      inv_mul_cancel₀ ht.ne'])
  rw [quadForm_smul_right, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul,
    RCLike.re_ofReal_mul] at h'
  have h'' := mul_le_mul_of_nonneg_right h' (sq_nonneg ‖WithLp.toLp 2 x‖)
  have e : ‖WithLp.toLp 2 x‖⁻¹ * ‖WithLp.toLp 2 x‖⁻¹ * RCLike.re (quadForm A x) *
      ‖WithLp.toLp 2 x‖ ^ 2 = RCLike.re (quadForm A x) := by
    field_simp
  rwa [e] at h''

/-- The quadratic form of `A` at a unit vector orthogonal to a frame of leading eigenvectors is
at most the next eigenvalue, by Ky Fan's maximum principle applied to the extended frame. -/
private theorem re_quadForm_le_eigenvalue_of_mul_eq_mul_diagonal {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {j : ℕ} {W : Matrix n (Fin (j + 1)) 𝕜} (hW : HasOrthonormalCols W)
    (hAW : A * W = W * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    {x : n → 𝕜} (hx₀ : Wᴴ *ᵥ x = 0) (hx : ‖WithLp.toLp 2 x‖ = 1) :
    RCLike.re (quadForm A x) ≤ eigenvalue A (j + 1) := by
  have h := hA.re_trace_conjTranspose_mul_mul_le_sum_eigenvalue (hW.fromCols_replicateCol hx₀ hx)
  have hcard : Fintype.card (Fin (j + 1) ⊕ Unit) = j + 1 + 1 := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  rw [hcard, trace_conjTranspose_fromCols_replicateCol_mul_mul, Matrix.mul_assoc, hAW,
    ← Matrix.mul_assoc, hW.conjTranspose_mul_self, Matrix.one_mul, Matrix.trace_diagonal,
    ← RCLike.ofReal_sum, map_add, RCLike.ofReal_re, Finset.sum_range_succ,
    Fin.sum_univ_eq_sum_range (fun i => eigenvalue A i) (j + 1)] at h
  linarith

/-- **The complement of a leading eigenframe.** If the columns of `W` are orthonormal
eigenvectors of the Hermitian matrix `A` for its `j + 1` largest eigenvalues, then on the
orthogonal complement `A` is at most `λ_{j+1}(A)`. This holds with repeated eigenvalues. -/
theorem one_sub_mul_mul_one_sub_le_of_mul_eq_mul_diagonal [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {j : ℕ} {W : Matrix n (Fin (j + 1)) 𝕜} (hW : HasOrthonormalCols W)
    (hAW : A * W = W * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜)) :
    (1 - W * Wᴴ) * A * (1 - W * Wᴴ) ≤ eigenvalue A (j + 1) • (1 - W * Wᴴ) :=
  one_sub_mul_mul_one_sub_le_of_forall hA hW fun _ hx₀ hx =>
    re_quadForm_le_eigenvalue_of_mul_eq_mul_diagonal hA hW hAW hx₀ hx

/-- The quadratic form of `A` on the span of an invariant frame `W` and a vector `x` orthogonal
to it splits into the form of the block on the frame and the form at `x`. -/
private theorem re_quadForm_fromCols_replicateCol_mulVec [DecidableEq p] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {W : Matrix n p 𝕜} {Λ : Matrix p p 𝕜} (hW : HasOrthonormalCols W)
    (hAW : A * W = W * Λ) {x : n → 𝕜} (hx₀ : Wᴴ *ᵥ x = 0) (v : p ⊕ Unit → 𝕜) :
    RCLike.re (quadForm A (Matrix.fromCols W (Matrix.replicateCol Unit x) *ᵥ v)) =
      RCLike.re (quadForm Λ (v ∘ Sum.inl)) + ‖v (Sum.inr ())‖ ^ 2 * RCLike.re (quadForm A x) := by
  have hcol : Matrix.replicateCol Unit x *ᵥ (v ∘ Sum.inr) = v (Sum.inr ()) • x := by
    ext i
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hcross : star (v (Sum.inr ()) • x) ⬝ᵥ (A *ᵥ (W *ᵥ (v ∘ Sum.inl))) = 0 := by
    have h : star (v (Sum.inr ()) • x) ᵥ* W = star (Wᴴ *ᵥ (v (Sum.inr ()) • x)) := by
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mulVec_mulVec, hAW, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h,
      Matrix.mulVec_smul, hx₀, smul_zero, star_zero, zero_dotProduct]
  have hΛ : Λ = Wᴴ * A * W := by
    rw [Matrix.mul_assoc, hAW, ← Matrix.mul_assoc, hW.conjTranspose_mul_self, Matrix.one_mul]
  rw [Matrix.fromCols_mulVec, hcol, add_comm, hA.re_quadForm_add, hcross, map_zero, mul_zero,
    add_zero, quadForm_smul_right, RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow,
    RCLike.re_ofReal_mul, hΛ, quadForm_conjTranspose_mul_mul, add_comm]

/-- The quadratic form of `A` at a unit vector orthogonal to an invariant frame with `j + 1`
columns on which `A` is at least `λ_j(A)` is at most `λ_{j+1}(A)`, when the two differ. -/
private theorem re_quadForm_le_eigenvalue_of_smul_one_le [DecidableEq p] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {W : Matrix n p 𝕜} {Λ : Matrix p p 𝕜} (hW : HasOrthonormalCols W)
    (hAW : A * W = W * Λ) {j : ℕ} (hp : Fintype.card p = j + 1)
    (hΛ : eigenvalue A j • (1 : Matrix p p 𝕜) ≤ Λ)
    (hgap : eigenvalue A (j + 1) < eigenvalue A j) {x : n → 𝕜} (hx₀ : Wᴴ *ᵥ x = 0)
    (hx : ‖WithLp.toLp 2 x‖ = 1) : RCLike.re (quadForm A x) ≤ eigenvalue A (j + 1) := by
  have hQ := hW.fromCols_replicateCol hx₀ hx
  have hcard : j + 1 + 1 = Fintype.card (p ⊕ Unit) := by
    rw [Fintype.card_sum, hp, Fintype.card_unit]
  have hH := Matrix.isHermitian_conjTranspose_mul_mul
    (Matrix.fromCols W (Matrix.replicateCol Unit x)) hA
  have hle : min (eigenvalue A j) (RCLike.re (quadForm A x)) •
      (1 : Matrix (p ⊕ Unit) (p ⊕ Unit) 𝕜) ≤
      (Matrix.fromCols W (Matrix.replicateCol Unit x))ᴴ * A *
        Matrix.fromCols W (Matrix.replicateCol Unit x) := by
    rw [(isHermitian_real_smul_one _).le_iff_re_quadForm_le hH]
    intro v
    have h₁ := re_quadForm_le_re_quadForm_of_le hΛ (v ∘ Sum.inl)
    rw [re_quadForm_real_smul_one] at h₁
    have h₂ : ‖WithLp.toLp 2 v‖ ^ 2 =
        ‖WithLp.toLp 2 (v ∘ Sum.inl)‖ ^ 2 + ‖v (Sum.inr ())‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq]
    rw [re_quadForm_real_smul_one, quadForm_conjTranspose_mul_mul,
      re_quadForm_fromCols_replicateCol_mulVec hA hW hAW hx₀, h₂, mul_add]
    have h₃ := mul_le_mul_of_nonneg_right
      (min_le_left (eigenvalue A j) (RCLike.re (quadForm A x)))
      (sq_nonneg ‖WithLp.toLp 2 (v ∘ Sum.inl)‖)
    have h₄ := mul_le_mul_of_nonneg_right
      (min_le_right (eigenvalue A j) (RCLike.re (quadForm A x))) (sq_nonneg ‖v (Sum.inr ())‖)
    linarith
  have h₁ := (hH.smul_one_le_iff hcard).mp hle
  have h₂ := hA.eigenvalue_conjTranspose_mul_mul_le hQ (k := j + 1) (by omega)
  rcases min_le_iff.mp (h₁.trans h₂) with h | h
  · exact absurd h (not_le.mpr hgap)
  · exact h

/-- The complement of a leading invariant subspace given by a Loewner bound: if `A * W = W * Λ`
for a frame `W` with `j + 1` columns, `λ_j(A) • 1 ≤ Λ`, and there is a gap
`λ_{j+1}(A) < λ_j(A)`, then on the orthogonal complement `A` is at most `λ_{j+1}(A)`. The gap is
needed: with a repeated eigenvalue the bound on `Λ` does not determine the subspace. -/
theorem one_sub_mul_mul_one_sub_le_of_smul_one_le [DecidableEq n] [DecidableEq p]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {W : Matrix n p 𝕜} {Λ : Matrix p p 𝕜}
    (hW : HasOrthonormalCols W) (hAW : A * W = W * Λ)
    {j : ℕ} (hp : Fintype.card p = j + 1) (hΛ : eigenvalue A j • (1 : Matrix p p 𝕜) ≤ Λ)
    (hgap : eigenvalue A (j + 1) < eigenvalue A j) :
    (1 - W * Wᴴ) * A * (1 - W * Wᴴ) ≤ eigenvalue A (j + 1) • (1 - W * Wᴴ) :=
  one_sub_mul_mul_one_sub_le_of_forall hA hW fun _ hx₀ hx =>
    re_quadForm_le_eigenvalue_of_smul_one_le hA hW hAW hp hΛ hgap hx₀ hx

/-- **Davis–Kahan for a leading eigenspace, residual form.** Let the columns of `W` be
orthonormal eigenvectors of the Hermitian matrix `A` for its `j + 1` largest eigenvalues. For any
pair `(U, L)` with `(λ_{j+1}(A) + δ) • 1 ≤ L`, in every unitarily invariant norm
`δ ‖(1 - W Wᴴ) U‖ ≤ ‖A U - U L‖`.
This is the form used for Ritz pairs: no frame of the complement appears.
[DavisKahan1970]; [StewartSun1990, Theorem V.3.6]; [Parlett1998, Theorem 11.7.1].
Result: davis-kahan -/
theorem SymmetricGauge.mul_matrixNorm_one_sub_mul_le_of_add_smul_one_le [DecidableEq n]
    [DecidableEq p] (Φ : SymmetricGauge) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {j : ℕ}
    {W : Matrix n (Fin (j + 1)) 𝕜} (hW : HasOrthonormalCols W)
    (hAW : A * W = W * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    {U : Matrix n p 𝕜} {L : Matrix p p 𝕜} {δ : ℝ}
    (hL : (eigenvalue A (j + 1) + δ) • (1 : Matrix p p 𝕜) ≤ L) :
    δ * Φ.matrixNorm ((1 - W * Wᴴ) * U) ≤ Φ.matrixNorm (A * U - U * L) := by
  have hQ : IsStarProjection (1 - W * Wᴴ) := hW.isStarProjection_mul_conjTranspose.one_sub
  have hcomm : A * (1 - W * Wᴴ) = (1 - W * Wᴴ) * A := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      hW.mul_conjTranspose_commute_of_mul_eq_mul hA hAW]
  have h := Φ.mul_matrixNorm_mul_le_of_mul_mul_le hQ hcomm
    (one_sub_mul_mul_one_sub_le_of_mul_eq_mul_diagonal hA hW hAW) hL (U := U)
  exact h.trans (Φ.matrixNorm_mul_le_of_isStarProjection hQ _)

/-! ### Two matrices -/

/-- **The `sin Θ` theorem for two Hermitian matrices.** If `A * U = U * L` with the spectrum of
`L` in `[a, b]`, and `B * V = V * M` with `B`, `M` Hermitian and every eigenvalue of `M` outside
`(a - δ, b + δ)`, then `δ ‖Vᴴ U‖ ≤ ‖Vᴴ (B - A) U‖` in every unitarily invariant norm.
[DavisKahan1970]; [Bhatia1997, Theorem VII.3.1].
Result: davis-kahan -/
theorem SymmetricGauge.mul_matrixNorm_conjTranspose_mul_le_of_mul_eq_mul [DecidableEq p]
    (Φ : SymmetricGauge) {A B : Matrix n n 𝕜} {U : Matrix n p 𝕜} {V : Matrix n q 𝕜}
    {L : Matrix p p 𝕜} {M : Matrix q q 𝕜} (hB : B.IsHermitian) (hM : M.IsHermitian)
    (hAU : A * U = U * L) (hBV : B * V = V * M) {a b δ : ℝ}
    (hL₁ : a • (1 : Matrix p p 𝕜) ≤ L) (hL₂ : L ≤ b • (1 : Matrix p p 𝕜))
    (hMsep : ∀ i, i < Fintype.card q → eigenvalue M i ≤ a - δ ∨ b + δ ≤ eigenvalue M i) :
    δ * Φ.matrixNorm (Vᴴ * U) ≤ Φ.matrixNorm (Vᴴ * (B - A) * U) := by
  have h := Φ.mul_matrixNorm_conjTranspose_mul_le_of_eigenvalue hB hM hBV hL₁ hL₂ hMsep (U := U)
  rwa [← hAU, ← Matrix.sub_mul, ← Matrix.mul_assoc] at h

/-- **Davis–Kahan for the leading eigenspaces of `A` and `A + E`.** Let `A` and `E` be
Hermitian, let `U` span an invariant subspace of `A` on which `A` is at least `λ_j(A)`
(`A * U = U * L`, `λ_j(A) • 1 ≤ L`), and let the columns of `U'` be orthonormal eigenvectors of
`A + E` for its `j + 1` largest eigenvalues. If `δ ≤ λ_j(A) - λ_{j+1}(A + E)`, then in every
unitarily invariant norm `δ ‖(1 - U' U'ᴴ) U‖ ≤ ‖E U‖`.
[DavisKahan1970]; [StewartSun1990, Theorem V.3.6].
Port of `NLAlib.sinePrincipalAngles_le_compressed_residual_div_top_gap`, there over `ℝ` with
chosen eigenframes.
Result: davis-kahan -/
theorem SymmetricGauge.mul_matrixNorm_one_sub_mul_le_of_eigenvalue_sub [DecidableEq n]
    [DecidableEq p] (Φ : SymmetricGauge) {A E : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hE : E.IsHermitian) {j : ℕ} {U : Matrix n p 𝕜} {L : Matrix p p 𝕜} (hAU : A * U = U * L)
    (hL : eigenvalue A j • (1 : Matrix p p 𝕜) ≤ L) {U' : Matrix n (Fin (j + 1)) 𝕜}
    (hU' : HasOrthonormalCols U')
    (hAU' : (A + E) * U' =
      U' * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue (A + E) i : ℝ) : 𝕜))
    {δ : ℝ} (hδ : δ ≤ eigenvalue A j - eigenvalue (A + E) (j + 1)) :
    δ * Φ.matrixNorm ((1 - U' * U'ᴴ) * U) ≤ Φ.matrixNorm (E * U) := by
  have hL' : (eigenvalue (A + E) (j + 1) + δ) • (1 : Matrix p p 𝕜) ≤ L :=
    (smul_one_le_smul_one (by linarith)).trans hL
  have h := Φ.mul_matrixNorm_one_sub_mul_le_of_add_smul_one_le (hA.add hE) hU' hAU' hL' (U := U)
  rwa [Matrix.add_mul, hAU, add_sub_cancel_left] at h

end NLAlib
