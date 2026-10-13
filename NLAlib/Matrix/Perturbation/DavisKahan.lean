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
* `NLAlib.specNorm_one_sub_mul_le_two_mul_specNorm_div_eigengap`,
  `NLAlib.frobNorm_one_sub_mul_le_sqrt_two_mul_frobNorm_div_eigengap`: bounds with the gap of the
  unperturbed matrix only.
* `NLAlib.eigengap_mul_frobNorm_one_sub_mul_sq_le`: the variational form, distance to the leading
  eigenspace from the loss of trace.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p q : Type*} [Fintype n] [Fintype p] [Fintype q]
  [DecidableEq n] [DecidableEq p] [DecidableEq q]

/-! ### The residual form -/

/-- The Sylvester identity behind the `sin Θ` theorems: if `A` is Hermitian, `A * V = V * M` and
`M` is Hermitian, then `Vᴴ (A U - U L) = M (Vᴴ U) - (Vᴴ U) L`.
Port of `NLAlib.sylvester_complement_overlap_eq`. -/
theorem conjTranspose_mul_mul_sub_mul_eq {A : Matrix n n 𝕜} {V : Matrix n q 𝕜} {M : Matrix q q 𝕜}
    (hA : A.IsHermitian) (hM : M.IsHermitian) (hAV : A * V = V * M) (U : Matrix n p 𝕜)
    (L : Matrix p p 𝕜) : Vᴴ * (A * U - U * L) = M * (Vᴴ * U) - Vᴴ * U * L := by
  sorry

/-- **The Davis–Kahan `sin Θ` theorem, residual form.** Let `A` be Hermitian with
`A * V = V * M`, `M` Hermitian. If the spectrum of `L` lies in `[a, b]` and every eigenvalue of
`M` lies outside `(a - δ, b + δ)`, then in every unitarily invariant norm
`δ ‖Vᴴ U‖ ≤ ‖Vᴴ (A U - U L)‖`.
[DavisKahan1970]; [Bhatia1997, Theorem VII.3.1]; [StewartSun1990, Theorem V.3.6].
Port of `NLAlib.sinePrincipalAngles_le_compressed_residual_div_of_interval`, there over `ℝ` for
the spectral norm.
Result: davis-kahan -/
theorem SymmetricGauge.mul_matrixNorm_conjTranspose_mul_le_of_eigenvalue (Φ : SymmetricGauge)
    {A : Matrix n n 𝕜} {V : Matrix n q 𝕜} {M : Matrix q q 𝕜} (hA : A.IsHermitian)
    (hM : M.IsHermitian) (hAV : A * V = V * M) {U : Matrix n p 𝕜} {L : Matrix p p 𝕜}
    {a b δ : ℝ} (hL₁ : a • (1 : Matrix p p 𝕜) ≤ L) (hL₂ : L ≤ b • (1 : Matrix p p 𝕜))
    (hMsep : ∀ i, i < Fintype.card q → eigenvalue M i ≤ a - δ ∨ b + δ ≤ eigenvalue M i) :
    δ * Φ.matrixNorm (Vᴴ * U) ≤ Φ.matrixNorm (Vᴴ * (A * U - U * L)) := by
  sorry

/-- The `sin Θ` theorem in residual form with a one-sided separation: `M ≤ (α - δ) • 1` and
`α • 1 ≤ L`. Port of `NLAlib.sinePrincipalAngles_le_compressed_residual_div_of_one_sided_frames`.
Result: davis-kahan -/
theorem SymmetricGauge.mul_matrixNorm_conjTranspose_mul_le_of_le (Φ : SymmetricGauge)
    {A : Matrix n n 𝕜} {V : Matrix n q 𝕜} {M : Matrix q q 𝕜} (hA : A.IsHermitian)
    (hAV : A * V = V * M) {U : Matrix n p 𝕜} {L : Matrix p p 𝕜} {α δ : ℝ}
    (hM : M ≤ (α - δ) • (1 : Matrix q q 𝕜)) (hL : α • (1 : Matrix p p 𝕜) ≤ L) :
    δ * Φ.matrixNorm (Vᴴ * U) ≤ Φ.matrixNorm (Vᴴ * (A * U - U * L)) := by
  sorry

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
  sorry

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
  sorry

/-! ### Projector form -/

/-- **The `sin Θ` theorem, projector form.** Let `A` be Hermitian and `Q` an orthogonal
projector commuting with `A` (the projector onto an invariant subspace) on whose range `A` is at
most `μ`, in the form `Q A Q ≤ μ • Q`. For any pair `(U, L)` with `(μ + δ) • 1 ≤ L`, in every
unitarily invariant norm `δ ‖Q U‖ ≤ ‖Q (A U - U L)‖`. With `Q = 1 - W Wᴴ` for a frame `W` of the
rest of the spectrum, `Q U` is the distance of the range of `U` from the range of `W`.
[DavisKahan1970]; [Bhatia1997, Theorem VII.3.1].
Result: davis-kahan -/
theorem SymmetricGauge.mul_matrixNorm_mul_le_of_mul_mul_le (Φ : SymmetricGauge)
    {A Q : Matrix n n 𝕜} (hA : A.IsHermitian) (hQ : IsStarProjection Q) (hAQ : A * Q = Q * A)
    {μ δ : ℝ} (hQA : Q * A * Q ≤ μ • Q) {U : Matrix n p 𝕜} {L : Matrix p p 𝕜}
    (hL : (μ + δ) • (1 : Matrix p p 𝕜) ≤ L) :
    δ * Φ.matrixNorm (Q * U) ≤ Φ.matrixNorm (Q * (A * U - U * L)) := by
  sorry

/-- The projector form with the invariant subspace above the Ritz block: `μ • Q ≤ Q A Q` and
`L ≤ (μ - δ) • 1`. -/
theorem SymmetricGauge.mul_matrixNorm_mul_le_of_le_mul_mul (Φ : SymmetricGauge)
    {A Q : Matrix n n 𝕜} (hA : A.IsHermitian) (hQ : IsStarProjection Q) (hAQ : A * Q = Q * A)
    {μ δ : ℝ} (hQA : μ • Q ≤ Q * A * Q) {U : Matrix n p 𝕜} {L : Matrix p p 𝕜}
    (hL : L ≤ (μ - δ) • (1 : Matrix p p 𝕜)) :
    δ * Φ.matrixNorm (Q * U) ≤ Φ.matrixNorm (Q * (A * U - U * L)) := by
  sorry

/-! ### Leading eigenspaces -/

/-- The projector onto an invariant subspace of a Hermitian matrix commutes with it. -/
theorem HasOrthonormalCols.mul_conjTranspose_commute_of_mul_eq_mul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {W : Matrix n p 𝕜} {M : Matrix p p 𝕜} (hW : HasOrthonormalCols W)
    (hAW : A * W = W * M) : A * (W * Wᴴ) = W * Wᴴ * A := by
  sorry

/-- **The complement of a leading eigenframe.** If the columns of `W` are orthonormal
eigenvectors of the Hermitian matrix `A` for its `j + 1` largest eigenvalues, then on the
orthogonal complement `A` is at most `λ_{j+1}(A)`. This holds with repeated eigenvalues. -/
theorem one_sub_mul_mul_one_sub_le_of_mul_eq_mul_diagonal {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {j : ℕ} {W : Matrix n (Fin (j + 1)) 𝕜} (hW : HasOrthonormalCols W)
    (hAW : A * W = W * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜)) :
    (1 - W * Wᴴ) * A * (1 - W * Wᴴ) ≤ eigenvalue A (j + 1) • (1 - W * Wᴴ) := by
  sorry

/-- The complement of a leading invariant subspace given by a Loewner bound: if `A * W = W * Λ`
for a frame `W` with `j + 1` columns, `λ_j(A) • 1 ≤ Λ`, and there is a gap
`λ_{j+1}(A) < λ_j(A)`, then on the orthogonal complement `A` is at most `λ_{j+1}(A)`. The gap is
needed: with a repeated eigenvalue the bound on `Λ` does not determine the subspace. -/
theorem one_sub_mul_mul_one_sub_le_of_smul_one_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {W : Matrix n p 𝕜} {Λ : Matrix p p 𝕜} (hW : HasOrthonormalCols W) (hAW : A * W = W * Λ)
    {j : ℕ} (hp : Fintype.card p = j + 1) (hΛ : eigenvalue A j • (1 : Matrix p p 𝕜) ≤ Λ)
    (hgap : eigenvalue A (j + 1) < eigenvalue A j) :
    (1 - W * Wᴴ) * A * (1 - W * Wᴴ) ≤ eigenvalue A (j + 1) • (1 - W * Wᴴ) := by
  sorry

/-- **Davis–Kahan for a leading eigenspace, residual form.** Let the columns of `W` be
orthonormal eigenvectors of the Hermitian matrix `A` for its `j + 1` largest eigenvalues. For any
pair `(U, L)` with `(λ_{j+1}(A) + δ) • 1 ≤ L`, in every unitarily invariant norm
`δ ‖(1 - W Wᴴ) U‖ ≤ ‖A U - U L‖`.
This is the form used for Ritz pairs: no frame of the complement appears.
[DavisKahan1970]; [StewartSun1990, Theorem V.3.6]; [Parlett1998, Theorem 11.7.1].
Result: davis-kahan -/
theorem SymmetricGauge.mul_matrixNorm_one_sub_mul_le_of_add_smul_one_le (Φ : SymmetricGauge)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {j : ℕ} {W : Matrix n (Fin (j + 1)) 𝕜}
    (hW : HasOrthonormalCols W)
    (hAW : A * W = W * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    {U : Matrix n p 𝕜} {L : Matrix p p 𝕜} {δ : ℝ}
    (hL : (eigenvalue A (j + 1) + δ) • (1 : Matrix p p 𝕜) ≤ L) :
    δ * Φ.matrixNorm ((1 - W * Wᴴ) * U) ≤ Φ.matrixNorm (A * U - U * L) := by
  sorry

/-! ### Two matrices -/

/-- **The `sin Θ` theorem for two Hermitian matrices.** If `A * U = U * L` with the spectrum of
`L` in `[a, b]`, and `B * V = V * M` with `B`, `M` Hermitian and every eigenvalue of `M` outside
`(a - δ, b + δ)`, then `δ ‖Vᴴ U‖ ≤ ‖Vᴴ (B - A) U‖` in every unitarily invariant norm.
[DavisKahan1970]; [Bhatia1997, Theorem VII.3.1].
Result: davis-kahan -/
theorem SymmetricGauge.mul_matrixNorm_conjTranspose_mul_le_of_mul_eq_mul (Φ : SymmetricGauge)
    {A B : Matrix n n 𝕜} {U : Matrix n p 𝕜} {V : Matrix n q 𝕜} {L : Matrix p p 𝕜}
    {M : Matrix q q 𝕜} (hB : B.IsHermitian) (hM : M.IsHermitian) (hAU : A * U = U * L)
    (hBV : B * V = V * M) {a b δ : ℝ} (hL₁ : a • (1 : Matrix p p 𝕜) ≤ L)
    (hL₂ : L ≤ b • (1 : Matrix p p 𝕜))
    (hMsep : ∀ i, i < Fintype.card q → eigenvalue M i ≤ a - δ ∨ b + δ ≤ eigenvalue M i) :
    δ * Φ.matrixNorm (Vᴴ * U) ≤ Φ.matrixNorm (Vᴴ * (B - A) * U) := by
  sorry

/-- **Davis–Kahan for the leading eigenspaces of `A` and `A + E`.** Let `A` and `E` be
Hermitian, let `U` span an invariant subspace of `A` on which `A` is at least `λ_j(A)`
(`A * U = U * L`, `λ_j(A) • 1 ≤ L`), and let the columns of `U'` be orthonormal eigenvectors of
`A + E` for its `j + 1` largest eigenvalues. If `δ ≤ λ_j(A) - λ_{j+1}(A + E)`, then in every
unitarily invariant norm `δ ‖(1 - U' U'ᴴ) U‖ ≤ ‖E U‖`.
[DavisKahan1970]; [StewartSun1990, Theorem V.3.6].
Port of `NLAlib.sinePrincipalAngles_le_compressed_residual_div_top_gap`, there over `ℝ` with
chosen eigenframes.
Result: davis-kahan -/
theorem SymmetricGauge.mul_matrixNorm_one_sub_mul_le_of_eigenvalue_sub (Φ : SymmetricGauge)
    {A E : Matrix n n 𝕜} (hA : A.IsHermitian) (hE : E.IsHermitian) {j : ℕ}
    {U : Matrix n p 𝕜} {L : Matrix p p 𝕜} (hAU : A * U = U * L)
    (hL : eigenvalue A j • (1 : Matrix p p 𝕜) ≤ L) {U' : Matrix n (Fin (j + 1)) 𝕜}
    (hU' : HasOrthonormalCols U')
    (hAU' : (A + E) * U' =
      U' * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue (A + E) i : ℝ) : 𝕜))
    {δ : ℝ} (hδ : δ ≤ eigenvalue A j - eigenvalue (A + E) (j + 1)) :
    δ * Φ.matrixNorm ((1 - U' * U'ᴴ) * U) ≤ Φ.matrixNorm (E * U) := by
  sorry

/-- **Davis–Kahan with the gap of the unperturbed matrix**, spectral norm. For leading
eigenframes `U` of `A` and `U'` of `A + E`, both with `j + 1` columns,
`‖(1 - U Uᴴ) U'‖₂ ≤ 2 ‖E‖₂ / (λ_j(A) - λ_{j+1}(A))`. The two frames have the same number of
columns, so the distance is symmetric in them
(`IsStarProjection.singularValues_one_sub_mul_eq_of_rank_eq`).
[YuWangSamworth2015, Theorem 2 context].
Port of `NLAlib.specNorm_sinePrincipalAngles_le_two_mul_specNorm_div_population_gap`.
Result: davis-kahan -/
theorem specNorm_one_sub_mul_le_two_mul_specNorm_div_eigengap {A E : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {j : ℕ} {U U' : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hU' : HasOrthonormalCols U')
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    (hAU' : (A + E) * U' =
      U' * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue (A + E) i : ℝ) : 𝕜))
    (hgap : 0 < eigengap A (j + 1)) :
    specNorm ((1 - U * Uᴴ) * U') ≤ 2 * specNorm E / eigengap A (j + 1) := by
  sorry

/-! ### The variational form -/

/-- **Distance to the leading eigenspace from the loss of trace.** Let the columns of `U` be
orthonormal eigenvectors of the Hermitian matrix `A` for its `j + 1` largest eigenvalues. For any
frame `Q` with `j + 1` columns,
`(λ_j - λ_{j+1}) ‖(1 - U Uᴴ) Q‖_F² ≤ ∑_{i ≤ j} λ_i - re tr (Qᴴ A Q)`.
This turns a near-optimal value of the Rayleigh trace into closeness of subspaces.
Port of `NLAlib.mul_frobSq_sinePrincipalAngles_le_trace_deficit`, there over `ℝ`. -/
theorem eigengap_mul_frobNorm_one_sub_mul_sq_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) {j : ℕ}
    {U Q : Matrix n (Fin (j + 1)) 𝕜} (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q)
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜)) :
    eigengap A (j + 1) * frobNorm ((1 - U * Uᴴ) * Q) ^ 2 ≤
      ∑ i ∈ Finset.range (j + 1), eigenvalue A i - RCLike.re (Qᴴ * A * Q).trace := by
  sorry

/-- The variational form for a perturbation: if `Q` attains the largest Rayleigh trace of
`A + E` among frames with `j + 1` columns, then
`(λ_j(A) - λ_{j+1}(A)) ‖(1 - U Uᴴ) Q‖_F² ≤ ⟨Q Qᴴ - U Uᴴ, E⟩_F`.
Port of `NLAlib.mul_frobSq_sinePrincipalAngles_le_frobInner_perturbation`, there over `ℝ`. -/
theorem eigengap_mul_frobNorm_one_sub_mul_sq_le_frobInner {A E : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {j : ℕ} {U Q : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q)
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    (hQtop : RCLike.re (Qᴴ * (A + E) * Q).trace =
      ∑ i ∈ Finset.range (j + 1), eigenvalue (A + E) i) :
    eigengap A (j + 1) * frobNorm ((1 - U * Uᴴ) * Q) ^ 2 ≤ frobInner (Q * Qᴴ - U * Uᴴ) E := by
  sorry

/-- **Davis–Kahan with the gap of the unperturbed matrix**, Frobenius norm:
`‖(1 - U Uᴴ) Q‖_F ≤ √2 ‖E‖_F / (λ_j(A) - λ_{j+1}(A))`.
[YuWangSamworth2015, Theorem 2].
Port of `NLAlib.frobNorm_sinePrincipalAngles_le_two_mul_min_div_population_gap`.
Result: davis-kahan -/
theorem frobNorm_one_sub_mul_le_sqrt_two_mul_frobNorm_div_eigengap {A E : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {j : ℕ} {U Q : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q)
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    (hQtop : RCLike.re (Qᴴ * (A + E) * Q).trace =
      ∑ i ∈ Finset.range (j + 1), eigenvalue (A + E) i)
    (hgap : 0 < eigengap A (j + 1)) :
    frobNorm ((1 - U * Uᴴ) * Q) ≤ √2 * frobNorm E / eigengap A (j + 1) := by
  sorry

/-- Davis–Kahan with the gap of the unperturbed matrix, Frobenius norm of the angles against the
spectral norm of the perturbation:
`‖(1 - U Uᴴ) Q‖_F ≤ 2 √(j + 1) ‖E‖₂ / (λ_j(A) - λ_{j+1}(A))`.
[YuWangSamworth2015, Theorem 2]. -/
theorem frobNorm_one_sub_mul_le_two_mul_sqrt_mul_specNorm_div_eigengap {A E : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {j : ℕ} {U Q : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q)
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    (hQtop : RCLike.re (Qᴴ * (A + E) * Q).trace =
      ∑ i ∈ Finset.range (j + 1), eigenvalue (A + E) i)
    (hgap : 0 < eigengap A (j + 1)) :
    frobNorm ((1 - U * Uᴴ) * Q) ≤ 2 * √((j : ℝ) + 1) * specNorm E / eigengap A (j + 1) := by
  sorry

end NLAlib
