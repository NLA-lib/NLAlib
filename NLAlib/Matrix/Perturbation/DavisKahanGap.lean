/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.DavisKahan
public import NLAlib.Matrix.Subspaces.ProjectorPair

/-!
# Davis–Kahan bounds with the gap of the unperturbed matrix

The `sin Θ` theorems of `NLAlib.Matrix.Perturbation.DavisKahan` separate the spectrum of `A` on
one subspace from the spectrum of `A + E` on the other. Here the leading eigenspaces of `A` and
of `A + E` are compared using only `NLAlib.eigengap A (j + 1) = λ_j(A) - λ_{j+1}(A)`, the form in
which the theorem is used in statistics.

In the spectral norm this follows from the `sin Θ` theorem and Weyl's inequality. In the Frobenius
norm it follows from a variational argument: the distance from a frame `Q` to the leading
eigenspace of `A` is controlled by how much Rayleigh trace `Q` loses, and a frame that is at
least as good as the leading eigenframe of `A` for `A + E` loses at most `⟨Q Qᴴ - U Uᴴ, E⟩`. That
argument uses of `Q` only the comparison of the two Rayleigh traces of `A + E`, so it applies to
approximate leading frames and to `E` that is not Hermitian.

## Main results

* `NLAlib.specNorm_one_sub_mul_le_two_mul_specNorm_div_eigengap`: the spectral norm bound.
* `NLAlib.eigengap_mul_frobNorm_one_sub_mul_sq_le`: the variational form, distance to the leading
  eigenspace from the loss of trace.
* `NLAlib.eigengap_mul_frobNorm_one_sub_mul_sq_le_frobInner_of_re_trace_le`: the variational form
  for a perturbation.
* `NLAlib.frobNorm_one_sub_mul_le_sqrt_two_mul_frobNorm_div_eigengap_of_re_trace_le`,
  `NLAlib.frobNorm_one_sub_mul_le_two_mul_sqrt_mul_specNorm_div_eigengap_of_re_trace_le`: the
  Frobenius norm bounds for a frame whose Rayleigh trace is at least that of the leading
  eigenframe.
* `NLAlib.frobNorm_one_sub_mul_le_sqrt_two_mul_frobNorm_div_eigengap`,
  `NLAlib.frobNorm_one_sub_mul_le_two_mul_sqrt_mul_specNorm_div_eigengap`: the same for a frame
  attaining the largest Rayleigh trace of `A + E`.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p q : Type*} [Fintype n] [Fintype p] [Fintype q]

/-! ### The spectral norm -/

/-- **Davis–Kahan with the gap of the unperturbed matrix**, spectral norm. For leading
eigenframes `U` of `A` and `U'` of `A + E`, both with `j + 1` columns,
`‖(1 - U Uᴴ) U'‖₂ ≤ 2 ‖E‖₂ / (λ_j(A) - λ_{j+1}(A))`. The two frames have the same number of
columns, so the distance is symmetric in them
(`IsStarProjection.singularValues_one_sub_mul_eq_of_rank_eq`).
[YuWangSamworth2015, Theorem 2 context].
Port of `NLAlib.specNorm_sinePrincipalAngles_le_two_mul_specNorm_div_population_gap`.
Result: davis-kahan -/
theorem specNorm_one_sub_mul_le_two_mul_specNorm_div_eigengap [DecidableEq n] {A E : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {j : ℕ} {U U' : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hU' : HasOrthonormalCols U')
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    (hAU' : (A + E) * U' =
      U' * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue (A + E) i : ℝ) : 𝕜))
    (hgap : 0 < eigengap A (j + 1)) :
    specNorm ((1 - U * Uᴴ) * U') ≤ 2 * specNorm E / eigengap A (j + 1) := by
  rw [eigengap_succ] at hgap ⊢
  have hQ : IsStarProjection (1 - U * Uᴴ) := hU.isStarProjection_mul_conjTranspose.one_sub
  have hs₁ : specNorm ((1 - U * Uᴴ) * U') ≤ 1 := (hQ.specNorm_mul_le U').trans hU'.specNorm_le_one
  have hs₀ := specNorm_nonneg ((1 - U * Uᴴ) * U')
  have hE₀ := specNorm_nonneg E
  rw [le_div_iff₀ hgap]
  rcases le_or_gt (eigenvalue A j - eigenvalue A (j + 1)) (2 * specNorm E) with h | h
  · nlinarith
  have hj : j < Fintype.card n := by
    have := hU.card_le
    rw [Fintype.card_fin] at this
    omega
  have hw := (abs_le.mp (abs_eigenvalue_sub_le hA (hA.add hE) j)).2
  rw [sub_add_cancel_left, specNorm_neg] at hw
  have hL : (eigenvalue A (j + 1) + (eigenvalue A j - eigenvalue A (j + 1) - specNorm E)) •
      (1 : Matrix (Fin (j + 1)) (Fin (j + 1)) 𝕜) ≤
      Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue (A + E) i : ℝ) : 𝕜) :=
    smul_one_le_diagonal_iff.mpr fun i => by
      have := (hA.add hE).eigenvalue_le_eigenvalue (Nat.lt_succ_iff.mp i.2) hj
      linarith
  have h' := (lpGauge ⊤ le_top).mul_matrixNorm_one_sub_mul_le_of_add_smul_one_le hA hU hAU hL
    (U := U')
  rw [lpGauge_top_matrixNorm, lpGauge_top_matrixNorm, ← hAU', Matrix.add_mul,
    sub_add_cancel_left, specNorm_neg] at h'
  have hEU : specNorm (E * U') ≤ specNorm E :=
    (specNorm_mul_le E U').trans (mul_le_of_le_one_right hE₀ hU'.specNorm_le_one)
  nlinarith

/-! ### The variational form -/

omit [Fintype n] in
/-- A positive semidefinite matrix weighted by a diagonal matrix with entries at least `c` has
trace at least `c` times its own. -/
private theorem mul_re_trace_le_re_trace_diagonal_mul [DecidableEq p] {d : p → ℝ} {c : ℝ}
    (hd : ∀ i, c ≤ d i) {G : Matrix p p 𝕜} (hG : G.PosSemidef) :
    c * RCLike.re G.trace ≤ RCLike.re ((Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) * G).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, map_sum, RCLike.re_ofReal_mul,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hd i) (RCLike.nonneg_iff.mp hG.diag_nonneg).1

/-- The distance between two frames with the same number of columns is symmetric. -/
private theorem frobNorm_one_sub_mul_comm [DecidableEq n] [DecidableEq p] {U Q : Matrix n p 𝕜}
    (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q) :
    frobNorm ((1 - Q * Qᴴ) * U) = frobNorm ((1 - U * Uᴴ) * Q) := by
  rw [← sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _), hU.frobNorm_one_sub_mul_sq hQ,
    hQ.frobNorm_one_sub_mul_sq hU, ← frobNorm_conjTranspose (Uᴴ * Q), Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

/-- The part of the trace deficit carried by the leading block: a diagonal block with entries at
least `c` loses at least `c` times the squared distance. -/
private theorem mul_card_sub_frobNorm_sq_le [DecidableEq p] [DecidableEq q] {U : Matrix n p 𝕜}
    {Q : Matrix n q 𝕜} (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q) {d : p → ℝ}
    {c : ℝ} (hd : ∀ i, c ≤ d i) :
    c * (Fintype.card p - frobNorm (Qᴴ * U) ^ 2) ≤ ∑ i, d i -
      RCLike.re (Qᴴ * (U * (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) * Q).trace := by
  classical
  have hG : (Uᴴ * (1 - Q * Qᴴ) * U).PosSemidef :=
    hQ.isStarProjection_mul_conjTranspose.one_sub.posSemidef.conjTranspose_mul_mul_same U
  have h := mul_re_trace_le_re_trace_diagonal_mul hd hG
  have e₁ : Uᴴ * (1 - Q * Qᴴ) * U = 1 - (Qᴴ * U)ᴴ * (Qᴴ * U) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU.conjTranspose_mul_self,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have e₂ : ((Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) * ((Qᴴ * U)ᴴ * (Qᴴ * U))).trace =
      (Qᴴ * (U * (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) * Q).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e₁, Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_sub, e₂,
    Matrix.trace_one, map_sub, map_sub, RCLike.natCast_re, ← frobNorm_sq_eq_re_trace,
    Matrix.trace_diagonal, ← RCLike.ofReal_sum, RCLike.ofReal_re] at h
  exact h

/-- The part of the trace deficit carried by the complement: a matrix that is at most `μ` on the
range of an orthogonal projector `R` has compressed trace at most `μ ‖R Q‖_F²`. -/
private theorem re_trace_conjTranspose_mul_mul_le_mul_frobNorm_sq {N R : Matrix n n 𝕜}
    (hR : IsStarProjection R) {μ : ℝ} (h : N ≤ μ • R) (Q : Matrix n p 𝕜) :
    RCLike.re (Qᴴ * N * Q).trace ≤ μ * frobNorm (R * Q) ^ 2 := by
  have h' := conjTranspose_mul_mul_le_conjTranspose_mul_mul h Q
  rw [Matrix.le_iff] at h'
  have ht := (RCLike.nonneg_iff.mp h'.trace_nonneg).1
  rw [Matrix.trace_sub, map_sub, sub_nonneg] at ht
  refine ht.trans (le_of_eq ?_)
  rw [frobNorm_sq_eq_re_trace, Matrix.conjTranspose_mul, hR.conjTranspose_eq,
    Matrix.mul_assoc Qᴴ R, ← Matrix.mul_assoc R R, hR.mul_self, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_smul, RCLike.smul_re, ← Matrix.mul_assoc]

/-- **Distance to the leading eigenspace from the loss of trace.** Let the columns of `U` be
orthonormal eigenvectors of the Hermitian matrix `A` for its `j + 1` largest eigenvalues. For any
frame `Q` with `j + 1` columns,
`(λ_j - λ_{j+1}) ‖(1 - U Uᴴ) Q‖_F² ≤ ∑_{i ≤ j} λ_i - re tr (Qᴴ A Q)`.
This turns a near-optimal value of the Rayleigh trace into closeness of subspaces.
Port of `NLAlib.mul_frobSq_sinePrincipalAngles_le_trace_deficit`, there over `ℝ`. -/
theorem eigengap_mul_frobNorm_one_sub_mul_sq_le [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {j : ℕ} {U Q : Matrix n (Fin (j + 1)) 𝕜} (hU : HasOrthonormalCols U)
    (hQ : HasOrthonormalCols Q)
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜)) :
    eigengap A (j + 1) * frobNorm ((1 - U * Uᴴ) * Q) ^ 2 ≤
      ∑ i ∈ Finset.range (j + 1), eigenvalue A i - RCLike.re (Qᴴ * A * Q).trace := by
  have hj : j < Fintype.card n := by
    have := hU.card_le
    rw [Fintype.card_fin] at this
    omega
  have hR : IsStarProjection (1 - U * Uᴴ) := hU.isStarProjection_mul_conjTranspose.one_sub
  have h₁ := mul_card_sub_frobNorm_sq_le hU hQ (d := fun i : Fin (j + 1) => eigenvalue A i)
    (c := eigenvalue A j) fun i => hA.eigenvalue_le_eigenvalue (Nat.lt_succ_iff.mp i.2) hj
  have h₂ := re_trace_conjTranspose_mul_mul_le_mul_frobNorm_sq hR
    (one_sub_mul_mul_one_sub_le_of_mul_eq_mul_diagonal hA hU hAU) Q
  have hs := hU.frobNorm_one_sub_mul_sq hQ
  have hN : (1 - U * Uᴴ) * A * (1 - U * Uᴴ) = A -
      U * (Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜)) * Uᴴ := by
    have e : A - U * Uᴴ * A = (1 - U * Uᴴ) * A := by rw [Matrix.sub_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_sub A, Matrix.mul_one,
      hU.mul_conjTranspose_commute_of_mul_eq_mul hA hAU, e, ← Matrix.mul_assoc, hR.mul_self, ← e,
      ← hU.mul_conjTranspose_commute_of_mul_eq_mul hA hAU, ← Matrix.mul_assoc, hAU]
  have htr : RCLike.re (Qᴴ * A * Q).trace =
      RCLike.re (Qᴴ * (U * (Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜)) *
        Uᴴ) * Q).trace + RCLike.re (Qᴴ * ((1 - U * Uᴴ) * A * (1 - U * Uᴴ)) * Q).trace := by
    rw [← map_add, ← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.mul_add, hN, add_sub_cancel]
  rw [Fintype.card_fin] at h₁ hs
  push_cast at h₁ hs
  rw [Fin.sum_univ_eq_sum_range (fun i => eigenvalue A i) (j + 1)] at h₁
  rw [hs] at h₂
  rw [eigengap_succ, htr, hs]
  linarith

/-- The pairing of a frame projector with a matrix is the trace of the compression. -/
private theorem frobInner_mul_conjTranspose_self (X : Matrix n p 𝕜) (E : Matrix n n 𝕜) :
    frobInner (X * Xᴴ) E = RCLike.re (Xᴴ * E * X).trace := by
  rw [frobInner_eq_re_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, Matrix.trace_mul_comm]

/-- **The variational form for a perturbation.** If the Rayleigh trace of `A + E` on the frame
`Q` is at least its Rayleigh trace on the leading eigenframe `U` of `A`, then
`(λ_j(A) - λ_{j+1}(A)) ‖(1 - U Uᴴ) Q‖_F² ≤ ⟨Q Qᴴ - U Uᴴ, E⟩_F`. Nothing is assumed of `E`, and `Q`
need not be an eigenframe of `A + E`.
Port of `NLAlib.mul_frobSq_sinePrincipalAngles_le_frobInner_perturbation`, there over `ℝ` for a
frame attaining the largest Rayleigh trace. -/
theorem eigengap_mul_frobNorm_one_sub_mul_sq_le_frobInner_of_re_trace_le [DecidableEq n]
    {A E : Matrix n n 𝕜} (hA : A.IsHermitian) {j : ℕ} {U Q : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q)
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    (hUQ : RCLike.re (Uᴴ * (A + E) * U).trace ≤ RCLike.re (Qᴴ * (A + E) * Q).trace) :
    eigengap A (j + 1) * frobNorm ((1 - U * Uᴴ) * Q) ^ 2 ≤ frobInner (Q * Qᴴ - U * Uᴴ) E := by
  have h := eigengap_mul_frobNorm_one_sub_mul_sq_le hA hU hQ hAU
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
    Matrix.trace_add, map_add, map_add] at hUQ
  have hUA : RCLike.re (Uᴴ * A * U).trace = ∑ i ∈ Finset.range (j + 1), eigenvalue A i := by
    rw [Matrix.mul_assoc, hAU, ← Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.one_mul,
      Matrix.trace_diagonal, ← RCLike.ofReal_sum, RCLike.ofReal_re,
      Fin.sum_univ_eq_sum_range (fun i => eigenvalue A i) (j + 1)]
  rw [frobInner_sub_left, frobInner_mul_conjTranspose_self, frobInner_mul_conjTranspose_self]
  linarith

/-- A frame attaining the largest Rayleigh trace of a Hermitian matrix has Rayleigh trace at least
that of any other frame with as many columns (Ky Fan's maximum principle). -/
private theorem re_trace_le_re_trace_of_eq_sum {B : Matrix n n 𝕜} (hB : B.IsHermitian) {j : ℕ}
    {U Q : Matrix n (Fin (j + 1)) 𝕜} (hU : HasOrthonormalCols U)
    (hQtop : RCLike.re (Qᴴ * B * Q).trace = ∑ i ∈ Finset.range (j + 1), eigenvalue B i) :
    RCLike.re (Uᴴ * B * U).trace ≤ RCLike.re (Qᴴ * B * Q).trace := by
  have hKF := hB.re_trace_conjTranspose_mul_mul_le_sum_eigenvalue hU
  rwa [Fintype.card_fin, ← hQtop] at hKF

/-- The variational form for a perturbation: if `Q` attains the largest Rayleigh trace of
`A + E` among frames with `j + 1` columns, then
`(λ_j(A) - λ_{j+1}(A)) ‖(1 - U Uᴴ) Q‖_F² ≤ ⟨Q Qᴴ - U Uᴴ, E⟩_F`.
Port of `NLAlib.mul_frobSq_sinePrincipalAngles_le_frobInner_perturbation`, there over `ℝ`. -/
theorem eigengap_mul_frobNorm_one_sub_mul_sq_le_frobInner [DecidableEq n] {A E : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {j : ℕ} {U Q : Matrix n (Fin (j + 1)) 𝕜}
    (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q)
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    (hQtop : RCLike.re (Qᴴ * (A + E) * Q).trace =
      ∑ i ∈ Finset.range (j + 1), eigenvalue (A + E) i) :
    eigengap A (j + 1) * frobNorm ((1 - U * Uᴴ) * Q) ^ 2 ≤ frobInner (Q * Qᴴ - U * Uᴴ) E :=
  eigengap_mul_frobNorm_one_sub_mul_sq_le_frobInner_of_re_trace_le hA hU hQ hAU
    (re_trace_le_re_trace_of_eq_sum (hA.add hE) hU hQtop)

/-- From `g s² ≤ C s` to `s ≤ C / g`. -/
private theorem le_div_of_mul_sq_le_mul {g s C : ℝ} (hg : 0 < g) (hs : 0 ≤ s) (hC : 0 ≤ C)
    (h : g * s ^ 2 ≤ C * s) : s ≤ C / g := by
  rw [le_div_iff₀ hg]
  rcases hs.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    exact hC
  · refine le_of_mul_le_mul_left ?_ hpos
    linarith

/-- The pairing of the difference of two frame projectors with `E` is at most
`2 √p ‖E‖₂ ‖(1 - U Uᴴ) Q‖_F`, for frames with `p` columns. -/
private theorem frobInner_mul_conjTranspose_sub_le [DecidableEq n] [DecidableEq p]
    {U Q : Matrix n p 𝕜} (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q)
    (E : Matrix n n 𝕜) :
    frobInner (Q * Qᴴ - U * Uᴴ) E ≤
      2 * √(Fintype.card p) * specNorm E * frobNorm ((1 - U * Uᴴ) * Q) := by
  have hRQ : IsStarProjection (1 - Q * Qᴴ) := hQ.isStarProjection_mul_conjTranspose.one_sub
  have e : Q * Qᴴ - U * Uᴴ = (1 - U * Uᴴ) * Q * Qᴴ - U * (Uᴴ * (1 - Q * Qᴴ)) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_sub,
      Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
    abel
  have hfU : frobNorm U = √(Fintype.card p) := by
    rw [← hU.frobNorm_sq, Real.sqrt_sq (frobNorm_nonneg U)]
  have hfQ : frobNorm Q = √(Fintype.card p) := by
    rw [← hQ.frobNorm_sq, Real.sqrt_sq (frobNorm_nonneg Q)]
  have h₁ : frobInner ((1 - U * Uᴴ) * Q * Qᴴ) E ≤
      frobNorm ((1 - U * Uᴴ) * Q) * (specNorm E * √(Fintype.card p)) := by
    rw [frobInner_mul_right, Matrix.conjTranspose_conjTranspose, ← hfQ]
    exact (frobInner_le _ _).trans (mul_le_mul_of_nonneg_left
      (frobNorm_mul_le_specNorm_mul_frobNorm E Q) (frobNorm_nonneg _))
  have h₂ : -frobInner (U * (Uᴴ * (1 - Q * Qᴴ))) E ≤
      frobNorm ((1 - U * Uᴴ) * Q) * (√(Fintype.card p) * specNorm E) := by
    have hn : frobNorm (Uᴴ * (1 - Q * Qᴴ)) = frobNorm ((1 - U * Uᴴ) * Q) := by
      rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hRQ.conjTranspose_eq, frobNorm_one_sub_mul_comm hU hQ]
    rw [frobInner_mul_left, ← hn, ← hfU, ← frobNorm_conjTranspose U]
    exact (neg_le_abs _).trans ((abs_frobInner_le _ _).trans (mul_le_mul_of_nonneg_left
      (frobNorm_mul_le_frobNorm_mul_specNorm Uᴴ E) (frobNorm_nonneg _)))
  rw [e, frobInner_sub_left]
  linarith

/-- **Davis–Kahan with the gap of the unperturbed matrix**, Frobenius norm, for a frame `Q`
whose Rayleigh trace for `A + E` is at least that of the leading eigenframe `U` of `A`:
`‖(1 - U Uᴴ) Q‖_F ≤ √2 ‖E‖_F / (λ_j(A) - λ_{j+1}(A))`.
[YuWangSamworth2015, Theorem 2], there for a leading eigenframe of a Hermitian `A + E`.
Result: davis-kahan -/
theorem frobNorm_one_sub_mul_le_sqrt_two_mul_frobNorm_div_eigengap_of_re_trace_le
    [DecidableEq n] {A E : Matrix n n 𝕜} (hA : A.IsHermitian) {j : ℕ}
    {U Q : Matrix n (Fin (j + 1)) 𝕜} (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q)
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    (hUQ : RCLike.re (Uᴴ * (A + E) * U).trace ≤ RCLike.re (Qᴴ * (A + E) * Q).trace)
    (hgap : 0 < eigengap A (j + 1)) :
    frobNorm ((1 - U * Uᴴ) * Q) ≤ √2 * frobNorm E / eigengap A (j + 1) := by
  have h := eigengap_mul_frobNorm_one_sub_mul_sq_le_frobInner_of_re_trace_le hA hU hQ hAU hUQ
  have hcs := frobInner_le (Q * Qᴴ - U * Uᴴ) E
  rw [hU.frobNorm_mul_conjTranspose_sub_mul_conjTranspose hQ] at hcs
  refine le_div_of_mul_sq_le_mul hgap (frobNorm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg 2) (frobNorm_nonneg E)) ?_
  linarith

/-- **Davis–Kahan with the gap of the unperturbed matrix**, Frobenius norm:
`‖(1 - U Uᴴ) Q‖_F ≤ √2 ‖E‖_F / (λ_j(A) - λ_{j+1}(A))`.
[YuWangSamworth2015, Theorem 2].
Port of `NLAlib.frobNorm_sinePrincipalAngles_le_two_mul_min_div_population_gap`.
Result: davis-kahan -/
theorem frobNorm_one_sub_mul_le_sqrt_two_mul_frobNorm_div_eigengap [DecidableEq n]
    {A E : Matrix n n 𝕜} (hA : A.IsHermitian) (hE : E.IsHermitian) {j : ℕ}
    {U Q : Matrix n (Fin (j + 1)) 𝕜} (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q)
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    (hQtop : RCLike.re (Qᴴ * (A + E) * Q).trace =
      ∑ i ∈ Finset.range (j + 1), eigenvalue (A + E) i)
    (hgap : 0 < eigengap A (j + 1)) :
    frobNorm ((1 - U * Uᴴ) * Q) ≤ √2 * frobNorm E / eigengap A (j + 1) :=
  frobNorm_one_sub_mul_le_sqrt_two_mul_frobNorm_div_eigengap_of_re_trace_le hA hU hQ hAU
    (re_trace_le_re_trace_of_eq_sum (hA.add hE) hU hQtop) hgap

/-- Davis–Kahan with the gap of the unperturbed matrix, Frobenius norm of the angles against the
spectral norm of the perturbation, for a frame `Q` whose Rayleigh trace for `A + E` is at least
that of the leading eigenframe `U` of `A`:
`‖(1 - U Uᴴ) Q‖_F ≤ 2 √(j + 1) ‖E‖₂ / (λ_j(A) - λ_{j+1}(A))`.
[YuWangSamworth2015, Theorem 2], there for a leading eigenframe of a Hermitian `A + E`. -/
theorem frobNorm_one_sub_mul_le_two_mul_sqrt_mul_specNorm_div_eigengap_of_re_trace_le
    [DecidableEq n] {A E : Matrix n n 𝕜} (hA : A.IsHermitian) {j : ℕ}
    {U Q : Matrix n (Fin (j + 1)) 𝕜} (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q)
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    (hUQ : RCLike.re (Uᴴ * (A + E) * U).trace ≤ RCLike.re (Qᴴ * (A + E) * Q).trace)
    (hgap : 0 < eigengap A (j + 1)) :
    frobNorm ((1 - U * Uᴴ) * Q) ≤ 2 * √((j : ℝ) + 1) * specNorm E / eigengap A (j + 1) := by
  have h := eigengap_mul_frobNorm_one_sub_mul_sq_le_frobInner_of_re_trace_le hA hU hQ hAU hUQ
  have hb := frobInner_mul_conjTranspose_sub_le hU hQ E
  rw [Fintype.card_fin] at hb
  push_cast at hb
  refine le_div_of_mul_sq_le_mul hgap (frobNorm_nonneg _)
    (mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg _)) (specNorm_nonneg E)) ?_
  linarith

/-- Davis–Kahan with the gap of the unperturbed matrix, Frobenius norm of the angles against the
spectral norm of the perturbation:
`‖(1 - U Uᴴ) Q‖_F ≤ 2 √(j + 1) ‖E‖₂ / (λ_j(A) - λ_{j+1}(A))`.
[YuWangSamworth2015, Theorem 2]. -/
theorem frobNorm_one_sub_mul_le_two_mul_sqrt_mul_specNorm_div_eigengap [DecidableEq n]
    {A E : Matrix n n 𝕜} (hA : A.IsHermitian) (hE : E.IsHermitian) {j : ℕ}
    {U Q : Matrix n (Fin (j + 1)) 𝕜} (hU : HasOrthonormalCols U) (hQ : HasOrthonormalCols Q)
    (hAU : A * U = U * Matrix.diagonal fun i : Fin (j + 1) => ((eigenvalue A i : ℝ) : 𝕜))
    (hQtop : RCLike.re (Qᴴ * (A + E) * Q).trace =
      ∑ i ∈ Finset.range (j + 1), eigenvalue (A + E) i)
    (hgap : 0 < eigengap A (j + 1)) :
    frobNorm ((1 - U * Uᴴ) * Q) ≤ 2 * √((j : ℝ) + 1) * specNorm E / eigengap A (j + 1) :=
  frobNorm_one_sub_mul_le_two_mul_sqrt_mul_specNorm_div_eigengap_of_re_trace_le hA hU hQ hAU
    (re_trace_le_re_trace_of_eq_sum (hA.add hE) hU hQtop) hgap

end NLAlib
