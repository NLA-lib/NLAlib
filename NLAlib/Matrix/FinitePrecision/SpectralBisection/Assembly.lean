/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.SpectralBisection.Child

/-!
# Assembling the output of a node of spectral bisection

The approximate diagonalization returned by a node of `NLAlib.eighAux` is assembled from its
children's: at a shift node the child's eigenvalues are shifted back by the stored shift, and at
a split the computed bases $\mathrm{mm}(\mathbf{Q}_\pm, \mathbf{U}_\pm)$ are put side by side,
with the residual and the singular-value window of the result bounded by those of the children,
the deflation and compression errors and the roundings ([Shah2024, proof of Lemma 4.1]).

## Main results

* `NLAlib.IsApproxDiagonalization.mono`: weakening the residual and the window.
* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_add_of_hermShift`: a shift node.
* `NLAlib.FloatMachine.IsAccurate.isApproxDiagonalization_submatrix_fromCols_mm`: a split node.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

open scoped ComplexOrder in
/-- Reindexing the columns of an approximate diagonalization. -/
private theorem isApproxDiagonalization_submatrix {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {A : Matrix m m ℂ} {U : Matrix m n ℂ} {d : n → ℝ} (e : m ≃ n)
    {η κ : ℝ} (h1 : specNorm (A - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) ≤ η)
    (h2 : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ Uᴴ * U)
    (h3 : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ)) :
    IsApproxDiagonalization A (U.submatrix id e) (fun i => d (e i)) η κ := by
  have hD : Matrix.diagonal (fun i => ((d (e i) : ℝ) : ℂ)) =
      (Matrix.diagonal (fun i => (d i : ℂ))).submatrix e e := by
    rw [Matrix.submatrix_diagonal_equiv]; rfl
  have hG : (U.submatrix id e)ᴴ * U.submatrix id e = (Uᴴ * U).submatrix e e := by
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
  have hsub : ∀ c : ℝ, (c • (1 : Matrix n n ℂ)).submatrix e e = c • (1 : Matrix m m ℂ) := by
    intro c; ext i j; simp [Matrix.one_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [hD, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
    simpa using h1
  · have := (Matrix.le_iff.mp h2).submatrix e
    rw [hG, ← hsub, Matrix.le_iff]
    convert this using 1
    rfl
  · have := (Matrix.le_iff.mp h3).submatrix e
    rw [hG, ← hsub, Matrix.le_iff]
    convert this using 1
    rfl

/-- Sandwich bound. -/
private theorem specNorm_mul_mul_conjTranspose_le_sq_mul {m n : Type*} [Fintype m] [Fintype n]
    {U : Matrix m n ℂ} {M : Matrix n n ℂ} {b : ℝ} (hU : specNorm U ≤ b) :
    specNorm (U * M * Uᴴ) ≤ b ^ 2 * specNorm M := by
  have hb : 0 ≤ b := (specNorm_nonneg U).trans hU
  calc specNorm (U * M * Uᴴ) ≤ specNorm U * specNorm M * specNorm Uᴴ :=
        (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _)
          (specNorm_nonneg _))
    _ ≤ b * specNorm M * b := by
        rw [specNorm_conjTranspose]
        gcongr
    _ = b ^ 2 * specNorm M := by ring

/-- Diagonal shift identity. -/
private theorem diagonal_add_smul_one_sub_diagonal {n : Type*} [DecidableEq n] (d e : n → ℝ)
    (σ : ℝ) :
    Matrix.diagonal (fun i => (d i : ℂ)) + σ • (1 : Matrix n n ℂ) -
        Matrix.diagonal (fun i => (e i : ℂ)) =
      Matrix.diagonal (fun i => ((d i + σ - e i : ℝ) : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

/-- Generic Loewner perturbation of a Gram matrix. -/
private theorem smul_one_le_and_le_smul_one_add {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq k]
    {G X : Matrix m k ℂ} {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hac : 0 ≤ a - c)
    (h₁ : a ^ 2 • (1 : Matrix k k ℂ) ≤ Gᴴ * G) (h₂ : Gᴴ * G ≤ b ^ 2 • (1 : Matrix k k ℂ))
    (hX : specNorm X ≤ c) :
    (a - c) ^ 2 • (1 : Matrix k k ℂ) ≤ (G + X)ᴴ * (G + X) ∧
      (G + X)ᴴ * (G + X) ≤ (b + c) ^ 2 • (1 : Matrix k k ℂ) := by
  have ha : 0 ≤ a := by linarith
  constructor
  · rw [smul_one_le_conjTranspose_mul_self_iff]
    rw [smul_one_le_conjTranspose_mul_self_iff] at h₁
    intro x
    have hG : a * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (G *ᵥ x)‖ := by
      have := h₁ x
      rw [← mul_pow] at this
      exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 this
    have hXx := (specNorm_le_iff hc).1 hX x
    have e : WithLp.toLp 2 (G *ᵥ x) =
        WithLp.toLp 2 ((G + X) *ᵥ x) - WithLp.toLp 2 (X *ᵥ x) := by
      rw [Matrix.add_mulVec, WithLp.toLp_add]; abel
    have ht := norm_sub_le (WithLp.toLp 2 ((G + X) *ᵥ x)) (WithLp.toLp 2 (X *ᵥ x))
    rw [← e] at ht
    have hl : (a - c) * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 ((G + X) *ᵥ x)‖ := by nlinarith
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hl 2
  · have hG : specNorm G ≤ b :=
      (sq_le_sq₀ (specNorm_nonneg _) hb).1
        ((specNorm_sq_le_iff_conjTranspose_mul_self_le (by positivity)).2 h₂)
    rw [← specNorm_sq_le_iff_conjTranspose_mul_self_le (by positivity)]
    exact pow_le_pow_left₀ (specNorm_nonneg _)
      ((specNorm_add_le _ _).trans (add_le_add hG hX)) 2

/-- (B') A Loewner upper bound on the Gram matrix bounds the spectral norm. -/
private theorem specNorm_le_of_conjTranspose_mul_self_le {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq n] {U : Matrix m n ℂ} {κ : ℝ} (hκ : 0 ≤ κ)
    (h : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ)) : specNorm U ≤ 1 + κ := by
  have h' := (specNorm_sq_le_iff_conjTranspose_mul_self_le (by positivity)).2 h
  exact (sq_le_sq₀ (specNorm_nonneg _) (by positivity)).1 h'

/-- (B) Near-unitary square matrix:
$\|\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf H}\|_2 \le 2\kappa + \kappa^2$. -/
private theorem specNorm_one_sub_mul_conjTranspose_le {n : Type*} [Fintype n]
    [DecidableEq n] {U : Matrix n n ℂ} {κ : ℝ} (hκ : 0 ≤ κ)
    (h₁ : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ Uᴴ * U)
    (h₂ : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ)) :
    specNorm (1 - U * Uᴴ) ≤ 2 * κ + κ ^ 2 := by
  have hn : specNorm U ≤ 1 + κ := specNorm_le_of_conjTranspose_mul_self_le hκ h₂
  have h1 : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ U * Uᴴ :=
    smul_one_le_mul_conjTranspose_self_of_smul_one_le h₁
  have h2 : U * Uᴴ ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ) := by
    have := conjTranspose_mul_self_le_specNorm_sq_smul_one Uᴴ
    rw [Matrix.conjTranspose_conjTranspose, specNorm_conjTranspose] at this
    refine this.trans (smul_one_le_smul_one ?_)
    exact pow_le_pow_left₀ (specNorm_nonneg _) hn 2
  have hH : (1 - U * Uᴴ).IsHermitian := by
    refine Matrix.IsHermitian.sub (Matrix.isHermitian_one) ?_
    simpa using Matrix.isHermitian_mul_conjTranspose_self U
  refine hH.specNorm_le_of_le_smul_one (by positivity) ?_ ?_
  · rw [Matrix.le_iff] at h2 ⊢
    convert h2 using 1
    rw [show (1 + κ) ^ 2 = 1 + (2 * κ + κ ^ 2) by ring]
    simp only [add_smul, one_smul]
    abel
  · have h3 : (1 - (2 * κ + κ ^ 2)) • (1 : Matrix n n ℂ) ≤ U * Uᴴ :=
      (smul_one_le_smul_one (by nlinarith)).trans h1
    rw [Matrix.le_iff] at h3 ⊢
    convert h3 using 1
    rw [sub_smul, one_smul]
    abel

/-- (A) The diagonal of an approximate diagonalization is bounded by the norm. -/
private theorem abs_le_specNorm_mul_diagonal_mul_div {n : Type*} [Fintype n]
    [DecidableEq n] {U : Matrix n n ℂ} {d : n → ℝ} {κ : ℝ} (hκ1 : κ < 1)
    (hU : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ Uᴴ * U) (i : n) :
    |d i| ≤ specNorm (U * Matrix.diagonal (fun j => (d j : ℂ)) * Uᴴ) / (1 - κ) ^ 2 := by
  set D := Matrix.diagonal (fun j => (d j : ℂ)) with hD
  have hc : 0 ≤ 1 - κ := by linarith
  have h1 := mul_specNorm_le_of_sq_smul_one_le hc hU (D * Uᴴ)
  have h2 := mul_specNorm_le_of_sq_smul_one_le hc hU Dᴴ
  have e : specNorm (D * Uᴴ) = specNorm (U * Dᴴ) := by
    rw [← specNorm_conjTranspose (D * Uᴴ), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  rw [specNorm_conjTranspose] at h2
  have h3 : |d i| ≤ specNorm D := by
    have := norm_apply_le_specNorm D i i
    simpa [hD] using this
  rw [le_div_iff₀ (by positivity), Matrix.mul_assoc]
  rw [e] at h1
  nlinarith [mul_le_mul_of_nonneg_left h3 hc, mul_le_mul_of_nonneg_left h2 hc]

/-- (S) The residual of a shift node. -/
private theorem specNorm_sub_mul_diagonal_mul_conjTranspose_le {n : Type*} [Fintype n]
    [DecidableEq n] {A A' U : Matrix n n ℂ} {d e : n → ℝ} {σ s κ ρ θ ε₀ : ℝ}
    (hσ : |σ| ≤ s) (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (hU₁ : (1 - κ) ^ 2 • (1 : Matrix n n ℂ) ≤ Uᴴ * U)
    (hU₂ : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix n n ℂ))
    (hA' : specNorm ((A - σ • (1 : Matrix n n ℂ)) - A') ≤ ε₀)
    (hF : specNorm (A' - U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) ≤ ρ)
    (he : ∀ i, |e i - (d i + σ)| ≤ θ) :
    specNorm (A - U * Matrix.diagonal (fun i => (e i : ℂ)) * Uᴴ) ≤
      ε₀ + ρ + s * (2 * κ + κ ^ 2) + (1 + κ) ^ 2 * θ := by
  have hn : specNorm U ≤ 1 + κ := specNorm_le_of_conjTranspose_mul_self_le hκ hU₂
  have hB := specNorm_one_sub_mul_conjTranspose_le hκ hU₁ hU₂
  set D := Matrix.diagonal (fun i => (d i : ℂ))
  set E := Matrix.diagonal (fun i => (e i : ℂ))
  have key : A - U * E * Uᴴ = ((A - σ • (1 : Matrix n n ℂ)) - A') + (A' - U * D * Uᴴ) +
      σ • (1 - U * Uᴴ) + U * (D + σ • (1 : Matrix n n ℂ) - E) * Uᴴ := by
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, smul_sub]
    abel
  have hT : specNorm (U * (D + σ • (1 : Matrix n n ℂ) - E) * Uᴴ) ≤ (1 + κ) ^ 2 * θ := by
    refine (specNorm_mul_mul_conjTranspose_le_sq_mul hn).trans ?_
    gcongr
    rw [diagonal_add_smul_one_sub_diagonal]
    refine specNorm_diagonal_le hθ fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact he i
  have hσ' : specNorm (σ • (1 - U * Uᴴ)) ≤ s * (2 * κ + κ ^ 2) := by
    rw [specNorm_real_smul]
    exact mul_le_mul hσ hB (specNorm_nonneg _) ((abs_nonneg σ).trans hσ)
  rw [key]
  refine (specNorm_add_le _ _).trans ?_
  refine add_le_add ?_ hT
  refine (specNorm_add_le _ _).trans ?_
  refine add_le_add ?_ hσ'
  exact (specNorm_add_le _ _).trans (add_le_add hA' hF)

/-- Perturbation of a congruence. -/
private theorem specNorm_mul_mul_conjTranspose_sub_le {m p : Type*} [Fintype m] [Fintype p]
    {G V : Matrix m p ℂ} {D' E : Matrix p p ℂ} {b ξ θ M : ℝ}
    (hG : specNorm G ≤ b) (hV : specNorm (V - G) ≤ ξ) (hDE : specNorm (D' - E) ≤ θ)
    (hE : specNorm E ≤ M) :
    specNorm (G * D' * Gᴴ - V * E * Vᴴ) ≤ b ^ 2 * θ + ξ * (2 * b + ξ) * M := by
  have hb : 0 ≤ b := (specNorm_nonneg _).trans hG
  have hξ : 0 ≤ ξ := (specNorm_nonneg _).trans hV
  have hM : 0 ≤ M := (specNorm_nonneg _).trans hE
  have key : G * D' * Gᴴ - V * E * Vᴴ =
      G * (D' - E) * Gᴴ - ((V - G) * E * Gᴴ + V * E * (V - G)ᴴ) := by
    simp only [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
    abel
  have hVn : specNorm V ≤ b + ξ := by
    have : V = G + (V - G) := by abel
    rw [this]; exact (specNorm_add_le _ _).trans (add_le_add hG hV)
  have h1 := specNorm_mul_mul_conjTranspose_le_sq_mul (M := D' - E) hG
  have h2 : specNorm ((V - G) * E * Gᴴ) ≤ ξ * M * b := by
    calc specNorm ((V - G) * E * Gᴴ) ≤ specNorm (V - G) * specNorm E * specNorm Gᴴ :=
          (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _)
            (specNorm_nonneg _))
      _ ≤ ξ * M * b := by
          rw [specNorm_conjTranspose]
          gcongr
  have h3 : specNorm (V * E * (V - G)ᴴ) ≤ (b + ξ) * M * ξ := by
    calc specNorm (V * E * (V - G)ᴴ) ≤ specNorm V * specNorm E * specNorm (V - G)ᴴ :=
          (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _)
            (specNorm_nonneg _))
      _ ≤ (b + ξ) * M * ξ := by
          rw [specNorm_conjTranspose]
          gcongr
  rw [key]
  refine (specNorm_sub_le _ _).trans ?_
  have := (specNorm_add_le ((V - G) * E * Gᴴ) (V * E * (V - G)ᴴ))
  have h1' : b ^ 2 * specNorm (D' - E) ≤ b ^ 2 * θ := by gcongr
  nlinarith

/-- One block of the assembled residual: replacing $\mathbf{Z}\mathbf{U}$ by $\mathbf{V}$ and
the shifted eigenvalues $d_i + \sigma$ by $e_i$. -/
private theorem specNorm_mul_diagonal_mul_conjTranspose_sub_le {m p : Type*} [Fintype m]
    [Fintype p] [DecidableEq p] {Z : Matrix m p ℂ} {U : Matrix p p ℂ} {V : Matrix m p ℂ}
    {d e : p → ℝ} {σ s κ ξ θ Dn : ℝ} (hZ : HasOrthonormalCols Z) (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (hσ : |σ| ≤ s) (hDn : 0 ≤ Dn) (hU₂ : Uᴴ * U ≤ (1 + κ) ^ 2 • (1 : Matrix p p ℂ))
    (hV : specNorm (V - Z * U) ≤ ξ) (hd : ∀ i, |d i| ≤ Dn) (he : ∀ i, |e i - (d i + σ)| ≤ θ) :
    specNorm ((Z * U) * Matrix.diagonal (fun i => ((d i + σ : ℝ) : ℂ)) * (Z * U)ᴴ -
      V * Matrix.diagonal (fun i => (e i : ℂ)) * Vᴴ) ≤
        (1 + κ) ^ 2 * θ + ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ) := by
  have hs : 0 ≤ s := (abs_nonneg _).trans hσ
  refine specNorm_mul_mul_conjTranspose_sub_le ?_ hV ?_ ?_
  · rw [hZ.specNorm_mul_left]; exact specNorm_le_of_conjTranspose_mul_self_le hκ hU₂
  · have : Matrix.diagonal (fun i => ((d i + σ : ℝ) : ℂ)) - Matrix.diagonal (fun i => (e i : ℂ)) =
        Matrix.diagonal (fun i => ((d i + σ - e i : ℝ) : ℂ)) := by
      ext i j; by_cases h : i = j
      · subst h; simp
      · simp [Matrix.diagonal_apply_ne _ h]
    rw [this]
    refine specNorm_diagonal_le hθ fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]; exact he i
  · refine specNorm_diagonal_le (by positivity) fun i => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 := he i; have h2 := hd i
    rw [abs_le] at h1 h2 hσ ⊢; constructor <;> linarith

/-- The residual of an assembled split: the blocks of $\mathbf{A}$ in the frames
$\mathbf{Z}_\pm$ against the children's diagonalizations, through the computed bases
$\mathbf{V}_\pm$. -/
private theorem specNorm_sub_fromCols_mul_diagonal_le {m p q : Type*} [Fintype m]
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {A : Matrix m m ℂ} {Zp : Matrix m p ℂ} {Zm : Matrix m q ℂ}
    (hZp : HasOrthonormalCols Zp) (hZm : HasOrthonormalCols Zm) (hZpm : Zpᴴ * Zm = 0)
    (hA : A = Zp * (Zpᴴ * A * Zp) * Zpᴴ + Zm * (Zmᴴ * A * Zm) * Zmᴴ)
    {Ap Up : Matrix p p ℂ} {Am Um : Matrix q q ℂ} {Vp : Matrix m p ℂ} {Vm : Matrix m q ℂ}
    {dp ep : p → ℝ} {dm em : q → ℝ} {σp σm s γ ρ κ ξ θ Dn : ℝ}
    (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) (hσp : |σp| ≤ s) (hσm : |σm| ≤ s) (hDn : 0 ≤ Dn)
    (hCp : specNorm (Ap - (Zpᴴ * A * Zp - σp • (1 : Matrix p p ℂ))) ≤ γ)
    (hCm : specNorm (Am - (Zmᴴ * A * Zm - σm • (1 : Matrix q q ℂ))) ≤ γ)
    (hFp : specNorm (Ap - Up * Matrix.diagonal (fun i => (dp i : ℂ)) * Upᴴ) ≤ ρ)
    (hFm : specNorm (Am - Um * Matrix.diagonal (fun i => (dm i : ℂ)) * Umᴴ) ≤ ρ)
    (hUp₁ : (1 - κ) ^ 2 • (1 : Matrix p p ℂ) ≤ Upᴴ * Up)
    (hUp₂ : Upᴴ * Up ≤ (1 + κ) ^ 2 • (1 : Matrix p p ℂ))
    (hUm₁ : (1 - κ) ^ 2 • (1 : Matrix q q ℂ) ≤ Umᴴ * Um)
    (hUm₂ : Umᴴ * Um ≤ (1 + κ) ^ 2 • (1 : Matrix q q ℂ))
    (hVp : specNorm (Vp - Zp * Up) ≤ ξ) (hVm : specNorm (Vm - Zm * Um) ≤ ξ)
    (hdp : ∀ i, |dp i| ≤ Dn) (hdm : ∀ i, |dm i| ≤ Dn)
    (hep : ∀ i, |ep i - (dp i + σp)| ≤ θ) (hem : ∀ i, |em i - (dm i + σm)| ≤ θ) :
    specNorm (A - Matrix.fromCols Vp Vm *
        Matrix.diagonal (fun i => ((Sum.elim ep em i : ℝ) : ℂ)) * (Matrix.fromCols Vp Vm)ᴴ) ≤
      γ + ρ + s * (2 * κ + κ ^ 2) +
        2 * ((1 + κ) ^ 2 * θ + ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ)) := by
  have hs : 0 ≤ s := (abs_nonneg _).trans hσp
  set Dp' := Matrix.diagonal (fun i => ((dp i + σp : ℝ) : ℂ))
  set Dm' := Matrix.diagonal (fun i => ((dm i + σm : ℝ) : ℂ))
  set Ep := Matrix.diagonal (fun i => (ep i : ℂ))
  set Em := Matrix.diagonal (fun i => (em i : ℂ))
  set Yp := Zpᴴ * A * Zp - Up * Dp' * Upᴴ
  set Ym := Zmᴴ * A * Zm - Um * Dm' * Umᴴ
  -- the blocks
  have hYp : specNorm Yp ≤ γ + ρ + s * (2 * κ + κ ^ 2) := by
    have := specNorm_sub_mul_diagonal_mul_conjTranspose_le (A := Zpᴴ * A * Zp)
      (e := fun i => dp i + σp)
      (θ := 0) (ε₀ := γ) hσp hκ le_rfl hUp₁ hUp₂ (by
        have h := specNorm_neg (Ap - (Zpᴴ * A * Zp - σp • (1 : Matrix _ _ ℂ)))
        rw [neg_sub] at h; rw [h]; exact hCp) hFp
      (fun i => by simp)
    exact (le_of_eq rfl).trans (this.trans (le_of_eq (by ring)))
  have hYm : specNorm Ym ≤ γ + ρ + s * (2 * κ + κ ^ 2) := by
    have := specNorm_sub_mul_diagonal_mul_conjTranspose_le (A := Zmᴴ * A * Zm)
      (e := fun i => dm i + σm)
      (θ := 0) (ε₀ := γ) hσm hκ le_rfl hUm₁ hUm₂ (by
        have h := specNorm_neg (Am - (Zmᴴ * A * Zm - σm • (1 : Matrix _ _ ℂ)))
        rw [neg_sub] at h; rw [h]; exact hCm) hFm
      (fun i => by simp)
    exact (le_of_eq rfl).trans (this.trans (le_of_eq (by ring)))
  set Z := Matrix.fromCols Zp Zm
  have hZ : HasOrthonormalCols Z := hasOrthonormalCols_fromCols_iff.mpr ⟨hZp, hZm, hZpm⟩
  have hblk : Zp * Yp * Zpᴴ + Zm * Ym * Zmᴴ = Z * Matrix.fromBlocks Yp 0 0 Ym * Zᴴ := by
    simp only [Z, Matrix.fromCols_mul_fromBlocks,
      Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows, Matrix.mul_zero, add_zero, zero_add]
  have hB : specNorm (Zp * Yp * Zpᴴ + Zm * Ym * Zmᴴ) ≤ γ + ρ + s * (2 * κ + κ ^ 2) := by
    rw [hblk, hZ.specNorm_mul_conjTranspose_right, hZ.specNorm_mul_left,
      specNorm_fromBlocks_zero₁₂_zero₂₁]
    exact max_le hYp hYm
  -- the T terms
  have hTp := specNorm_mul_diagonal_mul_conjTranspose_sub_le hZp hκ hθ hσp hDn hUp₂ hVp hdp hep
  have hTm := specNorm_mul_diagonal_mul_conjTranspose_sub_le hZm hκ hθ hσm hDn hUm₂ hVm hdm hem
  -- the decomposition
  have hE : Matrix.diagonal (fun i => ((Sum.elim ep em i : ℝ) : ℂ)) =
      Matrix.fromBlocks Ep 0 0 Em := by
    rw [Matrix.fromBlocks_diagonal]; congr 1; ext (i | i) <;> rfl
  have hCp' : Zpᴴ * A * Zp = Yp + Up * Dp' * Upᴴ := by simp [Yp]
  have hCm' : Zmᴴ * A * Zm = Ym + Um * Dm' * Umᴴ := by simp [Ym]
  have key : A - Matrix.fromCols Vp Vm *
        Matrix.diagonal (fun i => ((Sum.elim ep em i : ℝ) : ℂ)) * (Matrix.fromCols Vp Vm)ᴴ =
      (Zp * Yp * Zpᴴ + Zm * Ym * Zmᴴ) +
        ((Zp * Up) * Dp' * (Zp * Up)ᴴ - Vp * Ep * Vpᴴ) +
        ((Zm * Um) * Dm' * (Zm * Um)ᴴ - Vm * Em * Vmᴴ) := by
    rw [hE, Matrix.fromCols_mul_fromBlocks, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromCols_mul_fromRows]
    nth_rewrite 1 [hA]
    rw [hCp', hCm']
    simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.conjTranspose_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [key]
  have h1 := specNorm_add_le (Zp * Yp * Zpᴴ + Zm * Ym * Zmᴴ)
    ((Zp * Up) * Dp' * (Zp * Up)ᴴ - Vp * Ep * Vpᴴ)
  refine (specNorm_add_le _ _).trans ?_
  linarith

/-- (D) The singular values of the assembled basis, before reindexing. -/
private theorem smul_one_le_and_le_smul_one_fromCols {m p q : Type*} [Fintype m]
    [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
    {Zp : Matrix m p ℂ} {Zm : Matrix m q ℂ}
    (hZp : HasOrthonormalCols Zp) (hZm : HasOrthonormalCols Zm) (hZpm : Zpᴴ * Zm = 0)
    {Up : Matrix p p ℂ} {Um : Matrix q q ℂ} {Vp : Matrix m p ℂ} {Vm : Matrix m q ℂ}
    {κ ξ : ℝ} (hκ : 0 ≤ κ) (hξ : 0 ≤ ξ) (hκξ : κ + √2 * ξ ≤ 1)
    (hUp₁ : (1 - κ) ^ 2 • (1 : Matrix p p ℂ) ≤ Upᴴ * Up)
    (hUp₂ : Upᴴ * Up ≤ (1 + κ) ^ 2 • (1 : Matrix p p ℂ))
    (hUm₁ : (1 - κ) ^ 2 • (1 : Matrix q q ℂ) ≤ Umᴴ * Um)
    (hUm₂ : Umᴴ * Um ≤ (1 + κ) ^ 2 • (1 : Matrix q q ℂ))
    (hVp : specNorm (Vp - Zp * Up) ≤ ξ) (hVm : specNorm (Vm - Zm * Um) ≤ ξ) :
    (1 - (κ + √2 * ξ)) ^ 2 • (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ) ≤
        (Matrix.fromCols Vp Vm)ᴴ * Matrix.fromCols Vp Vm ∧
      (Matrix.fromCols Vp Vm)ᴴ * Matrix.fromCols Vp Vm ≤
        (1 + (κ + √2 * ξ)) ^ 2 • (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ) := by
  set Z := Matrix.fromCols Zp Zm
  have hZ : HasOrthonormalCols Z := hasOrthonormalCols_fromCols_iff.mpr ⟨hZp, hZm, hZpm⟩
  set B : Matrix (p ⊕ q) (p ⊕ q) ℂ := Matrix.fromBlocks Up 0 0 Um
  set G := Z * B
  set X := Matrix.fromCols (Vp - Zp * Up) (Vm - Zm * Um)
  have hGX : Matrix.fromCols Vp Vm = G + X := by
    simp only [G, X, Z, B, Matrix.fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, zero_add]
    ext i (j | j) <;> simp
  have hGG : Gᴴ * G = Matrix.fromBlocks (Upᴴ * Up) 0 0 (Umᴴ * Um) := by
    simp only [G, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Zᴴ, show Zᴴ * Z = 1 from hZ, Matrix.one_mul]
    simp only [B, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hblk : ∀ (r : ℝ), r • (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ) =
      Matrix.fromBlocks (r • (1 : Matrix p p ℂ)) 0 0 (r • (1 : Matrix q q ℂ)) := by
    intro r
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero, smul_zero]
  have h₁ : (1 - κ) ^ 2 • (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ) ≤ Gᴴ * G := by
    rw [hGG, hblk, Matrix.le_iff]
    rw [Matrix.le_iff] at hUp₁ hUm₁
    have := Matrix.PosSemidef.fromBlocks_zero₁₂_zero₂₁ hUp₁ hUm₁
    convert this using 1
    simp [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  have h₂ : Gᴴ * G ≤ (1 + κ) ^ 2 • (1 : Matrix (p ⊕ q) (p ⊕ q) ℂ) := by
    rw [hGG, hblk, Matrix.le_iff]
    rw [Matrix.le_iff] at hUp₂ hUm₂
    have := Matrix.PosSemidef.fromBlocks_zero₁₂_zero₂₁ hUp₂ hUm₂
    convert this using 1
    simp [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  have hX : specNorm X ≤ √2 * ξ := by
    have h := specNorm_fromCols_sq_le (Vp - Zp * Up) (Vm - Zm * Um)
    have h' : specNorm X ^ 2 ≤ (√2 * ξ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      nlinarith [specNorm_nonneg (Vp - Zp * Up), specNorm_nonneg (Vm - Zm * Um)]
    exact (sq_le_sq₀ (specNorm_nonneg _) (by positivity)).1 h'
  have := smul_one_le_and_le_smul_one_add (a := 1 - κ) (b := 1 + κ) (by linarith) (by positivity)
    (by linarith) h₁ h₂ hX
  rw [hGX]
  convert this using 3 <;> ring

/-- A rounding of a bounded number. -/
private theorem abs_sub_le_of_isRoundingOf_of_abs_le {u τ Ω a z c : ℝ} (h : IsRoundingOf u τ Ω a z)
    (ha : |a| ≤ c) (hc : c ≤ Ω) (hu : 0 ≤ u) (hτ : 0 ≤ τ) : |z - a| ≤ u * (c + τ) := by
  rw [abs_sub_comm]
  exact (abs_sub_le_of_isRoundingOf h (ha.trans hc) hu hτ).trans
    (mul_le_mul_of_nonneg_left (by linarith) hu)

/-- The eigenvalues of a child's approximate diagonalization are bounded. -/
private theorem abs_le_of_isApproxDiagonalization {n : Type*} [Fintype n] [DecidableEq n]
    {A U : Matrix n n ℂ} {d : n → ℝ} {ρ κ r : ℝ} (h : IsApproxDiagonalization A U d ρ κ)
    (hA : specNorm A ≤ r) (hκ1 : κ < 1) (i : n) :
    |d i| ≤ (r + ρ) / (1 - κ) ^ 2 := by
  refine (abs_le_specNorm_mul_diagonal_mul_div hκ1 h.smul_one_le i).trans ?_
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  have e : U * Matrix.diagonal (fun j => (d j : ℂ)) * Uᴴ =
      A - (A - U * Matrix.diagonal (fun j => (d j : ℂ)) * Uᴴ) := by abel
  rw [e]
  exact (specNorm_sub_le _ _).trans (add_le_add hA h.specNorm_sub_le)

/-- The computed product `mm(Q, U)` against the ideal frame. -/
private theorem FloatMachine.IsAccurate.specNorm_decodeMatrix_mm_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ}
    {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k r : ℕ}
    (hr : r ≤ k) {Q : Matrix (Fin k) (Fin r) (F × F)} {X : Matrix (Fin r) (Fin r) (F × F)}
    {Z : Matrix (Fin k) (Fin r) ℂ} {η κ : ℝ} (hZ : HasOrthonormalCols Z)
    (hQ : specNorm (Z - decodeMatrix dec Q) ≤ η) (hX : specNorm (decodeMatrix dec X) ≤ 1 + κ)
    (hκ : 0 ≤ κ) (hΩ : (1 + η) * (1 + κ) ≤ Ω) (hμ : 0 ≤ μM k) (hu : 0 ≤ u) (hτ : 0 ≤ τ) :
    specNorm (decodeMatrix dec (M.mm Q X) - Z * decodeMatrix dec X) ≤
      η * (1 + κ) + μM k * u * ((1 + η) * (1 + κ) + τ) := by
  have hQn : specNorm (decodeMatrix dec Q) ≤ 1 + η := by
    have e : decodeMatrix dec Q = Z - (Z - decodeMatrix dec Q) := by abel
    rw [e]
    exact (specNorm_sub_le _ _).trans (add_le_add hZ.specNorm_le_one hQ)
  have hη : 0 ≤ η := (specNorm_nonneg _).trans hQ
  have hprod : specNorm (decodeMatrix dec Q) * specNorm (decodeMatrix dec X) ≤
      (1 + η) * (1 + κ) :=
    mul_le_mul hQn hX (specNorm_nonneg _) (by linarith)
  have hmm := hM.isMatMulErr.specNorm_mul_sub_le Q X (hprod.trans hΩ)
  have hk : max k (max r r) = k := by omega
  rw [hk] at hmm
  change specNorm (decodeMatrix dec Q * decodeMatrix dec X - decodeMatrix dec (M.mm Q X)) ≤
    μM k * u * max (specNorm (decodeMatrix dec Q) * specNorm (decodeMatrix dec X)) τ at hmm
  have e : decodeMatrix dec (M.mm Q X) - Z * decodeMatrix dec X =
      -(decodeMatrix dec Q * decodeMatrix dec X - decodeMatrix dec (M.mm Q X)) -
        (Z - decodeMatrix dec Q) * decodeMatrix dec X := by
    rw [Matrix.sub_mul]; abel
  rw [e]
  refine (specNorm_sub_le _ _).trans ?_
  rw [specNorm_neg]
  have h1 := (specNorm_mul_le (Z - decodeMatrix dec Q) (decodeMatrix dec X)).trans
    (mul_le_mul hQ hX (specNorm_nonneg _) hη)
  have h2 : μM k * u * max (specNorm (decodeMatrix dec Q) * specNorm (decodeMatrix dec X)) τ ≤
      μM k * u * ((1 + η) * (1 + κ) + τ) :=
    mul_le_mul_of_nonneg_left (max_le (by linarith) (by
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + η) (by linarith : (0 : ℝ) ≤ 1 + κ)
      linarith)) (mul_nonneg hμ hu)
  linarith

/-- Weakening the residual and the singular-value window of an approximate diagonalization. -/
theorem IsApproxDiagonalization.mono {n : Type*} [Fintype n] [DecidableEq n]
    {A U : Matrix n n ℂ} {d : n → ℝ} {η η' κ κ' : ℝ} (h : IsApproxDiagonalization A U d η κ)
    (hη : η ≤ η') (hκ0 : 0 ≤ κ) (hκ : κ ≤ κ') (hκ1 : κ' ≤ 1) :
    IsApproxDiagonalization A U d η' κ' :=
  ⟨h.specNorm_sub_le.trans hη, (smul_one_le_smul_one (by nlinarith)).trans h.smul_one_le,
    h.le_smul_one.trans (smul_one_le_smul_one (by nlinarith))⟩

/-- **A shift node**: under `NLAlib.FloatMachine.IsAccurate` with $u, \tau \ge 0$, the child's
approximate diagonalization of the stored
$\mathrm{fl}(\mathbf{A} - \sigma\mathbf{I})$ (residual $\rho$, window $\kappa < 1$, norm at most
$r'$), with its eigenvalues shifted back by the stored $\sigma$, $\lvert\sigma\rvert \le s$, is one
of $\mathbf{A}$ ($\|\mathbf{A}\|_2 \le R$) with residual
$u(R + s + \tau) + \rho + s(2\kappa + \kappa^2) + (1 + \kappa)^2\theta$,
$\theta = u(D + s + \tau)$, $D = (r' + \rho)/(1 - \kappa)^2$. [Shah2024, proof of Lemma 4.1]. -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_add_of_hermShift {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k : ℕ} {A U : Matrix (Fin k) (Fin k) (F × F)}
    {d : Fin k → F} {σ : F} {R s r' ρ κ : ℝ} (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hA : (decodeMatrix dec A).IsHermitian) (hR : specNorm (decodeMatrix dec A) ≤ R)
    (hσ : |dec σ| ≤ s) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hc : IsApproxDiagonalization (decodeMatrix dec (M.hermShift A σ)) (decodeMatrix dec U)
      (fun i => dec (d i)) ρ κ)
    (hA'R : specNorm (decodeMatrix dec (M.hermShift A σ)) ≤ r') (hΩ1 : R + s + τ ≤ Ω)
    (hΩ2 : (r' + ρ) / (1 - κ) ^ 2 + s + τ ≤ Ω) :
    IsApproxDiagonalization (decodeMatrix dec A) (decodeMatrix dec U)
      (fun i => dec (M.add (d i) σ)) (u * (R + s + τ) + ρ + s * (2 * κ + κ ^ 2) +
        (1 + κ) ^ 2 * (u * ((r' + ρ) / (1 - κ) ^ 2 + s + τ))) κ := by
  have hρ0 := (specNorm_nonneg _).trans hc.specNorm_sub_le
  have hr0 := (specNorm_nonneg _).trans hA'R
  have hs0 := (abs_nonneg _).trans hσ
  have hR0 := (specNorm_nonneg _).trans hR
  have hn : specNorm (decodeMatrix dec A - dec σ • (1 : Matrix (Fin k) (Fin k) ℂ)) ≤ R + s := by
    refine (specNorm_sub_le _ _).trans (add_le_add hR ?_)
    rw [specNorm_real_smul]
    exact (mul_le_mul_of_nonneg_left specNorm_one_le (abs_nonneg _)).trans (by linarith)
  have hA'err := (hM.specNorm_sub_decodeMatrix_hermShift_le hu hA σ (by linarith)).trans
    (mul_le_mul_of_nonneg_left (max_le (c := R + s + τ) (by linarith) (by linarith)) hu)
  have hd := abs_le_of_isApproxDiagonalization hc hA'R hκ1
  have hθ0 : 0 ≤ u * ((r' + ρ) / (1 - κ) ^ 2 + s + τ) := mul_nonneg hu (by positivity)
  refine ⟨specNorm_sub_mul_diagonal_mul_conjTranspose_le hσ hκ0 hθ0 hc.smul_one_le
    hc.le_smul_one hA'err hc.specNorm_sub_le fun i =>
    abs_sub_le_of_isRoundingOf_of_abs_le (hM.add _ _)
      ((abs_add_le _ _).trans (add_le_add (hd i) hσ)) (by linarith) hu hτ₀, hc.smul_one_le,
    hc.le_smul_one⟩

/-- The rotated frames $\mathbf{Z}_\pm = \mathbf{V}_\pm\mathbf{W}_\pm$ of the two spectral
projectors $\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} - c\mathbf{I}))$ are mutually
orthogonal and block-diagonalize $\mathbf{A}$. -/
private theorem conjTranspose_mul_eq_zero_and_eq_add_of_mul_conjTranspose_eq {k p q : ℕ}
    {A : Matrix (Fin k) (Fin k) ℂ} {c : ℝ} {Vp : Matrix (Fin k) (Fin p) ℂ}
    {Vm : Matrix (Fin k) (Fin q) ℂ} {Wp : Matrix (Fin p) (Fin p) ℂ}
    {Wm : Matrix (Fin q) (Fin q) ℂ} (hWp : HasOrthonormalCols Wp) (hWm : HasOrthonormalCols Wm)
    (hZp : HasOrthonormalCols (Vp * Wp)) (hZm : HasOrthonormalCols (Vm * Wm))
    (hVpP : Vp * Vpᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))))
    (hVmP : Vm * Vmᴴ = (2⁻¹ : ℝ) • (1 - cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)))) :
    (Vp * Wp)ᴴ * (Vm * Wm) = 0 ∧ A = (Vp * Wp) * ((Vp * Wp)ᴴ * A * (Vp * Wp)) * (Vp * Wp)ᴴ +
      (Vm * Wm) * ((Vm * Wm)ᴴ * A * (Vm * Wm)) * (Vm * Wm)ᴴ := by
  set Zp := Vp * Wp with hZpdef
  set Zm := Vm * Wm with hZmdef
  have hPp : Zp * Zpᴴ = Vp * Vpᴴ := by
    rw [hZpdef, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wp,
      mul_eq_one_comm.mp hWp, Matrix.one_mul]
  have hPm : Zm * Zmᴴ = Vm * Vmᴴ := by
    rw [hZmdef, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wm,
      mul_eq_one_comm.mp hWm, Matrix.one_mul]
  set S := cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))
  have hPQ : Zp * Zpᴴ + Zm * Zmᴴ = 1 := by
    rw [hPp, hPm, hVpP, hVmP, ← smul_add, add_add_sub_cancel, ← two_smul ℝ, smul_smul]
    norm_num
  have hZpm : Zpᴴ * Zm = 0 := by
    have h : Zpᴴ * Zm = Zpᴴ * Zm + Zpᴴ * Zm := by
      calc Zpᴴ * Zm = Zpᴴ * (Zp * Zpᴴ + Zm * Zmᴴ) * Zm := by rw [hPQ, Matrix.mul_one]
        _ = (Zpᴴ * Zp) * (Zpᴴ * Zm) + (Zpᴴ * Zm) * (Zmᴴ * Zm) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = _ := by rw [hZp, hZm, Matrix.one_mul, Matrix.mul_one]
    simpa using h
  have hZmp : Zmᴴ * Zp = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose Zp, ← Matrix.conjTranspose_mul, hZpm,
      Matrix.conjTranspose_zero]
  have hcomm : Commute S A := Commute.cfc_real
    ((Commute.refl A).sub_left ((Commute.one_left A).smul_left _)) Real.sign
  have hPc : Commute (Zp * Zpᴴ) A := by
    rw [hPp, hVpP]; exact ((Commute.one_left A).add_left hcomm).smul_left _
  have hQc : Commute (Zm * Zmᴴ) A := by
    rw [show Zm * Zmᴴ = 1 - Zp * Zpᴴ by rw [← hPQ]; abel]
    exact (Commute.one_left A).sub_left hPc
  refine ⟨hZpm, ?_⟩
  have h1 : Zp * Zpᴴ * A * (Zm * Zmᴴ) = 0 := by
    rw [hPc.eq, Matrix.mul_assoc, Matrix.mul_assoc Zp, ← Matrix.mul_assoc Zpᴴ, hZpm,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
  have h2 : Zm * Zmᴴ * A * (Zp * Zpᴴ) = 0 := by
    rw [hQc.eq, Matrix.mul_assoc, Matrix.mul_assoc Zm, ← Matrix.mul_assoc Zmᴴ, hZmp,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.mul_zero]
  calc A = (Zp * Zpᴴ + Zm * Zmᴴ) * A * (Zp * Zpᴴ + Zm * Zmᴴ) := by
        rw [hPQ, Matrix.one_mul, Matrix.mul_one]
    _ = Zp * Zpᴴ * A * (Zp * Zpᴴ) + Zm * Zmᴴ * A * (Zm * Zmᴴ) +
        (Zp * Zpᴴ * A * (Zm * Zmᴴ) + Zm * Zmᴴ * A * (Zp * Zpᴴ)) := by
      simp only [Matrix.mul_add, Matrix.add_mul]; abel
    _ = _ := by rw [h1, h2, add_zero, add_zero]; simp only [Matrix.mul_assoc]

/-- **A split node**: under `NLAlib.FloatMachine.IsAccurate` with $u, \tau \ge 0$,
$\mu_{\mathrm{MM}}(k) \ge 0$ and range $\Omega \ge \max(4, D + s + \tau)$, the children's
approximate diagonalizations (residual $\rho$, window
$\kappa < 1$, norms at most $r'$), through the computed bases $\mathrm{mm}(\mathbf{Q}_\pm,
\mathbf{U}_\pm)$ (with $\mathbf{Q}_\pm$ within $\eta$ of orthonormal, mutually orthogonal frames
$\mathbf{Z}_\pm$ that block-diagonalize $\mathbf{A}$) and the stored shift $\pm\sigma$, assemble
into one of $\mathbf{A}$. [Shah2024, proof of Lemma 4.1]. -/
theorem FloatMachine.IsAccurate.isApproxDiagonalization_submatrix_fromCols_mm {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k kp : ℕ} (hkp : kp ≤ k)
    (hk : k = kp + (k - kp))
    {A : Matrix (Fin k) (Fin k) (F × F)} {Qp : Matrix (Fin k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)} {Ap Up : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am Um : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)} {dp : Fin kp → F}
    {dm : Fin (k - kp) → F} {σ : F} {c : ℝ} {Vp : Matrix (Fin k) (Fin kp) ℂ}
    {Vm : Matrix (Fin k) (Fin (k - kp)) ℂ} {Wp : Matrix (Fin kp) (Fin kp) ℂ}
    {Wm : Matrix (Fin (k - kp)) (Fin (k - kp)) ℂ} {η γ s ρ κ r' ξ Dn θ : ℝ} (hμM : 0 ≤ μM k)
    (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) (hVp : HasOrthonormalCols Vp) (hVm : HasOrthonormalCols Vm)
    (hWp : HasOrthonormalCols Wp) (hWm : HasOrthonormalCols Wm)
    (hVpP : Vp * Vpᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (decodeMatrix dec A -
      c • (1 : Matrix (Fin k) (Fin k) ℂ))))
    (hVmP : Vm * Vmᴴ = (2⁻¹ : ℝ) • (1 - cfc Real.sign (decodeMatrix dec A -
      c • (1 : Matrix (Fin k) (Fin k) ℂ))))
    (hQp : specNorm (Vp * Wp - decodeMatrix dec Qp) ≤ η)
    (hQm : specNorm (Vm * Wm - decodeMatrix dec Qm) ≤ η)
    (hAp : specNorm (decodeMatrix dec Ap - (Wpᴴ * (Vpᴴ * decodeMatrix dec A * Vp) * Wp -
      dec σ • (1 : Matrix (Fin kp) (Fin kp) ℂ))) ≤ γ)
    (hAm : specNorm (decodeMatrix dec Am - (Wmᴴ * (Vmᴴ * decodeMatrix dec A * Vm) * Wm +
      dec σ • (1 : Matrix (Fin (k - kp)) (Fin (k - kp)) ℂ))) ≤ γ)
    (hcp : IsApproxDiagonalization (decodeMatrix dec Ap) (decodeMatrix dec Up)
      (fun i => dec (dp i)) ρ κ)
    (hcm : IsApproxDiagonalization (decodeMatrix dec Am) (decodeMatrix dec Um)
      (fun i => dec (dm i)) ρ κ)
    (hApR : specNorm (decodeMatrix dec Ap) ≤ r') (hAmR : specNorm (decodeMatrix dec Am) ≤ r')
    (hσ : |dec σ| ≤ s) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hκξ : κ + √2 * ξ ≤ 1) (hη1 : η ≤ 1)
    (hΩ4 : 4 ≤ Ω) (hΩd : Dn + s + τ ≤ Ω)
    (hξ : ξ = η * (1 + κ) + μM k * u * ((1 + η) * (1 + κ) + τ)) (hDn : Dn = (r' + ρ) / (1 - κ) ^ 2)
    (hθ : θ = u * (Dn + s + τ)) :
    IsApproxDiagonalization (decodeMatrix dec A)
      (decodeMatrix dec ((Matrix.fromCols (M.mm Qp Up) (M.mm Qm Um)).submatrix id
        ((finCongr hk).trans finSumFinEquiv.symm)))
      (fun i => dec (Sum.elim (fun j => M.add (dp j) σ) (fun j => M.sub (dm j) σ)
        (((finCongr hk).trans finSumFinEquiv.symm) i)))
      (γ + ρ + s * (2 * κ + κ ^ 2) + 2 * ((1 + κ) ^ 2 * θ + ξ * (2 * (1 + κ) + ξ) * (Dn + s + θ)))
      (κ + √2 * ξ) := by
  have hη0 : 0 ≤ η := (specNorm_nonneg _).trans hQp
  have hξ0' : 0 ≤ ξ := by rw [hξ]; positivity
  have hZp := hVp.mul hWp
  have hZm := hVm.mul hWm
  obtain ⟨hZpm, hAdec⟩ := conjTranspose_mul_eq_zero_and_eq_add_of_mul_conjTranspose_eq hWp hWm
    hZp hZm hVpP hVmP
  have hCp : specNorm (decodeMatrix dec Ap - ((Vp * Wp)ᴴ * decodeMatrix dec A * (Vp * Wp) -
      dec σ • (1 : Matrix (Fin kp) (Fin kp) ℂ))) ≤ γ := by
    convert hAp using 4; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hCm : specNorm (decodeMatrix dec Am - ((Vm * Wm)ᴴ * decodeMatrix dec A * (Vm * Wm) -
      (-dec σ) • (1 : Matrix (Fin (k - kp)) (Fin (k - kp)) ℂ))) ≤ γ := by
    rw [neg_smul, sub_neg_eq_add]
    convert hAm using 4; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hκ1' : κ ≤ 1 := by linarith [mul_nonneg (Real.sqrt_nonneg 2) hξ0']
  have hΩq : (1 + η) * (1 + κ) ≤ Ω := by
    linarith [mul_le_mul (by linarith : 1 + η ≤ 2) (by linarith : 1 + κ ≤ 2) (by linarith)
      (by norm_num : (0 : ℝ) ≤ 2)]
  have hρ0 := (specNorm_nonneg _).trans hcp.specNorm_sub_le
  have hr0 := (specNorm_nonneg _).trans hApR
  have hξ0 : 0 ≤ ξ := by rw [hξ]; positivity
  have hDn0 : 0 ≤ Dn := by rw [hDn]; exact div_nonneg (by linarith) (sq_nonneg _)
  have hθ0 : 0 ≤ θ := by rw [hθ]; have := (abs_nonneg _).trans hσ; positivity
  have hVoutp := hM.specNorm_decodeMatrix_mm_sub_le hkp hZp hQp
    (specNorm_le_of_conjTranspose_mul_self_le hκ0 hcp.le_smul_one) hκ0 hΩq hμM hu hτ₀ (X := Up)
  have hVoutm := hM.specNorm_decodeMatrix_mm_sub_le (Nat.sub_le _ _) hZm hQm
    (specNorm_le_of_conjTranspose_mul_self_le hκ0 hcm.le_smul_one) hκ0 hΩq hμM hu hτ₀ (X := Um)
  rw [← hξ] at hVoutp hVoutm
  have hdp := abs_le_of_isApproxDiagonalization hcp hApR hκ1
  have hdm := abs_le_of_isApproxDiagonalization hcm hAmR hκ1
  rw [← hDn] at hdp hdm
  have hep := fun i => abs_sub_le_of_isRoundingOf_of_abs_le (hM.add (dp i) σ)
    ((abs_add_le _ _).trans (add_le_add (hdp i) hσ)) (by linarith) hu hτ₀
  have hem := fun i => abs_sub_le_of_isRoundingOf_of_abs_le (hM.sub (dm i) σ)
    ((abs_sub _ _).trans (add_le_add (hdm i) hσ)) (by linarith) hu hτ₀
  rw [← hθ] at hep hem
  have hres := specNorm_sub_fromCols_mul_diagonal_le hZp hZm hZpm hAdec hκ0 hθ0 hσ
    (by rwa [abs_neg]) hDn0 hCp hCm hcp.specNorm_sub_le hcm.specNorm_sub_le hcp.smul_one_le
    hcp.le_smul_one hcm.smul_one_le hcm.le_smul_one hVoutp hVoutm hdp hdm hep
    (fun i => by rw [← sub_eq_add_neg]; exact hem i)
  obtain ⟨hlo, hhi⟩ := smul_one_le_and_le_smul_one_fromCols hZp hZm hZpm hκ0 hξ0 hκξ
    hcp.smul_one_le hcp.le_smul_one hcm.smul_one_le hcm.le_smul_one hVoutp hVoutm
  have key := isApproxDiagonalization_submatrix
    ((finCongr (Nat.add_sub_of_le hkp).symm).trans finSumFinEquiv.symm) hres hlo hhi
  convert key using 2
  · simp only [decodeMatrix, ← Matrix.submatrix_map, Matrix.fromCols_map]
  · rename_i i
    generalize ((finCongr (Nat.add_sub_of_le hkp).symm).trans finSumFinEquiv.symm) i = j
    cases j <;> rfl

end NLAlib

