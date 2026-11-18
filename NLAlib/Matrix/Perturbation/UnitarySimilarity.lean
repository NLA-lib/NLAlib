/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Block

/-!
# Perturbed unitary similarity

A matrix $\mathbf{B}$ is a **perturbed unitary similarity** of $\mathbf{A}$ with backward error
$\varepsilon$ when $\mathbf{B} = \mathbf{U}^{\mathsf{H}}(\mathbf{A} + \mathbf{E})\mathbf{U}$ for a
unitary $\mathbf{U}$ and a perturbation with $\|\mathbf{E}\|_2 \le \varepsilon$. It is the
backward-error statement of a step of a unitary eigenvalue algorithm (a sweep of rotations, a
shifted QR step, a deflation) in finite precision; in exact arithmetic $\varepsilon = 0$. The
relation hides $\mathbf{U}$: it serves eigenvalue algorithms, not the computed Schur vectors.

The backward errors of consecutive steps add, because a unitary similarity keeps the spectral
norm of the next perturbation:
$$\mathbf{U}_2^{\mathsf{H}}\bigl(\mathbf{U}_1^{\mathsf{H}}(\mathbf{A} + \mathbf{E}_1)\mathbf{U}_1 +
  \mathbf{E}_2\bigr)\mathbf{U}_2 = (\mathbf{U}_1\mathbf{U}_2)^{\mathsf{H}}(\mathbf{A} +
  \mathbf{E}_1 + \mathbf{U}_1\mathbf{E}_2\mathbf{U}_1^{\mathsf{H}})(\mathbf{U}_1\mathbf{U}_2),
  \qquad \|\mathbf{U}_1\mathbf{E}_2\mathbf{U}_1^{\mathsf{H}}\|_2 = \|\mathbf{E}_2\|_2.$$
[Higham2002], [BanksGarzaVargasSrivastava2022].

## Main definitions

* `NLAlib.IsPerturbedUnitarySimilar`: $\mathbf{B} = \mathbf{U}^{\mathsf{H}}(\mathbf{A} +
  \mathbf{E})\mathbf{U}$, $\mathbf{U}$ unitary, $\|\mathbf{E}\|_2 \le \varepsilon$.

## Main results

* `NLAlib.IsPerturbedUnitarySimilar.refl`, `NLAlib.IsPerturbedUnitarySimilar.trans`,
  `NLAlib.IsPerturbedUnitarySimilar.mono`, `NLAlib.IsPerturbedUnitarySimilar.symm`: the
  algebra; backward errors add.
* `NLAlib.isPerturbedUnitarySimilar_zero_iff`,
  `NLAlib.HasOrthonormalCols.isPerturbedUnitarySimilar`:
  backward error $0$ is an exact unitary similarity.
* `NLAlib.isPerturbedUnitarySimilar_add`, `NLAlib.IsPerturbedUnitarySimilar.add_right`,
  `NLAlib.IsPerturbedUnitarySimilar.sub_single`: a perturbation of the output, and zeroing
  one entry (deflation).
* `NLAlib.IsPerturbedUnitarySimilar.of_specNorm_sub_le`,
  `NLAlib.IsPerturbedUnitarySimilar.of_near_unitary`: from the outputs of a rounded kernel.
* `NLAlib.IsPerturbedUnitarySimilar.exists_submatrix`: a step on a principal block (a range of a
  partition) is a step on the whole matrix, with the same backward error.
* `NLAlib.IsPerturbedUnitarySimilar.submatrix_equiv`: relabelling the indices.
* `NLAlib.IsPerturbedUnitarySimilar.exists_fromBlocks₁₁`,
  `NLAlib.IsPerturbedUnitarySimilar.exists_fromBlocks₂₂`: a step on one diagonal block of a block
  upper triangular matrix is a step on the whole matrix.
* `NLAlib.IsPerturbedUnitarySimilarBy`, `NLAlib.isPerturbedUnitarySimilar_iff_exists_by`,
  `NLAlib.IsPerturbedUnitarySimilarBy.fromBlocks₁₁`,
  `NLAlib.IsPerturbedUnitarySimilarBy.of_range_block`:
  the relation with its unitary named, and its block lifts with computed couplings.
* `NLAlib.IsTrackedUnitarySimilar`, `NLAlib.IsTrackedUnitarySimilar.trans`,
  `NLAlib.IsTrackedUnitarySimilar.specNorm_sub_mul_mul_conjTranspose_le`: a stored accumulator
  tracked with a relative error, and the computed Schur form.
* `NLAlib.IsPerturbedUnitarySimilar.specNorm_le`: $\|\mathbf{B}\|_2 \le \|\mathbf{A}\|_2 +
  \varepsilon$.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n m p : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p]

/-- $\mathbf{B}$ is a perturbed unitary similarity of $\mathbf{A}$ with backward error
$\varepsilon$: $\mathbf{B} = \mathbf{U}^{\mathsf{H}}(\mathbf{A} + \mathbf{E})\mathbf{U}$ for a
square $\mathbf{U}$ with orthonormal columns and a perturbation $\mathbf{E}$ with
$\|\mathbf{E}\|_2 \le \varepsilon$. -/
def IsPerturbedUnitarySimilar (A B : Matrix n n 𝕜) (ε : ℝ) : Prop :=
  ∃ U E : Matrix n n 𝕜, HasOrthonormalCols U ∧ specNorm E ≤ ε ∧ B = Uᴴ * (A + E) * U

namespace IsPerturbedUnitarySimilar

/-- Every matrix is a perturbed unitary similarity of itself with backward error $0$. -/
theorem refl (A : Matrix n n 𝕜) : IsPerturbedUnitarySimilar A A 0 :=
  ⟨1, 0, hasOrthonormalCols_one, by rw [specNorm_zero], by simp⟩

/-- A larger backward error is weaker. -/
theorem mono {A B : Matrix n n 𝕜} {ε ε' : ℝ} (h : IsPerturbedUnitarySimilar A B ε)
    (hε : ε ≤ ε') : IsPerturbedUnitarySimilar A B ε' :=
  let ⟨U, E, hU, hE, hB⟩ := h
  ⟨U, E, hU, hE.trans hε, hB⟩

/-- The backward error is nonnegative. -/
theorem nonneg {A B : Matrix n n 𝕜} {ε : ℝ} (h : IsPerturbedUnitarySimilar A B ε) : 0 ≤ ε :=
  let ⟨_, E, _, hE, _⟩ := h
  (specNorm_nonneg E).trans hE

/-- Backward errors add: if $\mathbf{B}$ is a perturbed unitary similarity of $\mathbf{A}$
with backward error $\varepsilon_1$ and $\mathbf{C}$ one of $\mathbf{B}$ with $\varepsilon_2$, then
$\mathbf{C}$ is one of $\mathbf{A}$ with $\varepsilon_1 + \varepsilon_2$. No printed source. -/
theorem trans {A B C : Matrix n n 𝕜} {ε₁ ε₂ : ℝ} (h₁ : IsPerturbedUnitarySimilar A B ε₁)
    (h₂ : IsPerturbedUnitarySimilar B C ε₂) : IsPerturbedUnitarySimilar A C (ε₁ + ε₂) := by
  obtain ⟨U₁, E₁, hU₁, hE₁, rfl⟩ := h₁
  obtain ⟨U₂, E₂, hU₂, hE₂, rfl⟩ := h₂
  refine ⟨U₁ * U₂, E₁ + U₁ * E₂ * U₁ᴴ, ?_, ?_, ?_⟩
  · rw [hasOrthonormalCols_iff, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc U₁ᴴ, hU₁.conjTranspose_mul_self, Matrix.one_mul,
      hU₂.conjTranspose_mul_self]
  · refine (specNorm_add_le _ _).trans (add_le_add hE₁ ?_)
    rwa [hU₁.specNorm_mul_conjTranspose_right, hU₁.specNorm_mul_left]
  · have h1 : U₁ᴴ * U₁ = 1 := hU₁.conjTranspose_mul_self
    simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U₁ᴴ U₁, h1, Matrix.one_mul, ← Matrix.mul_assoc U₁ᴴ U₁, h1,
      Matrix.one_mul]
    simp only [← Matrix.mul_assoc]
    abel

/-- The relation is symmetric: $\mathbf{A} = \mathbf{U}(\mathbf{B} -
\mathbf{U}^{\mathsf{H}}\mathbf{E}\mathbf{U})\mathbf{U}^{\mathsf{H}}$. -/
theorem symm {A B : Matrix n n 𝕜} {ε : ℝ} (h : IsPerturbedUnitarySimilar A B ε) :
    IsPerturbedUnitarySimilar B A ε := by
  obtain ⟨U, E, hU, hE, rfl⟩ := h
  have h1 : U * Uᴴ = 1 := hU.mul_conjTranspose_self
  refine ⟨Uᴴ, -(Uᴴ * E * U), ?_, ?_, ?_⟩
  · rw [hasOrthonormalCols_iff, Matrix.conjTranspose_conjTranspose, h1]
  · rwa [specNorm_neg, hU.specNorm_conjTranspose_mul_mul]
  · rw [Matrix.conjTranspose_conjTranspose, ← sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul,
      add_sub_cancel_right, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul,
      Matrix.mul_assoc, h1, Matrix.mul_one]

/-- The spectral norm grows by at most the backward error:
$\|\mathbf{B}\|_2 \le \|\mathbf{A}\|_2 + \varepsilon$. -/
theorem specNorm_le {A B : Matrix n n 𝕜} {ε : ℝ} (h : IsPerturbedUnitarySimilar A B ε) :
    specNorm B ≤ specNorm A + ε := by
  obtain ⟨U, E, hU, hE, rfl⟩ := h
  rw [hU.specNorm_conjTranspose_mul_mul]
  exact (specNorm_add_le A E).trans (add_le_add_right hE _)

/-- A perturbation of the output adds its spectral norm: if $\mathbf{B}$ is a perturbed unitary
similarity of $\mathbf{A}$ with backward error $\varepsilon$, then $\mathbf{B} + \mathbf{F}$ is one
with $\varepsilon + \|\mathbf{F}\|_2$. -/
theorem add_right {A B : Matrix n n 𝕜} {ε : ℝ} (h : IsPerturbedUnitarySimilar A B ε)
    (F : Matrix n n 𝕜) : IsPerturbedUnitarySimilar A (B + F) (ε + specNorm F) :=
  h.trans ⟨1, F, hasOrthonormalCols_one, le_rfl, by simp⟩

end IsPerturbedUnitarySimilar

/-- A matrix plus a perturbation is a perturbed unitary similarity of the matrix, with backward
error the spectral norm of the perturbation. -/
theorem isPerturbedUnitarySimilar_add (A E : Matrix n n 𝕜) :
    IsPerturbedUnitarySimilar A (A + E) (specNorm E) := by
  simpa using (IsPerturbedUnitarySimilar.refl A).add_right E

/-- Backward error zero is an exact unitary similarity:
$\mathbf{B} = \mathbf{U}^{\mathsf{H}}(\mathbf{A} + \mathbf{E})\mathbf{U}$ with
$\|\mathbf{E}\|_2 \le 0$ exactly when $\mathbf{B} = \mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{U}$ for
a unitary $\mathbf{U}$. -/
theorem isPerturbedUnitarySimilar_zero_iff {A B : Matrix n n 𝕜} :
    IsPerturbedUnitarySimilar A B 0 ↔
      ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧ B = Uᴴ * A * U := by
  constructor
  · rintro ⟨U, E, hU, hE, rfl⟩
    obtain rfl : E = 0 := specNorm_eq_zero_iff.mp (le_antisymm hE (specNorm_nonneg E))
    exact ⟨U, hU, by rw [add_zero]⟩
  · rintro ⟨U, hU, rfl⟩
    exact ⟨U, 0, hU, by rw [specNorm_zero], by rw [add_zero]⟩

/-- An exact unitary similarity $\mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{U}$ is a perturbed
unitary similarity of $\mathbf{A}$ with backward error $0$. -/
theorem HasOrthonormalCols.isPerturbedUnitarySimilar {U : Matrix n n 𝕜} (hU : HasOrthonormalCols U)
    (A : Matrix n n 𝕜) : IsPerturbedUnitarySimilar A (Uᴴ * A * U) 0 :=
  isPerturbedUnitarySimilar_zero_iff.mpr ⟨U, hU, rfl⟩

/-- The spectral norm of a matrix with one nonzero entry $x$ is at most $\lvert x \rvert$. -/
theorem specNorm_single_le (i j : n) (x : 𝕜) : specNorm (Matrix.single i j x) ≤ ‖x‖ := by
  refine (specNorm_le_frobNorm _).trans (le_of_eq ?_)
  have h : frobNorm (Matrix.single i j x) ^ 2 = ‖x‖ ^ 2 := by
    rw [frobNorm_sq_eq_sum]
    simp [Matrix.single_apply, apply_ite (fun y : 𝕜 => ‖y‖ ^ 2), ite_and]
  exact (pow_left_inj₀ (frobNorm_nonneg _) (norm_nonneg x) two_ne_zero).mp h

/-- Deflation adds the modulus of the zeroed entry: if $\mathbf{B}$ is a perturbed unitary
similarity of $\mathbf{A}$ with backward error $\varepsilon$ and
$\lvert b_{ij} \rvert \le \delta$, then $\mathbf{B}$ with the entry $(i, j)$ set to zero is one
with $\varepsilon + \delta$.
[BanksGarzaVargasSrivastava2022, §6] (Deflate). -/
theorem IsPerturbedUnitarySimilar.sub_single {A B : Matrix n n 𝕜} {ε δ : ℝ}
    (h : IsPerturbedUnitarySimilar A B ε) (i j : n) (hδ : ‖B i j‖ ≤ δ) :
    IsPerturbedUnitarySimilar A (B - Matrix.single i j (B i j)) (ε + δ) := by
  rw [sub_eq_add_neg]
  refine (h.add_right _).mono (add_le_add_right ?_ _)
  rw [specNorm_neg]
  exact (specNorm_single_le i j _).trans hδ

/-- A step read through a constructed unitary: if $\mathbf{U}$ is unitary and
$\|\mathbf{B} - \mathbf{U}^{\mathsf{H}}\mathbf{A}\mathbf{U}\|_2 \le \varepsilon$, then
$\mathbf{B}$ is a perturbed unitary similarity of $\mathbf{A}$ with backward error
$\varepsilon$. The form of a rounded kernel that returns an exact similarity plus an error. -/
theorem IsPerturbedUnitarySimilar.of_specNorm_sub_le {U A B : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) {ε : ℝ} (h : specNorm (B - Uᴴ * A * U) ≤ ε) :
    IsPerturbedUnitarySimilar A B ε := by
  have h' := (hU.isPerturbedUnitarySimilar A).add_right (B - Uᴴ * A * U)
  rw [add_sub_cancel, zero_add] at h'
  exact h'.mono h

/-- A nearly unitary transformation: if $\mathbf{U}$ is unitary and
$\|\hat{\mathbf{U}} - \mathbf{U}\|_2 \le \eta$, then $\hat{\mathbf{U}}^{\mathsf{H}}\mathbf{A}
\hat{\mathbf{U}}$ is a perturbed unitary similarity of $\mathbf{A}$ with backward error
$(2\eta + \eta^2)\|\mathbf{A}\|_2$. The form of a rounded kernel whose computed rotation is
within $\eta$ of an exact one. [Higham2002, §19.3]. -/
theorem IsPerturbedUnitarySimilar.of_near_unitary {U Û : Matrix n n 𝕜}
    (hU : HasOrthonormalCols U) {η : ℝ} (hη : specNorm (Û - U) ≤ η) (A : Matrix n n 𝕜) :
    IsPerturbedUnitarySimilar A (Ûᴴ * A * Û) ((2 * η + η ^ 2) * specNorm A) := by
  refine IsPerturbedUnitarySimilar.of_specNorm_sub_le hU ?_
  have e : Ûᴴ * A * Û - Uᴴ * A * U = (Û - U)ᴴ * A * Û + Uᴴ * A * (Û - U) := by
    simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have ha := specNorm_nonneg A
  have hd := specNorm_nonneg (Û - U)
  have hÛ : specNorm Û ≤ 1 + η := by
    have := specNorm_add_le U (Û - U)
    rw [add_sub_cancel] at this
    linarith [hU.specNorm_le_one]
  have h₁ : specNorm ((Û - U)ᴴ * A * Û) ≤ η * specNorm A * (1 + η) := by
    refine (specNorm_mul_le _ _).trans ?_
    refine mul_le_mul ((specNorm_mul_le _ _).trans ?_) hÛ (specNorm_nonneg _)
      (mul_nonneg (hd.trans hη) ha)
    rw [specNorm_conjTranspose]
    exact mul_le_mul_of_nonneg_right hη ha
  have h₂ : specNorm (Uᴴ * A * (Û - U)) ≤ specNorm A * η := by
    refine (specNorm_mul_le _ _).trans (mul_le_mul ((specNorm_mul_le _ _).trans ?_) hη hd ha)
    rw [specNorm_conjTranspose]
    nlinarith [hU.specNorm_le_one]
  rw [e]
  refine (specNorm_add_le _ _).trans ?_
  nlinarith

/-- Relabelling the indices: a perturbed unitary similarity stays one, with the same backward
error, after both matrices are reindexed by the same bijection. -/
theorem IsPerturbedUnitarySimilar.submatrix_equiv {A B : Matrix n n 𝕜} {ε : ℝ}
    (h : IsPerturbedUnitarySimilar A B ε) (e : m ≃ n) :
    IsPerturbedUnitarySimilar (A.submatrix e e) (B.submatrix e e) ε := by
  obtain ⟨U, E, hU, hE, rfl⟩ := h
  refine ⟨U.submatrix e e, E.submatrix e e, ?_, by rwa [specNorm_submatrix_equiv], ?_⟩
  · rw [hasOrthonormalCols_iff, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      hU.conjTranspose_mul_self, Matrix.submatrix_one_equiv]
  · rw [Matrix.conjTranspose_submatrix,
      show A.submatrix e e + E.submatrix e e = (A + E).submatrix e e from rfl,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

/-- A step on a principal block is a step on the whole matrix: for an injective
$e : m \to n$ (the indices of a block, such as a range of a partition), if $\mathbf{B}$ is a
perturbed unitary similarity of the principal block $\mathbf{A}_{ee}$ with backward error
$\varepsilon$, there is $\mathbf{A}'$, a perturbed unitary similarity of $\mathbf{A}$ with
backward error $\varepsilon$, whose block $\mathbf{A}'_{ee}$ is $\mathbf{B}$, whose entries with
both indices off the block are those of $\mathbf{A}$, and which is block triangular for every
labelling $L$ that labels the block by one value and for which $\mathbf{A}$ is. -/
theorem IsPerturbedUnitarySimilar.exists_submatrix {e : m → n} (he : Function.Injective e)
    {A : Matrix n n 𝕜} {B : Matrix m m 𝕜} {ε : ℝ}
    (h : IsPerturbedUnitarySimilar (A.submatrix e e) B ε) :
    ∃ A' : Matrix n n 𝕜, IsPerturbedUnitarySimilar A A' ε ∧ A'.submatrix e e = B ∧
      (∀ i j, i ∉ Set.range e → j ∉ Set.range e → A' i j = A i j) ∧
      ∀ {β : Type} [LinearOrder β] (L : n → β) (l : β), (∀ a, L (e a) = l) →
        A.BlockTriangular L → A'.BlockTriangular L := by
  obtain ⟨U, E, hU, hE, rfl⟩ := h
  set Q : Matrix n m 𝕜 := (1 : Matrix n n 𝕜).submatrix id e with hQdef
  have hsub : ∀ X : Matrix n n 𝕜, Qᴴ * X * Q = X.submatrix e e := fun X => by
    ext a b
    simp [Q, Matrix.mul_apply, Matrix.one_apply]
  have hQ : HasOrthonormalCols Q := by
    rw [hasOrthonormalCols_iff, ← Matrix.mul_one Qᴴ, hsub, Matrix.submatrix_one _ he]
  have hrow : ∀ i, i ∉ Set.range e → ∀ (Y : Matrix m n 𝕜) j, (Q * Y) i j = 0 :=
    fun i hi Y j => by
      have hne : ∀ a, i ≠ e a := fun a h => hi ⟨a, h.symm⟩
      simp [Q, Matrix.mul_apply, hne]
  have hcol : ∀ j, j ∉ Set.range e → ∀ (Y : Matrix n m 𝕜) i, (Y * Qᴴ) i j = 0 :=
    fun j hj Y i => by
      rw [← Matrix.conjTranspose_conjTranspose (Y * Qᴴ), Matrix.conjTranspose_apply,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hrow j hj, star_zero]
  have hQQY : ∀ Y : Matrix m n 𝕜, Qᴴ * (Q * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hQ.conjTranspose_mul_self, Matrix.one_mul]
  set W := 1 + Q * (U - 1) * Qᴴ with hW
  have hWH : Wᴴ = 1 + Q * (Uᴴ - 1) * Qᴴ := by
    simp [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.mul_assoc]
  have key : (Uᴴ - 1) + (U - 1) + (Uᴴ - 1) * (U - 1) = 0 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, hU.conjTranspose_mul_self, Matrix.mul_one,
      Matrix.one_mul]
    abel
  have hWW : HasOrthonormalCols W := by
    rw [hasOrthonormalCols_iff, hWH]
    calc _ = 1 + Q * ((Uᴴ - 1) + (U - 1) + (Uᴴ - 1) * (U - 1)) * Qᴴ := by
          simp only [W, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
            Matrix.mul_assoc, hQQY]
          abel
      _ = 1 := by rw [key]; simp
  have hWQ : W * Q = Q * U := by
    simp only [W, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hQ.conjTranspose_mul_self,
      Matrix.mul_one, Matrix.mul_sub]
    abel
  set X := A + Q * E * Qᴴ with hX
  refine ⟨Wᴴ * X * W, ⟨W, Q * E * Qᴴ, hWW, ?_, rfl⟩, ?_, fun i j hi hj => ?_, ?_⟩
  · rwa [hQ.specNorm_mul_conjTranspose_right, hQ.specNorm_mul_left]
  · have hXQ : Qᴴ * X * Q = A.submatrix e e + E := by
      rw [hX, Matrix.mul_add, Matrix.add_mul, hsub A]
      congr 1
      simp only [Matrix.mul_assoc, hQQY, hQ.conjTranspose_mul_self, Matrix.mul_one]
    rw [← hsub, show Qᴴ * (Wᴴ * X * W) * Q = (W * Q)ᴴ * X * (W * Q) by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc], hWQ, ← hXQ]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · have e' : Wᴴ * X * W = A + Q * (E * Qᴴ) + Q * ((Uᴴ - 1) * Qᴴ * X * W) +
        X * Q * (U - 1) * Qᴴ := by
      rw [hWH]
      simp only [W, X, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_assoc]
      abel
    rw [e', Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, hrow i hi, hrow i hi,
      hcol j hj]
    simp
  · intro β _ L l hL hA
    have hBT : ∀ Z : Matrix m m 𝕜, (Q * Z * Qᴴ).BlockTriangular L := by
      intro Z i j hij
      by_cases hi : i ∈ Set.range e
      · by_cases hj : j ∈ Set.range e
        · obtain ⟨a, rfl⟩ := hi
          obtain ⟨b, rfl⟩ := hj
          rw [hL, hL] at hij
          exact absurd hij (lt_irrefl _)
        · exact hcol j hj _ i
      · rw [Matrix.mul_assoc]
        exact hrow i hi _ j
    rw [hWH]
    exact ((Matrix.blockTriangular_one.add (hBT _)).mul (hA.add (hBT _))).mul
      (Matrix.blockTriangular_one.add (hBT _))

/-- The block-diagonal unitary that acts as $\mathbf{U}$ on the first block. -/
private theorem hasOrthonormalCols_fromBlocks_one {U : Matrix m m 𝕜} (hU : HasOrthonormalCols U) :
    HasOrthonormalCols (Matrix.fromBlocks U 0 0 (1 : Matrix p p 𝕜)) := by
  rw [hasOrthonormalCols_iff, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    hU.conjTranspose_mul_self]
  simp [Matrix.fromBlocks_one]

/-- A step on the leading diagonal block is a step on the whole matrix: if $\mathbf{B}_1$ is a
perturbed unitary similarity of $\mathbf{A}_1$ with backward error $\varepsilon$, then
$\begin{bmatrix} \mathbf{B}_1 & \mathbf{X}' \\ \mathbf{0} & \mathbf{A}_2 \end{bmatrix}$ is one of
$\begin{bmatrix} \mathbf{A}_1 & \mathbf{X} \\ \mathbf{0} & \mathbf{A}_2 \end{bmatrix}$ with
$\varepsilon$, for some off-diagonal block $\mathbf{X}'$. -/
theorem IsPerturbedUnitarySimilar.exists_fromBlocks₁₁ {A₁ B₁ : Matrix m m 𝕜} {ε : ℝ}
    (h : IsPerturbedUnitarySimilar A₁ B₁ ε) (X : Matrix m p 𝕜) (A₂ : Matrix p p 𝕜) :
    ∃ X' : Matrix m p 𝕜, IsPerturbedUnitarySimilar (Matrix.fromBlocks A₁ X 0 A₂)
      (Matrix.fromBlocks B₁ X' 0 A₂) ε := by
  obtain ⟨U, E, hU, hE, rfl⟩ := h
  refine ⟨Uᴴ * X, Matrix.fromBlocks U 0 0 1, Matrix.fromBlocks E 0 0 0,
    hasOrthonormalCols_fromBlocks_one hU, ?_, ?_⟩
  · rw [specNorm_fromBlocks_zero₁₂_zero₂₁, specNorm_zero]
    exact max_le hE ((specNorm_nonneg E).trans hE)
  · rw [Matrix.fromBlocks_add, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp

/-- A step on the trailing diagonal block is a step on the whole matrix: if $\mathbf{B}_2$ is
a perturbed unitary similarity of $\mathbf{A}_2$ with backward error $\varepsilon$, then
$\begin{bmatrix} \mathbf{A}_1 & \mathbf{X}' \\ \mathbf{0} & \mathbf{B}_2 \end{bmatrix}$ is one of
$\begin{bmatrix} \mathbf{A}_1 & \mathbf{X} \\ \mathbf{0} & \mathbf{A}_2 \end{bmatrix}$ with
$\varepsilon$, for some off-diagonal block $\mathbf{X}'$. -/
theorem IsPerturbedUnitarySimilar.exists_fromBlocks₂₂ {A₂ B₂ : Matrix p p 𝕜} {ε : ℝ}
    (h : IsPerturbedUnitarySimilar A₂ B₂ ε) (A₁ : Matrix m m 𝕜) (X : Matrix m p 𝕜) :
    ∃ X' : Matrix m p 𝕜, IsPerturbedUnitarySimilar (Matrix.fromBlocks A₁ X 0 A₂)
      (Matrix.fromBlocks A₁ X' 0 B₂) ε := by
  obtain ⟨U, E, hU, hE, rfl⟩ := h
  have hW : HasOrthonormalCols (Matrix.fromBlocks (1 : Matrix m m 𝕜) 0 0 U) := by
    rw [hasOrthonormalCols_iff, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      hU.conjTranspose_mul_self]
    simp [Matrix.fromBlocks_one]
  refine ⟨X * U, Matrix.fromBlocks 1 0 0 U, Matrix.fromBlocks 0 0 0 E, hW, ?_, ?_⟩
  · rw [specNorm_fromBlocks_zero₁₂_zero₂₁, specNorm_zero]
    exact max_le ((specNorm_nonneg E).trans hE) hE
  · rw [Matrix.fromBlocks_add, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp

/-! ### The witnessed relation: the unitary named -/

/-- $\mathbf{B}$ is a perturbed unitary similarity of $\mathbf{A}$ by the named unitary
$\mathbf{V}$ with backward error $\varepsilon$: $\mathbf{V}$ has orthonormal columns and
$\mathbf{B} = \mathbf{V}^{\mathsf{H}}(\mathbf{A} + \mathbf{E})\mathbf{V}$ with
$\|\mathbf{E}\|_2 \le \varepsilon$. It is `NLAlib.IsPerturbedUnitarySimilar` with its unitary
exposed (`NLAlib.isPerturbedUnitarySimilar_iff_exists_by`), for consumers that need the unitary:
computed Schur vectors, an accumulated product of rotations. -/
def IsPerturbedUnitarySimilarBy (V A B : Matrix n n 𝕜) (ε : ℝ) : Prop :=
  HasOrthonormalCols V ∧ ∃ E : Matrix n n 𝕜, specNorm E ≤ ε ∧ B = Vᴴ * (A + E) * V

/-- Forgetting the unitary. -/
theorem IsPerturbedUnitarySimilarBy.isPerturbedUnitarySimilar {V A B : Matrix n n 𝕜} {ε : ℝ}
    (h : IsPerturbedUnitarySimilarBy V A B ε) : IsPerturbedUnitarySimilar A B ε := by
  obtain ⟨hV, E, hE, rfl⟩ := h
  exact ⟨V, E, hV, hE, rfl⟩

/-- The hidden unitary of a perturbed unitary similarity can be named. -/
theorem isPerturbedUnitarySimilar_iff_exists_by {A B : Matrix n n 𝕜} {ε : ℝ} :
    IsPerturbedUnitarySimilar A B ε ↔ ∃ V, IsPerturbedUnitarySimilarBy V A B ε := by
  constructor
  · rintro ⟨V, E, hV, hE, rfl⟩
    exact ⟨V, hV, E, hE, rfl⟩
  · rintro ⟨V, h⟩
    exact h.isPerturbedUnitarySimilar

/-- The identity carries every matrix to itself with backward error $0$. -/
theorem IsPerturbedUnitarySimilarBy.refl (A : Matrix n n 𝕜) :
    IsPerturbedUnitarySimilarBy 1 A A 0 := sorry

/-- Backward errors add and the unitaries multiply: $\mathbf{V}\mathbf{W}$ carries $\mathbf{A}$
to $\mathbf{C}$. -/
theorem IsPerturbedUnitarySimilarBy.trans {V W A B C : Matrix n n 𝕜} {ε₁ ε₂ : ℝ}
    (h₁ : IsPerturbedUnitarySimilarBy V A B ε₁) (h₂ : IsPerturbedUnitarySimilarBy W B C ε₂) :
    IsPerturbedUnitarySimilarBy (V * W) A C (ε₁ + ε₂) := sorry

/-- A larger backward error is weaker. -/
theorem IsPerturbedUnitarySimilarBy.mono {V A B : Matrix n n 𝕜} {ε ε' : ℝ}
    (h : IsPerturbedUnitarySimilarBy V A B ε) (hε : ε ≤ ε') :
    IsPerturbedUnitarySimilarBy V A B ε' := by
  obtain ⟨hV, E, hE, rfl⟩ := h
  exact ⟨hV, E, hE.trans hε, rfl⟩

/-- The witnessed lift to a leading diagonal block with a computed coupling block: a step
by $\mathbf{V}$ on $\mathbf{A}_1$ and a computed coupling $\mathbf{X}'$ within $\rho$ of
$\mathbf{V}^{\mathsf H}\mathbf{X}$ give a step by $\operatorname{diag}(\mathbf{V}, \mathbf{I})$ on
the block upper triangular matrix, with backward error $\varepsilon + \rho$. The witnessed form
of `NLAlib.IsPerturbedUnitarySimilar.exists_fromBlocks₁₁`. -/
theorem IsPerturbedUnitarySimilarBy.fromBlocks₁₁ {V A₁ B₁ : Matrix m m 𝕜} {ε ρ : ℝ}
    (h : IsPerturbedUnitarySimilarBy V A₁ B₁ ε) {X X' : Matrix m p 𝕜} (A₂ : Matrix p p 𝕜)
    (hX : specNorm (X' - Vᴴ * X) ≤ ρ) :
    IsPerturbedUnitarySimilarBy (Matrix.fromBlocks V 0 0 1) (Matrix.fromBlocks A₁ X 0 A₂)
      (Matrix.fromBlocks B₁ X' 0 A₂) (ε + ρ) := sorry

/-- The witnessed lift to a trailing diagonal block with a computed coupling block: a step
by $\mathbf{V}$ on $\mathbf{A}_2$ and a computed coupling $\mathbf{X}'$ within $\rho$ of
$\mathbf{X}\mathbf{V}$ give a step by $\operatorname{diag}(\mathbf{I}, \mathbf{V})$, with
backward error $\varepsilon + \rho$. The witnessed form of
`NLAlib.IsPerturbedUnitarySimilar.exists_fromBlocks₂₂`. -/
theorem IsPerturbedUnitarySimilarBy.fromBlocks₂₂ {V A₂ B₂ : Matrix p p 𝕜} {ε ρ : ℝ}
    (h : IsPerturbedUnitarySimilarBy V A₂ B₂ ε) (A₁ : Matrix m m 𝕜) {X X' : Matrix m p 𝕜}
    (hX : specNorm (X' - X * V) ≤ ρ) :
    IsPerturbedUnitarySimilarBy (Matrix.fromBlocks 1 0 0 V) (Matrix.fromBlocks A₁ X 0 A₂)
      (Matrix.fromBlocks A₁ X' 0 B₂) (ε + ρ) := sorry

/-! ### Range blocks of a matrix of order `N` -/

/-- The index $lo + i$ of the range $[lo, lo + d)$ of `Fin N`. -/
def rangeEmb {N lo d : ℕ} (h : lo + d ≤ N) (i : Fin d) : Fin N :=
  ⟨lo + i, by omega⟩

/-- The square matrix acting by $\mathbf{V}$ on the range $[lo, lo + d)$ and by the identity
off it: $\operatorname{diag}(\mathbf{I}_{lo}, \mathbf{V}, \mathbf{I})$. -/
def embedBlock {N : ℕ} (lo : ℕ) {d : ℕ} (V : Matrix (Fin d) (Fin d) 𝕜) :
    Matrix (Fin N) (Fin N) 𝕜 :=
  Matrix.of fun i j =>
    if hi : lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d then
      if hj : lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d then V ⟨i - lo, by omega⟩ ⟨j - lo, by omega⟩
      else 0
    else if i = j then 1 else 0

/-- The coupling part of `X` for the range $[lo, lo + d)$: the entries with exactly one index
in the range, zero elsewhere. -/
def couplingPart {N : ℕ} (lo d : ℕ) (X : Matrix (Fin N) (Fin N) 𝕜) : Matrix (Fin N) (Fin N) 𝕜 :=
  Matrix.of fun i j =>
    if (lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d) ↔ (lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d) then 0 else X i j

/-- `T` is block upper triangular for the three ranges $[0, lo)$, $[lo, lo + d)$,
$[lo + d, N)$: the entries below the diagonal blocks vanish. -/
def IsRangeBlockTriangular {N : ℕ} (lo d : ℕ) (T : Matrix (Fin N) (Fin N) 𝕜) : Prop :=
  ∀ i j : Fin N, ((j : ℕ) < lo ∧ lo ≤ (i : ℕ)) ∨ ((j : ℕ) < lo + d ∧ lo + d ≤ (i : ℕ)) →
    T i j = 0

/-- A step on the range block $[lo, lo + d)$ of a block upper triangular matrix, with computed
couplings (the range form of `NLAlib.IsPerturbedUnitarySimilarBy.fromBlocks₁₁` and
`NLAlib.IsPerturbedUnitarySimilarBy.fromBlocks₂₂`): if the block of `T'` is a step by $\mathbf{V}$
on the block of `T` with backward error $\varepsilon$, `T'` agrees with `T` off the range, keeps
the zero blocks, and its couplings are within $\rho$ of the exact
$\widetilde{\mathbf{V}}^{\mathsf H}\mathbf{T}\widetilde{\mathbf{V}}$,
$\widetilde{\mathbf{V}} = \operatorname{diag}(\mathbf{I}, \mathbf{V}, \mathbf{I})$, then `T'` is
a step on `T` by $\widetilde{\mathbf{V}}$ with backward error $\varepsilon + \rho$. -/
theorem IsPerturbedUnitarySimilarBy.of_range_block {N lo d : ℕ} (hN : lo + d ≤ N)
    {T T' : Matrix (Fin N) (Fin N) 𝕜} {V : Matrix (Fin d) (Fin d) 𝕜} {ε ρ : ℝ}
    (hT : IsRangeBlockTriangular lo d T) (hT' : IsRangeBlockTriangular lo d T')
    (h : IsPerturbedUnitarySimilarBy V (T.submatrix (rangeEmb hN) (rangeEmb hN))
      (T'.submatrix (rangeEmb hN) (rangeEmb hN)) ε)
    (hout : ∀ i j : Fin N, ¬(lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d) →
      ¬(lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d) → T' i j = T i j)
    (hcpl : specNorm (couplingPart lo d (T' - (embedBlock lo V)ᴴ * T * embedBlock lo V)) ≤ ρ) :
    IsPerturbedUnitarySimilarBy (embedBlock lo V) T T' (ε + ρ) := sorry

/-! ### The tracked relation: a stored accumulator and the exact unitary -/

/-- The tracked unitary similarity with errors $(\varepsilon_U, \varepsilon_T)$: an exact
unitary $\mathbf{V}$ carries $\mathbf{A}$ to $\mathbf{A}'$ with backward error $\varepsilon_T$
(`NLAlib.IsPerturbedUnitarySimilarBy`), and the stored accumulator moves from $\mathbf{U}$ to
within $\varepsilon_U\|\mathbf{U}\|_2$ of $\mathbf{U}\mathbf{V}$ (a relative error, so that
accumulations telescope as $(1 + a)(1 + b) - 1$). The state relation of a Schur pipeline: the
two errors stay apart, $\varepsilon_U$ a deterministic rounding error, $\varepsilon_T$ the
backward error. -/
def IsTrackedUnitarySimilar (εU εT : ℝ) (U A U' A' : Matrix n n 𝕜) : Prop :=
  ∃ V : Matrix n n 𝕜, IsPerturbedUnitarySimilarBy V A A' εT ∧
    specNorm (U' - U * V) ≤ εU * specNorm U

/-- A witnessed step with an exactly updated accumulator is a tracked step with $\varepsilon_U
= 0$. -/
theorem IsTrackedUnitarySimilar.of_by {V A A' U : Matrix n n 𝕜} {εT : ℝ}
    (h : IsPerturbedUnitarySimilarBy V A A' εT) :
    IsTrackedUnitarySimilar 0 εT U A (U * V) A' :=
  ⟨V, h, by simp⟩

/-- No step: errors $0$. -/
theorem IsTrackedUnitarySimilar.refl (U A : Matrix n n 𝕜) :
    IsTrackedUnitarySimilar 0 0 U A U A := sorry

/-- Tracked steps compose: the backward errors add, the relative accumulator errors compose
as $(1 + \varepsilon_U)(1 + \varepsilon_U') - 1$. -/
theorem IsTrackedUnitarySimilar.trans {εU εT εU' εT' : ℝ} {U A U' A' U'' A'' : Matrix n n 𝕜}
    (hεU : 0 ≤ εU) (hεU' : 0 ≤ εU') (h : IsTrackedUnitarySimilar εU εT U A U' A')
    (h' : IsTrackedUnitarySimilar εU' εT' U' A' U'' A'') :
    IsTrackedUnitarySimilar ((1 + εU) * (1 + εU') - 1) (εT + εT') U A U'' A'' := sorry

/-- Larger errors are weaker. -/
theorem IsTrackedUnitarySimilar.mono {εU εT εU' εT' : ℝ} {U A U' A' : Matrix n n 𝕜}
    (h : IsTrackedUnitarySimilar εU εT U A U' A') (hU : εU ≤ εU') (hT : εT ≤ εT') :
    IsTrackedUnitarySimilar εU' εT' U A U' A' := by
  obtain ⟨V, hV, hU'⟩ := h
  exact ⟨V, hV.mono hT, hU'.trans (mul_le_mul_of_nonneg_right hU (specNorm_nonneg U))⟩

/-- The computed Schur form from a tracked run started at $(\mathbf{I}, \mathbf{A})$: with
$\varepsilon_U \le 1/8$, $\|\mathbf{A} - \widehat{\mathbf{U}}\widehat{\mathbf{T}}
\widehat{\mathbf{U}}^{\mathsf H}\|_2 \le \varepsilon_T + (2\varepsilon_U + \varepsilon_U^2)
(\|\mathbf{A}\|_2 + \varepsilon_T)$ and $\|\widehat{\mathbf{U}}^{\mathsf H}\widehat{\mathbf{U}} -
\mathbf{I}\|_2 \le 2\varepsilon_U + \varepsilon_U^2$. -/
theorem IsTrackedUnitarySimilar.specNorm_sub_mul_mul_conjTranspose_le {εU εT : ℝ}
    {A U T : Matrix n n 𝕜} (h : IsTrackedUnitarySimilar εU εT 1 A U T) (hεU0 : 0 ≤ εU)
    (hεU : εU ≤ 1 / 8) :
    specNorm (A - U * T * Uᴴ) ≤ εT + (2 * εU + εU ^ 2) * (specNorm A + εT) ∧
      specNorm (Uᴴ * U - 1) ≤ 2 * εU + εU ^ 2 := sorry

/-- The exact-unitary form of a tracked run from $(\mathbf{I}, \mathbf{A})$: an exact unitary
$\mathbf{V}$ within $\varepsilon_U$ of $\widehat{\mathbf{U}}$ with $\mathbf{A} + \mathbf{E} =
\mathbf{V}\widehat{\mathbf{T}}\mathbf{V}^{\mathsf H}$, $\|\mathbf{E}\|_2 \le \varepsilon_T$. -/
theorem IsTrackedUnitarySimilar.exists_eq_mul_mul_conjTranspose {εU εT : ℝ}
    {A U T : Matrix n n 𝕜} (h : IsTrackedUnitarySimilar εU εT 1 A U T) (hεU0 : 0 ≤ εU) :
    ∃ V E : Matrix n n 𝕜, HasOrthonormalCols V ∧ specNorm (U - V) ≤ εU ∧
      specNorm E ≤ εT ∧ A + E = V * T * Vᴴ := sorry

/-- A leaf lift with a dense computed unitary: the leaf's tracked relation on the range block
$[lo, lo + d)$ (from $(\mathbf{I}, \mathbf{B})$ to $(\mathbf{U}_b, \mathbf{T}_b)$), computed
couplings within $\rho$ of those by $\operatorname{diag}(\mathbf{I}, \mathbf{U}_b, \mathbf{I})$,
and a computed accumulator within $\rho_U\|\mathbf{U}\|_2$ of
$\mathbf{U}\operatorname{diag}(\mathbf{I}, \mathbf{U}_b, \mathbf{I})$ give a tracked step on the
whole matrix. The extra backward error $2\varepsilon_U\|\mathbf{T}\|_2$ is the coupling computed
with $\mathbf{U}_b$ instead of the exact unitary. -/
theorem IsTrackedUnitarySimilar.lift_leaf_block {N lo d : ℕ} (hN : lo + d ≤ N)
    {T T' U U' : Matrix (Fin N) (Fin N) 𝕜} {Ub Tb : Matrix (Fin d) (Fin d) 𝕜}
    {εU εT ρ ρU : ℝ} (hεU0 : 0 ≤ εU) (hT : IsRangeBlockTriangular lo d T)
    (hT' : IsRangeBlockTriangular lo d T')
    (hleaf : IsTrackedUnitarySimilar εU εT 1 (T.submatrix (rangeEmb hN) (rangeEmb hN)) Ub Tb)
    (hblk : T'.submatrix (rangeEmb hN) (rangeEmb hN) = Tb)
    (hout : ∀ i j : Fin N, ¬(lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d) →
      ¬(lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d) → T' i j = T i j)
    (hcpl : specNorm (couplingPart lo d (T' - (embedBlock lo Ub)ᴴ * T * embedBlock lo Ub)) ≤ ρ)
    (hU : specNorm (U' - U * embedBlock lo Ub) ≤ ρU * specNorm U) :
    IsTrackedUnitarySimilar (εU + ρU) (εT + ρ + 2 * εU * specNorm T) U T U' T' := sorry

end NLAlib
