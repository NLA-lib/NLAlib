/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import NLAlib.Matrix.Spectral.CourantFischer
public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Pseudoinverse.Pinv

/-!
# Functions of a Hermitian matrix

For a Hermitian matrix $\mathbf{A}$ and a function $f$ from $\mathbb{R}$ to $\mathbb{R}$, the
matrix $f(\mathbf{A})$ is Mathlib's continuous functional calculus `cfc`. This file gives the
working API in the vocabulary of this library: $f(\mathbf{A})$ through any unitary
diagonalisation, its trace, eigenvalues, quadratic form and spectral norm, and its behaviour under
unitary conjugation and block diagonal sums; the inverse and the inverse square root of a positive
definite matrix are functions of it.

No definition is introduced. `cfc f A` is the spelling of $f(\mathbf{A})$; the square root
$\mathbf{A}^{1/2}$ is `CFC.sqrt`, a real power $\mathbf{A}^r$ of a positive semidefinite matrix is
`A ^ r`, the absolute value $\lvert \mathbf{A} \rvert$ is `CFC.abs` and the positive part
$\mathbf{A}^{+}$ is `A⁺`, all from Mathlib and all available with `open scoped MatrixOrder`. They
unfold to `cfc` by `CFC.sqrt_eq_real_sqrt`, `CFC.rpow_eq_cfc_real`, `CFC.abs_eq_cfc_norm` and
`CFC.posPart_def` (the first and the last to the non-unital `cfcₙ`, which is `cfc` by
`cfcₙ_eq_cfc`). General facts are Mathlib's: `cfc_predicate` ($f(\mathbf{A})$ is Hermitian),
`cfc_commute_cfc`, `cfc_mono` (comparison on the spectrum), `cfc_nonneg`, `cfc_pow_id`,
`cfc_inv_id`, `cfc_polynomial`.

The location of the spectrum is the hypothesis that the real spectrum (Mathlib's `spectrum`) of
$\mathbf{A}$ lies in a set $s$, or a Loewner sandwich
$a\mathbf{I} \preceq \mathbf{A} \preceq b\mathbf{I}$ for an interval.

## Main results

* `NLAlib.HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose`:
  $f(\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}})
  = \mathbf{U} f(\mathbf{D}) \mathbf{U}^{\mathsf{H}}$.
* `Matrix.IsHermitian.cfc_mul_eq_mul_diagonal_of_mul_eq`: a function of $\mathbf{A}$ on an
  invariant frame, $\mathbf{A}\mathbf{W} = \mathbf{W}\operatorname{diag}(\mathbf{d})
  \Rightarrow f(\mathbf{A})\mathbf{W} = \mathbf{W}\operatorname{diag}(f(\mathbf{d}_i))$.
* `NLAlib.HasOrthonormalCols.cfc_mul_mul_conjTranspose`: a function of a zero-padded
  compression, $f(\mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf{H}}) =
  \mathbf{U}f(\mathbf{T})\mathbf{U}^{\mathsf{H}}
  + f(0)(\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf{H}})$.
* `Matrix.IsHermitian.spectrum_subset_iff`: the spectrum through the sorted eigenvalues.
* `Matrix.IsHermitian.smul_one_le_iff_spectrum_subset_Ici`,
  `Matrix.IsHermitian.le_smul_one_iff_spectrum_subset_Iic`: one-sided Loewner bounds are
  spectral bounds.
* `Matrix.IsHermitian.spectrum_conjTranspose_mul_mul_subset_Icc`: Ritz values stay in an
  interval containing the spectrum.
* `Matrix.IsHermitian.re_trace_cfc`:
  $\operatorname{tr} f(\mathbf{A}) = \sum_i f(\lambda_i(\mathbf{A}))$.
* `Matrix.IsHermitian.eigenvalue_cfc_of_monotoneOn`: eigenvalues of $f(\mathbf{A})$ for monotone
  $f$.
* `Matrix.IsHermitian.specNorm_cfc_le`: $\|f(\mathbf{A})\|_2 \le \max \lvert f \rvert$ on the
  spectrum.
* `NLAlib.HasOrthonormalCols.re_quadForm_cfc_eq_sum`: the quadratic form of $f(\mathbf{A})$ as a
  weighted sum.
* `Matrix.IsHermitian.norm_toLp_cfc_mulVec_sq`,
  `Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_le`: the norm of
  $\psi(\mathbf{A})\mathbf{x}$ as a quadratic form, and a Cauchy–Schwarz inequality for
  functions of one Hermitian matrix.
* `Matrix.IsHermitian.frobNorm_cfc_sub_cfc_le`: a $1$-Lipschitz function is $1$-Lipschitz in
  the Frobenius norm on Hermitian matrices over either scalar field [Kittaneh1985].
* `Matrix.IsHermitian.cfc_fromBlocks_zero₁₂_zero₂₁`, `NLAlib.cfc_blockDiagonal`: block diagonal
  sums.
* `Matrix.PosDef.inv_eq_cfc`, `Matrix.PosDef.inv_sqrt_eq_cfc`: the inverse and the inverse
  square root.
* `Matrix.IsHermitian.cfc_inv_eq_pinv`: the pseudoinverse of a Hermitian matrix is the function
  $x \mapsto x^{-1}$ of it (with $0^{-1} = 0$).
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Diagonalisation -/

/-- A matrix intertwining two real diagonal matrices intertwines their images under $f$: if
$\operatorname{diag}(\mathbf{d})\mathbf{W} = \mathbf{W}\operatorname{diag}(\mathbf{e})$ then
$\operatorname{diag}(f(\mathbf{d}_i))\mathbf{W}
= \mathbf{W}\operatorname{diag}(f(\mathbf{e}_j))$. -/
private theorem diagonal_mul_eq_mul_diagonal_of_eq {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] {W : Matrix p q 𝕜} {d : p → ℝ} {e : q → ℝ}
    (h : Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * W =
      W * Matrix.diagonal fun j => ((e j : ℝ) : 𝕜)) (f : ℝ → ℝ) :
    Matrix.diagonal (fun i => ((f (d i) : ℝ) : 𝕜)) * W =
      W * Matrix.diagonal fun j => ((f (e j) : ℝ) : 𝕜) := by
  ext i j
  have hij := congrFun (congrFun h i) j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij ⊢
  by_cases hW : W i j = 0
  · rw [hW, mul_zero, zero_mul]
  · have hde : d i = e j := by
      rw [mul_comm] at hij
      exact RCLike.ofReal_injective (mul_left_cancel₀ hW hij)
    rw [hde, mul_comm]

/-- $f(\mathbf{A})$ through a unitary diagonalisation: if
$\mathbf{A} = \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$ with $\mathbf{d}$
real and $\mathbf{U}$ unitary, that is, with orthonormal columns and as many columns as rows, on
any column index type, then
$f(\mathbf{A}) = \mathbf{U}\operatorname{diag}(f(\mathbf{d}_i))\mathbf{U}^{\mathsf{H}}$. The frame
of the spectral theorem `Matrix.IsHermitian.exists_eq_mul_diagonal_mul_conjTranspose` is such a
$\mathbf{U}$. -/
theorem HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose {r : Type*} [Fintype r]
    [DecidableEq r]
    {A : Matrix n n 𝕜} {U : Matrix n r 𝕜} {d : r → ℝ} (hU : HasOrthonormalCols U)
    (hr : Fintype.card r = Fintype.card n)
    (hA : A = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) (f : ℝ → ℝ) :
    cfc f A = U * Matrix.diagonal (fun i => ((f (d i) : ℝ) : 𝕜)) * Uᴴ := by
  have hH : A.IsHermitian := by
    rw [hA]
    refine Matrix.isHermitian_mul_mul_conjTranspose U ?_
    rw [Matrix.isHermitian_diagonal_iff]
    exact fun i => RCLike.conj_ofReal (d i)
  have hUU : U * Uᴴ = 1 := hU.mul_conjTranspose_self_of_card_eq hr.symm
  have hV := hH.hasOrthonormalCols_eigenvectorUnitary
  have hAV : A = (hH.eigenvectorUnitary : Matrix n n 𝕜) *
      Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : 𝕜)) *
        (hH.eigenvectorUnitary : Matrix n n 𝕜)ᴴ := by
    have h := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h
  have hcfc : cfc f A = (hH.eigenvectorUnitary : Matrix n n 𝕜) *
      Matrix.diagonal (fun i => ((f (hH.eigenvalues i) : ℝ) : 𝕜)) *
        (hH.eigenvectorUnitary : Matrix n n 𝕜)ᴴ := by
    rw [hH.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rfl
  generalize (hH.eigenvectorUnitary : Matrix n n 𝕜) = V at hV hAV hcfc
  have hW : Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * (Uᴴ * V) =
      Uᴴ * V * Matrix.diagonal fun i => ((hH.eigenvalues i : ℝ) : 𝕜) := by
    calc Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * (Uᴴ * V)
        = Uᴴ * (U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) * V := by
          simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]
      _ = Uᴴ * A * V := by rw [← hA]
      _ = Uᴴ * (V * Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : 𝕜)) * Vᴴ) * V := by
          rw [← hAV]
      _ = Uᴴ * V * Matrix.diagonal fun i => ((hH.eigenvalues i : ℝ) : 𝕜) := by
          simp only [Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.mul_one]
  have hfW := diagonal_mul_eq_mul_diagonal_of_eq hW f
  rw [hcfc]
  calc V * Matrix.diagonal (fun i => ((f (hH.eigenvalues i) : ℝ) : 𝕜)) * Vᴴ
      = U * (Uᴴ * V * Matrix.diagonal fun i => ((f (hH.eigenvalues i) : ℝ) : 𝕜)) * Vᴴ := by
        simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
    _ = U * Matrix.diagonal (fun i => ((f (d i) : ℝ) : 𝕜)) * Uᴴ * (V * Vᴴ) := by
        rw [← hfW]
        simp only [Matrix.mul_assoc]
    _ = U * Matrix.diagonal (fun i => ((f (d i) : ℝ) : 𝕜)) * Uᴴ := by
        rw [hV.mul_conjTranspose_self, Matrix.mul_one]

/-- $f(\mathbf{A})$ through the sorted spectral decomposition of a Hermitian matrix. -/
private theorem exists_cfc_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ U : Matrix n (Fin (Fintype.card n)) 𝕜, HasOrthonormalCols U ∧ U * Uᴴ = 1 ∧
      (A = U * (Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)) *
        Uᴴ) ∧
      ∀ f : ℝ → ℝ, cfc f A = U * (Matrix.diagonal fun i : Fin (Fintype.card n) =>
        ((f (eigenvalue A i) : ℝ) : 𝕜)) * Uᴴ := by
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  exact ⟨U, hU, hU.mul_conjTranspose_self_of_card_eq hr.symm, hAU,
    HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose hU hr hAU⟩

/-- $f$ of a real diagonal matrix is the diagonal matrix of the values of $f$:
$f(\operatorname{diag}(\mathbf{d})) = \operatorname{diag}(f(\mathbf{d}_i))$. -/
theorem cfc_diagonal (f : ℝ → ℝ) (d : n → ℝ) :
    cfc f (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) =
      Matrix.diagonal fun i => ((f (d i) : ℝ) : 𝕜) := by
  have h := HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose (𝕜 := 𝕜)
    (U := (1 : Matrix n n 𝕜)) (d := d)
    hasOrthonormalCols_one rfl (by rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]) f
  rwa [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h

/-- An eigenvector of a Hermitian $\mathbf{A}$ is an eigenvector of $f(\mathbf{A})$: if
$\mathbf{A}\mathbf{x} = \mu\mathbf{x}$ with $\mu$ real then
$f(\mathbf{A})\mathbf{x} = f(\mu)\mathbf{x}$. -/
theorem _root_.Matrix.IsHermitian.cfc_mulVec_of_mulVec_eq_smul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) {x : n → 𝕜} {μ : ℝ} (hx : A *ᵥ x = μ • x) :
    cfc f A *ᵥ x = f μ • x := by
  obtain ⟨U, hU, hUU, hAU, hcfc⟩ := exists_cfc_eq hA
  have hy : ∀ i : Fin (Fintype.card n),
      ((eigenvalue A i : ℝ) : 𝕜) * (Uᴴ *ᵥ x) i = (μ : 𝕜) * (Uᴴ *ᵥ x) i := by
    intro i
    have h := congrFun (congrArg (Uᴴ *ᵥ ·) hx) i
    simp only [Matrix.mulVec_smul, Pi.smul_apply, RCLike.real_smul_eq_coe_mul] at h
    rw [← h]
    conv_rhs => rw [hAU]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU.conjTranspose_mul_self,
      Matrix.one_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
  have hfy : (Matrix.diagonal fun i : Fin (Fintype.card n) => ((f (eigenvalue A i) : ℝ) : 𝕜)) *ᵥ
      (Uᴴ *ᵥ x) = f μ • (Uᴴ *ᵥ x) := by
    ext i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, RCLike.real_smul_eq_coe_mul]
    by_cases h0 : (Uᴴ *ᵥ x) i = 0
    · rw [h0, mul_zero, mul_zero]
    · rw [RCLike.ofReal_injective (mul_right_cancel₀ h0 (hy i))]
  rw [hcfc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfy, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]

/-! ### Conjugation, relabelling and block sums -/

/-- $f$ commutes with unitary conjugation:
$f(\mathbf{U}\mathbf{A}\mathbf{U}^{\mathsf{H}}) = \mathbf{U} f(\mathbf{A}) \mathbf{U}^{\mathsf{H}}$
for Hermitian $\mathbf{A}$ and $\mathbf{U}$ unitary, that is, with orthonormal columns and as many
columns as rows, on any column index type. -/
theorem HasOrthonormalCols.cfc_mul_mul_conjTranspose_of_card_eq {r : Type*} [Fintype r]
    [DecidableEq r] {U : Matrix n r 𝕜}
    (hU : HasOrthonormalCols U) (hr : Fintype.card r = Fintype.card n) {A : Matrix r r 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) : cfc f (U * A * Uᴴ) = U * cfc f A * Uᴴ := by
  obtain ⟨V, hV, -, hAV, hcfc⟩ := exists_cfc_eq hA
  have hr' : Fintype.card (Fin (Fintype.card r)) = Fintype.card n := by
    rw [Fintype.card_fin, hr]
  have hUV : U * A * Uᴴ = U * V * (Matrix.diagonal fun i : Fin (Fintype.card r) =>
      ((eigenvalue A i : ℝ) : 𝕜)) * (U * V)ᴴ := by
    conv_lhs => rw [hAV]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose (hU.mul hV) hr' hUV f, hcfc f]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- $f$ commutes with relabelling: for Hermitian $\mathbf{A}$ and a bijection $e$ of index types,
$f$ of $\mathbf{A}$ with rows and columns relabelled by $e$ is $f(\mathbf{A})$ relabelled by $e$. -/
theorem _root_.Matrix.IsHermitian.cfc_submatrix_equiv {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (e : m ≃ n) :
    cfc f (A.submatrix e e) = (cfc f A).submatrix e e := by
  obtain ⟨V, hV, -, hAV, hcfc⟩ := exists_cfc_eq hA
  have hr : Fintype.card (Fin (Fintype.card n)) = Fintype.card m := by
    rw [Fintype.card_fin, Fintype.card_congr e]
  have hsub : ∀ D : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) 𝕜,
      (V * D * Vᴴ).submatrix e e = V.submatrix e (Equiv.refl _) * D *
        (V.submatrix e (Equiv.refl _))ᴴ := by
    intro D
    rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul_equiv (V * D) Vᴴ e (Equiv.refl _) e,
      ← Matrix.submatrix_mul_equiv V D e (Equiv.refl _) (Equiv.refl _)]
    rfl
  have hA' : A.submatrix e e = V.submatrix e (Equiv.refl _) *
      (Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)) *
        (V.submatrix e (Equiv.refl _))ᴴ := by
    conv_lhs => rw [hAV]
    exact hsub _
  rw [HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose (hV.submatrix e (Equiv.refl
    _).injective) hr hA' f,
    hcfc f, hsub]

/-- $f$ of a block diagonal matrix with Hermitian blocks $\mathbf{A}$, $\mathbf{B}$ is the
block diagonal matrix of $f(\mathbf{A})$ and $f(\mathbf{B})$:
$$f\left(\begin{bmatrix} \mathbf{A} & \mathbf{0} \\ \mathbf{0} & \mathbf{B} \end{bmatrix}\right)
  = \begin{bmatrix} f(\mathbf{A}) & \mathbf{0} \\ \mathbf{0} & f(\mathbf{B}) \end{bmatrix} .$$ -/
theorem _root_.Matrix.IsHermitian.cfc_fromBlocks_zero₁₂_zero₂₁ {A : Matrix m m 𝕜} {B : Matrix n n 𝕜}
    (hA : A.IsHermitian)
    (hB : B.IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.fromBlocks A 0 0 B) = Matrix.fromBlocks (cfc f A) 0 0 (cfc f B) := by
  obtain ⟨V, hV, -, hAV, hcfcA⟩ := exists_cfc_eq hA
  obtain ⟨W, hW, -, hBW, hcfcB⟩ := exists_cfc_eq hB
  have hU : HasOrthonormalCols (Matrix.fromBlocks V 0 0 W) := by
    rw [HasOrthonormalCols, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      hV.conjTranspose_mul_self, hW.conjTranspose_mul_self, Matrix.fromBlocks_one]
  have hr : Fintype.card (Fin (Fintype.card m) ⊕ Fin (Fintype.card n)) =
      Fintype.card (m ⊕ n) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
  have hblock : ∀ a : Fin (Fintype.card m) → ℝ, ∀ b : Fin (Fintype.card n) → ℝ,
      Matrix.fromBlocks (V * (Matrix.diagonal fun i => ((a i : ℝ) : 𝕜)) * Vᴴ) 0 0
        (W * (Matrix.diagonal fun i => ((b i : ℝ) : 𝕜)) * Wᴴ) =
      Matrix.fromBlocks V 0 0 W * (Matrix.diagonal fun i => ((Sum.elim a b i : ℝ) : 𝕜)) *
        (Matrix.fromBlocks V 0 0 W)ᴴ := by
    intro a b
    have hd : (Matrix.diagonal fun i => ((Sum.elim a b i : ℝ) : 𝕜)) =
        Matrix.fromBlocks (Matrix.diagonal fun i => ((a i : ℝ) : 𝕜)) 0 0
          (Matrix.diagonal fun i => ((b i : ℝ) : 𝕜)) := by
      rw [Matrix.fromBlocks_diagonal]
      congr 1
      funext i
      cases i <;> rfl
    rw [hd, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hAB : Matrix.fromBlocks A 0 0 B = Matrix.fromBlocks V 0 0 W *
      (Matrix.diagonal fun i => ((Sum.elim (fun i : Fin (Fintype.card m) => eigenvalue A i)
        (fun i : Fin (Fintype.card n) => eigenvalue B i) i : ℝ) : 𝕜)) *
        (Matrix.fromBlocks V 0 0 W)ᴴ := by
    rw [← hblock, ← hAV, ← hBW]
  rw
    [HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose hU hr hAB f, hcfcA f, hcfcB f, hblock]
  congr 3
  funext i
  cases i <;> rfl

/-- $f$ of a block diagonal matrix with Hermitian blocks $\mathbf{A}_i$ is the block diagonal
matrix of the $f(\mathbf{A}_i)$; the version of `Matrix.IsHermitian.cfc_fromBlocks_zero₁₂_zero₂₁`
for a family of blocks of one size. -/
theorem cfc_blockDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Matrix m m 𝕜} (hA : ∀ i, (A i).IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.blockDiagonal A) = Matrix.blockDiagonal fun i => cfc f (A i) := by
  choose U hU hAU using fun i => (hA i).exists_eq_mul_diagonal_mul_conjTranspose
  have hW : HasOrthonormalCols (Matrix.blockDiagonal U) := by
    rw [HasOrthonormalCols, Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    simp only [(hU _).conjTranspose_mul_self]
    exact Matrix.blockDiagonal_one
  have hr : Fintype.card (Fin (Fintype.card m) × ι) = Fintype.card (m × ι) := by
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
  have hdiag : ∀ g : ℝ → ℝ, (Matrix.blockDiagonal fun i => U i *
      (Matrix.diagonal fun k : Fin (Fintype.card m) => ((g (eigenvalue (A i) k) : ℝ) : 𝕜)) *
        (U i)ᴴ) = Matrix.blockDiagonal U *
      (Matrix.diagonal fun p : Fin (Fintype.card m) × ι =>
        ((g (eigenvalue (A p.2) p.1) : ℝ) : 𝕜)) * (Matrix.blockDiagonal U)ᴴ := fun g => by
    rw [Matrix.blockDiagonal_mul, Matrix.blockDiagonal_mul, Matrix.blockDiagonal_conjTranspose,
      Matrix.blockDiagonal_diagonal]
  have hA' : Matrix.blockDiagonal A = Matrix.blockDiagonal U *
      (Matrix.diagonal fun p : Fin (Fintype.card m) × ι =>
        ((eigenvalue (A p.2) p.1 : ℝ) : 𝕜)) * (Matrix.blockDiagonal U)ᴴ := by
    exact (congrArg _ (funext hAU)).trans (hdiag id)
  rw [HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose hW hr hA' f, ← hdiag f]
  exact congrArg _ (funext fun i =>
    (HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose (hU i) (Fintype.card_fin _) (hAU i)
        f).symm)

/-- A function of a zero-padded compression: for $\mathbf{U}$ with orthonormal columns
(not necessarily square) and Hermitian $\mathbf{T}$,
$f(\mathbf{U}\mathbf{T}\mathbf{U}^{\mathsf{H}}) = \mathbf{U}f(\mathbf{T})\mathbf{U}^{\mathsf{H}}
+ f(0)(\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf{H}})$: the padding contributes the eigenvalue
$0$. Generalises `NLAlib.HasOrthonormalCols.cfc_mul_mul_conjTranspose_of_card_eq`, which needs
$\mathbf{U}$ square. -/
theorem HasOrthonormalCols.cfc_mul_mul_conjTranspose {r : Type*} [Fintype r] [DecidableEq r]
    {U : Matrix n r 𝕜} (hU : HasOrthonormalCols U) {T : Matrix r r 𝕜} (hT : T.IsHermitian)
    (f : ℝ → ℝ) : cfc f (U * T * Uᴴ) = U * cfc f T * Uᴴ + f 0 • (1 - U * Uᴴ) := by
  -- complete $\mathbf{U}$ to a unitary $[\mathbf{U}, \mathbf{U}']$ and use the square case
  set p := Fin (Fintype.card n - Fintype.card r)
  have hcard : Fintype.card r + Fintype.card p = Fintype.card n := by
    have := hU.card_le
    simp only [p, Fintype.card_fin]
    omega
  obtain ⟨U', hW⟩ := hU.exists_fromCols hcard
  have hsum := HasOrthonormalCols.mul_conjTranspose_add_mul_conjTranspose hW hcard
  have hWc : Fintype.card (r ⊕ p) = Fintype.card n := by rw [Fintype.card_sum, hcard]
  have hblock : ∀ (X : Matrix r r 𝕜) (Y : Matrix p p 𝕜),
      Matrix.fromCols U U' * Matrix.fromBlocks X 0 0 Y * (Matrix.fromCols U U')ᴴ =
        U * X * Uᴴ + U' * Y * U'ᴴ := by
    intro X Y
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
    simp only [Matrix.mul_zero, add_zero, zero_add]
  have hTB : (Matrix.fromBlocks T 0 0 (0 : Matrix p p 𝕜)).IsHermitian :=
    hT.fromBlocks (by simp) Matrix.isHermitian_zero
  have hUTU : U * T * Uᴴ = Matrix.fromCols U U' * Matrix.fromBlocks T 0 0 (0 : Matrix p p 𝕜) *
      (Matrix.fromCols U U')ᴴ := by
    rw [hblock]
    simp
  rw [hUTU, NLAlib.HasOrthonormalCols.cfc_mul_mul_conjTranspose_of_card_eq hW hWc hTB,
    Matrix.IsHermitian.cfc_fromBlocks_zero₁₂_zero₂₁ hT Matrix.isHermitian_zero, hblock,
      cfc_apply_zero,
    Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    ← hsum, add_sub_cancel_left]

/-! ### The spectrum -/

/-- The real spectrum of a Hermitian matrix lies in a set $s$ exactly when its eigenvalues
$\lambda_i(\mathbf{A})$, $i < \lvert n \rvert$, do. -/
theorem _root_.Matrix.IsHermitian.spectrum_subset_iff {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {s : Set ℝ} : spectrum ℝ A ⊆ s ↔ ∀ i, i < Fintype.card n → eigenvalue A i ∈ s := by
  classical
  rw [hA.spectrum_eq_image_eigenvalue, Set.image_subset_iff]
  exact Iff.rfl

/-- A matrix with $a\mathbf{I} \preceq \mathbf{A} \preceq b\mathbf{I}$ has its real spectrum in
$[a, b]$. -/
theorem spectrum_subset_Icc_of_le {A : Matrix n n 𝕜} {a b : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) :
    spectrum ℝ A ⊆ Set.Icc a b := by
  have hA := isHermitian_of_le_smul_one h₂
  rw [hA.spectrum_subset_iff]
  intro i hi
  have : Nonempty n := Fintype.card_pos_iff.mp (Nat.zero_lt_of_lt hi)
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n := ⟨Fintype.card n - 1, by omega⟩
  exact ⟨((hA.smul_one_le_iff hk).mp h₁).trans
      (hA.eigenvalue_le_eigenvalue (by omega) (by omega)),
    (hA.eigenvalue_le_eigenvalue (Nat.zero_le i) hi).trans (hA.le_smul_one_iff.mp h₂)⟩

/-- A lower spectral bound is a Loewner bound: for Hermitian $\mathbf{A}$,
$a\mathbf{I} \preceq \mathbf{A}$ iff the real spectrum lies in $[a, \infty)$. The converse half
of `spectrum_subset_Icc_of_le`, by Mathlib's `algebraMap_le_iff_le_spectrum`. -/
theorem _root_.Matrix.IsHermitian.smul_one_le_iff_spectrum_subset_Ici {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (a : ℝ) : a • (1 : Matrix n n 𝕜) ≤ A ↔ spectrum ℝ A ⊆ Set.Ici a := by
  rw [← Algebra.algebraMap_eq_smul_one]
  exact algebraMap_le_iff_le_spectrum (a := A) hA

/-- An upper spectral bound is a Loewner bound: for Hermitian $\mathbf{A}$,
$\mathbf{A} \preceq b\mathbf{I}$ iff the real spectrum lies in $(-\infty, b]$, by Mathlib's
`le_algebraMap_iff_spectrum_le`. -/
theorem _root_.Matrix.IsHermitian.le_smul_one_iff_spectrum_subset_Iic {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : ℝ) : A ≤ b • (1 : Matrix n n 𝕜) ↔ spectrum ℝ A ⊆ Set.Iic b := by
  rw [← Algebra.algebraMap_eq_smul_one]
  exact le_algebraMap_iff_spectrum_le (a := A) hA

/-- Ritz values lie in every interval containing the spectrum: for Hermitian $\mathbf{A}$
with spectrum in $[a, a']$ and $\mathbf{Q}$ with orthonormal columns, the spectrum of
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ lies in $[a, a']$. A zero-padded compression
$\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$ has the extra
eigenvalue $0$, which is why a frame is assumed. -/
theorem _root_.Matrix.IsHermitian.spectrum_conjTranspose_mul_mul_subset_Icc {r : Type*}
    [Fintype r] [DecidableEq r] {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) :
    spectrum ℝ (Qᴴ * A * Q) ⊆ Set.Icc a a' := by
  have hA' : IsSelfAdjoint A := hA
  have h₁ : a • (1 : Matrix n n 𝕜) ≤ A := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (algebraMap_le_iff_le_spectrum hA').mpr fun x hx => (hs hx).1
  have h₂ : A ≤ a' • (1 : Matrix n n 𝕜) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (le_algebraMap_iff_spectrum_le hA').mpr fun x hx => (hs hx).2
  have hc : ∀ c : ℝ, Qᴴ * (c • (1 : Matrix n n 𝕜)) * Q = c • 1 := fun c => by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQ.conjTranspose_mul_self]
  refine spectrum_subset_Icc_of_le ?_ ?_
  · rw [← hc]
    exact conjTranspose_mul_mul_le_conjTranspose_mul_mul h₁ Q
  · rw [← hc]
    exact conjTranspose_mul_mul_le_conjTranspose_mul_mul h₂ Q

/-- The spectrum of a positive semidefinite matrix is nonnegative. -/
theorem _root_.Matrix.PosSemidef.spectrum_subset_Ici {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    spectrum ℝ A ⊆ Set.Ici 0 := by
  rw [hA.isHermitian.spectrum_subset_iff]
  exact fun i _ => hA.eigenvalue_nonneg i

/-- The spectrum of a positive semidefinite matrix lies in $[0, \lambda_0(\mathbf{A})]$,
$\lambda_0(\mathbf{A})$ its largest eigenvalue. -/
theorem _root_.Matrix.PosSemidef.spectrum_subset_Icc_eigenvalue_zero {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : spectrum ℝ A ⊆ Set.Icc 0 (eigenvalue A 0) :=
  hA.isHermitian.spectrum_subset_iff.2 fun i hi =>
    ⟨hA.eigenvalue_nonneg i, hA.isHermitian.eigenvalue_le_eigenvalue (Nat.zero_le i) hi⟩

/-- The spectrum of a positive definite matrix is positive. -/
theorem _root_.Matrix.PosDef.spectrum_subset_Ioi {A : Matrix n n 𝕜} (hA : A.PosDef) :
    spectrum ℝ A ⊆ Set.Ioi 0 := by
  rw [hA.isHermitian.spectrum_subset_iff]
  exact hA.isHermitian.posDef_iff_eigenvalue_pos.mp hA

/-! ### Trace, eigenvalues and quadratic forms -/

/-- **The trace of $f(\mathbf{A})$** is the sum of $f$ over the eigenvalues: for Hermitian
$\mathbf{A}$,
$\operatorname{Re} \operatorname{tr} f(\mathbf{A})
= \sum_{i < \lvert n \rvert} f(\lambda_i(\mathbf{A}))$.
[Tropp2015, Definition 8.3.1]; there the sum defines the trace function, with the remark that it
agrees with the trace of the standard matrix function.
Result: trace-of-matrix-function -/
theorem _root_.Matrix.IsHermitian.re_trace_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    RCLike.re (cfc f A).trace = ∑ i ∈ Finset.range (Fintype.card n), f (eigenvalue A i) := by
  obtain ⟨U, hU, -, -, hcfc⟩ := exists_cfc_eq hA
  rw [hcfc f, Matrix.trace_mul_cycle, hU.conjTranspose_mul_self, Matrix.one_mul,
    Matrix.trace_diagonal, map_sum]
  simp only [RCLike.ofReal_re]
  exact Fin.sum_univ_eq_sum_range (fun i => f (eigenvalue A i)) _

/-- Eigenvalues of $f(\mathbf{A})$ for a non-decreasing $f$: for Hermitian $\mathbf{A}$ and
$k < \lvert n \rvert$, $\lambda_k(f(\mathbf{A})) = f(\lambda_k(\mathbf{A}))$, when $f$ is monotone
on a set containing the spectrum of $\mathbf{A}$. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_cfc_of_monotoneOn {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s)
    (hs : spectrum ℝ A ⊆ s) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue (cfc f A) k = f (eigenvalue A k) := by
  obtain ⟨U, hU, -, -, hcfc⟩ := exists_cfc_eq hA
  have hanti : Antitone fun i : Fin (Fintype.card n) => f (eigenvalue A i) := fun i j hij =>
    hf (hs (hA.eigenvalue_mem_spectrum j.isLt)) (hs (hA.eigenvalue_mem_spectrum i.isLt))
      (hA.eigenvalue_le_eigenvalue hij j.isLt)
  exact HasOrthonormalCols.eigenvalue_eq_of_eq_mul_diagonal_mul_conjTranspose hU rfl hanti (hcfc f)
    ⟨k, hk⟩

/-- Eigenvalues of $f(\mathbf{A})$ for a non-increasing $f$: for Hermitian $\mathbf{A}$ and $f$
antitone on a set containing the spectrum,
$\lambda_k(f(\mathbf{A})) = f(\lambda_j(\mathbf{A}))$ with $k + j + 1 = \lvert n \rvert$. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_cfc_of_antitoneOn {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {s : Set ℝ} (hf : AntitoneOn f s)
    (hs : spectrum ℝ A ⊆ s) {k j : ℕ} (hkj : k + j + 1 = Fintype.card n) :
    eigenvalue (cfc f A) k = f (eigenvalue A j) := by
  have hj : j < Fintype.card n := by omega
  have h := hA.eigenvalue_cfc_of_monotoneOn (f := fun x => -f x) hf.neg hs hj
  have hneg : cfc f A = -cfc (fun x => -f x) A := by rw [cfc_neg, neg_neg]
  rw [hneg, eigenvalue_neg _ hkj, h, neg_neg]

/-- The quadratic form of $f(\mathbf{A})$ through a unitary diagonalisation
$\mathbf{A} = \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$, $\mathbf{d}$ real,
with $\mathbf{U}$ having orthonormal columns and as many columns as rows, on any column index
type:
$$\operatorname{Re}(\mathbf{x}^{\mathsf{H}} f(\mathbf{A}) \mathbf{x})
  = \sum_i f(\mathbf{d}_i) \, \lvert (\mathbf{U}^{\mathsf{H}}\mathbf{x})_i \rvert^2 \,.$$
This is the identity behind Gauss quadrature for $\mathbf{x}^{\mathsf{H}} f(\mathbf{A}) \mathbf{x}$.
-/
theorem HasOrthonormalCols.re_quadForm_cfc_eq_sum {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix n n 𝕜}
    {U : Matrix n r 𝕜} {d : r → ℝ} (hU : HasOrthonormalCols U)
    (hr : Fintype.card r = Fintype.card n)
    (hA : A = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) (f : ℝ → ℝ) (x : n → 𝕜) :
    RCLike.re (quadForm (cfc f A) x) = ∑ i, f (d i) * ‖(Uᴴ *ᵥ x) i‖ ^ 2 := by
  have h := quadForm_conjTranspose_mul_mul (Matrix.diagonal fun i => ((f (d i) : ℝ) : 𝕜)) Uᴴ x
  rw [Matrix.conjTranspose_conjTranspose] at h
  rw [HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose hU hr hA f, h, quadForm_diagonal,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- **A nonnegative trace function dominates its value at the largest eigenvalue**: if
$\varphi \ge 0$ on the spectrum of a Hermitian $\mathbf{A}$ of positive size ($n$ nonempty) then
$\varphi(\lambda_0(\mathbf{A})) \le \operatorname{Re} \operatorname{tr} \varphi(\mathbf{A})$. With
$\varphi = \exp$ this is the first step of the matrix Laplace transform method; with
$\varphi(t) = \max(t - 1, 0)$ it is the first step of the intrinsic-dimension bounds.
[Tropp2015, Proposition 3.2.1 and §7.5]. -/
theorem _root_.Matrix.IsHermitian.apply_eigenvalue_zero_le_re_trace_cfc [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {φ : ℝ → ℝ} (hφ : ∀ x ∈ spectrum ℝ A, 0 ≤ φ x) :
    φ (eigenvalue A 0) ≤ RCLike.re (cfc φ A).trace := by
  rw [hA.re_trace_cfc]
  exact Finset.single_le_sum (f := fun i => φ (eigenvalue A i))
    (fun i hi => hφ _ (hA.eigenvalue_mem_spectrum (Finset.mem_range.mp hi)))
    (Finset.mem_range.mpr Fintype.card_pos)

/-! ### Order and norm bounds -/

/-- Comparison on an interval containing the spectrum: if
$a\mathbf{I} \preceq \mathbf{A} \preceq b\mathbf{I}$ and $f \le g$ on $[a, b]$, then
$f(\mathbf{A}) \preceq g(\mathbf{A})$. The comparison on the spectrum itself is Mathlib's
`cfc_mono`. -/
theorem cfc_le_cfc_of_forall_mem_Icc {A : Matrix n n 𝕜} {a b : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) {f g : ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc a b, f x ≤ g x) : cfc f A ≤ cfc g A := by
  have hs := spectrum_subset_Icc_of_le h₁ h₂
  exact cfc_mono (fun x hx => h x (hs hx)) (A.finite_real_spectrum.continuousOn f)
    (A.finite_real_spectrum.continuousOn g)

/-- The quadratic form of $f(\mathbf{A})$ is bounded by the largest $\lvert f \rvert$ on the
spectrum: if $\lvert f \rvert \le c$ there, then
$\lvert \operatorname{Re}(\mathbf{x}^{\mathsf{H}} f(\mathbf{A}) \mathbf{x}) \rvert
\le c \|\mathbf{x}\|^2$. -/
private theorem abs_re_quadForm_cfc_le_aux {A : Matrix n n 𝕜} (hA : A.IsHermitian) {f : ℝ → ℝ}
    {c : ℝ} (h : ∀ x ∈ spectrum ℝ A, |f x| ≤ c) (x : n → 𝕜) :
    |RCLike.re (quadForm (cfc f A) x)| ≤ c * ‖WithLp.toLp 2 x‖ ^ 2 := by
  obtain ⟨U, hU, -, hAU, -⟩ := exists_cfc_eq hA
  have hr := Fintype.card_fin (Fintype.card n)
  rw [HasOrthonormalCols.re_quadForm_cfc_eq_sum hU hr hAU f x,
    ← (hU.conjTranspose_of_card_eq hr.symm).norm_toLp_mulVec x, EuclideanSpace.norm_sq_eq,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖(Uᴴ *ᵥ x) i‖ ^ 2)]
  exact mul_le_mul_of_nonneg_right (h _ (hA.eigenvalue_mem_spectrum i.isLt)) (by positivity)

/-- The spectral norm of $f(\mathbf{A})$ is at most the largest $\lvert f \rvert$ on the
spectrum: for Hermitian $\mathbf{A}$, if $c \ge 0$ and $\lvert f(x) \rvert \le c$ for every $x$ in
the spectrum of $\mathbf{A}$, then $\|f(\mathbf{A})\|_2 \le c$. -/
theorem _root_.Matrix.IsHermitian.specNorm_cfc_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ spectrum ℝ A, |f x| ≤ c) :
    specNorm (cfc f A) ≤ c := by
  have hH : (cfc f A).IsHermitian := cfc_predicate f A
  exact (hH.specNorm_le_iff_abs_re_quadForm_le hc).mpr (abs_re_quadForm_cfc_le_aux hA h)

/-- The quadratic form of $f(\mathbf{A})$ is bounded by the largest $\lvert f \rvert$ on the
spectrum: for Hermitian $\mathbf{A}$, if $\lvert f(x) \rvert \le c$ for every $x$ in the spectrum,
then $\lvert \operatorname{Re}(\mathbf{x}^{\mathsf{H}} f(\mathbf{A}) \mathbf{x}) \rvert
\le c \|\mathbf{x}\|^2$ for every vector $\mathbf{x}$. -/
theorem _root_.Matrix.IsHermitian.abs_re_quadForm_cfc_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {c : ℝ} (h : ∀ x ∈ spectrum ℝ A, |f x| ≤ c) (x : n → 𝕜) :
    |RCLike.re (quadForm (cfc f A) x)| ≤ c * ‖WithLp.toLp 2 x‖ ^ 2 := by
  exact abs_re_quadForm_cfc_le_aux hA h x

/-- The squared norm of $\psi(\mathbf{A})\mathbf{x}$ is a quadratic form in
$\psi^2(\mathbf{A})$, for Hermitian $\mathbf{A}$ and real $\psi$:
$\|\psi(\mathbf{A})\mathbf{x}\|^2 = \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\psi^2(\mathbf{A})
\mathbf{x})$. -/
theorem _root_.Matrix.IsHermitian.norm_toLp_cfc_mulVec_sq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (ψ : ℝ → ℝ) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (cfc ψ A *ᵥ x)‖ ^ 2 = RCLike.re (quadForm (cfc (fun t => ψ t ^ 2) A) x) := by
  have hH : (cfc ψ A).IsHermitian := cfc_predicate ψ A
  have hsq : cfc (fun t => ψ t ^ 2) A = cfc ψ A * cfc ψ A :=
    (cfc_pow ψ 2 A (A.finite_real_spectrum.continuousOn _) hA).trans (sq _)
  rw [EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct, hsq, quadForm_def, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, hH.eq, Matrix.mulVec_mulVec]

/-- **Cauchy–Schwarz for functions of one Hermitian matrix**: if
$\lvert\varphi\rvert \le \lvert\psi\rvert\,\lvert\chi\rvert$ on the spectrum of $\mathbf{A}$,
then $\lvert\mathbf{x}^{\mathsf{H}}\varphi(\mathbf{A})\mathbf{y}\rvert \le
\|\psi(\mathbf{A})\mathbf{x}\|\,\|\chi(\mathbf{A})\mathbf{y}\|$.
[HornJohnson2013, Theorem 5.1.4]; there for vectors (locator to check). -/
theorem _root_.Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {φ ψ χ : ℝ → ℝ} (h : ∀ x ∈ spectrum ℝ A, |φ x| ≤ |ψ x| * |χ x|)
    (x y : n → 𝕜) :
    ‖star x ⬝ᵥ (cfc φ A *ᵥ y)‖ ≤
      ‖WithLp.toLp 2 (cfc ψ A *ᵥ x)‖ * ‖WithLp.toLp 2 (cfc χ A *ᵥ y)‖ := by
  have hc : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ A) := fun g =>
    A.finite_real_spectrum.continuousOn g
  -- $\varphi = \psi\,\omega\,\chi$ on the spectrum with $\lvert\omega\rvert \le 1$
  set ω : ℝ → ℝ := fun t => φ t / (ψ t * χ t)
  have hω : ∀ t ∈ spectrum ℝ A, |ω t| ≤ 1 := fun t ht => by
    simp only [ω, abs_div, abs_mul]
    exact div_le_one_of_le₀ (h t ht) (by positivity)
  have hφ : cfc φ A = cfc ψ A * (cfc ω A * cfc χ A) := by
    rw [← cfc_mul _ _ A (hc _) (hc _), ← cfc_mul _ _ A (hc _) (hc _)]
    refine cfc_congr fun t ht => ?_
    by_cases h0 : ψ t * χ t = 0
    · have : |φ t| ≤ 0 := by
        have := h t ht
        rwa [← abs_mul, h0, abs_zero] at this
      rw [abs_nonpos_iff.mp this, ← mul_assoc, mul_comm (ψ t), mul_assoc, h0, mul_zero]
    · simp only [ω]
      have h1 : ψ t ≠ 0 := left_ne_zero_of_mul h0
      have h2 : χ t ≠ 0 := right_ne_zero_of_mul h0
      field_simp
  have hH : (cfc ψ A).IsHermitian := cfc_predicate ψ A
  have hdot : star x ⬝ᵥ (cfc φ A *ᵥ y) =
      star (cfc ψ A *ᵥ x) ⬝ᵥ (cfc ω A *ᵥ (cfc χ A *ᵥ y)) := by
    rw [Matrix.star_mulVec, hH.eq, ← Matrix.dotProduct_mulVec, hφ]
    simp only [Matrix.mulVec_mulVec]
  rw [hdot]
  refine (norm_star_dotProduct_mulVec_le _ _ _).trans ?_
  have hω' : specNorm (cfc ω A) ≤ 1 := hA.specNorm_cfc_le zero_le_one hω
  calc ‖WithLp.toLp 2 (cfc ψ A *ᵥ x)‖ * specNorm (cfc ω A) * ‖WithLp.toLp 2 (cfc χ A *ᵥ y)‖
      ≤ ‖WithLp.toLp 2 (cfc ψ A *ᵥ x)‖ * 1 * ‖WithLp.toLp 2 (cfc χ A *ᵥ y)‖ := by gcongr
    _ = _ := by rw [mul_one]

/-- A lower bound for the trace of $f(\mathbf{A})$ from a lower bound of $f$ on the spectrum: for
Hermitian $\mathbf{A}$, if $b \le f(x)$ for every $x$ in the spectrum, then
$b \lvert n \rvert \le \operatorname{Re} \operatorname{tr} f(\mathbf{A})$. -/
theorem _root_.Matrix.IsHermitian.mul_card_le_re_trace_cfc {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {f : ℝ → ℝ} {b : ℝ} (h : ∀ x ∈ spectrum ℝ A, b ≤ f x) :
    b * Fintype.card n ≤ RCLike.re (cfc f A).trace := by
  rw [hA.re_trace_cfc, mul_comm]
  have hsum := Finset.card_nsmul_le_sum (Finset.range (Fintype.card n))
    (fun i => f (eigenvalue A i)) b
    (fun i hi => h _ (hA.eigenvalue_mem_spectrum (Finset.mem_range.mp hi)))
  rwa [Finset.card_range, nsmul_eq_mul] at hsum

/-! ### The inverse and the inverse square root -/

/-- The inverse of a positive definite matrix through the functional calculus:
$\mathbf{A}^{-1} = f(\mathbf{A})$ for $f(x) = x^{-1}$. -/
theorem _root_.Matrix.PosDef.inv_eq_cfc {A : Matrix n n 𝕜} (hA : A.PosDef) :
    A⁻¹ = cfc (fun x : ℝ => x⁻¹) A := by
  have hH : IsSelfAdjoint A := hA.isHermitian
  have h : cfc (fun x : ℝ => x⁻¹) A * cfc (fun x : ℝ => x) A = 1 := by
    rw [← cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _), ← cfc_one ℝ A]
    refine cfc_congr fun x hx => ?_
    simp only [Pi.one_apply]
    exact inv_mul_cancel₀ (hA.spectrum_subset_Ioi hx).ne'
  rw [cfc_id' ℝ A hH] at h
  exact Matrix.inv_eq_left_inv h

/-- The pseudoinverse of a Hermitian matrix is a function of it:
$\mathbf{A}^{+} = f(\mathbf{A})$ for $f(x) = x^{-1}$, $f(0) = 0$ (Lean's convention for
$0^{-1}$). Generalises `Matrix.PosDef.inv_eq_cfc`. -/
theorem _root_.Matrix.IsHermitian.cfc_inv_eq_pinv {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    cfc (fun x : ℝ => x⁻¹) A = pinv A := by
  have hA' : IsSelfAdjoint A := hA
  have hc : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ A) := fun g =>
    A.finite_real_spectrum.continuousOn g
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA'
  have hl : A * cfc (fun x : ℝ => x⁻¹) A = cfc (fun x : ℝ => x * x⁻¹) A := by
    rw [cfc_mul (fun x : ℝ => x) (fun x => x⁻¹) A (hc _) (hc _), hid]
  have hr : cfc (fun x : ℝ => x⁻¹) A * A = cfc (fun x : ℝ => x⁻¹ * x) A := by
    rw [cfc_mul (fun x : ℝ => x⁻¹) (fun x => x) A (hc _) (hc _), hid]
  -- the four Penrose conditions, each an identity of real functions
  symm
  refine pinv_eq_iff.mpr ⟨?_, ?_, ?_, ?_⟩
  · rw [hl]
    calc cfc (fun x : ℝ => x * x⁻¹) A * A
        = cfc (fun x : ℝ => x * x⁻¹) A * cfc (fun x : ℝ => x) A := by rw [hid]
      _ = cfc (fun x : ℝ => x * x⁻¹ * x) A := (cfc_mul _ _ A (hc _) (hc _)).symm
      _ = cfc (fun x : ℝ => x) A := cfc_congr fun x _ => by
          by_cases hx : x = 0
          · simp [hx]
          · field_simp
      _ = A := hid
  · rw [hr, ← cfc_mul _ _ A (hc _) (hc _)]
    refine cfc_congr fun x _ => ?_
    by_cases hx : x = 0
    · simp [hx]
    · field_simp
  · rw [hl]
    exact cfc_predicate _ A
  · rw [hr]
    exact cfc_predicate _ A

/-- The functional calculus of $x \mapsto 1/\sqrt{x}$ is a left inverse of the square root of a
positive definite matrix. -/
private theorem cfc_inv_sqrt_mul_sqrt {A : Matrix n n 𝕜} (hA : A.PosDef) :
    cfc (fun x : ℝ => (√x)⁻¹) A * CFC.sqrt A = 1 := by
  have hH : IsSelfAdjoint A := hA.isHermitian
  rw [CFC.sqrt_eq_real_sqrt A (Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef), cfcₙ_eq_cfc,
    ← cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _)
      (A.finite_real_spectrum.continuousOn _), ← cfc_one ℝ A]
  refine cfc_congr fun x hx => ?_
  have hx0 : 0 < √x := Real.sqrt_pos.mpr (hA.spectrum_subset_Ioi hx)
  simp only [Pi.one_apply]
  exact inv_mul_cancel₀ hx0.ne'

/-- The inverse of the square root of a positive definite matrix through the functional
calculus: $(\mathbf{A}^{1/2})^{-1} = f(\mathbf{A})$ for $f(x) = 1/\sqrt{x}$. -/
theorem _root_.Matrix.PosDef.inv_sqrt_eq_cfc {A : Matrix n n 𝕜} (hA : A.PosDef) :
    (CFC.sqrt A)⁻¹ = cfc (fun x : ℝ => (√x)⁻¹) A := by
  exact Matrix.inv_eq_left_inv (cfc_inv_sqrt_mul_sqrt hA)

/-- The square root of a positive definite matrix is invertible. -/
theorem _root_.Matrix.PosDef.isUnit_sqrt {A : Matrix n n 𝕜} (hA : A.PosDef) :
    IsUnit (CFC.sqrt A) := by
  exact IsUnit.of_mul_eq_one_right _ (cfc_inv_sqrt_mul_sqrt hA)


omit [DecidableEq m] in
/-- A function of a Hermitian matrix on an invariant frame: if
$\mathbf{A}\mathbf{W} = \mathbf{W}\operatorname{diag}(\mathbf{d})$ with $\mathbf{d}$ real, then
$$f(\mathbf{A})\mathbf{W} = \mathbf{W}\operatorname{diag}(f(\mathbf{d}_i))\,,$$
for any columns $\mathbf{W}$ (each nonzero column is an eigenvector, a zero column is mapped to
zero). The partial form of `NLAlib.HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose`; the
polynomial twin is `NLAlib.aeval_mul_eq_mul_aeval_of_mul_eq_mul`. -/
theorem _root_.Matrix.IsHermitian.cfc_mul_eq_mul_diagonal_of_mul_eq {r : Type*} [Fintype r]
    [DecidableEq r] {A : Matrix n n 𝕜} (hA : A.IsHermitian) {W : Matrix n r 𝕜} {d : r → ℝ}
    (hAW : A * W = W * Matrix.diagonal fun i => (d i : 𝕜)) (f : ℝ → ℝ) :
    cfc f A * W = W * Matrix.diagonal fun i => (f (d i) : 𝕜) := by
  obtain ⟨U, hU, hUU, hAU, hcfc⟩ := exists_cfc_eq hA
  set Λ := Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜)
  have hZ : Λ * (Uᴴ * W) = Uᴴ * W * Matrix.diagonal fun i => ((d i : ℝ) : 𝕜) := by
    calc Λ * (Uᴴ * W) = Uᴴ * (U * Λ * Uᴴ) * W := by
          simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]
      _ = Uᴴ * (A * W) := by rw [← hAU, Matrix.mul_assoc]
      _ = Uᴴ * W * Matrix.diagonal fun i => ((d i : ℝ) : 𝕜) := by
          rw [hAW, Matrix.mul_assoc]
  rw [hcfc, Matrix.mul_assoc, Matrix.mul_assoc, diagonal_mul_eq_mul_diagonal_of_eq hZ f,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul]

/-! ### Lipschitz functions in the Frobenius norm -/

/-- **A $1$-Lipschitz function is $1$-Lipschitz in the Frobenius norm on Hermitian matrices**:
for Hermitian $\mathbf{A}$, $\mathbf{B}$ over $\Bbbk$ and $f : \mathbb{R} \to \mathbb{R}$ with
$\lvert f(x) - f(y)\rvert \le
\lvert x - y\rvert$,
$\|f(\mathbf{A}) - f(\mathbf{B})\|_{\mathsf{F}} \le \|\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}$.
The finite-dimensional Hermitian specialization of [Kittaneh1985, abstract], with Lipschitz
constant one. The statement includes both real and complex matrices and empty index types.
Result: lipschitz-cfc-frobenius -/
theorem _root_.Matrix.IsHermitian.frobNorm_cfc_sub_cfc_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A B : Matrix ι ι 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) {f : ℝ → ℝ}
    (hf : LipschitzWith 1 f) :
    frobNorm (cfc f A - cfc f B) ≤ frobNorm (A - B) := by
  have hdec : ∀ {C : Matrix ι ι 𝕜} (hC : C.IsHermitian) (g : ℝ → ℝ),
      cfc g C = (hC.eigenvectorUnitary : Matrix ι ι 𝕜) *
        Matrix.diagonal (fun i => ((g (hC.eigenvalues i) : ℝ) : 𝕜)) *
          (hC.eigenvectorUnitary : Matrix ι ι 𝕜)ᴴ := by
    intro C hC g
    rw [hC.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose]
    rfl
  set U := (hA.eigenvectorUnitary : Matrix ι ι 𝕜)
  set V := (hB.eigenvectorUnitary : Matrix ι ι 𝕜)
  set a := hA.eigenvalues
  set b := hB.eigenvalues
  have hU := hA.hasOrthonormalCols_eigenvectorUnitary
  have hV := hB.hasOrthonormalCols_eigenvectorUnitary
  have hUU : Uᴴ * U = 1 := hU.conjTranspose_mul_self
  have hVV : Vᴴ * V = 1 := hV.conjTranspose_mul_self
  have hA' : A = U * Matrix.diagonal (fun i => ((a i : ℝ) : 𝕜)) * Uᴴ := by
    have := hdec hA (fun x => x)
    rwa [cfc_id' ℝ A] at this
  have hB' : B = V * Matrix.diagonal (fun i => ((b i : ℝ) : 𝕜)) * Vᴴ := by
    have := hdec hB (fun x => x)
    rwa [cfc_id' ℝ B] at this
  -- conjugate both differences by the two eigenbases
  have hconj : ∀ (d e : ι → 𝕜),
      Uᴴ * (U * Matrix.diagonal d * Uᴴ - V * Matrix.diagonal e * Vᴴ) * V =
        Matrix.diagonal d * (Uᴴ * V) - Uᴴ * V * Matrix.diagonal e := by
    intro d e
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hVV, Matrix.mul_one]
  have hfrob : ∀ X : Matrix ι ι 𝕜, frobNorm X = frobNorm (Uᴴ * X * V) := fun X => by
    rw [Matrix.mul_assoc, hU.conjTranspose.frobNorm_mul_left, hV.frobNorm_mul_right]
  have hAB : A - B = U * Matrix.diagonal (fun i => ((a i : ℝ) : 𝕜)) * Uᴴ -
      V * Matrix.diagonal (fun i => ((b i : ℝ) : 𝕜)) * Vᴴ := by
    rw [← hA', ← hB']
  rw [hfrob, hfrob (A - B), hdec hA f, hdec hB f, hconj, hAB, hconj]
  have hsq : frobNorm (Matrix.diagonal (fun i => ((f (a i) : ℝ) : 𝕜)) * (Uᴴ * V) -
      Uᴴ * V * Matrix.diagonal (fun i => ((f (b i) : ℝ) : 𝕜))) ^ 2 ≤
      frobNorm (Matrix.diagonal (fun i => ((a i : ℝ) : 𝕜)) * (Uᴴ * V) -
        Uᴴ * V * Matrix.diagonal (fun i => ((b i : ℝ) : 𝕜))) ^ 2 := by
    rw [frobNorm_sq_eq_sum, frobNorm_sq_eq_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have hl : |f (a i) - f (b j)| ≤ |a i - b j| := by
      have := hf.dist_le_mul (a i) (b j)
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using this
    have he (x y : ℝ) (z : 𝕜) :
        ‖(x : 𝕜) * z - z * (y : 𝕜)‖ = |x - y| * ‖z‖ := by
      rw [show (x : 𝕜) * z - z * (y : 𝕜) = ((x - y : ℝ) : 𝕜) * z by
        push_cast
        ring, norm_mul, RCLike.norm_ofReal]
    rw [he, he]
    gcongr
  exact (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1 hsq

end NLAlib
