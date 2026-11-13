/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.Grade
public import NLAlib.Krylov.Functions.LanczosFA
public import NLAlib.Matrix.Spectral.SpectralMeasure
public import NLAlib.Polynomial.Orthogonal.Gauss
public import NLAlib.Polynomial.Orthogonal.Radau
public import NLAlib.Polynomial.Orthogonal.RadauJacobi
public import NLAlib.Krylov.Processes.LanczosPolynomials
public import NLAlib.Polynomial.Approximation.MinimaxError

/-!
# Lanczos quadrature

The quadratic form $\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$ of a Hermitian $\mathbf{A}$
is the integral of $f$ against the spectral measure $\mu_{\mathbf{A},\mathbf{b}}$. Its Lanczos
(Gauss) quadrature after $q$ steps is
$\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)$, the integral of $f$
against the Lanczos rule
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q) =
\mu_{\mathbf{P}\mathbf{A}\mathbf{P},\,\mathbf{P}\mathbf{b}}$,
$\mathbf{P}$ the orthogonal projector onto $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$. For any
orthonormal basis $\mathbf{Q}$ of the Krylov space the rule is the spectral measure of
$(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}, \mathbf{Q}^{\mathsf{H}}\mathbf{b})$: its nodes are
the Ritz values. From the Lanczos recurrence it is
$\|\mathbf{b}\|^2$ times the spectral measure of $(\mathbf{T}, \mathbf{e}_0)$, and in an
eigenbasis of $\mathbf{T}$ its weights are the squared first eigenvector entries (Golub–Welsch).

The rule is exact through degree $2q - 1$: it matches the first $2q$ moments of
$\mu_{\mathbf{A},\mathbf{b}}$. If $f$ is within $\varepsilon$ of a polynomial of degree less
than $2q$ on an interval containing the spectrum, the quadrature error is at most
$2\varepsilon\|\mathbf{b}\|^2$; explicit rates follow for analytic and for Lipschitz $f$.
Below the grade the Ritz values are distinct, their nodal polynomial is the degree-$q$
orthogonal polynomial of $\mu_{\mathbf{A},\mathbf{b}}$, the Lanczos rule is the Gauss rule of
$\mu_{\mathbf{A},\mathbf{b}}$, and every Ritz value carries positive weight. None of this needs
tridiagonal theory: the compression lemmas of `NLAlib.Krylov.Basic.Compression` carry it.

## Main definitions

* `NLAlib.lanczosQuadrature`: the Lanczos rule as a measure.

## Main results

* `NLAlib.integral_lanczosQuadrature`: its integrals are the Lanczos quadratures.
* `NLAlib.HasOrthonormalCols.lanczosQuadrature_eq`,
  `Matrix.IsHermitian.lanczosQuadrature_succ_eq`,
  `Matrix.IsHermitian.lanczosQuadrature_succ_eq_sum`: the frame, tridiagonal and Golub–Welsch
  forms.
* `Matrix.IsHermitian.star_dotProduct_lanczosFA_eval`: exactness through degree $2q - 1$.
* `Matrix.IsHermitian.matchesMoments_lanczosQuadrature`: the rule matches $2q$ moments.
* `Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn`:
  the $2\varepsilon\|\mathbf{b}\|^2$ bound, with its analytic and Lipschitz rates.
* `NLAlib.HasOrthonormalCols.lanczosQuadrature_eq_interpolatoryQuadrature`: the Lanczos rule is
  the Gauss rule of the spectral measure.
* `NLAlib.HasOrthonormalCols.lanczosQuadrature_real_singleton_pos`: positive weights at the
  Ritz values.
* `Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`: Lanczos quadrature is the Gauss rule.
* `NLAlib.HasOrthonormalCols.nodal_eq_orthogonalPolynomial`,
  `NLAlib.HasOrthonormalCols.gaussNodes_spectralMeasure_eq`: the Ritz values are the Gauss nodes.
* `NLAlib.spectralMeasure_jacobiMatrix`, `NLAlib.spectralMeasure_map_jacobiMatrix`,
  `NLAlib.HasOrthonormalCols.gaussQuadrature_succ_eq_sum`: Golub–Welsch.
* `Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_continuousOn`: the bound
  $2E_{2q + 1}(f)\|\mathbf{b}\|^2$.
* `NLAlib.spectralMeasure_radauJacobiMatrix`: Golub–Welsch for the Radau rule.
* `Matrix.IsHermitian.integral_radauQuadrature_spectralMeasure`: the Radau quadrature of
  $\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$ from the modified tridiagonal.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix ComplexOrder MatrixOrder NNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r]
  [DecidableEq r]

/-! ### The Lanczos rule -/

/-- The **Lanczos (Gauss) quadrature rule** of $q$ steps from $\mathbf{b}$:
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q) := \mu_{\mathbf{P}\mathbf{A}\mathbf{P},
\mathbf{P}\mathbf{b}}$ with $\mathbf{P} = \mathbf{P}_{\mathbf{K}_q(\mathbf{A},\mathbf{b})}$; for
any orthonormal basis $\mathbf{Q}$ of the Krylov space it is the spectral measure of
$(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}, \mathbf{Q}^{\mathsf{H}}\mathbf{b})$
(`HasOrthonormalCols.lanczosQuadrature_eq`): atoms at the Ritz values. Junk: $0$ at $q = 0$ and
when the compression is not Hermitian. [GolubMeurant2010, Ch. 6]. -/
noncomputable def lanczosQuadrature (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) : Measure ℝ :=
  spectralMeasure (rangeProjector (krylovMatrix A b q) * A * rangeProjector (krylovMatrix A b q))
    (rangeProjector (krylovMatrix A b q) *ᵥ b)

/-- The Lanczos rule is a finite measure. -/
instance isFiniteMeasure_lanczosQuadrature (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    IsFiniteMeasure (lanczosQuadrature A b q) := by
  unfold lanczosQuadrature
  infer_instance

/-- The Lanczos quadrature as the quadratic form of the compression. -/
private theorem quadForm_cfc_rangeProjector (A : Matrix n n 𝕜) (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    quadForm (cfc f (rangeProjector (krylovMatrix A b q) * A * rangeProjector (krylovMatrix A b q)))
      (rangeProjector (krylovMatrix A b q) *ᵥ b) = star b ⬝ᵥ lanczosFA A f b q := by
  rw [quadForm_def, star_mulVec_dotProduct, conjTranspose_rangeProjector, lanczosFA, compressedCfc,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- The Lanczos quadrature from the Lanczos recurrence, as a quadratic form of $f(\mathbf{T})$. -/
private theorem star_dotProduct_lanczosFA_succ {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    star b ⬝ᵥ lanczosFA A f b (q + 1) = quadForm (cfc f (lanczosTridiagonal A b (q + 1)))
      ((‖WithLp.toLp 2 b‖ : 𝕜) • Pi.single 0 1) := by
  have hdot : ∀ v, star b ⬝ᵥ (arnoldiMatrix A b (q + 1) *ᵥ v) =
      star ((arnoldiMatrix A b (q + 1))ᴴ *ᵥ b) ⬝ᵥ v := fun v => by
    rw [star_mulVec_dotProduct, Matrix.conjTranspose_conjTranspose]
  rw [lanczosFA_eq_arnoldiMatrix, hA.lanczosTridiagonal_eq, dotProduct_smul, hdot,
    conjTranspose_arnoldiMatrix_mulVec_self]
  simp only [quadForm_def, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct,
    smul_eq_mul, RCLike.star_def, RCLike.conj_ofReal]

/-- The Lanczos rule integrates to the Lanczos quadrature: for every square $\mathbf{A}$,
every $f : \mathbb{R} \to \mathbb{R}$, $\mathbf{b}$ and $q$,
$$\int f\,d\,\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q) =
\operatorname{Re}\,\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)\,;$$
both sides are built from the same compression. -/
theorem integral_lanczosQuadrature (A : Matrix n n 𝕜) (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    ∫ x, f x ∂lanczosQuadrature A b q = RCLike.re (star b ⬝ᵥ lanczosFA A f b q) := by
  rw [lanczosQuadrature, integral_spectralMeasure, quadForm_cfc_rangeProjector]

/-- The Lanczos rule in any orthonormal basis of the Krylov space: for every square
$\mathbf{A}$ and $\mathbf{Q}$ with orthonormal columns spanning
$\mathcal{K}_q(\mathbf{A}, \mathbf{b})$,
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q) =
\mu_{\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q},\,\mathbf{Q}^{\mathsf{H}}\mathbf{b}}$; its atoms
are the Ritz values. Both sides are $0$ when $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ is not
Hermitian. -/
theorem HasOrthonormalCols.lanczosQuadrature_eq {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) :
    lanczosQuadrature A b q = spectralMeasure (Qᴴ * A * Q) (Qᴴ *ᵥ b) := by
  have hP : rangeProjector (krylovMatrix A b q) = Q * Qᴴ := by
    rw [← hQ.rangeProjector_eq]
    exact rangeProjector_inj.mpr hK.symm
  rw [lanczosQuadrature, hP, ← hQ.spectralMeasure_mul_mul_conjTranspose (Qᴴ * A * Q) (Qᴴ *ᵥ b),
    Matrix.mulVec_mulVec]
  simp only [Matrix.mul_assoc]

/-- The Lanczos rule from the Lanczos recurrence: for Hermitian $\mathbf{A}$ and every $q$,
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q + 1) =
\mu_{\mathbf{T},\,\|\mathbf{b}\|\mathbf{e}_0}$, with $\mathbf{T}$ the tridiagonal matrix of
$q + 1$ steps of the recurrence (`lanczosTridiagonal`). Past the grade the recurrence pads
$\mathbf{T}$ with zeros, and the statement still holds. -/
theorem _root_.Matrix.IsHermitian.lanczosQuadrature_succ_eq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) :
    lanczosQuadrature A b (q + 1) =
      spectralMeasure (lanczosTridiagonal A b (q + 1))
        ((‖WithLp.toLp 2 b‖ : 𝕜) • Pi.single 0 1) := by
  ext S hS
  rw [lanczosQuadrature, spectralMeasure_apply, spectralMeasure_apply, quadForm_cfc_rangeProjector,
    star_dotProduct_lanczosFA_succ hA]

/-- **The Lanczos quadrature from the tridiagonal matrix**: for Hermitian $\mathbf{A}$, every
$f : \mathbb{R} \to \mathbb{R}$ and every $q$,
$$\int f\,d\,\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q + 1) =
\|\mathbf{b}\|^2\operatorname{Re}\,\mathbf{e}_0^{\mathsf{H}}f(\mathbf{T})\mathbf{e}_0\,,$$
with $\mathbf{T}$ the tridiagonal matrix of $q + 1$ steps of the Lanczos recurrence.
[GolubMeurant2010, Theorem 6.6]. -/
theorem _root_.Matrix.IsHermitian.integral_lanczosQuadrature_succ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    ∫ x, f x ∂lanczosQuadrature A b (q + 1) =
      ‖WithLp.toLp 2 b‖ ^ 2 * RCLike.re (cfc f (lanczosTridiagonal A b (q + 1)) 0 0) := by
  rw [hA.lanczosQuadrature_succ_eq, integral_spectralMeasure, quadForm_smul_right,
    RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, RCLike.re_ofReal_mul, ← sq]
  congr 2
  simp [quadForm_def]

/-- **Golub–Welsch**: for Hermitian $\mathbf{A}$, every $q$, and a unitary diagonalisation
$\mathbf{T} = \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$ of the
tridiagonal matrix of $q + 1$ steps of the Lanczos recurrence,
$$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q + 1) =
\sum_i \|\mathbf{b}\|^2\lvert\mathbf{U}_{0,i}\rvert^2\,\delta_{\mathbf{d}_i}\,:$$
the nodes are the eigenvalues of $\mathbf{T}$, the weights the squared first entries of its
eigenvectors. [GolubMeurant2010, Theorem 6.2].
Result: lanczos-gauss-quadrature -/
theorem _root_.Matrix.IsHermitian.lanczosQuadrature_succ_eq_sum {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) {U : Matrix (Fin (q + 1)) (Fin (q + 1)) 𝕜}
    (hU : HasOrthonormalCols U) {d : Fin (q + 1) → ℝ}
    (hT : lanczosTridiagonal A b (q + 1) = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) :
    lanczosQuadrature A b (q + 1) =
      ∑ i, ENNReal.ofReal (‖WithLp.toLp 2 b‖ ^ 2 * ‖U 0 i‖ ^ 2) • Measure.dirac (d i) := by
  rw [hA.lanczosQuadrature_succ_eq, hU.spectralMeasure_eq_sum rfl hT]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, RCLike.norm_ofReal,
    abs_norm]
  simp

/-- The Lanczos rule lives in every interval containing the spectrum: for Hermitian
$\mathbf{A}$ with spectrum in $[a, a']$, almost every point of
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q)$ lies in $[a, a']$ (the Ritz values do). -/
theorem _root_.Matrix.IsHermitian.ae_mem_Icc_lanczosQuadrature {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (b : n → 𝕜) (q : ℕ) :
    ∀ᵐ x ∂lanczosQuadrature A b q, x ∈ Set.Icc a a' := by
  obtain ⟨k, Q, hQ, hK⟩ := exists_hasOrthonormalCols_range_eq_krylovSpace A b q
  rw [hQ.lanczosQuadrature_eq hK]
  exact ae_mem_Icc_spectralMeasure _ (hA.spectrum_conjTranspose_mul_mul_subset_Icc hs hQ) _

/-- The mass of the Lanczos rule: for Hermitian $\mathbf{A}$ and $q > 0$,
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q)(\mathbb{R}) = \|\mathbf{b}\|^2$, the mass
of $\mu_{\mathbf{A},\mathbf{b}}$. -/
theorem _root_.Matrix.IsHermitian.lanczosQuadrature_real_univ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) {q : ℕ} (hq : 0 < q) :
    (lanczosQuadrature A b q).real Set.univ = ‖WithLp.toLp 2 b‖ ^ 2 := by
  obtain ⟨k, Q, hQ, hK⟩ := exists_hasOrthonormalCols_range_eq_krylovSpace A b q
  rw [hQ.lanczosQuadrature_eq hK,
    (Matrix.isHermitian_conjTranspose_mul_mul Q hA).spectralMeasure_real_univ]
  obtain ⟨y, hy⟩ : b ∈ LinearMap.range Q.mulVecLin := hK ▸ self_mem_krylovSpace A b hq
  rw [← hy, Matrix.mulVecLin_apply, hQ.conjTranspose_mulVec_mulVec, hQ.norm_toLp_mulVec]

/-! ### Exactness -/

/-- **Gauss (Lanczos) quadrature is exact through degree $2q - 1$**: for Hermitian
$\mathbf{A}$ and a real polynomial $p$ with $\deg p < 2q$,
$\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, p, \mathbf{b}, q) =
\mathbf{b}^{\mathsf{H}}p(\mathbf{A})\mathbf{b}$; Lanczos-FA itself is exact only through degree
$q - 1$. [GolubMeurant2010, Ch. 6].
Result: lanczos-gauss-quadrature -/
theorem _root_.Matrix.IsHermitian.star_dotProduct_lanczosFA_eval {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) {q : ℕ} {p : ℝ[X]} (hp : p.degree < 2 * q) :
    star b ⬝ᵥ lanczosFA A (fun x => p.eval x) b q = quadForm (aeval A p) b := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hp0 : p = 0 := by
      rw [Nat.cast_zero, mul_zero] at hp
      exact degree_eq_bot.mp (WithBot.lt_coe_bot.mp hp)
    rw [hp0, lanczosFA_zero, dotProduct_zero, map_zero, quadForm_zero_left]
  obtain ⟨k, Q, hQ, hK⟩ := exists_hasOrthonormalCols_range_eq_krylovSpace A b q
  have hT : (Qᴴ * A * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  have hmon : (X ^ q : ℝ[X]).Monic := monic_X_pow q
  -- $p = X^q d + r$ with $\deg d, \deg r < q$
  set d := p /ₘ X ^ q
  set r := p %ₘ X ^ q
  have hpdr : p = X ^ q * d + r := by
    rw [add_comm]
    exact (modByMonic_add_div p (X ^ q)).symm
  have hr : r.degree < q := by
    have h := degree_modByMonic_lt p hmon
    rwa [degree_X_pow] at h
  have hd : d.degree < q := by
    have hnat : p.natDegree < 2 * q := by
      by_cases hp0 : p = 0
      · rw [hp0, natDegree_zero]
        omega
      · exact (natDegree_lt_iff_degree_lt hp0).mpr (by exact_mod_cast hp)
    have h := natDegree_divByMonic p hmon
    rw [natDegree_X_pow] at h
    exact (degree_le_natDegree).trans_lt (by rw [h]; exact_mod_cast (by omega))
  have hdot : ∀ u v, star u ⬝ᵥ (Q *ᵥ v) = star (Qᴴ *ᵥ u) ⬝ᵥ v := fun u v => by
    rw [star_mulVec_dotProduct, Matrix.conjTranspose_conjTranspose]
  have hpow : (Qᴴ * A * Q) ^ q *ᵥ (Qᴴ *ᵥ b) = Qᴴ *ᵥ (A ^ q *ᵥ b) := by
    have h := hQ.conjTranspose_mulVec_aeval_mulVec_eq hK (p := (X ^ q : ℝ[X]))
      (by rw [degree_X_pow])
    simpa only [map_pow, aeval_X] using h.symm
  -- the remainder part and the quotient part
  have hR := hQ.mulVec_aeval_conjTranspose_mul_mul_mulVec_eq hK hr
  have hD := hQ.mulVec_aeval_conjTranspose_mul_mul_mulVec_eq hK hd
  rw [hQ.lanczosFA_eq hK, hT.cfc_eq_aeval_of_forall_eval_eq (f := fun x => p.eval x)
    fun _ _ => rfl, hdot, quadForm_def, hpdr]
  simp only [map_add, map_mul, map_pow, aeval_X, Matrix.add_mulVec, dotProduct_add,
    ← Matrix.mulVec_mulVec]
  congr 1
  · rw [← (hT.pow q).eq, ← star_mulVec_dotProduct, hpow, ← hdot, hD,
      star_mulVec_dotProduct, (hA.pow q).eq]
  · rw [← hdot, hR]

/-- **Lanczos quadrature matches the first $2q$ moments of the spectral measure**: for
Hermitian $\mathbf{A}$, every $\mathbf{b}$ and every $q$,
$\int p\,d\mu_{\mathbf{A},\mathbf{b}} = \int p\,d\,\mathsf{lanczosQuadrature}(\mathbf{A},
\mathbf{b}, q)$ for every real polynomial $p$ of degree less than $2q$.
[GolubMeurant2010, Theorems 6.1–6.2]. [ChenTrogdonUbaru2022, §4.2] uses this polynomial exactness
for spectrum approximation.
Result: lanczos-gauss-quadrature -/
theorem _root_.Matrix.IsHermitian.matchesMoments_lanczosQuadrature {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) :
    MatchesMoments (spectralMeasure A b) (lanczosQuadrature A b q) (2 * q) := by
  intro p hp
  have hp' : p.degree < 2 * (q : WithBot ℕ) := by exact_mod_cast hp
  rw [hA.integral_eval_spectralMeasure, integral_lanczosQuadrature,
    hA.star_dotProduct_lanczosFA_eval b hp']

/-! ### Error bounds -/

/-- **The Lanczos quadrature error from uniform approximation**: for Hermitian $\mathbf{A}$
with spectrum in $[a, a']$, if a real polynomial $p$ of degree less than $2q$ is within
$\varepsilon$ of $f$ on $[a, a']$, then
$$\bigl\lvert\mathbf{b}^{\mathsf{H}}\bigl(f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)\bigr)\bigr\rvert \le
2\varepsilon\|\mathbf{b}\|^2\,:$$
the quadrature is exact on $p$, and $f - p$ is at most $\varepsilon$ on the spectrum and on
the Ritz values. [GolubMeurant2010, Ch. 6], the exactness it rests on. -/
theorem
_root_.Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {f : ℝ → ℝ} {q : ℕ} {p : ℝ[X]} (hp : p.degree < 2 * q) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε) (b : n → 𝕜) :
    ‖star b ⬝ᵥ (cfc f A *ᵥ b - lanczosFA A f b q)‖ ≤ 2 * ε * ‖WithLp.toLp 2 b‖ ^ 2 := by
  set g : ℝ → ℝ := fun x => f x - p.eval x
  -- the error is that of $g = f - p$, since the quadrature is exact on $p$
  have heq : star b ⬝ᵥ (cfc f A *ᵥ b - lanczosFA A f b q) =
      star b ⬝ᵥ (cfc g A *ᵥ b - lanczosFA A g b q) := by
    rw [lanczosFA_sub A f (fun x => p.eval x) b q,
      cfc_sub f (fun x => p.eval x) A (A.finite_real_spectrum.continuousOn _)
        (A.finite_real_spectrum.continuousOn _),
      hA.cfc_eq_aeval_of_forall_eval_eq (f := fun x => p.eval x) fun _ _ => rfl,
      Matrix.sub_mulVec]
    simp only [dotProduct_sub]
    rw [hA.star_dotProduct_lanczosFA_eval b hp, quadForm_def]
    ring
  have hg : Metric.IsUniformApproxOn (fun x => (0 : ℝ[X]).eval x) g (Set.Icc a a') ε :=
    fun x hx => by
      have h := hε.apply hx
      rw [Real.dist_eq, abs_sub_comm] at h
      change dist ((0 : ℝ[X]).eval x) (g x) ≤ ε
      rwa [eval_zero, Real.dist_eq, zero_sub, abs_neg]
  have hvec := hA.norm_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hs
    (by rw [degree_zero]; exact WithBot.bot_lt_coe q) hg b
  have hin : star b ⬝ᵥ (cfc g A *ᵥ b - lanczosFA A g b q) =
      inner 𝕜 (WithLp.toLp 2 b) (WithLp.toLp 2 (cfc g A *ᵥ b - lanczosFA A g b q)) := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [heq, hin]
  calc _ ≤ ‖WithLp.toLp 2 b‖ * ‖WithLp.toLp 2 (cfc g A *ᵥ b - lanczosFA A g b q)‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖WithLp.toLp 2 b‖ * (2 * ε * ‖WithLp.toLp 2 b‖) :=
        mul_le_mul_of_nonneg_left hvec (norm_nonneg _)
    _ = 2 * ε * ‖WithLp.toLp 2 b‖ ^ 2 := by ring

/-- **Lanczos quadrature for analytic functions**: let $\mathbf{A}$ be Hermitian with spectrum
in $[a, a']$, $a < a'$, and let $f$ on $[a, a']$, pulled back to $[-1, 1]$ by
$t \mapsto ((a' - a)t + a' + a)/2$, extend to a function holomorphic and bounded by $M$ on the
open Bernstein ellipse $E_\rho$, $\rho > 1$. Then $q + 1$ steps give
$$\bigl\lvert\mathbf{b}^{\mathsf{H}}\bigl(f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q + 1)\bigr)\bigr\rvert \le
\frac{4M}{\rho^{2q + 1}(\rho - 1)}\|\mathbf{b}\|^2\,,$$
twice the rate of Lanczos-FA in the exponent, from the Chebyshev truncation of degree
$2q + 1$. [Trefethen2019, Theorem 8.2, Eq. (8.2)], the approximation rate;
constants composed here.
Result: lanczos-gauss-quadrature -/
theorem
_root_.Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_differentiableOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => ((f (((a' - a) * t + a' + a) / 2) : ℝ) : ℂ))
      (fun t : ℝ => F t) (Set.Icc (-1 : ℝ) 1))
    (b : n → 𝕜) (q : ℕ) :
    ‖star b ⬝ᵥ (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      4 * M / (ρ ^ (2 * q + 1) * (ρ - 1)) * ‖WithLp.toLp 2 b‖ ^ 2 := by
  obtain ⟨p, hp, hε⟩ := exists_degree_le_isUniformApproxOn_Icc_of_differentiableOn (𝕜 := ℝ)
    (f := f) haa hρ hFd hM (fun t ht => by
      rw [← hExt ht]
      exact RCLike.toComplex_ofReal (𝕜 := ℝ) _) (2 * q + 1)
  have hp' : p.degree < 2 * ((q + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast (by omega : 2 * q + 1 < 2 * (q + 1)))
  have h := hA.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hs hp' hε b
  refine h.trans_eq ?_
  ring

/-- **Lanczos quadrature for Lipschitz functions**: for Hermitian $\mathbf{A}$ with spectrum in
$[a, a']$, $a < a'$, and $f$ $L$-Lipschitz on $[a, a']$, $q + 1$ steps
give <!-- value jacksonApproximationConstant -->
$$\bigl\lvert\mathbf{b}^{\mathsf{H}}\bigl(f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q + 1)\bigr)\bigr\rvert \le
\frac{\pi L(a' - a)}{2q + 3}\|\mathbf{b}\|^2\,,$$
from Jackson's theorem on $[a, a']$ in degree $2q + 1$ (the constant is
`jacksonApproximationConstant`). The approximation step is
[ChenTrogdonUbaru2022, Appendix C, Theorem 38]; constants composed here.
Result: lanczos-gauss-quadrature -/
theorem
_root_.Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_lipschitzOnWith
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a a')) (b : n → 𝕜) (q : ℕ) :
    ‖star b ⬝ᵥ (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      jacksonApproximationConstant * L * (a' - a) / (2 * q + 3) * ‖WithLp.toLp 2 b‖ ^ 2 := by
  obtain ⟨p, hp, hε⟩ :=
    exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith (𝕜 := ℝ) haa hf (2 * q + 1)
  have hp' : p.degree < 2 * ((q + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast (by omega : 2 * q + 1 < 2 * (q + 1)))
  have h := hA.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hs hp' hε b
  refine h.trans_eq ?_
  push_cast
  field_simp
  ring

/-! ### The orthogonal-polynomial reading -/

/-- At most $\min(q, \nu)$ Ritz values: the compression is $\dim\mathcal{K}_q$ square. -/
private theorem card_spectrum_le_of_range_eq {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) :
    Nat.card (spectrum ℝ (Qᴴ * A * Q)) ≤ min q (krylovGrade A b) := by
  have hT : (Qᴴ * A * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  have hr : Fintype.card r = min q (krylovGrade A b) := by
    rw [← hQ.rank_eq, ← finrank_krylovSpace, ← hK]
    rfl
  rw [Nat.card_coe_set_eq, ← hr]
  exact hT.ncard_spectrum_le

/-- The number of distinct Ritz values as the cardinality of a finset listing them. -/
private theorem card_eq_natCard_spectrum {B : Matrix r r 𝕜} {s : Finset ℝ}
    (hs : (s : Set ℝ) = spectrum ℝ B) : s.card = Nat.card (spectrum ℝ B) := by
  rw [← hs, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- Every real function is integrable against the Lanczos rule, a spectral measure. -/
private theorem integrable_lanczosQuadrature (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ)
    (f : ℝ → ℝ) : Integrable f (lanczosQuadrature A b q) :=
  integrable_spectralMeasure _ _ f

/-- The Lanczos rule sees a function only through its values at the Ritz values. -/
private theorem integral_lanczosQuadrature_congr {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) {f g : ℝ → ℝ}
    (hfg : Set.EqOn f g (spectrum ℝ (Qᴴ * A * Q))) :
    ∫ x, f x ∂lanczosQuadrature A b q = ∫ x, g x ∂lanczosQuadrature A b q := by
  rw [hQ.lanczosQuadrature_eq hK, integral_spectralMeasure, integral_spectralMeasure,
    cfc_congr hfg]

/-- The Lanczos rule as a sum over the Ritz values with the interpolatory weights of
$\mu_{\mathbf{A},\mathbf{b}}$: $\int f\,d\,\mathsf{lanczosQuadrature} =
\sum_{x\in s}\bigl(\int\ell_x\,d\mu_{\mathbf{A},\mathbf{b}}\bigr)f(x)$. -/
private theorem integral_lanczosQuadrature_eq_sum {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) {s : Finset ℝ}
    (hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q)) (f : ℝ → ℝ) :
    ∫ t, f t ∂lanczosQuadrature A b q =
      ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂spectralMeasure A b) * f x := by
  have hcard : s.card ≤ q := by
    rw [card_eq_natCard_spectrum hs]
    exact (card_spectrum_le_of_range_eq hQ hA hK).trans (min_le_left _ _)
  rw [integral_lanczosQuadrature_congr hQ hK (g := fun t => (Lagrange.interpolate s id f).eval t)
    fun t ht => by
      rw [← hs] at ht
      exact (Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) ht).symm]
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]
  rw [integral_finsetSum s fun x _ => integrable_lanczosQuadrature A b q _]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hdeg : (Lagrange.basis s id x).degree < (2 * q : ℕ) := by
    rw [Lagrange.degree_basis (Set.injOn_id _) hx]
    exact_mod_cast (by omega : s.card - 1 < 2 * q)
  rw [integral_const_mul, mul_comm,
    hA.matchesMoments_lanczosQuadrature b q _ hdeg]

/-- The interpolatory weights of $\mu_{\mathbf{A},\mathbf{b}}$ at the Ritz values are
nonnegative: $\int\ell_x\,d\mu_{\mathbf{A},\mathbf{b}} =
\int\ell_x^2\,d\,\mathsf{lanczosQuadrature}$. -/
private theorem integral_basis_nonneg {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) {s : Finset ℝ}
    (hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q)) {x : ℝ} (hx : x ∈ s) :
    0 ≤ ∫ t, (Lagrange.basis s id x).eval t ∂spectralMeasure A b := by
  have hcard : s.card ≤ q := by
    rw [card_eq_natCard_spectrum hs]
    exact (card_spectrum_le_of_range_eq hQ hA hK).trans (min_le_left _ _)
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hdeg : (Lagrange.basis s id x).degree < (2 * q : ℕ) := by
    rw [Lagrange.degree_basis (Set.injOn_id _) hx]
    exact_mod_cast (by omega : s.card - 1 < 2 * q)
  rw [hA.matchesMoments_lanczosQuadrature b q _ hdeg,
    integral_lanczosQuadrature_congr hQ hK (g := fun t => (Lagrange.basis s id x).eval t ^ 2)]
  · exact integral_nonneg fun t => sq_nonneg _
  · intro t ht
    rw [← hs] at ht
    by_cases htx : t = x
    · have h1 : (Lagrange.basis s id x).eval x = 1 :=
        Lagrange.eval_basis_self (v := id) (Set.injOn_id _) hx
      simp only [htx, h1, one_pow]
    · have h0 : (Lagrange.basis s id x).eval t = 0 :=
        Lagrange.eval_basis_of_ne (v := id) (Ne.symm htx) ht
      simp only [h0]
      ring

/-- Distinct Ritz values below the grade: for Hermitian $\mathbf{A}$, $\mathbf{Q}$ with
orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$ and $q$ at most the grade
of $\mathbf{b}$, the compression $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ has exactly $q$
distinct eigenvalues: a nodal polynomial of fewer Ritz values would make $\pi(\mathbf{A})\mathbf{b}$
a vector of $\mathcal{K}_q$ orthogonal to $\mathcal{K}_q$, hence zero, against the grade. -/
theorem HasOrthonormalCols.card_spectrum_conjTranspose_mul_mul_eq {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b) :
    Nat.card (spectrum ℝ (Qᴴ * A * Q)) = q := by
  refine le_antisymm ((card_spectrum_le_of_range_eq hQ hA hK).trans (min_le_left _ _)) ?_
  by_contra hlt
  push Not at hlt
  have hT : (Qᴴ * A * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  set s := (Qᴴ * A * Q).finite_real_spectrum.toFinset
  have hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q) := Set.Finite.coe_toFinset _
  have hsc : s.card < q := by rwa [card_eq_natCard_spectrum hs]
  have hdeg : (Lagrange.nodal s id).degree < q := by
    rw [Lagrange.degree_nodal]
    exact_mod_cast hsc
  have h0 : aeval A (Lagrange.nodal s id) *ᵥ b = 0 := by
    rw [← hQ.mulVec_aeval_conjTranspose_mul_mul_mulVec_eq hK hdeg, hT.aeval_nodal_eq_zero hs.ge,
      Matrix.zero_mulVec, Matrix.mulVec_zero]
  exact aeval_mulVec_ne_zero_of_degree_lt_krylovGrade Lagrange.nodal_monic.ne_zero
    (hdeg.trans_le (by exact_mod_cast hq)) h0

/-- **The Ritz polynomial is the orthogonal polynomial**: for Hermitian $\mathbf{A}$ and
$\mathbf{Q}$ with orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$, the
nodal polynomial $\pi(z) = \prod_{\theta\in s}(z - \theta)$ of the set $s$ of distinct Ritz values
(the eigenvalues of $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$) is orthogonal in
$L^2(\mu_{\mathbf{A},\mathbf{b}})$ to every real polynomial of degree less than $q$.
[GolubMeurant2010, Ch. 4]; there through the Lanczos polynomials. -/
theorem HasOrthonormalCols.isOrthogonalPolynomial_nodal {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) {s : Finset ℝ}
    (hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q)) :
    IsOrthogonalPolynomial (spectralMeasure A b) q (Lagrange.nodal s id) := by
  intro p hp
  have hcard : s.card ≤ q := by
    rw [card_eq_natCard_spectrum hs]
    exact (card_spectrum_le_of_range_eq hQ hA hK).trans (min_le_left _ _)
  have h0 := hQ.conjTranspose_mulVec_aeval_nodal_mulVec_eq_zero hA hK hs.ge hcard
  have heval : ∀ t, (Lagrange.nodal s id).eval t * p.eval t =
      (p * Lagrange.nodal s id).eval t := fun t => by
    rw [eval_mul, mul_comm]
  simp_rw [heval]
  rw [hA.integral_eval_spectralMeasure, map_mul, quadForm_def, ← Matrix.mulVec_mulVec,
    ← (hA.aeval p).eq, ← star_mulVec_dotProduct]
  obtain ⟨y, hy⟩ : aeval A p *ᵥ b ∈ LinearMap.range Q.mulVecLin :=
    hK ▸ aeval_mulVec_mem_krylovSpace A b hp
  rw [← hy, Matrix.mulVecLin_apply, star_mulVec_dotProduct, h0, dotProduct_zero, map_zero]

/-- **Lanczos quadrature is the Gauss rule of the spectral measure**: for Hermitian
$\mathbf{A}$, $\mathbf{Q}$ with orthonormal columns spanning
$\mathcal{K}_q(\mathbf{A}, \mathbf{b})$ and every $q$,
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q)$ is the interpolatory rule of
$\mu_{\mathbf{A},\mathbf{b}}$ at the set $s$ of the distinct Ritz values (the eigenvalues of
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$), $q$ of them when $q$ is at most the grade of
$\mathbf{b}$. Past the grade both sides are $\mu_{\mathbf{A},\mathbf{b}}$ itself.
[GolubMeurant2010, Ch. 6].
Result: lanczos-gauss-quadrature -/
theorem HasOrthonormalCols.lanczosQuadrature_eq_interpolatoryQuadrature {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q)
    {s : Finset ℝ} (hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q)) :
    lanczosQuadrature A b q = interpolatoryQuadrature (spectralMeasure A b) s := by
  ext S hS
  rw [← ofReal_measureReal (measure_ne_top _ S), ← ofReal_measureReal (measure_ne_top _ S),
    ← integral_indicator_one hS, ← integral_indicator_one hS,
    integral_lanczosQuadrature_eq_sum hQ hA hK hs]
  congr 1
  unfold interpolatoryQuadrature
  rw [integral_finsetSum_measure fun x _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (integral_basis_nonneg hQ hA hK hs hx)]

/-- Every Ritz value carries positive weight: for Hermitian $\mathbf{A}$, $\mathbf{Q}$ with
orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$, every $q$ and a Ritz
value $x$ (an eigenvalue of $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$),
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q)(\{x\}) > 0$; so the support of the
Lanczos rule is exactly the set of Ritz values. The weight is
$\int\ell_x\,d\mu_{\mathbf{A},\mathbf{b}} = \|\ell_x(\mathbf{A})\mathbf{b}\|^2$, $\ell_x$ the
Lagrange basis polynomial of $x$ at the Ritz values, and $\ell_x(\mathbf{A})\mathbf{b} \ne
\mathbf{0}$ because $\ell_x$ is a nonzero polynomial of degree less than
$\dim\mathcal{K}_q(\mathbf{A}, \mathbf{b})$, which is at most the grade. -/
theorem HasOrthonormalCols.lanczosQuadrature_real_singleton_pos {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q)
    {x : ℝ} (hx : x ∈ spectrum ℝ (Qᴴ * A * Q)) :
    0 < (lanczosQuadrature A b q).real {x} := by
  set s := (Qᴴ * A * Q).finite_real_spectrum.toFinset
  have hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q) := Set.Finite.coe_toFinset _
  have hxs : x ∈ s := by
    rw [← Finset.mem_coe, hs]
    exact hx
  set ℓ := Lagrange.basis s id x
  have hcard : s.card ≤ min q (krylovGrade A b) := by
    rw [card_eq_natCard_spectrum hs]
    exact card_spectrum_le_of_range_eq hQ hA hK
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨x, hxs⟩
  have hℓ : ℓ.degree < (s.card : WithBot ℕ) := by
    rw [Lagrange.degree_basis (Set.injOn_id _) hxs]
    exact_mod_cast (by omega : s.card - 1 < s.card)
  have hℓ2 : (ℓ ^ 2).degree < (2 * q : ℕ) := by
    have h1 : (ℓ ^ 2).natDegree < 2 * q := by
      have := natDegree_pow_le (p := ℓ) (n := 2)
      rw [Lagrange.natDegree_basis (Set.injOn_id _) hxs] at this
      have : min q (krylovGrade A b) ≤ q := min_le_left _ _
      omega
    exact degree_le_natDegree.trans_lt (by exact_mod_cast h1)
  have hw : aeval A ℓ *ᵥ b ≠ 0 := aeval_mulVec_ne_zero_of_degree_lt_krylovGrade
    (Lagrange.basis_ne_zero (Set.injOn_id _) hxs)
    (hℓ.trans_le (by exact_mod_cast hcard.trans (min_le_right _ _)))
  have hq : star b ⬝ᵥ (aeval A ℓ *ᵥ (aeval A ℓ *ᵥ b)) =
      star (aeval A ℓ *ᵥ b) ⬝ᵥ (aeval A ℓ *ᵥ b) := by
    rw [star_mulVec_dotProduct, (hA.aeval ℓ).eq]
  rw [← integral_indicator_one (measurableSet_singleton x),
    integral_lanczosQuadrature_congr hQ hK (g := fun t => (ℓ ^ 2).eval t),
    ← hA.matchesMoments_lanczosQuadrature b q _ hℓ2, hA.integral_eval_spectralMeasure,
    quadForm_def, map_pow, sq, ← Matrix.mulVec_mulVec, hq]
  · exact (RCLike.pos_iff.mp (Matrix.dotProduct_star_self_pos_iff.mpr hw)).1
  · intro t ht
    rw [← hs] at ht
    by_cases htx : t = x
    · have h1 : ℓ.eval x = 1 := Lagrange.eval_basis_self (v := id) (Set.injOn_id _) hxs
      simp only [htx, Set.indicator_of_mem (Set.mem_singleton x), Pi.one_apply, eval_pow, h1,
        one_pow]
    · have h0 : ℓ.eval t = 0 := Lagrange.eval_basis_of_ne (v := id) (Ne.symm htx) ht
      simp [Set.indicator_of_notMem (show t ∉ ({x} : Set ℝ) by simpa using htx), h0]

/-- **Lanczos quadrature is the Gauss rule of the spectral measure**: for Hermitian
$\mathbf{A}$ and every $q$,
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q)$ is the $q$-point Gauss rule of
$\mu_{\mathbf{A},\mathbf{b}}$, for every `RCLike` field (complex Hermitian included).
[GolubMeurant2010, Ch. 6].
Result: lanczos-gauss-quadrature -/
theorem _root_.Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) :
    lanczosQuadrature A b q = gaussQuadrature (spectralMeasure A b) q := by
  classical
  obtain ⟨k, Q, hQ, hK⟩ := exists_hasOrthonormalCols_range_eq_krylovSpace A b q
  have hT : (Qᴴ * A * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  have hfinT : (spectrum ℝ (Qᴴ * A * Q)).Finite := Matrix.finite_real_spectrum
  have hcard : hfinT.toFinset.card ≤ q := by
    rw [← Set.ncard_eq_toFinset_card _ hfinT, ← Nat.card_coe_set_eq]
    exact (card_spectrum_le_of_range_eq hQ hA hK).trans (min_le_left _ _)
  have hν : ∀ᵐ x ∂lanczosQuadrature A b q, x ∈ hfinT.toFinset := by
    rw [hQ.lanczosQuadrature_eq hK]
    have hae : ∀ᵐ x ∂spectralMeasure (Qᴴ * A * Q) (Qᴴ *ᵥ b), x ∈ spectrum ℝ (Qᴴ * A * Q) :=
      ae_iff.2 (spectralMeasure_compl_spectrum_eq_zero _ _)
    filter_upwards [hae] with x hx
    exact hfinT.mem_toFinset.2 hx
  obtain ⟨a, c, hμ⟩ := exists_ae_mem_Icc_spectralMeasure A b
  exact (hA.matchesMoments_lanczosQuadrature b q).eq_gaussQuadrature hμ hν hcard

/-- **The Ritz values are the Gauss nodes** (nodal form): for Hermitian $\mathbf{A}$,
$\mathbf{Q}$ with orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$, $q$ at
most the grade and $s$ the set of Ritz values, the nodal polynomial of $s$ is the monic
orthogonal polynomial of degree $q$ of $\mu_{\mathbf{A},\mathbf{b}}$. [GolubMeurant2010, Theorem
6.2]. -/
theorem HasOrthonormalCols.nodal_eq_orthogonalPolynomial {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b)
    {s : Finset ℝ} (hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q)) :
    Lagrange.nodal s id = orthogonalPolynomial (spectralMeasure A b) q := by
  have hpos : IsMomentPosDef (spectralMeasure A b) q :=
    (hA.isMomentPosDef_spectralMeasure_iff b q).mpr hq
  have hcard : s.card = q :=
    (card_eq_natCard_spectrum hs).trans (hQ.card_spectrum_conjTranspose_mul_mul_eq hA hK hq)
  obtain ⟨a, c, hμ⟩ := exists_ae_mem_Icc_spectralMeasure A b
  exact hpos.eq_orthogonalPolynomial hμ Lagrange.nodal_monic
    (by rw [Lagrange.natDegree_nodal, hcard]) (hQ.isOrthogonalPolynomial_nodal hA hK hs)

/-- **The Ritz values are the Gauss nodes**: for Hermitian $\mathbf{A}$, $\mathbf{Q}$ with
orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$, $q$ at most the grade and
$s$ the set of Ritz values, the Gauss nodes of order $q$ of $\mu_{\mathbf{A},\mathbf{b}}$ are $s$.
The grade hypothesis is needed: past the grade the Gauss nodes can contain a spurious $0$ of
weight $0$. [GolubMeurant2010, Theorem 6.2]. -/
theorem HasOrthonormalCols.gaussNodes_spectralMeasure_eq {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b)
    {s : Finset ℝ} (hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q)) :
    gaussNodes (spectralMeasure A b) q = s := by
  rw [gaussNodes, ← hQ.nodal_eq_orthogonalPolynomial hA hK hq hs, Lagrange.nodal]
  simp [roots_prod_X_sub_C]

/-- **Golub–Welsch**: for a finite measure $\mu$ supported in $[a, c]$ and every $k$, the
$(k+1)$-point Gauss rule of $\mu$ is the spectral measure of its Jacobi matrix and
$\sqrt{\mu(\mathbb{R})}\,\mathbf{e}_0$: its nodes are the eigenvalues of
$\mathbf{J}_{k+1}(\mu)$ and its weights $\mu(\mathbb{R})$ times the squared first components of
the eigenvectors. Past the support size of $\mu$ the matrix has zero rows, and the extra
eigenvalues carry no weight. [Gautschi2004, Theorem 3.1]; [GolubWelsch1969, §2, Eq. (2.6)].
Result: golub-welsch -/
theorem spectralMeasure_jacobiMatrix (μ : Measure ℝ) [IsFiniteMeasure μ] {a c : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a c) (k : ℕ) :
    spectralMeasure (jacobiMatrix μ (k + 1)) ((√(μ.real Set.univ) : ℝ) • Pi.single 0 1) =
      gaussQuadrature μ (k + 1) := by
  set ν := gaussQuadrature μ (k + 1) with hνdef
  have hν_mem : ∀ᵐ x ∂ν, x ∈ gaussNodes μ (k + 1) := ae_mem_interpolatoryQuadrature μ _
  have hD : spectralMeasure (Matrix.diagonal fun x : gaussNodes μ (k + 1) => (x : ℝ))
      (fun x => √(ν.real {(x : ℝ)})) = ν :=
    spectralMeasure_diagonal_sqrt_of_ae_mem hν_mem
  have hDh : (Matrix.diagonal fun x : gaussNodes μ (k + 1) => (x : ℝ)).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by funext x; rfl)
  have hgauss : lanczosQuadrature (Matrix.diagonal fun x : gaussNodes μ (k + 1) => (x : ℝ))
      (fun x => √(ν.real {(x : ℝ)})) (k + 1) = ν := by
    rw [hDh.lanczosQuadrature_eq_gaussQuadrature, hD]
    exact (MatchesMoments.eq_gaussQuadrature (MatchesMoments.refl ν _)
      (ae_mem_Icc_gaussQuadrature hμ (k + 1)) hν_mem (card_gaussNodes_le μ (k + 1))).symm
  have hT : lanczosTridiagonal (Matrix.diagonal fun x : gaussNodes μ (k + 1) => (x : ℝ))
      (fun x => √(ν.real {(x : ℝ)})) (k + 1) = jacobiMatrix ν (k + 1) := by
    rw [hDh.lanczosTridiagonal_eq_jacobiMatrix, hD]
    simp
  have hnorm : ‖WithLp.toLp 2 (fun x : gaussNodes μ (k + 1) => √(ν.real {(x : ℝ)}))‖ =
      √(μ.real Set.univ) := by
    have h1 := hDh.spectralMeasure_real_univ
      (fun x : gaussNodes μ (k + 1) => √(ν.real {(x : ℝ)}))
    have hmass : ν.real Set.univ = μ.real Set.univ := by
      rw [hνdef]; exact gaussQuadrature_real_univ hμ (Nat.succ_pos k)
    rw [hD, hmass] at h1
    rw [h1, Real.sqrt_sq (norm_nonneg _)]
  have hJ : jacobiMatrix μ (k + 1) = jacobiMatrix ν (k + 1) :=
    MatchesMoments.jacobiMatrix_eq (matchesMoments_gaussQuadrature hμ (k + 1))
  calc spectralMeasure (jacobiMatrix μ (k + 1)) ((√(μ.real Set.univ) : ℝ) • Pi.single 0 1)
      = spectralMeasure (lanczosTridiagonal (Matrix.diagonal fun x : gaussNodes μ (k + 1) =>
            (x : ℝ)) (fun x => √(ν.real {(x : ℝ)})) (k + 1))
          ((√(μ.real Set.univ) : ℝ) • Pi.single 0 1) := by
        rw [hJ, hT]
    _ = spectralMeasure (lanczosTridiagonal (Matrix.diagonal fun x : gaussNodes μ (k + 1) =>
            (x : ℝ)) (fun x => √(ν.real {(x : ℝ)})) (k + 1))
          ((‖WithLp.toLp 2 (fun x : gaussNodes μ (k + 1) => √(ν.real {(x : ℝ)}))‖ : ℝ) •
            Pi.single 0 1) := by
        rw [hnorm]
    _ = lanczosQuadrature (Matrix.diagonal fun x : gaussNodes μ (k + 1) => (x : ℝ))
          (fun x => √(ν.real {(x : ℝ)})) (k + 1) :=
        (hDh.lanczosQuadrature_succ_eq _ _).symm
    _ = ν := hgauss

/-- **Golub–Welsch, explicit form**: for a finite measure $\mu$ supported in $[a, c]$, every
$k$, and an orthogonal diagonalisation
$\mathbf{J}_{k+1}(\mu) = \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$ of its
Jacobi matrix,
$$\mathsf{gaussQuadrature}(\mu, k + 1) = \sum_i\mu(\mathbb{R})\,\mathbf{U}_{0,i}^2\,
\delta_{\mathbf{d}_i}\,.$$
[Gautschi2004, Theorem 3.1]; [GolubWelsch1969, §2, Eq. (2.6)]. -/
theorem HasOrthonormalCols.gaussQuadrature_succ_eq_sum {k : ℕ}
    {U : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} (hU : HasOrthonormalCols U) {μ : Measure ℝ}
    [IsFiniteMeasure μ] {a c : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a c) {d : Fin (k + 1) → ℝ}
    (hJ : jacobiMatrix μ (k + 1) = U * Matrix.diagonal d * Uᴴ) :
    gaussQuadrature μ (k + 1) =
      ∑ i, ENNReal.ofReal (μ.real Set.univ * U 0 i ^ 2) • Measure.dirac (d i) := by
  rw [← spectralMeasure_jacobiMatrix μ hμ k,
    hU.spectralMeasure_eq_sum rfl (by simpa using hJ) ((√(μ.real Set.univ) : ℝ) • Pi.single 0 1)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 3
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one]
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.col_apply, Matrix.transpose_apply,
    norm_mul, Real.norm_eq_abs]
  rw [mul_pow, sq_abs, sq_abs, Real.sq_sqrt measureReal_nonneg]

/-- **Golub–Welsch over any `RCLike` field**: for a finite measure $\mu$ supported in $[a, c]$
and every $k$, the $(k+1)$-point Gauss rule of $\mu$ is the spectral measure of the Jacobi matrix
$\mathbf{J}_{k+1}(\mu)$, with its real entries read in $\Bbbk$, and
$\sqrt{\mu(\mathbb{R})}\,\mathbf{e}_0$. The form for implementation statements over a complex
Hermitian matrix. [Gautschi2004, Theorem 3.1]; [GolubWelsch1969, §2, Eq. (2.6)]. -/
theorem spectralMeasure_map_jacobiMatrix (μ : Measure ℝ) [IsFiniteMeasure μ] {a c : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a c) (k : ℕ) :
    spectralMeasure ((jacobiMatrix μ (k + 1)).map (algebraMap ℝ 𝕜))
        ((√(μ.real Set.univ) : 𝕜) • Pi.single 0 1) = gaussQuadrature μ (k + 1) := by
  have hJh : (jacobiMatrix μ (k + 1)).IsHermitian := isHermitian_jacobiMatrix μ (k + 1)
  have hJ : jacobiMatrix μ (k + 1) =
      (hJh.eigenvectorUnitary : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) *
        Matrix.diagonal hJh.eigenvalues *
        (hJh.eigenvectorUnitary : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)ᴴ :=
    hJh.spectral_theorem
  have hU := hasOrthonormalCols_iff_mem_unitaryGroup.2 hJh.eigenvectorUnitary.2
  have hVU : HasOrthonormalCols
      ((hJh.eigenvectorUnitary : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).map (algebraMap ℝ 𝕜)) := by
    rw [hasOrthonormalCols_iff, ← Matrix.conjTranspose_map _ fun r => by simp, ← Matrix.map_mul,
      hasOrthonormalCols_iff.mp hU, Matrix.map_one _ (map_zero _) (map_one _)]
  have hA : (jacobiMatrix μ (k + 1)).map (algebraMap ℝ 𝕜) =
      (hJh.eigenvectorUnitary : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).map (algebraMap ℝ 𝕜) *
        Matrix.diagonal (fun i => ((hJh.eigenvalues i : ℝ) : 𝕜)) *
        (((hJh.eigenvectorUnitary : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ)).map
          (algebraMap ℝ 𝕜))ᴴ := by
    conv_lhs => rw [hJ]
    rw [← Matrix.conjTranspose_map _ fun r => by simp, Matrix.map_mul, Matrix.map_mul,
      Matrix.diagonal_map (map_zero _)]
  rw [hVU.spectralMeasure_eq_sum rfl hA, HasOrthonormalCols.gaussQuadrature_succ_eq_sum hU hμ hJ]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 3
  simp only [algebraMap_smul, Matrix.mulVec_smul, Matrix.mulVec_single, MulOpposite.op_one,
    one_smul, Pi.smul_apply, Matrix.col_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, RCLike.star_def, RCLike.conj_ofReal,
    RCLike.real_smul_ofReal, norm_mul, norm_algebraMap', Real.norm_eq_abs]
  rw [mul_pow, sq_abs, sq_abs, Real.sq_sqrt measureReal_nonneg]

/-- **Lanczos quadrature and the minimax error**: for Hermitian $\mathbf{A}$ with spectrum in
$[a, a']$ and $f$ continuous on $[a, a']$, $q + 1$ Lanczos steps give
$$\bigl\lvert\mathbf{b}^{\mathsf{H}}\bigl(f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q + 1)\bigr)\bigr\rvert \le
2E_{2q + 1}(f; [a, a'])\|\mathbf{b}\|^2\,,$$
$E_{2q + 1}$ the error of the best uniform approximation of $f$ on $[a, a']$ by polynomials of
degree at most $2q + 1$ (`minimaxError`), the degree of exactness of the Gauss rule.
[GolubMeurant2010, Ch. 6], the exactness it rests on.
Result: lanczos-gauss-quadrature -/
theorem
_root_.Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_continuousOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) (b : n → 𝕜) (q : ℕ) :
    ‖star b ⬝ᵥ (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      2 * minimaxError f (Set.Icc a a') (2 * q + 1) * ‖WithLp.toLp 2 b‖ ^ 2 := by
  obtain ⟨p, hp, hε⟩ :=
    exists_degree_le_isUniformApproxOn_minimaxError isCompact_Icc hf (2 * q + 1)
  have hp' : p.degree < 2 * ((q + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast (by omega : 2 * q + 1 < 2 * (q + 1)))
  exact hA.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hs hp' hε b

/-! ### Golub–Welsch for the Radau rule -/

/-- The Radau Jacobi matrix is real symmetric: it differs from `jacobiMatrix` in one diagonal
entry. -/
private lemma radauJacobiMatrix_isHermitian (μ : Measure ℝ) (c : ℝ) (k : ℕ) :
    (radauJacobiMatrix μ c k).IsHermitian := by
  have hJ := isHermitian_jacobiMatrix μ (k + 1)
  have hji : ∀ i j, jacobiMatrix μ (k + 1) j i = jacobiMatrix μ (k + 1) i j := fun i j => by
    have := congrFun (congrFun hJ.eq j) i
    simpa [Matrix.conjTranspose_apply] using this.symm
  unfold radauJacobiMatrix
  ext i j
  by_cases hi : i = Fin.last k <;> by_cases hj : j = Fin.last k <;>
    simp [Matrix.conjTranspose_apply, hi, hj, hji]

/-- The spectral measure of a real Hermitian matrix at `√(μ(ℝ)) e₀`: its moments are
`μ(ℝ)` times the `(0, 0)` entry of the polynomial in the matrix. -/
private lemma integral_eval_spectralMeasure_e0 (μ : Measure ℝ) {m : ℕ}
    {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} (hA : A.IsHermitian) (p : ℝ[X]) :
    ∫ x, p.eval x ∂spectralMeasure A ((√(μ.real Set.univ) : ℝ) • Pi.single 0 1) =
      μ.real Set.univ * aeval A p 0 0 := by
  rw [hA.integral_eval_spectralMeasure, quadForm_def, Matrix.mulVec_smul,
    Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply, ← mul_assoc, Real.mul_self_sqrt measureReal_nonneg]

/-- **Golub–Welsch for the Radau rule**: for a finite measure $\mu$ supported in $[a, b]$,
positive definite up to degree $k + 1$, and $c \in \{a, b\}$, the Radau rule of $\mu$ with
prescribed node $c$ and $k$ free nodes is the spectral measure of the Radau Jacobi matrix
$\tilde{\mathbf{J}}$ of order $k + 1$ and $\sqrt{\mu(\mathbb{R})}\,\mathbf{e}_0$: its nodes are
the eigenvalues of $\tilde{\mathbf{J}}$ (one of them $c$) and its weights $\mu(\mathbb{R})$ times
the squared first eigenvector components. [Golub1973, §7, Eqs. (7.4)–(7.6)]; [GolubMeurant2010,
§6.2.2].
Result: gauss-radau-jacobi-matrix -/
theorem spectralMeasure_radauJacobiMatrix (μ : Measure ℝ) [IsFiniteMeasure μ] {a b c : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b) {k : ℕ} (h : IsMomentPosDef μ (k + 1)) :
    spectralMeasure (radauJacobiMatrix μ c k) ((√(μ.real Set.univ) : ℝ) • Pi.single 0 1) =
      radauQuadrature μ c k := by
  have hJh := radauJacobiMatrix_isHermitian μ c k
  have hmom : MatchesMoments μ
      (spectralMeasure (radauJacobiMatrix μ c k) ((√(μ.real Set.univ) : ℝ) • Pi.single 0 1))
      (2 * k + 1) := by
    intro p hp
    have hdeg : p.natDegree ≤ 2 * k :=
      Polynomial.natDegree_le_iff_degree_le.2 (Order.le_of_lt_succ (by exact_mod_cast hp))
    have hentry : aeval (radauJacobiMatrix μ c k) p 0 0 = aeval (jacobiMatrix μ (k + 1)) p 0 0 := by
      rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.sum_apply, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [Matrix.smul_apply, Matrix.smul_apply,
        radauJacobiMatrix_pow_apply_zero_zero μ c (by omega : i ≤ 2 * k)]
    have hchain : ∫ x, p.eval x ∂spectralMeasure (radauJacobiMatrix μ c k)
        ((√(μ.real Set.univ) : ℝ) • Pi.single 0 1) =
        ∫ x, p.eval x ∂gaussQuadrature μ (k + 1) := by
      rw [integral_eval_spectralMeasure_e0 μ hJh p, hentry,
        ← integral_eval_spectralMeasure_e0 μ (isHermitian_jacobiMatrix μ (k + 1)) p,
        spectralMeasure_jacobiMatrix μ hμ k]
    rw [hchain]
    exact matchesMoments_gaussQuadrature hμ (k + 1) p
      (lt_of_lt_of_le hp (by exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * (k + 1))))
  have hfin := (radauJacobiMatrix μ c k).finite_real_spectrum
  have hspec : c ∈ spectrum ℝ (radauJacobiMatrix μ c k) := h.mem_spectrum_radauJacobiMatrix hμ hc
  have hcmem : c ∈ hfin.toFinset := hfin.mem_toFinset.2 hspec
  have hcard : (hfin.toFinset.erase c).card ≤ k := by
    have htot : hfin.toFinset.card ≤ k + 1 := by
      refine (Finset.card_le_card (t := Finset.univ.image hJh.eigenvalues) fun x hx => ?_).trans
        (Finset.card_image_le.trans (by simp))
      obtain ⟨i, rfl⟩ := hJh.spectrum_real_eq_range_eigenvalues ▸ hfin.mem_toFinset.1 hx
      simp
    rw [Finset.card_erase_of_mem hcmem]
    omega
  have hsupp : ∀ᵐ x ∂spectralMeasure (radauJacobiMatrix μ c k)
      ((√(μ.real Set.univ) : ℝ) • Pi.single 0 1), x ∈ insert c (hfin.toFinset.erase c) := by
    rw [Finset.insert_erase hcmem]
    exact ae_iff.2 (measure_mono_null (fun x hx hxs => hx (hfin.mem_toFinset.2 hxs))
      (spectralMeasure_compl_spectrum_eq_zero _ _))
  exact MatchesMoments.eq_radauQuadrature hmom hμ hc hsupp hcard

/-- **The Radau quadrature of a quadratic form from the modified tridiagonal**: for Hermitian
$\mathbf{A}$ with spectrum in $[a, a']$, $c \in \{a, a'\}$, $q + 1$ at most the grade of
$\mathbf{b}$, and every $f : \mathbb{R} \to \mathbb{R}$,
$$\int f\,d\,\mathsf{radauQuadrature}(\mu_{\mathbf{A},\mathbf{b}}, c, q) =
\|\mathbf{b}\|^2 f(\tilde{\mathbf{J}})_{0,0}\,,$$
$\tilde{\mathbf{J}}$ the Radau Jacobi matrix of order $q + 1$ of $\mu_{\mathbf{A},\mathbf{b}}$:
the Lanczos tridiagonal of order $q + 1$ (`Matrix.IsHermitian.lanczosTridiagonal_eq_jacobiMatrix`)
with its last diagonal entry replaced. [GolubMeurant2010, §6.2.2, Theorem 6.6]. -/
theorem _root_.Matrix.IsHermitian.integral_radauQuadrature_spectralMeasure {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' c : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (hc : c = a ∨ c = a')
    (b : n → 𝕜) {q : ℕ} (hq : q + 1 ≤ krylovGrade A b) (f : ℝ → ℝ) :
    ∫ x, f x ∂radauQuadrature (spectralMeasure A b) c q =
      ‖WithLp.toLp 2 b‖ ^ 2 * cfc f (radauJacobiMatrix (spectralMeasure A b) c q) 0 0 := by
  have hmom : IsMomentPosDef (spectralMeasure A b) (q + 1) :=
    (hA.isMomentPosDef_spectralMeasure_iff b (q + 1)).mpr hq
  have hrad := spectralMeasure_radauJacobiMatrix (spectralMeasure A b) (a := a) (b := a')
    (ae_mem_Icc_spectralMeasure A hs b) hc hmom
  rw [← hrad, integral_spectralMeasure, quadForm_def, hA.spectralMeasure_real_univ b,
    Real.sqrt_sq (norm_nonneg _), RCLike.re_to_real]
  simp only [star_trivial, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    Matrix.mulVec_single_one, smul_eq_mul, single_dotProduct, Matrix.col_apply]
  ring

end NLAlib
