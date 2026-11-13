/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Topology.UniformSpace.UniformApproximation
public import NLAlib.Krylov.Basic.Compression
public import NLAlib.Krylov.LinearSystems.CGLanczos
public import NLAlib.Polynomial.Approximation.AnalyticApproximation
public import NLAlib.Polynomial.Approximation.Jackson
public import NLAlib.Polynomial.Approximation.MinimaxError

/-!
# The Lanczos method for matrix functions

Lanczos-FA is defined mathematically, with no algorithm. The compressed function of
$\mathbf{A}$ on the column space of $\mathbf{X}$ is
$\mathsf{compressedCfc}(\mathbf{A}, f, \mathbf{X}) =
\mathbf{P}f(\mathbf{P}\mathbf{A}\mathbf{P})\mathbf{P}$ with $\mathbf{P} = \mathbf{P}_{\mathbf{X}}$;
it depends on the subspace only and equals
$\mathbf{Q}f(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})\mathbf{Q}^{\mathsf{H}}$ for every
orthonormal basis $\mathbf{Q}$ of it. The function of the zero-padded compression
$\mathbf{P}\mathbf{A}\mathbf{P}$ is well defined for every $f$ because a matrix spectrum is
finite; the outer projectors remove the value $f(0)$ that the padding contributes. The
Lanczos-FA approximation to $f(\mathbf{A})\mathbf{b}$ is the case of a Krylov space,
$\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q) =
\mathsf{compressedCfc}(\mathbf{A}, f, \mathbf{K}_q(\mathbf{A}, \mathbf{b}))\,\mathbf{b}$.

It is exact on polynomials of degree less than $q$, equals the interpolant of $f$ at the Ritz
values applied to $\mathbf{b}$, is within $2\varepsilon\|\mathbf{b}\|$ of $f(\mathbf{A})\mathbf{b}$
when $f$ is $\varepsilon$-close to a polynomial of degree less than $q$ on an interval
containing the spectrum, is CG for $f(x) = x^{-1}$ and CG on $\mathbf{A} + s\mathbf{I}$ for
$f(x) = (x + s)^{-1}$, and is computed from the Lanczos recurrence as
$\|\mathbf{b}\|\,\mathbf{Q}f(\mathbf{T})\mathbf{e}_0$.

Junk value: for non-Hermitian $\mathbf{A}$ the compression is not Hermitian and the definition
returns $\mathbf{0}$ (Mathlib's `cfc` of a non-self-adjoint element); Arnoldi-FA is not covered.

## Main definitions

* `NLAlib.compressedCfc`: $\mathbf{P}f(\mathbf{P}\mathbf{A}\mathbf{P})\mathbf{P}$.
* `NLAlib.lanczosFA`: the Lanczos-FA approximation.

## Main results

* `NLAlib.HasOrthonormalCols.lanczosFA_eq`: the frame form
  $\mathbf{Q}f(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})\mathbf{Q}^{\mathsf{H}}\mathbf{b}$.
* `NLAlib.HasOrthonormalCols.lanczosFA_eq_aeval_mulVec`: interpolation at the Ritz values.
* `Matrix.IsHermitian.lanczosFA_eval`: exactness for degree less than $q$.
* `Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn`: the
  $2\varepsilon\|\mathbf{b}\|$ bound.
* `Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_differentiableOn`,
  `Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_lipschitzOnWith`: explicit rates for
  analytic and for Lipschitz functions.
* `Matrix.IsHermitian.lanczosFA_inv_eq_cgIterate`,
  `Matrix.IsHermitian.lanczosFA_inv_add_eq_cgIterate`: CG and shifted CG.
* `Matrix.IsHermitian.lanczosFA_eq_cfc_mulVec_of_krylovGrade_le`: exact past the grade.
* `Matrix.IsHermitian.lanczosFA_eq_lanczosMatrix`: the Lanczos recurrence computes it.
* `Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_continuousOn`: the bound
  $2E_q(f)\|\mathbf{b}\|$ after $q + 1$ steps.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder NNReal
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p r : Type*} [Fintype n] [DecidableEq n] [Fintype p]
  [Fintype r] [DecidableEq r]

/-! ### The compressed functional calculus -/

/-- The **compressed function** of $\mathbf{A}$ on the column space of $\mathbf{X}$:
$\mathsf{compressedCfc}(\mathbf{A}, f, \mathbf{X}) :=
\mathbf{P}f(\mathbf{P}\mathbf{A}\mathbf{P})\mathbf{P}$, $\mathbf{P} = \mathbf{P}_{\mathbf{X}}$,
where $f(\cdot)$ is Mathlib's `cfc f`. It depends on $\mathbf{X}$ only through its column space
(`compressedCfc_eq_of_range_eq`) and equals
$\mathbf{Q}f(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})\mathbf{Q}^{\mathsf{H}}$ for every
$\mathbf{Q}$ with orthonormal columns spanning it (`HasOrthonormalCols.compressedCfc_eq`).
For $f(x) = x^{-1}$ it is `galerkinInverse A X`. Junk value: $\mathbf{0}$ when the compression
is not Hermitian (in particular for most non-Hermitian $\mathbf{A}$).
[Saad1992, §2]; [ChenPersson2026, (1)]. -/
noncomputable def compressedCfc (A : Matrix n n 𝕜) (f : ℝ → ℝ) (X : Matrix n p 𝕜) :
    Matrix n n 𝕜 :=
  rangeProjector X * cfc f (rangeProjector X * A * rangeProjector X) * rangeProjector X

omit [DecidableEq r] in
/-- The compressed function $\mathsf{compressedCfc}(\mathbf{A}, f, \mathbf{X})$ depends only on
the column space. -/
theorem compressedCfc_eq_of_range_eq (A : Matrix n n 𝕜) (f : ℝ → ℝ) {X : Matrix n p 𝕜}
    {Y : Matrix n r 𝕜} (h : LinearMap.range X.mulVecLin = LinearMap.range Y.mulVecLin) :
    compressedCfc A f X = compressedCfc A f Y := by
  rw [compressedCfc, compressedCfc, rangeProjector_inj.mpr h]

/-- The compressed function in a partial isometry, for every $\mathbf{A}$: for $\mathbf{Q}$
with $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{Q}$ (orthonormal columns, possibly
with some zero columns, as `arnoldiMatrix` past the grade) spanning the column space of
$\mathbf{X}$,
$\mathsf{compressedCfc}(\mathbf{A}, f, \mathbf{X}) =
\mathbf{Q}f(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})\mathbf{Q}^{\mathsf{H}}$. When
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ is not Hermitian, neither is the padded
compression, and both sides are $\mathbf{0}$. -/
theorem compressedCfc_eq_of_mul_conjTranspose_mul_self {Q : Matrix n r 𝕜}
    (hQ : Q * Qᴴ * Q = Q) {X : Matrix n p 𝕜}
    (h : LinearMap.range Q.mulVecLin = LinearMap.range X.mulVecLin) (A : Matrix n n 𝕜)
    (f : ℝ → ℝ) : compressedCfc A f X = Q * cfc f (Qᴴ * A * Q) * Qᴴ := by
  set T := Qᴴ * A * Q with hT
  have hP : rangeProjector X = Q * Qᴴ := by
    rw [← rangeProjector_inj.mpr h,
      rangeProjector_eq_mul_conjTranspose_of_mul_conjTranspose_mul_self hQ]
  have hQ' : Qᴴ * Q * Qᴴ = Qᴴ := by
    have h' := congrArg Matrix.conjTranspose hQ
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc] at h'
  have hQa : Q * (Qᴴ * Q) = Q := by rw [← Matrix.mul_assoc, hQ]
  have hPAP : rangeProjector X * A * rangeProjector X = Q * T * Qᴴ := by
    rw [hP, hT]
    simp only [Matrix.mul_assoc]
  have hTE : Qᴴ * (Q * T * Qᴴ) * Q = T := by
    calc Qᴴ * (Q * T * Qᴴ) * Q = (Qᴴ * Q * Qᴴ) * A * (Q * Qᴴ * Q) := by
          simp only [hT, Matrix.mul_assoc]
      _ = T := by rw [hQ, hQ']
  by_cases hTh : T.IsHermitian
  · have hM : (Q * T * Qᴴ).IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose Q hTh
    have hint : Q * T * Qᴴ * Q = Q * T := by
      simp only [hT, Matrix.mul_assoc, hQa]
    obtain ⟨p, hp₁, hp₂⟩ := exists_eval_eq_of_mem_spectrum (Q * T * Qᴴ) T f
    rw [compressedCfc, hPAP, hM.cfc_eq_aeval_of_forall_eval_eq hp₁,
      hTh.cfc_eq_aeval_of_forall_eval_eq hp₂, hP,
      show Q * Qᴴ * aeval (Q * T * Qᴴ) p * (Q * Qᴴ) =
        Q * Qᴴ * (aeval (Q * T * Qᴴ) p * Q) * Qᴴ by simp only [Matrix.mul_assoc],
      aeval_mul_eq_mul_aeval_of_mul_eq_mul hint p, ← Matrix.mul_assoc (Q * Qᴴ), hQ]
  · have hM : ¬ IsSelfAdjoint (Q * T * Qᴴ) := fun hM =>
      hTh (hTE ▸ Matrix.isHermitian_conjTranspose_mul_mul Q hM)
    have hTh' : ¬ IsSelfAdjoint T := hTh
    rw [compressedCfc, hPAP, cfc_apply_of_not_predicate _ hM, cfc_apply_of_not_predicate _ hTh',
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_mul]

/-- **Frame form of the compressed function**, for every $\mathbf{A}$: for $\mathbf{Q}$ with
orthonormal columns spanning the column space of $\mathbf{X}$,
$\mathsf{compressedCfc}(\mathbf{A}, f, \mathbf{X}) =
\mathbf{Q}f(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})\mathbf{Q}^{\mathsf{H}}$; when
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ is not Hermitian both sides are $\mathbf{0}$.
No printed source: the projector form of `compressedCfc` is the library's definition, and this
bridge identifies it with the frame form in which the literature writes Lanczos-FA.
Result: lanczos-fa-formula -/
theorem HasOrthonormalCols.compressedCfc_eq {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {X : Matrix n p 𝕜} (h : LinearMap.range Q.mulVecLin = LinearMap.range X.mulVecLin)
    (A : Matrix n n 𝕜) (f : ℝ → ℝ) :
    compressedCfc A f X = Q * cfc f (Qᴴ * A * Q) * Qᴴ :=
  compressedCfc_eq_of_mul_conjTranspose_mul_self hQ.mul_conjTranspose_mul_self h A f

/-- **The compressed inverse is the Galerkin inverse**, for Hermitian $\mathbf{A}$:
$\mathsf{compressedCfc}(\mathbf{A}, x \mapsto x^{-1}, \mathbf{X}) =
\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{X})$, through
`Matrix.IsHermitian.cfc_inv_eq_pinv` on the compression to an orthonormal basis.
No printed source: a bridge between two of the library's definitions.
Result: lanczos-fa-cg -/
theorem _root_.Matrix.IsHermitian.compressedCfc_inv_eq_galerkinInverse {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (X : Matrix n p 𝕜) :
    compressedCfc A (fun x => x⁻¹) X = galerkinInverse A X := by
  obtain ⟨Q, hQ, hQX⟩ :=
    exists_hasOrthonormalCols_range_eq (p := Fin X.rank) X (Fintype.card_fin _)
  rw [hQ.compressedCfc_eq hQX, (Matrix.isHermitian_conjTranspose_mul_mul Q hA).cfc_inv_eq_pinv,
    hQ.galerkinInverse_eq hQX]

/-! ### Lanczos-FA -/

/-- The **Lanczos-FA approximation** to $f(\mathbf{A})\mathbf{b}$ after $q$ steps:
$\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q) :=
\mathsf{compressedCfc}(\mathbf{A}, f, \mathbf{K}_q(\mathbf{A}, \mathbf{b}))\,\mathbf{b}$, which is
$\mathbf{Q}f(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})\mathbf{Q}^{\mathsf{H}}\mathbf{b}$ for
every orthonormal basis $\mathbf{Q}$ of $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$
(`HasOrthonormalCols.lanczosFA_eq`). Basis-free, total and not an algorithm; the Lanczos
recurrence computes it (`Matrix.IsHermitian.lanczosFA_eq_lanczosMatrix`). Junk values: $q = 0$
gives $\mathbf{0}$; non-Hermitian $\mathbf{A}$ gives $\mathbf{0}$ (see `compressedCfc`).
[Saad1992, §2]; [ChenPersson2026, (1)]. -/
noncomputable def lanczosFA (A : Matrix n n 𝕜) (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  compressedCfc A f (krylovMatrix A b q) *ᵥ b

/-- The approximation $\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)$ lies in the Krylov
space. -/
theorem lanczosFA_mem_krylovSpace (A : Matrix n n 𝕜) (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    lanczosFA A f b q ∈ krylovSpace A b q := by
  rw [krylovSpace, ← range_rangeProjector]
  refine ⟨(cfc f (rangeProjector (krylovMatrix A b q) * A * rangeProjector (krylovMatrix A b q)) *
    rangeProjector (krylovMatrix A b q)) *ᵥ b, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
  rfl

/-- No steps, no approximation: $\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, 0) = \mathbf{0}$. -/
@[simp]
theorem lanczosFA_zero (A : Matrix n n 𝕜) (f : ℝ → ℝ) (b : n → 𝕜) : lanczosFA A f b 0 = 0 := by
  have h := lanczosFA_mem_krylovSpace A f b 0
  rwa [krylovSpace_zero, Submodule.mem_bot] at h

/-- **Lanczos-FA in any orthonormal basis of the Krylov space**, for every $\mathbf{A}$:
$\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q) =
\mathbf{Q}f(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})\mathbf{Q}^{\mathsf{H}}\mathbf{b}$.
[Saad1992, §2]; [ChenPersson2026, (1)].
Result: lanczos-fa-formula -/
theorem HasOrthonormalCols.lanczosFA_eq {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (f : ℝ → ℝ) :
    lanczosFA A f b q = Q *ᵥ (cfc f (Qᴴ * A * Q) *ᵥ (Qᴴ *ᵥ b)) := by
  rw [lanczosFA, hQ.compressedCfc_eq hK A f, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/-- **Lanczos-FA is interpolation at the Ritz values**: for Hermitian $\mathbf{A}$, a frame
$\mathbf{Q}$ of $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$ and a real polynomial $p$ of degree
less than $q$ that agrees with $f$ on the spectrum of
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$,
$\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q) = p(\mathbf{A})\mathbf{b}$. The Lagrange
interpolant at the Ritz values is such a $p$.
[ChenPersson2026, (9)].
Result: lanczos-fa-interpolation -/
theorem HasOrthonormalCols.lanczosFA_eq_aeval_mulVec {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) {f : ℝ → ℝ} {p : ℝ[X]}
    (hp : p.degree < q) (hf : ∀ x ∈ spectrum ℝ (Qᴴ * A * Q), p.eval x = f x) :
    lanczosFA A f b q = aeval A p *ᵥ b := by
  rw [hQ.lanczosFA_eq hK f,
    (Matrix.isHermitian_conjTranspose_mul_mul Q hA).cfc_eq_aeval_of_forall_eval_eq hf]
  exact hQ.mulVec_aeval_conjTranspose_mul_mul_mulVec_eq hK hp

/-- **Exactness**: for Hermitian $\mathbf{A}$ and a real polynomial of degree less than $q$,
$\mathsf{lanczosFA}(\mathbf{A}, p, \mathbf{b}, q) = p(\mathbf{A})\mathbf{b}$.
[Saad1992, Lemma 3.1].
Result: lanczos-fa-exactness -/
theorem _root_.Matrix.IsHermitian.lanczosFA_eval {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (b : n → 𝕜) {q : ℕ} {p : ℝ[X]} (hp : p.degree < q) :
    lanczosFA A (fun x => p.eval x) b q = aeval A p *ᵥ b := by
  obtain ⟨k, Q, hQ, hK⟩ := exists_hasOrthonormalCols_range_eq_krylovSpace A b q
  exact hQ.lanczosFA_eq_aeval_mulVec hA hK hp fun _ _ => rfl

/-- Lanczos-FA sees $f$ only on an interval containing the spectrum: if $f = g$ on $[a, a']$
and the spectrum of Hermitian $\mathbf{A}$ lies in $[a, a']$, the approximations
$\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)$ and
$\mathsf{lanczosFA}(\mathbf{A}, g, \mathbf{b}, q)$ agree, since the Ritz values lie in $[a, a']$
(`Matrix.IsHermitian.spectrum_conjTranspose_mul_mul_subset_Icc`). -/
theorem _root_.Matrix.IsHermitian.lanczosFA_congr {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') {f g : ℝ → ℝ}
    (h : ∀ x ∈ Set.Icc a a', f x = g x) (b : n → 𝕜) (q : ℕ) :
    lanczosFA A f b q = lanczosFA A g b q := by
  obtain ⟨k, Q, hQ, hK⟩ := exists_hasOrthonormalCols_range_eq_krylovSpace A b q
  have hsT := hA.spectrum_conjTranspose_mul_mul_subset_Icc hs hQ
  rw [hQ.lanczosFA_eq hK, hQ.lanczosFA_eq hK, cfc_congr fun x hx => h x (hsT hx)]

/-- Lanczos-FA is linear in the function, for every $\mathbf{A}$:
$\mathsf{lanczosFA}(\mathbf{A}, f - g, \mathbf{b}, q) =
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q) -
\mathsf{lanczosFA}(\mathbf{A}, g, \mathbf{b}, q)$.
No continuity is needed: matrix spectra are finite. -/
theorem lanczosFA_sub (A : Matrix n n 𝕜) (f g : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    lanczosFA A (fun x => f x - g x) b q = lanczosFA A f b q - lanczosFA A g b q := by
  set M := rangeProjector (krylovMatrix A b q) * A * rangeProjector (krylovMatrix A b q)
  rw [lanczosFA, lanczosFA, lanczosFA, compressedCfc, compressedCfc, compressedCfc,
    cfc_sub f g M (M.finite_real_spectrum.continuousOn _) (M.finite_real_spectrum.continuousOn _),
    Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mulVec]

/-- **Lanczos-FA is exact past the grade**: for Hermitian $\mathbf{A}$ and
$\nu \le q$, $\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q) = f(\mathbf{A})\mathbf{b}$, since
the Krylov space is then invariant. [Saad1992, §3.2].
Result: lanczos-fa-exactness -/
theorem _root_.Matrix.IsHermitian.lanczosFA_eq_cfc_mulVec_of_krylovGrade_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) {b : n → 𝕜} {q : ℕ} (h : krylovGrade A b ≤ q) :
    lanczosFA A f b q = cfc f A *ᵥ b := by
  obtain ⟨k, Q, hQ, hK⟩ := exists_hasOrthonormalCols_range_eq_krylovSpace A b q
  have hT := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  -- the Krylov space is invariant: $\mathbf{A}\mathbf{Q} = \mathbf{Q}\mathbf{T}$
  have hAQ : A * Q = Q * (Qᴴ * A * Q) := by
    have hle : LinearMap.range (A * Q).mulVecLin ≤ LinearMap.range Q.mulVecLin := by
      rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, hK]
      exact mulVec_mem_krylovSpace_of_krylovGrade_le h (hK ▸ ⟨c, rfl⟩)
    have h' := rangeProjector_mul_eq_self_iff.mpr hle
    rw [hQ.rangeProjector_eq] at h'
    rw [← h']
    simp only [Matrix.mul_assoc]
  have hb : Q *ᵥ (Qᴴ *ᵥ b) = b := by
    have hmem : b ∈ LinearMap.range Q.mulVecLin := by
      rw [hK, krylovSpace_eq_of_krylovGrade_le h,
        ← krylovSpace_eq_of_krylovGrade_le (h.trans q.le_succ)]
      exact self_mem_krylovSpace A b q.succ_pos
    obtain ⟨y, hy⟩ := hmem
    rw [← hy, Matrix.mulVecLin_apply, hQ.conjTranspose_mulVec_mulVec]
  obtain ⟨p, hp₁, hp₂⟩ := exists_eval_eq_of_mem_spectrum A (Qᴴ * A * Q) f
  rw [hQ.lanczosFA_eq hK, hT.cfc_eq_aeval_of_forall_eval_eq hp₂,
    hA.cfc_eq_aeval_of_forall_eval_eq hp₁, Matrix.mulVec_mulVec,
    ← aeval_mul_eq_mul_aeval_of_mul_eq_mul hAQ p, ← Matrix.mulVec_mulVec, hb]

/-- **The uniform approximation bound**: for Hermitian $\mathbf{A}$ with spectrum in
$[a, a']$, if a real polynomial $p$ of degree less than $q$ is within $\varepsilon$ of $f$ on
$[a, a']$, then
$\|f(\mathbf{A})\mathbf{b} - \mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)\| \le
2\varepsilon\|\mathbf{b}\|$: Lanczos-FA is exact on $p$, and $f - p$ is at most $\varepsilon$
on the spectrum of $\mathbf{A}$ and on the Ritz values. [ChenPersson2026, (2)]; [Saad1992, §3].
Result: lanczos-fa-uniform-bound -/
theorem _root_.Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {f : ℝ → ℝ} {q : ℕ} {p : ℝ[X]} (hp : p.degree < q) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε) (b : n → 𝕜) :
    ‖WithLp.toLp 2 (cfc f A *ᵥ b - lanczosFA A f b q)‖ ≤ 2 * ε * ‖WithLp.toLp 2 b‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 : ∀ v : n → 𝕜, ‖WithLp.toLp 2 v‖ = 0 := fun v => by
      rw [Subsingleton.elim v 0, WithLp.toLp_zero, norm_zero]
    rw [h0, h0, mul_zero]
  set g : ℝ → ℝ := fun x => f x - p.eval x
  have hε0 : 0 ≤ ε := hε.nonneg ⟨_, hs (hA.eigenvalue_mem_spectrum Fintype.card_pos)⟩
  have hg : ∀ x ∈ Set.Icc a a', |g x| ≤ ε := fun x hx => by
    have h := hε.apply hx
    rwa [Real.dist_eq, abs_sub_comm] at h
  -- the error is that of $g = f - p$, since Lanczos-FA is exact on $p$
  have heq : cfc f A *ᵥ b - lanczosFA A f b q = cfc g A *ᵥ b - lanczosFA A g b q := by
    rw [lanczosFA_sub A f (fun x => p.eval x) b q, hA.lanczosFA_eval b hp,
      cfc_sub f (fun x => p.eval x) A (A.finite_real_spectrum.continuousOn _)
        (A.finite_real_spectrum.continuousOn _),
      hA.cfc_eq_aeval_of_forall_eval_eq (f := fun x => p.eval x) fun _ _ => rfl,
      Matrix.sub_mulVec]
    abel
  obtain ⟨k, Q, hQ, hK⟩ := exists_hasOrthonormalCols_range_eq_krylovSpace A b q
  have hT := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  have hsT := hA.spectrum_conjTranspose_mul_mul_subset_Icc hs hQ
  have h₁ : ‖WithLp.toLp 2 (cfc g A *ᵥ b)‖ ≤ ε * ‖WithLp.toLp 2 b‖ :=
    (norm_toLp_mulVec_le _ b).trans (mul_le_mul_of_nonneg_right
      (hA.specNorm_cfc_le hε0 fun x hx => hg x (hs hx)) (norm_nonneg _))
  have h₂ : ‖WithLp.toLp 2 (lanczosFA A g b q)‖ ≤ ε * ‖WithLp.toLp 2 b‖ := by
    rw [hQ.lanczosFA_eq hK g, hQ.norm_toLp_mulVec]
    exact (norm_toLp_mulVec_le _ _).trans (mul_le_mul
      (hT.specNorm_cfc_le hε0 fun x hx => hg x (hsT hx))
      (hQ.norm_toLp_conjTranspose_mulVec_le b) (norm_nonneg _) hε0)
  rw [heq, WithLp.toLp_sub]
  calc _ ≤ ‖WithLp.toLp 2 (cfc g A *ᵥ b)‖ + ‖WithLp.toLp 2 (lanczosFA A g b q)‖ :=
        norm_sub_le _ _
    _ ≤ ε * ‖WithLp.toLp 2 b‖ + ε * ‖WithLp.toLp 2 b‖ := add_le_add h₁ h₂
    _ = 2 * ε * ‖WithLp.toLp 2 b‖ := by ring

/-- **CG is Lanczos-FA for the inverse**, for every Hermitian $\mathbf{A}$:
$\mathsf{lanczosFA}(\mathbf{A}, x \mapsto x^{-1}, \mathbf{b}, q) =
\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{0}, q)$ (CG from the zero start), with
Lean's $0^{-1} = 0$ matching the
pseudoinverse junk value of `galerkinInverse`. [ChenPersson2026, §1.1]; [Saad2003, §6.7].
Result: lanczos-fa-cg -/
theorem _root_.Matrix.IsHermitian.lanczosFA_inv_eq_cgIterate {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) :
    lanczosFA A (fun x => x⁻¹) b q = cgIterate A b 0 q := by
  rw [cgIterate, Matrix.mulVec_zero, sub_zero, zero_add, lanczosFA,
    hA.compressedCfc_inv_eq_galerkinInverse]

/-- **Shifted CG is Lanczos-FA for a shifted inverse**, for Hermitian $\mathbf{A}$ and real
$s$: $\mathsf{lanczosFA}(\mathbf{A}, x \mapsto (x + s)^{-1}, \mathbf{b}, q) =
\mathsf{cgIterate}(\mathbf{A} + s\mathbf{I}, \mathbf{b}, \mathbf{0}, q)$, by shift
invariance of the Krylov space (`krylovSpace_add_smul_one`) and the frame forms.
[Saad2003, §6.7.1]; (6.86) there writes the CG iterate as
$\mathbf{x}_0 + \mathbf{V}_m\mathbf{T}_m^{-1}(\beta\mathbf{e}_1)$ with the Lanczos basis
$\mathbf{V}_m$, $\beta = \|\mathbf{r}_0\|$, which at $\mathbf{x}_0 = \mathbf{0}$ is the Lanczos-FA
approximation for $f(x) = x^{-1}$; the shift $s$ and the singular case are the library's.
Result: lanczos-fa-cg -/
theorem _root_.Matrix.IsHermitian.lanczosFA_inv_add_eq_cgIterate {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (s : ℝ) (b : n → 𝕜) (q : ℕ) :
    lanczosFA A (fun x => (x + s)⁻¹) b q = cgIterate (A + s • (1 : Matrix n n 𝕜)) b 0 q := by
  obtain ⟨k, Q, hQ, hK⟩ := exists_hasOrthonormalCols_range_eq_krylovSpace A b q
  have hK' : LinearMap.range Q.mulVecLin =
      krylovSpace (A + s • (1 : Matrix n n 𝕜)) (b - (A + s • (1 : Matrix n n 𝕜)) *ᵥ 0) q := by
    rw [Matrix.mulVec_zero, sub_zero, krylovSpace_add_smul_one, hK]
  set T := Qᴴ * A * Q
  have hT : IsSelfAdjoint T := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  have hTs : Qᴴ * (A + s • (1 : Matrix n n 𝕜)) * Q = T + s • 1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hQ.conjTranspose_mul_self]
  have hadd : cfc (fun x : ℝ => x + s) T = T + s • 1 := by
    have h₁ : cfc (fun x : ℝ => x + s) T = cfc (fun x : ℝ => x) T + algebraMap ℝ _ s :=
      cfc_add_const s (fun x : ℝ => x) T (T.finite_real_spectrum.continuousOn _) hT
    rw [h₁, cfc_id' ℝ T hT, Algebra.algebraMap_eq_smul_one]
  have hHs : (T + s • (1 : Matrix (Fin k) (Fin k) 𝕜)).IsHermitian :=
    hadd ▸ cfc_predicate _ T
  have hcomp : cfc (fun x : ℝ => (x + s)⁻¹) T = cfc (fun x : ℝ => x⁻¹) (cfc (fun x => x + s) T) :=
    cfc_comp' (fun x : ℝ => x⁻¹) (fun x => x + s) T
      ((T.finite_real_spectrum.image _).continuousOn _) (T.finite_real_spectrum.continuousOn _) hT
  rw [hQ.lanczosFA_eq hK, hQ.cgIterate_eq hK', Matrix.mulVec_zero, sub_zero, zero_add, hTs, hcomp,
    hadd, hHs.cfc_inv_eq_pinv]

/-- **The Lanczos basis yields Lanczos-FA**, for every $\mathbf{A}$ and every $q$: with
$\mathbf{Q} = \mathsf{arnoldiMatrix}(\mathbf{A}, \mathbf{b}, q + 1)$ the canonical basis of
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{b})$ (zero columns past the grade) and
$\mathbf{T} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$,
$\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q + 1) =
\|\mathbf{b}\|\,\mathbf{Q}f(\mathbf{T})\mathbf{e}_0$, by the partial-isometry form
`compressedCfc_eq_of_mul_conjTranspose_mul_self` and
$\mathbf{Q}^{\mathsf{H}}\mathbf{b} = \|\mathbf{b}\|\mathbf{e}_0$
(`conjTranspose_arnoldiMatrix_mulVec_self`). [Saad1992, §2].
Result: lanczos-fa-recurrence -/
theorem lanczosFA_eq_arnoldiMatrix (A : Matrix n n 𝕜) (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    lanczosFA A f b (q + 1) = (‖WithLp.toLp 2 b‖ : 𝕜) • (arnoldiMatrix A b (q + 1) *ᵥ
      (cfc f ((arnoldiMatrix A b (q + 1))ᴴ * A * arnoldiMatrix A b (q + 1)) *ᵥ
        Pi.single 0 1)) := by
  have hQ : arnoldiMatrix A b (q + 1) * (arnoldiMatrix A b (q + 1))ᴴ *
      arnoldiMatrix A b (q + 1) = arnoldiMatrix A b (q + 1) := by
    rw [Matrix.mul_assoc]
    exact gramSchmidtQ_mul_conjTranspose_gramSchmidtQ_mul_self _
  rw [lanczosFA,
    compressedCfc_eq_of_mul_conjTranspose_mul_self hQ (range_arnoldiMatrix A b (q + 1)) A f,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, conjTranspose_arnoldiMatrix_mulVec_self,
    Matrix.mulVec_smul, Matrix.mulVec_smul]

/-- **The Lanczos recurrence computes Lanczos-FA**, for Hermitian $\mathbf{A}$ and every $q$:
$\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q + 1) =
\|\mathbf{b}\|\,\mathbf{Q}f(\mathbf{T})\mathbf{e}_0$ with $\mathbf{Q}$ and $\mathbf{T}$ from
$q + 1$ steps of the recurrence. [Saad1992, §2].
Result: lanczos-fa-recurrence -/
theorem _root_.Matrix.IsHermitian.lanczosFA_eq_lanczosMatrix {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    lanczosFA A f b (q + 1) = (‖WithLp.toLp 2 b‖ : 𝕜) • (lanczosMatrix A b (q + 1) *ᵥ
      (cfc f (lanczosTridiagonal A b (q + 1)) *ᵥ Pi.single 0 1)) := by
  rw [hA.lanczosMatrix_eq_arnoldiMatrix, hA.lanczosTridiagonal_eq, lanczosFA_eq_arnoldiMatrix]

/-! ### Explicit rates -/

/-- **Lanczos-FA for analytic functions**: let $\mathbf{A}$ be Hermitian with spectrum in
$[a, a']$, $a < a'$, and let $f$ on $[a, a']$, pulled back to $[-1, 1]$ by
$t \mapsto ((a' - a)t + a' + a)/2$, extend to a function holomorphic and bounded by $M$ on the
open Bernstein ellipse $E_\rho$, $\rho > 1$. Then $q + 1$ steps give
$$\|f(\mathbf{A})\mathbf{b} - \mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q + 1)\| \le
\frac{4M}{\rho^q(\rho - 1)}\|\mathbf{b}\|\,,$$
from the uniform bound and the Chebyshev truncation of degree $q$.
[Trefethen2019, Theorem 8.2, Eq. (8.2)], the
approximation rate; constants composed here.
Result: lanczos-fa-uniform-bound -/
theorem _root_.Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_differentiableOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => ((f (((a' - a) * t + a' + a) / 2) : ℝ) : ℂ))
      (fun t : ℝ => F t) (Set.Icc (-1 : ℝ) 1))
    (b : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      4 * M / (ρ ^ q * (ρ - 1)) * ‖WithLp.toLp 2 b‖ := by
  obtain ⟨p, hp, hε⟩ := exists_degree_le_isUniformApproxOn_Icc_of_differentiableOn (𝕜 := ℝ)
    (f := f) haa hρ hFd hM (fun t ht => by
      rw [← hExt ht]
      exact RCLike.toComplex_ofReal (𝕜 := ℝ) _) q
  have hp' : p.degree < ((q + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast Nat.lt_succ_self q)
  have h := hA.norm_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hs hp' hε b
  refine h.trans_eq ?_
  ring

/-- **Lanczos-FA for Lipschitz functions**: for Hermitian $\mathbf{A}$ with spectrum in
$[a, a']$, $a < a'$, and $f$ $L$-Lipschitz on $[a, a']$, $q + 1$ steps
give <!-- value jacksonApproximationConstant -->
$$\|f(\mathbf{A})\mathbf{b} - \mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q + 1)\| \le
\frac{\pi L(a' - a)}{q + 2}\|\mathbf{b}\|\,,$$
from the uniform bound and Jackson's theorem on $[a, a']$ in degree $q$ (the constant is
`jacksonApproximationConstant`). No printed source for this composition; the approximation step
is [ChenTrogdonUbaru2022, Appendix C, Theorem 38].
Result: lanczos-fa-uniform-bound -/
theorem _root_.Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_lipschitzOnWith
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a a')) (b : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      jacksonApproximationConstant * L * (a' - a) / (q + 2) * ‖WithLp.toLp 2 b‖ := by
  obtain ⟨p, hp, hε⟩ :=
    exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith (𝕜 := ℝ) haa hf q
  have hp' : p.degree < ((q + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast Nat.lt_succ_self q)
  have h := hA.norm_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hs hp' hε b
  refine h.trans_eq ?_
  field_simp

/-- **Lanczos-FA and the minimax error**: for Hermitian $\mathbf{A}$ with spectrum in $[a, a']$
and $f$ continuous on $[a, a']$, $q + 1$ steps of Lanczos-FA satisfy
$$\|f(\mathbf{A})\mathbf{b} - \mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q + 1)\| \le
2E_q(f; [a, a'])\|\mathbf{b}\|\,,$$
$E_q$ the error of the best uniform approximation of $f$ on $[a, a']$ by polynomials of degree
at most $q$ (`minimaxError`). [ChenPersson2026, (2)]; [Saad1992, §3]; there with $E_q$.
Result: lanczos-fa-uniform-bound -/
theorem _root_.Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_continuousOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) (b : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      2 * minimaxError f (Set.Icc a a') q * ‖WithLp.toLp 2 b‖ := by
  obtain ⟨p, hp, hε⟩ := exists_degree_le_isUniformApproxOn_minimaxError isCompact_Icc hf q
  exact hA.norm_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hs
    (hp.trans_lt (by exact_mod_cast Nat.lt_succ_self q)) hε b

end NLAlib
