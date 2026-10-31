/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.BackwardSpectral
public import NLAlib.Krylov.Functions.Quadrature
public import NLAlib.Polynomial.Approximation.Jackson
public import NLAlib.Polynomial.Chebyshev.Interval

/-!
# Finite-precision Lanczos quadrature and Lanczos-FA: Druskin–Knizhnerman and Knizhnerman bounds

The polynomial facts (Chebyshev polynomials on an interval, bounded Chebyshev coefficients) are in
`NLAlib/Polynomial/Chebyshev/Interval.lean`. For a finite-precision Lanczos run
`L : NLAlib.LanczosRun n k` on a symmetric $\mathbf{H}$ with spectrum in $[a, a']$, write
$I_c = [a - c, a' + c]$ with <!-- value lanczosBackwardFactor k -->
$c = 2000k^4\varepsilon\|\mathbf{H}\|_2$ (`NLAlib.lanczosBackwardFactor`).

* **Quadrature (Knizhnerman 1996 type)**, through the backward model: exact Lanczos on
  $(\tilde{\mathbf{H}}, \tilde{\mathbf{v}})$ computes $\mathbf{T}_k$, its Gauss rule is exact to
  degree $2k - 1$, the spectrum of $\tilde{\mathbf{H}}$ lies in $I_c$, and the quadratic forms of
  $(\mathbf{H}, \bar{\mathbf{v}}_1)$ and $(\tilde{\mathbf{H}}, \tilde{\mathbf{v}})$ differ by at
  most $L c$ for $L$-Lipschitz $f$ (Kittaneh). Hence
  $$\lvert\bar{\mathbf{v}}_1^{\mathsf{T}}f(\mathbf{H})\bar{\mathbf{v}}_1 -
  (f(\mathbf{T}_k))_{00}\rvert \le 2E_{2k-1}(f; I_c) + L c .$$
* **Lanczos-FA (Druskin–Knizhnerman 1991 type)**, through the stability of the Chebyshev
  recurrence under the computed three-term recurrence (the backward model contributes only the
  containment of the Ritz values in $I_c$):
  $$\|f(\mathbf{H})\mathbf{v}_1 - \mathbf{V}_k f(\mathbf{T}_k)\mathbf{e}_0\| \le
  (2 + \sqrt{k})E_{k-1}(f; I_c) + 16k^{9/2}\varepsilon\|\mathbf{H}\|_2\,
  \frac{\sup_{I_c}\lvert f\rvert}{a' - a + 2c} .$$

The bounds are of the type of [Knizhnerman1996] (quadrature) and [DruskinKnizhnerman1991]
(Lanczos-FA), through [MuscoMuscoSidford2018]; the forms proved here are new.

The generic statements are on `NLAlib.LanczosData` (any symmetric three-term datum), so that
the CG backward model can reuse them.

## Main results

* `NLAlib.LanczosData.cfc_tridiagonal_firstIndex_eq_integral`: $(f(\mathbf{T}_k))_{00}$ is the
  Gauss rule of the backward model.
* `NLAlib.LanczosData.abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_isUniformApproxOn`,
  `NLAlib.LanczosRun.abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_continuousOn`,
  `NLAlib.LanczosRun.abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_lipschitzOnWith`:
  the quadrature bounds.
* `NLAlib.LanczosData.norm_aeval_chebyshevOn_mulVec_sub_basis_mulVec_le`,
  `NLAlib.LanczosData.norm_aeval_mulVec_sub_basis_mulVec_le_of_degree_lt`,
  `NLAlib.LanczosRun.norm_cfc_mulVec_sub_basis_mulVec_le_of_continuousOn`: the Lanczos-FA
  bounds.
-/

@[expose] public section

open Polynomial MeasureTheory
open scoped Matrix NNReal

namespace NLAlib

/-! ### The perturbed Chebyshev recurrence -/

/-- **Bandwidth of powers of a tridiagonal matrix**: $(\mathbf{T}^p)_{ij} = 0$ for
$p + j < i$. -/
private theorem pow_apply_eq_zero_of_add_lt {m : ℕ} {T : Matrix (Fin m) (Fin m) ℝ}
    (hT : IsTridiagonal T) (p : ℕ) {i j : Fin m} (h : p + (j : ℕ) < i) : (T ^ p) i j = 0 := by
  induction p generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_apply_ne]
    exact fun hij => by rw [hij] at h; omega
  | succ p ih =>
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) ≤ j + 1
    · rw [ih (by omega), zero_mul]
    · rw [hT l j (Or.inr (by omega)), mul_zero]

/-- **Bandwidth of polynomials in a tridiagonal matrix**: $(q(\mathbf{T}))_{ij} = 0$ when
$\deg q + j < i$. -/
private theorem aeval_apply_eq_zero_of_natDegree_add_lt {m : ℕ}
    {T : Matrix (Fin m) (Fin m) ℝ} (hT : IsTridiagonal T) {q : ℝ[X]} {i j : Fin m}
    (h : q.natDegree + (j : ℕ) < i) : aeval T q i j = 0 := by
  rw [aeval_eq_sum_range, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [Matrix.smul_apply, pow_apply_eq_zero_of_add_lt hT d
    (by rw [Finset.mem_range] at hd; omega), smul_zero]

/-- The Chebyshev-type step $\mathbf{x} \mapsto 2\mathbf{A}\mathbf{x} - \mathbf{y}$ under
`aeval`. -/
private theorem aeval_two_mul_X_mul_sub_mulVec {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) (p q : ℝ[X]) (v : m → ℝ) :
    aeval A (2 * X * p - q) *ᵥ v = (2 : ℝ) • (A *ᵥ (aeval A p *ᵥ v)) - aeval A q *ᵥ v := by
  rw [map_sub, map_mul, map_mul, aeval_X, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  congr 1
  rw [map_ofNat, Matrix.ofNat_mulVec]

/-- The **residual sequence** of a sequence $\mathbf{d}_j$ for the Chebyshev recurrence of
$\mathbf{A}$: $\mathbf{f}_0 = \mathbf{d}_1$, $\mathbf{f}_{j+1} = \mathbf{d}_{j+2} -
2\mathbf{A}\mathbf{d}_{j+1} + \mathbf{d}_j$. -/
private noncomputable def chebyshevRecurrenceResidual {m : Type*} [Fintype m] (A : Matrix m m ℝ)
    (d : ℕ → m → ℝ) : ℕ → m → ℝ
  | 0 => d 1
  | j + 1 => d (j + 2) - (2 : ℝ) • (A *ᵥ d (j + 1)) + d j

/-- **Solution of the perturbed Chebyshev recurrence** (Clenshaw): a sequence with
$\mathbf{d}_0 = \mathbf{0}$ is
$\mathbf{d}_i = \sum_{j<i}U_{i-1-j}(\mathbf{A})\mathbf{f}_j$ in its residual sequence. -/
private theorem eq_sum_aeval_U_mulVec_chebyshevRecurrenceResidual {m : Type*} [Fintype m]
    [DecidableEq m] (A : Matrix m m ℝ) {d : ℕ → m → ℝ} (hd0 : d 0 = 0) (i : ℕ) :
    d i = ∑ j ∈ Finset.range i,
      aeval A (Chebyshev.U ℝ ((i : ℤ) - 1 - j)) *ᵥ chebyshevRecurrenceResidual A d j := by
  induction i using Nat.twoStepInduction with
  | zero => simp [hd0]
  | one => simp [chebyshevRecurrenceResidual]
  | more i ih0 ih1 =>
    have hU : ∀ j ∈ Finset.range (i + 1),
        aeval A (Chebyshev.U ℝ (((i + 2 : ℕ) : ℤ) - 1 - j)) *ᵥ chebyshevRecurrenceResidual A d j =
          (2 : ℝ) • (A *ᵥ (aeval A (Chebyshev.U ℝ (((i + 1 : ℕ) : ℤ) - 1 - j)) *ᵥ
            chebyshevRecurrenceResidual A d j)) -
          aeval A (Chebyshev.U ℝ ((i : ℤ) - 1 - j)) *ᵥ chebyshevRecurrenceResidual A d j := by
      intro j _
      rw [show ((i + 2 : ℕ) : ℤ) - 1 - j = ((i : ℤ) - 1 - j) + 2 by push_cast; ring,
        Chebyshev.U_add_two, aeval_two_mul_X_mul_sub_mulVec,
        show (i : ℤ) - 1 - j + 1 = ((i + 1 : ℕ) : ℤ) - 1 - j by push_cast; ring]
    have hlast : aeval A (Chebyshev.U ℝ ((i : ℤ) - 1 - (i : ℕ))) *ᵥ
        chebyshevRecurrenceResidual A d i = 0 := by
      rw [show (i : ℤ) - 1 - (i : ℕ) = -1 by ring, Chebyshev.U_neg_one, map_zero,
        Matrix.zero_mulVec]
    rw [Finset.sum_range_succ, Finset.sum_congr rfl hU, Finset.sum_sub_distrib,
      ← Finset.smul_sum, ← Matrix.mulVec_sum, ← ih1, Finset.sum_range_succ, hlast, add_zero,
      ← ih0, show ((i + 2 : ℕ) : ℤ) - 1 - (i + 1 : ℕ) = 0 by push_cast; ring, Chebyshev.U_zero,
      map_one, Matrix.one_mulVec]
    simp only [chebyshevRecurrenceResidual]
    abel

/-- $\sum_{j<i}(i - j) = i(i + 1)/2$. -/
private theorem sum_range_sub_eq (i : ℕ) :
    ∑ j ∈ Finset.range i, ((i : ℝ) - j) = i * (i + 1) / 2 := by
  induction i with
  | zero => simp
  | succ i ih =>
    push_cast
    rw [Finset.sum_range_succ]
    simp only [add_sub_right_comm _ (1 : ℝ), Finset.sum_add_distrib, ih, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    ring

/-- $\sum_{i<k} i(i + 1) \le k^3/3$. -/
private theorem sum_range_mul_succ_le (k : ℕ) :
    ∑ i ∈ Finset.range k, (i : ℝ) * (i + 1) ≤ (k : ℝ) ^ 3 / 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

namespace LanczosData

variable {n k : ℕ} (D : LanczosData n k)

/-- The first index $0 : \mathrm{Fin}\,k$ ($k \ge 1$). -/
def firstIndex : Fin k := ⟨0, D.k_pos⟩

/-- The computed tridiagonal matrix is symmetric. -/
theorem isHermitian_tridiagonal : D.tridiagonal.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, D.transpose_tridiagonal]

/-- The dilated start is a unit vector (for unit vectors). -/
theorem norm_toLp_dilatedStart (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    ‖WithLp.toLp 2 D.dilatedStart‖ = 1 := by
  rw [← D.dilatedBasisSucc_col_zero]
  exact (D.hasOrthonormalCols_dilatedBasisSucc hW).norm_toLp_col 0

/-- **Containment of the Ritz values of a datum**: for unit vectors,
$\operatorname{spec}\mathbf{H} \subseteq [a, a']$ and
$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}} \le c$, the spectrum
of $\mathbf{T}_k$ lies in $[a - c, a' + c]$: $\mathbf{T}_k$ is a compression of
$\tilde{\mathbf{H}}$ to orthonormal columns. -/
theorem spectrum_tridiagonal_subset_Icc (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1)
    {a a' c : ℝ} (hs : spectrum ℝ D.H ⊆ Set.Icc a a')
    (hc : frobNorm (D.backwardH - D.dilatedH) ≤ c) :
    spectrum ℝ D.tridiagonal ⊆ Set.Icc (a - c) (a' + c) := by
  have hT : D.dilatedBasisᴴ * D.backwardH * D.dilatedBasis = D.tridiagonal := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc,
      D.backwardH_mul_dilatedBasis hW, D.transpose_dilatedBasis_mul_dilatedBasisSucc_mul hW]
  rw [← hT]
  exact (D.isHermitian_backwardH hW).spectrum_conjTranspose_mul_mul_subset_Icc
    (D.spectrum_backwardH_subset_Icc hW hs hc) (D.hasOrthonormalCols_dilatedBasis hW)

/-- The Kittaneh transfer for a $K$-Lipschitz function: for unit vectors,
$\lvert\mathbf{v}_1^{\mathsf{T}}g(\mathbf{H})\mathbf{v}_1 -
\tilde{\mathbf{v}}^{\mathsf{T}}g(\tilde{\mathbf{H}})\tilde{\mathbf{v}}\rvert \le
K\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}}$. -/
private theorem abs_dotProduct_cfc_mulVec_sub_le_mul_frobNorm
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) {g : ℝ → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) :
    |D.v 1 ⬝ᵥ (cfc g D.H *ᵥ D.v 1) - D.dilatedStart ⬝ᵥ (cfc g D.backwardH *ᵥ D.dilatedStart)| ≤
      K * frobNorm (D.backwardH - D.dilatedH) := by
  rcases eq_or_ne K 0 with rfl | hK
  · have hconst : g = fun _ => g 0 := funext fun x => by
      have h := hg.dist_le_mul x 0
      simp only [NNReal.coe_zero, zero_mul, dist_le_zero] at h
      exact h
    have hv1 : D.v 1 ⬝ᵥ D.v 1 = 1 := by
      have h := hW 0
      simp only [Matrix.mul_apply, Matrix.transpose_apply, basisSucc, Matrix.of_apply] at h
      simpa [dotProduct] using h
    have hvt : D.dilatedStart ⬝ᵥ D.dilatedStart = 1 := by
      rw [← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, D.norm_toLp_dilatedStart hW, one_pow]
    have hsa : IsSelfAdjoint D.H := D.isHermitian
    have hsb : IsSelfAdjoint D.backwardH := D.isHermitian_backwardH hW
    rw [hconst, cfc_const (g 0) D.H hsa, cfc_const (g 0) D.backwardH hsb,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, dotProduct_smul,
      dotProduct_smul, hv1, hvt, sub_self, abs_zero, NNReal.coe_zero, zero_mul]
  · have hK0 : (0 : ℝ) < K :=
      lt_of_le_of_ne K.coe_nonneg (fun h => hK (NNReal.coe_eq_zero.1 h.symm))
    have h1 : LipschitzWith 1 (fun x => (K : ℝ)⁻¹ * g x) := LipschitzWith.of_dist_le_mul
      fun x y => by
        rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hK0), NNReal.coe_one, one_mul,
          inv_mul_le_iff₀ hK0, ← Real.dist_eq]
        exact hg.dist_le_mul x y
    have h := D.abs_dotProduct_cfc_mulVec_sub_le_frobNorm hW h1
    rw [cfc_const_mul _ _ D.H (D.H.finite_real_spectrum.continuousOn _),
      cfc_const_mul _ _ D.backwardH (D.backwardH.finite_real_spectrum.continuousOn _),
      Matrix.smul_mulVec,
      Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_sub,
      abs_mul, abs_of_pos (inv_pos.2 hK0), inv_mul_le_iff₀ hK0] at h
    exact h

/-! ### Quadrature through the backward model -/

/-- A degree below $m + 1$ is a degree at most $m$. -/
private theorem degree_le_of_degree_lt_succ {p : ℝ[X]} {m : ℕ}
    (hp : p.degree < ((m + 1 : ℕ) : WithBot ℕ)) : p.degree ≤ m := by
  rw [Nat.cast_add, Nat.cast_one] at hp
  exact Order.le_of_lt_succ hp

/-- Two functions within $\delta$ on a set containing the spectrum give quadratic forms within
$\delta\|\mathbf{x}\|^2$. -/
private theorem abs_dotProduct_cfc_mulVec_sub_dotProduct_cfc_mulVec_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {s : Set ℝ}
    (hs : spectrum ℝ A ⊆ s) {f g : ℝ → ℝ} {δ : ℝ} (h : ∀ x ∈ s, |f x - g x| ≤ δ) (x : ι → ℝ) :
    |x ⬝ᵥ (cfc f A *ᵥ x) - x ⬝ᵥ (cfc g A *ᵥ x)| ≤ δ * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [← dotProduct_sub, ← Matrix.sub_mulVec, ← cfc_sub f g A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _)]
  have := hA.abs_re_quadForm_cfc_le (f := fun y => f y - g y) (fun y hy => h y (hs hy)) x
  simpa only [quadForm_def, star_trivial, RCLike.re_to_real] using this

/-- An entry on the diagonal of $f(\mathbf{A})$ is the quadratic form at a coordinate vector. -/
private theorem cfc_apply_self_eq_dotProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (i : ι) : B i i = (Pi.single i 1 : ι → ℝ) ⬝ᵥ (B *ᵥ Pi.single i 1) := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- A coordinate vector is a unit vector. -/
private theorem norm_toLp_single_one {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    ‖WithLp.toLp 2 (Pi.single i 1 : ι → ℝ)‖ = 1 := by
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
  simp [dotProduct, Pi.single_apply]


/-- **The $(0,0)$ entry of $f(\mathbf{T}_k)$ is the Gauss rule of the backward model**: for
unit vectors and the sign conditions on $\beta$,
$(f(\mathbf{T}_k))_{00} = \int f\,d\,\mathsf{lanczosQuadrature}(\tilde{\mathbf{H}},
\tilde{\mathbf{v}}, k)$, since exact Lanczos on $(\tilde{\mathbf{H}}, \tilde{\mathbf{v}})$
computes $\mathbf{T}_k$ (`NLAlib.LanczosData.lanczosTridiagonal_backwardH_dilatedStart`) and
$\|\tilde{\mathbf{v}}\| = 1$ (`Matrix.IsHermitian.integral_lanczosQuadrature_succ`). -/
theorem cfc_tridiagonal_firstIndex_eq_integral
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) (hβ : ∀ j ≤ k, 0 ≤ D.β j)
    (hβpos : ∀ j, 1 ≤ j → j < k → 0 < D.β j) (f : ℝ → ℝ) :
    cfc f D.tridiagonal D.firstIndex D.firstIndex =
      ∫ x, f x ∂lanczosQuadrature D.backwardH D.dilatedStart k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos D.k_pos).symm⟩
  rw [(D.isHermitian_backwardH hW).integral_lanczosQuadrature_succ,
    LanczosData.lanczosTridiagonal_backwardH_dilatedStart hW hβ hβpos, D.norm_toLp_dilatedStart hW]
  simp only [one_pow, one_mul, RCLike.re_to_real]
  rfl

/-- **Knizhnerman-type quadrature bound, polynomial form**: for unit vectors, the sign conditions
on $\beta$, $\operatorname{spec}\mathbf{H} \subseteq [a, a']$ and
$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}} \le c$, if a real
polynomial of degree less than $2k$ is within $\delta$ of $f$ on $I_c = [a - c, a' + c]$ and $f$
is $L$-Lipschitz on $I_c$, then
$$\bigl\lvert\mathbf{v}_1^{\mathsf{T}}f(\mathbf{H})\mathbf{v}_1 - (f(\mathbf{T}_k))_{00}\bigr\rvert
\le 2\delta + Lc .$$
Knizhnerman (1996) proves a bound of the form
$O(k)E_{2k-1} + O(\mathrm{poly}(k)\varepsilon)\sup\lvert f\rvert$, through Paige's bounds and the
Chebyshev recurrence. No printed source. -/
theorem abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_isUniformApproxOn
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) (hβ : ∀ j ≤ k, 0 ≤ D.β j)
    (hβpos : ∀ j, 1 ≤ j → j < k → 0 < D.β j) {a a' c : ℝ}
    (hs : spectrum ℝ D.H ⊆ Set.Icc a a') (hc : frobNorm (D.backwardH - D.dilatedH) ≤ c)
    {f : ℝ → ℝ} {p : ℝ[X]} (hp : p.degree < 2 * k) {δ : ℝ}
    (hδ : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc (a - c) (a' + c)) δ)
    {L : ℝ≥0} (hf : LipschitzOnWith L f (Set.Icc (a - c) (a' + c))) :
    |D.v 1 ⬝ᵥ (cfc f D.H *ᵥ D.v 1) - cfc f D.tridiagonal D.firstIndex D.firstIndex| ≤
      2 * δ + L * c := by
  have hc0 : 0 ≤ c := (frobNorm_nonneg _).trans hc
  have hsub : Set.Icc a a' ⊆ Set.Icc (a - c) (a' + c) :=
    Set.Icc_subset_Icc (by linarith) (by linarith)
  have hsB := D.spectrum_backwardH_subset_Icc hW hs hc
  -- the Gauss rule of the backward model is exact to degree `2k - 1`
  have hG : |D.dilatedStart ⬝ᵥ (cfc f D.backwardH *ᵥ D.dilatedStart) -
      cfc f D.tridiagonal D.firstIndex D.firstIndex| ≤ 2 * δ := by
    have h := (D.isHermitian_backwardH
      hW).norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hsB hp hδ
      D.dilatedStart
    rw [D.cfc_tridiagonal_firstIndex_eq_integral hW hβ hβpos f, integral_lanczosQuadrature]
    rw [D.norm_toLp_dilatedStart hW, star_trivial, dotProduct_sub, Real.norm_eq_abs, one_pow,
      mul_one] at h
    simpa only [star_trivial, RCLike.re_to_real] using h
  -- the spectral measures are `W₁`-close
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  have hH : cfc f D.H = cfc g D.H := cfc_congr (hfg.mono (hs.trans hsub))
  have hB : cfc f D.backwardH = cfc g D.backwardH := cfc_congr (hfg.mono hsB)
  have hK := (D.abs_dotProduct_cfc_mulVec_sub_le_mul_frobNorm hW hg).trans
    (mul_le_mul_of_nonneg_left hc L.coe_nonneg)
  rw [← hH, ← hB] at hK
  calc _ ≤ |D.v 1 ⬝ᵥ (cfc f D.H *ᵥ D.v 1) -
          D.dilatedStart ⬝ᵥ (cfc f D.backwardH *ᵥ D.dilatedStart)| +
        |D.dilatedStart ⬝ᵥ (cfc f D.backwardH *ᵥ D.dilatedStart) -
          cfc f D.tridiagonal D.firstIndex D.firstIndex| := abs_sub_le _ _ _
    _ ≤ L * c + 2 * δ := add_le_add hK hG
    _ = 2 * δ + L * c := add_comm _ _

/-- **Knizhnerman-type quadrature bound for bounded $f$**: for unit vectors, the sign conditions
on $\beta$, $\operatorname{spec}\mathbf{H} \subseteq [a, a']$ with $a < a'$, $0 \le c$ and
$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}} \le c$, if a real
polynomial of degree less than $2k$ is within $\delta$ of $f$ on $I_c = [a - c, a' + c]$ and
$\lvert f\rvert \le M$ on $I_c$, then
$$\bigl\lvert\mathbf{v}_1^{\mathsf{T}}f(\mathbf{H})\mathbf{v}_1 - (f(\mathbf{T}_k))_{00}\bigr\rvert
\le 4\delta + 11k^3\frac{(M + \delta)\,c}{a' - a + 2c} ,$$
the Lipschitz constant of the approximating polynomial coming from its Chebyshev expansion
(`NLAlib.lipschitzOnWith_eval_of_degree_le_of_isUniformApproxOn`, $m = 2k - 1$). This is the
shape of the Knizhnerman (1996) bound (an additive term proportional to
$\sup\lvert f\rvert$); unoptimised. -/
theorem abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_isUniformApproxOn_of_abs_le
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) (hβ : ∀ j ≤ k, 0 ≤ D.β j)
    (hβpos : ∀ j, 1 ≤ j → j < k → 0 < D.β j) {a a' c : ℝ} (haa : a < a') (hc0 : 0 ≤ c)
    (hs : spectrum ℝ D.H ⊆ Set.Icc a a') (hc : frobNorm (D.backwardH - D.dilatedH) ≤ c)
    {f : ℝ → ℝ} {p : ℝ[X]} (hp : p.degree < 2 * k) {δ : ℝ}
    (hδ : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc (a - c) (a' + c)) δ)
    {M : ℝ} (hM : ∀ x ∈ Set.Icc (a - c) (a' + c), |f x| ≤ M) :
    |D.v 1 ⬝ᵥ (cfc f D.H *ᵥ D.v 1) - cfc f D.tridiagonal D.firstIndex D.firstIndex| ≤
      4 * δ + 11 * (k : ℝ) ^ 3 * (M + δ) * c / (a' - a + 2 * c) := by
  have hδ0 : 0 ≤ δ := hδ.nonneg ⟨a, by linarith, by linarith⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM a ⟨by linarith, by linarith⟩)
  have hw : 0 < a' - a + 2 * c := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast D.k_pos
  have hpdeg : p.degree ≤ ((2 * k - 1 : ℕ) : WithBot ℕ) := by
    apply degree_le_of_degree_lt_succ
    rw [show 2 * k - 1 + 1 = 2 * k by have := D.k_pos; omega]
    exact_mod_cast hp
  have hpM : Metric.IsUniformApproxOn (fun x => p.eval x) (fun _ => 0)
      (Set.Icc (a - c) (a' + c)) (M + δ) := fun x hx => by
    have h1 := hδ.apply hx
    have h2 := hM x hx
    rw [Real.dist_eq] at h1
    rw [Real.dist_eq, sub_zero]
    calc |p.eval x| ≤ |p.eval x - f x| + |f x| := by
          simpa using abs_add_le (p.eval x - f x) (f x)
      _ ≤ M + δ := by linarith
  have hLp := lipschitzOnWith_eval_of_degree_le_of_isUniformApproxOn (by linarith) hpdeg hpM
  have hQ := D.abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_isUniformApproxOn hW hβ hβpos
    hs hc hp (δ := 0) (fun x _ => by simp) hLp
  have hsub : Set.Icc a a' ⊆ Set.Icc (a - c) (a' + c) :=
    Set.Icc_subset_Icc (by linarith) (by linarith)
  have hfp : ∀ x ∈ Set.Icc (a - c) (a' + c), |f x - p.eval x| ≤ δ := fun x hx => by
    rw [abs_sub_comm, ← Real.dist_eq]
    exact hδ.apply hx
  have hv1 : ‖WithLp.toLp 2 (D.v 1)‖ = 1 := by
    have h := hW 0
    simp only [Matrix.mul_apply, Matrix.transpose_apply, basisSucc, Matrix.of_apply] at h
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
      EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    simpa [dotProduct] using h
  have h1 := abs_dotProduct_cfc_mulVec_sub_dotProduct_cfc_mulVec_le D.isHermitian
    (hs.trans hsub) hfp (D.v 1)
  have h2 := abs_dotProduct_cfc_mulVec_sub_dotProduct_cfc_mulVec_le
    (D.isHermitian_tridiagonal) (D.spectrum_tridiagonal_subset_Icc hW hs hc) hfp
    (Pi.single D.firstIndex 1)
  rw [hv1, one_pow, mul_one] at h1
  rw [norm_toLp_single_one, one_pow, mul_one, ← cfc_apply_self_eq_dotProduct,
    ← cfc_apply_self_eq_dotProduct] at h2
  have hcast : (((2 * k - 1 : ℕ) : ℝ) + 1) = 2 * k := by
    rw [Nat.cast_sub (by have := D.k_pos; omega)]
    push_cast
    ring
  rw [coe_nnnorm, Real.norm_of_nonneg (div_nonneg (by positivity) (by linarith)), hcast,
    show a' + c - (a - c) = a' - a + 2 * c by ring] at hQ
  have hLc : 4 / 3 * (2 * (k : ℝ)) ^ 3 * (M + δ) / (a' - a + 2 * c) * c ≤
      11 * (k : ℝ) ^ 3 * (M + δ) * c / (a' - a + 2 * c) := by
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hw.le
    nlinarith [mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ k) 3)
      (mul_nonneg (add_nonneg hM0 hδ0) hc0)]
  calc _ ≤ |D.v 1 ⬝ᵥ (cfc f D.H *ᵥ D.v 1) - D.v 1 ⬝ᵥ (cfc (fun x => p.eval x) D.H *ᵥ D.v 1)| +
        |D.v 1 ⬝ᵥ (cfc (fun x => p.eval x) D.H *ᵥ D.v 1) -
          cfc (fun x => p.eval x) D.tridiagonal D.firstIndex D.firstIndex| +
        |cfc f D.tridiagonal D.firstIndex D.firstIndex -
          cfc (fun x => p.eval x) D.tridiagonal D.firstIndex D.firstIndex| := by
        have := abs_sub_le (D.v 1 ⬝ᵥ (cfc f D.H *ᵥ D.v 1))
          (D.v 1 ⬝ᵥ (cfc (fun x => p.eval x) D.H *ᵥ D.v 1))
          (cfc f D.tridiagonal D.firstIndex D.firstIndex)
        have := abs_sub_le (D.v 1 ⬝ᵥ (cfc (fun x => p.eval x) D.H *ᵥ D.v 1))
          (cfc (fun x => p.eval x) D.tridiagonal D.firstIndex D.firstIndex)
          (cfc f D.tridiagonal D.firstIndex D.firstIndex)
        rw [abs_sub_comm (cfc (fun x => p.eval x) D.tridiagonal D.firstIndex D.firstIndex)]
          at this
        linarith
    _ ≤ δ + (2 * 0 + 4 / 3 * (2 * (k : ℝ)) ^ 3 * (M + δ) / (a' - a + 2 * c) * c) + δ := by
        gcongr
    _ ≤ 4 * δ + 11 * (k : ℝ) ^ 3 * (M + δ) * c / (a' - a + 2 * c) := by linarith

/-! ### Lanczos-FA through the Chebyshev recurrence -/

/-- The computed recurrence under the affine change of variable
$\hat{\mathbf{H}} = \sigma\mathbf{H} - \tau\mathbf{I}$:
$\mathbf{V}_k\hat{\mathbf{T}}_k = \hat{\mathbf{H}}\mathbf{V}_k -
\sigma(\beta_k\mathbf{v}_{k+1}\mathbf{e}_{k-1}^{\mathsf{T}} + \mathbf{F}_k)$. -/
private theorem basis_mulVec_aeval_mulVec (σ τ : ℝ) (y : Fin k → ℝ) :
    D.basis *ᵥ (aeval D.tridiagonal (C σ * X - C τ) *ᵥ y) =
      aeval D.H (C σ * X - C τ) *ᵥ (D.basis *ᵥ y) -
        σ • ((Matrix.vecMulVec (D.β k • D.v (k + 1)) (Pi.single D.lastIndex 1) +
          D.residual) *ᵥ y) := by
  have hM : D.basis * aeval D.tridiagonal (C σ * X - C τ) =
      aeval D.H (C σ * X - C τ) * D.basis -
        σ • (Matrix.vecMulVec (D.β k • D.v (k + 1)) (Pi.single D.lastIndex 1) + D.residual) := by
    simp only [map_sub, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, D.mul_basis]
    module
  rw [Matrix.mulVec_mulVec, hM, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec]

/-- **The bandwidth of $\mathbf{T}_k$ kills the last coordinate**: for $j + 1 < k$,
$\mathbf{e}_{k-1}^{\mathsf{T}}\hat T_j(\mathbf{T}_k)\mathbf{e}_0 = 0$. -/
private theorem aeval_chebyshevOn_mulVec_lastIndex {α β : ℝ} {j : ℕ} (hj : j + 1 < k) :
    (aeval D.tridiagonal (chebyshevOn α β j) *ᵥ Pi.single D.firstIndex 1) D.lastIndex = 0 := by
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  refine aeval_apply_eq_zero_of_natDegree_add_lt D.isTridiagonal_tridiagonal ?_
  have h := natDegree_le_of_degree_le (degree_chebyshevOn_le α β j)
  simp only [firstIndex, lastIndex]
  omega

/-- $\|U_m(\hat{\mathbf{H}})\mathbf{w}\| \le (m + 1)\|\mathbf{w}\|$ for
$\operatorname{spec}\mathbf{H} \subseteq [\alpha, \beta]$. -/
private theorem norm_aeval_U_mulVec_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.IsHermitian) {α β : ℝ} (hαβ : α < β)
    (hs : spectrum ℝ H ⊆ Set.Icc α β) (m : ℕ) (w : ι → ℝ) :
    ‖WithLp.toLp 2 (aeval (aeval H (C (2 / (β - α)) * X - C ((β + α) / (β - α))))
      (Chebyshev.U ℝ (m : ℤ)) *ᵥ w)‖ ≤ (m + 1) * ‖WithLp.toLp 2 w‖ := by
  rw [← aeval_comp]
  refine (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right
    (hH.specNorm_aeval_le _ (by positivity) fun x hx => ?_) (norm_nonneg _))
  simp only [eval_comp, eval_sub, eval_mul, eval_C, eval_X]
  exact abs_eval_U_le m (abs_div_mul_sub_div_le_one hαβ (hs hx))

/-- $\|\hat T_j(\mathbf{A})\mathbf{w}\| \le \|\mathbf{w}\|$ for
$\operatorname{spec}\mathbf{A} \subseteq [\alpha, \beta]$. -/
private theorem norm_aeval_chebyshevOn_mulVec_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.IsHermitian) {α β : ℝ} (hαβ : α < β)
    (hs : spectrum ℝ H ⊆ Set.Icc α β) (j : ℕ) (w : ι → ℝ) :
    ‖WithLp.toLp 2 (aeval H (chebyshevOn α β j) *ᵥ w)‖ ≤ ‖WithLp.toLp 2 w‖ := by
  refine (norm_toLp_mulVec_le _ _).trans ?_
  conv_rhs => rw [← one_mul ‖WithLp.toLp 2 w‖]
  exact mul_le_mul_of_nonneg_right (hH.specNorm_aeval_le _ zero_le_one fun x hx =>
    abs_eval_chebyshevOn_le_one hαβ j (hs hx)) (norm_nonneg _)

/-- The Clenshaw sum is at most $i(i+1)/2$ times a bound on its terms: for
$\operatorname{spec}\mathbf{H} \subseteq [\alpha, \beta]$ and $\|\mathbf{f}_j\| \le B$ ($j < i$),
$\|\sum_{j<i}U_{i-1-j}(\hat{\mathbf{H}})\mathbf{f}_j\| \le i(i+1)B/2$. -/
private theorem norm_sum_aeval_U_mulVec_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.IsHermitian) {α β : ℝ} (hαβ : α < β)
    (hs : spectrum ℝ H ⊆ Set.Icc α β) (i : ℕ) {f : ℕ → ι → ℝ} {B : ℝ}
    (hf : ∀ j < i, ‖WithLp.toLp 2 (f j)‖ ≤ B) :
    ‖WithLp.toLp 2 (∑ j ∈ Finset.range i,
      aeval (aeval H (C (2 / (β - α)) * X - C ((β + α) / (β - α))))
        (Chebyshev.U ℝ ((i : ℤ) - 1 - j)) *ᵥ f j)‖ ≤ i * (i + 1) / 2 * B := by
  rw [WithLp.toLp_sum, ← sum_range_sub_eq, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  rw [Finset.mem_range] at hj
  rw [show (i : ℤ) - 1 - j = ((i - 1 - j : ℕ) : ℤ) by omega]
  refine (norm_aeval_U_mulVec_le hH hαβ hs _ _).trans ?_
  rw [show (((i - 1 - j : ℕ) : ℝ) + 1) = (i : ℝ) - j by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring]
  exact mul_le_mul_of_nonneg_left (hf j hj) (by
    have : (j : ℝ) < i := by exact_mod_cast hj
    linarith)

/-- **The computed recurrence applies Chebyshev polynomials stably** ([DruskinKnizhnerman1991,
§4]; [MuscoMuscoSidford2018, Lemma 10]; Chen's thesis, Theorem 8.4): for any symmetric
three-term datum with $\mathbf{H}\mathbf{V}_k = \mathbf{V}_{k+1}\underline{\mathbf{T}}_k +
\mathbf{F}_k$ (`NLAlib.LanczosData.mul_basis`), $\operatorname{spec}\mathbf{H} \subseteq
[\alpha, \beta]$ and $\operatorname{spec}\mathbf{T}_k \subseteq [\alpha, \beta]$, for $i < k$,
$$\|\hat T_i(\mathbf{H})\mathbf{v}_1 - \mathbf{V}_k\hat T_i(\mathbf{T}_k)\mathbf{e}_0\|
\le \frac{2i(i + 1)}{\beta - \alpha}\|\mathbf{F}_k\|_2 .$$
No orthogonality of the computed basis is assumed. -/
theorem norm_aeval_chebyshevOn_mulVec_sub_basis_mulVec_le {α β : ℝ} (hαβ : α < β)
    (hs : spectrum ℝ D.H ⊆ Set.Icc α β) (hT : spectrum ℝ D.tridiagonal ⊆ Set.Icc α β)
    {i : ℕ} (hi : i < k) :
    ‖WithLp.toLp 2 (aeval D.H (chebyshevOn α β i) *ᵥ D.v 1 -
      D.basis *ᵥ (aeval D.tridiagonal (chebyshevOn α β i) *ᵥ Pi.single D.firstIndex 1))‖ ≤
      2 * i * (i + 1) / (β - α) * specNorm D.residual := by
  have hd : 0 < β - α := sub_pos.2 hαβ
  set σ := 2 / (β - α) with hσ
  set ℓ : ℝ[X] := C σ * X - C ((β + α) / (β - α)) with hℓ
  set A := aeval D.H ℓ
  set e₀ : Fin k → ℝ := Pi.single D.firstIndex 1
  set E := Matrix.vecMulVec (D.β k • D.v (k + 1)) (Pi.single D.lastIndex (1 : ℝ))
  set F := D.residual
  set y : ℕ → Fin k → ℝ := fun j => aeval D.tridiagonal (chebyshevOn α β j) *ᵥ e₀ with hy
  set d : ℕ → Fin n → ℝ := fun j => aeval D.H (chebyshevOn α β j) *ᵥ D.v 1 - D.basis *ᵥ y j
    with hd_def
  have hcheb : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (j : ℕ),
      aeval M (chebyshevOn α β j) = aeval (aeval M ℓ) (Chebyshev.T ℝ (j : ℤ)) :=
    fun M j => by rw [chebyshevOn, aeval_comp]
  have hrec : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (w : ι → ℝ) (j : ℕ),
      aeval M (chebyshevOn α β (j + 2)) *ᵥ w = (2 : ℝ) • (aeval M ℓ *ᵥ
        (aeval M (chebyshevOn α β (j + 1)) *ᵥ w)) - aeval M (chebyshevOn α β j) *ᵥ w := by
    intro ι _ _ M w j
    rw [hcheb, hcheb, hcheb, show ((j + 2 : ℕ) : ℤ) = (j : ℤ) + 2 by push_cast; ring,
      Chebyshev.T_add_two, aeval_two_mul_X_mul_sub_mulVec]
    push_cast
    rfl
  have hV0 : D.basis *ᵥ e₀ = D.v 1 := by
    rw [Matrix.mulVec_single_one]
    rfl
  have hd0 : d 0 = 0 := by
    simp only [hd_def, hy, hcheb, Nat.cast_zero, Chebyshev.T_zero, map_one, Matrix.one_mulVec,
      hV0, sub_self]
  have hE : ∀ j, j + 1 < k → E *ᵥ y j = 0 := fun j hj => by
    have h0 : y j D.lastIndex = 0 := D.aeval_chebyshevOn_mulVec_lastIndex hj
    rw [Matrix.vecMulVec_mulVec, single_one_dotProduct, h0, MulOpposite.op_zero, zero_smul]
  have hFy : ∀ j, ‖WithLp.toLp 2 (F *ᵥ y j)‖ ≤ specNorm F := fun j => by
    refine (norm_toLp_mulVec_le _ _).trans ?_
    conv_rhs => rw [← mul_one (specNorm F)]
    refine mul_le_mul_of_nonneg_left ((norm_aeval_chebyshevOn_mulVec_le D.isHermitian_tridiagonal
      hαβ hT j e₀).trans (norm_toLp_single_one _).le) (specNorm_nonneg _)
  -- the residual sequence of the recurrence
  have hf : ∀ j, j + 1 < k →
      ‖WithLp.toLp 2 (chebyshevRecurrenceResidual A d j)‖ ≤ 2 * σ * specNorm F := by
    intro j hj
    have hσ0 : 0 < σ := div_pos two_pos hd
    rcases j with _ | j
    · have hy0 : y 0 = e₀ := by
        simp only [hy, hcheb, Nat.cast_zero, Chebyshev.T_zero, map_one, Matrix.one_mulVec]
      have h1 : chebyshevRecurrenceResidual A d 0 = σ • (F *ᵥ y 0) := by
        have hk := D.basis_mulVec_aeval_mulVec σ ((β + α) / (β - α)) e₀
        rw [hV0, ← hℓ] at hk
        have hd1 : d 1 = A *ᵥ D.v 1 - D.basis *ᵥ (aeval D.tridiagonal ℓ *ᵥ e₀) := by
          simp only [hd_def, hy, hcheb, Nat.cast_one, Chebyshev.T_one, aeval_X, A]
        have hE0 : E *ᵥ e₀ = 0 := hy0 ▸ hE 0 hj
        change d 1 = _
        rw [hd1, hk, Matrix.add_mulVec, hE0, zero_add, hy0]
        abel
      rw [h1, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hσ0]
      nlinarith [hFy 0, specNorm_nonneg F]
    · have h1 : chebyshevRecurrenceResidual A d (j + 1) = (2 * σ) • (F *ᵥ y (j + 1)) := by
        have hk := D.basis_mulVec_aeval_mulVec σ ((β + α) / (β - α)) (y (j + 1))
        rw [← hℓ, Matrix.add_mulVec, hE (j + 1) hj, zero_add] at hk
        have hy2 : y (j + 2) = (2 : ℝ) • (aeval D.tridiagonal ℓ *ᵥ y (j + 1)) - y j :=
          hrec D.tridiagonal e₀ j
        simp only [chebyshevRecurrenceResidual, hd_def, hrec D.H (D.v 1) j, hy2,
          Matrix.mulVec_sub, Matrix.mulVec_smul, hk]
        module
      rw [h1, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (hFy _) (by positivity)
  -- the Clenshaw representation and the bounds
  change ‖WithLp.toLp 2 (d i)‖ ≤ _
  rw [eq_sum_aeval_U_mulVec_chebyshevRecurrenceResidual A hd0 i]
  refine (norm_sum_aeval_U_mulVec_le D.isHermitian hαβ hs i fun j hj => hf j (by omega)).trans
    (le_of_eq ?_)
  rw [hσ]
  field_simp

/-- **The computed recurrence applies bounded polynomials stably** ([MuscoMuscoSidford2018,
Lemma 9]): for a real polynomial of degree less than $k$ bounded by $M$ on $[\alpha, \beta]$,
$$\|p(\mathbf{H})\mathbf{v}_1 - \mathbf{V}_kp(\mathbf{T}_k)\mathbf{e}_0\| \le
\frac{4}{3}k^3\frac{M}{\beta - \alpha}\|\mathbf{F}_k\|_2 ,$$
by the Chebyshev expansion $p = \sum_{i < k}a_i\hat T_i$, $\lvert a_i\rvert \le 2M$, and
`norm_aeval_chebyshevOn_mulVec_sub_basis_mulVec_le`
($\sum_{i<k} 2M \cdot 2i(i+1) = 4M(k-1)k(k+1)/3$). -/
theorem norm_aeval_mulVec_sub_basis_mulVec_le_of_degree_lt {α β : ℝ} (hαβ : α < β)
    (hs : spectrum ℝ D.H ⊆ Set.Icc α β) (hT : spectrum ℝ D.tridiagonal ⊆ Set.Icc α β)
    {p : ℝ[X]} (hp : p.degree < k) {M : ℝ}
    (hM : Metric.IsUniformApproxOn (fun x => p.eval x) (fun _ => 0) (Set.Icc α β) M) :
    ‖WithLp.toLp 2 (aeval D.H p *ᵥ D.v 1 -
      D.basis *ᵥ (aeval D.tridiagonal p *ᵥ Pi.single D.firstIndex 1))‖ ≤
      4 / 3 * (k : ℝ) ^ 3 * M / (β - α) * specNorm D.residual := by
  have hd : 0 < β - α := sub_pos.2 hαβ
  have hM0 : 0 ≤ M := hM.nonneg ⟨α, le_rfl, hαβ.le⟩
  have hpdeg : p.degree ≤ ((k - 1 : ℕ) : WithBot ℕ) :=
    degree_le_of_degree_lt_succ (by rw [Nat.sub_add_cancel D.k_pos]; exact hp)
  obtain ⟨a, hpa, ha0, ha⟩ := exists_eq_sum_smul_chebyshevOn_of_isUniformApproxOn hαβ hpdeg hM
  have ha' : ∀ i, |a i| ≤ 2 * M := fun i => by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · linarith
    · exact ha i hi
  rw [Nat.sub_add_cancel D.k_pos] at hpa
  have hsum : aeval D.H p *ᵥ D.v 1 -
      D.basis *ᵥ (aeval D.tridiagonal p *ᵥ Pi.single D.firstIndex 1) =
      ∑ i ∈ Finset.range k, a i • (aeval D.H (chebyshevOn α β i) *ᵥ D.v 1 -
        D.basis *ᵥ (aeval D.tridiagonal (chebyshevOn α β i) *ᵥ Pi.single D.firstIndex 1)) := by
    rw [hpa]
    simp only [map_sum, map_smul, Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.mulVec_sum,
      Matrix.mulVec_smul, smul_sub, Finset.sum_sub_distrib]
  rw [hsum, WithLp.toLp_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ Finset.range k, ‖WithLp.toLp 2 (a i • (aeval D.H (chebyshevOn α β i) *ᵥ D.v 1 -
        D.basis *ᵥ (aeval D.tridiagonal (chebyshevOn α β i) *ᵥ Pi.single D.firstIndex 1)))‖
      ≤ ∑ i ∈ Finset.range k,
          2 * M * (2 * i * (i + 1) / (β - α) * specNorm D.residual) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (ha' i) (D.norm_aeval_chebyshevOn_mulVec_sub_basis_mulVec_le hαβ hs hT
          (Finset.mem_range.1 hi)) (norm_nonneg _) (by positivity)
    _ = 4 * M * specNorm D.residual / (β - α) *
          ∑ i ∈ Finset.range k, (i : ℝ) * (i + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ 4 * M * specNorm D.residual / (β - α) * ((k : ℝ) ^ 3 / 3) := by
        have := specNorm_nonneg D.residual
        gcongr
        exact sum_range_mul_succ_le k
    _ = 4 / 3 * (k : ℝ) ^ 3 * M / (β - α) * specNorm D.residual := by ring

end LanczosData

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- The first index $0 : \mathrm{Fin}\,k$ of a run. -/
def firstIndex : Fin k := L.toLanczosData.firstIndex

/-- The **width of the enlarged interval** $I_c = [a - c, a' + c]$, namely
(`NLAlib.lanczosBackwardFactor`) <!-- value lanczosBackwardFactor k -->
$c = 2000k^4\varepsilon\|\mathbf{H}\|_2$. -/
noncomputable def enlargement : ℝ := lanczosBackwardFactor k * L.ε * specNorm L.H

/-- **Containment of the computed Ritz values** as a spectrum inclusion: for
$\operatorname{spec}\mathbf{H} \subseteq [a, a']$,
$\operatorname{spec}\mathbf{T}_k \subseteq [a - c, a' + c]$ with
$c = 2000k^4\varepsilon\|\mathbf{H}\|_2$. The eigenpair forms are
`NLAlib.LanczosRun.eigenvalue_last_sub_le_of_mulVec_eq_smul` and
`NLAlib.LanczosRun.sub_eigenvalue_zero_le_of_mulVec_eq_smul`. -/
theorem spectrum_tridiagonal_subset_Icc {a a' : ℝ} (hs : spectrum ℝ L.H ⊆ Set.Icc a a') :
    spectrum ℝ L.tridiagonal ⊆ Set.Icc (a - L.enlargement) (a' + L.enlargement) :=
  L.normalized.spectrum_tridiagonal_subset_Icc L.transpose_basisSucc_mul_self_apply hs
    L.frobNorm_backwardH_sub_dilatedH_le

/-- The enlargement is nonnegative. -/
theorem enlargement_nonneg : 0 ≤ L.enlargement := by
  have := L.ε_nonneg
  have := specNorm_nonneg L.H
  rw [enlargement, lanczosBackwardFactor_def]
  positivity

/-! ### Quadrature -/

/-- **Knizhnerman-type quadrature bound for a Lanczos run** (continuous $f$, Lipschitz on the
enlarged interval): for $\operatorname{spec}\mathbf{H} \subseteq [a, a']$,
$c = 2000k^4\varepsilon\|\mathbf{H}\|_2$, $I_c = [a - c, a' + c]$ and $f$ $L$-Lipschitz on
$I_c$, <!-- value lanczosBackwardFactor k -->
$$\bigl\lvert\bar{\mathbf{v}}_1^{\mathsf{T}}f(\mathbf{H})\bar{\mathbf{v}}_1 -
(f(\mathbf{T}_k))_{00}\bigr\rvert \le 2E_{2k-1}(f; I_c) + 2000k^4\varepsilon\|\mathbf{H}\|_2\,L ,$$
$E_{2k-1}$ the best uniform approximation error by polynomials of degree at most $2k - 1$
(`NLAlib.minimaxError`), $\bar{\mathbf{v}}_1$ the normalised computed first vector. Compare
Knizhnerman (1996): $O(k)E_{2k-1}(f; I_\eta) + O(\mathrm{poly}(k)\varepsilon)
\sup_{I_\eta}\lvert f\rvert$ with Paige's $\eta$ (as summarised in Chen's thesis §8.4 and the
handbook, Cor. 7.5). No printed source.
Result: lanczos-quadrature-finite-precision -/
theorem abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_continuousOn {a a' : ℝ}
    (hs : spectrum ℝ L.H ⊆ Set.Icc a a') {f : ℝ → ℝ} {Lf : ℝ≥0}
    (hf : LipschitzOnWith Lf f (Set.Icc (a - L.enlargement) (a' + L.enlargement))) :
    |L.normalizedV 1 ⬝ᵥ (cfc f L.H *ᵥ L.normalizedV 1) -
        cfc f L.tridiagonal L.firstIndex L.firstIndex| ≤
      2 * minimaxError f (Set.Icc (a - L.enlargement) (a' + L.enlargement)) (2 * k - 1) +
        Lf * L.enlargement := by
  obtain ⟨p, hp, hpf⟩ := exists_degree_le_isUniformApproxOn_minimaxError isCompact_Icc
    hf.continuousOn (2 * k - 1)
  have hp' : p.degree < 2 * k :=
    hp.trans_lt (by exact_mod_cast (by have := L.k_pos; omega : 2 * k - 1 < 2 * k))
  exact L.normalized.abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_isUniformApproxOn
    L.transpose_basisSucc_mul_self_apply L.β_nonneg L.β_pos hs
    L.frobNorm_backwardH_sub_dilatedH_le hp' hpf hf

/-- **Knizhnerman-type quadrature bound, explicit rate for Lipschitz $f$** (Jackson):
for $f$ $L$-Lipschitz on $I_c$, <!-- value jacksonApproximationConstant -->
$$\bigl\lvert\bar{\mathbf{v}}_1^{\mathsf{T}}f(\mathbf{H})\bar{\mathbf{v}}_1 -
(f(\mathbf{T}_k))_{00}\bigr\rvert \le L\Bigl(\frac{\pi(a' - a + 2c)}{2k + 1} + c\Bigr) ,
\qquad c = 2000k^4\varepsilon\|\mathbf{H}\|_2 .$$
No printed source.
Result: lanczos-quadrature-finite-precision -/
theorem abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_lipschitzOnWith {a a' : ℝ}
    (haa : a < a') (hs : spectrum ℝ L.H ⊆ Set.Icc a a') {f : ℝ → ℝ} {Lf : ℝ≥0}
    (hf : LipschitzOnWith Lf f (Set.Icc (a - L.enlargement) (a' + L.enlargement))) :
    |L.normalizedV 1 ⬝ᵥ (cfc f L.H *ᵥ L.normalizedV 1) -
        cfc f L.tridiagonal L.firstIndex L.firstIndex| ≤
      Lf * (jacksonApproximationConstant * (a' - a + 2 * L.enlargement) / (2 * k + 1) +
        L.enlargement) := by
  have hc0 := L.enlargement_nonneg
  have h := L.abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_continuousOn hs hf
  have hJ := minimaxError_le_of_lipschitzOnWith
    (by linarith : a - L.enlargement < a' + L.enlargement) hf (2 * k - 1)
  have hcast : ((2 * k - 1 : ℕ) : ℝ) + 2 = 2 * k + 1 := by
    rw [Nat.cast_sub (by have := L.k_pos; omega)]
    push_cast
    ring
  rw [hcast, show a' + L.enlargement - (a - L.enlargement) = a' - a + 2 * L.enlargement by
    ring] at hJ
  have hk : (0 : ℝ) < 2 * k + 1 := by positivity
  calc _ ≤ _ := h
    _ ≤ 2 * (jacksonApproximationConstant * Lf * (a' - a + 2 * L.enlargement) /
          (2 * (2 * k + 1))) + Lf * L.enlargement := by gcongr
    _ = _ := by field_simp

/-- **The quadrature bound with the computed (unnormalised) first vector**: for
$\operatorname{spec}\mathbf{H} \subseteq [a, a']$, <!-- value lanczosBackwardFactor k -->
$c = 2000k^4\varepsilon\|\mathbf{H}\|_2$, $I_c = [a - c, a' + c]$, $f$ $L$-Lipschitz on $I_c$
and $\lvert f\rvert \le M$ on $I_c$, the computed first vector $\mathbf{v}_1$ satisfies
$$\bigl\lvert\mathbf{v}_1^{\mathsf{T}}f(\mathbf{H})\mathbf{v}_1 - (f(\mathbf{T}_k))_{00}\bigr\rvert
\le 2E_{2k-1}(f; I_c) + 2000k^4\varepsilon\|\mathbf{H}\|_2\,L + \varepsilon M ,$$
the last term from $\bigl\lvert\|\mathbf{v}_1\|^2 - 1\bigr\rvert \le \varepsilon$. -/
theorem abs_dotProduct_cfc_mulVec_v_sub_cfc_tridiagonal_le_of_continuousOn {a a' : ℝ}
    (hs : spectrum ℝ L.H ⊆ Set.Icc a a') {f : ℝ → ℝ} {Lf : ℝ≥0}
    (hf : LipschitzOnWith Lf f (Set.Icc (a - L.enlargement) (a' + L.enlargement))) {M : ℝ}
    (hM : ∀ x ∈ Set.Icc (a - L.enlargement) (a' + L.enlargement), |f x| ≤ M) :
    |L.v 1 ⬝ᵥ (cfc f L.H *ᵥ L.v 1) - cfc f L.tridiagonal L.firstIndex L.firstIndex| ≤
      2 * minimaxError f (Set.Icc (a - L.enlargement) (a' + L.enlargement)) (2 * k - 1) +
        Lf * L.enlargement + L.ε * M := by
  have hc0 := L.enlargement_nonneg
  have h := L.abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_continuousOn hs hf
  have hpos := L.norm_v_pos le_rfl L.k_pos
  have hv : L.v 1 = ‖WithLp.toLp 2 (L.v 1)‖ • L.normalizedV 1 := by
    rw [L.normalizedV_of_le L.k_pos, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  have hq : L.v 1 ⬝ᵥ (cfc f L.H *ᵥ L.v 1) = ‖WithLp.toLp 2 (L.v 1)‖ ^ 2 *
      (L.normalizedV 1 ⬝ᵥ (cfc f L.H *ᵥ L.normalizedV 1)) := by
    conv_lhs => rw [hv]
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  have hb : |L.normalizedV 1 ⬝ᵥ (cfc f L.H *ᵥ L.normalizedV 1)| ≤ M := by
    have := L.isHermitian.abs_re_quadForm_cfc_le (f := f) (c := M)
      (fun x hx => hM x (Set.Icc_subset_Icc (by linarith) (by linarith) (hs hx)))
      (L.normalizedV 1)
    rw [L.norm_normalizedV le_rfl (by omega), one_pow, mul_one] at this
    simpa only [quadForm_def, star_trivial, RCLike.re_to_real] using this
  have hε := L.abs_norm_v_sq_sub_one_le 1 le_rfl L.k_pos
  rw [hq]
  calc _ = |(L.normalizedV 1 ⬝ᵥ (cfc f L.H *ᵥ L.normalizedV 1) -
          cfc f L.tridiagonal L.firstIndex L.firstIndex) +
        (‖WithLp.toLp 2 (L.v 1)‖ ^ 2 - 1) *
          (L.normalizedV 1 ⬝ᵥ (cfc f L.H *ᵥ L.normalizedV 1))| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by
        rw [abs_mul]
        exact add_le_add h (mul_le_mul hε hb (abs_nonneg _) L.ε_nonneg))

/-! ### Lanczos-FA -/

/-- **Druskin–Knizhnerman-type Lanczos-FA bound for a Lanczos run**: for
$\operatorname{spec}\mathbf{H} \subseteq [a, a']$, <!-- value lanczosBackwardFactor k -->
$c = 2000k^4\varepsilon\|\mathbf{H}\|_2$,
$I_c = [a - c, a' + c]$, $f$ continuous on $I_c$ with $\lvert f\rvert \le M$ there, the computed
basis $\mathbf{V}_k$ and tridiagonal matrix $\mathbf{T}_k$ satisfy
$$\|f(\mathbf{H})\mathbf{v}_1 - \mathbf{V}_kf(\mathbf{T}_k)\mathbf{e}_0\| \le
(2 + \sqrt{k})\,E_{k-1}(f; I_c) + 16k^4\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2\,
\frac{M}{a' - a + 2c} .$$
Compare [MuscoMuscoSidford2018, Lemma 11]:
$(k + 2)\delta_k + 92Ck^4n^{3/2}\|\mathbf{A}\|_2\varepsilon_{\mathrm{mach}}
/(\lambda_{\max} - \lambda_{\min} + 2\eta)$ with Paige's
$\eta \ge 85n^{3/2}k^{5/2}\|\mathbf{A}\|_2\varepsilon_{\mathrm{mach}}$;
[DruskinKnizhnerman1991, §4] for the method of proof.
Result: lanczos-fa-finite-precision -/
theorem norm_cfc_mulVec_sub_basis_mulVec_le_of_continuousOn {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ L.H ⊆ Set.Icc a a') {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (a - L.enlargement) (a' + L.enlargement))) {M : ℝ}
    (hM : ∀ x ∈ Set.Icc (a - L.enlargement) (a' + L.enlargement), |f x| ≤ M) :
    ‖WithLp.toLp 2 (cfc f L.H *ᵥ L.v 1 -
      L.basis *ᵥ (cfc f L.tridiagonal *ᵥ Pi.single L.firstIndex 1))‖ ≤
      (2 + Real.sqrt k) *
          minimaxError f (Set.Icc (a - L.enlargement) (a' + L.enlargement)) (k - 1) +
        16 * (k : ℝ) ^ 4 * Real.sqrt k * L.ε * specNorm L.H * M /
          (a' - a + 2 * L.enlargement) := by
  set c := L.enlargement
  set I := Set.Icc (a - c) (a' + c)
  set E := minimaxError f I (k - 1)
  set e₀ : Fin k → ℝ := Pi.single L.firstIndex 1
  have hc0 : 0 ≤ c := L.enlargement_nonneg
  have hsub : Set.Icc a a' ⊆ I := Set.Icc_subset_Icc (by linarith) (by linarith)
  have hw : 0 < a' - a + 2 * c := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM a (hsub ⟨le_rfl, haa.le⟩))
  have hε := L.ε_nonneg
  have hH := specNorm_nonneg L.H
  have hT := L.spectrum_tridiagonal_subset_Icc hs
  obtain ⟨p, hp, hpf⟩ := exists_degree_le_isUniformApproxOn_minimaxError isCompact_Icc hf (k - 1)
  have hE0 : 0 ≤ E := minimaxError_nonneg _ _ _
  have hEM : E ≤ M := minimaxError_le_of_isUniformApproxOn (p := 0) (by simp) hM0
    fun x hx => by simpa only [eval_zero, Real.dist_eq, zero_sub, abs_neg] using hM x hx
  have hpdeg : p.degree < k :=
    hp.trans_lt (by exact_mod_cast Nat.sub_one_lt_of_lt L.k_pos)
  have hfp : ∀ x ∈ I, |f x - p.eval x| ≤ E := fun x hx => by
    rw [abs_sub_comm, ← Real.dist_eq]
    exact hpf.apply hx
  have hpM : Metric.IsUniformApproxOn (fun x => p.eval x) (fun _ => 0) I (M + E) :=
    fun x hx => by
      rw [Real.dist_eq, sub_zero]
      calc |p.eval x| ≤ |f x - p.eval x| + |f x| := by
            simpa [abs_sub_comm] using abs_sub_le (p.eval x) (f x) 0
        _ ≤ M + E := by linarith [hfp x hx, hM x hx]
  -- the three terms
  have hmid := L.toLanczosData.norm_aeval_mulVec_sub_basis_mulVec_le_of_degree_lt
    (by linarith : a - c < a' + c) (hs.trans hsub) hT hpdeg hpM
  rw [show a' + c - (a - c) = a' - a + 2 * c by ring] at hmid
  have hmid' : ‖WithLp.toLp 2 (aeval L.H p *ᵥ L.v 1 - L.basis *ᵥ (aeval L.tridiagonal p *ᵥ e₀))‖ ≤
      4 / 3 * (k : ℝ) ^ 3 * (M + E) / (a' - a + 2 * c) * specNorm L.residual := hmid
  have hres : specNorm L.residual ≤ 6 * k * Real.sqrt k * L.ε * specNorm L.H := by
    have := L.specNorm_residual_le
    rwa [lanczosResidualFactor_def] at this
  have h1 : ‖WithLp.toLp 2 ((cfc f L.H - cfc (fun x => p.eval x) L.H) *ᵥ L.v 1)‖ ≤
      E * (1 + L.ε / 2) := by
    refine (norm_toLp_mulVec_le _ _).trans (mul_le_mul ?_ (L.norm_v_le L.k_pos) (norm_nonneg _)
      hE0)
    rw [← cfc_sub f _ L.H (L.H.finite_real_spectrum.continuousOn _)
      (L.H.finite_real_spectrum.continuousOn _)]
    exact L.isHermitian.specNorm_cfc_le hE0 fun x hx => hfp x (hsub (hs hx))
  have h3 : ‖WithLp.toLp 2 (L.basis *ᵥ ((cfc f L.tridiagonal -
      cfc (fun x => p.eval x) L.tridiagonal) *ᵥ e₀))‖ ≤ (1 + L.ε / 2) * Real.sqrt k * E := by
    refine (norm_toLp_mulVec_le _ _).trans (mul_le_mul ((specNorm_le_frobNorm _).trans
      L.frobNorm_basis_le) ((norm_toLp_mulVec_le _ _).trans ?_) (norm_nonneg _) (by positivity))
    rw [LanczosData.norm_toLp_single_one, mul_one, ← cfc_sub f _ L.tridiagonal
      (L.tridiagonal.finite_real_spectrum.continuousOn _)
      (L.tridiagonal.finite_real_spectrum.continuousOn _)]
    exact L.toLanczosData.isHermitian_tridiagonal.specNorm_cfc_le hE0 fun x hx => hfp x (hT hx)
  have hdec : cfc f L.H *ᵥ L.v 1 - L.basis *ᵥ (cfc f L.tridiagonal *ᵥ e₀) =
      (cfc f L.H - cfc (fun x => p.eval x) L.H) *ᵥ L.v 1 +
        (aeval L.H p *ᵥ L.v 1 - L.basis *ᵥ (aeval L.tridiagonal p *ᵥ e₀)) -
        L.basis *ᵥ ((cfc f L.tridiagonal - cfc (fun x => p.eval x) L.tridiagonal) *ᵥ e₀) := by
    have hsa : IsSelfAdjoint L.H := L.isHermitian
    have hsT : IsSelfAdjoint L.tridiagonal := L.toLanczosData.isHermitian_tridiagonal
    rw [← cfc_polynomial p L.H hsa, ← cfc_polynomial p L.tridiagonal hsT]
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub]
    abel
  rw [hdec]
  refine (norm_sub_le_of_le (norm_add_le_of_le h1 hmid') h3).trans ?_
  -- the arithmetic
  have hsk : Real.sqrt k ≤ k := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.k_pos
    exact (Real.sqrt_le_sqrt (by nlinarith : (k : ℝ) ≤ k ^ 2)).trans_eq
      (Real.sqrt_sq (by linarith))
  have hkε := L.k_mul_ε_le
  have hεs : L.ε * Real.sqrt k ≤ 1 / 100 := by nlinarith
  have hA : E * (1 + L.ε / 2) + (1 + L.ε / 2) * Real.sqrt k * E ≤ (2 + Real.sqrt k) * E := by
    nlinarith [L.ε_le, Real.sqrt_nonneg (k : ℝ)]
  have hB : 4 / 3 * (k : ℝ) ^ 3 * (M + E) / (a' - a + 2 * c) * specNorm L.residual ≤
      16 * (k : ℝ) ^ 4 * Real.sqrt k * L.ε * specNorm L.H * M / (a' - a + 2 * c) := by
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hw.le
    have hX : 0 ≤ (k : ℝ) ^ 3 * (k * Real.sqrt k * L.ε * specNorm L.H) := by positivity
    calc 4 / 3 * (k : ℝ) ^ 3 * (M + E) * specNorm L.residual
        ≤ 4 / 3 * (k : ℝ) ^ 3 * (M + E) * (6 * k * Real.sqrt k * L.ε * specNorm L.H) := by
          gcongr
      _ ≤ 16 * (k : ℝ) ^ 4 * Real.sqrt k * L.ε * specNorm L.H * M := by nlinarith
  linarith

end LanczosRun

end NLAlib
