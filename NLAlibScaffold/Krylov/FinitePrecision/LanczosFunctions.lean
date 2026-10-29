/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.BackwardSpectral
public import NLAlib.Krylov.Functions.Quadrature
public import NLAlibScaffold.Krylov.Processes.LanczosRounding
public import NLAlib.Polynomial.Approximation.ChebyshevTruncation
public import NLAlib.Polynomial.Approximation.Jackson
public import NLAlib.Polynomial.Chebyshev.EvenFilter
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Finite-precision Lanczos quadrature and Lanczos-FA: Druskin–Knizhnerman and Knizhnerman bounds

Statements only (research branch `research/dk-bounds`; design
`docs/design/research/Krylov-LanczosFunctionsRounding.md`). For a finite-precision Lanczos run
`L : NLAlib.LanczosRun n k` on a symmetric $\mathbf{H}$ with spectrum in $[a, a']$, write
$c = 2000k^4\varepsilon\|\mathbf{H}\|_2$ (`NLAlib.lanczosBackwardFactor`) and
$I_c = [a - c, a' + c]$.

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
  \frac{\sup_{I_c}|f|}{a' - a + 2c} .$$

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
* `NLAlib.Computation.IsRelErrSem.exists_lanczosQuadratureBound_of_lanczosBasisDenseProg`:
  the quadrature bound for the dense program, end to end.
-/

@[expose] public section

open Polynomial MeasureTheory
open scoped Matrix NNReal

namespace NLAlib

open Computation Builder

/-! ### Scaled Chebyshev polynomials -/

/-- The **Chebyshev polynomial of the first kind on $[\alpha, \beta]$**:
$\hat T_i(x) = T_i\bigl((2x - \alpha - \beta)/(\beta - \alpha)\bigr)$. -/
noncomputable def chebyshevOn (α β : ℝ) (i : ℕ) : ℝ[X] :=
  (Chebyshev.T ℝ (i : ℤ)).comp (C (2 / (β - α)) * X - C ((β + α) / (β - α)))

/-- The affine map $x \mapsto (2x - \alpha - \beta)/(\beta - \alpha)$ sends $[\alpha, \beta]$ into
$[-1, 1]$. -/
private theorem abs_affine_le_one {α β : ℝ} (hαβ : α < β) {x : ℝ} (hx : x ∈ Set.Icc α β) :
    |2 / (β - α) * x - (β + α) / (β - α)| ≤ 1 := by
  have hd : 0 < β - α := sub_pos.2 hαβ
  rw [show 2 / (β - α) * x - (β + α) / (β - α) = (2 * x - β - α) / (β - α) by
    field_simp; ring, abs_div, abs_of_pos hd, div_le_one hd, abs_le]
  constructor <;> linarith [hx.1, hx.2]

/-- $\hat T_i$ has degree at most $i$. -/
theorem degree_chebyshevOn_le (α β : ℝ) (i : ℕ) : (chebyshevOn α β i).degree ≤ i := by
  have hl : (C (2 / (β - α)) * X - C ((β + α) / (β - α))).natDegree ≤ 1 := by compute_degree
  have h := natDegree_comp_le (p := Chebyshev.T ℝ (i : ℤ))
    (q := C (2 / (β - α)) * X - C ((β + α) / (β - α)))
  rw [Chebyshev.natDegree_T, Int.natAbs_natCast] at h
  refine degree_le_natDegree.trans ?_
  exact_mod_cast h.trans (by nlinarith)

/-- $|\hat T_i| \le 1$ on $[\alpha, \beta]$. -/
theorem abs_eval_chebyshevOn_le_one {α β : ℝ} (hαβ : α < β) (i : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc α β) : |(chebyshevOn α β i).eval x| ≤ 1 := by
  simp only [chebyshevOn, eval_comp, eval_sub, eval_mul, eval_C, eval_X]
  exact Chebyshev.abs_eval_T_real_le_one _ (abs_affine_le_one hαβ hx)

/-- $\hat T_i$ is $2i^2/(\beta - \alpha)$-Lipschitz on $[\alpha, \beta]$ (Markov's inequality for
Chebyshev polynomials: $T_i' = iU_{i-1}$, $|U_{i-1}| \le i$). -/
theorem lipschitzOnWith_eval_chebyshevOn {α β : ℝ} (hαβ : α < β) (i : ℕ) :
    LipschitzOnWith (Real.toNNReal (2 * i ^ 2 / (β - α)))
      (fun x => (chebyshevOn α β i).eval x) (Set.Icc α β) := by
  have hd : 0 < β - α := sub_pos.2 hαβ
  refine (convex_Icc α β).lipschitzOnWith_of_nnnorm_deriv_le
    (fun x _ => (chebyshevOn α β i).differentiableAt) fun x hx => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity), Polynomial.deriv,
    chebyshevOn, derivative_comp, eval_mul, eval_comp]
  simp only [derivative_sub, derivative_mul, derivative_C, zero_mul, derivative_X, mul_one,
    zero_add, sub_zero, eval_C, eval_sub, eval_mul, eval_X, Real.norm_eq_abs, abs_mul,
    abs_of_pos (div_pos two_pos hd)]
  have hT := Chebyshev.abs_iterate_derivative_T_real_le (i : ℤ) 1 (abs_affine_le_one hαβ hx)
  simp only [Function.iterate_one, Chebyshev.derivative_T_eval_one, Int.cast_natCast] at hT
  rw [div_mul_eq_mul_div]
  gcongr

/-- **Chebyshev expansion of a polynomial on $[\alpha, \beta]$ with bounded coefficients**: a
real polynomial of degree at most $m$ bounded by $M$ on $[\alpha, \beta]$ is
$\sum_{i \le m} a_i\hat T_i$ with $|a_0| \le M$ and $|a_i| \le 2M$. [Trefethen2019, Thm 3.1];
the finite case of `NLAlib.chebyshevTrunc_eval`, scaled. -/
theorem exists_eq_sum_smul_chebyshevOn_of_isUniformApproxOn {α β : ℝ} (hαβ : α < β)
    {p : ℝ[X]} {m : ℕ} (hp : p.degree ≤ m) {M : ℝ}
    (hM : Metric.IsUniformApproxOn (fun x => p.eval x) (fun _ => 0) (Set.Icc α β) M) :
    ∃ a : ℕ → ℝ, p = ∑ i ∈ Finset.range (m + 1), a i • chebyshevOn α β i ∧
      |a 0| ≤ M ∧ ∀ i, 1 ≤ i → |a i| ≤ 2 * M := by
  have hd : 0 < β - α := sub_pos.2 hαβ
  set ℓ : ℝ[X] := C ((β - α) / 2) * X + C ((β + α) / 2) with hℓ
  set q := p.comp ℓ with hq
  have hqdeg : q.degree ≤ m := by
    have h := natDegree_comp_le (p := p) (q := ℓ)
    have hl : ℓ.natDegree ≤ 1 := by rw [hℓ]; compute_degree
    have hpm : p.natDegree ≤ m := natDegree_le_of_degree_le hp
    refine degree_le_natDegree.trans ?_
    exact_mod_cast h.trans (by nlinarith)
  have hqM : Metric.IsUniformApproxOn (fun t : ℝ => q.eval t) (fun _ => 0)
      (Set.Icc (-1 : ℝ) 1) M := fun t ht => by
    have hmem : (β - α) / 2 * t + (β + α) / 2 ∈ Set.Icc α β :=
      ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    simpa only [hq, eval_comp, hℓ, eval_add, eval_mul, eval_C, eval_X] using hM.apply hmem
  have h := chebyshevTrunc_eval (𝕜 := ℝ) hqdeg
  simp only [RCLike.ofReal_real_eq_id, id] at h
  refine ⟨fun i => chebyshevCoeff (fun t : ℝ => q.eval t) i, ?_, ?_, fun i _ => ?_⟩
  · refine Polynomial.funext fun x => ?_
    have hx := congrArg (eval (2 / (β - α) * x - (β + α) / (β - α))) h
    rw [eval_chebyshevTrunc] at hx
    have hinv : (β - α) / 2 * (2 / (β - α) * x - (β + α) / (β - α)) + (β + α) / 2 = x := by
      field_simp
      ring
    have hqx : q.eval (2 / (β - α) * x - (β + α) / (β - α)) = p.eval x := by
      rw [hq, eval_comp, hℓ]
      simp only [eval_add, eval_mul, eval_C, eval_X, hinv]
    rw [hqx] at hx
    rw [← hx, eval_finsetSum]
    simp only [eval_smul, smul_eq_mul, chebyshevOn, eval_comp, eval_sub, eval_mul, eval_C, eval_X]
  · simpa only [Real.norm_eq_abs] using norm_chebyshevCoeff_zero_le hqM
  · simpa only [Real.norm_eq_abs] using norm_chebyshevCoeff_le hqM i

/-- $\sum_{i<n} i^2 \le n^3/3$. -/
private theorem sum_range_sq_le (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- **Lipschitz constant of a bounded polynomial on an interval**, through its Chebyshev
expansion: a polynomial of degree at most $m$ bounded by $M$ on $[\alpha, \beta]$ is
$\frac{4}{3}(m + 1)^3 M/(\beta - \alpha)$-Lipschitz there (unoptimised; Markov's inequality
gives $2m^2M/(\beta - \alpha)$). -/
theorem lipschitzOnWith_eval_of_degree_le_of_isUniformApproxOn {α β : ℝ} (hαβ : α < β)
    {p : ℝ[X]} {m : ℕ} (hp : p.degree ≤ m) {M : ℝ}
    (hM : Metric.IsUniformApproxOn (fun x => p.eval x) (fun _ => 0) (Set.Icc α β) M) :
    LipschitzOnWith (Real.toNNReal (4 / 3 * (m + 1 : ℝ) ^ 3 * M / (β - α)))
      (fun x => p.eval x) (Set.Icc α β) := by
  have hd : 0 < β - α := sub_pos.2 hαβ
  have hM0 : 0 ≤ M := hM.nonneg ⟨α, le_rfl, hαβ.le⟩
  obtain ⟨a, hpa, ha0, ha⟩ := exists_eq_sum_smul_chebyshevOn_of_isUniformApproxOn hαβ hp hM
  have ha' : ∀ i, |a i| ≤ 2 * M := fun i => by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · linarith
    · exact ha i hi
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Real.coe_toNNReal _ (by positivity), hpa]
  simp only [eval_finsetSum, eval_smul, smul_eq_mul, Real.dist_eq, ← Finset.sum_sub_distrib,
    ← mul_sub]
  calc |∑ i ∈ Finset.range (m + 1),
        a i * ((chebyshevOn α β i).eval x - (chebyshevOn α β i).eval y)|
      ≤ ∑ i ∈ Finset.range (m + 1), 2 * M * (2 * (i : ℝ) ^ 2 / (β - α) * |x - y|) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul]
        have hL := (lipschitzOnWith_eval_chebyshevOn hαβ i).dist_le_mul x hx y hy
        rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq] at hL
        exact mul_le_mul (ha' i) hL (abs_nonneg _) (by positivity)
    _ = 4 * M * |x - y| / (β - α) * ∑ i ∈ Finset.range (m + 1), (i : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ 4 * M * |x - y| / (β - α) * ((m + 1 : ℝ) ^ 3 / 3) := by
        gcongr
        exact_mod_cast sum_range_sq_le (m + 1)
    _ = 4 / 3 * (m + 1 : ℝ) ^ 3 * M / (β - α) * |x - y| := by ring

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
Proof: `cfc_tridiagonal_firstIndex_eq_integral`, the Gauss rule of
$(\tilde{\mathbf{H}}, \tilde{\mathbf{v}})$ is exact to degree $2k - 1$ and its spectrum lies in
$I_c$ (`Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn`,
`NLAlib.LanczosData.spectrum_backwardH_subset_Icc`), and the quadratic forms of
$(\mathbf{H}, \mathbf{v}_1)$ and $(\tilde{\mathbf{H}}, \tilde{\mathbf{v}})$ differ by at most
$Lc$ (`NLAlib.LanczosData.abs_dotProduct_cfc_mulVec_sub_le_frobNorm` applied to the Lipschitz
extension of $f/L$, `LipschitzOnWith.extend_real`). [Knizhnerman1996] (bound of the form
$O(k)E_{2k-1} + O(\mathrm{poly}(k)\varepsilon)\sup|f|$, through Paige's bounds and the
Chebyshev recurrence); no printed source for this form. -/
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

/-- **Knizhnerman-type quadrature bound for bounded $f$**: as
`abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_isUniformApproxOn`, with $|f| \le M$ on
$I_c$ in place of the Lipschitz hypothesis:
$$\bigl\lvert\mathbf{v}_1^{\mathsf{T}}f(\mathbf{H})\mathbf{v}_1 - (f(\mathbf{T}_k))_{00}\bigr\rvert
\le 4\delta + 11k^3\frac{(M + \delta)\,c}{a' - a + 2c} ,$$
the Lipschitz constant of the approximating polynomial coming from its Chebyshev expansion
(`NLAlib.lipschitzOnWith_eval_of_degree_le_of_isUniformApproxOn`, $m = 2k - 1$). This is the
shape of [Knizhnerman1996] (an additive term proportional to $\sup|f|$); unoptimised. -/
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
  rw [Real.coe_toNNReal _ (div_nonneg (by positivity) (by linarith)), hcast,
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
  exact abs_eval_U_le m (abs_affine_le_one hαβ (hs hx))

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

/-- **The computed recurrence applies Chebyshev polynomials stably** ([DruskinKnizhnerman1991,
§4]; [MuscoMuscoSidford2018, Lemma 10]; Chen's thesis, Theorem 8.4): for any symmetric
three-term datum with $\mathbf{H}\mathbf{V}_k = \mathbf{V}_{k+1}\underline{\mathbf{T}}_k +
\mathbf{F}_k$ (`NLAlib.LanczosData.mul_basis`), $\operatorname{spec}\mathbf{H} \subseteq
[\alpha, \beta]$ and $\operatorname{spec}\mathbf{T}_k \subseteq [\alpha, \beta]$, for $i < k$,
$$\|\hat T_i(\mathbf{H})\mathbf{v}_1 - \mathbf{V}_k\hat T_i(\mathbf{T}_k)\mathbf{e}_0\|
\le \frac{2i(i + 1)}{\beta - \alpha}\|\mathbf{F}_k\|_2 .$$
Proof: $\mathbf{d}_i = \hat T_i(\mathbf{H})\mathbf{v}_1 -
\mathbf{V}_k\hat T_i(\mathbf{T}_k)\mathbf{e}_0$ satisfies $\mathbf{d}_0 = \mathbf{0}$ and the
perturbed Chebyshev recurrence $\mathbf{d}_{i+1} = 2\hat{\mathbf{H}}\mathbf{d}_i - \mathbf{d}_{i-1}
+ \frac{4}{\beta - \alpha}\mathbf{F}_k\hat T_i(\mathbf{T}_k)\mathbf{e}_0$ (the term
$\beta_k\mathbf{v}_{k+1}\mathbf{e}_{k-1}^{\mathsf{T}}\hat T_i(\mathbf{T}_k)\mathbf{e}_0$ vanishes
for $i < k - 1$ since $\mathbf{T}_k$ is tridiagonal), so $\mathbf{d}_i$ is a sum of
$\hat U_{i-j-1}(\mathbf{H})$ applied to the perturbations, with $\|\hat U_m(\mathbf{H})\| \le
m + 1$ and $\|\hat T_j(\mathbf{T}_k)\mathbf{e}_0\| \le 1$. No orthogonality is used. -/
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
  rw [eq_sum_aeval_U_mulVec_chebyshevRecurrenceResidual A hd0 i, WithLp.toLp_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j ∈ Finset.range i, ‖WithLp.toLp 2 (aeval A (Chebyshev.U ℝ ((i : ℤ) - 1 - j)) *ᵥ
        chebyshevRecurrenceResidual A d j)‖
      ≤ ∑ j ∈ Finset.range i, ((i : ℝ) - j) * (2 * σ * specNorm F) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [show (i : ℤ) - 1 - j = ((i - 1 - j : ℕ) : ℤ) by omega]
        refine (norm_aeval_U_mulVec_le D.isHermitian hαβ hs _ _).trans ?_
        rw [show (((i - 1 - j : ℕ) : ℝ) + 1) = (i : ℝ) - j by
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring]
        exact mul_le_mul_of_nonneg_left (hf j (by omega)) (by
          have : (j : ℝ) < i := by exact_mod_cast hj
          linarith)
    _ = 2 * i * (i + 1) / (β - α) * specNorm F := by
        rw [← Finset.sum_mul, sum_range_sub_eq, hσ]
        field_simp

/-- **The computed recurrence applies bounded polynomials stably** ([MuscoMuscoSidford2018,
Lemma 9]): for a real polynomial of degree less than $k$ bounded by $M$ on $[\alpha, \beta]$,
$$\|p(\mathbf{H})\mathbf{v}_1 - \mathbf{V}_kp(\mathbf{T}_k)\mathbf{e}_0\| \le
\frac{4}{3}k^3\frac{M}{\beta - \alpha}\|\mathbf{F}_k\|_2 ,$$
by the Chebyshev expansion $p = \sum_{i < k}a_i\hat T_i$, $|a_i| \le 2M$, and
`norm_aeval_chebyshevOn_mulVec_sub_basis_mulVec_le`
($\sum_{i<k} 2M \cdot 2i(i+1) = \frac{4}{3}M(k-1)k(k+1)$). -/
theorem norm_aeval_mulVec_sub_basis_mulVec_le_of_degree_lt {α β : ℝ} (hαβ : α < β)
    (hs : spectrum ℝ D.H ⊆ Set.Icc α β) (hT : spectrum ℝ D.tridiagonal ⊆ Set.Icc α β)
    {p : ℝ[X]} (hp : p.degree < k) {M : ℝ}
    (hM : Metric.IsUniformApproxOn (fun x => p.eval x) (fun _ => 0) (Set.Icc α β) M) :
    ‖WithLp.toLp 2 (aeval D.H p *ᵥ D.v 1 -
      D.basis *ᵥ (aeval D.tridiagonal p *ᵥ Pi.single D.firstIndex 1))‖ ≤
      4 / 3 * (k : ℝ) ^ 3 * M / (β - α) * specNorm D.residual := by
  sorry

end LanczosData

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- The first index $0 : \mathrm{Fin}\,k$ of a run. -/
def firstIndex : Fin k := L.toLanczosData.firstIndex

/-- The **width of the enlarged interval** $I_c = [a - c, a' + c]$,
$c = 2000k^4\varepsilon\|\mathbf{H}\|_2$ (`NLAlib.lanczosBackwardFactor`). -/
noncomputable def enlargement : ℝ := lanczosBackwardFactor k * L.ε * specNorm L.H

/-- **Containment of the computed Ritz values** as a spectrum inclusion: for
$\operatorname{spec}\mathbf{H} \subseteq [a, a']$,
$\operatorname{spec}\mathbf{T}_k \subseteq [a - c, a' + c]$ with
$c = 2000k^4\varepsilon\|\mathbf{H}\|_2$. The eigenpair forms are
`NLAlib.LanczosRun.eigenvalue_last_sub_le_of_mulVec_eq_smul` and
`NLAlib.LanczosRun.sub_eigenvalue_zero_le_of_mulVec_eq_smul`. -/
theorem spectrum_tridiagonal_subset_Icc {a a' : ℝ} (hs : spectrum ℝ L.H ⊆ Set.Icc a a') :
    spectrum ℝ L.tridiagonal ⊆ Set.Icc (a - L.enlargement) (a' + L.enlargement) := by
  sorry

/-! ### Quadrature -/

/-- **Knizhnerman-type quadrature bound for a Lanczos run** (continuous $f$, Lipschitz on the
enlarged interval): for $\operatorname{spec}\mathbf{H} \subseteq [a, a']$,
$c = 2000k^4\varepsilon\|\mathbf{H}\|_2$, $I_c = [a - c, a' + c]$ and $f$ $L$-Lipschitz on
$I_c$, <!-- value lanczosBackwardFactor k -->
$$\bigl\lvert\bar{\mathbf{v}}_1^{\mathsf{T}}f(\mathbf{H})\bar{\mathbf{v}}_1 -
(f(\mathbf{T}_k))_{00}\bigr\rvert \le 2E_{2k-1}(f; I_c) + 2000k^4\varepsilon\|\mathbf{H}\|_2\,L ,$$
$E_{2k-1}$ the best uniform approximation error by polynomials of degree at most $2k - 1$
(`NLAlib.minimaxError`), $\bar{\mathbf{v}}_1$ the normalised computed first vector. Compare
[Knizhnerman1996]: $O(k)E_{2k-1}(f; I_\eta) + O(\mathrm{poly}(k)\varepsilon)\sup_{I_\eta}|f|$
with Paige's $\eta$ (as summarised in Chen's thesis §8.4 and the handbook, Cor. 7.5).
Result: lanczos-quadrature-finite-precision -/
theorem abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_continuousOn {a a' : ℝ}
    (hs : spectrum ℝ L.H ⊆ Set.Icc a a') {f : ℝ → ℝ} {Lf : ℝ≥0}
    (hf : LipschitzOnWith Lf f (Set.Icc (a - L.enlargement) (a' + L.enlargement))) :
    |L.normalizedV 1 ⬝ᵥ (cfc f L.H *ᵥ L.normalizedV 1) -
        cfc f L.tridiagonal L.firstIndex L.firstIndex| ≤
      2 * minimaxError f (Set.Icc (a - L.enlargement) (a' + L.enlargement)) (2 * k - 1) +
        Lf * L.enlargement := by
  sorry

/-- **Knizhnerman-type quadrature bound, explicit rate for Lipschitz $f$** (Jackson):
<!-- value jacksonApproximationConstant -->
$$\bigl\lvert\bar{\mathbf{v}}_1^{\mathsf{T}}f(\mathbf{H})\bar{\mathbf{v}}_1 -
(f(\mathbf{T}_k))_{00}\bigr\rvert \le L\Bigl(\frac{\pi(a' - a + 2c)}{2k + 1} + c\Bigr) ,
\qquad c = 2000k^4\varepsilon\|\mathbf{H}\|_2 .$$
Result: lanczos-quadrature-finite-precision -/
theorem abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_lipschitzOnWith {a a' : ℝ}
    (haa : a < a') (hs : spectrum ℝ L.H ⊆ Set.Icc a a') {f : ℝ → ℝ} {Lf : ℝ≥0}
    (hf : LipschitzOnWith Lf f (Set.Icc (a - L.enlargement) (a' + L.enlargement))) :
    |L.normalizedV 1 ⬝ᵥ (cfc f L.H *ᵥ L.normalizedV 1) -
        cfc f L.tridiagonal L.firstIndex L.firstIndex| ≤
      Lf * (jacksonApproximationConstant * (a' - a + 2 * L.enlargement) / (2 * k + 1) +
        L.enlargement) := by
  sorry

/-- **The quadrature bound with the computed (unnormalised) first vector**: as
`abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_continuousOn`, for $\mathbf{v}_1$ itself,
at the price of $\varepsilon\sup_{I_c}|f|$ from $|\|\mathbf{v}_1\|^2 - 1| \le \varepsilon$. -/
theorem abs_dotProduct_cfc_mulVec_v_sub_cfc_tridiagonal_le_of_continuousOn {a a' : ℝ}
    (hs : spectrum ℝ L.H ⊆ Set.Icc a a') {f : ℝ → ℝ} {Lf : ℝ≥0}
    (hf : LipschitzOnWith Lf f (Set.Icc (a - L.enlargement) (a' + L.enlargement))) {M : ℝ}
    (hM : ∀ x ∈ Set.Icc (a - L.enlargement) (a' + L.enlargement), |f x| ≤ M) :
    |L.v 1 ⬝ᵥ (cfc f L.H *ᵥ L.v 1) - cfc f L.tridiagonal L.firstIndex L.firstIndex| ≤
      2 * minimaxError f (Set.Icc (a - L.enlargement) (a' + L.enlargement)) (2 * k - 1) +
        Lf * L.enlargement + L.ε * M := by
  sorry

/-! ### Lanczos-FA -/

/-- **Druskin–Knizhnerman-type Lanczos-FA bound for a Lanczos run**: for
$\operatorname{spec}\mathbf{H} \subseteq [a, a']$, $c = 2000k^4\varepsilon\|\mathbf{H}\|_2$,
$I_c = [a - c, a' + c]$, $f$ continuous on $I_c$ with $|f| \le M$ there, the computed
basis $\mathbf{V}_k$ and tridiagonal matrix $\mathbf{T}_k$ satisfy
<!-- value lanczosBackwardFactor k --> <!-- value lanczosResidualFactor k -->
$$\|f(\mathbf{H})\mathbf{v}_1 - \mathbf{V}_kf(\mathbf{T}_k)\mathbf{e}_0\| \le
(2 + \sqrt{k})\,E_{k-1}(f; I_c) + 16k^4\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2\,
\frac{M}{a' - a + 2c} .$$
Proof: $p$ the best approximation of degree less than $k$ on $I_c$ (so $|p| \le M + E_{k-1}$
there); $\|f(\mathbf{H})\mathbf{v}_1 - p(\mathbf{H})\mathbf{v}_1\| \le E_{k-1}\|\mathbf{v}_1\|$,
$\|\mathbf{V}_k(f - p)(\mathbf{T}_k)\mathbf{e}_0\| \le \|\mathbf{V}_k\|_{\mathsf{F}}E_{k-1}$ with
$\|\mathbf{V}_k\|_{\mathsf{F}} \le (1 + \varepsilon/2)\sqrt{k}$
(`NLAlib.LanczosRun.frobNorm_basis_le`) and the Ritz values in $I_c$
(`NLAlib.LanczosRun.spectrum_tridiagonal_subset_Icc`), and
`NLAlib.LanczosData.norm_aeval_mulVec_sub_basis_mulVec_le_of_degree_lt` with
$\|\mathbf{F}_k\|_2 \le 6k\sqrt{k}\varepsilon\|\mathbf{H}\|_2$
(`NLAlib.LanczosRun.specNorm_residual_le`) and $E_{k-1} \le M$. Compare
[MuscoMuscoSidford2018, Lemma 11]: $(k + 2)\delta_k + 92Ck^4n^{3/2}\|\mathbf{A}\|\epsilon_{\rm mach}
/(\lambda_{\max} - \lambda_{\min} + 2\eta)$ with Paige's $\eta \ge 85n^{3/2}k^{5/2}\|\mathbf{A}\|
\epsilon_{\rm mach}$; [DruskinKnizhnerman1991] for the method of proof.
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
  sorry

end LanczosRun

/-! ### End to end -/

/-- The tridiagonal matrix assembled from the output coefficients $\alpha_j$, $\beta_j$
(0-based, as the program writes them): $\alpha_i$ on the diagonal, $\beta_j$ at $(j + 1, j)$
and $(j, j + 1)$. -/
def lanczosOutputTridiagonal (α β : ℕ → ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if i = j then α i else if (i : ℕ) = j + 1 then β j else if (j : ℕ) = i + 1 then β i else 0

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

omit [AddMonoid C] in
/-- **The outputs of a Lanczos run satisfy the quadrature bound**: with $k$ the number of steps
before breakdown, $c = 2000k^4\varepsilon\|\mathbf{H}\|_2$ and
$\bar{\mathbf{v}}_1 = \mathbf{v}_1/\|\mathbf{v}_1\|$ the normalised computed first vector, for
every $f$ $L$-Lipschitz on $I_c = [a - c, a' + c]$ and the index $i_0 = 0$ of $\mathbf{T}_k$,
$$\bigl\lvert\bar{\mathbf{v}}_1^{\mathsf{T}}f(\mathbf{H})\bar{\mathbf{v}}_1 -
(f(\mathbf{T}_k))_{00}\bigr\rvert \le 2E_{2k-1}(f; I_c) + Lc .$$ -/
def HasLanczosQuadratureBound (st : St P K C) (p : P)
    (dec : P → K → ℝ) (u ε : ℝ) (alpha beta Q : ℕ) {N : ℕ} (q : ℕ)
    (H : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (a a' : ℝ) : Prop :=
  ∃ (α β : ℕ → ℝ) (V : ℕ → Fin N → ℝ), LanczosOutputs st p dec alpha beta Q q α β V ∧
    (∃ (c : ℝ) (δ₀ : Fin N → ℝ), 0 < c ∧ c • V 0 = b + δ₀ ∧
      ‖WithLp.toLp 2 δ₀‖ ≤ u * ‖WithLp.toLp 2 b‖) ∧
    ∀ (f : ℝ → ℝ) (Lf : ℝ≥0),
      LipschitzOnWith Lf f (Set.Icc (a - lanczosBackwardFactor (lanczosSteps β q) * ε * specNorm H)
        (a' + lanczosBackwardFactor (lanczosSteps β q) * ε * specNorm H)) →
      ∀ i₀ : Fin (lanczosSteps β q), (i₀ : ℕ) = 0 →
      |(‖WithLp.toLp 2 (V 0)‖⁻¹ • V 0) ⬝ᵥ (cfc f H *ᵥ (‖WithLp.toLp 2 (V 0)‖⁻¹ • V 0)) -
          cfc f (lanczosOutputTridiagonal α β (lanczosSteps β q)) i₀ i₀| ≤
        2 * minimaxError f
            (Set.Icc (a - lanczosBackwardFactor (lanczosSteps β q) * ε * specNorm H)
              (a' + lanczosBackwardFactor (lanczosSteps β q) * ε * specNorm H))
            (2 * lanczosSteps β q - 1) +
          Lf * (lanczosBackwardFactor (lanczosSteps β q) * ε * specNorm H)

/-- **The dense Lanczos program satisfies the Knizhnerman-type quadrature bound** (end to end):
under the hypotheses of
`NLAlib.Computation.IsRelErrSem.exists_lanczosBackwardModel_of_lanczosBasisDenseProg` and
$\operatorname{spec}\mathbf{H} \subseteq [a, a']$, the run succeeds and its outputs satisfy
`NLAlib.HasLanczosQuadratureBound` with $\varepsilon = \max(\sqrt{N}\gamma_N, \gamma_{N+4})$.
Proof: the dense bridge and
`NLAlib.LanczosRun.abs_dotProduct_cfc_mulVec_sub_cfc_tridiagonal_le_of_continuousOn`, with
`lanczosOutputTridiagonal α β k = L.tridiagonal` from the output clauses.
Result: lanczos-quadrature-finite-precision -/
theorem _root_.NLAlib.Computation.IsRelErrSem.exists_lanczosQuadratureBound_of_lanczosBasisDenseProg
    {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C) (p : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    {N : ℕ} (q : ℕ) (Hw : Fin N → Fin N → K)
    (hH : (Matrix.of fun i j => dec p (Hw i j))ᵀ = Matrix.of fun i j => dec p (Hw i j))
    {a a' : ℝ} (hs : spectrum ℝ (Matrix.of fun i j => dec p (Hw i j)) ⊆ Set.Icc a a')
    (b : Fin N → K) (hb : (fun i => dec p (b i)) ≠ 0)
    (hq : 0 < q) (hu : ((N + 4 : ℕ) : ℝ) * u p < 1)
    (hsmall : (q : ℝ) * lanczosRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p)) ≤
      1 / 100) :
    ∃ st', exec I (lanczosBasisDenseProg p (.const N) (.const q) 0 1 2 3 4).run
        (inputState p [(List.ofFn fun t : Fin (N * N) =>
            some (Hw ⟨t % N, Nat.mod_lt _ (Nat.pos_of_mul_pos_right
              (Nat.zero_lt_of_lt t.2))⟩ ⟨t / N, Nat.div_lt_of_lt_mul t.2⟩)).toArray,
          (List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
          Array.replicate q none, Array.replicate (N * (q + 1)) none]) = some st' ∧
      HasLanczosQuadratureBound st' p dec (u p)
        (lanczosRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p))) 2 3 4 q
        (Matrix.of fun i j => dec p (Hw i j)) (fun i => dec p (b i)) a a' := by
  sorry

end NLAlib
