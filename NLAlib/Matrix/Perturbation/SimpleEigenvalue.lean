/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Topology.Instances.Matrix
public import NLAlib.Matrix.Perturbation.Residual
public import NLAlib.Matrix.Spectral.Weyl

/-!
# First-order perturbation of a simple eigenvalue

A simple eigenvalue moves differentiably under a perturbation `A + t • E`, with derivative
`yᴴ E x / yᴴ x` for right and left eigenvectors `x`, `y`. For a Hermitian matrix the sorted
eigenvalue `eigenvalue (A + t • E) k` itself is differentiable at `t = 0` when `eigenvalue A k` is
simple, with derivative `xᴴ E x` for a unit eigenvector: no branch has to be chosen.

## Main results

* `Matrix.IsHermitian.hasDerivAt_eigenvalue_add_smul`: the Hermitian case.
* `NLAlib.hasDerivAt_of_isRoot_charpoly_add_smul`: every continuous eigenvalue branch through a
  simple eigenvalue of a complex matrix has derivative `yᵀ E x / yᵀ x`.
* `NLAlib.exists_eigenvalue_branch_of_rootMultiplicity_eq_one`: a differentiable branch through a
  simple eigenvalue of a complex matrix.
-/

@[expose] public section

open scoped Matrix Topology

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Hermitian matrices -/

omit [DecidableEq n] in
/-- The second-order remainder in the Hermitian case: for `t` small,
`|λ_k(A + t E) - λ_k(A) - t xᴴ E x| δ ≤ t² ‖E‖₂²`, where `δ` is half the distance from
`eigenvalue A k` to the rest of the spectrum.
[Parlett1998, Theorem 11.7.1 applied to the Rayleigh quotient of `x`]. -/
theorem _root_.Matrix.IsHermitian.abs_eigenvalue_add_smul_sub_mul_le {A E : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i, i < Fintype.card n → i ≠ k → 2 * δ ≤ |eigenvalue A i - eigenvalue A k|)
    {x : n → 𝕜} (hx : ‖WithLp.toLp 2 x‖ = 1) (hAx : A *ᵥ x = eigenvalue A k • x) {t : ℝ}
    (ht : |t| * specNorm E < δ / 2) :
    |eigenvalue (A + t • E) k - eigenvalue A k - t * RCLike.re (star x ⬝ᵥ E *ᵥ x)| * δ ≤
      t ^ 2 * specNorm E ^ 2 := by
  have hB : (A + t • E).IsHermitian := hA.add (hE.smul (IsSelfAdjoint.all t))
  have hweyl (i : ℕ) : |eigenvalue (A + t • E) i - eigenvalue A i| ≤ |t| * specNorm E := by
    have h := abs_eigenvalue_sub_le hB hA i
    rwa [add_sub_cancel_left, specNorm_real_smul] at h
  have hq : RCLike.re (quadForm A x) = eigenvalue A k := by
    rw [quadForm_def, hAx, dotProduct_smul, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq,
      hx, one_pow, RCLike.ofReal_one, RCLike.real_smul_eq_coe_mul, mul_one, RCLike.ofReal_re]
  have hρ : rayleighQuotient (A + t • E) x =
      eigenvalue A k + t * RCLike.re (star x ⬝ᵥ E *ᵥ x) := by
    rw [rayleighQuotient_of_norm_eq_one _ hx, quadForm_add_left,
      RCLike.real_smul_eq_coe_smul (K := 𝕜), quadForm_smul_left, map_add, RCLike.re_ofReal_mul,
      hq, quadForm_def]
  have hEx : |t * RCLike.re (star x ⬝ᵥ E *ᵥ x)| ≤ |t| * specNorm E := by
    have h := abs_re_quadForm_le E x
    rw [hx, one_pow, mul_one, quadForm_def] at h
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg t)
  have hres : ‖WithLp.toLp 2 ((A + t • E) *ᵥ x - rayleighQuotient (A + t • E) x • x)‖ ≤
      |t| * specNorm E := by
    refine (hB.norm_mulVec_sub_rayleighQuotient_smul_le x (eigenvalue A k)).trans ?_
    have e : (A + t • E) *ᵥ x - eigenvalue A k • x = t • (E *ᵥ x) := by
      rw [Matrix.add_mulVec, hAx, Matrix.smul_mulVec, add_sub_cancel_left]
    rw [e, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)
    exact (norm_toLp_mulVec_le E x).trans_eq (by rw [hx, mul_one])
  have hℓ : |eigenvalue (A + t • E) k - rayleighQuotient (A + t • E) x| < δ := by
    rw [hρ]
    have h₁ := abs_le.mp (hweyl k)
    have h₂ := abs_le.mp hEx
    rw [abs_lt]
    constructor <;> linarith
  have hiso : ∀ i, i < Fintype.card n →
      |eigenvalue (A + t • E) i - rayleighQuotient (A + t • E) x| < δ →
        eigenvalue (A + t • E) i = eigenvalue (A + t • E) k := by
    intro i hi hlt
    by_cases hik : i = k
    · rw [hik]
    · exfalso
      rw [hρ, abs_lt] at hlt
      have h₁ := abs_le.mp (hweyl i)
      have h₂ := abs_le.mp hEx
      rcases le_abs.mp (hsep i hi hik) with h | h <;> linarith
  have h := hB.abs_sub_rayleighQuotient_mul_le_norm_sq hx hδ hℓ hiso
  calc |eigenvalue (A + t • E) k - eigenvalue A k - t * RCLike.re (star x ⬝ᵥ E *ᵥ x)| * δ
      = |eigenvalue (A + t • E) k - rayleighQuotient (A + t • E) x| * δ := by rw [hρ, sub_sub]
    _ ≤ ‖WithLp.toLp 2 ((A + t • E) *ᵥ x - rayleighQuotient (A + t • E) x • x)‖ ^ 2 := h
    _ ≤ (|t| * specNorm E) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hres 2
    _ = t ^ 2 * specNorm E ^ 2 := by rw [mul_pow, sq_abs]

omit [DecidableEq n] in
/-- **First-order perturbation of a simple eigenvalue of a Hermitian matrix.** If `A` and `E` are
Hermitian, `eigenvalue A k` is a simple eigenvalue of `A` and `x` is a unit eigenvector for it,
then `t ↦ eigenvalue (A + t • E) k` has derivative `re (xᴴ E x)` at `0`.
[StewartSun1990, Theorem IV.2.3]; [Kato1995, §II.6.4]. -/
theorem _root_.Matrix.IsHermitian.hasDerivAt_eigenvalue_add_smul {A E : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hE : E.IsHermitian) {k : ℕ}
    (hsimple : ∀ i, i < Fintype.card n → i ≠ k → eigenvalue A i ≠ eigenvalue A k)
    {x : n → 𝕜} (hx : ‖WithLp.toLp 2 x‖ = 1) (hAx : A *ᵥ x = eigenvalue A k • x) :
    HasDerivAt (fun t : ℝ => eigenvalue (A + t • E) k) (RCLike.re (star x ⬝ᵥ E *ᵥ x)) 0 := by
  obtain ⟨δ, hδ, hsep⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, i < Fintype.card n → i ≠ k →
      2 * δ ≤ |eigenvalue A i - eigenvalue A k| := by
    rcases ((Finset.range (Fintype.card n)).erase k).eq_empty_or_nonempty with h | h
    · refine ⟨1, one_pos, fun i hi hik => absurd
        (Finset.mem_erase.mpr ⟨hik, Finset.mem_range.mpr hi⟩) ?_⟩
      rw [h]
      exact Finset.notMem_empty i
    · obtain ⟨i₀, hi₀, hmin⟩ :=
        Finset.exists_min_image _ (fun i => |eigenvalue A i - eigenvalue A k|) h
      rw [Finset.mem_erase, Finset.mem_range] at hi₀
      refine ⟨|eigenvalue A i₀ - eigenvalue A k| / 2,
        half_pos (abs_pos.mpr (sub_ne_zero.mpr (hsimple i₀ hi₀.2 hi₀.1))), fun i hi hik => ?_⟩
      rw [mul_div_cancel₀ _ two_ne_zero]
      exact hmin i (Finset.mem_erase.mpr ⟨hik, Finset.mem_range.mpr hi⟩)
  rw [hasDerivAt_iff_isLittleO]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun t : ℝ => t ^ 2) ?_ ?_
  · refine Asymptotics.IsBigO.of_bound (specNorm E ^ 2 / δ) ?_
    have hev : ∀ᶠ t : ℝ in 𝓝 0, |t| * specNorm E < δ / 2 := by
      have hc : ContinuousAt (fun t : ℝ => |t| * specNorm E) 0 := by fun_prop
      exact hc.eventually_lt continuousAt_const (by simpa using half_pos hδ)
    filter_upwards [hev] with t ht
    have h := hA.abs_eigenvalue_add_smul_sub_mul_le hE hδ hsep hx hAx ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, zero_smul, add_zero, sub_zero, smul_eq_mul, abs_pow,
      sq_abs, div_mul_eq_mul_div, le_div_iff₀ hδ, mul_comm (specNorm E ^ 2)]
    exact h
  · simpa using Asymptotics.isLittleO_pow_id (𝕜 := ℝ) one_lt_two

/-! ### General complex matrices -/

/-- Pairing with a left eigenvector turns powers of the shifted matrix into scalar powers. -/
private theorem dotProduct_sub_smul_one_pow_mulVec {A : Matrix n n ℂ} {y : n → ℂ} {α : ℂ}
    (hy : y ᵥ* A = α • y) (μ : ℂ) (k : ℕ) (z : n → ℂ) :
    y ⬝ᵥ ((A - μ • (1 : Matrix n n ℂ)) ^ k *ᵥ z) = (α - μ) ^ k * (y ⬝ᵥ z) := by
  have hshift : y ᵥ* (A - μ • (1 : Matrix n n ℂ)) = (α - μ) • y := by
    rw [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, hy, sub_smul]
  induction k with
  | zero => simp only [pow_zero, Matrix.one_mulVec, one_mul]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hshift, smul_dotProduct,
      smul_eq_mul, ih, pow_succ', mul_assoc]

/-- A left eigenvector annihilates the generalized eigenspaces of the other eigenvalues. -/
private theorem dotProduct_eq_zero_of_mem_maxGenEigenspace {A : Matrix n n ℂ} {y z : n → ℂ}
    {α μ : ℂ} (hy : y ᵥ* A = α • y) (hαμ : α ≠ μ)
    (hz : z ∈ Module.End.maxGenEigenspace A.toLin' μ) : y ⬝ᵥ z = 0 := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace A.toLin' μ z).mp hz
  have hkM : (A - μ • (1 : Matrix n n ℂ)) ^ k *ᵥ z = 0 := by
    have e : ((A - μ • (1 : Matrix n n ℂ)) ^ k).toLin' = (A.toLin' - μ • 1) ^ k := by
      rw [Matrix.toLin'_pow, map_sub, map_smul, Matrix.toLin'_one]
      rfl
    rw [← Matrix.toLin'_apply, e]
    exact hk
  have hpair := dotProduct_sub_smul_one_pow_mulVec hy μ k z
  rw [hkM, dotProduct_zero] at hpair
  exact (mul_eq_zero.mp hpair.symm).resolve_left (pow_ne_zero k (sub_ne_zero.mpr hαμ))

/-- The generalized eigenspace of a simple root of the characteristic polynomial is the line
through an eigenvector. -/
private theorem span_singleton_eq_maxGenEigenspace {A : Matrix n n ℂ} {x : n → ℂ} {μ : ℂ}
    (hx : x ≠ 0) (hAx : A *ᵥ x = μ • x) (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ℂ ∙ x = Module.End.maxGenEigenspace A.toLin' μ := by
  have hdim : Module.finrank ℂ (Module.End.maxGenEigenspace A.toLin' μ) = 1 := by
    rw [LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin', hμ]
  have hxgen : x ∈ Module.End.maxGenEigenspace A.toLin' μ :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hAx)
  exact Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem x _).mpr hxgen)
    (by rw [finrank_span_singleton hx, hdim])

/-- The eigenspace of a simple root of the characteristic polynomial is a line. -/
private theorem exists_eq_smul_of_rootMultiplicity_eq_one {A : Matrix n n ℂ} {x : n → ℂ} {μ : ℂ}
    (hx : x ≠ 0) (hAx : A *ᵥ x = μ • x) (hμ : A.charpoly.rootMultiplicity μ = 1) {v : n → ℂ}
    (hv : A *ᵥ v = μ • v) : ∃ c : ℂ, v = c • x := by
  have h : v ∈ Module.End.maxGenEigenspace A.toLin' μ :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hv)
  rw [← span_singleton_eq_maxGenEigenspace hx hAx hμ, Submodule.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.symm⟩

/-- For a simple eigenvalue the left and right eigenvectors are not orthogonal: `yᵀ x ≠ 0`.
[HornJohnson2013, Lemma 6.3.10].
Port of `NLAlib.dotProduct_ne_zero_of_simple_eigenvalue`, there over any algebraically closed
field. -/
theorem dotProduct_ne_zero_of_rootMultiplicity_eq_one {A : Matrix n n ℂ} {x y : n → ℂ} {μ : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1) : y ⬝ᵥ x ≠ 0 := by
  intro hpair
  let ℓ : (n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun z := y ⬝ᵥ z
      map_add' _ _ := dotProduct_add _ _ _
      map_smul' c z := by rw [dotProduct_smul]; rfl }
  have hgen (ν : ℂ) : Module.End.maxGenEigenspace A.toLin' ν ≤ ℓ.ker := by
    by_cases hν : ν = μ
    · rw [hν, ← span_singleton_eq_maxGenEigenspace hx hAx hμ]
      exact (Submodule.span_singleton_le_iff_mem x _).mpr hpair
    · exact fun z hz => dotProduct_eq_zero_of_mem_maxGenEigenspace hyA (Ne.symm hν) hz
  have htop : (⊤ : Submodule ℂ (n → ℂ)) ≤ ℓ.ker := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top A.toLin']
    exact iSup_le hgen
  refine hy (funext fun i => ?_)
  have hi : Pi.single i 1 ∈ ℓ.ker := htop Submodule.mem_top
  simpa only [ℓ, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_single, mul_one,
    Pi.zero_apply] using hi

/-- The matrix `μ • 1 - A`, bordered by the rank-one matrix of the two eigenvectors of a simple
eigenvalue `μ`, is invertible. -/
private theorem det_smul_one_sub_add_smul_vecMulVec_ne_zero {A : Matrix n n ℂ} {x y : n → ℂ}
    {μ : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1) :
    (μ • (1 : Matrix n n ℂ) - A + (y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y).det ≠ 0 := by
  have ha := dotProduct_ne_zero_of_rootMultiplicity_eq_one hx hy hAx hyA hμ
  intro hdet
  obtain ⟨w, hw, hKw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul] at hKw
  have hyw : y ⬝ᵥ w = 0 := by
    have h := congrArg (fun v => y ⬝ᵥ v) hKw
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, Matrix.dotProduct_mulVec, hyA,
      smul_dotProduct, smul_eq_mul, dotProduct_zero, sub_self, zero_add] at h
    rwa [mul_comm (y ⬝ᵥ w), inv_mul_cancel_left₀ ha] at h
  rw [hyw, zero_smul, smul_zero, add_zero, sub_eq_zero] at hKw
  obtain ⟨c, rfl⟩ := exists_eq_smul_of_rootMultiplicity_eq_one hx hAx hμ hKw.symm
  rw [dotProduct_smul, smul_eq_mul, mul_eq_zero] at hyw
  rcases hyw with hc | hc
  · exact hw (by rw [hc, zero_smul])
  · exact ha hc

/-- If `M` is singular and its rank-one update `K = M + c • x yᵀ` is not, then `adj K x` is in
the kernel of `M`. -/
private theorem mulVec_adjugate_add_smul_vecMulVec_mulVec {M : Matrix n n ℂ} (hM : M.det = 0)
    {c : ℂ} {x y : n → ℂ} (hK : (M + c • Matrix.vecMulVec x y).det ≠ 0) :
    M *ᵥ ((M + c • Matrix.vecMulVec x y).adjugate *ᵥ x) = 0 := by
  obtain ⟨w, hw, hMw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hM
  have hKw : (M + c • Matrix.vecMulVec x y) *ᵥ w = (c * (y ⬝ᵥ w)) • x := by
    rw [Matrix.add_mulVec, hMw, zero_add, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      op_smul_eq_smul, smul_smul]
  have h₁ : (M + c • Matrix.vecMulVec x y).det • w =
      (c * (y ⬝ᵥ w)) • ((M + c • Matrix.vecMulVec x y).adjugate *ᵥ x) := by
    rw [← Matrix.mulVec_smul, ← hKw, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hc : c * (y ⬝ᵥ w) ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h₁
    exact hw ((smul_eq_zero.mp h₁).resolve_left hK)
  have h := congrArg (fun v => M *ᵥ v) h₁
  simp only [Matrix.mulVec_smul, hMw, smul_zero] at h
  exact (smul_eq_zero.mp h.symm).resolve_left hc

/-- **Every continuous eigenvalue branch through a simple eigenvalue is differentiable.** Let `μ`
be a simple root of the characteristic polynomial of the complex matrix `A`, with right
eigenvector `x` and left eigenvector `y` (`y ᵥ* A = μ • y`). If `φ` is continuous at `0`,
`φ 0 = μ`, and `φ t` is an eigenvalue of `A + t • E` for `t` near `0` (a root of the
characteristic polynomial; see `Matrix.mem_spectrum_iff_isRoot_charpoly`), then `φ` has derivative
`yᵀ E x / yᵀ x` at `0`. Only continuity at the base point is assumed of `φ`, so this applies to
any selection of eigenvalues, not only to the branch of
`NLAlib.exists_eigenvalue_branch_of_rootMultiplicity_eq_one`.
[StewartSun1990, Theorem IV.2.3]; [HornJohnson2013, Theorem 6.3.12].
Result: simple-eigenvalue-perturbation -/
theorem hasDerivAt_of_isRoot_charpoly_add_smul {A : Matrix n n ℂ} (E : Matrix n n ℂ)
    {x y : n → ℂ} {μ : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x)
    (hyA : y ᵥ* A = μ • y) (hμ : A.charpoly.rootMultiplicity μ = 1) {φ : ℂ → ℂ} (hφ₀ : φ 0 = μ)
    (hφc : ContinuousAt φ 0) (hφ : ∀ᶠ t in 𝓝 0, (A + t • E).charpoly.IsRoot (φ t)) :
    HasDerivAt φ (y ⬝ᵥ E *ᵥ x / y ⬝ᵥ x) 0 := by
  have ha := dotProduct_ne_zero_of_rootMultiplicity_eq_one hx hy hAx hyA hμ
  -- The bordered matrix `K t` is invertible near `0`, and `u t` spans the kernel of
  -- `φ t • 1 - (A + t • E)` there.
  let K : ℂ → Matrix n n ℂ := fun t =>
    φ t • (1 : Matrix n n ℂ) - (A + t • E) + (y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y
  let u : ℂ → n → ℂ := fun t => (K t).adjugate *ᵥ x
  have hKc : ContinuousAt K 0 :=
    ((hφc.smul continuousAt_const).sub (by fun_prop)).add continuousAt_const
  have huc : ContinuousAt u 0 :=
    ((continuous_id.matrix_adjugate.matrix_mulVec continuous_const).continuousAt
      (x := K 0)).comp hKc
  have hK₀ : K 0 = μ • (1 : Matrix n n ℂ) - A + (y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y := by
    simp only [K, hφ₀, zero_smul, add_zero]
  have hdet₀ : (K 0).det ≠ 0 := by
    rw [hK₀]
    exact det_smul_one_sub_add_smul_vecMulVec_ne_zero hx hy hAx hyA hμ
  have hu₀ : u 0 = (K 0).det • x := by
    have hKx : K 0 *ᵥ x = x := by
      rw [hK₀, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, hAx, sub_self, zero_add,
        smul_smul, inv_mul_cancel₀ ha, one_smul]
    calc u 0 = (K 0).adjugate *ᵥ (K 0 *ᵥ x) := by rw [hKx]
      _ = (K 0).det • x := by
        rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hdet : ∀ᶠ t in 𝓝 0, (K t).det ≠ 0 :=
    (((continuous_id.matrix_det (R := ℂ) (n := n)).continuousAt (x := K 0)).comp
      hKc).eventually_ne hdet₀
  have hyuc : ContinuousAt (fun t => y ⬝ᵥ u t) 0 :=
    ((continuous_const.dotProduct continuous_id).continuousAt (x := u 0)).comp huc
  have hyEuc : ContinuousAt (fun t => y ⬝ᵥ E *ᵥ u t) 0 :=
    ((continuous_const.dotProduct (continuous_const.matrix_mulVec continuous_id)).continuousAt
      (x := u 0)).comp huc
  have hyu₀ : y ⬝ᵥ u 0 ≠ 0 := by
    rw [hu₀, dotProduct_smul, smul_eq_mul]
    exact mul_ne_zero hdet₀ ha
  have hyu : ∀ᶠ t in 𝓝 0, y ⬝ᵥ u t ≠ 0 := hyuc.eventually_ne hyu₀
  have hkey : ∀ᶠ t in 𝓝 0, (φ t - μ) * (y ⬝ᵥ u t) = t * (y ⬝ᵥ E *ᵥ u t) := by
    filter_upwards [hφ, hdet] with t hroot hdK
    have hM : (φ t • (1 : Matrix n n ℂ) - (A + t • E)).det = 0 := by
      rw [Matrix.smul_one_eq_diagonal, ← Matrix.scalar_apply, ← Matrix.eval_charpoly]
      exact hroot
    have h := congrArg (fun v => y ⬝ᵥ v) (mulVec_adjugate_add_smul_vecMulVec_mulVec hM hdK)
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_zero, smul_eq_mul] at h
    have hyAu : y ⬝ᵥ A *ᵥ u t = μ * (y ⬝ᵥ u t) := by
      rw [Matrix.dotProduct_mulVec, hyA, smul_dotProduct, smul_eq_mul]
    rw [hyAu] at h
    linear_combination h
  rw [hasDerivAt_iff_tendsto_slope]
  have hq : Filter.Tendsto (fun t => y ⬝ᵥ E *ᵥ u t / y ⬝ᵥ u t) (𝓝[≠] 0)
      (𝓝 (y ⬝ᵥ E *ᵥ x / y ⬝ᵥ x)) := by
    have h : Filter.Tendsto (fun t => y ⬝ᵥ E *ᵥ u t / y ⬝ᵥ u t) (𝓝[≠] 0)
        (𝓝 (y ⬝ᵥ E *ᵥ u 0 / y ⬝ᵥ u 0)) :=
      (hyEuc.div hyuc hyu₀).tendsto.mono_left nhdsWithin_le_nhds
    rwa [hu₀, Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      mul_div_mul_left _ _ hdet₀] at h
  refine hq.congr' ?_
  filter_upwards [nhdsWithin_le_nhds hkey, nhdsWithin_le_nhds hyu, self_mem_nhdsWithin]
    with t h₁ h₂ ht
  rw [slope_def_field, hφ₀, sub_zero, div_eq_div_iff h₂ ht]
  linear_combination -h₁

/-- The function `(t, z) ↦ det (z • 1 - (A + t • E))` is continuously differentiable. -/
private theorem contDiff_eval_charpoly_add_smul (A E : Matrix n n ℂ) :
    ContDiff ℂ 1 fun p : ℂ × ℂ => (A + p.1 • E).charpoly.eval p.2 := by
  simp only [Matrix.eval_charpoly, Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> fun_prop

/-- The derivative of `(t, z) ↦ det (z • 1 - (A + t • E))` in the direction of `z` is the
derivative of the characteristic polynomial. -/
private theorem fderiv_eval_charpoly_add_smul_apply (A E : Matrix n n ℂ) (p : ℂ × ℂ) :
    fderiv ℂ (fun p : ℂ × ℂ => (A + p.1 • E).charpoly.eval p.2) p (0, 1) =
      (A + p.1 • E).charpoly.derivative.eval p.2 := by
  have hf := ((contDiff_eval_charpoly_add_smul A E).differentiable one_ne_zero p).hasFDerivAt
  have hg : HasDerivAt (fun z : ℂ => (p.1, z)) ((0 : ℂ), (1 : ℂ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (hf.comp_hasDerivAt p.2 hg).unique ((A + p.1 • E).charpoly.hasDerivAt p.2)

/-- A root of a nonzero polynomial at which the derivative does not vanish is simple. -/
private theorem rootMultiplicity_eq_one_of_isRoot_of_derivative_ne_zero {q : Polynomial ℂ}
    (hq : q ≠ 0) {z : ℂ} (hz : q.IsRoot z) (hd : q.derivative.eval z ≠ 0) :
    q.rootMultiplicity z = 1 := by
  have hpos := (Polynomial.rootMultiplicity_pos hq).mpr hz
  have hle : q.rootMultiplicity z ≤ 1 := by
    by_contra! hgt
    exact hd ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hq).mp hgt).2
  omega

/-- The implicit function of the product-domain implicit function theorem is continuous on a
neighbourhood of the base point. -/
private theorem eventually_continuousAt_implicitFunctionOfProdDomain {f : ℂ × ℂ → ℂ}
    {f' : ℂ × ℂ →L[ℂ] ℂ} {u : ℂ × ℂ} (hf : HasStrictFDerivAt f f' u)
    (hf' : (f' ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible) :
    ∀ᶠ t in 𝓝 u.1, ContinuousAt (hf.implicitFunctionOfProdDomain hf') t := by
  have h₀ := (hf.implicitFunctionDataOfProdDomain hf').map_pt_mem_toOpenPartialHomeomorph_target
  rw [HasStrictFDerivAt.pt_implicitFunctionDataOfProdDomain,
    HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain,
    HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain] at h₀
  have htarget : ∀ᶠ t in 𝓝 u.1,
      (f u, t) ∈ (hf.implicitFunctionDataOfProdDomain hf').toOpenPartialHomeomorph.target :=
    (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
      ((hf.implicitFunctionDataOfProdDomain hf').toOpenPartialHomeomorph.open_target.mem_nhds h₀)
  filter_upwards [htarget] with t ht
  rw [HasStrictFDerivAt.implicitFunctionOfProdDomain_def]
  simp only [ImplicitFunctionData.implicitFunction_apply]
  exact (((hf.implicitFunctionDataOfProdDomain hf').toOpenPartialHomeomorph.symm.continuousAt
    ht).comp (continuousAt_const.prodMk continuousAt_id)).snd

/-- **A differentiable branch through a simple eigenvalue.** Let `μ` be a simple root of the
characteristic polynomial of the complex matrix `A`, with right eigenvector `x` and left
eigenvector `y`. Then there is a function `φ` with `φ 0 = μ`, derivative `yᵀ E x / yᵀ x` at `0`,
such that near `(0, μ)` the eigenvalues of `A + t • E` close to `μ` are exactly `φ t`, and they
remain simple. The left eigenvector enters through the bilinear product `yᵀ x`, with
`y ᵥ* A = μ • y`; for Hermitian `A` take `y = star x` to recover the derivative `xᴴ E x`.
[StewartSun1990, Theorem IV.2.3]; [HornJohnson2013, Theorem 6.3.12].
Port of `NLAlib.exists_eigenvalue_branch_of_simple_with_multiplicity`.
Result: simple-eigenvalue-perturbation -/
theorem exists_eigenvalue_branch_of_rootMultiplicity_eq_one {A : Matrix n n ℂ}
    (E : Matrix n n ℂ) {x y : n → ℂ} {μ : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (hAx : A *ᵥ x = μ • x)
    (hyA : y ᵥ* A = μ • y) (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ∃ φ : ℂ → ℂ, φ 0 = μ ∧ HasDerivAt φ (y ⬝ᵥ E *ᵥ x / y ⬝ᵥ x) 0 ∧
      (∀ᶠ t in 𝓝 0, ContinuousAt φ t) ∧
      (∀ᶠ p : ℂ × ℂ in 𝓝 (0, μ), p.2 ∈ spectrum ℂ (A + p.1 • E) ↔ φ p.1 = p.2) ∧
      ∀ᶠ t in 𝓝 0, (A + t • E).charpoly.rootMultiplicity (φ t) = 1 := by
  have hp : A.charpoly ≠ 0 := A.charpoly_monic.ne_zero
  have hroot : A.charpoly.IsRoot μ := (Polynomial.rootMultiplicity_pos hp).mp (by omega)
  have hder : A.charpoly.derivative.eval μ ≠ 0 := fun h0 => by
    have h := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hroot, h0⟩
    omega
  have hFc := contDiff_eval_charpoly_add_smul A E
  have hF := hFc.hasStrictFDerivAt (x := ((0 : ℂ), μ)) one_ne_zero
  have hF₀ : (A + ((0 : ℂ), μ).1 • E).charpoly.eval ((0 : ℂ), μ).2 = 0 := by
    rw [zero_smul, add_zero]
    exact hroot
  have hinv : (fderiv ℂ (fun p : ℂ × ℂ => (A + p.1 • E).charpoly.eval p.2) (0, μ) ∘L
      ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible := by
    have hc : (fderiv ℂ (fun p : ℂ × ℂ => (A + p.1 • E).charpoly.eval p.2) (0, μ) ∘L
        ContinuousLinearMap.inr ℂ ℂ ℂ) 1 = A.charpoly.derivative.eval μ := by
      have h := fderiv_eval_charpoly_add_smul_apply A E (0, μ)
      rw [zero_smul, add_zero] at h
      exact h
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := (A.charpoly.derivative.eval μ)⁻¹ • ContinuousLinearMap.id ℂ ℂ) ?_ ?_
    · refine ContinuousLinearMap.ext_ring ?_
      simp [hc, hder]
    · refine ContinuousLinearMap.ext_ring ?_
      simp [hc, hder]
  have hiff := hF.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  have hφ₀ : hF.implicitFunctionOfProdDomain hinv 0 = μ := hiff.self_of_nhds.mp rfl
  have hφc : ContinuousAt (hF.implicitFunctionOfProdDomain hinv) 0 :=
    (hF.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).continuousAt
  have hφroot : ∀ᶠ t in 𝓝 (0 : ℂ),
      (A + t • E).charpoly.IsRoot (hF.implicitFunctionOfProdDomain hinv t) := by
    filter_upwards [hF.eventually_apply_implicitFunctionOfProdDomain hinv] with t ht
    exact ht.trans hF₀
  refine ⟨hF.implicitFunctionOfProdDomain hinv, hφ₀,
    hasDerivAt_of_isRoot_charpoly_add_smul E hx hy hAx hyA hμ hφ₀ hφc hφroot,
    eventually_continuousAt_implicitFunctionOfProdDomain hF hinv, ?_, ?_⟩
  · filter_upwards [hiff] with p hp
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, ← hp, hF₀]
    rfl
  · have hG : Continuous fun p : ℂ × ℂ => (A + p.1 • E).charpoly.derivative.eval p.2 := by
      have h := (hFc.continuous_fderiv one_ne_zero).clm_apply
        (continuous_const (y := ((0 : ℂ), (1 : ℂ))))
      simpa only [fderiv_eval_charpoly_add_smul_apply] using h
    have hne : ∀ᶠ t in 𝓝 (0 : ℂ), (A + t • E).charpoly.derivative.eval
        (hF.implicitFunctionOfProdDomain hinv t) ≠ 0 := by
      have hc : ContinuousAt (fun t : ℂ => (A + t • E).charpoly.derivative.eval
          (hF.implicitFunctionOfProdDomain hinv t)) 0 :=
        ContinuousAt.comp (f := fun t : ℂ => (t, hF.implicitFunctionOfProdDomain hinv t))
          hG.continuousAt (continuousAt_id.prodMk hφc)
      refine hc.eventually_ne ?_
      rw [zero_smul, add_zero, hφ₀]
      exact hder
    filter_upwards [hφroot, hne] with t ht hdt
    exact rootMultiplicity_eq_one_of_isRoot_of_derivative_ne_zero
      (A + t • E).charpoly_monic.ne_zero ht hdt

end NLAlib
