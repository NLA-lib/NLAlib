/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.CStarAlgebra.Matrix
public import NLAlib.Matrix.Functions.Exponential
public import NLAlib.Matrix.Spectral.HermitianPart
public import NLAlib.Matrix.Spectral.CourantFischer
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Sharp growth of matrix exponential semigroups

The Hermitian part controls the Euclidean energy of each orbit of a real or complex
matrix. Nonnormal and defective generators are allowed.

## Main results

* `NLAlib.forall_specNorm_exp_smul_le_iff`: the semigroup bound and generator order bound.
* `NLAlib.isLeast_specNorm_exp_smul_le`: the smallest growth exponent.
-/

@[expose] public section
open Matrix Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology

namespace NLAlib
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

private noncomputable local instance : NormedAlgebra ℝ (Matrix n n 𝕜) :=
  Matrix.l2OpNormedAlgebraReal

/-- Each Euclidean orbit of a matrix exponential solves the associated
constant-coefficient differential equation. -/
private theorem hasDerivAt_exp_orbit (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • A)).toEuclideanLin x)
      (A.toEuclideanLin ((NormedSpace.exp (t • A)).toEuclideanLin x)) t := by
  let L : Matrix n n 𝕜 →ₗ[ℝ] EuclideanSpace 𝕜 n :=
    ((LinearMap.applyₗ x).comp Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ
  have h := (L.toContinuousLinearMap.hasFDerivAt (x := NormedSpace.exp (t • A))).comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' A t)
  convert! h using 1
  change WithLp.toLp 2 (A *ᵥ ((NormedSpace.exp (t • A)) *ᵥ x.ofLp)) =
    WithLp.toLp 2 ((A * NormedSpace.exp (t • A)) *ᵥ x.ofLp)
  rw [Matrix.mulVec_mulVec]

/-- The exponential inherits every uniform upper bound on the real
quadratic form of its generator. The constant may be negative. -/
private theorem specNorm_exp_smul_le_of_energy (A : Matrix n n 𝕜) (c : ℝ)
    (hA : ∀ x : EuclideanSpace 𝕜 n,
      inner ℝ x (A.toEuclideanLin x) ≤ c * ‖x‖ ^ 2)
    {t : ℝ} (ht : 0 ≤ t) : specNorm (NormedSpace.exp (t • A)) ≤ Real.exp (t * c) := by
  have horbit (x : EuclideanSpace 𝕜 n) :
      ‖(NormedSpace.exp (t • A) : Matrix n n 𝕜).toEuclideanLin x‖ ≤
        Real.exp (t * c) * ‖x‖ := by
    let L : Matrix n n 𝕜 →ₗ[ℝ] EuclideanSpace 𝕜 n :=
      ((LinearMap.applyₗ x).comp Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ
    let z (s : ℝ) := L (NormedSpace.exp (s • A))
    have hz (s : ℝ) : HasDerivAt z (A.toEuclideanLin (z s)) s := by
      exact hasDerivAt_exp_orbit A x s
    let F (s : ℝ) := Real.exp (-2 * c * s) * ‖z s‖ ^ 2
    let D (s : ℝ) := Real.exp (-2 * c * s) *
      (2 * inner ℝ (z s) (A.toEuclideanLin (z s)) - 2 * c * ‖z s‖ ^ 2)
    have hF (s : ℝ) : HasDerivAt F (D s) s := by
      have h := (((hasDerivAt_id s).const_mul (-2 * c)).exp).mul (hz s).norm_sq
      convert! h using 1
      dsimp [D]
      ring
    have hanti : Antitone F := antitone_of_hasDerivAt_nonpos hF (fun s => by
      dsimp [D]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by nlinarith [hA (z s)]))
    have he := hanti ht
    have hz0 : z 0 = x := by
      change (NormedSpace.exp ((0 : ℝ) • A) : Matrix n n 𝕜).toEuclideanLin x = x
      simp [Matrix.toEuclideanLin]
    change Real.exp (-2 * c * t) * ‖z t‖ ^ 2 ≤ Real.exp (-2 * c * 0) * ‖z 0‖ ^ 2 at he
    rw [hz0] at he
    simp only [mul_zero, Real.exp_zero, one_mul] at he
    have hex : Real.exp (-2 * c * t) * (Real.exp (t * c) * ‖x‖) ^ 2 = ‖x‖ ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
      norm_num only [Nat.cast_ofNat]
      have heq : -2 * c * t + 2 * (t * c) = 0 := by ring
      rw [heq, Real.exp_zero, one_mul]
    have hsq : ‖z t‖ ^ 2 ≤ (Real.exp (t * c) * ‖x‖) ^ 2 :=
      (mul_le_mul_iff_right₀ (Real.exp_pos (-2 * c * t))).mp (he.trans_eq hex.symm)
    have hn : 0 ≤ Real.exp (t * c) * ‖x‖ := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    exact (sq_le_sq₀ (norm_nonneg _) hn).mp hsq
  rw [specNorm_eq_norm, Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro x
  exact horbit x

/-- An exponential semigroup bound forces the corresponding real
quadratic-form bound on its generator. -/
private theorem energy_le_of_specNorm_exp_smul_le (A : Matrix n n 𝕜) (c : ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → specNorm (NormedSpace.exp (t • A)) ≤ Real.exp (t * c))
    (x : EuclideanSpace 𝕜 n) :
    inner ℝ x (A.toEuclideanLin x) ≤ c * ‖x‖ ^ 2 := by
  let z (s : ℝ) := (NormedSpace.exp (s • A)).toEuclideanLin x
  have hz0 : z 0 = x := by simp [z, Matrix.toEuclideanLin]
  have hg : HasDerivAt (fun s : ℝ => ‖z s‖ ^ 2)
      (2 * inner ℝ x (A.toEuclideanLin x)) 0 := by
    convert! (hasDerivAt_exp_orbit A x 0).norm_sq using 1
    change 2 * inner ℝ x (A.toEuclideanLin x) =
      2 * inner ℝ (z 0) (A.toEuclideanLin (z 0))
    rw [hz0]
  have hh : HasDerivAt (fun s : ℝ => Real.exp (s * c) ^ 2 * ‖x‖ ^ 2)
      (2 * c * ‖x‖ ^ 2) 0 := by
    convert! ((((hasDerivAt_id (0 : ℝ)).mul_const c).exp).pow 2).mul_const (‖x‖ ^ 2) using 1
    norm_num
  have hle : 2 * inner ℝ x (A.toEuclideanLin x) ≤ 2 * c * ‖x‖ ^ 2 := by
    apply le_of_tendsto_of_tendsto hg.tendsto_slope_zero_right hh.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 0 < s := hs
    have hn : ‖z s‖ ≤ Real.exp (s * c) * ‖x‖ := by
      have h := (NormedSpace.exp (s • A)).l2_opNorm_mulVec x
      exact h.trans (mul_le_mul_of_nonneg_right (hA s hs'.le) (norm_nonneg _))
    have hsq : ‖z s‖ ^ 2 ≤ Real.exp (s * c) ^ 2 * ‖x‖ ^ 2 := by
      simpa only [mul_pow] using
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mpr hn
    simp only [zero_add, zero_mul, Real.exp_zero, one_pow, one_mul, hz0]
    exact smul_le_smul_of_nonneg_left (sub_le_sub_right hsq _) (inv_pos.mpr hs').le
  linarith

private theorem real_inner_apply (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    inner ℝ x (A.toEuclideanLin x) = RCLike.re (quadForm A x.ofLp) := by
  simp only [PiLp.inner_apply, quadForm, dotProduct, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  convert! real_inner_eq_re_inner 𝕜 (x.ofLp i) ((A *ᵥ x.ofLp) i) using 1
  simp only [RCLike.inner_apply, mul_comm]
  rfl

/-- **Exponential growth and the Hermitian part.** The Euclidean operator norm of the
semigroup generated by a square matrix grows at most as $e^{ct}$ at every nonnegative time
if and only if its Hermitian part is bounded above by $c\mathbf{I}$. For $c=0$ this is
the contraction criterion. [Higham2022, Theorems 3 and 6].
Result: matrix-exponential-logarithmic-norm -/
theorem forall_specNorm_exp_smul_le_iff (A : Matrix n n 𝕜) (c : ℝ) :
    (∀ t : ℝ, 0 ≤ t → specNorm (NormedSpace.exp (t • A)) ≤ Real.exp (t * c)) ↔
      hermitianPart A ≤ c • 1 := by
  rw [(isHermitian_hermitianPart A).le_iff_re_quadForm_le
    (isHermitian_real_smul_one c)]
  simp only [re_quadForm_hermitianPart, re_quadForm_real_smul_one]
  constructor
  · intro h z
    simpa only [real_inner_apply, WithLp.ofLp_toLp] using
      energy_le_of_specNorm_exp_smul_le A c h (WithLp.toLp 2 z)
  · intro h t ht
    apply specNorm_exp_smul_le_of_energy A c _ ht
    intro x
    simpa only [real_inner_apply, WithLp.toLp_ofLp] using h x.ofLp

/-- **Logarithmic norm.** For a nonempty real or complex square matrix, the largest eigenvalue
of the Hermitian part is the least exponent of a semigroup norm bound with unit leading
constant. [Higham2022, Theorems 3 and 6].
Result: matrix-exponential-logarithmic-norm -/
theorem isLeast_specNorm_exp_smul_le [Nonempty n] (A : Matrix n n 𝕜) :
    IsLeast {c : ℝ | ∀ t : ℝ, 0 ≤ t →
      specNorm (NormedSpace.exp (t • A)) ≤ Real.exp (t * c)} (eigenvalue (hermitianPart A) 0) :=
  ⟨(forall_specNorm_exp_smul_le_iff A _).2
      (isHermitian_hermitianPart A).le_eigenvalue_zero_smul_one,
    fun _ h => (isHermitian_hermitianPart A).le_smul_one_iff.mp
      ((forall_specNorm_exp_smul_le_iff A _).1 h)⟩

end NLAlib
