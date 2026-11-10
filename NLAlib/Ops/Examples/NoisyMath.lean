/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import NLAlib.Ops.Catalog.Isotropic
public import NLAlib.Ops.TapeLaw

/-!
# Mathematics of the noisy product by a matrix

No program occurs in this file. A noisy product is a function `N v w` of the input vector `v`
and of a window `w` of `n` draws. Its contract is about its conditional law
(`NLAlib.Ops.Examples.IsNoisyMv`): given `v`, the output has the law of
`A v + σ ‖v‖ g` with `g` isotropic (for example `g ~ N(0, I)`).

The noisy power iteration `v_{j+1} = N v_j w_j` (`NLAlib.Ops.Examples.noisyIter`) feeds each
output back as the next input, so the input of step `j` depends on all the earlier noise. The
window of step `j` is independent of the past of its position, and that is all the analysis
uses.

## Main results

* `NLAlib.Ops.Examples.integral_sqNorm_noisyIter_le`:
  `𝔼 ‖v_j‖² ≤ (a + n σ²)^j ‖v₀‖²` when `‖A v‖² ≤ a ‖v‖²`. One step is
  `𝔼 ‖v_{j+1}‖² = 𝔼 ‖A v_j‖² + n σ² 𝔼 ‖v_j‖²`: the cross term vanishes because the noise has
  mean zero given the history, and its variance `σ² ‖v_j‖² n` depends on the history.
* `NLAlib.Ops.Examples.integral_noisyIter`: `𝔼 v_j = A^j v₀`.
* `NLAlib.Ops.Examples.isNoisyMv_noiseFn`: the function `A v + σ ‖v‖ dec w` meets the contract
  when the draws decode to a standard law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib.Ops.Examples

variable {K : Type} [MeasurableSpace K] {n : ℕ}

/-- **The contract of a noisy product by `A`**, on its conditional law: given the input `v`, the
output `N v w` over a window `w` of `n` fresh draws of `μ` has the law of `A v + σ ‖v‖ g`, where
`g` has the isotropic law `ν`. -/
structure IsNoisyMv (A : Matrix (Fin n) (Fin n) ℝ) (σ : ℝ) (ν : Measure (Fin n → ℝ))
    (μ : Measure K) (N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ) : Prop where
  /-- The output is measurable in the input and the window. -/
  measurable : Measurable (Function.uncurry N)
  /-- The noise is isotropic. -/
  iso : IsIsotropic ν
  /-- The conditional law of the output given the input. -/
  law : ∀ v, condLaw μ N v = ν.map fun g i => A.mulVec v i + σ * √(sqNorm v) * g i

namespace IsNoisyMv

variable {A : Matrix (Fin n) (Fin n) ℝ} {σ : ℝ} {ν : Measure (Fin n → ℝ)} {μ : Measure K}
  {N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ}

theorem measurable_affine (b : Fin n → ℝ) (c : ℝ) :
    Measurable fun (g : Fin n → ℝ) i => b i + c * g i :=
  measurable_pi_lambda _ fun i =>
    measurable_const.add (measurable_const.mul (measurable_pi_apply i))

/-- An integral against the conditional law is an integral over the isotropic noise. -/
theorem integral_condLaw (h : IsNoisyMv A σ ν μ N) (v : Fin n → ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) : ∫ y, f y ∂(condLaw μ N v) =
      ∫ g, f (fun i => A.mulVec v i + σ * √(sqNorm v) * g i) ∂ν := by
  rw [h.law, integral_map (measurable_affine _ _).aemeasurable hf.aestronglyMeasurable]

theorem integrable_condLaw_iff (h : IsNoisyMv A σ ν μ N) (v : Fin n → ℝ)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) : Integrable f (condLaw μ N v) ↔
      Integrable (fun g => f fun i => A.mulVec v i + σ * √(sqNorm v) * g i) ν := by
  rw [h.law]
  exact integrable_map_measure hf.aestronglyMeasurable (measurable_affine _ _).aemeasurable

/-- **Given the input, the output is unbiased.** -/
theorem integral_coord (h : IsNoisyMv A σ ν μ N) (v : Fin n → ℝ) (i : Fin n) :
    ∫ y, y i ∂(condLaw μ N v) = A.mulVec v i := by
  rw [h.integral_condLaw v (measurable_pi_apply i)]
  exact h.iso.integral_affine _ _ i

/-- **Given the input, the second moment of the output** is `‖A v‖² + σ² ‖v‖² n`. -/
theorem integral_sqNorm (h : IsNoisyMv A σ ν μ N) (v : Fin n → ℝ) :
    ∫ y, sqNorm y ∂(condLaw μ N v) = sqNorm (A.mulVec v) + n * σ ^ 2 * sqNorm v := by
  rw [h.integral_condLaw v measurable_sqNorm, h.iso.integral_sqNorm_affine, mul_pow,
    Real.sq_sqrt (sqNorm_nonneg v)]
  ring

theorem integrable_sqNorm (h : IsNoisyMv A σ ν μ N) (v : Fin n → ℝ) :
    Integrable sqNorm (condLaw μ N v) :=
  (h.integrable_condLaw_iff v measurable_sqNorm).mpr (h.iso.integrable_sqNorm_affine _ _)

theorem integrable_coord (h : IsNoisyMv A σ ν μ N) (v : Fin n → ℝ) (i : Fin n) :
    Integrable (fun y : Fin n → ℝ => y i) (condLaw μ N v) := by
  have := h.iso.prob
  have h1 : Integrable (fun g : Fin n → ℝ => σ * √(sqNorm v) * g i) ν :=
    (h.iso.integrable_coord i).const_mul _
  exact (h.integrable_condLaw_iff v (measurable_pi_apply i)).mpr ((integrable_const _).add h1)

end IsNoisyMv

/-- **The noisy power iteration**, as a function of the tape entries from the position `p`: step
`j` reads the window of `n` Gaussian entries at `p + j n`. -/
def noisyIter (N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ) (v₀ : Fin n → ℝ) (τ : Tape K)
    (p : ℕ) : ℕ → Fin n → ℝ
  | 0 => v₀
  | j + 1 => N (noisyIter N v₀ τ p j) (Tape.windowFn τ Stream.gauss (p + j * n) n)

section Iter

variable {A : Matrix (Fin n) (Fin n) ℝ} {σ a : ℝ} {ν : Measure (Fin n → ℝ)}
  {law : ℕ → Measure K} {N : (Fin n → ℝ) → (Fin n → K) → Fin n → ℝ} {Ω : Type}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ξ : Ω → Tape K}

/-- The iterate after `j` steps is a function of the tape before the position `p + j n`: it is
part of the history when step `j` is called. -/
theorem measurable_noisyIter (hN : Measurable (Function.uncurry N)) (ξ : Ω → Tape K)
    (v₀ : Fin n → ℝ) (p j : ℕ) :
    Measurable[Tape.past ξ (p + j * n)] fun ω => noisyIter N v₀ (ξ ω) p j := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hle : p + j * n + n ≤ p + (j + 1) * n := by rw [Nat.succ_mul]; omega
    exact hN.comp ((ih.mono (Tape.past_mono (by omega)) le_rfl).prodMk
      (Tape.measurable_windowFn_past hle Stream.gauss))

/-- **The second moment of the noisy power iteration**: integrable, and at most
`(a + n σ²)^j ‖v₀‖²`. -/
theorem integral_sqNorm_noisyIter_le (hN : IsNoisyMv A σ ν (law Stream.gauss) N)
    (ha : 0 ≤ a) (hA : ∀ v, sqNorm (A.mulVec v) ≤ a * sqNorm v) (h : IsTapeLaw law P ξ)
    (v₀ : Fin n → ℝ) (p j : ℕ) : Integrable (fun ω => sqNorm (noisyIter N v₀ (ξ ω) p j)) P ∧
      ∫ ω, sqNorm (noisyIter N v₀ (ξ ω) p j) ∂P ≤ (a + n * σ ^ 2) ^ j * sqNorm v₀ := by
  have := h.isProbabilityMeasure
  induction j with
  | zero =>
    simp only [noisyIter]
    exact ⟨integrable_const _, by simp⟩
  | succ j ih =>
    obtain ⟨hi, hb⟩ := ih
    have hV := measurable_noisyIter hN.measurable ξ v₀ p j
    have hVm : Measurable fun ω => noisyIter N v₀ (ξ ω) p j := hV.mono (h.sigma_le _) le_rfl
    have hφ : Measurable (Function.uncurry fun (_ : Fin n → ℝ) (y : Fin n → ℝ) => sqNorm y) :=
      measurable_sqNorm.comp measurable_snd
    -- the inner integral: the conditional second moment given the iterate
    have hψ : ∀ ω, ∫ y, ‖sqNorm y‖ ∂(condLaw (law Stream.gauss) N (noisyIter N v₀ (ξ ω) p j)) =
        sqNorm (A.mulVec (noisyIter N v₀ (ξ ω) p j)) +
          n * σ ^ 2 * sqNorm (noisyIter N v₀ (ξ ω) p j) := fun ω => by
      simp only [Real.norm_of_nonneg (sqNorm_nonneg _)]
      exact hN.integral_sqNorm _
    have hψi : Integrable (fun ω => sqNorm (A.mulVec (noisyIter N v₀ (ξ ω) p j)) +
        n * σ ^ 2 * sqNorm (noisyIter N v₀ (ξ ω) p j)) P := by
      refine ((hi.const_mul a).add (hi.const_mul (n * σ ^ 2))).mono'
        ((measurable_sqNorm.comp ((measurable_mulVec A).comp hVm)).add
          ((measurable_sqNorm.comp hVm).const_mul _)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_of_nonneg (add_nonneg (sqNorm_nonneg _)
        (mul_nonneg (by positivity) (sqNorm_nonneg _)))]
      exact add_le_add (hA _) le_rfl
    have hint := h.integrable_hidden hV Stream.gauss hN.measurable hφ
      (fun v => hN.integrable_sqNorm v) (hψi.congr (Filter.Eventually.of_forall fun ω =>
        (hψ ω).symm))
    refine ⟨hint, ?_⟩
    have key := h.integral_hidden hV Stream.gauss hN.measurable hφ hint
    simp only [noisyIter]
    rw [key]
    simp only [hN.integral_sqNorm]
    calc ∫ ω, sqNorm (A.mulVec (noisyIter N v₀ (ξ ω) p j)) +
          n * σ ^ 2 * sqNorm (noisyIter N v₀ (ξ ω) p j) ∂P
        ≤ ∫ ω, (a + n * σ ^ 2) * sqNorm (noisyIter N v₀ (ξ ω) p j) ∂P :=
          integral_mono hψi (hi.const_mul _) fun ω => by
            have := hA (noisyIter N v₀ (ξ ω) p j)
            simp only
            linarith
      _ = (a + n * σ ^ 2) * ∫ ω, sqNorm (noisyIter N v₀ (ξ ω) p j) ∂P := integral_const_mul _ _
      _ ≤ (a + n * σ ^ 2) * ((a + n * σ ^ 2) ^ j * sqNorm v₀) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (a + n * σ ^ 2) ^ (j + 1) * sqNorm v₀ := by ring

/-- **The noisy power iteration is unbiased**: `𝔼 v_j = A^j v₀`. Each step is unbiased given the
history, and the history enters the next step linearly. -/
theorem integral_noisyIter (hN : IsNoisyMv A σ ν (law Stream.gauss) N)
    (ha : 0 ≤ a) (hA : ∀ v, sqNorm (A.mulVec v) ≤ a * sqNorm v) (h : IsTapeLaw law P ξ)
    (v₀ : Fin n → ℝ) (p j : ℕ) (i : Fin n) :
    ∫ ω, noisyIter N v₀ (ξ ω) p j i ∂P = (A ^ j).mulVec v₀ i := by
  have := h.isProbabilityMeasure
  have hci : ∀ j i, Integrable (fun ω => noisyIter N v₀ (ξ ω) p j i) P := fun j i => by
    have hVm : Measurable fun ω => noisyIter N v₀ (ξ ω) p j :=
      (measurable_noisyIter hN.measurable ξ v₀ p j).mono (h.sigma_le _) le_rfl
    refine ((integrable_const 1).add (integral_sqNorm_noisyIter_le hN ha hA h v₀ p j).1).mono'
      ((measurable_pi_apply i).comp hVm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := sq_le_sqNorm (noisyIter N v₀ (ξ ω) p j) i
    rw [Real.norm_eq_abs]
    change _ ≤ 1 + sqNorm (noisyIter N v₀ (ξ ω) p j)
    nlinarith [sq_abs (noisyIter N v₀ (ξ ω) p j i), sq_nonneg (|noisyIter N v₀ (ξ ω) p j i| - 1)]
  induction j generalizing i with
  | zero => simp [noisyIter]
  | succ j ih =>
    have hV := measurable_noisyIter hN.measurable ξ v₀ p j
    have hφ : Measurable (Function.uncurry fun (_ : Fin n → ℝ) (y : Fin n → ℝ) => y i) :=
      (measurable_pi_apply i).comp measurable_snd
    have key := h.integral_hidden hV Stream.gauss hN.measurable hφ (hci (j + 1) i)
    have e : ∀ v : Fin n → ℝ, A.mulVec v i = ∑ k, A i k * v k := fun v => by
      simp [Matrix.mulVec, dotProduct]
    simp only [noisyIter] at key ⊢
    rw [key]
    simp only [hN.integral_coord, e]
    rw [integral_finsetSum _ fun k _ => (hci j k).const_mul _]
    simp only [integral_const_mul, ih]
    rw [← e, Matrix.mulVec_mulVec, ← pow_succ']

end Iter

/-- The noisy product computed from an exact product, a norm and a Gaussian probe:
`A v + σ ‖v‖ dec w`. -/
noncomputable def noiseFn (dec : K → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (σ : ℝ)
    (v : Fin n → ℝ) (w : Fin n → K) : Fin n → ℝ :=
  fun i => A.mulVec v i + σ * √(sqNorm v) * dec (w i)

/-- **The noisy product by a drawn probe meets the contract** when the draws decode to a standard
law: the noise is the decoded probe, which is isotropic. -/
theorem isNoisyMv_noiseFn {dec : K → ℝ} (hdec : Measurable dec) {μ : Measure K}
    (hstd : IsStdLaw (μ.map dec)) (A : Matrix (Fin n) (Fin n) ℝ) (σ : ℝ) :
    IsNoisyMv A σ (probeLaw dec μ n) μ (noiseFn dec A σ) where
  measurable := measurable_pi_lambda _ fun i =>
    ((measurable_pi_apply i).comp ((measurable_mulVec A).comp measurable_fst)).add
      (((measurable_sqNorm.comp measurable_fst).sqrt.const_mul σ).mul
        (hdec.comp ((measurable_pi_apply i).comp measurable_snd)))
  iso := isIsotropic_probeLaw hdec hstd n
  law v := by
    have hm : Measurable fun w : Fin n → K => fun j => dec (w j) :=
      measurable_pi_lambda _ fun j => hdec.comp (measurable_pi_apply j)
    rw [condLaw, probeLaw, Measure.map_map (IsNoisyMv.measurable_affine _ _) hm]
    rfl

end NLAlib.Ops.Examples
