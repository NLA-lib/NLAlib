/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.TapeRounding
public import NLAlib.ForMathlib.Data.Nat.Init
public import NLAlib.Probability.Distributions.Rademacher
public import NLAlib.RandomMatrix.Gaussian.Basic
public import Mathlib.Probability.ConditionalProbability

/-!
# Probability laws of numerical tapes

Independent real streams, their matrix windows, and the support of uniform draws. These laws
are mathematical properties of measures and do not refer to a program evaluator.

## Main results

* `NLAlib.Computation.hasLaw_apply_of_hasLaw_tapeLaw`: each stream has its prescribed iid law.
* `NLAlib.hasLaw_tapeMatrix_of_hasLaw_iidSequence`: Gaussian matrix windows.
* `NLAlib.Computation.ae_forall_mem_Icc_of_hasLaw_tapeLaw`: uniform support.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

open Computation

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The tape positions of an $N \times k$ draw from position `off` are distinct. -/
private theorem injective_tapePos (off N k : ℕ) :
    Function.Injective fun p : Fin N × Fin k => off + p.1.1 + N * p.2.1 := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have h' : i.1 + N * j.1 = i'.1 + N * j'.1 := by simp only at h; omega
  obtain ⟨h1, h2⟩ := (Nat.add_mul_eq_add_mul_iff_of_lt i.2 i'.2).mp h'
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- **A Gaussian tape draws a Gaussian matrix**: if the tape $x$ is an i.i.d. sequence of standard
Gaussians, the $N \times k$ matrix drawn from it from position $\mathit{off}$, column-major, is a
standard Gaussian matrix. No printed source.
Result: tape-gaussian-matrix -/
theorem hasLaw_tapeMatrix_of_hasLaw_iidSequence {x : Ω → ℕ → ℝ}
    (hx : HasLaw x (iidSequence (gaussianReal 0 1)) μ) (off N k : ℕ) :
    HasLaw (fun ω => tapeMatrix (𝕜 := ℝ) (x ω) off N k) (gaussianMatrix (Fin N) (Fin k)) μ := by
  refine hasLaw_gaussianMatrix_of_hasLaw_uncurry ?_
  have h := hx.comp_of_injective (injective_tapePos off N k)
  convert h using 2 with ω
  funext ⟨i, j⟩
  simp only [tapeMatrix]
  rfl

/-- **Consecutive draws are independent**: if the tape $x$ is an i.i.d. sequence with a
probability law $\nu$, the $N \times k$ matrix drawn from position $0$ and the $N \times \ell$
matrix drawn after it, from position $Nk$, are independent. No printed source.
Result: tape-independent-draws -/
theorem indepFun_tapeMatrix_of_hasLaw_iidSequence {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {x : Ω → ℕ → ℝ} (hx : HasLaw x (iidSequence ν) μ) (N k ℓ : ℕ) :
    IndepFun (fun ω => tapeMatrix (𝕜 := ℝ) (x ω) 0 N k)
      (fun ω => tapeMatrix (𝕜 := ℝ) (x ω) (N * k) N ℓ) μ := by
  have : IsProbabilityMeasure μ := hx.isProbabilityMeasure_iff.mpr inferInstance
  have hind := ((hasLaw_infinitePi_iff (ν := fun _ : ℕ => ν)).mp hx).1
  have hST : Disjoint (Finset.range (N * k)) (Finset.Ico (N * k) (N * k + N * ℓ)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_range, Finset.mem_Ico] at ha hb
    omega
  have h := hind.indepFun_finset₀ _ _ hST fun n => (hx.aemeasurable.eval n)
  have hS : ∀ (i : Fin N) (j : Fin k), i.1 + N * j.1 ∈ Finset.range (N * k) := by
    intro i j
    simp only [Finset.mem_range]
    nlinarith [i.2, j.2]
  have hT : ∀ (i : Fin N) (j : Fin ℓ), N * k + i.1 + N * j.1 ∈
      Finset.Ico (N * k) (N * k + N * ℓ) := by
    intro i j
    simp only [Finset.mem_Ico]
    constructor
    · omega
    · nlinarith [i.2, j.2]
  have := h.comp (φ := fun v : Finset.range (N * k) → ℝ =>
      (Matrix.of fun (i : Fin N) (j : Fin k) => v ⟨_, hS i j⟩ : Matrix (Fin N) (Fin k) ℝ))
    (ψ := fun v : Finset.Ico (N * k) (N * k + N * ℓ) → ℝ =>
      (Matrix.of fun (i : Fin N) (j : Fin ℓ) => v ⟨_, hT i j⟩ : Matrix (Fin N) (Fin ℓ) ℝ))
    (by fun_prop) (by fun_prop)
  convert this using 1 <;> funext ω <;> ext i j <;> simp [tapeMatrix]

namespace Computation

/-- The law of one draw from each distribution: the standard Gaussian, the Rademacher law
(a random sign), and the uniform law on $[-1, 1]$ (Lebesgue measure conditioned on the
interval). -/
noncomputable def Dist.law : Dist → Measure ℝ
  | .gaussian => gaussianReal 0 1
  | .rademacher => rademacherMeasure
  | .uniform => volume[|Set.Icc (-1) 1]

/-- The law of a draw is a probability measure. -/
instance isProbabilityMeasure_law (d : Dist) : IsProbabilityMeasure d.law := by
  cases d
  · exact inferInstanceAs (IsProbabilityMeasure (gaussianReal 0 1))
  · exact inferInstanceAs (IsProbabilityMeasure rademacherMeasure)
  · exact cond_isProbabilityMeasure_of_finite (by simp) (by simp)

/-- **The law of the tape**: the tapes of the distributions are independent, and the tape of `d`
is an i.i.d. sequence with law `d.law`. -/
noncomputable def tapeLaw : Measure (Dist → ℕ → ℝ) :=
  Measure.infinitePi fun d : Dist => iidSequence d.law

/-- The law of the tape is a probability measure. -/
instance isProbabilityMeasure_tapeLaw : IsProbabilityMeasure tapeLaw :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun d : Dist => iidSequence d.law))

/-- Under the law of the tape, the tape of one distribution is an i.i.d. sequence with its law. -/
theorem hasLaw_apply_of_hasLaw_tapeLaw {ξ : Ω → Dist → ℕ → ℝ} (hξ : HasLaw ξ tapeLaw μ)
    (d : Dist) : HasLaw (fun ω => ξ ω d) (iidSequence d.law) μ :=
  (measurePreserving_eval_infinitePi (fun d : Dist => iidSequence d.law) d).fun_comp_hasLaw hξ

/-- The uniform law lives on $[-1, 1]$: the law of a uniform draw gives the interval
$[-1, 1]$ mass one. No printed source. -/
theorem Dist.law_uniform_Icc : Dist.uniform.law (Set.Icc (-1) 1) = 1 :=
  cond_apply_self (by norm_num [Real.volume_Icc]) measure_Icc_lt_top.ne

/-- The uniform law of a subinterval: for $-1 \le a \le b \le 1$, a uniform draw lies in
$[a, b]$ with probability
$$\frac{b - a}{2}.$$
No printed source. -/
theorem Dist.real_law_uniform_Icc {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Dist.uniform.law.real (Set.Icc a b) = (b - a) / 2 := by
  have hab' : 0 ≤ b - a := by linarith
  have h2 : 0 ≤ 1 - (-1 : ℝ) := by norm_num
  change ((volume[|Set.Icc (-1 : ℝ) 1]) (Set.Icc a b)).toReal = _
  rw [cond_apply measurableSet_Icc, Set.Icc_inter_Icc, max_eq_right ha, min_eq_right hb,
    ENNReal.toReal_mul, ENNReal.toReal_inv, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_ofReal hab', ENNReal.toReal_ofReal h2]
  ring

/-- Ideal uniform draws lie in $[-1, 1]$: if the tape $\xi$ has the law of the tape
`NLAlib.Computation.tapeLaw` under $\mu$, then $\mu$-almost surely every uniform draw
$\xi(\omega)(d, i)$, $d$ = `NLAlib.Computation.Dist.uniform`, $i \in \mathbb{N}$, lies in
$[-1, 1]$. No printed source. -/
theorem ae_forall_mem_Icc_of_hasLaw_tapeLaw {Ω : Type} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ξ : Ω → Dist → ℕ → ℝ} (hξ : HasLaw ξ tapeLaw μ) :
    ∀ᵐ ω ∂μ, ∀ i, ξ ω .uniform i ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  have hlaw : HasLaw (fun ω => ξ ω .uniform i) Dist.uniform.law μ :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => Dist.uniform.law) i).fun_comp_hasLaw
      (hasLaw_apply_of_hasLaw_tapeLaw hξ .uniform)
  have hae : ∀ᵐ x ∂(μ.map fun ω => ξ ω .uniform i), x ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hlaw.map_eq]
    exact ae_cond_mem measurableSet_Icc
  exact (ae_map_iff hlaw.aemeasurable measurableSet_Icc).mp hae

/-- Stored uniform draws lie in $[-1, 1]$: under the tape-rounding contract
`NLAlib.Computation.IsTapeRounding` for $\rho$, at tag `p`, and an ideal tape $\xi$ with the law of
the tape under $\mu$, $\mu$-almost surely every stored uniform draw
$\rho(d, i, \xi(\omega)(d, i))$, $d$ = `NLAlib.Computation.Dist.uniform`, decodes into
$[-1, 1]$. No printed source. -/
theorem IsTapeRounding.ae_forall_mem_Icc_of_hasLaw_tapeLaw {P K : Type} {dec : P → K → ℝ}
    {p : P} {u τ Ω : ℝ} {c : Dist → ℝ} {ρ : Dist → ℕ → ℝ → K}
    (h : IsTapeRounding dec p u τ Ω c ρ)
    {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ξ : Ω → Dist → ℕ → ℝ}
    (hξ : HasLaw ξ tapeLaw μ) :
    ∀ᵐ ω ∂μ, ∀ i, dec p (ρ .uniform i (ξ ω .uniform i)) ∈ Set.Icc (-1 : ℝ) 1 :=
  (NLAlib.Computation.ae_forall_mem_Icc_of_hasLaw_tapeLaw hξ).mono fun _ hω i => h.2 i _ (hω i)

end Computation

end NLAlib
