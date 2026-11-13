/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Samples
public import NLAlib.RandomMatrix.Gaussian.Complex
public import NLAlib.RandomMatrix.TapeLaw

/-!
# The complex Gaussian matrix of a Gaussian tape

The ideal sample a program draws from the Gaussian tape, two real draws per complex entry scaled by
$1/\sqrt2$ (`NLAlib.Computation.tapeComplexMatrix`), is a standard complex Gaussian matrix.

## Main results

* `NLAlib.Computation.hasLaw_tapeComplexMatrix_of_hasLaw_tapeLaw`: the law of the sample.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib.Computation

private lemma map_pair_eq_complexGaussian :
    (Measure.pi fun _ : Fin 2 => gaussianReal 0 1).map
      (fun v : Fin 2 → ℝ => (⟨v 0 / √2, v 1 / √2⟩ : ℂ)) = complexGaussian := by
  have hA : Measurable (Complex.measurableEquivRealProd.symm ∘ Prod.map (· / √2) (· / √2)) :=
    Complex.measurableEquivRealProd.symm.measurable.comp (by fun_prop)
  have hfun : (fun v : Fin 2 → ℝ => (⟨v 0 / √2, v 1 / √2⟩ : ℂ)) =
      (Complex.measurableEquivRealProd.symm ∘ Prod.map (· / √2) (· / √2)) ∘
        MeasurableEquiv.finTwoArrow := rfl
  have hd : (gaussianReal 0 1).map (· / √2) = gaussianReal 0 2⁻¹ := by
    have hfn : (fun x : ℝ => x / √2) = fun x => (√2)⁻¹ * x :=
      funext fun x => div_eq_inv_mul _ _
    rw [hfn, gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply NNReal.eq
      simp [mul_comm]
  rw [hfun, ← Measure.map_map hA MeasurableEquiv.finTwoArrow.measurable,
    (measurePreserving_finTwoArrow _).map_eq,
    ← Measure.map_map Complex.measurableEquivRealProd.symm.measurable (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), hd]
  rfl

/-- A Gaussian tape draws a complex Gaussian matrix: if $\xi$ has the law of the tape
`NLAlib.Computation.tapeLaw` under $\mu$, the $n \times n$ matrix with entry $(i, j)$ equal to
$(\xi_{2(i + nj)} + i\,\xi_{2(i + nj) + 1})/\sqrt2$, from the Gaussian draws, has the law of a
matrix with independent standard complex Gaussian entries (`NLAlib.complexGaussianMatrix`). No
printed source. -/
theorem hasLaw_tapeComplexMatrix_of_hasLaw_tapeLaw {Ω : Type} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ξ : Ω → Dist → ℕ → ℝ} (hξ : HasLaw ξ tapeLaw μ) (n : ℕ) :
    HasLaw (fun ω => tapeComplexMatrix (ξ ω .gaussian) n)
      (complexGaussianMatrix (Fin n) (Fin n)) μ := by
  have hf : Function.Injective fun p : (Fin n × Fin n) × Fin 2 =>
      2 * (p.1.1 + n * p.1.2) + p.2.1 := by
    rintro ⟨⟨i, j⟩, t⟩ ⟨⟨i', j'⟩, t'⟩ h
    have h' : i.1 + n * j.1 = i'.1 + n * j'.1 := by simp only at h; omega
    have ht : t.1 = t'.1 := by simp only at h; omega
    obtain ⟨h1, h2⟩ := (Nat.add_mul_eq_add_mul_iff_of_lt i.2 i'.2).mp h'
    exact Prod.ext (Prod.ext (Fin.ext h1) (Fin.ext h2)) (Fin.ext ht)
  have hY : HasLaw
      (fun ω (p : (Fin n × Fin n) × Fin 2) => ξ ω .gaussian (2 * (p.1.1 + n * p.1.2) + p.2.1))
      (Measure.pi fun _ : (Fin n × Fin n) × Fin 2 => gaussianReal 0 1) μ :=
    (hasLaw_apply_of_hasLaw_tapeLaw hξ .gaussian).comp_of_injective hf
  -- the Gaussian entries regrouped by rows and columns, then the pair map
  have hG := measurePreserving_curry_pi (m := Fin n × Fin n) (n := Fin 2)
    (ν := fun _ _ => gaussianReal 0 1)
  have hH := measurePreserving_curry_pi (m := Fin n) (n := Fin n) (α := Fin 2 → ℝ)
    (ν := fun _ _ => Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
  have hHG := hH.comp hG
  -- the pair map on the entries, applied row by row and entry by entry
  have hpair : Measurable fun v : Fin 2 → ℝ => (⟨v 0 / √2, v 1 / √2⟩ : ℂ) :=
    Complex.measurableEquivRealProd.symm.measurable.comp (f := fun v : Fin 2 → ℝ =>
      (v 0 / √2, v 1 / √2)) (((measurable_pi_apply 0).div_const _).prodMk
        ((measurable_pi_apply 1).div_const _))
  have hPmap : Measure.map
      (fun x : Fin n → Fin n → Fin 2 → ℝ =>
        (Matrix.of fun i j => (⟨x i j 0 / √2, x i j 1 / √2⟩ : ℂ) : Matrix (Fin n) (Fin n) ℂ))
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n =>
        Measure.pi fun _ : Fin 2 => gaussianReal 0 1) = complexGaussianMatrix (Fin n) (Fin n) := by
    refine (Measure.pi_map_pi (f := fun _ (r : Fin n → Fin 2 → ℝ) j =>
        (⟨r j 0 / √2, r j 1 / √2⟩ : ℂ))
      (fun _ => (measurable_pi_lambda _ fun j =>
        hpair.comp (measurable_pi_apply j)).aemeasurable)).trans ?_
    refine congrArg Measure.pi (funext fun i => ?_)
    refine (Measure.pi_map_pi (f := fun _ (v : Fin 2 → ℝ) => (⟨v 0 / √2, v 1 / √2⟩ : ℂ))
      (fun _ => hpair.aemeasurable)).trans ?_
    exact congrArg Measure.pi (funext fun _ => map_pair_eq_complexGaussian)
  have hPm : Measurable fun x : Fin n → Fin n → Fin 2 → ℝ =>
      (Matrix.of fun i j => (⟨x i j 0 / √2, x i j 1 / √2⟩ : ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      hpair.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))
  -- the entry map, as the composite of the two regroupings and the pair map
  have hFm : Measurable fun y : (Fin n × Fin n) × Fin 2 → ℝ =>
      (Matrix.of fun i j => (⟨y ((i, j), 0) / √2, y ((i, j), 1) / √2⟩ : ℂ) :
        Matrix (Fin n) (Fin n) ℂ) :=
    hPm.comp hHG.measurable
  have hmap : Measure.map
      (fun y : (Fin n × Fin n) × Fin 2 → ℝ =>
        (Matrix.of fun i j => (⟨y ((i, j), 0) / √2, y ((i, j), 1) / √2⟩ : ℂ) :
          Matrix (Fin n) (Fin n) ℂ))
      (Measure.pi fun _ : (Fin n × Fin n) × Fin 2 => gaussianReal 0 1) =
        complexGaussianMatrix (Fin n) (Fin n) := by
    rw [← hPmap, ← hHG.map_eq, Measure.map_map hPm hHG.measurable]
    rfl
  exact (HasLaw.mk hFm.aemeasurable hmap).comp hY

end NLAlib.Computation
