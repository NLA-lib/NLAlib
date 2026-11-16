/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Samples
public import NLAlib.RandomMatrix.Gaussian.Complex
public import NLAlib.RandomMatrix.TapeLaw
public import NLAlib.Ops.TapeLaw

/-!
# The complex Gaussian matrix of a Gaussian tape

The ideal sample a program draws from the Gaussian tape, two real draws per complex entry scaled by
$1/\sqrt2$ (`NLAlib.Computation.tapeComplexMatrix`), is a standard complex Gaussian matrix.

## Main results

* `NLAlib.Computation.hasLaw_tapeComplexMatrix_of_hasLaw_pi`,
  `NLAlib.Computation.hasLaw_tapeComplexMatrix_of_hasLaw_tapeLaw`: the law of the sample.
* `NLAlib.Ops.IsTapeLaw.hasLaw_pi_of_injective`: distinct entries of a stream are independent.
* `NLAlib.Computation.hasLaw_complexGaussianMatrix_windowFn`,
  `NLAlib.Computation.hasLaw_complexGaussianVector_windowFn`: the same for a window of a Gaussian
  stream of an operation-core tape (`NLAlib.Ops.IsTapeLaw`).
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

/-- The tape positions of the entries of `NLAlib.Computation.tapeComplexMatrix`, the real draw
$t$ of entry $(i, j)$ at $2(i + nj) + t$, are distinct. -/
private theorem injective_tapeComplexMatrix_pos (n : ℕ) :
    Function.Injective fun p : (Fin n × Fin n) × Fin 2 => 2 * (p.1.1 + n * p.1.2) + p.2.1 := by
  rintro ⟨⟨i, j⟩, t⟩ ⟨⟨i', j'⟩, t'⟩ h
  have h' : i.1 + n * j.1 = i'.1 + n * j'.1 := by simp only at h; omega
  have ht : t.1 = t'.1 := by simp only at h; omega
  obtain ⟨h1, h2⟩ := (Nat.add_mul_eq_add_mul_iff_of_lt i.2 i'.2).mp h'
  exact Prod.ext (Prod.ext (Fin.ext h1) (Fin.ext h2)) (Fin.ext ht)

/-- Independent standard real Gaussian draws at the tape positions of
`NLAlib.Computation.tapeComplexMatrix` give a complex Gaussian matrix: if the draws $x_{2(i + nj)
+ t}$, $t < 2$, are independent standard real Gaussians, the matrix has the law
`NLAlib.complexGaussianMatrix`. -/
theorem hasLaw_tapeComplexMatrix_of_hasLaw_pi {Ω : Type} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {x : Ω → ℕ → ℝ} {n : ℕ}
    (hY : HasLaw (fun ω (p : (Fin n × Fin n) × Fin 2) => x ω (2 * (p.1.1 + n * p.1.2) + p.2.1))
      (Measure.pi fun _ : (Fin n × Fin n) × Fin 2 => gaussianReal 0 1) μ) :
    HasLaw (fun ω => tapeComplexMatrix (x ω) n) (complexGaussianMatrix (Fin n) (Fin n)) μ := by
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

/-- A Gaussian tape draws a complex Gaussian matrix: if $\xi$ has the law of the tape
`NLAlib.Computation.tapeLaw` under $\mu$, the $n \times n$ matrix with entry $(i, j)$ equal to
$(\xi_{2(i + nj)} + i\,\xi_{2(i + nj) + 1})/\sqrt2$, from the Gaussian draws, has the law of a
matrix with independent standard complex Gaussian entries (`NLAlib.complexGaussianMatrix`). No
printed source. -/
theorem hasLaw_tapeComplexMatrix_of_hasLaw_tapeLaw {Ω : Type} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ξ : Ω → Dist → ℕ → ℝ} (hξ : HasLaw ξ tapeLaw μ) (n : ℕ) :
    HasLaw (fun ω => tapeComplexMatrix (ξ ω .gaussian) n)
      (complexGaussianMatrix (Fin n) (Fin n)) μ :=
  hasLaw_tapeComplexMatrix_of_hasLaw_pi
    ((hasLaw_apply_of_hasLaw_tapeLaw hξ .gaussian).comp_of_injective
      (injective_tapeComplexMatrix_pos n))

/-- Distinct entries of a stream of a tape law are independent draws: under
`NLAlib.Ops.IsTapeLaw`, for an injective $f : \iota \to \mathbb{N}$ on a finite type, the entries
of the stream $s$ at the positions $f(i)$ have the product law of `law s`. -/
theorem _root_.NLAlib.Ops.IsTapeLaw.hasLaw_pi_of_injective {Ω ι : Type} [Fintype ι]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {law : ℕ → Measure ℝ} {ξ : Ω → Ops.Tape ℝ}
    (hξ : Ops.IsTapeLaw law P ξ) (s : ℕ) {f : ι → ℕ} (hf : Function.Injective f) :
    HasLaw (fun ω i => ξ ω (f i) s) (Measure.pi fun _ : ι => law s) P := by
  have := hξ.isProbabilityMeasure
  have := hξ.isProbabilityMeasure_law s
  have hind : iIndepFun (fun i ω => ξ ω (f i) s) P :=
    hξ.indep.precomp (g := fun i => (f i, s)) fun a b hab => hf (by simpa using hab)
  exact hind.hasLaw_pi fun i => ⟨(hξ.measurable _ _).aemeasurable, hξ.map (f i) s⟩

/-- **A window of a Gaussian stream is a complex Gaussian matrix**: under a tape law
(`NLAlib.Ops.IsTapeLaw`) whose stream $s$ is standard real Gaussian, the $N \times N$ matrix with
entry $(i, j)$ equal to $(x_{2(i + Nj)} + i\,x_{2(i + Nj) + 1})/\sqrt2$, for the $2N^2$ entries
$x$ of the stream $s$ from the position $p$, has the law of a matrix with independent standard
complex Gaussian entries. It is the law of the perturbation drawn by the program of
[BanksGarzaVargasSrivastava2025, Theorem 1.1]. -/
theorem hasLaw_complexGaussianMatrix_windowFn {Ω : Type} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {law : ℕ → Measure ℝ} {ξ : Ω → Ops.Tape ℝ} (hξ : Ops.IsTapeLaw law P ξ)
    {s : ℕ} (hs : law s = gaussianReal 0 1) (p N : ℕ) :
    HasLaw (fun ω => tapeComplexMatrix (fun j => ξ ω (p + j) s) N)
      (complexGaussianMatrix (Fin N) (Fin N)) P := by
  refine hasLaw_tapeComplexMatrix_of_hasLaw_pi ?_
  rw [← hs]
  exact hξ.hasLaw_pi_of_injective s
    ((add_right_injective p).comp (injective_tapeComplexMatrix_pos N))

/-- **A window of a Gaussian stream is a complex Gaussian vector**: under a tape law whose stream
$s$ is standard real Gaussian, the vector with entry $i$ equal to
$(x_{2i} + i\,x_{2i + 1})/\sqrt2$, for the $2N$ entries $x$ of the stream $s$ from the position
$p$, has independent standard complex Gaussian entries. It is the law of the random direction
of [BanksGarzaVargasSrivastava2025, Proposition 5.3], drawn as a Gaussian vector. -/
theorem hasLaw_complexGaussianVector_windowFn {Ω : Type} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {law : ℕ → Measure ℝ} {ξ : Ω → Ops.Tape ℝ} (hξ : Ops.IsTapeLaw law P ξ)
    {s : ℕ} (hs : law s = gaussianReal 0 1) (p N : ℕ) :
    HasLaw (fun ω (i : Fin N) =>
        (⟨ξ ω (p + 2 * i) s / √2, ξ ω (p + 2 * i + 1) s / √2⟩ : ℂ))
      (complexGaussianVector (Fin N)) P := by
  have hf : Function.Injective fun q : Fin N × Fin 2 => p + (2 * q.1.1 + q.2.1) := by
    rintro ⟨i, t⟩ ⟨i', t'⟩ h
    have hi : i.1 = i'.1 := by simp only at h; omega
    have ht : t.1 = t'.1 := by simp only at h; omega
    exact Prod.ext (Fin.ext hi) (Fin.ext ht)
  have hY := hξ.hasLaw_pi_of_injective s hf
  rw [hs] at hY
  have hC := measurePreserving_curry_pi (m := Fin N) (n := Fin 2)
    (ν := fun _ _ => gaussianReal 0 1)
  have hpair : Measurable fun v : Fin 2 → ℝ => (⟨v 0 / √2, v 1 / √2⟩ : ℂ) :=
    Complex.measurableEquivRealProd.symm.measurable.comp (f := fun v : Fin 2 → ℝ =>
      (v 0 / √2, v 1 / √2)) (((measurable_pi_apply 0).div_const _).prodMk
        ((measurable_pi_apply 1).div_const _))
  have hPm : Measurable fun x : Fin N → Fin 2 → ℝ => fun i => (⟨x i 0 / √2, x i 1 / √2⟩ : ℂ) :=
    measurable_pi_lambda _ fun i => hpair.comp (measurable_pi_apply i)
  have hPmap : Measure.map (fun x : Fin N → Fin 2 → ℝ => fun i => (⟨x i 0 / √2, x i 1 / √2⟩ : ℂ))
      (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin 2 => gaussianReal 0 1) =
        complexGaussianVector (Fin N) := by
    refine (Measure.pi_map_pi (f := fun _ (v : Fin 2 → ℝ) => (⟨v 0 / √2, v 1 / √2⟩ : ℂ))
      (fun _ => hpair.aemeasurable)).trans ?_
    exact congrArg Measure.pi (funext fun _ => map_pair_eq_complexGaussian)
  have hmap : Measure.map (fun y : Fin N × Fin 2 → ℝ => fun i : Fin N =>
      (⟨y (i, 0) / √2, y (i, 1) / √2⟩ : ℂ))
      (Measure.pi fun _ : Fin N × Fin 2 => gaussianReal 0 1) = complexGaussianVector (Fin N) := by
    rw [← hPmap, ← hC.map_eq, Measure.map_map hPm hC.measurable]
    rfl
  exact (HasLaw.mk (hPm.comp hC.measurable).aemeasurable hmap).comp hY

end NLAlib.Computation
