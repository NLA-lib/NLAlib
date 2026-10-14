/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.ProductMeasure
public import NLAlib.ForMathlib.MeasureTheory.Matrix

/-!
# Laws of random vectors and random matrices

Statements in NLAlib take a random variable `X` with Mathlib's `HasLaw X ν μ`, never a canonical
measure space (`docs/PORT_PROBABILITY.md` D2). "Independent coordinates with laws `ν i`" is the
single hypothesis `HasLaw X (Measure.pi ν) μ`, and a random matrix with independent entries has
the nested product law `Measure.pi fun i => Measure.pi fun j => ν i j`. This file takes those
hypotheses apart into independence and marginals, and back, and transports integrability and
`MemLp` along a law.

## Main results

* `NLAlib.hasLaw_pi_iff`: a product law is independence plus marginals.
* `ProbabilityTheory.HasLaw.eval`, `ProbabilityTheory.HasLaw.iIndepFun_eval`: its two halves.
* `NLAlib.hasLaw_pi_pi_iff`: the same for the entries of a random matrix, indexed by `m × n`.
* `ProbabilityTheory.HasLaw.entry`, `ProbabilityTheory.HasLaw.iIndepFun_entry`.
* `ProbabilityTheory.HasLaw.integrable_comp_iff`, `ProbabilityTheory.HasLaw.memLp_comp_iff`:
  integrability depends only on the law. (The bridge to `IdentDistrib` is Mathlib's
  `ProbabilityTheory.HasLaw.identDistrib`.)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

section Pi

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
  {ν : ∀ i, Measure (E i)} {X : Ω → ∀ i, E i}

/-- A random vector has the product law `Measure.pi ν` exactly when its coordinates are
independent and the `i`-th coordinate has law `ν i`. The hypothesis that `μ` is a probability
measure is needed only for the reverse direction when `ι` is empty. -/
theorem hasLaw_pi_iff [IsProbabilityMeasure μ] [∀ i, IsProbabilityMeasure (ν i)] :
    HasLaw X (Measure.pi ν) μ ↔
      iIndepFun (fun i ω => X ω i) μ ∧ ∀ i, HasLaw (fun ω => X ω i) (ν i) μ := by
  refine ⟨fun hX => ?_, fun h => h.1.hasLaw_pi h.2⟩
  have hev : ∀ i, HasLaw (fun ω => X ω i) (ν i) μ := fun i =>
    (measurePreserving_eval ν i).fun_comp_hasLaw hX
  exact ⟨(iIndepFun_iff_hasLaw_pi_pi hev).2 hX, hev⟩

/-- The `i`-th coordinate of a random vector with law `Measure.pi ν` has law `ν i`. -/
theorem _root_.ProbabilityTheory.HasLaw.eval [∀ i, IsProbabilityMeasure (ν i)]
    (hX : HasLaw X (Measure.pi ν) μ) (i : ι) : HasLaw (fun ω => X ω i) (ν i) μ := by
  exact (measurePreserving_eval ν i).fun_comp_hasLaw hX

/-- The coordinates of a random vector with a product law are independent. -/
theorem _root_.ProbabilityTheory.HasLaw.iIndepFun_eval [∀ i, IsProbabilityMeasure (ν i)]
    (hX : HasLaw X (Measure.pi ν) μ) : iIndepFun (fun i ω => X ω i) μ := by
  have := hX.isProbabilityMeasure
  exact (hasLaw_pi_iff.1 hX).1

end Pi

section Matrix

variable {m n α : Type*} [Fintype m] [Fintype n] [MeasurableSpace α] {ν : m → n → Measure α}
  [∀ i j, IsProbabilityMeasure (ν i j)] {X : Ω → Matrix m n α}

private theorem measurePreserving_curry_pi :
    MeasurePreserving (MeasurableEquiv.curry m n α) (Measure.pi fun p : m × n => ν p.1 p.2)
      (Measure.pi fun i => Measure.pi fun j => ν i j) := by
  refine ⟨(MeasurableEquiv.curry m n α).measurable, ?_⟩
  simp_rw [← Measure.infinitePi_eq_pi]
  exact Measure.infinitePi_map_curry ν

/-- A random matrix has the law `Measure.pi fun i => Measure.pi fun j => ν i j` exactly when its
entries, indexed by `m × n`, are independent and the `(i, j)` entry has law `ν i j`. -/
theorem hasLaw_pi_pi_iff [IsProbabilityMeasure μ] :
    HasLaw X (Measure.pi fun i => Measure.pi fun j => ν i j) μ ↔
      iIndepFun (fun p : m × n => fun ω => X ω p.1 p.2) μ ∧
        ∀ i j, HasLaw (fun ω => X ω i j) (ν i j) μ := by
  have hY : HasLaw X (Measure.pi fun i => Measure.pi fun j => ν i j) μ ↔
      HasLaw (fun ω (p : m × n) => X ω p.1 p.2) (Measure.pi fun p : m × n => ν p.1 p.2) μ :=
    ⟨fun hX => measurePreserving_curry_pi.symm.fun_comp_hasLaw hX,
      fun hX => measurePreserving_curry_pi.fun_comp_hasLaw hX⟩
  rw [hY, hasLaw_pi_iff, Prod.forall]

/-- The `(i, j)` entry of a random matrix with independent entries has law `ν i j`. -/
theorem _root_.ProbabilityTheory.HasLaw.entry
    (hX : HasLaw X (Measure.pi fun i => Measure.pi fun j => ν i j) μ) (i : m) (j : n) :
    HasLaw (fun ω => X ω i j) (ν i j) μ := by
  exact (measurePreserving_eval _ j).fun_comp_hasLaw
    ((measurePreserving_eval (fun i => Measure.pi fun j => ν i j) i).fun_comp_hasLaw hX)

/-- The entries of a random matrix with the nested product law are independent, as a family
indexed by `m × n`. -/
theorem _root_.ProbabilityTheory.HasLaw.iIndepFun_entry
    (hX : HasLaw X (Measure.pi fun i => Measure.pi fun j => ν i j) μ) :
    iIndepFun (fun p : m × n => fun ω => X ω p.1 p.2) μ := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 <|
    inferInstanceAs (IsProbabilityMeasure (Measure.pi fun i => Measure.pi fun j => ν i j))
  exact (hasLaw_pi_pi_iff.1 hX).1

end Matrix

section Transport

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {ν : Measure 𝓧} {X : Ω → 𝓧}
  {E : Type*} [NormedAddCommGroup E]

/-- Integrability of `f ∘ X` depends only on the law of `X`. -/
theorem _root_.ProbabilityTheory.HasLaw.integrable_comp_iff (hX : HasLaw X ν μ) {f : 𝓧 → E}
    (hf : AEStronglyMeasurable f ν) :
    Integrable (fun ω => f (X ω)) μ ↔ Integrable f ν := by
  rw [← hX.map_eq] at hf ⊢
  exact (integrable_map_measure hf hX.aemeasurable).symm

/-- Membership of `f ∘ X` in `Lᵖ` depends only on the law of `X`. -/
theorem _root_.ProbabilityTheory.HasLaw.memLp_comp_iff (hX : HasLaw X ν μ) {f : 𝓧 → E}
    (hf : AEStronglyMeasurable f ν) {p : ℝ≥0∞} :
    MemLp (fun ω => f (X ω)) p μ ↔ MemLp f p ν := by
  rw [← hX.map_eq] at hf ⊢
  exact (memLp_map_measure_iff hf hX.aemeasurable).symm
end Transport

end NLAlib
