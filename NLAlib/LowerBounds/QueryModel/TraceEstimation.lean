/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.GirardHutchinson
public import NLAlib.LowerBounds.QueryModel.Basic

/-!
# Trace estimators in the matrix–vector query model

Girard–Hutchinson is a nonadaptive query algorithm: the seed is the probe matrix, queries are
its columns, and the output pairs each response with its probe and averages. The algorithm
receives the matrix only through its oracle responses. The run equality connects the same
estimator used by the probability upper bounds to the response-history model of lower bounds.
It supplies an instance of that model, rather than a new trace-estimation lower bound.

## Main results

* `NLAlib.run_girardHutchinsonQueryAlgorithm`: the oracle run is `NLAlib.girardHutchinson`.
* `NLAlib.isNonAdaptive_girardHutchinsonQueryAlgorithm`: the queries use no responses.
* `NLAlib.isMeasurableFamily_girardHutchinsonQueryAlgorithm`: joint seed/history measurability.
* `NLAlib.integral_run_girardHutchinsonQueryAlgorithm`: isotropic probes give unbiased runs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] {q : ℕ}

/-- The Girard–Hutchinson query algorithm with seed $\mathbf{\Omega}$ having $q$ probe columns:
query $j$ is column $j$ of the seed and the output is the average of each probe's inner product
with its response. There are exactly $q$ query rounds. Neither queries nor output receive
$\mathbf{A}$; running against its matrix–vector oracle computes
$\mathsf{girardHutchinson}(\mathbf{A},\mathbf{\Omega})$. For $q = 0$ the output is zero.
[Epperly2023, Girard–Hutchinson Estimator: The Basics].
Algorithm: girard-hutchinson (run model) -/
noncomputable def girardHutchinsonQueryAlgorithm (Ω : Matrix n (Fin q) 𝕜) :
    QueryAlgorithm (n → 𝕜) (n → 𝕜) q 𝕜 where
  query i _ := if hi : i < q then fun a => Ω a ⟨i, hi⟩ else 0
  output τ := (∑ j, ∑ i, star (Ω i j) * τ j i) / q

/-- The Girard–Hutchinson query algorithm is nonadaptive: every query depends only on the seed,
not on any oracle response. -/
theorem isNonAdaptive_girardHutchinsonQueryAlgorithm (Ω : Matrix n (Fin q) 𝕜) :
    (girardHutchinsonQueryAlgorithm Ω).IsNonAdaptive := by
  intro i hi h h'
  rfl

/-- Running the seeded Girard–Hutchinson algorithm against the oracle
$\mathbf{x}\mapsto\mathbf{A}\mathbf{x}$ gives exactly
$\mathsf{girardHutchinson}(\mathbf{A},\mathbf{\Omega})$, for every square matrix over
$\Bbbk$ and every probe seed, including the zero-query case. -/
theorem run_girardHutchinsonQueryAlgorithm (A : Matrix n n 𝕜) (Ω : Matrix n (Fin q) 𝕜) :
    (girardHutchinsonQueryAlgorithm Ω).run A.mulVec = girardHutchinson A Ω := by
  rw [girardHutchinson_eq_sum]
  change (∑ j, ∑ i, star (Ω i j) *
    (girardHutchinsonQueryAlgorithm Ω).history A.mulVec q j i) / (q : 𝕜) = _
  simp only [Fintype.card_fin]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [QueryAlgorithm.history_apply]
  simp only [QueryAlgorithm.queryAt, girardHutchinsonQueryAlgorithm, dif_pos j.isLt]
  rfl

/-- Relabelling the ambient coordinates transports the Girard–Hutchinson oracle algorithm
without changing its output or query count. Queries are sent along the coordinate equivalence
and responses read back along its inverse; the estimator still sees only matrix–vector products.
This is a same-dimension simulation, with no assertion about larger padded dimensions. -/
theorem run_mapQuery_comapResponse_girardHutchinsonQueryAlgorithm {n' : Type*} [Fintype n']
    (e : n ≃ n') (A : Matrix n n 𝕜) (Ω : Matrix n (Fin q) 𝕜) :
    (((girardHutchinsonQueryAlgorithm Ω).mapQuery (fun v => v ∘ e.symm)).comapResponse
      (fun v => v ∘ e)).run (Matrix.reindex e e A).mulVec = girardHutchinson A Ω := by
  rw [QueryAlgorithm.run_comapResponse, QueryAlgorithm.run_mapQuery]
  have horacle : ((fun v => v ∘ e) ∘ (Matrix.reindex e e A).mulVec) ∘
      (fun v => v ∘ e.symm) = A.mulVec := by
    funext v i
    simp only [Function.comp_apply, Matrix.reindex_apply]
    rw [Matrix.submatrix_mulVec_equiv A (v ∘ e.symm) e.symm e.symm]
    simp only [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id,
      Function.comp_apply, Equiv.symm_apply_apply]
  rw [horacle]
  exact run_girardHutchinsonQueryAlgorithm A Ω

/-- The Girard–Hutchinson family is jointly measurable in the probe seed and response history.
It therefore meets the randomized-algorithm measurability hypothesis used in query lower bounds.
No distribution on the probes is needed for this structural property. -/
theorem isMeasurableFamily_girardHutchinsonQueryAlgorithm :
    QueryAlgorithm.IsMeasurableFamily
      (girardHutchinsonQueryAlgorithm (𝕜 := 𝕜) (n := n) (q := q)) := by
  constructor
  · intro i hi
    simp only [girardHutchinsonQueryAlgorithm, dif_pos hi]
    fun_prop
  · change Measurable fun p : Matrix n (Fin q) 𝕜 × (Fin q → n → 𝕜) =>
      (∑ j, ∑ i, star (p.1 i j) * p.2 j i) / (q : 𝕜)
    fun_prop

/-- For a positive number of isotropic probes, the Girard–Hutchinson oracle run is unbiased:
its expectation equals $\operatorname{tr}\mathbf{A}$. Probe independence is not required.
This consumes the oracle-run equality with the existing estimator's probability theorem;
it asserts no lower bound. [Epperly2023, Unbiasedness]. -/
theorem integral_run_girardHutchinsonQueryAlgorithm {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [DecidableEq n] [Nonempty (Fin q)] {X : Ω → Matrix n (Fin q) 𝕜}
    (hX : ∀ j, IsIsotropic (fun ω i => X ω i j) μ) (A : Matrix n n 𝕜) :
    ∫ ω, (girardHutchinsonQueryAlgorithm (X ω)).run A.mulVec ∂μ = A.trace := by
  simp only [run_girardHutchinsonQueryAlgorithm]
  exact integral_girardHutchinson hX A

end NLAlib
