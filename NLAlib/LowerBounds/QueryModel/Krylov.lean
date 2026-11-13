/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.Space
public import NLAlib.Krylov.Eigenvalues.PowerIteration
public import NLAlib.LowerBounds.QueryModel.Basic

/-!
# Krylov algorithms in the matrix–vector query model

The start vector is the seed. Each query after the first is the preceding response, so the
matrix is available only through the oracle. After q products the queries and responses give
the existing Krylov matrix, and the last response gives the power vector. A Rayleigh estimate
uses one additional product; its output never receives the matrix.

These are exact oracle representations, without claims about scalar arithmetic, storage or
finite precision. They supply actual consumers of the adaptive query model.

## Main results

* `NLAlib.run_powerQueryAlgorithm`: exact agreement with a matrix power applied to the seed.
* `NLAlib.queryMatrix_powerQueryAlgorithm`: queries are the existing Krylov matrix.
* `NLAlib.run_powerRayleighQueryAlgorithm`: q+1 queries give the power Rayleigh estimate.
* `NLAlib.isMeasurableFamily_powerQueryAlgorithm`: joint seed/history measurability.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Power iteration with start vector as seed and exactly q oracle rounds. The initial query
is the seed; each later query is the preceding response. The output is the last response, or
the seed for zero rounds. No matrix is supplied to the algorithm.
[TrefethenBau1997, §27].
Algorithm: power-iteration (run model) -/
def powerQueryAlgorithm (b : n → 𝕜) (q : ℕ) :
    QueryAlgorithm (n → 𝕜) (n → 𝕜) q (n → 𝕜) where
  query
    | 0, _ => b
    | i + 1, h => h (Fin.last i)
  output h := match q with
    | 0 => b
    | i + 1 => h (Fin.last i)

/-- Query i of the seeded power iteration is exactly the i-th power of the matrix applied
to the start. The identity also holds beyond the declared query budget, since histories are
total; only indices below q are executed. -/
theorem queryAt_powerQueryAlgorithm (A : Matrix n n 𝕜) (b : n → 𝕜) (q i : ℕ) :
    (powerQueryAlgorithm b q).queryAt A.mulVec i = A ^ i *ᵥ b := by
  induction i with
  | zero => simp [QueryAlgorithm.queryAt, powerQueryAlgorithm]
  | succ i ih =>
    change (powerQueryAlgorithm b q).history A.mulVec (i + 1) (Fin.last i) = _
    rw [QueryAlgorithm.history_apply, Fin.val_last, ih]
    simp only [pow_succ', ← Matrix.mulVec_mulVec]

/-- The q-query power algorithm returns exactly the q-th power vector, including q=0. -/
theorem run_powerQueryAlgorithm (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    (powerQueryAlgorithm b q).run A.mulVec = A ^ q *ᵥ b := by
  cases q with
  | zero => simp [QueryAlgorithm.run, powerQueryAlgorithm]
  | succ q =>
    change (powerQueryAlgorithm b (q + 1)).history A.mulVec (q + 1) (Fin.last q) = _
    rw [QueryAlgorithm.history_apply, queryAt_powerQueryAlgorithm]
    simp only [Fin.val_last, pow_succ', ← Matrix.mulVec_mulVec]

/-- The actual query matrix of power iteration is the library's Krylov matrix with q
generators. This identifies the query span used by lower bounds with the existing space. -/
theorem queryMatrix_powerQueryAlgorithm (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    (powerQueryAlgorithm b q).queryMatrix ((powerQueryAlgorithm b q).transcript A.mulVec) =
      krylovMatrix A b q := by
  ext a j
  change (powerQueryAlgorithm b q).queries _ j a = _
  rw [← QueryAlgorithm.queryAt_eq_queries_transcript, queryAt_powerQueryAlgorithm]
  rfl

/-- The range of the actual power queries is the existing Krylov space. -/
theorem range_queryMatrix_powerQueryAlgorithm (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    LinearMap.range ((powerQueryAlgorithm b q).queryMatrix
      ((powerQueryAlgorithm b q).transcript A.mulVec)).mulVecLin = krylovSpace A b q := by
  rw [queryMatrix_powerQueryAlgorithm]
  rfl

omit [RCLike 𝕜] [Fintype n] [DecidableEq n] in
/-- Power iteration is pass-structured with one response-dependent query per pass.
Its executed pass labels satisfy i < q, so q passes suffice. -/
theorem isPassStructured_powerQueryAlgorithm (b : n → 𝕜) (q : ℕ) :
    (powerQueryAlgorithm b q).IsPassStructured id :=
  QueryAlgorithm.isPassStructured_id _

omit [Fintype n] [DecidableEq n] in
/-- With a nonempty vector coordinate type and at least two rounds, power iteration is
genuinely adaptive: its second query can distinguish two possible first responses. -/
theorem not_isNonAdaptive_powerQueryAlgorithm [Nonempty n] (b : n → 𝕜) (q : ℕ) :
    ¬ (powerQueryAlgorithm b (q + 2)).IsNonAdaptive := by
  intro h
  have he := h 1 (by omega) (fun _ => 0) (fun _ => 1)
  obtain ⟨a⟩ := ‹Nonempty n›
  exact zero_ne_one (congrFun he a)

omit [Fintype n] [DecidableEq n] in
/-- The seeded power family is jointly measurable in its seed and response history. -/
theorem isMeasurableFamily_powerQueryAlgorithm (q : ℕ) :
    QueryAlgorithm.IsMeasurableFamily (fun b : n → 𝕜 => powerQueryAlgorithm b q) := by
  constructor
  · intro i hi
    cases i <;> simp only [powerQueryAlgorithm] <;> fun_prop
  · cases q <;> simp only [powerQueryAlgorithm] <;> fun_prop

/-- The power Rayleigh estimator uses q+1 matrix–vector rounds: q to form the power vector
and one to evaluate its quadratic form. Its seed is only the start vector; the output uses
the last two successive vectors and has no direct matrix access. At q=0 it queries the start.
[TrefethenBau1997, §27].
Algorithm: power-iteration (run model) -/
noncomputable def powerRayleighQueryAlgorithm (b : n → 𝕜) (q : ℕ) :
    QueryAlgorithm (n → 𝕜) (n → 𝕜) (q + 1) ℝ where
  query := (powerQueryAlgorithm b (q + 1)).query
  output τ :=
    RCLike.re (star ((powerQueryAlgorithm b q).output (fun j => τ j.castSucc)) ⬝ᵥ
      τ (Fin.last q)) /
      ‖WithLp.toLp 2 ((powerQueryAlgorithm b q).output (fun j => τ j.castSucc))‖ ^ 2

/-- The Rayleigh power algorithm and power-vector algorithm have the same queries. -/
theorem queryAt_powerRayleighQueryAlgorithm (A : Matrix n n 𝕜) (b : n → 𝕜) (q i : ℕ) :
    (powerRayleighQueryAlgorithm b q).queryAt A.mulVec i = A ^ i *ᵥ b := by
  induction i with
  | zero => simp [QueryAlgorithm.queryAt, powerRayleighQueryAlgorithm, powerQueryAlgorithm]
  | succ i ih =>
    change (powerRayleighQueryAlgorithm b q).history A.mulVec (i + 1) (Fin.last i) = _
    rw [QueryAlgorithm.history_apply, Fin.val_last, ih]
    simp only [pow_succ', ← Matrix.mulVec_mulVec]

/-- The q+1-query Rayleigh power estimator returns the existing Rayleigh quotient at the
q-th power vector. The extra product is included in its query budget. -/
theorem run_powerRayleighQueryAlgorithm (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    (powerRayleighQueryAlgorithm b q).run A.mulVec =
      rayleighQuotient A (A ^ q *ᵥ b) := by
  have hτ (j : Fin (q + 1)) :
      (powerRayleighQueryAlgorithm b q).transcript A.mulVec j = A ^ (j.val + 1) *ᵥ b := by
    rw [QueryAlgorithm.transcript, QueryAlgorithm.history_apply,
      queryAt_powerRayleighQueryAlgorithm, pow_succ', ← Matrix.mulVec_mulVec]
  have hv : (powerQueryAlgorithm b q).output
      (fun j => (powerRayleighQueryAlgorithm b q).transcript A.mulVec j.castSucc) =
        A ^ q *ᵥ b := by
    cases q with
    | zero => simp [powerQueryAlgorithm]
    | succ q => simp only [powerQueryAlgorithm, hτ, Fin.val_castSucc, Fin.val_last]
  change RCLike.re (star _ ⬝ᵥ _) / _ = _
  rw [hv, hτ]
  simp only [Fin.val_last, pow_succ', ← Matrix.mulVec_mulVec, rayleighQuotient, quadForm]

omit [DecidableEq n] in
/-- The Rayleigh power estimator has one response-dependent query per pass, including the
final product used to form the Rayleigh quotient. -/
theorem isPassStructured_powerRayleighQueryAlgorithm (b : n → 𝕜) (q : ℕ) :
    (powerRayleighQueryAlgorithm b q).IsPassStructured id :=
  QueryAlgorithm.isPassStructured_id _

omit [DecidableEq n] in
/-- The seeded Rayleigh power estimator is jointly measurable in seed and responses,
including a zero power vector, whose Rayleigh estimate is zero. -/
theorem isMeasurableFamily_powerRayleighQueryAlgorithm (q : ℕ) :
    QueryAlgorithm.IsMeasurableFamily
      (fun b : n → 𝕜 => powerRayleighQueryAlgorithm b q) := by
  constructor
  · intro i hi
    cases i <;> simp only [powerRayleighQueryAlgorithm, powerQueryAlgorithm] <;> fun_prop
  · cases q <;> simp only [powerRayleighQueryAlgorithm, powerQueryAlgorithm] <;> fun_prop

/-- The existing gapped power bound applies directly to the oracle estimator's output.
The seed has positive spectral mass at c, and the remaining spectrum lies in [-r,r], r<|c|.
The algorithm uses q+1 oracle rounds, including evaluation of the final Rayleigh quotient. -/
theorem _root_.Matrix.IsHermitian.abs_sub_run_powerRayleighQueryAlgorithm_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c r : ℝ} (hrc : r < |c|)
    (hs : spectrum ℝ A ⊆ Set.Icc (-r) r ∪ {c}) (b : n → 𝕜)
    (hb : 0 < (spectralMeasure A b).real {c}) (q : ℕ) :
    |c - (powerRayleighQueryAlgorithm b q).run A.mulVec| ≤
      (|c| + r) * (r / |c|) ^ (2 * q) * spectralTangentSq A b c := by
  rw [run_powerRayleighQueryAlgorithm]
  exact hA.abs_sub_rayleighQuotient_pow_mulVec_le hrc hs b hb q

end NLAlib
