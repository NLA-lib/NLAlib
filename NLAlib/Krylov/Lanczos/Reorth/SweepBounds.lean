/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.TwoPass
public import NLAlib.Ops.Catalog.Operator
public import NLAlib.Krylov.Lanczos.Math.RoundedLocal

/-!
# Normwise bounds for the actual classical-pass update

The program subtracts projections by sequential axpys. Its normwise bound therefore comes
from the certified axpy chain, rather than the old matrix-vector-product update constants.
No orthogonality or nonbreakdown assumption is needed for this local representation bound.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.PassOut.coefficient_error_le`: normwise coefficient errors.
* `NLAlib.Krylov.Lanczos.Reorth.PassOut.project_error_norm_le`: the accumulated update error.
* `NLAlib.Krylov.Lanczos.Reorth.TwoPassOut.project_error_norm_le`: the combined two-pass error.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops

private theorem norm_le_of_abs_le_sum {n k : ℕ} {e x : Fin n → ℝ}
    {y : ℕ → Fin n → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |e i| ≤ c * (|x i| + ∑ j ∈ Finset.range k, |y j i|)) :
    ‖WithLp.toLp 2 e‖ ≤ c * (‖WithLp.toLp 2 x‖ +
      ∑ j ∈ Finset.range k, ‖WithLp.toLp 2 (y j)‖) := by
  have habs : ∀ z : Fin n → ℝ, ‖WithLp.toLp 2 (fun i => |z i|)‖ = ‖WithLp.toLp 2 z‖ :=
    fun z => by simp [EuclideanSpace.norm_eq]
  have hdom := EuclideanSpace.norm_toLp_le_norm_toLp (x := e)
    (y := c • ((fun i => |x i|) + ∑ j ∈ Finset.range k, fun i => |y j i|)) fun i => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
      rw [abs_of_nonneg (a := c * (|x i| + ∑ j ∈ Finset.range k, |y j i|))
        (mul_nonneg hc (add_nonneg (abs_nonneg _)
          (Finset.sum_nonneg fun _ _ => abs_nonneg _)))]
      exact h i
  refine hdom.trans ?_
  rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [WithLp.toLp_add, WithLp.toLp_sum]
  refine (norm_add_le _ _).trans (add_le_add (habs x).le ?_)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (habs (y j)).le)

/-- The rounded coefficient error is bounded by the dot constant times the column norm and
input norm. This uses Cauchy–Schwarz and does not require an orthogonal basis. -/
theorem PassOut.coefficient_error_le {K : Type} [Inhabited K] {dec : K → ℝ}
    {ed ea : ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec ed ea n k qs ws ws' hs) (hd : 0 ≤ ed) {j : ℕ} (hj : j < k) :
    |dec (vec hs j) - (fun i : Fin n => dec (vec qs (j * n + i))) ⬝ᵥ decv dec n ws| ≤
      ed * ‖WithLp.toLp 2 (fun i : Fin n => dec (vec qs (j * n + i)))‖ *
        ‖WithLp.toLp 2 (decv dec n ws)‖ := by
  let q : Fin n → ℝ := fun i => dec (vec qs (j * n + i))
  let w := decv dec n ws
  have he : |dec (vec hs j) - q ⬝ᵥ w| ≤ ed * ∑ i : Fin n, |q i * w i| := by
    change |dec (vec hs j) - ∑ i : Fin n, dec (vec qs (j * n + i))*dec (vec ws i)| ≤
      ed * ∑ i : Fin n, |dec (vec qs (j * n + i))*dec (vec ws i)|
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => dec (vec qs (j * n + i))*dec (vec ws i)) n,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => |dec (vec qs (j * n + i))*dec (vec ws i)|) n]
    exact h.dot j hj
  have hc := Lanczos.abs_dotProduct_sub_le_of_componentwise
    (x := q) (y := w) (α := dec (vec hs j)) hd
    (by simpa only [abs_sub_comm] using he)
  simpa only [abs_sub_comm] using hc

/-- The update error has an explicit Euclidean bound in terms of the actual computed
coefficient magnitudes and basis-column norms. This remains valid for a dependent basis. -/
theorem PassOut.project_error_norm_le {K : Type} [Inhabited K] {dec : K → ℝ}
    {ed ea : ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec ed ea n k qs ws ws' hs) (ha : 0 ≤ ea) :
    ‖WithLp.toLp 2 (decv dec n ws' - (decv dec n ws -
      ∑ j ∈ Finset.range k, dec (vec hs j) •
        (fun i : Fin n => dec (vec qs (j * n + i)))))‖ ≤
      ((1 + ea) ^ k - 1) * (‖WithLp.toLp 2 (decv dec n ws)‖ +
        ∑ j ∈ Finset.range k, |dec (vec hs j)| *
          ‖WithLp.toLp 2 (fun i : Fin n => dec (vec qs (j * n + i)))‖) := by
  have hγ : 0 ≤ (1 + ea) ^ k - 1 := sub_nonneg.mpr (one_le_pow₀ (by linarith))
  have hb := norm_le_of_abs_le_sum hγ (x := decv dec n ws)
    (y := fun j => dec (vec hs j) • (fun i : Fin n => dec (vec qs (j * n + i))))
    (e := decv dec n ws' - (decv dec n ws - ∑ j ∈ Finset.range k,
      dec (vec hs j) • (fun i : Fin n => dec (vec qs (j * n + i)))))
    (fun i => by simpa only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, decv] using h.backward ha i)
  simpa only [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs] using hb

/-- Both rounded passes give a normwise representation witness with the exact sum of their
computed coefficients. The coefficients are ghost data discarded by the program. -/
theorem TwoPassOut.project_error_norm_le {K : Type} [Inhabited K] {dec : K → ℝ}
    {ed ea : ℝ} {n k : ℕ} {qs ws ws' : List K}
    (h : TwoPassOut dec ed ea n k qs ws ws') (ha : 0 ≤ ea) :
    ∃ mid h₁ h₂ : List K, PassOut dec ed ea n k qs ws mid h₁ ∧
      PassOut dec ed ea n k qs mid ws' h₂ ∧
      ‖WithLp.toLp 2 (decv dec n ws' - (decv dec n ws -
        ∑ j ∈ Finset.range k, (dec (vec h₁ j) + dec (vec h₂ j)) •
          (fun i : Fin n => dec (vec qs (j * n + i)))))‖ ≤
        ((1 + ea) ^ k - 1) * (‖WithLp.toLp 2 (decv dec n ws)‖ +
          ∑ j ∈ Finset.range k, |dec (vec h₁ j)| *
            ‖WithLp.toLp 2 (fun i : Fin n => dec (vec qs (j * n + i)))‖) +
        ((1 + ea) ^ k - 1) * (‖WithLp.toLp 2 (decv dec n mid)‖ +
          ∑ j ∈ Finset.range k, |dec (vec h₂ j)| *
            ‖WithLp.toLp 2 (fun i : Fin n => dec (vec qs (j * n + i)))‖) := by
  obtain ⟨mid, h₁, h₂, hp₁, hp₂⟩ := h
  refine ⟨mid, h₁, h₂, hp₁, hp₂, ?_⟩
  have heq : decv dec n ws' - (decv dec n ws - ∑ j ∈ Finset.range k,
      (dec (vec h₁ j) + dec (vec h₂ j)) • (fun i : Fin n => dec (vec qs (j * n + i)))) =
      (decv dec n mid - (decv dec n ws - ∑ j ∈ Finset.range k,
        dec (vec h₁ j) • (fun i : Fin n => dec (vec qs (j * n + i))))) +
      (decv dec n ws' - (decv dec n mid - ∑ j ∈ Finset.range k,
        dec (vec h₂ j) • (fun i : Fin n => dec (vec qs (j * n + i))))) := by
    simp only [add_smul, Finset.sum_add_distrib]
    abel
  rw [heq, WithLp.toLp_add]
  exact (norm_add_le _ _).trans (add_le_add
    (hp₁.project_error_norm_le ha) (hp₂.project_error_norm_le ha))

end NLAlib.Krylov.Lanczos.Reorth
