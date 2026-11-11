/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.TwoPass
public import NLAlib.Ops.Blas.Decoded
public import NLAlib.Krylov.Processes.LanczosReorthRecurrence

/-!
# Exact specialization of classical reorthogonalization

Zero local errors give the classical projection equations. The certificates still establish
total execution, including zero dimensions and dependent or zero basis columns.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.cgs2_spec_exact`: exact total two-pass certificate.
* `NLAlib.Krylov.Lanczos.Reorth.PassOut.update_eq`: exact decoded projection update.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has Blas1Op Op]

omit [Has ScalarOp Op] in
private theorem axpy_zero {dec : K → ℝ} {ok : ℕ → Prop} {I : Interp Op Tst K}
    (h : IsExactBlas1 dec ok I) :
    I.Meets .total (Has.inj Blas1Op.axpy) ((axpyRel dec 0).spec (InPlace ok)) := by
  refine h.axpy.mono (fun _ _ _ _ _ hp => hp) ?_
  intro d ins outs τ m m' _ hpost
  obtain ⟨X, hread, hroom, Y, hlen, hrel, hm⟩ := hpost
  refine ⟨X, hread, hroom, Y, hlen, ?_, hm⟩
  simp only [axpyExactRel_rel] at hrel
  split at hrel
  · simpa [axpyRel, IsAxpyErr, sub_eq_zero] using hrel
  · contradiction

/-- An exact machine and exact level-1 operations give a total exact classical pass. -/
theorem cgsPass_spec_exact {M : Machine K} {dec : K → ℝ} {ok : ℕ → Prop}
    {I : Interp Op Tst K} (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec ok I) :
    (cgsPassImpl (Op := Op) (Tst := Tst)).Meets I .total
      ((passRel dec (fun _ => 0) 0).spec (PassOperands ok)) :=
  cgsPass_spec hS hB.dot_zero (axpy_zero hB) hM.neg

/-- Both exact classical passes execute without rank or nonbreakdown assumptions. -/
theorem cgs2_spec_exact {M : Machine K} {dec : K → ℝ} {ok : ℕ → Prop}
    {I : Interp Op Tst K} (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec ok I) :
    (cgs2Impl (Op := Op) (Tst := Tst)).Meets I .total
      ((twoPassRel dec (fun _ => 0) 0).spec (TwoPassOperands ok)) :=
  cgs2_spec hS hB.dot_zero (axpy_zero hB) hM.neg

omit [Has ScalarOp Op] [Has Blas1Op Op] in
/-- Each exact coefficient uses the vector from the start of the classical pass. -/
theorem PassOut.dot_eq {dec : K → ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec 0 0 n k qs ws ws' hs) {j : ℕ} (hj : j < k) :
    dec (vec hs j) = ∑ i ∈ Finset.range n, dec (vec qs (j * n + i)) * dec (vec ws i) := by
  simpa [IsDotErr, sub_eq_zero] using h.dot j hj

omit [Has ScalarOp Op] [Has Blas1Op Op] in
/-- With zero axpy error the updated vector is exactly the input minus all projections. -/
theorem PassOut.update_eq {dec : K → ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec 0 0 n k qs ws ws' hs) (i : Fin n) :
    dec (vec ws' i) = dec (vec ws i) -
      ∑ j ∈ Finset.range k, dec (vec hs j) * dec (vec qs (j * n + i)) := by
  have hb := h.backward (by rfl) i
  simpa [sub_eq_zero] using hb

omit [Has ScalarOp Op] [Has Blas1Op Op] in
/-- The decoded pass is the existing pure classical Gram–Schmidt projection. -/
theorem PassOut.project_eq {dec : K → ℝ} {n k : ℕ} {qs ws ws' hs : List K}
    (h : PassOut dec 0 0 n k qs ws ws' hs) :
    decv dec n ws' = cgsProject (fun j (i : Fin n) => dec (vec qs (j * n + i))) k
      (decv dec n ws) := by
  funext i
  rw [show decv dec n ws' i = dec (vec ws' i) from rfl, h.update_eq i]
  simp only [cgsProject, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h.dot_eq (Finset.mem_range.mp hj)]
  congr 1
  symm
  simpa [dotProduct, decv] using
    Fin.sum_univ_eq_sum_range (fun t : ℕ => dec (vec qs (j * n + t)) * dec (vec ws t)) n

omit [Has ScalarOp Op] [Has Blas1Op Op] in
/-- Two exact program passes coincide with the two projections of the old pure recurrence. -/
theorem TwoPassOut.project_eq {dec : K → ℝ} {n k : ℕ} {qs ws ws' : List K}
    (h : TwoPassOut dec 0 0 n k qs ws ws') :
    decv dec n ws' = cgsProject (fun j (i : Fin n) => dec (vec qs (j * n + i))) k
      (cgsProject (fun j (i : Fin n) => dec (vec qs (j * n + i))) k (decv dec n ws)) := by
  obtain ⟨mid, hs₁, hs₂, h₁, h₂⟩ := h
  rw [h₂.project_eq, h₁.project_eq]

end NLAlib.Krylov.Lanczos.Reorth
