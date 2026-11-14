/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Storage
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Ops.Profiles.RoundedScalarBlas
public import NLAlib.Ops.Logic.Builder

/-!
# Norms of interleaved complex words

The real component words of the existing pair codec have the same Euclidean norm as the
complex matrix's Frobenius norm. Scalar norm computations can consume this identity directly.

## Main results

* `NLAlib.ShiftedQR.sum_sq_matrixWords`: squared real-word norm equals squared Frobenius norm.
* `NLAlib.ShiftedQR.matrixNorm_writes`: the actual scalar-lowered Frobenius norm computation.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- The squared Euclidean norm of every interleaved component word is the complex matrix's
squared Frobenius norm. The equality uses the existing pair codec and its column-major order. -/
theorem sum_sq_matrixWords {rows cols : ℕ} (H : Matrix (Fin rows) (Fin cols) ℂ) :
    (∑ q ∈ Finset.range (2 * (cols * rows)), (vec (matrixWords H) q) ^ 2) = frobNorm H ^ 2 := by
  have hwords (i : Fin rows) (j : Fin cols) (z : Fin 2) :
      vec (matrixWords H) (finProdFinEquiv (finProdFinEquiv (j, i), z)) =
        (EntryCodec.pair ℝ).words ((H i j).re, (H i j).im) z := by
    have hv := (EntryCodec.pair ℝ).vec_packFinMatrix
      (H.map fun a => (a.re, a.im)) i j z
    simpa [matrixWords, Matrix.map_apply, finProdFinEquiv, Nat.mul_comm,
      Nat.add_comm] using hv
  rw [Nat.mul_comm 2, ← Fin.sum_univ_eq_sum_range]
  rw [← Equiv.sum_comp
    (finProdFinEquiv : Fin (cols * rows) × Fin 2 ≃ Fin (cols * rows * 2))]
  rw [Fintype.sum_prod_type]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin cols × Fin rows ≃ Fin (cols * rows))]
  simp only [Fintype.sum_prod_type, hwords, Fin.sum_univ_two]
  rw [frobNorm_sq_eq_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  change (H j i).re ^ 2 + (H j i).im ^ 2 = ‖H j i‖ ^ 2
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

variable {Op Tst : Type} [Has ScalarOp Op]

/-- The Frobenius norm of actual interleaved matrix words, using the existing fully scalar
sequential Euclidean-norm lowering. Its square and summation scratch is scoped by that lowering. -/
def matrixNorm : Impl Op Tst := opsImpl% [rows, cols] (H) → (Norm) {
  run RoundedScalarBlas.nrm2.body [2 * (cols * rows)] (H, Norm)
}

/-- Exact scalar arithmetic computes the matrix Frobenius norm directly from every supplied
real and imaginary component word. No matrix norm operation remains a primitive. -/
theorem matrixNorm_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {rows cols : ℕ} {a z : ℕ × ℕ} {H : Matrix (Fin rows) (Fin cols) ℂ}
    (hl : m.Live [a, z]) (hH : HoldsMatrix a H m.store)
    (hz : z.2 < m.store.len z.1) (haz : a.1 ≠ z.1) :
    Writes .total I τ matrixNorm.body (Env.frame [rows, cols] [a, z])
      (Store.inBlock z.1 z.2 1)
      (fun μ => μ.pos = m.pos ∧ μ.store.get z.1 z.2 = some (frobNorm H)) m := by
  have hn := RoundedScalarBlas.writes_nrm2_exact (τ := τ) (xs := matrixWords H)
    (n := 2 * (cols * rows)) hS hE hl hH hz haz
  refine (hn.in_frame rfl rfl hl).mono le_rfl ?_
  intro μ _ ⟨hp, hout⟩
  refine ⟨hp, ?_⟩
  simpa only [sum_sq_matrixWords, Real.sqrt_sq (frobNorm_nonneg H)] using hout


end NLAlib.ShiftedQR
