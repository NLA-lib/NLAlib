/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlus
public import NLAlib.Matrix.Factorizations.MGS.Math

/-!
# Matrix identities for the rank-revealing Hutch++ implementation

The MGS sweep is the complementary range projection even when the sketch image is
rank deficient. Quadratic forms of the concatenated basis and residual probes then
recover the existing mathematical estimator.

## Main results

* `NLAlib.HutchPlusPlus.mgsSweep_column_gramSchmidtQ` is the projection identity.
* `NLAlib.HutchPlusPlus.hutchpp_eq_of_mgsSweep` identifies the explicit trace sums.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib.HutchPlusPlus

variable {𝕜 : Type} [RCLike 𝕜]

/-- Concatenate the retained basis and probe matrices in column-major order. -/
def basisProbes {n k ell : ℕ} (Q : Matrix (Fin n) (Fin k) 𝕜)
    (G : Matrix (Fin n) (Fin ell) 𝕜) : Matrix (Fin n) (Fin (k + ell)) 𝕜 :=
  Matrix.of fun i j => if hj : (j : ℕ) < k then Q i ⟨j, hj⟩
    else G i ⟨j - k, by omega⟩

/-- A finite matrix column addressed by a natural index, with zero outside its columns.
This is mathematical padding; executable reads are justified by actual column bounds. -/
def column {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) (j : ℕ) : Fin m → 𝕜 :=
  fun i => if h : j < n then A i ⟨j, h⟩ else 0

/-- A valid natural column index selects the corresponding actual finite column. -/
theorem column_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) (j : ℕ) (hj : j < n) :
    column A j = (fun i => A i ⟨j, hj⟩) := by
  funext i
  simp [column, hj]

/-- Keep a basis prefix and sweep each remaining probe against all basis columns. -/
def projectedBasis {n k ell : ℕ} (Q : Matrix (Fin n) (Fin k) 𝕜)
    (G : Matrix (Fin n) (Fin ell) 𝕜) : Matrix (Fin n) (Fin (k + ell)) 𝕜 :=
  Matrix.of fun i j => if hj : (j : ℕ) < k then Q i ⟨j, hj⟩ else
    mgsSweep (column Q) (column G (j - k)) k i

/-- Summing column quadratic forms gives the trace of the compressed operator. -/
theorem sum_column_eq_trace {N n m : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (W : Matrix (Fin N) (Fin n) 𝕜) (M : Matrix (Fin N) (Fin m) 𝕜) (c0 : ℕ) (hm : c0 + m ≤ n)
    (hW : ∀ (a : Fin N) (j : Fin m), W a ⟨c0 + j, by omega⟩ = M a j) :
    ∑ j ∈ Finset.range m, star (column W (c0 + j)) ⬝ᵥ column (A * W) (c0 + j) =
      (Mᴴ * A * M).trace := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => star (column W (c0 + j)) ⬝ᵥ column (A * W) (c0 + j)),
    Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : c0 + j < n := by omega
  rw [Matrix.diag, Matrix.mul_assoc]
  simp only [column, hj, dif_pos, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct, Pi.star_apply, hW]

/-- The concatenated basis and projected probes compute the mathematical estimator. -/
theorem hutchpp_eq_column {N k ℓ : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (S : Matrix (Fin N) (Fin k) 𝕜) (G : Matrix (Fin N) (Fin ℓ) 𝕜)
    (W : Matrix (Fin N) (Fin (k + ℓ)) 𝕜)
    (hWQ : ∀ (a : Fin N) (c : Fin k), W a ⟨c, by omega⟩ = gramSchmidtQ (A * S) a c)
    (hWG : ∀ (a : Fin N) (j : Fin ℓ), W a ⟨k + j, by omega⟩ =
      ((1 - gramSchmidtQ (A * S) * (gramSchmidtQ (A * S))ᴴ) * G : Matrix (Fin N) (Fin ℓ) 𝕜) a j) :
    (0 + ∑ j ∈ Finset.range k, star (column W j) ⬝ᵥ column (A * W) j) +
      (0 + ∑ j ∈ Finset.range ℓ, star (column W (k + j)) ⬝ᵥ column (A * W) (k + j)) / ℓ =
      hutchpp A S G := by
  set Q := gramSchmidtQ (A * S)
  rw [hutchpp_eq_of_mul_conjTranspose_self_eq_rangeProjector (gramSchmidtQ_mul_conjTranspose _) G,
    girardHutchinson, Fintype.card_fin, zero_add, zero_add,
    sum_column_eq_trace A W ((1 - Q * Qᴴ) * G) k le_rfl hWG]
  have h1 := sum_column_eq_trace A W Q 0 (by omega) fun a c => by simpa using hWQ a c
  simp only [zero_add] at h1
  rw [h1]
  congr 2
  have hP : (1 - Q * Qᴴ)ᴴ = 1 - Q * Qᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  rw [Matrix.conjTranspose_mul, hP]
  simp only [Matrix.mul_assoc]
  rfl

/-- A full sweep against the rank-revealing Gram–Schmidt columns is a residual projection. -/
theorem mgsSweep_column_gramSchmidtQ {N k : ℕ} (Y : Matrix (Fin N) (Fin k) 𝕜)
    (g : Fin N → 𝕜) (a : Fin N) :
    mgsSweep (column (gramSchmidtQ Y)) g k a =
      ((1 - gramSchmidtQ Y * (gramSchmidtQ Y)ᴴ) *ᵥ g) a := by
  set Q := gramSchmidtQ Y
  have hcol : ∀ i (h : i < k), column Q i = Q.col ⟨i, h⟩ := fun i h => by
    ext b; simp [column, h, Matrix.col]
  rw [mgsSweep_eq_sub_sum]
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.sub_apply, ← Matrix.mulVec_mulVec]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => (star (column Q i) ⬝ᵥ g) • column Q i) k,
      Finset.sum_apply, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcol i i.2]
    simp [Matrix.mulVec, dotProduct, Matrix.col, mul_comm]
  · intro i hi j hj
    rw [hcol i hi, hcol j (hj.trans hi)]
    have h := congrFun (congrFun (conjTranspose_gramSchmidtQ_mul_self Y) ⟨i, hi⟩) ⟨j, hj.trans hi⟩
    rw [Matrix.mul_apply, Matrix.diagonal_apply_ne _ (by simp [Fin.ext_iff]; omega)] at h
    rw [← h, dotProduct]
    rfl

/-- The explicit post-MGS trace accumulation equals Hutch++, including deficient rank. -/
theorem hutchpp_eq_of_mgsSweep {N k ℓ : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (S : Matrix (Fin N) (Fin k) 𝕜) (G : Matrix (Fin N) (Fin ℓ) 𝕜) :
    (let W : Matrix (Fin N) (Fin (k + ℓ)) 𝕜 := Matrix.of fun a c =>
        if h : (c : ℕ) < k then gramSchmidtQ (A * S) a ⟨c, h⟩
        else mgsSweep (column (gramSchmidtQ (A * S))) (column G (c - k)) k a;
      (0 + ∑ j ∈ Finset.range k, star (column W j) ⬝ᵥ column (A * W) j) +
        (0 + ∑ j ∈ Finset.range ℓ, star (column W (k + j)) ⬝ᵥ column (A * W) (k + j)) / ℓ) =
      hutchpp A S G := by
  refine hutchpp_eq_column A S G _ (fun a c => by simp [c.2]) fun a j => ?_
  have h := mgsSweep_column_gramSchmidtQ (A * S) (column G j) a
  simp only [Matrix.of_apply, show ¬ (k + (j : ℕ) < k) by omega, dif_neg, not_false_eq_true,
    show k + (j : ℕ) - k = j by omega]
  rw [h]
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, column]

end NLAlib.HutchPlusPlus
