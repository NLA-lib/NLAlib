/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.List.GetD
public import NLAlib.Matrix.Factorizations.Cholesky
public import NLAlib.Ops.Logic.Layout
public import NLAlib.Ops.Catalog.Orth

/-!
# Stored prefixes of right-looking Cholesky

The residual decodes to the Gaussian state and the completed factor columns are canonical.
All entries are initialized, and the actual words above the diagonal remain the initial zero
literal. This invariant records mathematical values of stored words, without an execution
witness or a nonbreakdown assumption.

## Main results

* `NLAlib.Cholesky.IsRightPrefix.initial`: copied input and zero-filled output.
* `NLAlib.Cholesky.IsRightPrefix.read_factor`: the final canonical factor and literal zeros.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K : Type} {N : ℕ}

/-- The full residual and initialized factor, with canonical completed columns and actual
zero words above the diagonal. Uncommitted columns have decoded value zero. -/
def IsRightPrefix (dec : K → ℝ) (zero : K) (A : Matrix (Fin N) (Fin N) ℝ)
    (k : ℕ) (R L : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ rw lw : ℕ → ℕ → K,
    s.HoldsMat ⟨R.1, R.2, N, N, N⟩ rw ∧
    s.HoldsMat ⟨L.1, L.2, N, N, N⟩ lw ∧
    (∀ i j : Fin N, dec (rw i j) = gaussState A k i j) ∧
    (∀ i j : Fin N, dec (lw i j) = if j.val < k then choleskyLower A i j else 0) ∧
    (∀ i j : Fin N, i < j → lw i j = zero)

variable [Inhabited K]

/-- A copied residual and zero-literal factor block establish the initial stored prefix.
Only the exact decoding of the zero literal is needed. -/
theorem IsRightPrefix.initial {M : Machine K} {dec : K → ℝ} (hM : ExactModel dec M)
    {R L : ℕ × ℕ} {s : Store K} {as : List K}
    (hR : s.readBlock R.1 R.2 (N * N) = some as)
    (hL : s.readBlock L.1 L.2 (N * N) = some (List.replicate (N * N) (M.lit 0))) :
    IsRightPrefix dec (M.lit 0) (decodeMatrix dec N N as) 0 R L s := by
  have hzero : dec (M.lit 0) = 0 := by simpa using hM.lit 0
  refine ⟨fun i j => vec as (j * N + i), fun _ _ => M.lit 0,
    Store.holdsMat_of_readBlock rfl hR, ?_, ?_, ?_, fun _ _ _ => rfl⟩
  · intro i hi j hj
    have hh := Store.holdsMat_of_readBlock (L := ⟨L.1, L.2, N, N, N⟩) rfl hL i hi j hj
    simpa only [vec,
      List.getD_replicate (α := K) (x := M.lit 0) (h := Idx.add_lt_mul hj hi)] using hh
  · intro i j
    rw [gaussState_zero, decodeMatrix_apply]
  · intro i j
    simp only [Nat.not_lt_zero, if_false, hzero]

/-- Replacing one initialized factor-column suffix by its canonical decoded values extends
both the decoded prefix and the actual literal upper zeros. The residual words are supplied
at the next exact Gaussian state; no execution witness is part of this storage constructor. -/
theorem IsRightPrefix.succ {dec : K → ℝ} {zero : K}
    {A : Matrix (Fin N) (Fin N) ℝ} {R L : ℕ × ℕ} {s : Store K}
    (k : Fin N) (rw lw : ℕ → ℕ → K) (ys : List K)
    (hR : s.HoldsMat ⟨R.1, R.2, N, N, N⟩ rw)
    (hL : s.HoldsMat ⟨L.1, L.2, N, N, N⟩
      (fun i j => if j = k.val ∧ k.val ≤ i then vec ys (i - k.val) else lw i j))
    (hres : ∀ i j : Fin N, dec (rw i j) = gaussState A (k.val + 1) i j)
    (hfac : ∀ i j : Fin N, dec (lw i j) = if j.val < k.val then choleskyLower A i j else 0)
    (hupper : ∀ i j : Fin N, i < j → lw i j = zero)
    (hy : ∀ i : Fin N, k ≤ i → dec (vec ys (i.val - k.val)) = choleskyLower A i k) :
    IsRightPrefix dec zero A (k.val + 1) R L s := by
  refine ⟨rw, fun i j => if j = k.val ∧ k.val ≤ i then vec ys (i - k.val) else lw i j,
    hR, hL, hres, ?_, ?_⟩
  · intro i j
    change dec (if j.val = k.val ∧ k.val ≤ i.val then vec ys (i.val - k.val) else lw i j) =
      if j.val < k.val + 1 then choleskyLower A i j else 0
    by_cases hj : j.val < k.val
    · rw [if_neg (fun h => hj.ne h.1), hfac i j, if_pos hj, if_pos (by omega)]
    · by_cases he : j = k
      · subst j
        by_cases hki : k ≤ i
        · rw [if_pos ⟨rfl, hki⟩, hy i hki, if_pos (by omega)]
        · rw [if_neg (fun h => hki h.2), hfac i k, if_neg (lt_irrefl _),
            if_pos (by omega)]
          exact (isLowerTriangular_choleskyLower A (i := i) (j := k) (lt_of_not_ge hki)).symm
      · have hne : j.val ≠ k.val := fun h => he (Fin.ext h)
        rw [if_neg (fun h => hne h.1), hfac i j, if_neg hj, if_neg (by omega)]
  · intro i j hij
    change (if j.val = k.val ∧ k.val ≤ i.val then vec ys (i.val - k.val) else lw i j) = zero
    rw [if_neg (by intro h; have hlt : i.val < j.val := hij; omega)]
    exact hupper i j hij

/-- A completed stored prefix reads as the canonical Cholesky matrix. Its actual upper
words, as well as their decoded values, are zero literals, including the empty matrix. -/
theorem IsRightPrefix.read_factor {dec : K → ℝ} {zero : K}
    {A : Matrix (Fin N) (Fin N) ℝ} {R L : ℕ × ℕ} {s : Store K}
    (h : IsRightPrefix dec zero A N R L s) :
    ∃ ls : List K, s.readBlock L.1 L.2 (N * N) = some ls ∧
      decodeMatrix dec N N ls = choleskyLower A ∧
      (∀ i j : Fin N, i < j → vec ls (j.val * N + i.val) = zero) := by
  obtain ⟨rw, lw, hR, hL, hres, hfac, hupper⟩ := h
  obtain ⟨ls, hls, hlen, hdata⟩ := hL.readBlock rfl
  refine ⟨ls, hls, ?_, ?_⟩
  · ext i j
    rw [decodeMatrix_apply, hdata i i.isLt j j.isLt, hfac i j, if_pos j.isLt]
  · intro i j hij
    rw [hdata i i.isLt j j.isLt]
    exact hupper i j hij

end NLAlib.Cholesky
