/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.List.GetD
public import NLAlib.Matrix.Factorizations.LUEntries
public import NLAlib.Ops.Logic.Layout
public import NLAlib.Ops.Catalog.Orth

/-!
# Stored prefixes of canonical LU factors

The Gaussian residual and the committed factor entries are mathematical values of actual
stored words. Future lower columns and upper rows remain initialized with decoded zeros.
The unpivoted and pivoted drivers use the same invariant, with the latter changing the
permuted input matrix between steps.

## Main results

* `NLAlib.LU.IsFactorPrefix.read_factors`: a completed prefix supplies actual factor blocks
  whose decoded matrices are the canonical factors.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K : Type} {N : ℕ}

/-- Actual stored residual and factor prefixes. The residual decodes to the Gaussian state;
completed lower columns and upper rows are canonical, and the remaining factor entries are
decoded zeros. Every entry is initialized; no successful-execution witness is included. -/
def IsFactorPrefix (dec : K → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ)
    (R L U : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ rw lw uw : ℕ → ℕ → K,
    s.HoldsMat ⟨R.1, R.2, N, N, N⟩ rw ∧
    s.HoldsMat ⟨L.1, L.2, N, N, N⟩ lw ∧
    s.HoldsMat ⟨U.1, U.2, N, N, N⟩ uw ∧
    (∀ i j : Fin N, dec (rw i j) = gaussState A k i j) ∧
    (∀ i j : Fin N, dec (lw i j) = if j.val < k then luLower A i j else 0) ∧
    (∀ i j : Fin N, dec (uw i j) = if i.val < k then luUpper A i j else 0)

variable [Inhabited K]

/-- Actual readable residual and factor blocks with the stated decoded entries reconstruct
the stored prefix invariant. No alternative word packing is introduced. -/
theorem IsFactorPrefix.of_reads {dec : K → ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    {k : ℕ} {R L U : ℕ × ℕ} {s : Store K} {rs ls us : List K}
    (hR : s.readBlock R.1 R.2 (N * N) = some rs)
    (hL : s.readBlock L.1 L.2 (N * N) = some ls)
    (hU : s.readBlock U.1 U.2 (N * N) = some us)
    (hres : ∀ i j : Fin N, decodeMatrix dec N N rs i j = gaussState A k i j)
    (hlo : ∀ i j : Fin N,
      decodeMatrix dec N N ls i j = if j.val < k then luLower A i j else 0)
    (hup : ∀ i j : Fin N,
      decodeMatrix dec N N us i j = if i.val < k then luUpper A i j else 0) :
    IsFactorPrefix dec A k R L U s := by
  refine ⟨fun i j => vec rs (j * N + i), fun i j => vec ls (j * N + i),
    fun i j => vec us (j * N + i), Store.holdsMat_of_readBlock rfl hR,
    Store.holdsMat_of_readBlock rfl hL, Store.holdsMat_of_readBlock rfl hU, ?_, ?_, ?_⟩
  · intro i j
    simpa only [decodeMatrix_apply] using hres i j
  · intro i j
    simpa only [decodeMatrix_apply] using hlo i j
  · intro i j
    simpa only [decodeMatrix_apply] using hup i j

/-- A copied residual and zero-literal factor blocks satisfy the initial prefix. Exact scalar
arithmetic is used only to decode the zero literal. -/
theorem IsFactorPrefix.initial {M : Machine K} {dec : K → ℝ} (hM : ExactModel dec M)
    {R L U : ℕ × ℕ} {s : Store K} {as : List K}
    (hR : s.readBlock R.1 R.2 (N * N) = some as)
    (hL : s.readBlock L.1 L.2 (N * N) = some (List.replicate (N * N) (M.lit 0)))
    (hU : s.readBlock U.1 U.2 (N * N) = some (List.replicate (N * N) (M.lit 0))) :
    IsFactorPrefix dec (decodeMatrix dec N N as) 0 R L U s := by
  have hzero : dec (M.lit 0) = 0 := by simpa using hM.lit 0
  refine ⟨fun i j => vec as (j * N + i), fun _ _ => M.lit 0,
    fun _ _ => M.lit 0, Store.holdsMat_of_readBlock rfl hR, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj
    have hh := Store.holdsMat_of_readBlock (L := ⟨L.1, L.2, N, N, N⟩) rfl hL i hi j hj
    have he : vec (List.replicate (N * N) (M.lit 0)) (j * N + i) = M.lit 0 :=
      List.getD_replicate (α := K) (x := M.lit 0) (h := Idx.add_lt_mul hj hi)
    dsimp only at hh
    rwa [he] at hh
  · intro i hi j hj
    have hh := Store.holdsMat_of_readBlock (L := ⟨U.1, U.2, N, N, N⟩) rfl hU i hi j hj
    have he : vec (List.replicate (N * N) (M.lit 0)) (j * N + i) = M.lit 0 :=
      List.getD_replicate (α := K) (x := M.lit 0) (h := Idx.add_lt_mul hj hi)
    dsimp only at hh
    rwa [he] at hh
  · intro i j
    rw [gaussState_zero, decodeMatrix_apply]
  · intro i j
    simp only [Nat.not_lt_zero, if_false, hzero]
  · intro i j
    simp only [Nat.not_lt_zero, if_false, hzero]

/-- Every stored prefix supplies its actual residual and factor blocks. Their decoded entries
are the current Gaussian state and canonical factors up to the committed columns and rows. -/
theorem IsFactorPrefix.read_blocks {dec : K → ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    {k : ℕ} {R L U : ℕ × ℕ} {s : Store K} (h : IsFactorPrefix dec A k R L U s) :
    ∃ rs ls us : List K,
      s.readBlock R.1 R.2 (N * N) = some rs ∧
      s.readBlock L.1 L.2 (N * N) = some ls ∧
      s.readBlock U.1 U.2 (N * N) = some us ∧
      (∀ i j : Fin N, decodeMatrix dec N N rs i j = gaussState A k i j) ∧
      (∀ i j : Fin N,
        decodeMatrix dec N N ls i j = if j.val < k then luLower A i j else 0) ∧
      (∀ i j : Fin N,
        decodeMatrix dec N N us i j = if i.val < k then luUpper A i j else 0) := by
  obtain ⟨rw, lw, uw, hR, hL, hU, hres, hlo, hup⟩ := h
  obtain ⟨rs, hrs, hrlen, hrdata⟩ := hR.readBlock rfl
  obtain ⟨ls, hls, hllen, hldata⟩ := hL.readBlock rfl
  obtain ⟨us, hus, hulen, hudata⟩ := hU.readBlock rfl
  refine ⟨rs, ls, us, hrs, hls, hus, ?_, ?_, ?_⟩
  · intro i j
    rw [decodeMatrix_apply, hrdata i i.isLt j j.isLt]
    exact hres i j
  · intro i j
    rw [decodeMatrix_apply, hldata i i.isLt j j.isLt]
    exact hlo i j
  · intro i j
    rw [decodeMatrix_apply, hudata i i.isLt j j.isLt]
    exact hup i j

/-- A completed stored prefix yields actual readable factor blocks with the canonical decoded
matrices. The empty matrix follows from the same reads and requires no entry witness. -/
theorem IsFactorPrefix.read_factors {dec : K → ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    {R L U : ℕ × ℕ} {s : Store K} (h : IsFactorPrefix dec A N R L U s) :
    ∃ ls us : List K,
      s.readBlock L.1 L.2 (N * N) = some ls ∧
      s.readBlock U.1 U.2 (N * N) = some us ∧
      decodeMatrix dec N N ls = luLower A ∧ decodeMatrix dec N N us = luUpper A := by
  obtain ⟨rs, ls, us, hR, hL, hU, hres, hlo, hup⟩ := h.read_blocks
  refine ⟨ls, us, hL, hU, ?_, ?_⟩
  · ext i j
    simpa only [if_pos j.isLt] using hlo i j
  · ext i j
    simpa only [if_pos i.isLt] using hup i j

end NLAlib.LU
