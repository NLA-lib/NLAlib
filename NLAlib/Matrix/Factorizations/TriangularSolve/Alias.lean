/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.TriangularSolve.Factors
public import NLAlib.Matrix.Factorizations.TriangularSolve.Cholesky
public import NLAlib.Ops.Blas.CopyAlias

/-!
# Raw and in-place triangular product solves

The guarded actual product-solve trees permit an exact right-hand-side/output alias or
spatially disjoint vector blocks. Their factors remain apart from the output. The empty
case needs no live handles, separation, capacities or scalar calls.

## Main results

* `NLAlib.TriangularSolve.factors_writes`: actual lower/upper solve with RHS aliases.
-/

@[expose] public section

namespace NLAlib.TriangularSolve

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op] [Inhabited K]

/-- The actual guarded lower/upper tree solves the original RHS with one net vector write.
The RHS and output are identical or block-disjoint, and source factors remain unchanged.
All live-handle, matrix/output separation and capacity requirements are conditional on a
positive dimension, so the empty case admits arbitrary invalid and coincident handles. -/
theorem factors_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) {n : ℕ} {τ : Tape K} {m : Mem K}
    {L U b x : ℕ × ℕ} {ls us bs : List K}
    (hlive : 0 < n → m.Live [L, U, b, x])
    (hLx : 0 < n → L.1 ≠ x.1) (hUx : 0 < n → U.1 ≠ x.1)
    (hbx : Fp.Disj (Store.inBlock b.1 b.2 n) (Store.inBlock x.1 x.2 n) ∨ b = x)
    (hls : m.store.readBlock L.1 L.2 (n * n) = some ls)
    (hus : m.store.readBlock U.1 U.2 (n * n) = some us)
    (hbs : m.store.readBlock b.1 b.2 n = some bs)
    (hroom : 0 < n → x.2 + n ≤ m.store.len x.1)
    (htri : (factorsSpec dec).pre [n] (τ.shift m.pos) [ls, us, bs]) :
    Writes .total I τ (factors (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [L, U, b, x]) (Store.inBlock x.1 x.2 n)
      (fun μ => μ.pos = m.pos ∧ ∃ xs, μ.store.readBlock x.1 x.2 n = some xs ∧
        (factorsSpec dec).post [n] (τ.shift m.pos) [ls, us, bs] [xs]) m := by
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    have hLive := hlive hn
    obtain ⟨hlL, hlU, hlb, hlx⟩ : L.1 < m.store.length ∧ U.1 < m.store.length ∧
        b.1 < m.store.length ∧ x.1 < m.store.length := by
      simpa only [Mem.live_cons, Mem.live_nil, and_true] using hLive
    have hLx' := hLx hn
    have hUx' := hUx hn
    obtain ⟨hL, hU, hdL, hdU⟩ := htri
    have hLiveCopy : m.Live [b, x] := by
      simpa only [Mem.live_cons, Mem.live_nil, and_true] using
        And.intro (hLive b (by simp)) (hLive x (by simp))
    refine ((copyLoopRoutine_writes_of_disj_or_eq hI hbx hbs (hroom hn)).in_frame
      rfl rfl hLiveCopy).seq_le le_rfl ?_
    intro μ hfr ⟨hpos, hcopy⟩
    have hls' : μ.store.readBlock L.1 L.2 (n * n) = some ls := by keep
    have hus' : μ.store.readBlock U.1 U.2 (n * n) = some us := by keep
    call (forward_meets hI hM.toStdModel_zero) [n] (L, x) (pre := hdL)
      as ν hfr' hpos' (ys) hforward
    have hLy := forwardSpec_mulVec_eq (τ := τ.shift μ.pos) hforward hL hdL
    call (upper_meets hI hM.toStdModel_zero) [n] (U, x) (pre := hdU)
      as ξ hfr'' hpos'' (zs) hupper
    have hUz := upperSpec_mulVec_eq (τ := τ.shift ν.pos) hupper hU hdU
    refine ⟨hpos''.trans (hpos'.trans hpos), zs, hzs, ?_⟩
    change (decodeMatrix dec n n ls * decodeMatrix dec n n us) *ᵥ decv dec n zs = _
    rw [← Matrix.mulVec_mulVec, hUz, hLy]
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    refine ⟨rfl, [], rfl, ?_⟩
    ext i
    exact i.elim0

/-- The actual guarded Cholesky Gram tree solves the original RHS with one net vector write.
The RHS and output are identical or block-disjoint, and source factors remain unchanged.
All live-handle, matrix/output separation and capacity requirements are conditional on a
positive dimension, so the empty case admits arbitrary invalid and coincident handles. -/
theorem cholesky_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) {n : ℕ} {τ : Tape K} {m : Mem K}
    {L b x : ℕ × ℕ} {ls bs : List K}
    (hlive : 0 < n → m.Live [L, b, x])
    (hLx : 0 < n → L.1 ≠ x.1)
    (hbx : Fp.Disj (Store.inBlock b.1 b.2 n) (Store.inBlock x.1 x.2 n) ∨ b = x)
    (hls : m.store.readBlock L.1 L.2 (n * n) = some ls)
    (hbs : m.store.readBlock b.1 b.2 n = some bs)
    (hroom : 0 < n → x.2 + n ≤ m.store.len x.1)
    (htri : (choleskySpec dec).pre [n] (τ.shift m.pos) [ls, bs]) :
    Writes .total I τ (cholesky (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [L, b, x]) (Store.inBlock x.1 x.2 n)
      (fun μ => μ.pos = m.pos ∧ ∃ xs, μ.store.readBlock x.1 x.2 n = some xs ∧
        (choleskySpec dec).post [n] (τ.shift m.pos) [ls, bs] [xs]) m := by
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    have hLive := hlive hn
    obtain ⟨hlL, hlb, hlx⟩ : L.1 < m.store.length ∧
        b.1 < m.store.length ∧ x.1 < m.store.length := by
      simpa only [Mem.live_cons, Mem.live_nil, and_true] using hLive
    have hLx' := hLx hn
    obtain ⟨hL, hdL⟩ := htri
    have hLiveCopy : m.Live [b, x] := by
      simpa only [Mem.live_cons, Mem.live_nil, and_true] using
        And.intro (hLive b (by simp)) (hLive x (by simp))
    refine ((copyLoopRoutine_writes_of_disj_or_eq hI hbx hbs (hroom hn)).in_frame
      rfl rfl hLiveCopy).seq_le le_rfl ?_
    intro μ hfr ⟨hpos, hcopy⟩
    have hls' : μ.store.readBlock L.1 L.2 (n * n) = some ls := by keep
    call (forward_meets hI hM.toStdModel_zero) [n] (L, x) (pre := hdL)
      as ν hfr' hpos' (ys) hforward
    have hLy := forwardSpec_mulVec_eq (τ := τ.shift μ.pos) hforward hL hdL
    call (backward_meets hI hM.toStdModel_zero) [n] (L, x) (pre := hdL)
      as ξ hfr'' hpos'' (zs) hbackward
    have hLz := backwardSpec_mulVec_eq (τ := τ.shift ν.pos) hbackward hL hdL
    refine ⟨hpos''.trans (hpos'.trans hpos), zs, hzs, ?_⟩
    change (decodeMatrix dec n n ls * (decodeMatrix dec n n ls)ᴴ) *ᵥ decv dec n zs = _
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mulVec_mulVec, hLz, hLy]
  · rw [if_neg hn]
    have hn0 : n = 0 := by omega
    subst n
    refine ⟨rfl, [], rfl, ?_⟩
    ext i
    exact i.elim0

/-- In-place interface for the unchanged guarded lower/upper solve body. The original RHS
is the reported output; matrix factors remain read-only operands. -/
def solveFactorsInPlace : Routine Op Tst :=
  routine% [n] (L : n * n, U : n * n, b : n) → (b) :=
    (factors (Op := Op) (Tst := Tst)).body

/-- The in-place interface uses exactly the existing guarded scalar instruction tree. -/
theorem body_solveFactorsInPlace :
    (solveFactorsInPlace (Op := Op) (Tst := Tst)).body =
      (factors (Op := Op) (Tst := Tst)).body := rfl

/-- The actual lower/upper solve overwrites its own RHS with a solution of the original
product system, retaining both factors and restoring all scratch and the tape position. -/
theorem solveFactorsInPlace_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) :
    (solveFactorsInPlace (Op := Op) (Tst := Tst)).Meets I (factorsSpec dec) := by
  routine_intro [n] (L, U, b) reads (ls, us, bs)
  have hLive : m.Live [L, U, b, b] := by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using
      And.intro hl.1 ⟨hl.2.1, hl.2.2, hl.2.2⟩
  refine (factors_writes hI hM (fun _ => hLive) (fun _ => hLb) (fun _ => hUb)
    (Or.inr rfl) hls hus hbs (fun _ => hroom) hpre).mono (by fp_sub) ?_
  rintro μ hfr ⟨hpos, xs, hxs, hpost⟩
  exact ⟨hpos, [xs], Mem.readBlocks_of_cons hxs rfl, hpost⟩

/-- In-place interface for the unchanged guarded lower/conjugate-transpose solve body. -/
def solveCholeskyInPlace : Routine Op Tst :=
  routine% [n] (L : n * n, b : n) → (b) :=
    (cholesky (Op := Op) (Tst := Tst)).body

/-- The in-place interface uses exactly the existing guarded scalar instruction tree. -/
theorem body_solveCholeskyInPlace :
    (solveCholeskyInPlace (Op := Op) (Tst := Tst)).body =
      (cholesky (Op := Op) (Tst := Tst)).body := rfl

/-- The actual Gram-system solve overwrites its RHS, retaining the factor and restoring all
scratch and the tape position. Its domain is exactly the existing stored-factor domain. -/
theorem solveCholeskyInPlace_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hM : ExactModel dec M) :
    (solveCholeskyInPlace (Op := Op) (Tst := Tst)).Meets I (choleskySpec dec) := by
  routine_intro [n] (L, b) reads (ls, bs)
  have hLive : m.Live [L, b, b] := by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using And.intro hl.1 ⟨hl.2, hl.2⟩
  refine (cholesky_writes hI hM (fun _ => hLive) (fun _ => hLb) (Or.inr rfl)
    hls hbs (fun _ => hroom) hpre).mono (by fp_sub) ?_
  rintro μ hfr ⟨hpos, xs, hxs, hpost⟩
  exact ⟨hpos, [xs], Mem.readBlocks_of_cons hxs rfl, hpost⟩

end NLAlib.TriangularSolve
