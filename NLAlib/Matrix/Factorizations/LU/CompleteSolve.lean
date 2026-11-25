/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.PivotedSolve
public import NLAlib.Matrix.Factorizations.TriangularSolve.Complete

/-!
# Complete-pivot factorization and solve

The actual full factorization supplies independent row and column logs. The row log
permutes the original RHS, scalar substitutions solve the stored factors, and reverse
column-log replay restores the original coordinates. Input nonsingularity alone justifies
all divisors. All factor/history storage is scoped, and the RHS may be overwritten in place.

## Main results

* `NLAlib.LU.solveCompleteWithScratch_writes`: actual factorization and two-log solve.
-/

@[expose] public section

namespace NLAlib.LU

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Compute both actual pivot logs and solve their factor system on declared caller scratch. -/
def solveCompleteWithScratch : Stmt Op Tst := ops% [n] (A, b, x, L, U, H, C) → () {
  run factorComplete [n] (A, L, U, H, C);
  run TriangularSolve.completePivoted [n] (L, U, H, C, b, x)
}

/-- Complete-pivot factor-then-solve with scoped factors and actual histories. Order zero
skips every operand frame, allocation and scalar or index operation. -/
def solveComplete : Routine Op Tst := routine% [n] (A : n * n, b : n) → (x : n) {
  ifPos n {
    let L ← alloc (n * n);
    let U ← alloc (n * n);
    let H ← alloc n;
    let C ← alloc n;
    run solveCompleteWithScratch [n] (A, b, x, L, U, H, C)
  }
}

variable [Inhabited K]

/-- The original nonsingular matrix and actual reported factor/log words justify the
complete-pivot solve. Only scratch is apart; original matrix and in-place RHS may overlap. -/
theorem solveCompleteWithScratch_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M)
    {n : ℕ} {τ : Tape K} {m : Mem K} {A b x L U H C : ℕ × ℕ} {as bs : List K}
    (hlive : m.Live [A, b, x, L, U, H, C])
    (hApart : ∀ T ∈ [L, U, H, C], T.1 ≠ A.1 ∧ T.1 ≠ b.1 ∧ T.1 ≠ x.1)
    (hOut : L.1 ≠ U.1 ∧ L.1 ≠ H.1 ∧ L.1 ≠ C.1 ∧ U.1 ≠ H.1 ∧ U.1 ≠ C.1 ∧ H.1 ≠ C.1)
    (hbx : Fp.Disj (Store.inBlock b.1 b.2 n) (Store.inBlock x.1 x.2 n) ∨ b = x)
    (has : m.store.readBlock A.1 A.2 (n * n) = some as)
    (hbs : m.store.readBlock b.1 b.2 n = some bs) (hA : IsUnit (decodeMatrix dec n n as))
    (hroom : m.Room [L, U, H, C, x] [n * n, n * n, n, n, n]) :
    Writes .total I τ (solveCompleteWithScratch (Op := Op) (Tst := Tst))
      (Env.frame [n] [A, b, x, L, U, H, C])
      (Fp.blocks [L, U, H, C, x] [n * n, n * n, n, n, n])
      (fun m' => m'.pos = m.pos ∧ ∃ zs : List K,
        m'.store.readBlock x.1 x.2 n = some zs ∧
        decodeMatrix dec n n as *ᵥ decv dec n zs = decv dec n bs) m := by
  obtain ⟨hLA, hLb, hLx⟩ := hApart L (by simp)
  obtain ⟨hUA, hUb, hUx⟩ := hApart U (by simp)
  obtain ⟨hHA, hHb, hHx⟩ := hApart H (by simp)
  obtain ⟨hCA, hCb, hCx⟩ := hApart C (by simp)
  obtain ⟨hLU, hLH, hLC, hUH, hUC, hHC⟩ := hOut
  have hlA : A.1 < m.store.length := hlive A (by simp)
  have hlb : b.1 < m.store.length := hlive b (by simp)
  have hlx : x.1 < m.store.length := hlive x (by simp)
  have hlL : L.1 < m.store.length := hlive L (by simp)
  have hlU : U.1 < m.store.length := hlive U (by simp)
  have hlH : H.1 < m.store.length := hlive H (by simp)
  have hlC : C.1 < m.store.length := hlive C (by simp)
  simp only [Mem.room_cons, Mem.room_nil, and_true] at hroom
  unfold solveCompleteWithScratch
  call (factorComplete_meets hI hcmp hlit hQ hM) [n] (A, L, U, H, C)
    as m₁ hfr₁ hpos₁ (ls, us, hs, qs) hfactor
  obtain ⟨p, q, hrows, hcols, hp, hq, _, _, hf, _⟩ := hfactor
  let P := luPivotPermutation p n
  let Q := luPivotPermutation q n
  let B := (decodeMatrix dec n n as).submatrix P Q
  have hB : IsUnit B := (Matrix.isUnit_submatrix_equiv P Q).mpr hA
  have hbs₁ : m₁.store.readBlock b.1 b.2 n = some bs := by keep
  have hlive₁ : m₁.Live [L, U, H, C, b, x] := by
    simp only [Mem.live_cons, Mem.live_nil]
    have he := hfr₁.length_eq
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, trivial⟩
  have hpre : (TriangularSolve.completePivotedSpec dec).pre [n] (τ.shift m₁.pos)
      [ls, us, hs, qs, bs] :=
    ⟨TriangularSolve.pivotedSpec_pre_of_isLU (τ := τ.shift m₁.pos) (bs := bs)
      hf hB p hp hrows, q, hq, hcols⟩
  refine ((TriangularSolve.completePivoted_writes hI hQ hM hlive₁ hLx hUx hHx hCx hbx
    hls hus hhs hqs hbs₁ (by simpa only [hfr₁.len_eq] using hroom.2.2.2.2) hpre).in_frame
      rfl rfl hlive₁).mono (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨hpos₂, zs, hzs, hsolve⟩
  have heq := hsolve p q hrows hcols
  rw [← hf.eq_mul] at heq
  have hback : ((decodeMatrix dec n n as).submatrix P Q).submatrix P.symm Q.symm =
      decodeMatrix dec n n as := by
    ext i j
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
  dsimp only [P, Q] at hback
  rw [hback] at heq
  exact ⟨hpos₂.trans hpos₁, zs, hzs, heq⟩

omit [Inhabited K] in
/-- The guarded complete-pivot solve leaves arbitrary empty-order operands untouched,
including invalid handles, arbitrary offsets and aliases, under every interpretation. -/
theorem eval_solveComplete_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (solveComplete (Op := Op) (Tst := Tst)).body (Env.frame [0] args) m = some m := by
  rfl

/-- Full complete-pivot solve from original nonsingularity, permitting exact in-place RHS
and source/RHS overlap. All original cells outside the output and every original buffer
extent are retained. Empty order requires neither valid handles nor output capacity. -/
theorem solveComplete_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M)
    {n : ℕ} {τ : Tape K} {m : Mem K} {A b x : ℕ × ℕ} {as bs : List K}
    (hlive : 0 < n → m.Live [A, b, x])
    (hbx : Fp.Disj (Store.inBlock b.1 b.2 n) (Store.inBlock x.1 x.2 n) ∨ b = x)
    (has : m.store.readBlock A.1 A.2 (n * n) = some as)
    (hbs : m.store.readBlock b.1 b.2 n = some bs) (hA : IsUnit (decodeMatrix dec n n as))
    (hroom : 0 < n → x.2 + n ≤ m.store.len x.1) :
    Writes .total I τ (solveComplete (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [A, b, x]) (Store.inBlock x.1 x.2 n)
      (fun m' => m'.pos = m.pos ∧ ∃ zs : List K,
        m'.store.readBlock x.1 x.2 n = some zs ∧
        decodeMatrix dec n n as *ᵥ decv dec n zs = decv dec n bs) m := by
  refine writes_ifPos (n := n) rfl ?_
  by_cases hn : 0 < n
  · rw [if_pos hn]
    have hlA : A.1 < m.store.length := hlive hn A (by simp)
    have hlb : b.1 < m.store.length := hlive hn b (by simp)
    have hlx : x.1 < m.store.length := hlive hn x (by simp)
    apply writes_allocs_preserving_post
      (lens := [.var 0 * .var 0, .var 0 * .var 0, .var 0, .var 0])
      (ns := [n * n, n * n, n, n]) rfl
    · intro s s' p hBelow hp
      obtain ⟨hpos, zs, hzs, hsolve⟩ := hp
      exact ⟨hpos, zs, (hBelow.readBlock hlx x.2 n).trans hzs, hsolve⟩
    · intro store hlength hlens hBelow
      have hlen : store.length = m.store.length + 4 := by simpa using hlength
      have hLlen : store.len m.store.length = n * n := by simpa using hlens 0 (by simp)
      have hUlen : store.len (m.store.length + 1) = n * n := by simpa using hlens 1 (by simp)
      have hHlen : store.len (m.store.length + 2) = n := by simpa using hlens 2 (by simp)
      have hClen : store.len (m.store.length + 3) = n :=
        by simpa using hlens 3 (by simp)
      have hLive : (Mem.mk store m.pos).Live
          [A, b, x, (m.store.length, 0), (m.store.length + 1, 0),
            (m.store.length + 2, 0),
            (m.store.length + 3, 0)] := by
        simp only [Mem.live_cons, Mem.live_nil]
        exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, trivial⟩
      refine ((solveCompleteWithScratch_writes hI hcmp hlit hQ hM hLive ?_
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
        hbx (by kept) (by kept) hA ?_).in_frame
          rfl rfl hLive).mono (by fp_sub) (fun _ _ h => h)
      · intro T hT
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
        rcases hT with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega, by omega⟩
      · simp only [Mem.room_cons, Mem.room_nil]
        exact ⟨by simpa using hLlen.ge, by simpa using hUlen.ge, by simpa using hHlen.ge,
          by simpa using hClen.ge, by simpa only [(hBelow x.1 hlx).1] using hroom hn, trivial⟩
  · rw [if_neg hn]
    have he : n = 0 := by omega
    subst n
    exact ⟨rfl, [], rfl, by ext i; exact Fin.elim0 i⟩

/-- The ordinary separate-output interface of the same full complete-pivot solve. -/
theorem solveComplete_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (solveComplete (Op := Op) (Tst := Tst)).Meets I (solvePivotedSpec dec) := by
  routine_intro [n] (A, b, x) reads (as, bs)
  refine (solveComplete_writes hI hcmp hlit hQ hM (fun _ => hlive)
    (.inl (Fp.disj_inBlock_of_ne hbx)) has hbs hpre (fun _ => hroom)).mono (by fp_sub) ?_
  rintro m' hfr ⟨hpos, zs, hzs, hsolve⟩
  exact ⟨hpos, [zs], Mem.readBlocks_of_cons hzs rfl, hsolve⟩

/-- A genuine in-place RHS interface of the same actual guarded scalar solve body. -/
def solveCompleteInPlace : Routine Op Tst :=
  routine% [n] (A : n * n, x : n) → (x) := (solveComplete (Op := Op) (Tst := Tst)).body

/-- The in-place RHS header uses the common raw alias proof, retaining the original matrix
and RHS values in the solve specification. Raw source/RHS overlap is admitted by that proof. -/
theorem solveCompleteInPlace_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (solveCompleteInPlace (Op := Op) (Tst := Tst)).Meets I (solvePivotedSpec dec) := by
  routine_intro [n] (A, x) reads (as, bs)
  have hlive' : m.Live [A, x, x] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl.1, hl.2, hl.2, trivial⟩
  refine (solveComplete_writes hI hcmp hlit hQ hM (fun _ => hlive')
    (.inr rfl) has hbs hpre (fun _ => hroom)).mono (by fp_sub) ?_
  rintro m' hfr ⟨hpos, zs, hzs, hsolve⟩
  exact ⟨hpos, [zs], Mem.readBlocks_of_cons hzs rfl, hsolve⟩

end NLAlib.LU
