/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Partial
public import NLAlib.Matrix.Factorizations.LU.Complete
public import NLAlib.Matrix.Factorizations.LU.UnapplyLog
public import NLAlib.Matrix.Factorizations.TriangularSolve.PivotedValues
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Matrix.Perturbation.ComponentwiseBackward

/-!
# Factor-then-solve with actual pivot histories

The original matrix is factored, its actual row log permutes the original right-hand side,
and scalar substitutions solve through the stored factors. Nonsingularity of the original
matrix supplies all triangular divisors. Source/RHS overlap and an in-place RHS are admitted
by raw operand rules; only the output vector remains written after scratch is released.

## Main results

* `NLAlib.LU.solvePartialWithScratch_writes`: actual partial-pivot factorization and solve.
-/

@[expose] public section

namespace NLAlib.LU

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Factor the original matrix, then copy, permute and solve its RHS on caller-owned factor
and history scratch. The RHS and output may be the same operand in this unchanged tree. -/
def solvePartialWithScratch : Stmt Op Tst := ops% [n] (A, b, x, L, U, H) → () {
  run factorPartial [n] (A, L, U, H);
  run TriangularSolve.pivoted [n] (L, U, H, b, x)
}

/-- Partial-pivot factorization and solve with scoped factors and actual history. The outer
dimension guard skips every operand frame and allocation at order zero. -/
def solvePartial : Routine Op Tst := routine% [n] (A : n * n, b : n) → (x : n) {
  ifPos n {
    let L ← alloc (n * n);
    let U ← alloc (n * n);
    let H ← alloc n;
    run solvePartialWithScratch [n] (A, b, x, L, U, H)
  }
}

variable [Inhabited K]

/-- Every nonsingular original input is admitted. The actual output solves its original
right-hand side, with no successful-factorization or computed-pivot restriction. -/
def solvePivotedSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [n] (as, bs) → (xs) requires IsUnit (decodeMatrix dec n n as) ensures
    decodeMatrix dec n n as *ᵥ decv dec n xs = decv dec n bs

/-- The actual stored factor and log words justify the solve on an original nonsingular
matrix. The source may overlap the RHS/output; scratch is explicitly apart from them. -/
theorem solvePartialWithScratch_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M)
    {n : ℕ} {τ : Tape K} {m : Mem K} {A b x L U H : ℕ × ℕ} {as bs : List K}
    (hlive : m.Live [A, b, x, L, U, H])
    (hApart : ∀ T ∈ [L, U, H], T.1 ≠ A.1 ∧ T.1 ≠ b.1 ∧ T.1 ≠ x.1)
    (hLU : L.1 ≠ U.1) (hLH : L.1 ≠ H.1) (hUH : U.1 ≠ H.1)
    (hbx : Fp.Disj (Store.inBlock b.1 b.2 n) (Store.inBlock x.1 x.2 n) ∨ b = x)
    (has : m.store.readBlock A.1 A.2 (n * n) = some as)
    (hbs : m.store.readBlock b.1 b.2 n = some bs) (hA : IsUnit (decodeMatrix dec n n as))
    (hroom : m.Room [L, U, H, x] [n * n, n * n, n, n]) :
    Writes .total I τ (solvePartialWithScratch (Op := Op) (Tst := Tst))
      (Env.frame [n] [A, b, x, L, U, H])
      (Store.inBlock L.1 L.2 (n * n) ⊔ Store.inBlock U.1 U.2 (n * n) ⊔
        Store.inBlock H.1 H.2 n ⊔ Store.inBlock x.1 x.2 n)
      (fun m' => m'.pos = m.pos ∧ ∃ zs : List K,
        m'.store.readBlock x.1 x.2 n = some zs ∧
        decodeMatrix dec n n as *ᵥ decv dec n zs = decv dec n bs) m := by
  obtain ⟨hLA, hLb, hLx⟩ := hApart L (by simp)
  obtain ⟨hUA, hUb, hUx⟩ := hApart U (by simp)
  obtain ⟨hHA, hHb, hHx⟩ := hApart H (by simp)
  have hlA : A.1 < m.store.length := hlive A (by simp)
  have hlb : b.1 < m.store.length := hlive b (by simp)
  have hlx : x.1 < m.store.length := hlive x (by simp)
  have hlL : L.1 < m.store.length := hlive L (by simp)
  have hlU : U.1 < m.store.length := hlive U (by simp)
  have hlH : H.1 < m.store.length := hlive H (by simp)
  simp only [Mem.room_cons, Mem.room_nil, and_true] at hroom
  unfold solvePartialWithScratch
  call (factorPartial_meets hI hcmp hlit hQ hM) [n] (A, L, U, H)
    as m₁ hfr₁ hpos₁ (ls, us, hs) hfactor
  obtain ⟨p, hlog, hp, _, _, hf, _⟩ := hfactor
  let B := (decodeMatrix dec n n as).submatrix (luPivotPermutation p n) id
  have hB : IsUnit B := (Matrix.isUnit_submatrix_equiv (luPivotPermutation p n)
    (Equiv.refl _)).mpr hA
  have hbs₁ : m₁.store.readBlock b.1 b.2 n = some bs := by keep
  have hlive₁ : m₁.Live [L, U, H, b, x] := by
    simp only [Mem.live_cons, Mem.live_nil]
    have he := hfr₁.length_eq
    exact ⟨by omega, by omega, by omega, by omega, by omega, trivial⟩
  have hpre := TriangularSolve.pivotedSpec_pre_of_isLU (τ := τ.shift m₁.pos)
    (bs := bs) hf hB p hp hlog
  refine ((TriangularSolve.pivoted_writes hI hQ hM hlive₁ hLx hUx hHx hbx hls hus hhs
    hbs₁ (by simpa only [hfr₁.len_eq] using hroom.2.2.2) hpre).in_frame
      rfl rfl hlive₁).mono (by fp_sub) ?_
  rintro m₂ hfr₂ ⟨hpos₂, zs, hzs, hsolve⟩
  have heq := hsolve p hlog
  rw [← hf.eq_mul] at heq
  have hout := TriangularSolve.mulVec_eq_of_submatrix_solve
    (luPivotPermutation p n) (Equiv.refl _) heq
  refine ⟨hpos₂.trans hpos₁, zs, hzs, ?_⟩
  simpa only [Equiv.refl_symm, Equiv.refl_apply, Function.comp_def] using hout

omit [Inhabited K] in
/-- The guarded partial-pivot solve leaves arbitrary empty-order operands untouched,
including invalid handles, arbitrary offsets and aliases, under every interpretation. -/
theorem eval_solvePartial_zero (I : Interp Op Tst K) (τ : Tape K)
    (args : List (ℕ × ℕ)) (m : Mem K) :
    Ops.eval I τ (solvePartial (Op := Op) (Tst := Tst)).body (Env.frame [0] args) m = some m := by
  rfl

/-- Full partial-pivot solve from original nonsingularity, permitting exact in-place RHS
and source/RHS overlap. All original cells outside the output and every original buffer
extent are retained. Empty order requires neither valid handles nor output capacity. -/
theorem solvePartial_writes {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M)
    {n : ℕ} {τ : Tape K} {m : Mem K} {A b x : ℕ × ℕ} {as bs : List K}
    (hlive : 0 < n → m.Live [A, b, x])
    (hbx : Fp.Disj (Store.inBlock b.1 b.2 n) (Store.inBlock x.1 x.2 n) ∨ b = x)
    (has : m.store.readBlock A.1 A.2 (n * n) = some as)
    (hbs : m.store.readBlock b.1 b.2 n = some bs) (hA : IsUnit (decodeMatrix dec n n as))
    (hroom : 0 < n → x.2 + n ≤ m.store.len x.1) :
    Writes .total I τ (solvePartial (Op := Op) (Tst := Tst)).body
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
      (lens := [.var 0 * .var 0, .var 0 * .var 0, .var 0]) (ns := [n * n, n * n, n]) rfl
    · intro s s' p hBelow hp
      obtain ⟨hpos, zs, hzs, hsolve⟩ := hp
      exact ⟨hpos, zs, (hBelow.readBlock hlx x.2 n).trans hzs, hsolve⟩
    · intro store hlength hlens hBelow
      have hlen : store.length = m.store.length + 3 := by simpa using hlength
      have hLlen : store.len m.store.length = n * n := by simpa using hlens 0 (by simp)
      have hUlen : store.len (m.store.length + 1) = n * n := by simpa using hlens 1 (by simp)
      have hHlen : store.len (m.store.length + 2) = n := by simpa using hlens 2 (by simp)
      have hLive : (Mem.mk store m.pos).Live
          [A, b, x, (m.store.length, 0), (m.store.length + 1, 0), (m.store.length + 2, 0)] := by
        simp only [Mem.live_cons, Mem.live_nil]
        exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, trivial⟩
      refine ((solvePartialWithScratch_writes hI hcmp hlit hQ hM hLive ?_
        (by omega) (by omega) (by omega) hbx (by kept) (by kept) hA ?_).in_frame
          rfl rfl hLive).mono (by fp_sub) (fun _ _ h => h)
      · intro T hT
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
        rcases hT with rfl | rfl | rfl <;> exact ⟨by omega, by omega, by omega⟩
      · simp only [Mem.room_cons, Mem.room_nil]
        exact ⟨by simpa using hLlen.ge, by simpa using hUlen.ge, by simpa using hHlen.ge,
          by simpa only [(hBelow x.1 hlx).1] using hroom hn, trivial⟩
  · rw [if_neg hn]
    have he : n = 0 := by omega
    subst n
    exact ⟨rfl, [], rfl, by ext i; exact Fin.elim0 i⟩

/-- The ordinary separate-output interface of the same full partial-pivot solve. -/
theorem solvePartial_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (solvePartial (Op := Op) (Tst := Tst)).Meets I (solvePivotedSpec dec) := by
  routine_intro [n] (A, b, x) reads (as, bs)
  refine (solvePartial_writes hI hcmp hlit hQ hM (fun _ => hlive)
    (.inl (Fp.disj_inBlock_of_ne hbx)) has hbs hpre (fun _ => hroom)).mono (by fp_sub) ?_
  rintro m' hfr ⟨hpos, zs, hzs, hsolve⟩
  exact ⟨hpos, [zs], Mem.readBlocks_of_cons hzs rfl, hsolve⟩

/-- A genuine in-place RHS interface of the same actual guarded scalar solve body. -/
def solvePartialInPlace : Routine Op Tst :=
  routine% [n] (A : n * n, x : n) → (x) := (solvePartial (Op := Op) (Tst := Tst)).body

/-- The in-place RHS header uses the common raw alias proof, retaining the original matrix
and RHS values in the solve specification. Raw source/RHS overlap is admitted by that proof. -/
theorem solvePartialInPlace_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I) (hlit : IsIndexLit M I)
    (hQ : IsToNat dec I) (hM : ExactModel dec M) :
    (solvePartialInPlace (Op := Op) (Tst := Tst)).Meets I (solvePivotedSpec dec) := by
  routine_intro [n] (A, x) reads (as, bs)
  have hlive' : m.Live [A, x, x] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl.1, hl.2, hl.2, trivial⟩
  refine (solvePartial_writes hI hcmp hlit hQ hM (fun _ => hlive')
    (.inr rfl) has hbs hpre (fun _ => hroom)).mono (by fp_sub) ?_
  rintro m' hfr ⟨hpos, zs, hzs, hsolve⟩
  exact ⟨hpos, [zs], Mem.readBlocks_of_cons hzs rfl, hsolve⟩

omit [Has ScalarOp Op] [Has IndexOp Op] [Has CmpTst Tst] [Has IdxTst Tst] in
/-- The original-system equation of either pivoted solve is the existing componentwise
backward-solution predicate at zero relative allowance and zero diagonal floor. -/
theorem isComponentwiseBackwardSolution_of_solvePivotedSpec {dec : K → ℝ} {n : ℕ}
    {as bs xs : List K} {τ : Tape K}
    (hpost : (solvePivotedSpec dec).post [n] τ [as, bs] [xs]) :
    IsComponentwiseBackwardSolution 0 0 (decodeMatrix dec n n as) (decv dec n bs) (decv dec n xs) :=
  IsComponentwiseBackwardSolution.of_mulVec_eq (le_refl 0) (le_refl 0) hpost

end NLAlib.LU
