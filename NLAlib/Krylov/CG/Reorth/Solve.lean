/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Reorth.Rounds
public import NLAlib.Krylov.CG.HSCG.Initialization

/-!
# Total exact full-reorthogonalized CG from stored inputs

Initialization and the residual guard are part of the program. Every cap succeeds for a
positive-definite system: convergence before the cap is a successful exit, and no later
division is attempted. The basis is scoped storage and only its initialized prefix is read.

## Main results

* `NLAlib.Krylov.CG.Reorth.solve_writes`: total execution from a stored right-hand side and guess.
* `NLAlib.Krylov.CG.Reorth.runs_solve`: exact CG output with closed counts and workspace.
* `NLAlib.Krylov.CG.Reorth.runs_solve_of_grade_le`: a sufficiently large cap returns a solution.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- Every cap succeeds from stored inputs; zero residuals stop before any further division. -/
theorem solve_writes {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec (fun _ => True) I)
    (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hPos : A.PosDef)
    {τ : Tape K} {μ : Mem K} {b x r p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hl : μ.Live [b, x, r, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs) (hz : μ.Room [x, r, p] [n, n, n]) :
    Writes .total I τ solve (Env.frame [n, cap] [b, x, x, r, p])
      (Fp.blocks [x, r, p] [n, n, n])
      (fun μ' => μ'.pos = μ.pos ∧ HSCG.StoresState dec n x r p
        (cgState A (decv dec n bs) (decv dec n xs)
          (min cap (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs)))) μ') μ := by
  have hbL := hl b (by simp)
  have hxL := hl x (by simp)
  have hrL := hl r (by simp)
  have hpL := hl p (by simp)
  refine writes_allocs (lens := [.var 1 * .var 0, .const 1]) (ns := [cap * n, 1]) rfl
    fun s₁ hs₁ hlen hBelow => ?_
  have hQ : s₁.len μ.store.length = cap * n := by simpa using hlen 0 (by simp)
  have hv : s₁.len (μ.store.length + 1) = 1 := by simpa using hlen 1 (by simp)
  have hs : s₁.length = μ.store.length + 2 := by simpa using hs₁
  dsimp only [Env.frame, List.append, List.range_succ, List.range_zero, List.map,
    List.length_cons, List.length_nil, Nat.add_zero] at *
  refine Writes.seq_le (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true]; omega)
    (HSCG.initialize_writes (bs := bs) (xs := xs) hS hM hB hA hbx hbr hbp hxr hxp hrp
      (by simp only [Mem.live_cons, Mem.live_nil, and_true]; omega)
      (by kept) (by kept) (by
        simpa only [Mem.room_cons, Mem.room_nil, and_true, (hBelow x.1 hxL).1,
          (hBelow r.1 hrL).1, (hBelow p.1 hpL).1] using hz))) (by fp_sub)
    fun μ₁ hfr₁ ⟨hpos₁, hstate₁⟩ => ?_
  obtain ⟨xs₁, rs₁, ps₁, hx₁, hr₁, hp₁, hdecoded₁⟩ := state_reads hstate₁
  step hB.dot as μ₂ hfr₂ ⟨hpos₂, rr, hrr, herr⟩
  have hstate₂ : HSCG.StoresState dec n x r p
      (cgState A (decv dec n bs) (decv dec n xs) 0) μ₂ :=
    ⟨xs₁, rs₁, ps₁, Mem.readBlocks_of_cons (by kept)
      (Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl)), hdecoded₁⟩
  have hrvec : decv dec n rs₁ = (cgState A (decv dec n bs) (decv dec n xs) 0).r :=
    congrArg CGState.r hdecoded₁
  refine (rounds_writes hS hM hB hA hCmp hPos hxr hxp hrp hxL hrL hpL
    (by rw [hfr₂.length_eq, hfr₁.length_eq]; exact hs)
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hQ)
    (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hv)
    (by simpa only [Mem.room_cons, Mem.room_nil, and_true, hfr₂.len_eq, hfr₁.len_eq,
      (hBelow x.1 hxL).1, (hBelow r.1 hrL).1, (hBelow p.1 hpL).1] using hz)
    hstate₂ ⟨rr, hrr, by simpa only [hrvec] using (dotExactRel_decoded (dec := dec) herr)⟩).mono
      le_rfl ?_
  rintro μ₃ hfr₃ ⟨hpos₃, hstate₃⟩ s₂ hs₂ hBelow₂
  obtain ⟨xs₃, rs₃, ps₃, hx₃, hr₃, hp₃, hdecoded₃⟩ := state_reads hstate₃
  exact ⟨by simp [hpos₃, hpos₂, hpos₁], xs₃, rs₃, ps₃, Mem.readBlocks_of_cons (by kept)
    (Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl)), hdecoded₃⟩

/-- The output is the exact CG iterate at the cap or its earlier grade, with all guards,
history projections and scratch accounted for. No execution-success premise is required. -/
theorem runs_solve {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec (fun _ => True) I)
    (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hPos : A.PosDef)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {b x r p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hl : μ.Live [b, x, r, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs) (hz : μ.Room [x, r, p] [n, n, n]) :
    ConditionalRuns I W τ solve (Env.frame [n, cap] [b, x, x, r, p]) μ
      (solveCount n cap) (solvePeak W n cap)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        decv dec n ys = cgIterate A (decv dec n bs) (decv dec n xs)
          (min cap (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs)))) := by
  have hw := solve_writes hS hM hB hA hCmp hPos (cap := cap) (τ := τ)
    hbx hbr hbp hxr hxp hrp hl hbs hxs hz
  obtain ⟨μ', hrun, hpos, hstate⟩ := hw.wp fun _ _ h => h
  refine (ConditionalRuns.of_run (Q := fun μ' => μ'.pos = μ.pos ∧ HSCG.StoresState dec n x r p
    (cgState A (decv dec n bs) (decv dec n xs)
      (min cap (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs)))) μ')
    hrun ⟨hpos, hstate⟩ W).mono
    (le_of_eq (staticCost_solve ..)) (staticPeak_solve_le ..) ?_
  rintro μ'' ⟨hpos', hstate'⟩
  obtain ⟨ys, rs, ps, hy, _, _, hdecoded⟩ := state_reads hstate'
  exact ⟨hpos', ys, hy, (congrArg CGState.x hdecoded).trans (hPos.cgState_x_eq _ _ _)⟩

/-- Once the cap covers the initial residual's grade, the computed output solves the system.
Earlier convergence is successful, and no scalar division is attempted afterward. -/
theorem runs_solve_of_grade_le {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec (fun _ => True) I)
    (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hPos : A.PosDef)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {b x r p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hl : μ.Live [b, x, r, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs) (hz : μ.Room [x, r, p] [n, n, n])
    (hcap : krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs) ≤ cap) :
    ConditionalRuns I W τ solve (Env.frame [n, cap] [b, x, x, r, p]) μ
      (solveCount n cap) (solvePeak W n cap)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        A *ᵥ decv dec n ys = decv dec n bs) := by
  refine (runs_solve hS hM hB hA hCmp hPos W hbx hbr hbp hxr hxp hrp hl hbs hxs hz).mono
    le_rfl le_rfl ?_
  rintro μ' ⟨hpos, ys, hy, heq⟩
  have hzero := (hPos.cgState_r_eq_zero_iff (decv dec n bs) (decv dec n xs)
    (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs))).mpr le_rfl
  rw [cgState_r_eq, hPos.cgState_x_eq, sub_eq_zero] at hzero
  exact ⟨hpos, ys, hy, by rw [heq, Nat.min_eq_right hcap]; exact hzero.symm⟩

end NLAlib.Krylov.CG.Reorth
