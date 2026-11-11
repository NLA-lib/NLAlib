/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Initialization
public import NLAlib.Krylov.CG.HSCG.Carried.Rounds

/-!
# Total exact CG with early convergence before an arbitrary cap

The program initializes all state from the right-hand side and initial iterate. Positive
definiteness and the exact operation models imply successful execution for every cap. The
loop stops at a zero residual before evaluating another division, so the cap may exceed the
initial Krylov grade. [HestenesStiefel1952, (3:1)].

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.solve_spec` certifies total successful execution.
* `NLAlib.Krylov.CG.HSCG.Carried.runs_solve` gives the computed iterate and operation budget.
* `NLAlib.Krylov.CG.HSCG.Carried.runs_solve_dim` solves the SPD system with cap equal to dimension.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- The five external buffers are different; the initial iterate is updated in place. -/
@[admNF] def SolveOperands (n : ℕ) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => d.headD 0 = n ∧ ∃ b x r p v,
    ins = [b, x] ∧ outs = [x, r, p, v] ∧
      b.1 ≠ x.1 ∧ b.1 ≠ r.1 ∧ b.1 ≠ p.1 ∧ b.1 ≠ v.1 ∧
      x.1 ≠ r.1 ∧ x.1 ≠ p.1 ∧ x.1 ≠ v.1 ∧
      r.1 ≠ p.1 ∧ r.1 ≠ v.1 ∧ p.1 ≠ v.1

/-- The output state is the CG recurrence at the earlier of cap and exact convergence. -/
@[simps (attr := storeNF)]
noncomputable def solveRel (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    BlockRel K where
  nd := 2
  inLens d := [d.headD 0, d.headD 0]
  outLens d := [d.headD 0, d.headD 0, d.headD 0, 1]
  rel d X _ Y := match X, Y with
    | [bs, xs], [xs', rs, ps, [v]] =>
        decodedState dec n xs' rs ps = cgState A (decv dec n bs) (decv dec n xs)
          (min (d.getD 1 0) (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs))) ∧
          dec v = decv dec n rs ⬝ᵥ decv dec n rs
    | _, _ => False

/-- Ordinary input blocks and the models suffice for successful execution for any cap. -/
theorem solve_writes {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef) {τ : Tape K} {μ : Mem K} {cap : ℕ}
    {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    Writes .total I τ solve (Env.frame [n, cap] [b, x, x, r, p, v])
      (Fp.blocks [x, r, p, v] [n, n, n, 1])
      (fun μ' => μ'.pos = μ.pos ∧ StoresState dec n x r p v
        (cgState A (decv dec n bs) (decv dec n xs)
          (min cap (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs)))) μ') μ := by
  have hl' : μ.Live [b, x, x, r, p, v] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.1, hl.2.2⟩
  refine Writes.seq_le (writes_frame rfl rfl hl'
    (initialize_writes hS hM hB hA hbx hbr hbp hbv hxr hxp hxv hrp hrv hpv hl hbs hxs hz))
    le_rfl fun μ₁ hfr ⟨hpos, hstate, _⟩ => ?_
  have hl₁ : μ₁.Live [x, r, p, v] := by
    simp only [Mem.Live, hfr.length_eq]
    exact fun z hz' => hl z (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz' ⊢
      exact Or.inr hz')
  have hz₁ : μ₁.Room [x, r, p, v] [n, n, n, 1] := by
    simpa [Mem.Room, hfr.len_eq] using hz
  refine (writes_frame rfl rfl ((μ₁.live_append _ _).mpr ⟨hl₁, hl₁⟩)
    (rounds_writes hS hM hB hA hCmp hPos hxr hxp hxv hrp hrv hpv hl₁ hstate hz₁)).mono
    le_rfl ?_
  intro μ₂ _ ⟨hpos₂, hstate₂⟩
  exact ⟨hpos₂.trans hpos, hstate₂⟩

/-- The complete solver is total for every SPD input and cap under the stated operation models;
there is no success premise or restriction on the cap. -/
theorem solve_spec {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef) :
    (solveImpl (Op := Op) (Tst := Tst)).Meets I .total
      ((solveRel dec A).spec (SolveOperands n)) := by
  cert_intro [m, cap] (b, x) → (x', r, p, v) reads (bs, xs)
  obtain ⟨hd, hx, hbx, hbr, hbp, hbv, hxr, hxp, hxv, hrp, hrv, hpv⟩ := hadm
  subst m x'
  have hl₀ : μ.Live [b, x, r, p, v] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.2.2⟩
  have hz₀ : μ.Room [x, r, p, v] [n, n, n, 1] := by
    simpa only [Mem.room_cons, Mem.room_nil, and_true] using hz
  refine (solve_writes hS hM hB hA hCmp hPos hbx hbr hbp hbv hxr hxp hxv hrp hrv hpv
    hl₀ hbs hxs hz₀).mono le_rfl ?_
  rintro μ' _ ⟨hpos, xs', rs, ps, rr, hread, hstate⟩
  exact ⟨by simpa using hpos, [xs', rs, ps, [rr]], hread, hstate⟩

/-- From ordinary inputs, the capped early-exit program successfully computes the CG iterate
at the earlier of cap and convergence, within its static operation and scratch budget. -/
theorem runs_solve {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef) (W : Op → List ℕ → ℕ)
    {τ : Tape K} {μ : Mem K} {cap : ℕ} {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    Runs I W τ solve (Env.frame [n, cap] [b, x, x, r, p, v]) μ
      (solveCount n cap) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        decv dec n ys = cgIterate A (decv dec n bs) (decv dec n xs)
          (min cap (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs)))) := by
  have hw := solve_writes hS hM hB hA hCmp hPos (τ := τ) (cap := cap)
    hbx hbr hbp hbv hxr hxp hxv hrp hrv hpv hl hbs hxs hz
  obtain ⟨μ', hrun, hpos, hstate⟩ := hw.wp fun _ _ h => h
  refine (Runs.of_run (Q := fun μ' => μ'.pos = μ.pos ∧ StoresState dec n x r p v
    (cgState A (decv dec n bs) (decv dec n xs)
      (min cap (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs)))) μ')
    hrun ⟨hpos, hstate⟩ W).mono (le_of_eq (staticCost_solve ..)) (staticPeak_solve_le ..) ?_
  rintro μ'' ⟨hpos', hstate'⟩
  obtain ⟨ys, rs, ps, rr, hread, he, _⟩ := hstate'
  obtain ⟨_, _, hy, _, hcons⟩ := Mem.readBlocks_cons_eq_some.mp hread
  have hys : μ''.store.readBlock x.1 x.2 n = some ys := (List.cons.inj hcons).1.symm ▸ hy
  exact ⟨hpos', ys, hys, (congrArg CGState.x he).trans (hPos.cgState_x_eq _ _ _)⟩

/-- With the vector dimension as cap, SPD CG successfully returns a solution of `A*x=b`.
Exact convergence may stop it earlier, including before the first round. -/
theorem runs_solve_dim {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef) (W : Op → List ℕ → ℕ)
    {τ : Tape K} {μ : Mem K} {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    Runs I W τ solve (Env.frame [n, n] [b, x, x, r, p, v]) μ
      (solveCount n n) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        A *ᵥ decv dec n ys = decv dec n bs) := by
  refine (runs_solve hS hM hB hA hCmp hPos W (τ := τ) (cap := n)
    hbx hbr hbp hbv hxr hxp hxv hrp hrv hpv hl hbs hxs hz).mono le_rfl le_rfl ?_
  rintro μ' ⟨hpos, ys, hys, he⟩
  have hg : krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs) ≤ n := by
    simpa using krylovGrade_le_card A (decv dec n bs - A *ᵥ decv dec n xs)
  refine ⟨hpos, ys, hys, ?_⟩
  rw [he]
  exact hPos.mulVec_cgIterate_eq_of_krylovGrade_le _ _ (Nat.le_min.mpr ⟨hg, le_rfl⟩)

end NLAlib.Krylov.CG.HSCG.Carried
