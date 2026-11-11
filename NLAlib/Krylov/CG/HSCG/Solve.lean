/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Initialization
public import NLAlib.Krylov.CG.HSCG.Rounds

/-!
# Exact fixed-horizon Hestenes–Stiefel conjugate gradient

The complete program initializes its residual and direction, then invokes the certified
round loop. For a positive-definite matrix and a horizon at most the initial Krylov grade,
the output is the existing mathematical CG iterate. The horizon condition ensures that
every executed scalar division has a nonzero divisor, including when the final round reaches
the exact solution.

## Main results

* `NLAlib.Krylov.CG.HSCG.solve_spec` certifies the complete program.
* `NLAlib.Krylov.CG.HSCG.runs_solve` states the CG iterate and evaluated operation budget.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- The solver retains the initial-iterate buffer and writes the two other state buffers. -/
@[admNF] def SolveOperands (n : ℕ) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => InitializeOperands n [d.headD 0] ins outs

/-- On a horizon at most the initial Krylov grade, the output is the specified CG state. -/
@[simps (attr := storeNF)]
noncomputable def solveRel (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    BlockRel K where
  nd := 2
  inLens d := [d.headD 0, d.headD 0]
  outLens d := [d.headD 0, d.headD 0, d.headD 0]
  dom d X _ := match X with
    | [bs, xs] => d.getD 1 0 ≤ krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs)
    | _ => False
  rel d X _ Y := match X, Y with
    | [bs, xs], [xs', rs, ps] =>
        decodedState dec n xs' rs ps = cgState A (decv dec n bs) (decv dec n xs) (d.getD 1 0)
    | _, _ => False

/-- Initialization and certified active rounds compose to store the exact CG state. -/
theorem solve_writes {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hPos : A.PosDef) {τ : Tape K} {μ : Mem K} {k : ℕ}
    {b x r p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hl : μ.Live [b, x, r, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hk : k ≤ krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs))
    (hz : μ.Room [x, r, p] [n, n, n]) :
    Writes .total I τ solve (Env.frame [n, k] [b, x, x, r, p])
      (Fp.blocks [x, r, p] [n, n, n])
      (fun μ' => μ'.pos = μ.pos ∧ StoresState dec n x r p
        (cgState A (decv dec n bs) (decv dec n xs) k) μ') μ := by
  have hl' : μ.Live [b, x, x, r, p] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.1, hl.2.2⟩
  refine Writes.seq_le (writes_frame rfl rfl hl'
    (initialize_writes hS hM hB hA hbx hbr hbp hxr hxp hrp hl hbs hxs hz))
    le_rfl fun μ₁ hfr ⟨hpos, hstate⟩ => ?_
  have hl₁ : μ₁.Live [x, r, p] := by
    simp only [Mem.Live, hfr.length_eq]
    exact fun z hz' => hl z (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz' ⊢
      exact Or.inr hz')
  have hz₁ : μ₁.Room [x, r, p] [n, n, n] := by simpa [Mem.Room, hfr.len_eq] using hz
  have hnb (j : ℕ) (hj : j < k) :
      Nonbreakdown A ((cgStep A)^[j] (cgState A (decv dec n bs) (decv dec n xs) 0)) := by
    rw [iterate_cgStep_cgState, Nat.zero_add]
    exact hPos.cgState_nonbreakdown _ _ (by omega)
  refine (writes_frame rfl rfl ((μ₁.live_append _ _).mpr ⟨hl₁, hl₁⟩)
    (rounds_writes hS hM hB hA hxr hxp hrp hl₁ hstate hnb hz₁)).mono le_rfl ?_
  intro μ₂ _ ⟨hpos₂, hstate₂⟩
  exact ⟨hpos₂.trans hpos, by simpa only [iterate_cgStep_cgState, Nat.zero_add] using hstate₂⟩

/-- The complete program satisfies its CG state contract for every exact operation
interpretation and every positive-definite matrix. -/
theorem solve_spec {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I) (hPos : A.PosDef) :
    (solveImpl (Op := Op) (Tst := Tst)).Triple I .total
      ((solveRel dec A).spec (SolveOperands n)) := by
  cert_intro [m, k] (b, x) → (x', r, p) reads (bs, xs)
  obtain ⟨hd, hx, hbx, hbr, hbp, hxr, hxp, hrp⟩ := hadm
  subst m x'
  change k ≤ krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs) at hdom
  have hl₀ : μ.Live [b, x, r, p] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.2.2⟩
  have hz₀ : μ.Room [x, r, p] [n, n, n] := by
    simpa only [Mem.room_cons, Mem.room_nil, and_true] using hz
  refine (solve_writes hS hM hB hA hPos hbx hbr hbp hxr hxp hrp hl₀ hbs hxs hdom hz₀).mono
    le_rfl ?_
  rintro μ' _ ⟨hpos, xs', rs, ps, hread, hstate⟩
  exact ⟨by simpa using hpos, [xs', rs, ps], hread, hstate⟩

private theorem StoresState.read_x {dec : K → ℝ} {n : ℕ} {x r p : ℕ × ℕ}
    {s : CGState ℝ (Fin n)} {μ : Mem K} (h : StoresState dec n x r p s μ) :
    ∃ xs, μ.store.readBlock x.1 x.2 n = some xs ∧ decv dec n xs = s.x := by
  obtain ⟨xs, rs, ps, hr, he⟩ := h
  obtain ⟨ys, _, hy, _, hcons⟩ := Mem.readBlocks_cons_eq_some.mp hr
  exact ⟨xs, (List.cons.inj hcons).1.symm ▸ hy, congrArg CGState.x he⟩

/-- For any exact interpretation, the fixed-horizon program computes the CG iterate, with
the evaluator-derived operation counts and workspace. The horizon may reach the initial
residual's Krylov grade. -/
theorem runs_solve {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I) (hPos : A.PosDef)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {k : ℕ}
    {b x r p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hl : μ.Live [b, x, r, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hk : k ≤ krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs))
    (hz : μ.Room [x, r, p] [n, n, n]) :
    ConditionalRuns I W τ solve (Env.frame [n, k] [b, x, x, r, p]) μ
      (solveCount n k) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        decv dec n ys = cgIterate A (decv dec n bs) (decv dec n xs) k) := by
  have hw := solve_writes hS hM hB hA hPos (τ := τ) hbx hbr hbp hxr hxp hrp hl hbs hxs hk hz
  obtain ⟨μ', hrun, hpos, hstate⟩ := hw.wp fun _ _ h => h
  refine (ConditionalRuns.of_run (Q := fun μ' => μ'.pos = μ.pos ∧ StoresState dec n x r p
    (cgState A (decv dec n bs) (decv dec n xs) k) μ') hrun ⟨hpos, hstate⟩ W).mono
    (le_of_eq (staticCost_solve ..))
    (staticPeak_solve_le ..) ?_
  rintro μ'' ⟨hpos', hstate'⟩
  obtain ⟨ys, hys, he⟩ := hstate'.read_x
  exact ⟨hpos', ys, hys, he.trans (hPos.cgState_x_eq _ _ _)⟩

end NLAlib.Krylov.CG.HSCG
