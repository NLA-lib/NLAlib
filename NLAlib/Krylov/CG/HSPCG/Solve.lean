/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Initialization
public import NLAlib.Krylov.CG.HSPCG.Rounds

/-!
# Exact fixed-horizon preconditioned conjugate gradient

The complete program initializes its residual and direction, then invokes the certified
round loop. For a positive-definite matrix and a horizon at most the initial Krylov grade,
the output is the existing mathematical PCG iterate. The horizon condition ensures that
every executed scalar division has a nonzero divisor, including when the final round reaches
the exact solution.

## Main results

* `NLAlib.Krylov.CG.HSPCG.solve_spec` certifies the complete program.
* `NLAlib.Krylov.CG.HSPCG.runs_solve` states the PCG iterate and evaluated operation budget.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op]

/-- The solver retains the initial-iterate buffer and writes the three other state buffers. -/
@[admNF] def SolveOperands (n : ℕ) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => InitializeOperands n [d.headD 0] ins outs

/-- On a horizon at most the initial Krylov grade, the output is the specified PCG state. -/
@[simps (attr := storeNF)]
noncomputable def solveRel (dec : K → ℝ) {n : ℕ} (A P : Matrix (Fin n) (Fin n) ℝ) :
    BlockRel K where
  nd := 2
  inLens d := [d.headD 0, d.headD 0]
  outLens d := [d.headD 0, d.headD 0, d.headD 0, d.headD 0]
  dom d X _ := match X with
    | [bs, xs] => d.getD 1 0 ≤ krylovGrade (P * A) (P *ᵥ (decv dec n bs - A *ᵥ decv dec n xs))
    | _ => False
  rel d X _ Y := match X, Y with
    | [bs, xs], [xs', rs, zs, ps] =>
        decodedState dec n xs' rs zs ps = pcgState A P (decv dec n bs) (decv dec n xs) (d.getD 1 0)
    | _, _ => False

/-- Initialization and certified active rounds compose to store the exact PCG state. -/
theorem solve_writes {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I)
    (hPos : A.PosDef) (hPPos : P.PosDef) {τ : Tape K} {μ : Mem K} {k : ℕ}
    {b x r z p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbz : b.1 ≠ z.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [b, x, r, z, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hk : k ≤ krylovGrade (P * A) (P *ᵥ (decv dec n bs - A *ᵥ decv dec n xs)))
    (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    Writes .total I τ solve (Env.frame [n, k] [b, x, x, r, z, p])
      (Fp.blocks [x, r, z, p] [n, n, n, n])
      (fun μ' => μ'.pos = μ.pos ∧ StoresState dec n x r z p
        (pcgState A P (decv dec n bs) (decv dec n xs) k) μ') μ := by
  have hl' : μ.Live [b, x, x, r, z, p] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.1, hl.2.2⟩
  refine Writes.seq_le (writes_frame rfl rfl hl'
    (initialize_writes hS hM hB hA hP hbx hbr hbz hbp hxr hxz hxp hrz hrp hzp hl hbs hxs hz))
    le_rfl fun μ₁ hfr ⟨hpos, hstate⟩ => ?_
  have hl₁ : μ₁.Live [x, r, z, p] := by
    simp only [Mem.Live, hfr.length_eq]
    exact fun z hz' => hl z (by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hz' ⊢
      exact Or.inr hz')
  have hz₁ : μ₁.Room [x, r, z, p] [n, n, n, n] := by simpa [Mem.Room, hfr.len_eq] using hz
  have hnb (j : ℕ) (hj : j < k) :
      Nonbreakdown A ((pcgStep A P)^[j] (pcgState A P (decv dec n bs) (decv dec n xs) 0)) := by
    rw [iterate_pcgStep_pcgState, Nat.zero_add]
    exact hPos.pcgState_nonbreakdown hPPos _ _ (by omega)
  refine (writes_frame rfl rfl ((μ₁.live_append _ _).mpr ⟨hl₁, hl₁⟩)
    (rounds_writes hS hM hB hA hP hxr hxz hxp hrz hrp hzp hl₁ hstate hnb hz₁)).mono le_rfl ?_
  intro μ₂ _ ⟨hpos₂, hstate₂⟩
  exact ⟨hpos₂.trans hpos, by simpa only [iterate_pcgStep_pcgState, Nat.zero_add] using hstate₂⟩

/-- The complete program satisfies its PCG state contract for every exact operation
interpretation and every positive-definite matrix. -/
theorem solve_spec {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I) (hPos : A.PosDef) (hPPos : P.PosDef) :
    (solveImpl (Op := Op) (Tst := Tst)).Meets I .total
      ((solveRel dec A P).spec (SolveOperands n)) := by
  cert_intro [m, k] (b, x) → (x', r, z, p) reads (bs, xs)
  obtain ⟨hd, hx, hbx, hbr, hbz, hbp, hxr, hxz, hxp, hrz, hrp, hzp⟩ := hadm
  subst m x'
  change k ≤ krylovGrade (P * A) (P *ᵥ (decv dec n bs - A *ᵥ decv dec n xs)) at hdom
  have hl₀ : μ.Live [b, x, r, z, p] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.2.2⟩
  have hz₀ : μ.Room [x, r, z, p] [n, n, n, n] := by
    simpa only [Mem.room_cons, Mem.room_nil, and_true] using hz
  refine (solve_writes hS hM hB hA hP hPos hPPos
    hbx hbr hbz hbp hxr hxz hxp hrz hrp hzp hl₀ hbs hxs hdom hz₀).mono
    le_rfl ?_
  rintro μ' _ ⟨hpos, xs', rs, zs, ps, hread, hstate⟩
  exact ⟨by simpa using hpos, [xs', rs, zs, ps], hread, hstate⟩

/-- A stored PCG state exposes its iterate through the first vector block. -/
theorem StoresState.read_x {dec : K → ℝ} {n : ℕ} {x r z p : ℕ × ℕ}
    {s : PCGState ℝ (Fin n)} {μ : Mem K} (h : StoresState dec n x r z p s μ) :
    ∃ xs, μ.store.readBlock x.1 x.2 n = some xs ∧ decv dec n xs = s.x := by
  obtain ⟨xs, rs, zs, ps, hr, he⟩ := h
  obtain ⟨ys, _, hy, _, hcons⟩ := Mem.readBlocks_cons_eq_some.mp hr
  exact ⟨xs, (List.cons.inj hcons).1.symm ▸ hy, congrArg PCGState.x he⟩

/-- For any exact interpretation, the fixed-horizon program computes the PCG iterate, with
the evaluator-derived operation counts and workspace. The horizon may reach the initial
residual's Krylov grade. -/
theorem runs_solve {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I) (hPos : A.PosDef) (hPPos : P.PosDef)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {k : ℕ}
    {b x r z p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbz : b.1 ≠ z.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [b, x, r, z, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hk : k ≤ krylovGrade (P * A) (P *ᵥ (decv dec n bs - A *ᵥ decv dec n xs)))
    (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    Runs I W τ solve (Env.frame [n, k] [b, x, x, r, z, p]) μ (solveCount n k) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        decv dec n ys = pcgIterate A P (decv dec n bs) (decv dec n xs) k) := by
  have hw := solve_writes hS hM hB hA hP hPos hPPos (τ := τ)
    hbx hbr hbz hbp hxr hxz hxp hrz hrp hzp hl hbs hxs hk hz
  obtain ⟨μ', hrun, hpos, hstate⟩ := hw.wp fun _ _ h => h
  refine (Runs.of_run (Q := fun μ' => μ'.pos = μ.pos ∧ StoresState dec n x r z p
    (pcgState A P (decv dec n bs) (decv dec n xs) k) μ') hrun ⟨hpos, hstate⟩ W).mono
    (le_of_eq (staticCost_solve ..))
    (staticPeak_solve_le ..) ?_
  rintro μ'' ⟨hpos', hstate'⟩
  obtain ⟨ys, hys, he⟩ := hstate'.read_x
  exact ⟨hpos', ys, hys, he.trans (hPos.pcgState_x_eq hPPos _ _ _)⟩

end NLAlib.Krylov.CG.HSPCG
