/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Solve
public import NLAlib.Krylov.CG.HSCG.Carried.Rounded
public import NLAlib.Krylov.CG.HSCG.Linked

/-!
# Total early-exit CG with sequential BLAS

Exact comparison queries coexist with the scalar, BLAS and operator contracts. Generic
profile transfer implements the carried-product solver with scalar arithmetic, retaining its
successful early-exit behavior and exposing the scalar and comparison budgets.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.exists_exactContracts` jointly realizes all model contracts.
* `NLAlib.Krylov.CG.HSCG.Carried.runs_solve_seq` gives the linked total solver and scalar budget.
* `NLAlib.Krylov.CG.HSCG.Carried.runs_solve_dim_seq` returns a solution of the SPD system.
* `NLAlib.Krylov.CG.HSCG.Carried.runs_rounded_step_seq` gives local standard-model error bounds.
* `NLAlib.Krylov.CG.HSCG.Carried.exists_inflContracts` witnesses genuinely nonexact scalar calls.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried

open Ops
open scoped Matrix

/-- Arbitrary real scalar arithmetic, exact matvec and decoded comparisons coexist on one
interpretation. Their contracts retain the same machine and matrix. -/
theorem exists_scalarMatvecCmp {Op Tst : Type} [Has ScalarOp Op] [Has OperatorOp Op]
    [Has CmpTst Tst] [Apart ScalarOp OperatorOp Op] {m n : ℕ}
    (M : Machine ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ I : Interp Op Tst ℝ, IsScalar M I ∧ IsExactMatvec id A I ∧ IsCmp id I := by
  obtain ⟨I, hS, hA⟩ := exists_isScalar_isExactMatvec_ofMachine (Op := Op) (Tst := Tst) M A
  let J : Interp Op Tst ℝ := { I with test := fun q d a μ => match Has.proj (G := CmpTst) q with
    | some c => (μ.readBlocks a c.lens).map (c.fn id)
    | none => I.test q d a μ }
  have hCmp : IsCmp id J := by
    intro c d a μ xs hread
    simp only [J, Has.proj_inj, hread, Option.map_some]
  exact ⟨J, hS, hA, hCmp⟩

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
variable [Apart Blas1Op ScalarOp Op] [Apart Blas1Op OperatorOp Op]

/-- Five vector-length multiplication counts per active standard CG round. Copies include
both direction copies, scalar dot outputs and the retained-product scalar copy. -/
noncomputable def seqStepCount (n : ℕ) : Count Op Tst :=
  (5 * n) • Count.one (Has.inj ScalarOp.mul) [] +
    (2 * (n - 1) + 3 * n) • Count.one (Has.inj ScalarOp.add) [] +
    (2 * (1 - (1 - n)) + 2 * n + 1) • Count.one (Has.inj ScalarOp.copy) [] +
    2 • Count.one (Has.inj (ScalarOp.lit 0)) [] +
    2 • Count.one (Has.inj ScalarOp.div) [] + Count.one (Has.inj ScalarOp.neg) [] +
    Count.one (Has.inj OperatorOp.matvec) [n, n]

/-- Sequential BLAS exposes the standard two-dot-product scalar count. -/
theorem push_stepCount_seq (n : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (stepCount n) = seqStepCount n := by
  count_eval [stepCount, seqStepCount, HSCG.seq_cost_matvec]

/-- Sequential dot-product scratch fits alongside the reused vector and three scalar cells. -/
theorem stepPeak_seq_le (n : ℕ) :
    stepPeak (Blas.ws (Op := Op) 0) n ≤ 2 * n + 4 := by
  simp [stepPeak, Blas.ws]
  omega

/-- Sequential BLAS supplies the rounded active CG recurrence from explicit input margins,
with scalar counts and no assumed successful execution. -/
theorem runs_rounded_step_seq {M : Machine K} {dec : K → ℝ} {n : ℕ} {em u : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hu : 0 ≤ u)
    (hA : IsMatvec dec A (em * specNorm A) I)
    {τ : Tape K} {μ : Mem K} {x r p v : ℕ × ℕ} {xs rs ps : List K} {rr : K}
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [x, r, p, v])
    (hx : μ.store.readBlock x.1 x.2 n = some xs)
    (hr : μ.store.readBlock r.1 r.2 n = some rs)
    (hp : μ.store.readBlock p.1 p.2 n = some ps) (hv : μ.store.get v.1 v.2 = some rr)
    (hed : (Blas.seq.err u).dot n < 1) (hrne : decv dec n rs ≠ 0)
    (hrr : |dec rr - decv dec n rs ⬝ᵥ decv dec n rs| ≤
      (Blas.seq.err u).dot n * ∑ i : Fin n, |decv dec n rs i * decv dec n rs i|)
    (hmargin : ∀ q : Fin n → ℝ,
      ‖WithLp.toLp 2 (A *ᵥ decv dec n ps - q)‖ ≤
        em * specNorm A * ‖WithLp.toLp 2 (decv dec n ps)‖ →
      (Blas.seq.err u).dot n * ∑ i, |decv dec n ps i * q i| < decv dec n ps ⬝ᵥ q)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    ConditionalRuns I (Blas.ws 0) τ (step.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n] [x, r, p, v, x, r, p, v]) μ (seqStepCount n) (2 * n + 4)
      ((Rounded.stepRel em u (Blas.seq.err u) dec A).Post
        [n] [xs, rs, ps, [rr]] [x, r, p, v] [] μ) := by
  have hcert := Blas.seq_certifies (Op := Op) (Tst := Tst) hM hu (fun _ => True)
  obtain ⟨hS', hB⟩ := hcert.meets I hS
  have hA' : IsMatvec dec A (em * specNorm A) (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  have hrun := Rounded.runs_step hS' hM hB trivial hA' (Blas.ws 0) (τ := τ)
    hxr hxp hxv hrp hrv hpv hl hx hr hp hv hed hrne hrr hmargin hz
  exact (hcert.transfer I τ _ _ _ _ _ _ hrun).mono
    (le_of_eq (push_stepCount_seq n)) (stepPeak_seq_le n) fun _ h => h

/-- Initial scalar counts include the residual's initial self-product. -/
noncomputable def seqInitializeCount (n : ℕ) : Count Op Tst :=
  HSCG.seqInitializeCount n + n • Count.one (Has.inj ScalarOp.mul) [] +
    (n - 1) • Count.one (Has.inj ScalarOp.add) [] +
    (1 - (1 - n)) • Count.one (Has.inj ScalarOp.copy) [] +
    Count.one (Has.inj (ScalarOp.lit 0)) []

/-- The scalar initialization budget is computed through the profile. -/
theorem push_initializeCount_seq (n : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (initializeCount n) =
      seqInitializeCount n := by
  count_eval [initializeCount, seqInitializeCount, HSCG.push_initializeCount_seq]

/-- The scalar implementation reuses initialization and dot-product scratch. -/
theorem initializePeak_seq_le (n : ℕ) :
    initializePeak (Blas.ws (Op := Op) 0) n ≤ n + 2 := by
  apply max_le (HSCG.initializePeak_seq_le n)
  simp [Blas.ws]

variable [Has CmpTst Tst]

/-- The complete scalar budget retains comparison tests and permits early exit below the cap. -/
noncomputable def seqSolveCount (n cap : ℕ) : Count Op Tst :=
  seqInitializeCount n + cap • (Count.test (Has.inj CmpTst.isPos) [] + seqStepCount n)

/-- Cost transfer preserves comparison queries while lowering every BLAS1 call. -/
theorem push_solveCount_seq (n cap : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (solveCount n cap) =
      seqSolveCount n cap := by
  simp only [solveCount, roundsCount, map_add, map_nsmul, Count.push_test,
    push_initializeCount_seq, push_stepCount_seq, seqSolveCount]

/-- The sequential solver's scratch bound is independent of its cap. -/
theorem solvePeak_seq_le (n : ℕ) : solvePeak (Blas.ws (Op := Op) 0) n ≤ 2 * n + 4 := by
  exact max_le ((initializePeak_seq_le n).trans (by omega)) (stepPeak_seq_le n)

/-- Scalar, BLAS1, operator and comparison contracts have a common real interpretation. -/
theorem exists_exactContracts [Apart ScalarOp OperatorOp Op] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ I : Interp Op Tst ℝ, ExactModel id exactMachine ∧ IsScalar exactMachine I ∧
      IsExactBlas1 id (fun _ => True) I ∧ IsExactMatvec id A I ∧ IsCmp id I := by
  obtain ⟨I, hS, hA, hCmp⟩ := exists_scalarMatvecCmp (Op := Op) (Tst := Tst) exactMachine A
  have hcert := Blas.seq_certifies_exact (Op := Op) (Tst := Tst)
    exactModel_exactMachine (fun _ => True)
  obtain ⟨hS', hB⟩ := hcert.meets I hS
  have hA' : IsExactMatvec id A (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  exact ⟨_, exactModel_exactMachine, hS', hB, hA', hCmp⟩

/-- Every real standard-model scalar machine has a joint sequential BLAS, exact matvec and
comparison interpretation, with its own unit roundoff and scalar functions. -/
theorem exists_stdContracts_ofMachine [Apart ScalarOp OperatorOp Op] {n : ℕ} {u : ℝ}
    (M : Machine ℝ) (hM : StdModel u id M) (hu : 0 ≤ u) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ I : Interp Op Tst ℝ, StdModel u id M ∧ IsScalar M I ∧
      IsBlas1 id (Blas.seq.err u) (fun _ => True) I ∧ IsExactMatvec id A I ∧ IsCmp id I := by
  obtain ⟨I, hS, hA, hCmp⟩ := exists_scalarMatvecCmp (Op := Op) (Tst := Tst) M A
  have hcert := Blas.seq_certifies (Op := Op) (Tst := Tst) hM hu (fun _ => True)
  obtain ⟨hS', hB⟩ := hcert.meets I hS
  have hA' : IsExactMatvec id A (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  exact ⟨_, hM, hS', hB, hA', hCmp⟩

/-- Rounded scalar, sequential BLAS, exact operator and comparison contracts coexist for
every nonnegative unit roundoff; the interpretation is concrete real arithmetic. -/
theorem exists_stdContracts [Apart ScalarOp OperatorOp Op] {n : ℕ}
    (u : ℝ) (hu : 0 ≤ u) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ I : Interp Op Tst ℝ, StdModel u id exactMachine ∧ IsScalar exactMachine I ∧
      IsBlas1 id (Blas.seq.err u) (fun _ => True) I ∧ IsExactMatvec id A I ∧ IsCmp id I := by
  exact exists_stdContracts_ofMachine (Op := Op) (Tst := Tst)
    exactMachine (stdModel_exact hu) hu A

/-- A genuinely nonexact scalar machine jointly realizes the standard-model contracts and
sequential BLAS: at positive roundoff, its computed `1+1` differs from two. -/
theorem exists_inflContracts [Apart ScalarOp OperatorOp Op] {n : ℕ}
    (u : ℝ) (hu : 0 < u) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ I : Interp Op Tst ℝ, StdModel u id (inflMachine u) ∧ IsScalar (inflMachine u) I ∧
      IsBlas1 id (Blas.seq.err u) (fun _ => True) I ∧ IsExactMatvec id A I ∧ IsCmp id I ∧
      (inflMachine u).add 1 1 ≠ 2 := by
  obtain ⟨I, hM, hS, hB, hA, hCmp⟩ := exists_stdContracts_ofMachine (Op := Op) (Tst := Tst)
    (inflMachine u) (stdModel_infl hu.le) hu.le A
  refine ⟨I, hM, hS, hB, hA, hCmp, ?_⟩
  change (1 + 1) * (1 + u) ≠ 2
  intro h
  nlinarith

/-- Sequential BLAS transfers successful early-exit CG, including its scalar/test budget.
The cap is arbitrary; the program stops safely if exact convergence occurs earlier. -/
theorem runs_solve_seq {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef)
    {τ : Tape K} {μ : Mem K} {cap : ℕ} {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    ConditionalRuns I (Blas.ws 0) τ (solve.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n, cap] [b, x, x, r, p, v]) μ (seqSolveCount n cap) (2 * n + 4)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        decv dec n ys = cgIterate A (decv dec n bs) (decv dec n xs)
          (min cap (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs)))) := by
  have hcert := Blas.seq_certifies_exact (Op := Op) (Tst := Tst) hM (fun _ => True)
  obtain ⟨hS', hB⟩ := hcert.meets I hS
  have hA' : IsExactMatvec dec A (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  have hCmp' : IsCmp dec (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) := hCmp
  have hrun := runs_solve hS' hM hB hA' hCmp' hPos (Blas.ws 0) (τ := τ) (cap := cap)
    hbx hbr hbp hbv hxr hxp hxv hrp hrv hpv hl hbs hxs hz
  exact (hcert.transfer I τ _ _ _ _ _ _ hrun).mono
    (le_of_eq (push_solveCount_seq n cap)) (solvePeak_seq_le n) fun _ h => h

/-- The sequential scalar implementation, capped by the dimension, successfully solves the
SPD system with its stated scalar/test budget and workspace. -/
theorem runs_solve_dim_seq {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef)
    {τ : Tape K} {μ : Mem K} {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    ConditionalRuns I (Blas.ws 0) τ (solve.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n, n] [b, x, x, r, p, v]) μ (seqSolveCount n n) (2 * n + 4)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        A *ᵥ decv dec n ys = decv dec n bs) := by
  refine (runs_solve_seq hS hM hA hCmp hPos (τ := τ) (cap := n)
    hbx hbr hbp hbv hxr hxp hxv hrp hrv hpv hl hbs hxs hz).mono le_rfl le_rfl ?_
  rintro μ' ⟨hpos, ys, hys, he⟩
  have hg : krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs) ≤ n := by
    simpa using krylovGrade_le_card A (decv dec n bs - A *ᵥ decv dec n xs)
  refine ⟨hpos, ys, hys, ?_⟩
  rw [he]
  exact hPos.mulVec_cgIterate_eq_of_krylovGrade_le _ _ (Nat.le_min.mpr ⟨hg, le_rfl⟩)

end NLAlib.Krylov.CG.HSCG.Carried
