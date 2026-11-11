/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Solve
public import NLAlib.Ops.Profiles.BlasCert

/-!
# Exact preconditioned conjugate gradient with sequential BLAS

The BLAS profile implements every vector operation using scalar arithmetic and sequential
summation. The system and inverse-preconditioner applications remain separately counted
primitive operators. Correctness and cost transfer use the generic profile theorem.

## Main results

* `NLAlib.Krylov.CG.HSPCG.exists_exactContracts` realizes all exact contracts jointly.
* `NLAlib.Krylov.CG.HSPCG.seqStepCount` states the linked round scalar counts.
* `NLAlib.Krylov.CG.HSPCG.runs_solve_seq` computes the fixed-horizon PCG iterate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op]
variable [Apart Blas1Op ScalarOp Op] [Apart Blas1Op OperatorOp Op]
  [Apart Blas1Op (Tagged Preconditioner OperatorOp) Op]

/-- The scalar counts of one round under the sequential BLAS profile, including the vector
copies and the zero literals of the three dot products. The operator call stays primitive. -/
noncomputable def seqStepCount (n : ℕ) : Count Op Tst :=
  (6 * n) • Count.one (Has.inj ScalarOp.mul) [] +
    (3 * (n - 1) + 3 * n) • Count.one (Has.inj ScalarOp.add) [] +
    (3 * (1 - (1 - n)) + 2 * n) • Count.one (Has.inj ScalarOp.copy) [] +
    3 • Count.one (Has.inj (ScalarOp.lit 0)) [] +
    2 • Count.one (Has.inj ScalarOp.div) [] + Count.one (Has.inj ScalarOp.neg) [] +
    Count.one (Has.inj OperatorOp.matvec) [n, n] +
    Count.one (Tagged.inj Preconditioner OperatorOp.matvec) [n, n]

/-- Pushing the abstract counts through sequential BLAS gives the stated scalar counts. -/
theorem push_stepCount_seq (n : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (stepCount n) = seqStepCount n := by
  count_eval [stepCount, seqStepCount]
  simp [Blas.seq, Profile.over, Blas.level1, Blas.level1Cost, Blas.sumSeq,
    Blas.sumSeqCost, Tagged.inj, Blas.sc]
  module

/-- Two vector scratch buffers, the dot-product workspace and five cells suffice. -/
theorem stepPeak_seq_le (n : ℕ) :
    stepPeak (Blas.ws (Op := Op) 0) n ≤ 3 * n + 5 := by
  simp [stepPeak, Blas.ws, Tagged.inj]
  omega

/-- Scalar counts of initialization under the sequential BLAS profile. -/
noncomputable def seqInitializeCount (n : ℕ) : Count Op Tst :=
  n • Count.one (Has.inj ScalarOp.mul) [] + n • Count.one (Has.inj ScalarOp.add) [] +
    (2 * n) • Count.one (Has.inj ScalarOp.copy) [] +
    Count.one (Has.inj (ScalarOp.lit (-1))) [] +
    Count.one (Has.inj OperatorOp.matvec) [n, n] +
    Count.one (Tagged.inj Preconditioner OperatorOp.matvec) [n, n]

/-- The complete scalar budget is initialization plus the prescribed number of rounds. -/
noncomputable def seqSolveCount (n k : ℕ) : Count Op Tst :=
  seqInitializeCount n + k • seqStepCount n

/-- The initialization count is pushed forward by the same implementation table. -/
theorem push_initializeCount_seq (n : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (initializeCount n) =
      seqInitializeCount n := by
  count_eval [initializeCount, seqInitializeCount]
  simp [Blas.seq, Profile.over, Blas.level1, Blas.level1Cost, Blas.sumSeq,
    Blas.sumSeqCost, Tagged.inj, Blas.sc]
  module

/-- The scalar budget of the complete solver is computed by cost transfer. -/
theorem push_solveCount_seq (n k : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (solveCount n k) = seqSolveCount n k := by
  simp only [solveCount, map_add, map_nsmul, push_initializeCount_seq,
    push_stepCount_seq, seqSolveCount]

/-- Sequential BLAS initialization needs one vector and two cells. -/
theorem initializePeak_seq_le (n : ℕ) :
    initializePeak (Blas.ws (Op := Op) 0) n ≤ n + 2 := by
  simp [initializePeak, Blas.ws, Tagged.inj]

/-- The solver reuses the round workspace after initialization. -/
theorem solvePeak_seq_le (n : ℕ) : solvePeak (Blas.ws (Op := Op) 0) n ≤ 3 * n + 5 := by
  exact max_le ((initializePeak_seq_le n).trans (by omega)) (stepPeak_seq_le n)

/-- Scalar arithmetic, both exact operators and sequential BLAS are jointly realizable. -/
theorem exists_exactContracts [Apart ScalarOp OperatorOp Op]
    [Apart ScalarOp (Tagged Preconditioner OperatorOp) Op]
    [Apart OperatorOp (Tagged Preconditioner OperatorOp) Op] {n : ℕ}
    (A P : Matrix (Fin n) (Fin n) ℝ) :
    ∃ I : Interp Op Tst ℝ, ExactModel id exactMachine ∧ IsScalar exactMachine I ∧
      IsExactBlas1 id (fun _ => True) I ∧ IsExactMatvec id A I ∧
      IsExactPreconditioner id P I := by
  let F : Op → BlockFn ℝ := fun o =>
    match Has.proj (G := ScalarOp) o with
    | some a => exactMachine.fn a
    | none => match Has.proj (G := OperatorOp) o with
      | some _ => exactMatvecFn A
      | none => exactMatvecFn P
  have hS : IsScalar exactMachine (Interp.ofFns F : Interp Op Tst ℝ) :=
    isScalar_ofFns _ _ fun a => by simp [F]
  have hA := Interp.ofFns_isFn (Tst := Tst) F .total (Has.inj OperatorOp.matvec) AnyOperands
  have hP := Interp.ofFns_isFn (Tst := Tst) F .total
    (Tagged.inj Preconditioner OperatorOp.matvec) AnyOperands
  have hfA : F (Has.inj OperatorOp.matvec) = exactMatvecFn A := by simp [F]
  have hfP : F (Tagged.inj Preconditioner OperatorOp.matvec) = exactMatvecFn P := by
    simp [F, Tagged.inj]
  rw [hfA] at hA
  rw [hfP] at hP
  obtain ⟨hS', hB⟩ := (Blas.seq_certifies_exact exactModel_exactMachine
    (fun _ => True)).meets (Interp.ofFns F : Interp Op Tst ℝ) hS
  have hA' : IsExactMatvec id A
      ((Interp.ofFns F : Interp Op Tst ℝ).link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec))
      hA.meets_matvec
  have hP' : IsExactPreconditioner id P
      ((Interp.ofFns F : Interp Op Tst ℝ).link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept
      (Apart.proj_inj (⟨OperatorOp.matvec⟩ : Tagged Preconditioner OperatorOp))) hP.meets_matvec
  exact ⟨_, exactModel_exactMachine, hS', hB, hA', hP'⟩

/-- Sequential BLAS supplies the complete exact fixed-horizon PCG result by generic linking,
with scalar operation counts and the same PCG iterate. -/
theorem runs_solve_seq {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I) (hPos : A.PosDef) (hPPos : P.PosDef)
    {τ : Tape K} {μ : Mem K} {k : ℕ} {b x r z p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbz : b.1 ≠ z.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [b, x, r, z, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hk : k ≤ krylovGrade (P * A) (P *ᵥ (decv dec n bs - A *ᵥ decv dec n xs)))
    (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    Runs I (Blas.ws 0) τ (solve.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n, k] [b, x, x, r, z, p]) μ (seqSolveCount n k) (3 * n + 5)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        decv dec n ys = pcgIterate A P (decv dec n bs) (decv dec n xs) k) := by
  have hcert := Blas.seq_certifies_exact (Op := Op) (Tst := Tst) hM (fun _ => True)
  obtain ⟨hS', hB⟩ := hcert.meets I hS
  have hA' : IsExactMatvec dec A (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  have hP' : IsExactPreconditioner dec P (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept
      (Apart.proj_inj (⟨OperatorOp.matvec⟩ : Tagged Preconditioner OperatorOp))) hP
  have hrun := runs_solve hS' hM hB hA' hP' hPos hPPos (Blas.ws 0) (τ := τ)
    hbx hbr hbz hbp hxr hxz hxp hrz hrp hzp hl hbs hxs hk hz
  exact (hcert.transfer I τ _ _ _ _ _ _ hrun).mono
    (le_of_eq (push_solveCount_seq n k)) (solvePeak_seq_le n) fun _ h => h

/-- At the preconditioned Krylov grade the linked program successfully solves the system.
The zero-grade case initializes successfully without executing a scalar division. -/
theorem runs_solve_seq_of_eq_krylovGrade {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A P : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hA : IsExactMatvec dec A I)
    (hP : IsExactPreconditioner dec P I) (hPos : A.PosDef) (hPPos : P.PosDef)
    {τ : Tape K} {μ : Mem K} {k : ℕ} {b x r z p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbz : b.1 ≠ z.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hzp : z.1 ≠ p.1)
    (hl : μ.Live [b, x, r, z, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hk : k = krylovGrade (P * A) (P *ᵥ (decv dec n bs - A *ᵥ decv dec n xs)))
    (hz : μ.Room [x, r, z, p] [n, n, n, n]) :
    Runs I (Blas.ws 0) τ (solve.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n, k] [b, x, x, r, z, p]) μ (seqSolveCount n k) (3 * n + 5)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        A *ᵥ decv dec n ys = decv dec n bs) := by
  have hrun := runs_solve_seq hS hM hA hP hPos hPPos (τ := τ)
    hbx hbr hbz hbp hxr hxz hxp hrz hrp hzp hl hbs hxs (le_of_eq hk) hz
  refine hrun.mono le_rfl le_rfl ?_
  rintro μ' ⟨hpos, ys, hys, he⟩
  refine ⟨hpos, ys, hys, ?_⟩
  rw [he]
  exact hPos.mulVec_pcgIterate_of_krylovGrade_le hPPos _ _ (ge_of_eq hk)

end NLAlib.Krylov.CG.HSPCG
