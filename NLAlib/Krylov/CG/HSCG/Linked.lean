/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Solve
public import NLAlib.Ops.Profiles.BlasCert

/-!
# Exact Hestenes–Stiefel programs with sequential BLAS

The BLAS profile implements every vector operation using scalar arithmetic and sequential
summation. The matrix-vector operation remains the chosen operator. Correctness and cost
transfer use the generic profile theorem.

## Main results

* `NLAlib.Krylov.CG.HSCG.exists_exactContracts` realizes all exact contracts jointly.
* `NLAlib.Krylov.CG.HSCG.runs_step_seq` gives the linked round with scalar counts.
* `NLAlib.Krylov.CG.HSCG.runs_solve_seq` computes the fixed-horizon CG iterate.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
variable [Apart Blas1Op ScalarOp Op] [Apart Blas1Op OperatorOp Op]

/-- The scalar counts of one round under the sequential BLAS profile, including the vector
copies and the zero literals of the three dot products. The operator call stays primitive. -/
noncomputable def seqStepCount (n : ℕ) : Count Op Tst :=
  (6 * n) • Count.one (Has.inj ScalarOp.mul) [] +
    (3 * (n - 1) + 3 * n) • Count.one (Has.inj ScalarOp.add) [] +
    (3 * (1 - (1 - n)) + 2 * n) • Count.one (Has.inj ScalarOp.copy) [] +
    3 • Count.one (Has.inj (ScalarOp.lit 0)) [] +
    2 • Count.one (Has.inj ScalarOp.div) [] + Count.one (Has.inj ScalarOp.neg) [] +
    Count.one (Has.inj OperatorOp.matvec) [n, n]

omit [Apart Blas1Op ScalarOp Op] in
/-- Sequential BLAS keeps the primitive matrix-vector operation and its call count. -/
theorem seq_cost_matvec (n : ℕ) :
    (Blas.seq (Op := Op) (Tst := Tst)).cost (Has.inj OperatorOp.matvec) [n, n] =
      Count.one (Has.inj OperatorOp.matvec) [n, n] := by
  simp [Blas.seq, Profile.over, Blas.level1, Blas.level1Cost, Blas.sumSeq,
    Blas.sumSeqCost]

/-- Pushing the abstract counts through sequential BLAS gives the stated scalar counts. -/
theorem push_stepCount_seq (n : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (stepCount n) = seqStepCount n := by
  count_eval [stepCount, seqStepCount, seq_cost_matvec]

/-- Two vector scratch buffers, the dot-product workspace and five cells suffice. -/
theorem stepPeak_seq_le (n : ℕ) :
    stepPeak (Blas.ws (Op := Op) 0) n ≤ 3 * n + 5 := by
  simp [stepPeak, Blas.ws]
  omega

/-- Scalar counts of initialization under the sequential BLAS profile. -/
noncomputable def seqInitializeCount (n : ℕ) : Count Op Tst :=
  n • Count.one (Has.inj ScalarOp.mul) [] + n • Count.one (Has.inj ScalarOp.add) [] +
    (2 * n) • Count.one (Has.inj ScalarOp.copy) [] +
    Count.one (Has.inj (ScalarOp.lit (-1))) [] +
    Count.one (Has.inj OperatorOp.matvec) [n, n]

/-- The complete scalar budget is initialization plus the prescribed number of rounds. -/
noncomputable def seqSolveCount (n k : ℕ) : Count Op Tst :=
  seqInitializeCount n + k • seqStepCount n

/-- The initialization count is pushed forward by the same implementation table. -/
theorem push_initializeCount_seq (n : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (initializeCount n) =
      seqInitializeCount n := by
  count_eval [initializeCount, seqInitializeCount, seq_cost_matvec]

/-- The scalar budget of the complete solver is computed by cost transfer. -/
theorem push_solveCount_seq (n k : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (solveCount n k) = seqSolveCount n k := by
  simp only [solveCount, map_add, map_nsmul, push_initializeCount_seq,
    push_stepCount_seq, seqSolveCount]

/-- Sequential BLAS initialization needs one vector and two cells. -/
theorem initializePeak_seq_le (n : ℕ) :
    initializePeak (Blas.ws (Op := Op) 0) n ≤ n + 2 := by
  simp [initializePeak, Blas.ws]

/-- The solver reuses the round workspace after initialization. -/
theorem solvePeak_seq_le (n : ℕ) : solvePeak (Blas.ws (Op := Op) 0) n ≤ 3 * n + 5 := by
  exact max_le ((initializePeak_seq_le n).trans (by omega)) (stepPeak_seq_le n)

/-- Exact scalar arithmetic, sequential BLAS1 and the exact operator contract have a common
real interpretation for every matrix and every dimension. -/
theorem exists_exactContracts [Apart ScalarOp OperatorOp Op] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ I : Interp Op Tst ℝ, ExactModel id exactMachine ∧ IsScalar exactMachine I ∧
      IsExactBlas1 id (fun _ => True) I ∧ IsExactMatvec id A I := by
  obtain ⟨I, hS, hA⟩ := exists_isScalar_isExactMatvec (Op := Op) (Tst := Tst) A
  obtain ⟨hS', hB⟩ := (Blas.seq_certifies_exact exactModel_exactMachine
    (fun _ => True)).meets I hS
  have hA' : IsExactMatvec id A (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  exact ⟨_, exactModel_exactMachine, hS', hB, hA'⟩

/-- Choosing sequential BLAS transfers the exact CG state and exposes the scalar operation
counts. The matrix-vector operation uses its exact contract as a primitive. -/
theorem runs_step_seq {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hA : IsExactMatvec dec A I)
    {τ : Tape K} {μ : Mem K} {x r p : ℕ × ℕ} {xs rs ps : List K}
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hl : μ.Live [x, r, p]) (hx : μ.store.readBlock x.1 x.2 n = some xs)
    (hr : μ.store.readBlock r.1 r.2 n = some rs)
    (hp : μ.store.readBlock p.1 p.2 n = some ps)
    (hdom : Nonbreakdown A (decodedState dec n xs rs ps))
    (hz : μ.Room [x, r, p] [n, n, n]) :
    Runs I (Blas.ws 0) τ (step.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n] [x, r, p, x, r, p]) μ (seqStepCount n) (3 * n + 5)
      ((stepRel dec A).Post [n] [xs, rs, ps] [x, r, p] [] μ) := by
  have hcert := Blas.seq_certifies_exact (Op := Op) (Tst := Tst) hM (fun _ => True)
  obtain ⟨hS', hB⟩ := hcert.meets I hS
  have hA' : IsExactMatvec dec A (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  have hrun := runs_step hS' hM hB hA' (Blas.ws 0) (τ := τ) hxr hxp hrp hl hx hr hp hdom hz
  exact (hcert.transfer I τ _ _ _ _ _ _ hrun).mono
    (le_of_eq (push_stepCount_seq n)) (stepPeak_seq_le n) fun _ h => h

/-- Sequential BLAS supplies the complete exact fixed-horizon CG result by generic linking,
with scalar operation counts and the same CG iterate. -/
theorem runs_solve_seq {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hA : IsExactMatvec dec A I) (hPos : A.PosDef)
    {τ : Tape K} {μ : Mem K} {k : ℕ} {b x r p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hl : μ.Live [b, x, r, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hk : k ≤ krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs))
    (hz : μ.Room [x, r, p] [n, n, n]) :
    Runs I (Blas.ws 0) τ (solve.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n, k] [b, x, x, r, p]) μ (seqSolveCount n k) (3 * n + 5)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        decv dec n ys = cgIterate A (decv dec n bs) (decv dec n xs) k) := by
  have hcert := Blas.seq_certifies_exact (Op := Op) (Tst := Tst) hM (fun _ => True)
  obtain ⟨hS', hB⟩ := hcert.meets I hS
  have hA' : IsExactMatvec dec A (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  have hrun := runs_solve hS' hM hB hA' hPos (Blas.ws 0) (τ := τ)
    hbx hbr hbp hxr hxp hrp hl hbs hxs hk hz
  exact (hcert.transfer I τ _ _ _ _ _ _ hrun).mono
    (le_of_eq (push_solveCount_seq n k)) (solvePeak_seq_le n) fun _ h => h

end NLAlib.Krylov.CG.HSCG
