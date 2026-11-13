/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Reorth.Solve
public import NLAlib.Krylov.CG.HSCG.Linked

/-!
# Full-reorthogonalized CG with sequential BLAS

The exact solver can link every vector operation to the existing sequential scalar profile.
The operator and comparisons remain abstract. All model contracts have a common real witness.

## Main results

* `NLAlib.Krylov.CG.Reorth.runs_solve_seq`: total any-cap execution with scalar counts.
* `NLAlib.Krylov.CG.Reorth.exists_exactContracts`: a joint nonvacuity witness.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]
variable [Apart Blas1Op ScalarOp Op] [Apart Blas1Op OperatorOp Op]

/-- Sequential dot-product counts, including the zero-length literal and optional copy. -/
noncomputable def seqDotCount (n : ℕ) : Count Op Tst :=
  n • Blas.sc .mul + (Blas.sc (.lit 0) +
    ((1 - (1 - n)) • Blas.sc .copy + (n - 1) • Blas.sc .add))

/-- Two dots and the unnormalized projection update, evaluated into scalar operations. -/
noncomputable def seqProjectionCount (n : ℕ) : Count Op Tst :=
  (3 * n) • Blas.sc .mul + (2 * (n - 1) + n) • Blas.sc .add +
    (2 * (1 - (1 - n))) • Blas.sc .copy + 2 • Blas.sc (.lit 0) +
    Blas.sc .div + Blas.sc .neg

/-- Initialization and every guard/active round, plus the triangular projection budget. -/
noncomputable def seqSolveCount (n cap : ℕ) : Count Op Tst :=
  HSCG.seqInitializeCount n + seqDotCount n +
    cap • (Count.test (Has.inj CmpTst.isPos) [] + HSCG.seqStepCount n +
      n • Blas.sc .copy + seqDotCount n) + (cap * (cap + 1) / 2) • seqProjectionCount n

/-- Linking evaluates all abstract BLAS charges into the stated scalar budget. -/
theorem push_solveCount_seq (n cap : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (solveCount n cap) =
      seqSolveCount n cap := by
  simp only [solveCount, map_add, map_nsmul, Count.push_one, Count.push_test,
    HSCG.push_stepCount_seq, HSCG.push_initializeCount_seq, seqSolveCount]
  simp [projectionCount, seqProjectionCount, seqDotCount,
    Blas.seq, Profile.over, Blas.level1, Blas.level1Cost, Blas.sumSeq, Blas.sumSeqCost]
  module

/-- The retained history and guard cell, two work vectors, dot scratch and seven cells suffice. -/
theorem solvePeak_seq_le (n cap : ℕ) :
    solvePeak (Blas.ws (Op := Op) 0) n cap ≤ cap * n + 3 * n + 8 := by
  simp [solvePeak, roundPeak, HSCG.initializePeak, HSCG.stepPeak, Blas.ws]
  omega

omit [Inhabited K] in
/-- Scalar, BLAS, exact operator and decoded comparison assumptions coexist over real words. -/
theorem exists_exactContracts [Apart ScalarOp OperatorOp Op] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ I : Interp Op Tst ℝ, ExactModel id exactMachine ∧ IsScalar exactMachine I ∧
      IsExactBlas1 id (fun _ => True) I ∧ IsExactMatvec id A I ∧ IsCmp id I := by
  obtain ⟨I, hM, hS, hB, hA⟩ := HSCG.exists_exactContracts (Op := Op) (Tst := Tst) A
  let J : Interp Op Tst ℝ := { I with test := fun q d a μ => match Has.proj (G := CmpTst) q with
    | some c => (μ.readBlocks a c.lens).map (c.fn id)
    | none => I.test q d a μ }
  have hCmp : IsCmp id J := by
    intro c d a μ xs hread
    simp only [J, Has.proj_inj, hread, Option.map_some]
  exact ⟨J, hM, hS, ⟨hB.sum, hB.dot, hB.axpy, hB.nrm2, hB.scal, hB.copy⟩, hA, hCmp⟩

/-- Sequential BLAS computes the exact any-cap output, with scalar charges and declared history
storage. The matrix-vector product retains its exact primitive contract. -/
theorem runs_solve_seq {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef) {τ : Tape K} {μ : Mem K}
    {b x r p : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hl : μ.Live [b, x, r, p]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs) (hz : μ.Room [x, r, p] [n, n, n]) :
    ConditionalRuns I (Blas.ws 0) τ (solve.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n, cap] [b, x, x, r, p]) μ (seqSolveCount n cap) (cap * n + 3 * n + 8)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys, μ'.store.readBlock x.1 x.2 n = some ys ∧
        decv dec n ys = cgIterate A (decv dec n bs) (decv dec n xs)
          (min cap (krylovGrade A (decv dec n bs - A *ᵥ decv dec n xs)))) := by
  have hcert := Blas.seq_certifies_exact (Op := Op) (Tst := Tst) hM (fun _ => True)
  obtain ⟨hS', hB⟩ := hcert.meets I hS
  have hA' : IsExactMatvec dec A (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  have hrun := runs_solve hS' hM hB hA' hCmp hPos (Blas.ws 0) (cap := cap) (τ := τ)
    hbx hbr hbp hxr hxp hrp hl hbs hxs hz
  exact (hcert.transfer I τ _ _ _ _ _ _ hrun).mono
    (le_of_eq (push_solveCount_seq n cap)) (solvePeak_seq_le n cap) fun _ h => h

end NLAlib.Krylov.CG.Reorth
