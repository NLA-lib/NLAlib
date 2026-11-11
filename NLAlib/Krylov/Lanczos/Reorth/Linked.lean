/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.Exact
public import NLAlib.Krylov.Lanczos.Profiles
public import NLAlib.Krylov.Lanczos.Reorth.SweepLinked

/-!
# Full reorthogonalized Lanczos with sequential BLAS

The complete exact solver lowers to scalar vector operations while the matrix-vector product
remains an exact oracle. The count charges both classical passes at every capped round and
the additional saved norm. All operation/model assumptions hold in one real interpretation.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.runs_solve_seq`: total scalar-linked Lanczos execution.
* `NLAlib.Krylov.Lanczos.Reorth.exists_exactContracts`: joint real model witness.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]
variable [Apart Blas1Op ScalarOp Op] [Apart Blas1Op OperatorOp Op]

/-- One classical coefficient and its projection update, fully lowered to scalar arithmetic. -/
noncomputable def seqProjectionCount (n : ℕ) : Count Op Tst :=
  Lanczos.seqDotCount n + Blas.sc .neg + n • (Blas.sc .mul + Blas.sc .add)

/-- The ordinary solver, cap extra zero-initialized norm cells, cap raw-norm computations and
the triangular pair of classical passes. -/
noncomputable def seqSolveCount (n cap : ℕ) : Count Op Tst :=
  Lanczos.seqSolveCount n cap + cap • Blas.sc (.lit 0) +
    cap • (Lanczos.seqDotCount n + Count.test (Has.inj CmpTst.isPos) [] + Blas.sc .sqrt) +
    (cap * (cap + 1)) • seqProjectionCount n

/-- Scalar lowering includes every zero literal, reduction, test and projection update. -/
theorem push_solveCount_seq (n cap : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (solveCount n cap) =
      seqSolveCount n cap := by
  have hdecomp : solveCount (Op := Op) (Tst := Tst) n cap =
      Lanczos.solveCount n cap + cap • Blas.sc (.lit 0) + cap • preNormCount n +
        (cap * (cap + 1)) • (Count.one (Has.inj Blas1Op.dot) [n] + Blas.sc .neg +
          Count.one (Has.inj Blas1Op.axpy) [n]) := by
    simp [solveCount, Lanczos.solveCount, Lanczos.zeroCount]
    module
  rw [hdecomp]
  simp only [map_add, map_nsmul, Lanczos.push_solveCount_seq]
  simp [preNormCount, seqSolveCount, seqProjectionCount, Lanczos.seqDotCount,
    Blas.seq, Profile.over, Blas.level1, Blas.level1Cost, Blas.sumSeq, Blas.sumSeqCost]
  module

/-- Two resident work vectors, dot workspace, cap coefficient cells and four scalar cells
bound the linked program's extra scratch. Oracle workspace is the declared retained zero. -/
theorem solvePeak_seq_le (n cap : ℕ) :
    solvePeak (Blas.ws (Op := Op) 0) n cap ≤ 3 * n + cap + 4 := by
  simp [solvePeak, primitivePeak, Blas.ws]
  omega

omit [Inhabited K] in
/-- Exact scalar, vector, operator and comparison contracts coexist over real words. -/
theorem exists_exactContracts [Apart ScalarOp OperatorOp Op] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ I : Interp Op Tst ℝ, ExactModel id exactMachine ∧ IsScalar exactMachine I ∧
      IsExactBlas1 id (fun _ => True) I ∧ IsExactMatvec id A I ∧ IsCmp id I := by
  obtain ⟨I, hS, hA⟩ := exists_isScalar_isExactMatvec (Op := Op) (Tst := Tst) A
  let J : Interp Op Tst ℝ := { I with
    test := fun q d a μ => match Has.proj (G := CmpTst) q with
      | some c => (μ.readBlocks a c.lens).map (c.fn id)
      | none => I.test q d a μ }
  have hCmp : IsCmp id J := by
    intro c d a μ xs hread
    simp only [J, Has.proj_inj, hread, Option.map_some]
  have hSJ : IsScalar exactMachine J := hS
  have hAJ : IsExactMatvec id A J := hA
  have hcert := Blas.seq_certifies_exact (Op := Op) (Tst := Tst)
    exactModel_exactMachine (fun _ => True)
  obtain ⟨hS', hB⟩ := hcert.meets J hSJ
  have hA' : IsExactMatvec id A (J.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hAJ
  exact ⟨_, exactModel_exactMachine, hS', hB, hA', hCmp⟩

/-- Exact scalar and oracle assumptions imply complete arbitrary-cap sequential execution.
The actual returned basis, tridiagonal coefficients and raw norms satisfy the pure recurrence. -/
theorem runs_solve_seq {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hAT : A.IsHermitian)
    {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 3 * cap + 2]) :
    Runs I (Blas.ws 0) τ (solve.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n, cap] [B, V, C]) μ (seqSolveCount n cap) (3 * n + cap + 4)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (3 * cap + 2) = some cs ∧
        Output dec A (decv dec n bs) cap vs cs) := by
  have hcert := Blas.seq_certifies_exact (Op := Op) (Tst := Tst) hM (fun _ => True)
  obtain ⟨hS', hB⟩ := hcert.meets I hS
  have hA' : IsExactMatvec dec A (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  have hr := runs_solve hS' hM hB trivial hA' hCmp hAT (Blas.ws 0)
    (τ := τ) (μ := μ) (cap := cap) (B := B) (V := V) (C := C) (bs := bs)
    hBV hBC hVC hl hb hz
  exact (hcert.transfer I τ _ _ _ _ _ _ hr).mono
    (le_of_eq (push_solveCount_seq n cap)) (solvePeak_seq_le n cap) fun _ h => h

end NLAlib.Krylov.Lanczos.Reorth
