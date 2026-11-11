/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Exact
public import NLAlib.Krylov.Lanczos.Profiles

/-!
# Total Lanczos with scalar sequential BLAS

The generic profile theorem lowers vector calls to scalar programs while retaining the exact
primitive matrix-vector operation and comparison semantics. Successful output and early
breakdown transfer together with the evaluated scalar count and reused scratch bound.

## Main results

* `NLAlib.Krylov.Lanczos.runs_solve_seq` proves successful linked execution and output.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]
variable [Apart Blas1Op ScalarOp Op] [Apart Blas1Op OperatorOp Op]

/-- Sequential scalar BLAS implements the complete capped Lanczos solver. Its numerical
output, safe early breakdown and total success follow from ordinary input and model assumptions;
the cap affects the budget and output storage but not its scratch bound. -/
theorem runs_solve_seq {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 2 * cap + 2]) :
    ConditionalRuns I (Blas.ws 0) τ (solve.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n, cap] [B, V, C]) μ (seqSolveCount n cap) (3 * n + 3)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (2 * cap + 2) = some cs ∧
        Output dec A (decv dec n bs) cap vs cs) := by
  have hcert := Blas.seq_certifies_exact (Op := Op) (Tst := Tst) hM (fun _ => True)
  obtain ⟨hS', hB⟩ := hcert.meets I hS
  have hA' : IsExactMatvec dec A (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  have hrun := runs_solve hS' hM hB trivial hA' hCmp (Blas.ws 0) (τ := τ)
    hBV hBC hVC hl hb hz
  exact (hcert.transfer I τ _ _ _ _ _ _ hrun).mono
    (le_of_eq (push_solveCount_seq n cap)) (solvePeak_seq_le n) (fun _ h => h)

end NLAlib.Krylov.Lanczos
