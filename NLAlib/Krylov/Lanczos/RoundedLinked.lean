/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedSolve
public import NLAlib.Krylov.Lanczos.Profiles
public import NLAlib.Ops.Profiles.Standard

/-!
# Complete rounded Lanczos with proved standard BLAS implementations

The selected exact, sequential or pairwise profile lowers all vector calls. Primitive
rounded matvec and exact comparisons are retained. Numerical extraction and early breakdown
transfer together with the profile's scalar/test counts and declared scratch configuration.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.runs_solve_standard`: all named BLAS schemes.
* `NLAlib.Krylov.Lanczos.Rounded.runs_solve_seq`: closed sequential scalar counts.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops
open scoped Matrix

/-- Any named standard BLAS profile implements the full solver, with rounded matvec and an
actual existing run tied to its packed outputs. Pairwise applicability is explicit. -/
theorem runs_solve_standard {K : Type} [Inhabited K] (scheme : Standard.Scheme)
    {M : Machine K} {dec : K → ℝ} {n cap : ℕ} {em u E : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Standard.Operation CmpTst K}
    (hS : IsScalar M I) (hM : StdModel (scheme.roundoff u) dec M) (hu : 0 ≤ u)
    (hok : scheme.admits n) (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
    (hAT : Aᵀ = A) (hprec : Precision em (scheme.roundoff u) E (scheme.errors u) n)
    {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 2 * cap + 2]) :
    ConditionalRuns I scheme.profile.wsLo τ (solve.link scheme.profile.table)
      (Env.frame [n, cap] [B, V, C]) μ
      (Count.push scheme.profile.cost (solveCount n cap)) (solvePeak scheme.profile.ws n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (2 * cap + 2) = some cs ∧
        Output dec A (decv dec n bs) E cap vs cs) := by
  have hc := scheme.certifies hM hu
  obtain ⟨hS', hB⟩ := hc.meets I hS
  have hA' := Interp.link_meets_kept scheme.table_matvec hA
  have hr := runs_solve hS' hM hB hok hA' hCmp hAT hprec scheme.profile.ws
    (τ := τ) hBV hBC hVC hl hb hz
  exact hc.transfer I τ _ _ _ _ _ _ hr

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]
variable [Apart Blas1Op ScalarOp Op] [Apart Blas1Op OperatorOp Op]

/-- The complete sequential scalar solver retains its rounded numerical output and closed
scalar/test budget. The matvec primitive has its own nonzero error allowance. -/
theorem runs_solve_seq {M : Machine K} {dec : K → ℝ} {n cap : ℕ} {em u E : ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hu : 0 ≤ u)
    (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
    (hAT : Aᵀ = A) (hprec : Precision em u E (Blas.seq.err u) n)
    {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 2 * cap + 2]) :
    ConditionalRuns I (Blas.ws 0) τ (solve.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n, cap] [B, V, C]) μ (seqSolveCount n cap) (3 * n + 3)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (2 * cap + 2) = some cs ∧
        Output dec A (decv dec n bs) E cap vs cs) := by
  have hc := Blas.seq_certifies (Op := Op) (Tst := Tst) hM hu (fun _ => True)
  obtain ⟨hS', hB⟩ := hc.meets I hS
  have hA' := Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  have hr := runs_solve hS' hM hB trivial hA' hCmp hAT hprec (Blas.ws 0)
    (τ := τ) hBV hBC hVC hl hb hz
  exact (hc.transfer I τ _ _ _ _ _ _ hr).mono
    (le_of_eq (push_solveCount_seq n cap)) (solvePeak_seq_le n) (fun _ h => h)

end NLAlib.Krylov.Lanczos.Rounded
