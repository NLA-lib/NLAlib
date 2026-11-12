/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Solve

/-!
# Full standard-model rounded CG with sequential BLAS

The shared scalar implementation table lowers every BLAS call in the complete solver. A
common bound covers scalar division, sequential dot products and rounded axpy updates. Input
spectral precision establishes successful execution; outputs are existing CGRun records tied
to the actual physical vectors and cache, with their accumulated residual-gap bound.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.runs_solve_seq` gives full scalar-program execution.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops
open scoped Matrix

/-- Nonnegative unit roundoff gives nonnegative dot and axpy error factors. -/
theorem seq_errors_nonneg {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    0 ≤ (Blas.seq.err u).dot n ∧ 0 ≤ (Blas.seq.err u).axpy := by
  have hs := Blas.seqSumErr_nonneg hu n
  dsimp only [Blas.seq.err, Blas.level1Err]
  constructor <;> nlinarith

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]
variable [Apart Blas1Op ScalarOp Op] [Apart Blas1Op OperatorOp Op]

/-- The complete linked rounded solver succeeds under input-only spectral precision and
returns its actual existing run and residual-gap bound. The matrix-vector oracle is rounded;
all BLAS calls are implemented through the same rounded scalar machine. -/
theorem runs_solve_seq {M : Machine K} {dec : K → ℝ} {em u e : ℝ}
    {n cap : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hA : IsMatvec dec A (em * specNorm A) I)
    (hCmp : IsCmp dec I) (hAT : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a') (hu : 0 ≤ u)
    (hem : em ≤ e) (hue : u ≤ e) (hde : (Blas.seq.err u).dot n ≤ e)
    (hae : (Blas.seq.err u).axpy ≤ e) (he : e ≤ 1 / 100)
    (hprec : 3 * e * a' ≤ a)
    (hwindow : (cap : ℝ) ^ 2 * Real.sqrt cap * e * (a' / a) ^ 2 ≤
      1 / 10 ^ 5)
    {τ : Tape K} {μ : Mem K} {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs) (hx0 : decv dec n xs = 0)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    ConditionalRuns I (Blas.ws 0) τ (solve.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n, cap] [b, x, x, r, p, v]) μ (seqSolveCount n cap) (2 * n + 4)
      (fun μ' => μ'.pos = μ.pos ∧
        Output dec A (decv dec n bs) e cap x r p v μ') := by
  have hcert := Blas.seq_certifies (Op := Op) (Tst := Tst) hM hu (fun _ => True)
  obtain ⟨hS', hB⟩ := hcert.meets I hS
  have hA' : IsMatvec dec A (em * specNorm A) (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) :=
    Interp.link_meets_kept (Blas.seq_table_kept (Apart.proj_inj OperatorOp.matvec)) hA
  have hCmp' : IsCmp dec (I.link (Blas.seq (Op := Op) (Tst := Tst)).table) := hCmp
  obtain ⟨hd, haa⟩ := seq_errors_nonneg hu n
  have hrun := runs_solve hS' hM hB trivial hA' hCmp' hAT ha hspec hu hd haa hem hue hde hae
    he hprec hwindow (Blas.ws 0) (τ := τ) hbx hbr hbp hbv hxr hxp hxv hrp hrv hpv
    hl hbs hxs hx0 hz
  exact (hcert.transfer I τ _ _ _ _ _ _ hrun).mono
    (le_of_eq (push_solveCount_seq n cap)) (solvePeak_seq_le n) fun _ h => h

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
