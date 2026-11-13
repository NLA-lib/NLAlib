/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.SweepExact
public import NLAlib.Krylov.Lanczos.Reorth.TwoPassInterface
public import NLAlib.Ops.Profiles.BlasCert

/-!
# Classical reorthogonalization using sequential BLAS

Both classical passes lower to the existing scalar profile. All primitive charges and scratch
are included, even at dimension zero. Rounded execution is total without a rank assumption.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.runs_cgs2_seq`: total rounded scalar implementation.
* `NLAlib.Krylov.Lanczos.Reorth.exists_inflModels`: genuinely rounded joint model witness.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Apart Blas1Op ScalarOp Op]

/-- Scalar cost of the two coefficient phases and two projection phases. -/
noncomputable def cgs2SeqCount (n k : ℕ) : Count Op Tst :=
  (2 * k) • ((2 * n) • Blas.sc .mul + ((n - 1) + n) • Blas.sc .add +
    (1 - (1 - n)) • Blas.sc .copy + Blas.sc (.lit 0) + Blas.sc .neg)

/-- Every abstract dot, negation and axpy charge lowers to the stated scalar count. -/
theorem push_cgs2Count_seq (n k : ℕ) :
    Count.push (Blas.seq (Op := Op) (Tst := Tst)).cost (cgs2Count n k) =
      cgs2SeqCount n k := by
  simp [cgs2Count, cgsPassCount, cgs2SeqCount, Blas.seq, Profile.over,
    Blas.level1, Blas.level1Cost, Blas.sumSeq, Blas.sumSeqCost]
  module

/-- The coefficient block, one negation cell and dot scratch account for all workspace. -/
theorem cgs2Peak_seq_le (n k : ℕ) :
    cgs2Peak (Blas.ws (Op := Op) 0) n k ≤ k + n + 2 := by
  simp [cgs2Peak, cgsPassPeak, Blas.ws]
  omega

/-- Sequentially implemented dots and updates execute both passes and return actual rounded
error witnesses. Only scalar standard-model assumptions and readable blocks are required. -/
theorem runs_cgs2_seq {M : Machine K} {dec : K → ℝ} {u : ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hu : 0 ≤ u)
    {n k : ℕ} {τ : Tape K} {μ : Mem K} {Q w : ℕ × ℕ} {qs ws : List K}
    (hQw : Q.1 ≠ w.1) (hl : μ.Live [Q, w])
    (hqs : μ.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hws : μ.store.readBlock w.1 w.2 n = some ws) (hz : μ.Room [w] [n]) :
    ConditionalRuns I (Blas.ws 0) τ (cgs2.link (Blas.seq (Op := Op) (Tst := Tst)).table)
      (Env.frame [n, k] [Q, w, w]) μ (cgs2SeqCount n k) (k + n + 2)
      ((twoPassRel dec (Blas.seq.err u).dot (Blas.seq.err u).axpy).Post
        [n, k] [qs, ws] [w] [] μ) := by
  have hcert := Blas.seq_certifies (Op := Op) (Tst := Tst) hM hu (fun _ => True)
  obtain ⟨hS', hB⟩ := hcert.meets I hS
  have hrun := runs_cgs2 hS' hB.dot hB.axpy hM.neg (Blas.ws 0)
    (τ := τ) (qs := qs) (ws := ws) trivial hQw hl hqs hws hz
  exact (hcert.transfer I τ _ _ _ _ _ _ hrun).mono
    (le_of_eq (push_cgs2Count_seq n k)) (cgs2Peak_seq_le n k) fun _ h => h

omit [Inhabited K] [Has ScalarOp Op] [Has Blas1Op Op] [Apart Blas1Op ScalarOp Op] in
/-- Exact scalar and vector contracts coexist over real words at every length. -/
theorem exists_exactModels :
    ∃ (M : Machine ℝ) (I : Interp (ScalarOp ⊕ Blas1Op) Tst ℝ),
      ExactModel id M ∧ IsScalar M I ∧ IsExactBlas1 id (fun _ => True) I :=
  Blas.exists_isExactBlas1 (fun _ => True)

omit [Inhabited K] [Has ScalarOp Op] [Has Blas1Op Op] [Apart Blas1Op ScalarOp Op] in
/-- A nonexact real scalar machine jointly realizes all rounded pass contracts. -/
theorem exists_inflModels (u : ℝ) (hu : 0 < u) :
    ∃ I : Interp (ScalarOp ⊕ Blas1Op) Tst ℝ,
      StdModel u id (inflMachine u) ∧ IsScalar (inflMachine u) I ∧
      IsBlas1 id (Blas.seq.err u) (fun _ => True) I ∧ (inflMachine u).add 1 1 ≠ 2 := by
  let F : ScalarOp ⊕ Blas1Op → BlockFn ℝ := fun o =>
    o.elim (inflMachine u).fn fun _ => .const 0
  have hI : IsScalar (inflMachine u) (Interp.ofFns F : Interp (ScalarOp ⊕ Blas1Op) Tst ℝ) :=
    isScalar_ofFns _ _ fun _ => rfl
  obtain ⟨hS, hB⟩ := (Blas.seq_certifies (Op := ScalarOp ⊕ Blas1Op) (Tst := Tst)
    (stdModel_infl hu.le) hu.le (fun _ => True)).meets _ hI
  refine ⟨_, stdModel_infl hu.le, hS, hB, ?_⟩
  change (1 + 1) * (1 + u) ≠ 2
  intro h
  nlinarith

end NLAlib.Krylov.Lanczos.Reorth
