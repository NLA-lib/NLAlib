/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Reorth.Exact
public import NLAlib.Ops.Profiles.BlasCert

/-!
# Composing exact residual sweeps

The block certificate gives both a footprint rule for larger programs and a total run with
closed counts and workspace. The existing exact scalar/BLAS witness meets all assumptions
jointly, including at zero dimensions and for rank-deficient bases.

## Main results

* `NLAlib.Krylov.CG.Reorth.sweep_writes`: the compositional footprint interface.
* `NLAlib.Krylov.CG.Reorth.runs_sweep`: total execution and accounting.
* `NLAlib.Krylov.CG.Reorth.exists_models`: a joint exact-real witness.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has Blas1Op Op]

/-- A sweep writes only the residual block and reads back the exact projected vector. -/
theorem sweep_writes {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec (fun _ => True) I)
    {τ : Tape K} {μ : Mem K} {n k : ℕ} {Q r : ℕ × ℕ} {qs rs : List K}
    (hQr : Q.1 ≠ r.1) (hl : μ.Live [Q, r])
    (hqs : μ.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hrs : μ.store.readBlock r.1 r.2 n = some rs) (hz : μ.Room [r] [n]) :
    Writes .total I τ sweep (Env.frame [n, k] [Q, r, r]) (Fp.blocks [r] [n])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ rs', μ'.readBlocks [r] [n] = some [rs'] ∧
        decv dec n rs' = sweepVec (column dec n qs) (decv dec n rs) k) μ := by
  have hl' : μ.Live ([Q, r] ++ [r]) := by
    simp only [List.cons_append, List.nil_append, Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2, hl.2⟩
  have hread : μ.readBlocks [Q, r] [k * n, n] = some [qs, rs] :=
    Mem.readBlocks_of_cons hqs (Mem.readBlocks_of_cons hrs rfl)
  have hpre : (((sweepRel dec).spec SweepOperands).on .total [n, k] [Q, r] [r] τ μ).pre μ :=
    ⟨rfl, ⟨Q, r, rfl, rfl, hQr⟩, fun _ => ⟨hl', ⟨[qs, rs], hread, trivial⟩, hz⟩⟩
  refine ((sweep_spec hS hM hB).writes hpre hl').mono le_rfl ?_
  rintro μ' _ ⟨X, hX, _, Y, hlen, hrel, rfl⟩
  obtain rfl : X = [qs, rs] := Option.some.inj (hX.symm.trans hread)
  obtain ⟨rs', rfl⟩ := List.length_eq_one_iff.mp
    (show Y.length = 1 by simpa using congrArg List.length hlen)
  have hout := Mem.readBlocks_updBlocks (m := μ) (zs := [r]) (ys := [rs'])
    (by rw [hlen]; simp [Fp.Apart]) (by rw [hlen]; exact hz)
  rw [hlen] at hout
  exact ⟨by simp [sweepRel], rs', by simpa [sweepRel] using hout, hrel⟩

/-- The exact sweep terminates for every stored basis, with no rank or nonbreakdown assumption. -/
theorem runs_sweep {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec (fun _ => True) I)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {n k : ℕ}
    {Q r : ℕ × ℕ} {qs rs : List K} (hQr : Q.1 ≠ r.1) (hl : μ.Live [Q, r])
    (hqs : μ.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hrs : μ.store.readBlock r.1 r.2 n = some rs) (hz : μ.Room [r] [n]) :
    Runs I W τ sweep (Env.frame [n, k] [Q, r, r]) μ (sweepCount n k) (sweepPeak W n)
      ((sweepRel dec).Post [n, k] [qs, rs] [r] [] μ) := by
  have hl' : μ.Live ([Q, r] ++ [r]) := by
    simp only [List.cons_append, List.nil_append, Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2, hl.2⟩
  refine ((sweep_spec hS hM hB).runs_rel W (d := [n, k]) (ins := [Q, r]) (outs := [r])
    rfl ⟨Q, r, rfl, rfl, hQr⟩ hl'
    (Mem.readBlocks_of_cons hqs (Mem.readBlocks_of_cons hrs rfl)) trivial hz).mono
      (le_of_eq (staticCost_sweep ..)) (staticPeak_sweep_le ..) ?_
  intro μ' h
  exact h

omit [Inhabited K] [Has ScalarOp Op] [Has Blas1Op Op] in
/-- The exact scalar and BLAS assumptions of the sweep hold jointly over real words. -/
theorem exists_models : ∃ (M : Machine ℝ) (I : Interp (ScalarOp ⊕ Blas1Op) Tst ℝ),
    ExactModel id M ∧ IsScalar M I ∧ IsExactBlas1 id (fun _ => True) I :=
  Blas.exists_isExactBlas1 (fun _ => True)

end NLAlib.Krylov.CG.Reorth
