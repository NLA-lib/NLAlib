/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Reorth.Solver
public import NLAlib.Krylov.CG.Reorth.State

/-!
# One active iteration with residual-history storage

The initialized history is extended before the round. Full reorthogonalization then fixes
the exact next residual, and the retained self-product is refreshed for the next guard.

## Main results

* `NLAlib.Krylov.CG.Reorth.advance_writes`: one total active iteration before the grade.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

omit [Has CmpTst Tst] in
/-- Before the grade, saving a residual and taking the reorthogonalized round succeeds. -/
theorem advance_writes {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec (fun _ => True) I)
    {n cap i L : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsExactMatvec dec A I)
    (hPos : A.PosDef) {τ : Tape K} {μ : Mem K} {b x r p : ℕ × ℕ}
    {bs x₀ : Fin n → ℝ} (hi : i < cap)
    (hig : i < krylovGrade A (bs - A *ᵥ x₀))
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hxL : x.1 < L) (hrL : r.1 < L) (hpL : p.1 < L)
    (hl : μ.store.length = L + 2) (hQ : μ.store.len L = cap * n)
    (hv : μ.store.len (L + 1) = 1) (hz : μ.Room [x, r, p] [n, n, n])
    (hs : HSCG.StoresState dec n x r p (cgState A bs x₀ i) μ)
    (hh : StoresHistory dec n (L, 0) (fun j => (cgState A bs x₀ j).r) i μ) :
    Writes .total I τ advance
      ⟨[n, cap, b.2, x.2, x.2, r.2, p.2, i], [b.1, x.1, x.1, r.1, p.1, L, L + 1]⟩
      (Fp.blocks [x, r, p] [n, n, n] ⊔ Fp.above L)
      (fun μ' => μ'.pos = μ.pos ∧
        HSCG.StoresState dec n x r p (cgState A bs x₀ (i + 1)) μ' ∧
        StoresHistory dec n (L, 0) (fun j => (cgState A bs x₀ j).r) (i + 1) μ' ∧
        ∃ rr, μ'.store.get (L + 1) 0 = some rr ∧
          dec rr = (cgState A bs x₀ (i + 1)).r ⬝ᵥ (cgState A bs x₀ (i + 1)).r) μ := by
  obtain ⟨xs, rs, ps, hx, hr, hp, hstate⟩ := state_reads hs
  obtain ⟨qs, hqs, hhistory⟩ := hh
  step hB.copy as μ₁ hfr₁ ⟨hpos₁, saved, hsaved, hcopy⟩
  subst saved
  have hh₁ : StoresHistory dec n (L, 0) (fun j => (cgState A bs x₀ j).r) (i + 1) μ₁ :=
    storesHistory_snoc (qs := qs) (rs := rs) (by kept) (by simpa using hsaved)
      hhistory (congrArg CGState.r hstate)
  obtain ⟨qs₁, hqs₁, hhistory₁⟩ := hh₁
  refine Writes.seq_le (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₁.length_eq]; omega)
    (round_writes (k := i + 1) (xs := xs) (rs := rs) (ps := ps) (qs := qs₁)
      hS hM hB hA hxr hxp hrp (by omega) (by omega) (by omega)
      (by simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₁.length_eq]; omega)
      (by kept) (by kept) (by kept) hqs₁
      (by simpa only [Mem.Room, hfr₁.len_eq] using hz)
      (by rw [hstate]; exact hPos.cgState_nonbreakdown bs x₀ hig))) (by fp_sub)
    fun μ₂ hfr₂ ⟨hpos₂, xs', rs', ps', hread₂, hstate₂⟩ => ?_
  have hs₂ : HSCG.StoresState dec n x r p (cgState A bs x₀ (i + 1)) μ₂ :=
    ⟨xs', rs', ps', hread₂, hstate₂.trans (by
      rw [hstate]; exact reorthStep_eq_cgState_of_history hPos bs x₀ qs₁ hhistory₁)⟩
  obtain ⟨xs₂, rs₂, ps₂, hx₂, hr₂, hp₂, hdecoded₂⟩ := state_reads hs₂
  step hB.dot as μ₃ hfr₃ ⟨hpos₃, rr, hrr, herr⟩
  refine ⟨by simp [hpos₃, hpos₂, hpos₁], ?_, ?_, rr, hrr, ?_⟩
  · exact ⟨xs₂, rs₂, ps₂, Mem.readBlocks_of_cons (by kept)
      (Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl)), hdecoded₂⟩
  · exact ⟨qs₁, by kept, hhistory₁⟩
  · have hrvec : decv dec n rs₂ = (cgState A bs x₀ (i + 1)).r :=
      congrArg CGState.r hdecoded₂
    simpa only [hrvec] using (dotExactRel_decoded (dec := dec) herr)

end NLAlib.Krylov.CG.Reorth
