/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Initialization
public import NLAlib.Krylov.CG.HSCG.Carried.State

/-!
# Initializing exact CG with its retained residual product

The existing residual initializer composes with one certified self-product. No positive
residual is assumed, so an initially solved system initializes a zero retained product and
can exit the subsequent loop without any division.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.initialize_writes` establishes the four-block state.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- Exact initialization establishes the retained-product state from ordinary input blocks. -/
theorem initialize_writes {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I)
    {τ : Tape K} {μ : Mem K} {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    Writes .total I τ initializeState (Env.frame [n] [b, x, x, r, p, v])
      (Fp.blocks [x, r, p, v] [n, n, n, 1])
      (fun μ' => μ'.pos = μ.pos ∧ StoresState dec n x r p v
        (cgState A (decv dec n bs) (decv dec n xs) 0) μ' ∧
        μ'.store.readBlock b.1 b.2 n = some bs) μ := by
  have hl₀ : μ.Live [b, x, r, p] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1⟩
  have hl₁ : μ.Live [b, x, x, r, p] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl₀ ⊢
    exact ⟨hl₀.1, hl₀.2.1, hl₀.2.1, hl₀.2.2⟩
  have hz₀ : μ.Room [x, r, p] [n, n, n] := by
    simp only [Mem.room_cons, Mem.room_nil, and_true] at hz ⊢
    exact ⟨hz.1, hz.2.1, hz.2.2.1⟩
  refine Writes.seq_le (writes_frame rfl rfl hl₁
    (HSCG.initialize_writes hS hM hB hA hbx hbr hbp hxr hxp hrp hl₀ hbs hxs hz₀))
    (by fp_sub) fun μ₁ hfr ⟨hpos, hstate⟩ => ?_
  obtain ⟨ys, rs, ps, hread, he⟩ := hstate
  obtain ⟨ys₁, X₁, hys, hr₁, hc₁⟩ := Mem.readBlocks_cons_eq_some.mp hread
  obtain ⟨rfl, rfl⟩ := List.cons.inj hc₁
  obtain ⟨rs₁, X₂, hrs, hr₂, hc₂⟩ := Mem.readBlocks_cons_eq_some.mp hr₁
  obtain ⟨rfl, rfl⟩ := List.cons.inj hc₂
  obtain ⟨ps₁, _, hps, _, hc₃⟩ := Mem.readBlocks_cons_eq_some.mp hr₂
  obtain ⟨rfl, _⟩ := List.cons.inj hc₃
  have hl₂ : μ₁.Live [r, r, v] := by
    have hll : μ₁.Live [b, x, r, p, v] := by
      simpa only [Mem.Live, hfr.length_eq] using hl
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hll ⊢
    exact ⟨hll.2.2.1, hll.2.2.1, hll.2.2.2.2⟩
  have hzv : v.2 < μ₁.store.len v.1 := by
    have hzz : μ₁.Room [x, r, p, v] [n, n, n, 1] := by
      simpa [Mem.Room, hfr.len_eq] using hz
    simp only [Mem.room_cons, Mem.room_nil, and_true] at hzz
    have hv := hzz.2.2.2
    omega
  step hB.dot as μ₂ hfr₂ ⟨hpos₂, rr, hrr, herr⟩
  refine (Writes.skip ?_).mono bot_le (fun _ _ h => h)
  refine ⟨hpos₂.trans hpos, ?_, by kept⟩
  refine ⟨ys, rs, ps, rr, ?_, he, dotExactRel_decoded herr⟩
  exact Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept)
    (Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl)))

end NLAlib.Krylov.CG.HSCG.Carried
