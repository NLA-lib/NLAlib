/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Reorth.Update
public import NLAlib.Krylov.CG.Reorth.Direction

/-!
# Exact composition of a reorthogonalized CG round

The prefix, full projection sweep and direction suffix compose by their footprint rules.
Only the ordinary CG denominators must be nonzero. The basis may be rank deficient.

## Main results

* `NLAlib.Krylov.CG.Reorth.round_writes`: total exact execution of one active round.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- One active round terminates and stores the exact reorthogonalized recurrence. -/
theorem round_writes {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec (fun _ => True) I)
    {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsExactMatvec dec A I)
    {τ : Tape K} {μ : Mem K} {x r p Q : ℕ × ℕ} {xs rs ps qs : List K}
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hQx : Q.1 ≠ x.1) (hQr : Q.1 ≠ r.1) (hQp : Q.1 ≠ p.1)
    (hl : μ.Live [x, r, p, Q])
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hrs : μ.store.readBlock r.1 r.2 n = some rs)
    (hps : μ.store.readBlock p.1 p.2 n = some ps)
    (hqs : μ.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hz : μ.Room [x, r, p] [n, n, n])
    (hdom : Nonbreakdown A (HSCG.decodedState dec n xs rs ps)) :
    Writes .total I τ round (Env.frame [n, k] [x, r, p, Q, x, r, p])
      (Fp.blocks [x, r, p] [n, n, n])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ xs' rs' ps',
        μ'.readBlocks [x, r, p] [n, n, n] = some [xs', rs', ps'] ∧
        HSCG.decodedState dec n xs' rs' ps' =
          reorthStep A (column dec n qs) k (HSCG.decodedState dec n xs rs ps)) μ := by
  have hxL := hl x (by simp)
  have hrL := hl r (by simp)
  have hpL := hl p (by simp)
  have hQL := hl Q (by simp)
  simp only [Mem.room_cons, Mem.room_nil, and_true] at hz
  refine writes_allocs (lens := [.var 0, .var 0, .const 4]) (ns := [n, n, 4]) rfl
    fun s₁ hs₁ hlen hBelow => ?_
  have hW : s₁.len μ.store.length = n := by simpa using hlen 0 (by simp)
  have hZ : s₁.len (μ.store.length + 1) = n := by simpa using hlen 1 (by simp)
  have ht : s₁.len (μ.store.length + 2) = 4 := by simpa using hlen 2 (by simp)
  have hs : s₁.length = μ.store.length + 3 := by simpa using hs₁
  dsimp only [Env.frame, List.append, List.range_succ, List.range_zero, List.map,
    List.length_cons, List.length_nil, Nat.add_zero] at *
  refine Writes.seq_le (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true]; omega)
    (update_writes hS hM hB hA hxr hxp hrp hxL hrL hpL hs hW ht
      (by simpa only [(hBelow x.1 hxL).1] using hz.1)
      (by simpa only [(hBelow r.1 hrL).1] using hz.2.1)
      (by kept) (by kept) (by kept) hdom)) (by fp_sub)
    fun μ₁ hfr₁ ⟨hpos₁, xs', raw, rr, hx₁, hr₁, hrr₁, hrrd, hxv, hrv⟩ => ?_
  refine Writes.seq_le (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₁.length_eq]; omega)
    (sweep_writes (qs := qs) (rs := raw) hS hM hB hQr (by
      simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₁.length_eq]; omega)
      (by kept) hr₁ (by
        simp only [Mem.room_cons, Mem.room_nil, and_true, hfr₁.len_eq]
        simpa only [(hBelow r.1 hrL).1] using hz.2.1))) (by fp_sub)
    fun μ₂ hfr₂ ⟨hpos₂, swept, hread₂, hsw⟩ => ?_
  obtain ⟨z, vs, hzv, hrv₂, hvs⟩ := Mem.readBlocks_one hread₂
  have hz_eq : z = r := (List.cons.inj hzv).1.symm
  subst z
  have hvs_eq : vs = swept := (List.cons.inj hvs).1.symm
  subst vs
  refine (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₂.length_eq, hfr₁.length_eq]
    omega)
    (direction_writes (rs := swept) (ps := ps) (rr := rr) hS hM hB hrL hpL
      (by rw [hfr₂.length_eq, hfr₁.length_eq]; exact hs)
      (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hZ)
      (by rw [hfr₂.len_eq, hfr₁.len_eq]; exact ht)
      (by rw [hfr₂.len_eq, hfr₁.len_eq]; simpa only [(hBelow p.1 hpL).1] using hz.2.2)
      hrv₂ (by kept) (by kept) (by rw [hrrd]; exact hdom.1))).mono (by fp_sub) ?_
  rintro μ₃ hfr₃ ⟨hpos₃, ps', hp₃, hpv⟩ s₂ hs₂ hBelow₂
  refine ⟨by simp [hpos₃, hpos₂, hpos₁], xs', swept, ps',
    Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept)
      (Mem.readBlocks_of_cons (by kept) rfl)), ?_⟩
  have hsw' : decv dec n swept =
      sweepVec (column dec n qs) (cgStep A (HSCG.decodedState dec n xs rs ps)).r k := by
    rw [hsw, hrv]
  change CGState.mk (decv dec n xs') (decv dec n swept) (decv dec n ps') = _
  dsimp only [reorthStep]
  rw [← hxv, ← hsw', hpv, hrrd]
  rfl

end NLAlib.Krylov.CG.Reorth
