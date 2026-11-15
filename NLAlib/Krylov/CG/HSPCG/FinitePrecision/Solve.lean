/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Rounds
public import NLAlib.Ops.Logic.Allocation

/-!
# Total capped rounded PCG execution

The copied right-hand side and actual approximate preconditioner establish the initial
state. The scoped stopping cache and capped loop retain an existing numerical PCG prefix.
Spectral and explicit finite-cap precision assumptions justify every division; the cache
is removed before returning the four physical output vectors.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.solve_writes`: total initialized rounded PCG execution.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG.Rounded

open Ops
open scoped Matrix

variable {Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op] [Has CmpTst Tst]

/-- Raw positive spectral windows and an explicit cap-dependent precision window imply total
rounded PCG execution. The output is its actual initialized prefix, with an early stop only
at a zero computed residual. The geometric precision bound is a conservative sufficient
condition, rather than a practical long-cap tolerance. -/
theorem solve_writes {F : Machine ℝ} {em u e : ℝ} {ε : Blas1Err}
    {ok : ℕ → Prop} {n cap : ℕ} {A P : Matrix (Fin n) (Fin n) ℝ}
    {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    (hS : IsScalar F I) (hF : StdModel u id F) (hB : IsBlas1 id ε ok I) (hok : ok n)
    (hA : IsMatvec id A (em * specNorm A) I)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n))
    (hD : I.IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn F) (OutApart (fun _ => True)))
    (hCmp : IsCmp id I) (hAT : Aᵀ = A) (hPT : Pᵀ = P) {a a' p p' : ℝ}
    (ha : 0 < a) (hp : 0 < p)
    (hAs : spectrum ℝ A ⊆ Set.Icc a a') (hPs : spectrum ℝ P ⊆ Set.Icc p p')
    (hu : 0 ≤ u) (hd : 0 ≤ ε.dot n) (haa : 0 ≤ ε.axpy)
    (hem : em ≤ e) (hue : u ≤ e) (hde : ε.dot n ≤ e) (hae : ε.axpy ≤ e)
    (he : e ≤ 1 / 100) (hOe : O.ε ≤ e)
    (hAp : 6 * e * a' ≤ a) (hPp : 6 * e * p' ≤ p)
    (hwindow : e * (1024 * (a' / a) * (p' / p)) ^ (cap + 1) ≤ 1 / 2)
    {τ : Tape ℝ} {μ : Mem ℝ} {b x r z v : ℕ × ℕ} {bs xs : List ℝ}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbz : b.1 ≠ z.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxv : x.1 ≠ v.1)
    (hrz : r.1 ≠ z.1) (hrv : r.1 ≠ v.1) (hzv : z.1 ≠ v.1)
    (hl : μ.Live [b, x, r, z, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs) (hx0 : decv id n xs = 0)
    (hz : μ.Room [x, r, z, v] [n, n, n, n]) :
    Writes .total I τ solve (Env.frame [n, cap] [b, x, x, r, z, v])
      (Fp.blocks [x, r, z, v] [n, n, n, n])
      (fun ν => ν.pos = μ.pos ∧ ∃ m ≤ cap, ∃ s rho,
        StoresState id n x r z v s ν ∧ RunPrefix A P O (decv id n bs) e m s rho ∧
          (m < cap → s.r = 0)) μ := by
  have hlinit : μ.Live [b, x, x, r, z, v] := by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.1, hl.2.2⟩
  refine Writes.seq_le (writes_frame rfl rfl hlinit
    (initialize_oracle_writes hB hok hP hbx hbr hbz hbv hxr hxz hxv hrz hrv hzv
      hl hbs hxs hx0 hz)) le_rfl fun ν hfr ⟨hpos, hinit⟩ => ?_
  have hlvec : ∀ a ∈ [x, r, z, v], a.1 < ν.store.length := by
    intro a ha
    rw [hfr.length_eq]
    exact hl a (by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢; tauto)
  have hzvec : ν.Room [x, r, z, v] [n, n, n, n] := by
    simpa only [Mem.Room, hfr.len_eq] using hz
  refine writes_allocs_preserving_post (lens := [.const 1]) (ns := [1]) rfl ?_ ?_
  · rintro s₁ s₂ q hBelow ⟨hq, m, hm, s, rho, hstate, hprefix, hstop⟩
    exact ⟨hq, m, hm, s, rho, hstate.of_below hBelow hlvec, hprefix, hstop⟩
  · intro s₁ hlen hlens hBelow
    let cache : ℕ × ℕ := (ν.store.length, 0)
    let ν₁ : Mem ℝ := ⟨s₁, ν.pos⟩
    have hclen : s₁.len cache.1 = 1 := by simpa [cache] using hlens 0 (by simp)
    have hcachelive : cache.1 < s₁.length := by
      simp only [cache, hlen, List.length_singleton]
      omega
    have hxl : x.1 < ν.store.length := hlvec x (by simp)
    have hrl : r.1 < ν.store.length := hlvec r (by simp)
    have hzl : z.1 < ν.store.length := hlvec z (by simp)
    have hvl : v.1 < ν.store.length := hlvec v (by simp)
    have hinit' := hinit.of_below (ν := ν₁) hBelow hlvec
    have hz' : ν₁.Room [x, r, z, v] [n, n, n, n] := by
      rw [Mem.room_eq_of_below hBelow hlvec]
      exact hzvec
    have hl' : ν₁.Live [x, r, z, v, cache] := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> dsimp [ν₁, Mem.Live] at * <;> omega
    dsimp only [Env.frame, List.append, List.range_succ, List.range_zero, List.map,
      List.length_cons, List.length_nil, Nat.add_zero]
    have hzcache : cache.2 + 1 ≤ ν₁.store.len cache.1 := by
      change 0 + 1 ≤ s₁.len cache.1
      rw [hclen]
    refine Writes.seq_le
      (cache_writes hB hok hD rfl rfl rfl (by simp; omega)
        (by simp; omega) (by simp; omega) (by simp; omega)
        (fun a ha => hl' a (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢; tauto))
        hinit' (by change 0 < s₁.len cache.1; rw [hclen]; norm_num))
      (Fp.inBlock_le_sup_above (by rfl)) fun ω hfr' ⟨hpos', rho, hstored, hnum, hfn⟩ => ?_
    have hlω : ω.Live [x, r, z, v, cache] := by
      simpa only [Mem.Live, hfr'.length_eq] using hl'
    have hzω : ω.Room [x, r, z, v, cache] [n, n, n, n, 1] := by
      have hz₁ : ν₁.Room [x, r, z, v, cache] [n, n, n, n, 1] := by
        simpa only [Mem.room_cons, Mem.room_nil, and_true] using
          And.intro hz'.1 (And.intro hz'.2.1
            (And.intro hz'.2.2.1 (And.intro hz'.2.2.2.1 hzcache)))
      simpa only [Mem.Room, hfr'.len_eq] using hz₁
    refine (writes_frame rfl rfl ((ω.live_append _ _).mpr ⟨hlω, hlω⟩)
      (rounds_writes hS hF hB hok hA hP hD hCmp hAT hPT ha hAs hp hPs
        hu hd haa hem hue hde hae he hOe hAp hPp hwindow
        hxr hxz hxv (by simp [cache]; omega) hrz hrv (by simp [cache]; omega)
        hzv (by simp [cache]; omega) (by simp [cache]; omega)
        hlω hstored hnum hfn hzω)).mono (by fp_sub) ?_
    rintro ω' _ ⟨hpos'', m, hm, s, rho', hstate, hprefix, hstop⟩
    exact ⟨hpos''.trans (hpos'.trans hpos), m, hm, s, rho', hstate.1, hprefix, hstop⟩

end NLAlib.Krylov.CG.HSPCG.Rounded
