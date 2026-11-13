/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Alg
public import NLAlib.Krylov.CG.HSPCG.FinitePrecision.Step
public import NLAlib.Ops.Logic.Allocation

/-!
# Stored rounded PCG states with a stopping cache

The four vectors keep the existing decoded PCG state representation. A separate scalar
stores the actual stopping pairing. Disjoint writes preserve the vectors through the shared
block-read frame rule; no unfolded execution equation enters the invariant.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.StoresCached` records the state and readable cache.
* `NLAlib.Krylov.CG.HSPCG.StoresState.of_eqOff` transports a state through disjoint writes.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSPCG

open Ops
open scoped Matrix

/-- A stored PCG state survives writes disjoint from its four vector blocks. -/
theorem StoresState.of_eqOff {K : Type} [Inhabited K] {dec : K → ℝ} {n : ℕ}
    {x r z p : ℕ × ℕ} {s : PCGState ℝ (Fin n)} {μ ν : Mem K} {F : Fp}
    (h : StoresState dec n x r z p s μ) (hfr : μ.store.EqOff F ν.store)
    (hdis : Fp.Disj F (Fp.blocks [x, r, z, p] [n, n, n, n])) :
    StoresState dec n x r z p s ν := by
  obtain ⟨xs, rs, zs, ps, hr, hs⟩ := h
  exact ⟨xs, rs, zs, ps, Mem.readBlocks_of_eqOff hfr hdis hr, hs⟩

/-- A stored state in surviving handles is preserved when scoped scratch is removed. -/
theorem StoresState.of_below {K : Type} [Inhabited K] {dec : K → ℝ} {n L : ℕ}
    {x r z p : ℕ × ℕ} {s : PCGState ℝ (Fin n)} {μ ν : Mem K}
    (h : StoresState dec n x r z p s μ) (hb : Store.Below L μ.store ν.store)
    (hl : ∀ a ∈ [x, r, z, p], a.1 < L) : StoresState dec n x r z p s ν := by
  obtain ⟨xs, rs, zs, ps, hr, hs⟩ := h
  refine ⟨xs, rs, zs, ps, ?_, hs⟩
  exact hb.keep (Store.readsOnly_readBlocks [x, r, z, p] [n, n, n, n]
    [xs, rs, zs, ps] μ.pos) (fun b i hi => by
      by_contra h
      exact (Fp.blocks_disj_above hl) b i hi (Nat.le_of_not_gt h)) hr

/-- The residual and its preconditioned value are readable as their unique real-word lists. -/
theorem StoresState.read_r_z {n : ℕ} {x r z p : ℕ × ℕ}
    {s : PCGState ℝ (Fin n)} {μ : Mem ℝ} (h : StoresState id n x r z p s μ) :
    μ.readBlocks [r, z] [n, n] = some [List.ofFn s.r, List.ofFn s.z] := by
  obtain ⟨xs, rs, zs, ps, hr, hs⟩ := h
  have hlens := Mem.map_length_of_readBlocks hr
  have hlr : rs.length = n := by simpa using congrArg (fun ls => ls.getD 1 0) hlens
  have hlz : zs.length = n := by simpa using congrArg (fun ls => ls.getD 2 0) hlens
  have hrvec : decv id n rs = s.r := congrArg PCGState.r hs
  have hzvec : decv id n zs = s.z := congrArg PCGState.z hs
  have hrs : List.ofFn s.r = rs := by rw [← hrvec]; exact ofFn_decv hlr
  have hzs : List.ofFn s.z = zs := by rw [← hzvec]; exact ofFn_decv hlz
  rw [hrs, hzs]
  simp only [Mem.readBlocks_cons_iff] at hr ⊢
  exact ⟨hr.2.1, hr.2.2.1, rfl⟩

namespace Rounded

/-- The four actual vector blocks and the actual scalar used by the stopping query. The
functional dot law, rather than this representation predicate, identifies the cache value. -/
def StoresCached (n : ℕ) (x r z p v : ℕ × ℕ) (s : PCGState ℝ (Fin n))
    (rho : ℝ) (μ : Mem ℝ) : Prop :=
  StoresState id n x r z p s μ ∧ μ.store.get v.1 v.2 = some rho

variable {Op Tst : Type} [Has Blas1Op Op]

/-- Refresh the stopping cache with the actual functional rounded dot. The four vectors
are preserved, and both the numerical bound and deterministic computed word are retained. -/
theorem cache_writes {F : Machine ℝ} {ε : Blas1Err} {ok : ℕ → Prop} {n : ℕ}
    {I : Interp Op Tst ℝ} (hB : IsBlas1 id ε ok I) (hok : ok n)
    (hD : I.IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn F) (OutApart (fun _ => True)))
    {τ : Tape ℝ} {μ : Mem ℝ} {ρ : Env} {ds : List IExp} {ins outs : List Operand}
    {x r z p v : ℕ × ℕ} {s : PCGState ℝ (Fin n)}
    (hd : IExp.evalList ρ.idx ds = some [n])
    (hi : Operand.evalList ρ ins = some [r, z])
    (ho : Operand.evalList ρ outs = some [v])
    (hxv : x.1 ≠ v.1) (hrv : r.1 ≠ v.1) (hzv : z.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [r, z, v]) (hs : StoresState id n x r z p s μ)
    (hv : v.2 < μ.store.len v.1) :
    Writes .total I τ (.call (Has.inj Blas1Op.dot) ds ins outs) ρ
      (Store.inBlock v.1 v.2 1)
      (fun ν => ν.pos = μ.pos ∧ ∃ rho, StoresCached n x r z p v s rho ν ∧
        |rho - s.r ⬝ᵥ s.z| ≤ ε.dot n * ∑ i, |s.r i * s.z i| ∧
        rho = pairingValue F s.r s.z) μ := by
  have hread := hs.read_r_z
  refine (writes_call_cell (dot_function_meets hB.dot hD) hd hi ho rfl rfl rfl
    ⟨hok, fun a ha b hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      subst b
      rcases ha with rfl | rfl
      · exact hrv
      · exact hzv⟩
    (fun _ => ⟨hl, ⟨_, hread, trivial⟩, hv⟩)).mono le_rfl ?_
  rintro ν hfr ⟨hpos, X, rho, hX, hget, hnum, hfn⟩
  have hXeq : X = [List.ofFn s.r, List.ofFn s.z] := Option.some.inj (hX.symm.trans hread)
  subst X
  refine ⟨by simpa using hpos, rho, ⟨hs.of_eqOff hfr (by disjoint), hget⟩, ?_, ?_⟩
  · change IsDotErr id (ε.dot n) n (vec (List.ofFn s.r))
      (vec (List.ofFn s.z)) rho at hnum
    simpa only [decv_ofFn, id_eq] using hnum.decoded
  · change rho = pairingValue F (decv id n (List.ofFn s.r))
      (decv id n (List.ofFn s.z)) at hfn
    simpa only [decv_ofFn] using hfn

variable [Has ScalarOp Op] [Has OperatorOp Op]
  [Has (Tagged Preconditioner OperatorOp) Op]

/-- The existing step and the refreshed stopping cache have the same adjacent computed
pairings. Both divisions are justified by the mathematical active-step margins. -/
theorem guardedStep_writes {F : Machine ℝ} {n : ℕ} {em u : ℝ} {ε : Blas1Err}
    {A P : Matrix (Fin n) (Fin n) ℝ} {O : MatvecOracle P} {I : Interp Op Tst ℝ}
    {ok : ℕ → Prop} (hS : IsScalar F I) (hF : StdModel u id F)
    (hB : IsBlas1 id ε ok I) (hok : ok n) (hA : IsMatvec id A (em * specNorm A) I)
    (hP : I.IsFn .total (Tagged.inj Preconditioner OperatorOp.matvec)
      (matvecFn O.mulVec) (MatvecOperands n n))
    (hD : I.IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn F) (OutApart (fun _ => True)))
    {τ : Tape ℝ} {μ : Mem ℝ} {x r z p v : ℕ × ℕ}
    {s : PCGState ℝ (Fin n)} {rho : ℝ}
    (hxr : x.1 ≠ r.1) (hxz : x.1 ≠ z.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrz : r.1 ≠ z.1) (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1)
    (hzp : z.1 ≠ p.1) (hzv : z.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [x, r, z, p, v]) (hs : StoresCached n x r z p v s rho μ)
    (hcache : rho = pairingValue F s.r s.z)
    (hdom : Margins em (ε.dot n) A s)
    (hz : μ.Room [x, r, z, p, v] [n, n, n, n, 1]) :
    Writes .total I τ guardedStep (Env.frame [n] [x, r, z, p, v, x, r, z, p, v])
      (Fp.blocks [x, r, z, p, v] [n, n, n, n, 1])
      (fun ν => ν.pos = μ.pos ∧ ∃ next rho', StoresCached n x r z p v next rho' ν ∧
        RoundBounds em u (ε.dot n) ε.axpy A O s next rho rho' ∧
        rho' = pairingValue F next.r next.z) μ := by
  have hlvec : μ.Live [x, r, z, p] := fun a ha => hl a (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    tauto)
  have hzvec : μ.Room [x, r, z, p] [n, n, n, n] := by
    simpa only [Mem.room_cons, Mem.room_nil, and_true] using
      And.intro hz.1 (And.intro hz.2.1 (And.intro hz.2.2.1 hz.2.2.2.1))
  change Writes .total I τ (.seq _ _) _ _ _ μ
  refine Writes.seq_le (writes_frame rfl rfl
    ((μ.live_append _ _).mpr ⟨hlvec, hlvec⟩)
    (step_writes_function hS hF hB hok hA hP hD
      hxr hxz hxp hrz hrp hzp hlvec hs.1 hdom hzvec)) (by fp_sub)
    fun ν hfr ⟨hpos, next, ri, ro, hnext, hb, hri, hro⟩ => ?_
  have hri' : ri = rho := hri.trans hcache.symm
  have hl' : ν.Live [r, z, v] := by
    simp only [Mem.Live, hfr.length_eq]
    intro a ha
    apply hl a
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    tauto
  have hv : v.2 < ν.store.len v.1 := by
    rw [hfr.len_eq]
    have hv := hz.2.2.2.2.1
    omega
  refine Writes.seq_le (cache_writes hB hok hD rfl rfl rfl hxv hrv hzv hpv hl' hnext hv)
    (by fp_sub) fun ω _ ⟨hpos', ru, hstored, _, hru⟩ => ?_
  have hru' : ru = ro := hru.trans hro.symm
  rw [hri'] at hb
  rw [hru'] at hstored
  exact wp_skip ⟨Store.EqOff.refl _ _, hpos'.trans hpos, next, ro, hstored, hb, hro⟩

end Rounded
end NLAlib.Krylov.CG.HSPCG
