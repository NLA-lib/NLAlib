/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.FinitePrecision.Initialization

/-!
# Stored rounded CG states and compositional block rules

The state predicate retains the decoded vectors and the actual scalar cache separately.
Their numerical relationship is supplied by the extracted existing CG run, without replacing
the computed cache by a fresh self-dot.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.StoresValues` describes the four stored values.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.initialize_writes` supplies the zero-start state.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.step_writes` supplies its actual local rounded bounds.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]

/-- The three vectors and retained scalar decode to the stated values. -/
def StoresValues (dec : K → ℝ) (n : ℕ) (x r p v : ℕ × ℕ)
    (s : CGState ℝ (Fin n)) (rho : ℝ) (μ : Mem K) : Prop :=
  ∃ xs rs ps rr, μ.readBlocks [x, r, p, v] [n, n, n, 1] = some [xs, rs, ps, [rr]] ∧
    decodedState dec n xs rs ps = s ∧ dec rr = rho

variable [Has Blas1Op Op]

/-- Initialization composes with later rounded blocks, exposing its computed cache error. -/
theorem initialize_writes {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop} {n : ℕ}
    {I : Interp Op Tst K} (hB : IsBlas1 dec ε ok I) (hok : ok n)
    {τ : Tape K} {μ : Mem K} {b x r p v : ℕ × ℕ} {bs xs : List K}
    (hbx : b.1 ≠ x.1) (hbr : b.1 ≠ r.1) (hbp : b.1 ≠ p.1) (hbv : b.1 ≠ v.1)
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [b, x, r, p, v]) (hbs : μ.store.readBlock b.1 b.2 n = some bs)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs) (hx0 : decv dec n xs = 0)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    Writes .total I τ initializeState (Env.frame [n] [b, x, x, r, p, v])
      (Fp.blocks [x, r, p, v] [n, n, n, 1])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ rho,
        StoresValues dec n x r p v ⟨0, decv dec n bs, decv dec n bs⟩ rho μ' ∧
        |rho - decv dec n bs ⬝ᵥ decv dec n bs| ≤
          ε.dot n * ∑ i : Fin n, |decv dec n bs i * decv dec n bs i|) μ := by
  have hread : μ.readBlocks [b, x] [n, n] = some [bs, xs] :=
    Mem.readBlocks_of_cons hbs (Mem.readBlocks_of_cons hxs rfl)
  have hl' : μ.Live ([b, x] ++ [x, r, p, v]) := by
    change μ.Live [b, x, x, r, p, v]
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hl ⊢
    exact ⟨hl.1, hl.2.1, hl.2.1, hl.2.2⟩
  have hpre : (((initializeRel dec (ε.dot n) n).spec (Carried.SolveOperands n)).on
      .total [n] [b, x] [x, r, p, v] τ μ).pre μ :=
    ⟨rfl, ⟨rfl, b, x, r, p, v, rfl, rfl, hbx, hbr, hbp, hbv, hxr, hxp, hxv, hrp, hrv, hpv⟩,
      fun _ => ⟨hl', ⟨[bs, xs], hread, hx0⟩, hz⟩⟩
  refine ((initialize_spec hB hok).writes hpre hl').mono le_rfl ?_
  rintro μ' _ ⟨X, hX, _, ys, hlen, hrel, rfl⟩
  obtain rfl : X = [bs, xs] := Option.some.inj (hX.symm.trans hread)
  obtain ⟨ys, rs, ps, vs, rfl⟩ := List.length_eq_four.mp
    (show ys.length = 4 by simpa using congrArg List.length hlen)
  have hvlen : vs.length = 1 := by
    simpa [initializeRel] using congrArg (fun L => L.getD 3 0) hlen
  obtain ⟨rr, rfl⟩ := List.length_eq_one_iff.mp hvlen
  have hap : Fp.Apart [x, r, p, v] [n, n, n, 1] := by disjoint
  have hout := Mem.readBlocks_updBlocks (m := μ) (ys := [ys, rs, ps, [rr]])
    (by rw [hlen]; exact hap) (by rw [hlen]; exact hz)
  rw [hlen] at hout
  change decodedState dec n ys rs ps = _ ∧ _ at hrel
  have hrvec := congrArg CGState.r hrel.1
  refine ⟨by simp [initializeRel], dec rr,
    ⟨ys, rs, ps, rr, by simpa [initializeRel] using hout, hrel.1, rfl⟩, ?_⟩
  simpa only [show decv dec n rs = decv dec n bs from hrvec] using hrel.2.decoded

variable [Has ScalarOp Op] [Has OperatorOp Op]

/-- A certified active rounded step produces both new stored values and the actual local
recurrence bounds, using explicit computed-denominator margins. -/
theorem step_writes {M : Machine K} {dec : K → ℝ} {u : ℝ} {ε : Blas1Err}
    {ok : ℕ → Prop} {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec ε ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) {τ : Tape K} {μ : Mem K}
    {x r p v : ℕ × ℕ} {s : CGState ℝ (Fin n)} {rho : ℝ}
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [x, r, p, v]) (hs : StoresValues dec n x r p v s rho μ)
    (hed : ε.dot n < 1) (hrne : s.r ≠ 0)
    (hcache : |rho - s.r ⬝ᵥ s.r| ≤ ε.dot n * ∑ i, |s.r i * s.r i|)
    (hmargin : ε.dot n * ∑ i, |s.p i * (A *ᵥ s.p) i| < s.p ⬝ᵥ (A *ᵥ s.p))
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    Writes .total I τ step (Env.frame [n] [x, r, p, v, x, r, p, v])
      (Fp.blocks [x, r, p, v] [n, n, n, 1])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ s' rho', StoresValues dec n x r p v s' rho' μ' ∧
        RoundBounds u (ε.dot n) ε.axpy A s s' rho rho') μ := by
  obtain ⟨xs, rs, ps, rr, hread, hstate, hrho⟩ := hs
  have hrvec : decv dec n rs = s.r := congrArg CGState.r hstate
  have hpvec : decv dec n ps = s.p := congrArg CGState.p hstate
  have hrr : IsDotErr dec (ε.dot n) n (vec rs) (vec rs) rr := by
    simpa only [IsDotErr, dotProduct_decv, decv,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => |dec (vec rs i) * dec (vec rs i)|)] using
      (show |dec rr - decv dec n rs ⬝ᵥ decv dec n rs| ≤ ε.dot n *
        ∑ i : Fin n, |decv dec n rs i * decv dec n rs i| by rwa [hrvec, hrho])
  have hl' := (μ.live_append _ _).mpr ⟨hl, hl⟩
  have hpre : (((stepRel u ε dec A).spec (StepOperands n)).on .total [n]
      [x, r, p, v] [x, r, p, v] τ μ).pre μ :=
    ⟨rfl, ⟨rfl, x, r, p, v, rfl, rfl, hxr, hxp, hxv, hrp, hrv, hpv⟩,
      fun _ => ⟨hl', ⟨[xs, rs, ps, [rr]], hread, hed,
        by rwa [hrvec], hrr, by simpa only [hpvec] using hmargin⟩, hz⟩⟩
  refine ((step_spec hS hM hB hok hA).writes hpre hl').mono le_rfl ?_
  rintro μ' _ ⟨X, hX, _, ys, hlen, hrel, rfl⟩
  obtain rfl : X = [xs, rs, ps, [rr]] := Option.some.inj (hX.symm.trans hread)
  obtain ⟨xs', rs', ps', vs, rfl⟩ := List.length_eq_four.mp
    (show ys.length = 4 by simpa using congrArg List.length hlen)
  have hvlen : vs.length = 1 := by simpa [stepRel] using congrArg (fun L => L.getD 3 0) hlen
  obtain ⟨rr', rfl⟩ := List.length_eq_one_iff.mp hvlen
  have hap : Fp.Apart [x, r, p, v] [n, n, n, 1] := by disjoint
  have hout := Mem.readBlocks_updBlocks (m := μ) (ys := [xs', rs', ps', [rr']])
    (by rw [hlen]; exact hap) (by rw [hlen]; exact hz)
  rw [hlen] at hout
  exact ⟨by simp [stepRel], decodedState dec n xs' rs' ps', dec rr',
    ⟨xs', rs', ps', rr', by simpa [stepRel] using hout, rfl, rfl⟩,
    by simpa only [stepRel_rel, hstate, hrho] using hrel⟩

/-- The actual retained scalar word is readable and decodes to the stored cache value. -/
theorem StoresValues.read_rho {dec : K → ℝ} {n : ℕ} {x r p v : ℕ × ℕ}
    {s : CGState ℝ (Fin n)} {rho : ℝ} {μ : Mem K}
    (h : StoresValues dec n x r p v s rho μ) :
    ∃ rr, μ.store.get v.1 v.2 = some rr ∧ dec rr = rho := by
  obtain ⟨xs, rs, ps, rr, hr, _, he⟩ := h
  obtain ⟨_, _, _, hr₁, hc₁⟩ := Mem.readBlocks_cons_eq_some.mp hr
  rw [← (List.cons.inj hc₁).2] at hr₁
  obtain ⟨_, _, _, hr₂, hc₂⟩ := Mem.readBlocks_cons_eq_some.mp hr₁
  rw [← (List.cons.inj hc₂).2] at hr₂
  obtain ⟨_, _, _, hr₃, hc₃⟩ := Mem.readBlocks_cons_eq_some.mp hr₂
  rw [← (List.cons.inj hc₃).2] at hr₃
  obtain ⟨_, _, hvread, _, hc₄⟩ := Mem.readBlocks_cons_eq_some.mp hr₃
  have hvread' : μ.store.readBlock v.1 v.2 1 = some [rr] :=
    (List.cons.inj hc₄).1.symm ▸ hvread
  exact ⟨rr, by simpa using Store.get_of_readBlock hvread' (j := 0) (by omega) rr, he⟩

/-- The physical iterate and residual are readable as decoded vectors. -/
theorem StoresValues.read_x_r {dec : K → ℝ} {n : ℕ} {x r p v : ℕ × ℕ}
    {s : CGState ℝ (Fin n)} {rho : ℝ} {μ : Mem K}
    (h : StoresValues dec n x r p v s rho μ) :
    ∃ xs rs, μ.store.readBlock x.1 x.2 n = some xs ∧ decv dec n xs = s.x ∧
      μ.store.readBlock r.1 r.2 n = some rs ∧ decv dec n rs = s.r := by
  obtain ⟨xs, rs, ps, rr, hr, he, _⟩ := h
  obtain ⟨_, _, hx, hr₁, hc₁⟩ := Mem.readBlocks_cons_eq_some.mp hr
  have hcx := (List.cons.inj hc₁).1
  rw [← (List.cons.inj hc₁).2] at hr₁
  obtain ⟨_, _, hrs, _, hc₂⟩ := Mem.readBlocks_cons_eq_some.mp hr₁
  exact ⟨xs, rs, hcx.symm ▸ hx, congrArg CGState.x he,
    (List.cons.inj hc₂).1.symm ▸ hrs, congrArg CGState.r he⟩

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
