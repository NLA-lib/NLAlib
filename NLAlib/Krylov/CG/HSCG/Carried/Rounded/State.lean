/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Rounded.Initialization

/-!
# Stored rounded CG states and compositional block rules

The state predicate retains the decoded vectors and the actual scalar cache separately.
Their numerical relationship is supplied by the extracted existing CG run, without replacing
the computed cache by a fresh self-dot.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.StoresValues` describes the four stored values.
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

/-- The four blocks `ys` of a state hold the state `s` and, in the cell, `rho`: the claim of
`StoresValues` on blocks rather than on a memory. -/
def HoldsValues (dec : K → ℝ) (n : ℕ) (ys : List (List K)) (s : CGState ℝ (Fin n))
    (rho : ℝ) : Prop :=
  ∃ xs rs ps rr, ys = [xs, rs, ps, [rr]] ∧ decodedState dec n xs rs ps = s ∧ dec rr = rho

/-- A memory stores the values of a state exactly when its four blocks hold them. -/
theorem storesValues_iff {dec : K → ℝ} {n : ℕ} {x r p v : ℕ × ℕ} {s : CGState ℝ (Fin n)}
    {rho : ℝ} {μ : Mem K} :
    StoresValues dec n x r p v s rho μ ↔
      ∃ ys, μ.readBlocks [x, r, p, v] [n, n, n, 1] = some ys ∧ HoldsValues dec n ys s rho := by
  constructor
  · rintro ⟨xs, rs, ps, rr, h, h₁, h₂⟩
    exact ⟨_, h, xs, rs, ps, rr, rfl, h₁, h₂⟩
  · rintro ⟨_, h, xs, rs, ps, rr, rfl, h₁, h₂⟩
    exact ⟨xs, rs, ps, rr, h, h₁, h₂⟩

variable [Has Blas1Op Op]

variable [Has ScalarOp Op] [Has OperatorOp Op]

/-- A certified active rounded step produces both new stored values and the actual local
recurrence bounds, using explicit computed-denominator margins.

The judgment `NLAlib.Krylov.CG.HSCG.Carried.Rounded.stepRoutine_meets` read on the state
predicate `StoresValues` that the loop invariant of `roundsRoutine_meets` carries; the loop rule
applies it to each active round. -/
theorem step_writes {M : Machine K} {dec : K → ℝ} {em u : ℝ} {ε : Blas1Err}
    {ok : ℕ → Prop} {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec ε ok I)
    (hok : ok n) (hA : IsMatvec dec A (em * specNorm A) I) {τ : Tape K} {μ : Mem K}
    {x r p v : ℕ × ℕ} {s : CGState ℝ (Fin n)} {rho : ℝ}
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [x, r, p, v]) (hs : StoresValues dec n x r p v s rho μ)
    (hed : ε.dot n < 1) (hrne : s.r ≠ 0)
    (hcache : |rho - s.r ⬝ᵥ s.r| ≤ ε.dot n * ∑ i, |s.r i * s.r i|)
    (hmargin : ∀ q : Fin n → ℝ,
      ‖WithLp.toLp 2 (A *ᵥ s.p - q)‖ ≤ em * specNorm A * ‖WithLp.toLp 2 s.p‖ →
      ε.dot n * ∑ i, |s.p i * q i| < s.p ⬝ᵥ q)
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    Writes .total I τ step (Env.frame [n] [x, r, p, v, x, r, p, v])
      (Fp.blocks [x, r, p, v] [n, n, n, 1])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ s' rho', StoresValues dec n x r p v s' rho' μ' ∧
        RoundBounds em u (ε.dot n) ε.axpy A s s' rho rho') μ := by
  obtain ⟨xs, rs, ps, rr, hread, hstate, hrho⟩ := hs
  have hrvec : decv dec n rs = s.r := congrArg CGState.r hstate
  have hpvec : decv dec n ps = s.p := congrArg CGState.p hstate
  have hrr : IsDotErr dec (ε.dot n) n (vec rs) (vec rs) rr := by
    simpa only [IsDotErr, dotProduct_decv, decv,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => |dec (vec rs i) * dec (vec rs i)|)] using
      (show |dec rr - decv dec n rs ⬝ᵥ decv dec n rs| ≤ ε.dot n *
        ∑ i : Fin n, |decv dec n rs i * decv dec n rs i| by rwa [hrvec, hrho])
  refine ((stepRoutine_meets hS hM hB hok hA) [n] [x, r, p, v] τ μ _ rfl rfl hl
    (by routine_sep) hread
    ⟨rfl, hed, by rwa [hrvec], hrr, by simpa only [hpvec] using hmargin⟩ hz).mono le_rfl ?_
  rintro μ' - ⟨hpos, ys, hys, hrel⟩
  routine_nf at hys
  split_reads hys as (xs', rs', ps', vs')
  obtain ⟨rr', rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs')
  have hrel : RoundBounds em u (ε.dot n) ε.axpy A (decodedState dec n xs rs ps)
      (decodedState dec n xs' rs' ps') (dec rr) (dec rr') := hrel
  rw [hstate, hrho] at hrel
  exact ⟨hpos, decodedState dec n xs' rs' ps', dec rr',
    ⟨xs', rs', ps', rr', hys, rfl, rfl⟩, hrel⟩

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
