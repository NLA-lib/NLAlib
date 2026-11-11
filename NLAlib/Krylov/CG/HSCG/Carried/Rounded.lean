/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Exact

/-!
# A standard-model CG round with its computed residual product

This slice uses an exact matrix-vector operator and rounded scalar and BLAS1 contracts. Its
input error and curvature margins guarantee positive computed divisors and successful total
execution. The result records the standard local recurrence bounds, including the retained
self-product for the next round. No success premise is assumed.

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.RoundBounds` describes the numerical recurrence.
* `NLAlib.Krylov.CG.HSCG.Carried.Rounded.step_spec` proves successful execution and these bounds.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried.Rounded

open Ops
open scoped Matrix

/-- The standard local CG recurrence with separately bounded dot products, divisions and
componentwise vector updates. The matrix-vector product is exact in this slice. -/
def RoundBounds {n : ℕ} (u ed ea : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (s s' : CGState ℝ (Fin n)) (rho rho' : ℝ) : Prop :=
  ∃ curvature alpha beta : ℝ, 0 < rho ∧ 0 < curvature ∧
    |curvature - s.p ⬝ᵥ (A *ᵥ s.p)| ≤ ed * ∑ i : Fin n, |s.p i * (A *ᵥ s.p) i| ∧
    |alpha - rho / curvature| ≤ u * |rho / curvature| ∧
    (∀ i, |s'.x i - (s.x i + alpha * s.p i)| ≤ ea * (|s.x i| + |alpha * s.p i|)) ∧
    (∀ i, |s'.r i - (s.r i - alpha * (A *ᵥ s.p) i)| ≤
      ea * (|s.r i| + |alpha * (A *ᵥ s.p) i|)) ∧
    |rho' - s'.r ⬝ᵥ s'.r| ≤ ed * ∑ i : Fin n, |s'.r i * s'.r i| ∧
    |beta - rho' / rho| ≤ u * |rho' / rho| ∧
    (∀ i, |s'.p i - (s'.r i + beta * s.p i)| ≤ ea * (|s'.r i| + |beta * s.p i|))

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- The input residual-product error and curvature margin suffice for both computed division
arguments to be positive. The output retains its newly computed residual product. -/
@[simps (attr := storeNF)]
noncomputable def stepRel (u : ℝ) (ε : Blas1Err) (dec : K → ℝ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0, d.headD 0, d.headD 0, 1]
  outLens d := [d.headD 0, d.headD 0, d.headD 0, 1]
  dom _ X _ := match X with
    | [_, rs, ps, [v]] => ε.dot n < 1 ∧ decv dec n rs ≠ 0 ∧
        IsDotErr dec (ε.dot n) n (vec rs) (vec rs) v ∧
        ε.dot n * ∑ i : Fin n, |decv dec n ps i * (A *ᵥ decv dec n ps) i| <
          decv dec n ps ⬝ᵥ (A *ᵥ decv dec n ps)
    | _ => False
  rel _ X _ Y := match X, Y with
    | [xs, rs, ps, [v]], [xs', rs', ps', [v']] =>
        RoundBounds u (ε.dot n) ε.axpy A (decodedState dec n xs rs ps)
          (decodedState dec n xs' rs' ps') (dec v) (dec v')
    | _, _ => False

/-- Input/model assumptions establish total successful execution and standard local CG error
bounds. The curvature margin is stated on the decoded input direction and exact operator. -/
theorem step_spec {M : Machine K} {dec : K → ℝ} {n : ℕ} {u : ℝ} {ε : Blas1Err}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M)
    (hB : IsBlas1 dec ε ok I) (hok : ok n) (hA : IsExactMatvec dec A I) :
    (stepImpl (Op := Op) (Tst := Tst)).Meets I .total
      ((stepRel u ε dec A).spec (StepOperands n)) := by
  cert_intro [m] (x, r, p, v) → (x', r', p', v') reads (xs, rs, ps, vs)
  obtain ⟨hd, hx, hr, hp, hv, hxr, hxp, hxv, hrp, hrv, hpv⟩ := hadm
  subst m x' r' p' v'
  obtain ⟨rr, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs)
  change ε.dot n < 1 ∧ decv dec n rs ≠ 0 ∧
    IsDotErr dec (ε.dot n) n (vec rs) (vec rs) rr ∧ _ at hdom
  have hrr : μ.store.get v.1 v.2 = some rr := by
    simpa using Store.get_of_readBlock hvs (j := 0) (by omega) rr
  refine writes_allocs (lens := [.var 0, .const 3]) (ns := [n, 3]) rfl
    fun s₁ hs₁ hlen hB₁ => ?_
  have hq : s₁.len μ.store.length = n := by simpa using hlen 0 (by simp)
  have ht : s₁.len (μ.store.length + 1) = 3 := by simpa using hlen 1 (by simp)
  dsimp only [Env.frame, List.append, List.range_succ, List.range_zero, List.map,
    List.length_cons, List.length_nil, Nat.add_zero] at *
  step hA as m₁ hfr₁ ⟨hpos₁, qs, hqs, heq⟩
  step hB.dot as m₂ hfr₂ ⟨hpos₂, pq, hpq, hepq⟩
  step (hS .div) as m₃ hfr₃ ⟨hpos₃, a, ha, hea⟩
  step hB.axpy as m₄ hfr₄ ⟨hpos₄, xs', hxs', hex⟩
  step (hS .neg) as m₅ hfr₅ ⟨hpos₅, na, hna, hena⟩
  step hB.axpy as m₆ hfr₆ ⟨hpos₆, rs', hrs', her⟩
  step hB.dot as m₇ hfr₇ ⟨hpos₇, rr', hrr', herr'⟩
  have hx₇ : m₇.store.readBlock x.1 x.2 n = some xs' := by kept
  have hr₇ : m₇.store.readBlock r.1 r.2 n = some rs' := by kept
  have hp₇ : m₇.store.readBlock p.1 p.2 n = some ps := by kept
  have hv₇ : m₇.store.get v.1 v.2 = some rr := by kept
  clear hfr₁ hfr₂ hfr₃ hfr₄ hfr₅ hfr₆
  step (hS .div) as m₈ hfr₈ ⟨hpos₈, b, hb, heb⟩
  step hB.copy as m₉ hfr₉ ⟨hpos₉, zs, hzs, rfl⟩
  step hB.axpy as m₁₀ hfr₁₀ ⟨hpos₁₀, ps', hps', hep⟩
  step hB.copy as m₁₁ hfr₁₁ ⟨hpos₁₁, ps'', hps'', rfl⟩
  step (hS .copy) as m₁₂ hfr₁₂ ⟨hpos₁₂, rr'', hrr'', rfl⟩
  have hrrpos : 0 < dec rr := hdom.2.2.1.self_pos_of_ne_zero hdom.1 hdom.2.1
  have hpqpos : 0 < dec pq := hepq.pos_of_margin (by simpa only [heq] using hdom.2.2.2)
  have halpha := hea ▸ hM.div rr pq hpqpos.ne'
  have hbeta := heb ▸ hM.div rr' rr hrrpos.ne'
  have hnad : dec na = -dec a := hena ▸ hM.neg a
  have hcurv := hepq.decoded
  rw [heq] at hcurv
  have hrvec (i : Fin n) := her.decoded i
  simp only [hnad, heq, neg_mul, ← sub_eq_add_neg, abs_neg] at hrvec
  intro s₂ hs₂ hB₂
  refine ⟨by simp [stepRel, hpos₁₂, hpos₁₁, hpos₁₀, hpos₉, hpos₈, hpos₇, hpos₆,
    hpos₅, hpos₄, hpos₃, hpos₂, hpos₁], [xs', zs, ps'', [rr']], ?_, ?_⟩
  · exact Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept)
      (Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl)))
  · exact ⟨dec pq, dec a, dec b, hrrpos, hpqpos, hcurv, halpha,
      hex.decoded, hrvec, herr'.decoded, hbeta, hep.decoded⟩

/-- Readable input state and explicit input error margins imply a successful rounded CG
round, its local numerical bounds and the evaluator-derived operation/workspace budget. -/
theorem runs_step {M : Machine K} {dec : K → ℝ} {n : ℕ} {u : ℝ} {ε : Blas1Err}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M)
    (hB : IsBlas1 dec ε ok I) (hok : ok n) (hA : IsExactMatvec dec A I)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {x r p v : ℕ × ℕ}
    {xs rs ps : List K} {rr : K}
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hxv : x.1 ≠ v.1)
    (hrp : r.1 ≠ p.1) (hrv : r.1 ≠ v.1) (hpv : p.1 ≠ v.1)
    (hl : μ.Live [x, r, p, v])
    (hx : μ.store.readBlock x.1 x.2 n = some xs)
    (hr : μ.store.readBlock r.1 r.2 n = some rs)
    (hp : μ.store.readBlock p.1 p.2 n = some ps) (hv : μ.store.get v.1 v.2 = some rr)
    (hed : ε.dot n < 1) (hrne : decv dec n rs ≠ 0)
    (hrr : |dec rr - decv dec n rs ⬝ᵥ decv dec n rs| ≤
      ε.dot n * ∑ i : Fin n, |decv dec n rs i * decv dec n rs i|)
    (hmargin : ε.dot n * ∑ i : Fin n, |decv dec n ps i * (A *ᵥ decv dec n ps) i| <
      decv dec n ps ⬝ᵥ (A *ᵥ decv dec n ps))
    (hz : μ.Room [x, r, p, v] [n, n, n, 1]) :
    Runs I W τ step (Env.frame [n] [x, r, p, v, x, r, p, v]) μ (stepCount n) (stepPeak W n)
      ((stepRel u ε dec A).Post [n] [xs, rs, ps, [rr]] [x, r, p, v] [] μ) := by
  have hrr' : IsDotErr dec (ε.dot n) n (vec rs) (vec rs) rr := by
    simpa only [IsDotErr, dotProduct_decv, decv,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => |dec (vec rs i) * dec (vec rs i)|)] using hrr
  refine ((step_spec hS hM hB hok hA).runs_rel W (τ := τ) (d := [n])
    (ins := [x, r, p, v]) (outs := [x, r, p, v]) (xs := [xs, rs, ps, [rr]]) rfl
    ⟨rfl, x, r, p, v, rfl, rfl, hxr, hxp, hxv, hrp, hrv, hpv⟩
    ((μ.live_append _ _).mpr ⟨hl, hl⟩)
    (Mem.readBlocks_of_cons hx (Mem.readBlocks_of_cons hr (Mem.readBlocks_of_cons hp
      (Mem.readBlocks_of_cons (Store.readBlock_one_of_get hv) rfl))))
    ⟨hed, hrne, hrr', hmargin⟩ hz).mono
      (le_of_eq (staticCost_step ..)) (staticPeak_step_le ..) ?_
  intro μ' hpost
  exact hpost

end NLAlib.Krylov.CG.HSCG.Carried.Rounded
