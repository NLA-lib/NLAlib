/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSCG.Carried.Alg
public import NLAlib.Krylov.CG.HSCG.Exact

/-!
# Exact CG with a retained residual product

The retained scalar equals the current residual self-product. The certificate proves successful
execution of every operation under exact contracts and nonbreakdown, and preserves this scalar
invariant at the next state. [HestenesStiefel1952, (3:1)].

## Main results

* `NLAlib.Krylov.CG.HSCG.Carried.step_spec` certifies the standard two-dot-product round.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- Four distinct state buffers, updated in place. The fourth block has one scalar cell. -/
@[admNF] def StepOperands (n : ℕ) :
    List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => d = [n] ∧ ∃ x r p v,
    ins = [x, r, p, v] ∧ outs = [x, r, p, v] ∧
      x.1 ≠ r.1 ∧ x.1 ≠ p.1 ∧ x.1 ≠ v.1 ∧
      r.1 ≠ p.1 ∧ r.1 ≠ v.1 ∧ p.1 ≠ v.1

/-- A retained-product round computes the existing exact CG recurrence and retains its new
residual self-product. -/
@[simps (attr := storeNF)]
noncomputable def stepRel (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    BlockRel K where
  nd := 1
  inLens d := [d.headD 0, d.headD 0, d.headD 0, 1]
  outLens d := [d.headD 0, d.headD 0, d.headD 0, 1]
  dom _ X _ := match X with
    | [xs, rs, ps, [v]] => Nonbreakdown A (decodedState dec n xs rs ps) ∧
        dec v = decv dec n rs ⬝ᵥ decv dec n rs
    | _ => False
  rel _ X _ Y := match X, Y with
    | [xs, rs, ps, [_]], [xs', rs', ps', [v']] =>
        decodedState dec n xs' rs' ps' = cgStep A (decodedState dec n xs rs ps) ∧
          dec v' = decv dec n rs' ⬝ᵥ decv dec n rs'
    | _, _ => False

/-- Exact contracts establish total execution of an active round and the retained-product
invariant needed by the next round. -/
theorem step_spec {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I) :
    (stepImpl (Op := Op) (Tst := Tst)).Meets I .total
      ((stepRel dec A).spec (StepOperands n)) := by
  cert_intro [m] (x, r, p, v) → (x', r', p', v') reads (xs, rs, ps, vs)
  obtain ⟨hd, hx, hr, hp, hv, hxr, hxp, hxv, hrp, hrv, hpv⟩ := hadm
  subst m x' r' p' v'
  obtain ⟨rr, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs)
  change Nonbreakdown A (decodedState dec n xs rs ps) ∧
    dec rr = decv dec n rs ⬝ᵥ decv dec n rs at hdom
  have hrr : μ.store.get v.1 v.2 = some rr := by
    simpa using Store.get_of_readBlock hvs (j := 0) (by omega) rr
  refine writes_allocs (lens := [.var 0, .var 0, .const 3]) (ns := [n, n, 3]) rfl
    fun s₁ hs₁ hlen hB₁ => ?_
  have hq : s₁.len μ.store.length = n := by simpa using hlen 0 (by simp)
  have hz : s₁.len (μ.store.length + 1) = n := by simpa using hlen 1 (by simp)
  have ht : s₁.len (μ.store.length + 2) = 3 := by simpa using hlen 2 (by simp)
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
  have hpqd := dotExactRel_decoded (dec := dec) (n := n) hepq
  have hrrd' := dotExactRel_decoded (dec := dec) (n := n) herr'
  have hrr0 : dec rr ≠ 0 := by rw [hdom.2]; exact hdom.1.1
  have hpq0 : dec pq ≠ 0 := by rw [hpqd, heq]; exact hdom.1.2
  have had : dec a = (decv dec n rs ⬝ᵥ decv dec n rs) /
      (decv dec n ps ⬝ᵥ (A *ᵥ decv dec n ps)) := by
    rw [← hea, hM.div rr pq hpq0, hdom.2, hpqd, heq]
  have hbd : dec b = (decv dec n zs ⬝ᵥ decv dec n zs) /
      (decv dec n rs ⬝ᵥ decv dec n rs) := by
    rw [← heb, hM.div rr' rr hrr0, hrrd', hdom.2]
  have hnad : dec na = -dec a := hena ▸ hM.neg a
  have hrvec : decv dec n zs = decv dec n rs - dec a • (A *ᵥ decv dec n ps) := by
    simpa [heq, hnad, sub_eq_add_neg, neg_smul] using
      (axpyExactRel_decoded (dec := dec) (n := n) her)
  have hstep := HSCG.decodedState_step A xs rs ps xs' zs ps'' (dec a) (dec b) had hbd
    (axpyExactRel_decoded hex) hrvec (axpyExactRel_decoded hep)
  intro s₂ hs₂ hB₂
  refine ⟨by simp [stepRel, hpos₁₂, hpos₁₁, hpos₁₀, hpos₉, hpos₈, hpos₇, hpos₆,
    hpos₅, hpos₄, hpos₃, hpos₂, hpos₁], [xs', zs, ps'', [rr']], ?_, hstep, hrrd'⟩
  exact Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept)
    (Mem.readBlocks_of_cons (by kept) (Mem.readBlocks_of_cons (by kept) rfl)))

end NLAlib.Krylov.CG.HSCG.Carried
