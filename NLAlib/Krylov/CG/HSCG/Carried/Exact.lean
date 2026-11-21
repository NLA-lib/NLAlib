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

* `NLAlib.Krylov.CG.HSCG.Carried.stepRoutine_meets` certifies the standard two-dot-product round.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.HSCG.Carried

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- At the dimension of the matrix, a nonbreaking state with its retained residual product is
advanced by one round of the recurrence, and the new residual product is retained. -/
noncomputable def stepSpec (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Routine.Spec K :=
  spec% [m] (xs, rs, ps, [v]) → (xs', rs', ps', [v'])
    requires m = n ∧ Nonbreakdown A (decodedState dec n xs rs ps) ∧
      dec v = decv dec n rs ⬝ᵥ decv dec n rs
    ensures decodedState dec n xs' rs' ps' = cgStep A (decodedState dec n xs rs ps) ∧
      dec v' = decv dec n rs' ⬝ᵥ decv dec n rs'

/-- The readable state blocks decode to the given CG state and retain its residual product. -/
def StoresState (dec : K → ℝ) (n : ℕ) (x r p v : ℕ × ℕ)
    (s : CGState ℝ (Fin n)) (μ : Mem K) : Prop :=
  ∃ xs rs ps rr, μ.readBlocks [x, r, p, v] [n, n, n, 1] = some [xs, rs, ps, [rr]] ∧
    decodedState dec n xs rs ps = s ∧ dec rr = decv dec n rs ⬝ᵥ decv dec n rs

/-- One retained-product round meets its specification under exact operation contracts: the
run is total and keeps the retained-product invariant needed by the next round. -/
theorem stepRoutine_meets {M : Machine K} {dec : K → ℝ} {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M)
    (hB : IsExactBlas1 dec (fun _ => True) I) (hA : IsExactMatvec dec A I) :
    (stepRoutine (Op := Op) (Tst := Tst)).Meets I (stepSpec dec A) := by
  routine_intro [n'] (x, r, p, v) reads (xs, rs, ps, vs)
  obtain ⟨rr, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock hvs)
  obtain ⟨hn, hdom⟩ := hpre
  obtain rfl : n = n' := hn.symm
  have hrr : m.store.get v.1 v.2 = some rr := by
    simpa using Store.get_of_readBlock hvs (j := 0) (by omega) rr
  refine writes_allocs (lens := [.var 0, .const 3]) (ns := [n, 3]) rfl
    fun s₁ hs₁ hlen hB₁ => ?_
  have hq : s₁.len m.store.length = n := by simpa using hlen 0 (by simp)
  have ht : s₁.len (m.store.length + 1) = 3 := by simpa using hlen 1 (by simp)
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
  routine_exit
  exact ⟨hstep, hrrd'⟩

end NLAlib.Krylov.CG.HSCG.Carried
