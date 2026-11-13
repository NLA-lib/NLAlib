/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Reorth.Round
public import NLAlib.Krylov.CG.HSCG.Exact

/-!
# The exact iterate and residual update before reorthogonalization

This footprint rule borrows vector and scalar scratch from a reorthogonalized round. It
stops before the new residual norm and search direction are formed, so a certified projection
sweep can be inserted between those stages.

## Main results

* `NLAlib.Krylov.CG.Reorth.update_writes`: the exact prefix with saved residual self-product.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- Exact arithmetic forms the new iterate and raw residual and retains the old squared norm.
The three caller buffers are below the three distinct scratch buffers starting at `L`. -/
theorem update_writes {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec (fun _ => True) I)
    {n L : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsExactMatvec dec A I)
    {τ : Tape K} {μ : Mem K} {x r p : ℕ × ℕ} {xs rs ps : List K}
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hxL : x.1 < L) (hrL : r.1 < L) (hpL : p.1 < L)
    (hl : μ.store.length = L + 3) (hW : μ.store.len L = n) (ht : μ.store.len (L + 2) = 4)
    (hxz : x.2 + n ≤ μ.store.len x.1) (hrz : r.2 + n ≤ μ.store.len r.1)
    (hxs : μ.store.readBlock x.1 x.2 n = some xs)
    (hrs : μ.store.readBlock r.1 r.2 n = some rs)
    (hps : μ.store.readBlock p.1 p.2 n = some ps)
    (hdom : Nonbreakdown A (HSCG.decodedState dec n xs rs ps)) :
    Writes .total I τ update (Env.frame [n] [x, r, p, (L, 0), (L + 2, 0), x, r])
      (Fp.blocks [x, r, (L, 0), (L + 2, 0)] [n, n, n, 4])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ xs' rs' rr,
        μ'.store.readBlock x.1 x.2 n = some xs' ∧
        μ'.store.readBlock r.1 r.2 n = some rs' ∧
        μ'.store.get (L + 2) 0 = some rr ∧
        dec rr = decv dec n rs ⬝ᵥ decv dec n rs ∧
        decv dec n xs' = (cgStep A (HSCG.decodedState dec n xs rs ps)).x ∧
        decv dec n rs' = (cgStep A (HSCG.decodedState dec n xs rs ps)).r) μ := by
  step hB.dot as m₁ hfr₁ ⟨hpos₁, rr, hrr, herr⟩
  step hA as m₂ hfr₂ ⟨hpos₂, ws, hws, hmv⟩
  step hB.dot as m₃ hfr₃ ⟨hpos₃, pq, hpq, hepq⟩
  step (hS .div) as m₄ hfr₄ ⟨hpos₄, a, ha, hea⟩
  step hB.axpy as m₅ hfr₅ ⟨hpos₅, xs', hxs', hex⟩
  step (hS .neg) as m₆ hfr₆ ⟨hpos₆, na, hna, hena⟩
  step hB.axpy as m₇ hfr₇ ⟨hpos₇, rs', hrs', her⟩
  have hrrd := dotExactRel_decoded (dec := dec) (n := n) herr
  have hpqd := dotExactRel_decoded (dec := dec) (n := n) hepq
  have hpq0 : dec pq ≠ 0 := by rw [hpqd, hmv]; exact hdom.2
  have had : dec a = (decv dec n rs ⬝ᵥ decv dec n rs) /
      (decv dec n ps ⬝ᵥ (A *ᵥ decv dec n ps)) := by
    rw [← hea, hM.div rr pq hpq0, hrrd, hpqd, hmv]
  have hnad : dec na = -dec a := hena ▸ hM.neg a
  refine ⟨by simp [hpos₇, hpos₆, hpos₅, hpos₄, hpos₃, hpos₂, hpos₁],
    xs', rs', rr, by kept, hrs', by kept, hrrd, ?_, ?_⟩
  · funext i
    simpa [cgStep_eq, HSCG.decodedState, had] using congrFun (axpyExactRel_decoded hex) i
  · funext i
    simpa [cgStep_eq, HSCG.decodedState, had, hnad, hmv, sub_eq_add_neg, neg_smul] using
      congrFun (axpyExactRel_decoded her) i

end NLAlib.Krylov.CG.Reorth
