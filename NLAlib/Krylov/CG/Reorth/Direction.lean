/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Reorth.Round

/-!
# The direction update after full residual reorthogonalization

The squared norm is computed from the swept residual. The old residual self-product is read
from the scalar scratch saved by the iterate/residual prefix.

## Main results

* `NLAlib.Krylov.CG.Reorth.direction_writes`: the exact new search direction.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

omit [Has OperatorOp Op] in
/-- The direction uses the new swept residual norm and the saved nonzero old squared norm. -/
theorem direction_writes {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec (fun _ => True) I)
    {n L : ℕ} {τ : Tape K} {μ : Mem K} {r p : ℕ × ℕ} {rs ps : List K} {rr : K}
    (hrL : r.1 < L) (hpL : p.1 < L)
    (hl : μ.store.length = L + 3) (hZ : μ.store.len (L + 1) = n)
    (ht : μ.store.len (L + 2) = 4) (hpz : p.2 + n ≤ μ.store.len p.1)
    (hrs : μ.store.readBlock r.1 r.2 n = some rs)
    (hps : μ.store.readBlock p.1 p.2 n = some ps)
    (hrr : μ.store.get (L + 2) 0 = some rr) (hrr0 : dec rr ≠ 0) :
    Writes .total I τ direction (Env.frame [n] [r, p, (L + 1, 0), (L + 2, 0), p])
      (Fp.blocks [p, (L + 1, 0), (L + 2, 0)] [n, n, 4])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ps', μ'.store.readBlock p.1 p.2 n = some ps' ∧
        decv dec n ps' = decv dec n rs +
          ((decv dec n rs ⬝ᵥ decv dec n rs) / dec rr) • decv dec n ps) μ := by
  step hB.dot as m₁ hfr₁ ⟨hpos₁, rr', hrr', herr'⟩
  step (hS .div) as m₂ hfr₂ ⟨hpos₂, b, hb, heb⟩
  step hB.copy as m₃ hfr₃ ⟨hpos₃, zs, hzs, hcopy⟩
  subst zs
  step hB.axpy as m₄ hfr₄ ⟨hpos₄, ps', hps', hep⟩
  step hB.copy as m₅ hfr₅ ⟨hpos₅, ps'', hps'', hcopy'⟩
  subst ps''
  have hrrd := dotExactRel_decoded (dec := dec) (n := n) herr'
  have hbd : dec b = (decv dec n rs ⬝ᵥ decv dec n rs) / dec rr := by
    rw [← heb, hM.div rr' rr hrr0, hrrd]
  exact ⟨by simp [hpos₅, hpos₄, hpos₃, hpos₂, hpos₁], ps', hps'',
    by simpa only [hbd] using (axpyExactRel_decoded hep)⟩

end NLAlib.Krylov.CG.Reorth
