/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Alg
public import NLAlib.Krylov.Lanczos.Spec
public import NLAlib.Ops.Blas.Decoded
public import NLAlib.Ops.Logic.Tactic

/-!
# The borrowed-workspace Lanczos three-term update

The update computes the diagonal coefficient and raw residual, stopping before its norm and
normalization. The full-reorthogonalization variant can insert its two classical passes at
this boundary. Matrix application remains an abstract exact operator.

## Main results

* `NLAlib.Krylov.Lanczos.update_writes` gives total execution and the exact raw recurrence.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- The Paige-order raw update borrows Prev=L, Work=L+1 and two scalar cells at L+2.
The current vector and coefficient cells lie below those buffers; the current vector and
alpha output use different buffers. No spectral or nonbreakdown assumption is needed. -/
theorem update_writes {M : Machine K} {dec : K → ℝ} {n L : ℕ} {I : Interp Op Tst K}
    {A : Matrix (Fin n) (Fin n) ℝ} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) {τ : Tape K} {μ : Mem K}
    {q b a : ℕ × ℕ} {ps qs : List K} {β : K}
    (hqa : q.1 ≠ a.1) (hqL : q.1 < L) (hbL : b.1 < L) (haL : a.1 < L)
    (hlen : μ.store.length = L + 3)
    (hw : μ.store.len (L + 1) = n)
    (ht : μ.store.len (L + 2) = 2) (ha : a.2 < μ.store.len a.1)
    (hps : μ.store.readBlock L 0 n = some ps)
    (hqs : μ.store.readBlock q.1 q.2 n = some qs) (hβ : μ.store.get b.1 b.2 = some β) :
    Writes .total I τ update
      (Env.frame [n] [(L, 0), q, b, (L + 1, 0), a, (L + 2, 0), (L + 1, 0), a])
      (Fp.blocks [(L + 1, 0), a, (L + 2, 1)] [n, 1, 1])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ws α,
        μ'.store.readBlock (L + 1) 0 n = some ws ∧ μ'.store.get a.1 a.2 = some α ∧
        dec α = lanczosAlpha A ⟨decv dec n ps, decv dec n qs, dec β⟩ ∧
        decv dec n ws = A *ᵥ decv dec n qs - dec β • decv dec n ps -
          dec α • decv dec n qs) μ := by
  step hA as μ₁ hfr₁ ⟨hpos₁, aq, haq, haqvec⟩
  step (hS .neg) as μ₂ hfr₂ ⟨hpos₂, nb, hnb, hnbword⟩
  step hB.axpy as μ₃ hfr₃ ⟨hpos₃, raw₁, hraw₁, hrawvec₁⟩
  step hB.dot as μ₄ hfr₄ ⟨hpos₄, α, hα, hαdot⟩
  step (hS .neg) as μ₅ hfr₅ ⟨hpos₅, na, hna, hnaword⟩
  step hB.axpy as μ₆ hfr₆ ⟨hpos₆, raw, hraw, hrawvec⟩
  have hnbdec : dec nb = -dec β := hnbword ▸ hM.neg β
  have hnadec : dec na = -dec α := hnaword ▸ hM.neg α
  have hfirst : decv dec n raw₁ = A *ᵥ decv dec n qs - dec β • decv dec n ps := by
    simpa [haqvec, hnbdec, sub_eq_add_neg, neg_smul] using axpyExactRel_decoded hrawvec₁
  have hαdec : dec α = lanczosAlpha A ⟨decv dec n ps, decv dec n qs, dec β⟩ := by
    simpa [lanczosAlpha, hfirst] using dotExactRel_decoded hαdot
  refine ⟨by simp [hpos₆, hpos₅, hpos₄, hpos₃, hpos₂, hpos₁], raw, α, hraw, by kept, hαdec, ?_⟩
  simpa [hfirst, hnadec, sub_eq_add_neg, neg_smul] using axpyExactRel_decoded hrawvec

end NLAlib.Krylov.Lanczos
