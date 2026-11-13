/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Update
public import NLAlib.Krylov.Lanczos.RoundedNormalization

/-!
# Rounded Paige-order Lanczos updates

The raw update uses an exact primitive matrix-vector product and rounded BLAS operations.
Its total certificate derives the local dot and axpy defects from actual readable outputs.
Guarded rounded normalization is supplied separately by `normalize_rounded_spec`; no global
finite-precision stability or backward-error transfer is asserted by this local slice.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.update_writes` proves the two update error bounds and dot bound.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops
open scoped Matrix

/-- The local componentwise defects in Paige order, with the intermediate vector retained in
this numerical relation. Scalar sign changes and the primitive matrix-vector product are exact. -/
def UpdateBounds {n : ℕ} (em ed ea : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (prev cur first raw : Fin n → ℝ) (beta alpha : ℝ) : Prop :=
  ∃ mv : Fin n → ℝ,
  ‖WithLp.toLp 2 (A *ᵥ cur - mv)‖ ≤ em * specNorm A * ‖WithLp.toLp 2 cur‖ ∧
  (∀ i, |first i - (mv i - beta * prev i)| ≤
    ea * (|mv i| + |beta * prev i|)) ∧
  |alpha - cur ⬝ᵥ first| ≤ ed * ∑ i : Fin n, |cur i * first i| ∧
  ∀ i, |raw i - (first i - alpha * cur i)| ≤ ea * (|first i| + |alpha * cur i|)

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op]

/-- Readable input vectors and operation models guarantee successful raw update execution.
Every error bound refers to the actual computed alpha and raw output, with no success premise. -/
theorem update_writes {M : Machine K} {dec : K → ℝ} {n L : ℕ} {em u : ℝ} {ε : Blas1Err}
    {I : Interp Op Tst K} {A : Matrix (Fin n) (Fin n) ℝ} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec ε ok I)
    (hok : ok n) (hA : IsMatvec dec A (em * specNorm A) I) {τ : Tape K} {μ : Mem K}
    {q b a : ℕ × ℕ} {ps qs : List K} {β : K}
    (hqa : q.1 ≠ a.1) (hqL : q.1 < L) (hbL : b.1 < L) (haL : a.1 < L)
    (hlen : μ.store.length = L + 3) (hw : μ.store.len (L + 1) = n)
    (ht : μ.store.len (L + 2) = 2) (ha : a.2 < μ.store.len a.1)
    (hps : μ.store.readBlock L 0 n = some ps)
    (hqs : μ.store.readBlock q.1 q.2 n = some qs) (hβ : μ.store.get b.1 b.2 = some β) :
    Writes .total I τ Lanczos.update
      (Env.frame [n] [(L, 0), q, b, (L + 1, 0), a, (L + 2, 0), (L + 1, 0), a])
      (Fp.blocks [(L + 1, 0), a, (L + 2, 1)] [n, 1, 1])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ first raw α,
        μ'.store.readBlock (L + 1) 0 n = some raw ∧ μ'.store.get a.1 a.2 = some α ∧
        UpdateBounds em (ε.dot n) ε.axpy A (decv dec n ps) (decv dec n qs)
          (decv dec n first) (decv dec n raw) (dec β) (dec α)) μ := by
  step hA as μ₁ hfr₁ ⟨hpos₁, aq, haq, haqvec⟩
  step (hS .neg) as μ₂ hfr₂ ⟨hpos₂, nb, hnb, hnbword⟩
  step hB.axpy as μ₃ hfr₃ ⟨hpos₃, first, hfirst, hfirsterr⟩
  step hB.dot as μ₄ hfr₄ ⟨hpos₄, α, hα, hαerr⟩
  step (hS .neg) as μ₅ hfr₅ ⟨hpos₅, na, hna, hnaword⟩
  step hB.axpy as μ₆ hfr₆ ⟨hpos₆, raw, hraw, hrawerr⟩
  have hnbdec : dec nb = -dec β := hnbword ▸ hM.neg β
  have hnadec : dec na = -dec α := hnaword ▸ hM.neg α
  refine ⟨by simp [hpos₆, hpos₅, hpos₄, hpos₃, hpos₂, hpos₁], first, raw, α,
    hraw, by kept, decv dec n aq, haqvec, ?_, hαerr.decoded, ?_⟩
  · intro i
    simpa only [hnbdec, neg_mul, ← sub_eq_add_neg, abs_neg] using hfirsterr.decoded i
  · intro i
    simpa only [hnadec, neg_mul, ← sub_eq_add_neg, abs_neg] using hrawerr.decoded i

end NLAlib.Krylov.Lanczos.Rounded
