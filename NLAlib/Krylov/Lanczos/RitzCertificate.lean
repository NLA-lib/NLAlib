/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Certificate
public import NLAlib.Krylov.Lanczos.LinkedCertificate
public import NLAlib.Krylov.Lanczos.RoundedRitz

/-!
# Canonical Lanczos certification with Ritz residual guarantees

A mathematical consequence of the actual stored output strengthens the complete canonical
certificate. The fixed program, jointly realized primitive model and every full instruction,
work, span, scratch and resident-memory bound are retained by `Algorithm.mapPost`.
Zero cap and zero input remain explicit complete outcomes.

## Main results

* `NLAlib.Krylov.Lanczos.SequentialCertification.ritzAlgorithm`: the same consequence
  for the actual sequential scalar lowering, retaining its separate resource manifest.

* `NLAlib.Krylov.Lanczos.Certification.ritzAlgorithm`: complete resource certification and
  physical rounded Ritz residual guarantees, without repeating an execution or cost proof.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Certification

open Ops

variable {K : Type} [Inhabited K]
variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The full resource specification with the existing numerical output strengthened by a
physical Ritz residual bound. Zero cap/input retain the initialized output alternatives. -/
noncomputable def ritzSpecification
    (model : Standard.Model (problem (K := K) domain admitted) (fun d => d 0))
    (E : (Fin 2 → ℕ) → ℝ) :
    Specification Standard.Operation CmpTst (problem (K := K) domain admitted) :=
  { specification model E with
    good := fun d x _ _ m => m.pos = 0 ∧ ∃ vs cs,
      m.store.readBlock 1 0 ((d 1 + 1) * d 0) = some vs ∧
      m.store.readBlock 2 0 (2 * d 1 + 2) = some cs ∧
      Rounded.RitzOutput model.decode (model.matrix d x) (decv model.decode (d 0) x.val.1)
        (E d) (d 1) vs cs }

/-- The same canonically certified Lanczos program also certifies physical rounded Ritz
residuals when cap times local error is at most one hundredth. No positivity of the cap or
nonzero-input restriction is needed; those cases retain their explicit output alternatives.
The full original resource specification is preserved unchanged. -/
noncomputable def ritzAlgorithm
    (model : Standard.Model (problem (K := K) domain admitted) (fun d => d 0))
    (E : (Fin 2 → ℕ) → ℝ) (cert : Algorithm model.access (specification model E))
    (hsmall : ∀ d, domain d → (d 1 : ℝ) * E d ≤ 1 / 100) :
    Algorithm model.access (ritzSpecification model E) :=
  cert.mapPost _ fun d hd _ _ _ _ h => by
    obtain ⟨hpos, vs, cs, hv, hc, hout⟩ := h
    exact ⟨hpos, vs, cs, hv, hc, hout.ritzOutput (hsmall d hd)⟩

end NLAlib.Krylov.Lanczos.Certification

namespace NLAlib.Krylov.Lanczos.SequentialCertification

open Ops

variable {K : Type} [Inhabited K]
variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The actual sequential scalar lowering retains its complete independently computed resource
specification while strengthening its output with the same physical Ritz residual guarantee. -/
noncomputable def ritzAlgorithm
    (model : Standard.Model (Certification.problem (K := K) domain admitted) (fun d => d 0))
    (E : (Fin 2 → ℕ) → ℝ) (cert : Algorithm model.access (specification model E))
    (hsmall : ∀ d, domain d → (d 1 : ℝ) * E d ≤ 1 / 100) :
    Algorithm model.access
      { specification model E with good := (Certification.ritzSpecification model E).good } :=
  cert.mapPost _ fun d hd _ _ _ _ h => by
    obtain ⟨hpos, vs, cs, hv, hc, hout⟩ := h
    exact ⟨hpos, vs, cs, hv, hc, hout.ritzOutput (hsmall d hd)⟩

end NLAlib.Krylov.Lanczos.SequentialCertification
