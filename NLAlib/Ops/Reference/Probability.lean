/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Reference.Equivalence
public import NLAlib.Ops.Randomized

/-!
# Randomized claims read through the reference execution rules

Acceptance is successful reference execution, all resource bounds, and the given event on
that same count and memory. Its negation includes missing execution and every bound/event
violation. Equivalence is pointwise, so the existing probability statement transfers without
a new probability calculus or an additional measurability assumption.

## Main definitions

* `NLAlib.Ops.Reference.Accepts`: resource and event acceptance under the reference rules.

## Main results

* `NLAlib.Ops.Reference.accepts_iff`: reference and canonical acceptance are equivalent.
* `NLAlib.Ops.Algorithm.failsAtMost_iff_reference`: the full failure-bound read-back.
* `NLAlib.Ops.RandomizedClaim.reference_holds`: a claim has its reference-rule meaning.
-/

@[expose] public section

namespace NLAlib.Ops.Reference

variable {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}

/-- A reference execution obeys the scratch, count, work, span and resident-memory bounds
and its final count and memory satisfy `Q`. Negation includes every execution/resource/event
failure. The deterministic output specification is supplied separately by the certificate. -/
def Accepts (S : Specification Op Tst P) (p : Program Op Tst r b)
    (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (d : Fin r → ℕ) (x : P.Input d) (Q : Count (Op ⊕ Bookkeeping) Tst → Mem K → Prop) : Prop :=
  ∃ st, Execution p I R P.formats τ d (P.initial d x) st ∧
    st.peak ≤ S.scratch d ∧ st.cost ≤ S.budget d ∧
    R.work st.cost ≤ S.work d ∧ R.span st.cost ≤ S.span d ∧
    P.initialBytes d x + st.peak ≤ S.memory d ∧ Q st.cost st.mem

/-- Reference acceptance is exactly canonical acceptance, on every tape and input, including
failure. Neither admission, successful execution nor event measurability is a premise. -/
theorem accepts_iff (S : Specification Op Tst P) (p : Program Op Tst r b)
    (I : Interp Op Tst K) (R : ResourceModel Op Tst) (τ : Tape K)
    (d : Fin r → ℕ) (x : P.Input d) (Q : Count (Op ⊕ Bookkeeping) Tst → Mem K → Prop) :
    Accepts S p I R τ d x Q ↔
      S.Accepts R d x (exec p I R P.formats τ d (P.initial d x)) Q := by
  simp only [Accepts, Specification.Accepts, execution_iff_exec]

end NLAlib.Ops.Reference

namespace NLAlib.Ops.Algorithm

open MeasureTheory

variable {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}
  {M : AccessModel Op Tst P} {S : Specification Op Tst P}

/-- The original randomized guarantee is equivalent to its reference-rule read-back, with
exactly the same admitted inputs, interpretation assumptions, tape law, event and bound. -/
theorem failsAtMost_iff_reference (A : Algorithm M S)
    (law : (d : Fin r → ℕ) → P.Input d → TapeModel K)
    (admits : (d : Fin r → ℕ) → P.Input d → Prop)
    (interprets : (d : Fin r → ℕ) → P.Input d → Interp Op Tst K → Prop)
    (event : (d : Fin r → ℕ) → P.Input d → Tape K → Count (Op ⊕ Bookkeeping) Tst → Mem K → Prop)
    (bound : (d : Fin r → ℕ) → P.Input d → ℝ) :
    A.FailsAtMost law admits interprets event bound ↔
      ∀ d, P.valid d → ∀ x : P.Input d, admits d x → ∀ I : Interp Op Tst K,
        M.contracts d x I → interprets d x I →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
          (tape : Ω → Tape K), law d x Ω μ tape →
          μ.real {ω | ¬ Reference.Accepts S A.program I M.resources (tape ω) d x
            (event d x (tape ω))} ≤ bound d x := by
  simp only [FailsAtMost, Reference.accepts_iff]

end NLAlib.Ops.Algorithm

namespace NLAlib.Ops.RandomizedClaim

open MeasureTheory

variable {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}
  {M : AccessModel Op Tst P} {S : Specification Op Tst P} {A : Algorithm M S}

/-- Under the claim's original law and all its original assumptions, reference execution
fails, violates a resource bound or misses the accuracy event with at most the claimed
probability. Tape-law realizability remains the claim's field `realizable`. -/
theorem reference_holds (C : RandomizedClaim A) (d : Fin r → ℕ) (hd : P.valid d)
    (x : P.Input d) (hx : C.admits d x) (I : Interp Op Tst K)
    (hI : M.contracts d x I) (hInt : C.interprets d x I)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (tape : Ω → Tape K) (hLaw : C.law d x Ω μ tape) :
    μ.real {ω | ¬ Reference.Accepts S A.program I M.resources (tape ω) d x
      (C.event d x (tape ω))} ≤ C.bound d x := by
  exact (A.failsAtMost_iff_reference C.law C.admits C.interprets C.event C.bound).mp
    C.holds d hd x hx I hI hInt Ω μ tape hLaw

end NLAlib.Ops.RandomizedClaim
