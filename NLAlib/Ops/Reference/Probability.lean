/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Reference.Equivalence
public import NLAlib.Ops.Randomized

/-!
# Randomized claims read with the evaluator

A randomized claim bounds the probability that a run is not accepted, and acceptance
(`NLAlib.Ops.Specification.Accepts`) is stated with the execution rules. The theorems here
restate the same bound with canonical execution. The equivalence is pointwise in the tape, so
no probability calculus or measurability assumption is added.

## Main results

* `NLAlib.Ops.Algorithm.failsAtMost_iff_exec`: the failure bound, read with the evaluator.
* `NLAlib.Ops.RandomizedClaim.holds_exec`: a claim, read with the evaluator.
-/

@[expose] public section

namespace NLAlib.Ops.Algorithm

open MeasureTheory

variable {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}
  {M : AccessModel Op Tst P} {S : Specification Op Tst P}

/-- A randomized guarantee read with the evaluator: with exactly the same admitted inputs,
interpretation assumptions, tape law, event and bound, the probability that canonical execution
fails, exceeds a resource bound or misses the event is at most the bound. -/
theorem failsAtMost_iff_exec (A : Algorithm M S)
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
          μ.real {ω | ¬ ∃ st, exec A.program I M.resources P.formats (tape ω) d
              (P.initial d x) = some st ∧
            st.peak ≤ S.scratch d ∧ st.cost ≤ S.budget d ∧
            M.resources.work st.cost ≤ S.work d ∧ M.resources.span st.cost ≤ S.span d ∧
            P.initialBytes d x + st.peak ≤ S.memory d ∧
            event d x (tape ω) st.cost st.mem} ≤ bound d x := by
  simp only [FailsAtMost, Specification.accepts_iff_exec]

end NLAlib.Ops.Algorithm

namespace NLAlib.Ops.RandomizedClaim

open MeasureTheory

variable {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}
  {M : AccessModel Op Tst P} {S : Specification Op Tst P} {A : Algorithm M S}

/-- A randomized claim read with the evaluator: under the claim's law and all its assumptions,
canonical execution fails, violates a resource bound or misses the accuracy event with at most
the claimed probability. Tape-law realizability remains the claim's field `realizable`. -/
theorem holds_exec (C : RandomizedClaim A) (d : Fin r → ℕ) (hd : P.valid d)
    (x : P.Input d) (hx : C.admits d x) (I : Interp Op Tst K)
    (hI : M.contracts d x I) (hInt : C.interprets d x I)
    (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (tape : Ω → Tape K) (hLaw : C.law d x Ω μ tape) :
    μ.real {ω | ¬ ∃ st, exec A.program I M.resources P.formats (tape ω) d
        (P.initial d x) = some st ∧
      st.peak ≤ S.scratch d ∧ st.cost ≤ S.budget d ∧
      M.resources.work st.cost ≤ S.work d ∧ M.resources.span st.cost ≤ S.span d ∧
      P.initialBytes d x + st.peak ≤ S.memory d ∧
      C.event d x (tape ω) st.cost st.mem} ≤ C.bound d x :=
  (A.failsAtMost_iff_exec C.law C.admits C.interprets C.event C.bound).mp
    C.holds d hd x hx I hI hInt Ω μ tape hLaw

end NLAlib.Ops.RandomizedClaim
