/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Cert
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Probability transfer from total canonical algorithm certificates

A total certificate supplies successful counted execution and every declared resource bound
on every tape. When its output specification and a mathematical reference event imply a
stronger postcondition, the complete actual failure event lies inside reference failure.
This includes `none`, all resource violations and failure of the stronger output property.

## Main results

* `NLAlib.Ops.Specification.Accepts`: one counted outcome satisfies all resource bounds and a post.
* `NLAlib.Ops.Algorithm.failure_subset`: actual failure is contained in reference failure.
* `NLAlib.Ops.Algorithm.measureReal_failure_le`: a reference bound controls complete run failure.
-/

@[expose] public section

namespace NLAlib.Ops

open MeasureTheory

variable {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}

/-- One actual counted outcome succeeds, obeys every resource claim of the specification,
and meets the supplied postcondition on that same count and final memory. Negation includes
failure, peak/count/work/span/resident-memory violations, and failure of the postcondition. -/
def Specification.Accepts (S : Specification Op Tst P) (resources : ResourceModel Op Tst)
    (d : Fin r → ℕ) (x : P.Input d) (outcome : Option (St (Op ⊕ Bookkeeping) Tst K))
    (Q : Count (Op ⊕ Bookkeeping) Tst → Mem K → Prop) : Prop :=
  ∃ st, outcome = some st ∧ st.peak ≤ S.scratch d ∧ st.cost ≤ S.budget d ∧
    resources.work st.cost ≤ S.work d ∧ resources.span st.cost ≤ S.span d ∧
    P.initialBytes d x + st.peak ≤ S.memory d ∧ Q st.cost st.mem

namespace Algorithm

variable {model : AccessModel Op Tst P} {S : Specification Op Tst P}
  (A : Algorithm model S) {d : Fin r → ℕ} (hd : P.valid d) (x : P.Input d)
  (I : Interp Op Tst K) (hI : model.contracts d x I)
  {Omega : Type} (tape : Omega → Tape K) (R : Omega → Prop)
  (Q : Omega → Count (Op ⊕ Bookkeeping) Tst → Mem K → Prop)
  (hPost : ∀ omega c m, S.good d x (tape omega) c m → R omega → Q omega c m)

include hd hI hPost

/-- The reference event strengthens the postcondition of the actual counted execution.
Success and all resource facts come from the total certificate, rather than premises. -/
theorem accepts_of_reference (omega : Omega) (hR : R omega) :
    S.Accepts model.resources d x
      (exec A.program I model.resources P.formats (tape omega) d (P.initial d x)) (Q omega) := by
  obtain ⟨st, hrun, hpeak, hcount, hwork, hspan, hmemory, hgood⟩ :=
    A.correct d hd x I hI (tape omega)
  exact ⟨st, hrun, hpeak, hcount, hwork, hspan, hmemory, hPost omega st.cost st.mem hgood hR⟩

/-- Actual counted failure, including any resource or output violation, is a subset of
mathematical reference failure. No execution-success assumption is required. -/
theorem failure_subset :
    {omega | ¬ S.Accepts model.resources d x
      (exec A.program I model.resources P.formats (tape omega) d (P.initial d x)) (Q omega)} ⊆
      {omega | ¬ R omega} := by
  intro omega hbad hR
  exact hbad (A.accepts_of_reference hd x I hI tape R Q hPost omega hR)

/-- Outer measure of complete actual failure is bounded by reference failure, without
additional measurability assumptions on the supplied postcondition. -/
theorem measure_failure_le [MeasurableSpace Omega] (mu : Measure Omega) :
    mu {omega | ¬ S.Accepts model.resources d x
      (exec A.program I model.resources P.formats (tape omega) d (P.initial d x)) (Q omega)} ≤
      mu {omega | ¬ R omega} :=
  measure_mono (A.failure_subset hd x I hI tape R Q hPost)

/-- For finite measures, a real-valued reference failure bound controls the complete actual
failure event of the same canonical run. Finiteness rules out converting infinity to real zero. -/
theorem measureReal_failure_le [MeasurableSpace Omega] (mu : Measure Omega)
    [IsFiniteMeasure mu] {delta : ℝ} (hBound : mu.real {omega | ¬ R omega} ≤ delta) :
    mu.real {omega | ¬ S.Accepts model.resources d x
      (exec A.program I model.resources P.formats (tape omega) d (P.initial d x)) (Q omega)} ≤
      delta :=
  (measureReal_mono (A.failure_subset hd x I hI tape R Q hPost)).trans hBound

end Algorithm

end NLAlib.Ops
