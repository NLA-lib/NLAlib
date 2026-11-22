/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Probability
public import NLAlib.Ops.TapeLaw

/-!
# Randomized claims about a certificate

A certificate `NLAlib.Ops.Algorithm` states what every run does, on every tape. The accuracy of
a randomized algorithm is a statement about the law of the tape, and it is a separate theorem.
A `NLAlib.Ops.RandomizedClaim` ties the two together, in one object a reader can find from the
certificate: it names

* the certificate it is about (its type is `RandomizedClaim A`);
* the law of the tape (`law`): which probability spaces and random tapes the claim covers;
* the hypotheses on the size and the input (`admits`) and on the interpretation of the
  operations (`interprets`);
* the accuracy event (`event`), a property of the count and the final memory of the run;
* the failure bound (`bound`), a function of the size and the input;

and it carries the proof (`holds`) that, under that law, the probability that the counted run of
the certified program fails, exceeds a resource bound of the specification or misses the event
is at most the bound. The run in the statement is the run of the certificate: the same program,
from the initial memory of the problem.

The law of a tape is given in one of two forms. `NLAlib.Ops.TapeModel.streams` says the entries
of the tape are independent with stated laws on named streams. `NLAlib.Ops.TapeModel.packed`
says the tape is a stated packing of a random mathematical object with a stated law. A claim may
also state its law directly.

A certificate whose routine has the specification `NLAlib.Ops.Routine.Spec.terminates` claims
nothing of what it writes; such a certificate has a randomized claim, and the certificate check
`scripts/OpsPrograms.lean` fails otherwise.

## Main definitions

* `NLAlib.Ops.TapeModel`, `NLAlib.Ops.TapeModel.streams`, `NLAlib.Ops.TapeModel.packed`: laws of
  the tape.
* `NLAlib.Ops.Algorithm.FailsAtMost`: the statement of a claim.
* `NLAlib.Ops.RandomizedClaim`: the claim.

## Main results

* `NLAlib.Ops.RandomizedClaim.ofReference`, `NLAlib.Ops.RandomizedClaim.ofWp`: a claim from each
  of the two transfers of `NLAlib/Ops/Probability.lean`.
-/

@[expose] public section

namespace NLAlib.Ops

open MeasureTheory ProbabilityTheory

variable {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}

/-- A law of the tape: the sample spaces, measures and random tapes that a claim covers. -/
abbrev TapeModel (K : Type) : Type 1 :=
  (Ω : Type) → [MeasurableSpace Ω] → Measure Ω → (Ω → Tape K) → Prop

namespace TapeModel

/-- The entries of the tape are independent, and an entry of each stream `s` listed in `fixed`
has the law listed with it. The laws of the other streams are not constrained. -/
def streams [MeasurableSpace K] (fixed : List (ℕ × Measure K)) : TapeModel K :=
  fun _ _ μ ξ => ∃ law : ℕ → Measure K, (∀ p ∈ fixed, law p.1 = p.2) ∧ IsTapeLaw law μ ξ

/-- The tape is the packing `pack` of a random object with the law `ν`. -/
def packed {α : Type} [MeasurableSpace α] (ν : Measure α) (pack : α → Tape K) : TapeModel K :=
  fun Ω _ μ ξ => ∃ X : Ω → α, HasLaw X ν μ ∧ ξ = fun ω => pack (X ω)

end TapeModel

namespace Algorithm

variable {model : AccessModel Op Tst P} {S : Specification Op Tst P}

/-- **The statement of a randomized claim.** For every admitted size and input satisfying
`admits`, every interpretation satisfying the contracts of the model and `interprets`, and every
finite measure and random tape with the law `law`: the probability that the counted run of the
certified program fails, exceeds a resource bound of the specification, or ends with a count and
memory outside `event`, is at most `bound`. -/
def FailsAtMost (A : Algorithm model S)
    (law : (d : Fin r → ℕ) → P.Input d → TapeModel K)
    (admits : (d : Fin r → ℕ) → P.Input d → Prop)
    (interprets : (d : Fin r → ℕ) → P.Input d → Interp Op Tst K → Prop)
    (event : (d : Fin r → ℕ) → P.Input d → Tape K → Count (Op ⊕ Bookkeeping) Tst → Mem K → Prop)
    (bound : (d : Fin r → ℕ) → P.Input d → ℝ) : Prop :=
  ∀ d, P.valid d → ∀ x : P.Input d, admits d x → ∀ I : Interp Op Tst K,
    model.contracts d x I → interprets d x I →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (tape : Ω → Tape K),
      law d x Ω μ tape →
      μ.real {ω | ¬ S.Accepts model.resources d x
        (exec A.program I model.resources P.formats (tape ω) d (P.initial d x))
        (event d x (tape ω))} ≤ bound d x

end Algorithm

/-- A stronger postcondition is accepted when a weaker one follows from it. -/
theorem Specification.Accepts.mono {S : Specification Op Tst P} {resources : ResourceModel Op Tst}
    {d : Fin r → ℕ} {x : P.Input d} {outcome : Option (St (Op ⊕ Bookkeeping) Tst K)}
    {Q Q' : Count (Op ⊕ Bookkeeping) Tst → Mem K → Prop}
    (h : S.Accepts resources d x outcome Q) (hQ : ∀ c m, Q c m → Q' c m) :
    S.Accepts resources d x outcome Q' := by
  obtain ⟨st, hrun, hpeak, hcount, hwork, hspan, hmemory, hq⟩ := h
  exact ⟨st, hrun, hpeak, hcount, hwork, hspan, hmemory, hQ _ _ hq⟩

/-- **A randomized claim about a certificate**: the law of the tape, the hypotheses, the
accuracy event and the failure bound, with the proof that the counted run of the certified
program misses the event, fails or exceeds a resource bound with probability at most the bound.
-/
structure RandomizedClaim {model : AccessModel Op Tst P} {S : Specification Op Tst P}
    (A : Algorithm model S) : Type 1 where
  /-- The law of the tape at a size and an input. -/
  law : (d : Fin r → ℕ) → P.Input d → TapeModel K
  /-- The hypotheses on the size and the input, beyond admission to the problem. -/
  admits : (d : Fin r → ℕ) → P.Input d → Prop
  /-- The hypotheses on the interpretation, beyond the contracts of the model. -/
  interprets : (d : Fin r → ℕ) → P.Input d → Interp Op Tst K → Prop
  /-- The accuracy event, on the tape, the count and the final memory of the run. -/
  event : (d : Fin r → ℕ) → P.Input d → Tape K → Count (Op ⊕ Bookkeeping) Tst → Mem K → Prop
  /-- The bound on the probability of failure. -/
  bound : (d : Fin r → ℕ) → P.Input d → ℝ
  /-- The counted run fails, exceeds a resource bound or misses the event with probability at
  most the bound. -/
  holds : A.FailsAtMost law admits interprets event bound

namespace RandomizedClaim

variable {model : AccessModel Op Tst P} {S : Specification Op Tst P} {A : Algorithm model S}

/-- A claim from a reference event: under the law, some event of the sample space has failure
probability at most the bound, and together with the output condition of the specification it
gives the accuracy event. The transfer is `NLAlib.Ops.Algorithm.measureReal_failure_le`. -/
def ofReference (A : Algorithm model S)
    (law : (d : Fin r → ℕ) → P.Input d → TapeModel K)
    (admits : (d : Fin r → ℕ) → P.Input d → Prop)
    (interprets : (d : Fin r → ℕ) → P.Input d → Interp Op Tst K → Prop)
    (event : (d : Fin r → ℕ) → P.Input d → Tape K → Count (Op ⊕ Bookkeeping) Tst → Mem K → Prop)
    (bound : (d : Fin r → ℕ) → P.Input d → ℝ)
    (h : ∀ d, P.valid d → ∀ x : P.Input d, admits d x → ∀ I : Interp Op Tst K,
      model.contracts d x I → interprets d x I →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (tape : Ω → Tape K),
        law d x Ω μ tape → ∃ R : Ω → Prop,
          (∀ ω c m, S.good d x (tape ω) c m → R ω → event d x (tape ω) c m) ∧
            μ.real {ω | ¬ R ω} ≤ bound d x) : RandomizedClaim A where
  law := law
  admits := admits
  interprets := interprets
  event := event
  bound := bound
  holds := fun d hd x hx I hI hint Ω _ μ _ tape hlaw => by
    obtain ⟨R, hPost, hBound⟩ := h d hd x hx I hI hint Ω μ tape hlaw
    exact A.measureReal_failure_le hd x I hI tape R _ hPost μ hBound

/-- A claim from the program logic: under the law, the memory semantics of the certified
program misses a total postcondition that gives the accuracy event with probability at most the
bound. The transfer is `NLAlib.Ops.Algorithm.measureReal_not_accepts_le_of_wp`. -/
def ofWp (A : Algorithm model S)
    (law : (d : Fin r → ℕ) → P.Input d → TapeModel K)
    (admits : (d : Fin r → ℕ) → P.Input d → Prop)
    (interprets : (d : Fin r → ℕ) → P.Input d → Interp Op Tst K → Prop)
    (event : (d : Fin r → ℕ) → P.Input d → Tape K → Count (Op ⊕ Bookkeeping) Tst → Mem K → Prop)
    (bound : (d : Fin r → ℕ) → P.Input d → ℝ)
    (h : ∀ d, P.valid d → ∀ x : P.Input d, admits d x → ∀ I : Interp Op Tst K,
      model.contracts d x I → interprets d x I →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (tape : Ω → Tape K),
        law d x Ω μ tape →
          μ.real {ω | ¬ Wp .total I (tape ω) A.program.body (Program.environment (b := b) d)
            (fun m => ∀ c, event d x (tape ω) c m) (P.initial d x)} ≤ bound d x) :
    RandomizedClaim A where
  law := law
  admits := admits
  interprets := interprets
  event := event
  bound := bound
  holds := fun d hd x hx I hI hint Ω _ μ _ tape hlaw => by
    refine (measureReal_mono ?_).trans
      (A.measureReal_not_accepts_le_of_wp hd x I hI μ tape
        (fun ω m => ∀ c, event d x (tape ω) c m) (h d hd x hx I hI hint Ω μ tape hlaw))
    intro ω hbad hacc
    exact hbad (hacc.mono fun c m hq => hq c)

end RandomizedClaim

end NLAlib.Ops
