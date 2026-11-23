/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Reference.Semantics

/-!
# Specifications and what it means to certify one

A specification lists the claims about one run of a program: a bound for each resource and a
condition on the final count and memory. A run is *accepted* when the execution rules
(`NLAlib.Ops.Reference.Execution`) derive an outcome that is within every bound and satisfies
the condition. A certificate states that every run is accepted.

These definitions are stated with the execution rules alone. The evaluator `NLAlib.Ops.exec`
computes the same outcome (`NLAlib.Ops.Reference.execution_iff_exec`), and
`NLAlib.Ops.Specification.accepts_iff_exec` and `NLAlib.Ops.Program.certifies_iff_exec` restate
acceptance and certification with it; proofs use those forms.

## Main definitions

* `NLAlib.Ops.Specification`: the claims about one run.
* `NLAlib.Ops.Specification.Accepts`: one run is accepted (an outcome derived by the rules, the
  five resource bounds and a postcondition).
* `NLAlib.Ops.Runs`, `NLAlib.Ops.Program.Certifies`: every run of a fixed program is accepted.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- An independently specified algorithmic claim. All resource budgets depend on sizes alone.
The actual counted postcondition may also depend on the input and tape. Structural instructions
are separate operation names in the same count, so omitting them is a false budget claim. -/
structure Specification (Op Tst : Type) {K : Type} {r b : ℕ} (P : Problem K r b) where
  /-- Budget for original operations, queries, index evaluation and control. -/
  budget : (Fin r → ℕ) → Count (Op ⊕ Bookkeeping) Tst
  /-- Peak additional scratch payload bytes above the declared buffers. -/
  scratch : (Fin r → ℕ) → ℕ
  /-- Total modeled work, including explicit structural work. -/
  work : (Fin r → ℕ) → ℕ
  /-- Sequential composition of modeled primitive critical paths. -/
  span : (Fin r → ℕ) → ℕ
  /-- Initial buffer payload plus peak scratch payload bytes. -/
  memory : (Fin r → ℕ) → ℕ
  /-- The postcondition of this same successful, counted execution. -/
  good : (d : Fin r → ℕ) → P.Input d → Tape K →
    Count (Op ⊕ Bookkeeping) Tst → Mem K → Prop

/-- **A run is accepted.** The execution rules derive an outcome of the program `p` from the
supplied buffers of the input `x`, under the interpretation `I` and the tape `τ`; that outcome
obeys every resource claim of the specification (scratch, counts, work, span, and resident
memory: the payload of the supplied buffers plus the peak scratch), and its count and final
memory meet the postcondition `Q`. Negation includes failure (no outcome is derived), a
violation of any of the five bounds, and failure of the postcondition. A certificate states that
every run is accepted (`NLAlib.Ops.Runs`); a randomized claim bounds the probability that a run
is not (`NLAlib.Ops.Algorithm.FailsAtMost`). -/
def Specification.Accepts {r b : ℕ} {P : Problem K r b}
    (S : Specification Op Tst P) (p : Program Op Tst r b) (I : Interp Op Tst K)
    (resources : ResourceModel Op Tst) (τ : Tape K) (d : Fin r → ℕ) (x : P.Input d)
    (Q : Count (Op ⊕ Bookkeeping) Tst → Mem K → Prop) : Prop :=
  ∃ st, Reference.Execution p I resources P.formats τ d (P.initial d x) st ∧
    st.peak ≤ S.scratch d ∧ st.cost ≤ S.budget d ∧
    resources.work st.cost ≤ S.work d ∧ resources.span st.cost ≤ S.span d ∧
    P.initialBytes d x + st.peak ≤ S.memory d ∧ Q st.cost st.mem

/-- Total certification of this fixed program against an independently specified model and
claim: at every admitted size, for every input, every interpretation satisfying the contracts
of the model and every tape, the run from the supplied buffers is accepted
(`NLAlib.Ops.Specification.Accepts`) with the output condition of the specification. A target
can require this proposition directly, fixing the program before every runtime size and input.
Realizability is already required by the type of the model. -/
def Runs {r b : ℕ} {P : Problem K r b}
    (p : Program Op Tst r b) (M : AccessModel Op Tst P) (S : Specification Op Tst P) : Prop :=
  ∀ d, P.valid d → ∀ (x : P.Input d) (I : Interp Op Tst K), M.contracts d x I → ∀ τ,
    S.Accepts p I M.resources τ d x (S.good d x τ)

/-- Certification is the canonical total run proposition for one fixed tree and model. -/
abbrev Program.Certifies {r b : ℕ} {P : Problem K r b}
    (p : Program Op Tst r b) (M : AccessModel Op Tst P) (S : Specification Op Tst P) : Prop :=
  Runs p M S

end NLAlib.Ops
