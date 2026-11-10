/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profile
public import NLAlib.Ops.TapeLaw

/-!
# Statements about the law of the tape, and their transfer through linking

A statement in expectation or in probability is about a random tape `ξ : Ω → Tape K`. The
interpretation is fixed before the sample, and linking is pointwise in the tape (`run_link`), so
these statements transfer from an algorithm to the linked program by lemmas proved once, here.

## Main results

* `NLAlib.Ops.RunsLaw`: the shape of a law-level theorem. For every sample the run succeeds
  within the counts and the workspace with an output `X ω`, and the random variable `X` satisfies
  a statement `Φ` (an expectation, a variance, a tail bound).
* `NLAlib.Ops.Profile.Certifies.runsLaw`: **the corollary for any algorithm and any certified
  profile**, law-level form. The abstract theorem may use that every operation reads the tape
  only in its window; the certificate provides it for the linked interpretation.
* `NLAlib.Ops.Profile.Certifies.measureReal_not_runs_le`: the probability that the linked
  program fails or misses its postcondition is at most that of the algorithm.
* `NLAlib.Ops.Profile.Certifies.integral_runVal`: the expectation of an observable of the final
  memory (`NLAlib.Ops.runVal`) is the same for the linked program.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib.Ops

variable {Op Lo Tst K Ω α : Type}

/-- **A law-level statement.** For every sample `ω`, the run under the tape `ξ ω` succeeds
within the counts `B` and the workspace `M` and its final memory satisfies `Q (X ω)`; the random
variable `X` satisfies `Φ`. -/
def RunsLaw (I : Interp Op Tst K) (W : Op → List ℕ → ℕ) (ξ : Ω → Tape K) (s : Stmt Op Tst)
    (ρ : Env) (m : Mem K) (B : Count Op Tst) (M : ℕ) (Q : α → Mem K → Prop)
    (Φ : (Ω → α) → Prop) : Prop :=
  ∃ X : Ω → α, (∀ ω, Runs I W (ξ ω) s ρ m B M (Q (X ω))) ∧ Φ X

/-- The observable `obs` of the final memory of a run; `0` if the run fails. -/
def runVal {E : Type} [Zero E] (I : Interp Op Tst K) (τ : Tape K) (s : Stmt Op Tst) (ρ : Env)
    (m : Mem K) (obs : Mem K → E) : E :=
  ((run I τ s ρ m).map obs).getD 0

/-- The observable of a run with a postcondition that fixes it. -/
theorem Runs.runVal_eq {E : Type} [Zero E] {I : Interp Op Tst K} {W : Op → List ℕ → ℕ}
    {τ : Tape K} {s : Stmt Op Tst} {ρ : Env} {m : Mem K} {B : Count Op Tst} {M : ℕ}
    {obs : Mem K → E} {x : E} (h : Runs I W τ s ρ m B M fun m' => obs m' = x) :
    runVal I τ s ρ m obs = x := by
  obtain ⟨st', hrun, -, -, hx⟩ := h
  have hr : run I τ s ρ m = some st'.mem := run_of_exec hrun
  simp [runVal, hr, hx]

/-- The observable of the linked program is that of the algorithm under the induced
interpretation, for every tape. No certificate is needed. -/
theorem runVal_link {E : Type} [Zero E] (I : Interp Lo Tst K) (T : Table Op Lo Tst) (τ : Tape K)
    (s : Stmt Op Tst) (ρ : Env) (m : Mem K) (obs : Mem K → E) :
    runVal I τ (s.link T) ρ m obs = runVal (I.link T) τ s ρ m obs := by
  rw [runVal, run_link, runVal]

namespace Profile.Certifies

variable {P : Profile Op Lo Tst} {Base : Interp Lo Tst K → Prop} {Ck : Interp Op Tst K → Prop}
  {I : Interp Lo Tst K} {ξ : Ω → Tape K} {s : Stmt Op Tst} {ρ : Env} {m : Mem K}
  {B : Count Op Tst} {M : ℕ}

/-- **The corollary for any algorithm and any certified profile, law-level form.** A law-level
theorem proved for every interpretation meeting `Ck` whose operations read the tape only in
their windows holds for the linked program over every interpretation meeting `Base` whose
operations read the tape only in theirs, with the counts pushed forward, the same workspace and
the same statement about the law. -/
theorem runsLaw (h : P.Certifies Base Ck) {Q : α → Mem K → Prop} {Φ : (Ω → α) → Prop}
    (hT : ∀ J, Ck J → (∀ o, J.TapeLocal o (P.win o)) → RunsLaw J P.ws ξ s ρ m B M Q Φ)
    (hI : Base I) (hloc : ∀ o, I.TapeLocal o (P.winLo o)) :
    RunsLaw I P.wsLo ξ (s.link P.table) ρ m (Count.push P.cost B) M Q Φ := by
  obtain ⟨X, hX, hΦ⟩ := hT _ (h.meets I hI) (h.tapeLocal I hI hloc)
  exact ⟨X, fun ω => h.transfer I (ξ ω) s ρ m B M _ (hX ω), hΦ⟩

/-- **Failure probabilities transfer**: the event that the linked program fails, exceeds its
budget or misses the postcondition is contained in that event for the algorithm under the
induced interpretation. -/
theorem measureReal_not_runs_le (h : P.Certifies Base Ck) {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ] (I : Interp Lo Tst K) (Q : Ω → Mem K → Prop) :
    μ.real {ω | ¬ Runs I P.wsLo (ξ ω) (s.link P.table) ρ m (Count.push P.cost B) M (Q ω)} ≤
      μ.real {ω | ¬ Runs (I.link P.table) P.ws (ξ ω) s ρ m B M (Q ω)} :=
  measureReal_mono fun _ hω hR => hω (h.transfer I _ s ρ m B M _ hR)

/-- A bound on the failure probability of the algorithm, for every interpretation meeting the
contracts, is a bound for the linked program. -/
theorem measureReal_not_runs_le_of (h : P.Certifies Base Ck) {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {Q : Ω → Mem K → Prop} {δ : ℝ}
    (hT : ∀ J, Ck J → (∀ o, J.TapeLocal o (P.win o)) →
      μ.real {ω | ¬ Runs J P.ws (ξ ω) s ρ m B M (Q ω)} ≤ δ)
    (hI : Base I) (hloc : ∀ o, I.TapeLocal o (P.winLo o)) :
    μ.real {ω | ¬ Runs I P.wsLo (ξ ω) (s.link P.table) ρ m (Count.push P.cost B) M (Q ω)} ≤ δ :=
  (h.measureReal_not_runs_le μ I Q).trans (hT _ (h.meets I hI) (h.tapeLocal I hI hloc))

/-- **Expectations transfer**: an expectation of an observable of the final memory, proved for
every interpretation meeting the contracts, holds for the linked program. -/
theorem integral_runVal (h : P.Certifies Base Ck) {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {obs : Mem K → ℝ} {c : ℝ}
    (hT : ∀ J, Ck J → (∀ o, J.TapeLocal o (P.win o)) →
      ∫ ω, runVal J (ξ ω) s ρ m obs ∂μ = c)
    (hI : Base I) (hloc : ∀ o, I.TapeLocal o (P.winLo o)) :
    ∫ ω, runVal I (ξ ω) (s.link P.table) ρ m obs ∂μ = c := by
  simp only [runVal_link]
  exact hT _ (h.meets I hI) (h.tapeLocal I hI hloc)

end Profile.Certifies

end NLAlib.Ops
