# Probabilistic block specifications on the operation core (stage PROB-LOGIC)

The stage note of **PROB-LOGIC** (targets: `~/nlalib-harness/pilot/prob-logic-targets.json`). It
plans the general probability layer that a randomized program on the
operation core needs when its routines draw from the tape **adaptively**: the start position of a
call, and its input, depend on the earlier draws. The first consumer is the finite-precision
shifted QR algorithm ([Eigensolvers-ShiftedQR-FiniteOps](Eigensolvers-ShiftedQR-FiniteOps.md)
§14); the second is randomized spectral bisection on Ops
([Computation-DynamicPrograms](Computation-DynamicPrograms.md) §7.1, "lazy sampling ... nothing
in Mathlib is a precedent"). The Lean docstrings mention neither algorithm. It is its own stage because it is new Ops
infrastructure with two consumers, and it lands on main before either of them. Skeleton on
`design/sqrfp-headline`, library `NLAlibScaffold`.

## 1. The gap

`Writes .total I τ c ρ F Post m` is a statement for one tape `τ`. A randomized routine meets its
contract only on a good set of tapes. Composing two randomized routines needs: the memory after
the first is a random variable; the second starts at a random position; its failure probability
from a fixed memory must transfer to that random start. Existing pieces:

* `IsTapeLaw` (independent entries, law by stream), `integral_future`, `map_windowFn`,
  `IsTapeLaw.shift` (deterministic shift), `run_follows` (a run reads only between its start and
  end positions) — `NLAlib/Ops/TapeLaw.lean`, `NLAlib/Ops/Tape.lean`;
* `Ops/Law.lean`: law-level statements of the shape `μ.real {ω | ¬ ConditionalRuns … (ξ ω) …}`,
  transferred through linking, but with no composition rule;
* `Probability/AdaptiveUnionBound.lean` (countable states) and the scaffold's U1
  (`measureReal_exists_lt_mem_le`, measurable states): union bounds over named random states,
  which a program proof would have to construct from the semantics.

Missing (searched Mathlib and `NLAlib/`): measurability of a run in its tape; the strong Markov
property of the tape at a random position; a composition rule for failure probabilities.

## 2. Design

**Memories are measurable through an observation.** `Mem.obs m` = (position, number of buffers,
buffer lengths, every cell as an initialised flag and a value). It is injective; the σ-algebra on
`Mem K` is its comap. `Interp.IsMeasurable I`: the success flag and result of every call are
measurable in (tape, memory), tests and indices in the memory. A machine whose operations are Borel
functions gives one (planned, PL4); a kernel's measurability is part of its contract.

**PWrites.** `PWrites law I c ρ F Pre Post φ`: there are good sets `G m` of tapes, jointly
measurable in (memory, tape) and determined by the tape from `m.pos` on, such that from every
`m` with `Pre m`, every tape of `G m` gives `Writes .total I τ c ρ F Post m`, and every tape law
with the stream laws `law` misses `G m` with probability at most `φ`. With `φ ≥ 1` it is trivial
(`G = ∅`); with `φ = 0` and `G = univ` it is the deterministic triple.

**Why good sets and not `P.real {¬ Writes …}`.** The postcondition is an arbitrary predicate, so
`{τ | ¬ Writes … Post m}` need not be measurable, and composing outer measures of sets with small
sections fails in general (Sierpiński). The good set is the measurable certificate; the failure
event of the run is contained in its complement (`PWrites.measureReal_not_writes_le`).

**The union bound is in `seq`.** For `c₁; c₂` the good set is
`{τ ∈ G₁ m | τ ∈ G₂ (m₁ τ)}` with `m₁ τ` the memory after `c₁`. Joint measurability: PL1.
Determined from `m.pos`: `run_follows` and `G₂ m₁` determined from `m₁.pos ≥ m.pos`. Probability:
`P(G₁ᶜ) + P(τ ∈ G₁, τ ∉ G₂(m₁ τ)) ≤ φ₁ + φ₂`, the second term by the strong Markov property at the
stopping time `p := m₁.pos` on success, `⊤` on failure (PL2, stated with Mathlib's
`IsStoppingTime` for `IsTapeLaw.filtration` and values in `WithTop ℕ`: a failing run has no end
position, and the clamp "`m.pos` on failure" is not a stopping time, since `{p = m.pos}` contains
the failure set, which depends on entries from `m.pos` on) and `Mid (m₁ τ)` on `G₁`. Equivalently
(the route Fable's review checked) by the per-position decomposition over `{success, pos = q}`
with `IsTapeLaw.shift` and `integral_future`; PL2 packages that decomposition once. Loops add per round. A program proof
applies the rules and never names the random state of a call.

## 3. Statements

| id | statement (Lean name) | file | diff | status |
|---|---|---|---|---|
| PL0 | `Mem.obs`, `Mem.instMeasurableSpace`, `Interp.IsMeasurable`, `Tape.DeterminedFrom`, `PWrites` (definitions) | `Ops/Logic/Probabilistic` | — | skel (defs) |
| PL1 | `Interp.IsMeasurable.measurable_eval`: success flag and final memory measurable in (tape, memory) | same | H | skel |
| PL2 | `IsTapeLaw.measure_inter_shift_mem`: for a `WithTop ℕ`-valued `IsStoppingTime h.filtration p`, an event `S` of the stopped σ-algebra and a measurable `A`, `P(S ∩ {p < ⊤, shift ξ p ∈ A}) = P(S ∩ {p < ⊤})·P(ξ ∈ A)` | `Ops/TapeStopping` | L | skel |
| PL3a | `PWrites.measureReal_not_writes_le`, `PWrites.of_writes`, `PWrites.mono` | `Ops/Logic/Probabilistic` | S | **proved** |
| PL3b | `PWrites.of_window`: a call wrong only on a bad window of `W` draws of stream `s` (`map_windowFn`) | same | M | skel |
| PL3c | `PWrites.seq` (`φ₁ + φ₂`; needs PL1, PL2, tape locality) | same | L | skel |
| PL3d | `PWrites.ite` (`max φ₁ φ₂`) | same | M | skel |
| PL3e | `PWrites.whileFuel` (`Σ φ_i + ψ`) | same | M | skel |
| PL3f | `PWrites.loop`, `PWrites.bindIdx`, `PWrites.allocs` (the mirrors of `writes_loop`, `writes_bindIdx`, `writes_allocs_preserving_post`), `PWrites.in_frame` | same | M, M, M, S | plan |
| PL4 | `Machine.IsMeasurable` (Borel operations) → measurability **per operation** of the catalog's scalar, index and comparison operations (`∀ a : ScalarOp, …(I.call (Has.inj a) …)`), plus an assembly lemma for a sum of operation types `O₁ ⊕ O₂` (a kernel's measurability comes from its own contract) | `Ops/Catalog/ScalarMeasurable` | M | plan |
| PL5 | `PBackwardStep` + `PBackwardStep.whileFuel`: a loop whose rounds are backward steps on their good sets; errors and failure probabilities both add (the probabilistic `BackwardStep.whileFuel`) | `Ops/Logic/Probabilistic` | L | plan |

| PL6 | bridge `PWrites.conditionalRunsLaw`: a probabilistic block specification gives the law-level shape of `Ops/Law.lean` (and so transfers through linking) | `Ops/Logic/Probabilistic` | S | plan |

Rule 10 placement: every statement is about Ops semantics and tape laws only.

## 4. Edge cases checked

* `PWrites` with `φ < 0`: satisfiable only if no tape law exists for `law` (non-probability
  stream laws) or the precondition is empty; with a genuine tape law it is false, so no consumer
  gets a vacuous bound. `φ ≥ 1`: trivial by `G = ∅`.
* `Tape.DeterminedFrom m.pos`: without it `seq` is false (a good set of `c₂` that looks at draws
  `c₁` already consumed is not independent of `m₁`).
* `of_window` with `W = 0`: the window is the empty vector; `Bad m` is `∅` or everything, and the
  bound is `0` or `1` — consistent.
* `ite`: the test must succeed from every memory of the precondition (`htest`), else the run fails
  on every tape and no bound below `1` holds.
* `whileFuel` at `N = 0`: only the exit block runs; the bound is `ψ`.
* PL2: a position that peeks at its own window is not a stopping time, and the lemma is false
  for it; `p = ⊤` (the call never happens) contributes nothing on either side.
* PL1: allocation changes the shape; `Mem.obs` records lengths and the buffer count, so `alloc`
  and the shape guard of `Interp.callS` are measurable.

## 5. Waves and counts

PROB-LOGIC wave 1: PL1 (H), PL2 (L), PL4 (M), PL3f-frame (S). Wave 2: PL3b–e, PL3f (loop,
bindIdx, allocs), PL6. Wave 3: PL5 (on PL3e). Open: 6 skeleton (M 3, L 2, H 1) + 7 planned
(S 2, M 4, L 1); 3 proved. Consumers: SQR-FP (C4p, P9–P11p) — they need PROB-LOGIC waves 1–3 on
main first; COMPDYN's spectral-bisection program probability (replaces its planned lazy-sampling
lemma).
