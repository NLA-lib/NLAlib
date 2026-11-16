/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.TapeLaw
public import Mathlib.Probability.Process.Stopping

/-!
# The tape after a stopping time

A program that reads its tape adaptively starts a subroutine at a position that depends on the
draws made so far, and on some tapes it never gets there (an earlier part fails). Such a position
is a **stopping time** of the filtration of positions (`NLAlib.Ops.IsTapeLaw.filtration`), with
values in `WithTop ℕ`, `⊤` for "never": whether it is at most $q$ is decided by the entries before
$q$. For a tape with independent entries whose law depends only on the stream
(`NLAlib.Ops.IsTapeLaw`), the tape shifted to a stopping time, on the event that it is finite,
has the law of the tape and is independent of everything decided before it (the strong Markov
property of an i.i.d. sequence). A failure bound proved for a subroutine started from a fixed
memory thus transfers to the same subroutine started at a random time.

## Main results

* `NLAlib.Ops.IsTapeLaw.measure_inter_shift_mem`: for an event $S$ of the stopped σ-algebra and a
  measurable set $A$ of tapes,
  $\mathbb{P}[S \cap \{p < \top,\ \xi \text{ shifted to } p \in A\}] =
  \mathbb{P}[S \cap \{p < \top\}]\,\mathbb{P}[\xi \in A]$.
* `NLAlib.Ops.IsTapeLaw.measure_past_shift_mem`: the same at a fixed position, for a pair of a
  function of the past and the shifted tape.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib.Ops

variable {K Ω : Type} [MeasurableSpace K] {mΩ : MeasurableSpace Ω}

/-- The tape shifted to the position `q` is a function of the entries from `q` on. -/
theorem Tape.measurable_shift {ξ : Ω → Tape K} (q : ℕ) :
    Measurable[Tape.sigma ξ (Set.Ici q)] fun ω => (ξ ω).shift q :=
  @measurable_pi_lambda _ _ _ (Tape.sigma ξ (Set.Ici q)) _ _ fun p =>
    @measurable_pi_lambda _ _ _ (Tape.sigma ξ (Set.Ici q)) _ _ fun s =>
      Tape.measurable_entry (Set.mem_Ici.mpr (Nat.le_add_right q p)) s

namespace IsTapeLaw

variable {law : ℕ → Measure K} {P : Measure Ω} {ξ : Ω → Tape K}

/-- A random tape with measurable entries is measurable. -/
theorem measurable_tape (h : IsTapeLaw law P ξ) : Measurable ξ :=
  measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun s => h.measurable i s

/-- **The law of the tape is determined by the stream laws**: it is the product of `law s` over
the positions and the streams, curried. -/
theorem map_eq (h : IsTapeLaw law P ξ) :
    P.map ξ = (Measure.infinitePi fun c : ℕ × ℕ => law c.2).map Function.curry := by
  have h1 : P.map (fun ω (c : ℕ × ℕ) => ξ ω c.1 c.2) =
      Measure.infinitePi fun c : ℕ × ℕ => law c.2 :=
    (h.hasLaw_reindex id Function.injective_id).map_eq
  rw [← h1, Measure.map_map measurable_curry (measurable_pi_lambda _ fun c => h.measurable c.1 c.2)]
  rfl

/-- The tape shifted to a fixed position has the law of the tape. -/
theorem map_shift (h : IsTapeLaw law P ξ) (q : ℕ) :
    P.map (fun ω => (ξ ω).shift q) = P.map ξ := by
  rw [(h.shift q).map_eq, h.map_eq]

/-- **A function of the past and the tape from a fixed position**: for `X` measurable with
respect to the past of `q` and a measurable set `B` of pairs, the probability that `X` and the tape
shifted to `q` lie in `B` integrates, over the value of `X`, the probability of the section. -/
theorem measure_past_shift_mem (h : IsTapeLaw law P ξ) {α : Type} [MeasurableSpace α] {q : ℕ}
    {X : Ω → α} (hX : Measurable[Tape.past ξ q] X) {B : Set (α × Tape K)}
    (hB : MeasurableSet B) :
    P {ω | (X ω, (ξ ω).shift q) ∈ B} = ∫⁻ ω, P {ω' | (X ω, (ξ ω').shift q) ∈ B} ∂P := by
  have := h.isProbabilityMeasure
  have hXm : Measurable X := hX.mono (h.sigma_le _) le_rfl
  have hW : Measurable fun ω => (ξ ω).shift q := (h.shift q).measurable_tape
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hW.aemeasurable).mp
    (h.indepFun_past_future hX (Tape.measurable_shift q))
  rw [show {ω | (X ω, (ξ ω).shift q) ∈ B} = (fun ω => (X ω, (ξ ω).shift q)) ⁻¹' B from rfl,
    ← Measure.map_apply (hXm.prodMk hW) hB, hmap, Measure.prod_apply hB,
    lintegral_map (measurable_measure_prodMk_left hB) hXm]
  refine lintegral_congr fun ω => ?_
  rw [Measure.map_apply hW (measurable_prodMk_left hB)]
  rfl

end IsTapeLaw

/-- **The strong Markov property of the tape**: let `p` be a stopping time, with values in
`WithTop ℕ`, of the filtration of positions of a tape `ξ` with independent entries of law
`law s` in the stream `s`. For an event `S` decided at time `p` (measurable for the stopped
σ-algebra) and a measurable set `A` of tapes, the event "`p` is finite, `S` holds and the tape
shifted to `p` lies in `A`" has probability $\mathbb{P}[S \cap \{p < \top\}]\,\mathbb{P}[\xi
\in A]$. -/
theorem IsTapeLaw.measure_inter_shift_mem {law : ℕ → Measure K} {P : Measure Ω}
    {ξ : Ω → Tape K} (h : IsTapeLaw law P ξ) {p : Ω → WithTop ℕ}
    (hp : IsStoppingTime h.filtration p) {S : Set Ω} (hS : MeasurableSet[hp.measurableSpace] S)
    {A : Set (Tape K)} (hA : MeasurableSet A) :
    P (S ∩ {ω | ∃ q : ℕ, p ω = q ∧ (ξ ω).shift q ∈ A}) =
      P (S ∩ {ω | p ω ≠ ⊤}) * P.map ξ A := by
  have := h.isProbabilityMeasure
  have hSq : ∀ q : ℕ, MeasurableSet[Tape.past ξ q] (S ∩ {ω | p ω = q}) := fun q =>
    (hp.measurableSet_inter_eq_iff S q).mp (hS.inter (hp.measurableSet_eq_of_countable' q))
  have hdisj : ∀ q : ℕ, Disjoint (Set.Iio q) (Set.Ici q) := fun q =>
    Set.disjoint_left.mpr fun _ h1 h2 => absurd (Set.mem_Iio.mp h1) (not_lt.mpr h2)
  have hind : ∀ q : ℕ, P (S ∩ {ω | p ω = q} ∩ {ω | (ξ ω).shift q ∈ A}) =
      P (S ∩ {ω | p ω = q}) * P.map ξ A := by
    intro q
    rw [show {ω | (ξ ω).shift q ∈ A} = (fun ω => (ξ ω).shift q) ⁻¹' A from rfl,
      (Indep_iff _ _ P).mp (h.indep_sigma (hdisj q)) _ _ (hSq q) (Tape.measurable_shift q hA),
      ← h.map_shift q, Measure.map_apply (h.shift q).measurable_tape hA]
  have hmeas : ∀ q : ℕ, MeasurableSet (S ∩ {ω | p ω = q}) := fun q => h.sigma_le _ _ (hSq q)
  have hpw : Pairwise (Function.onFun Disjoint fun q : ℕ => S ∩ {ω | p ω = q}) :=
    fun i j hij => Set.disjoint_left.mpr fun ω (h1 : ω ∈ S ∩ {ω | p ω = i})
      (h2 : ω ∈ S ∩ {ω | p ω = j}) => hij (by simpa using h1.2.symm.trans h2.2)
  have e1 : S ∩ {ω | ∃ q : ℕ, p ω = q ∧ (ξ ω).shift q ∈ A} =
      ⋃ q : ℕ, S ∩ {ω | p ω = q} ∩ {ω | (ξ ω).shift q ∈ A} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨hs, q, hq, ha⟩ => ⟨q, ⟨hs, hq⟩, ha⟩, fun ⟨q, ⟨hs, hq⟩, ha⟩ => ⟨hs, q, hq, ha⟩⟩
  have e2 : S ∩ {ω | p ω ≠ ⊤} = ⋃ q : ℕ, S ∩ {ω | p ω = q} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, WithTop.ne_top_iff_exists]
    exact ⟨fun ⟨hs, q, hq⟩ => ⟨q, hs, hq.symm⟩, fun ⟨q, hs, hq⟩ => ⟨hs, q, hq.symm⟩⟩
  rw [e1, e2, measure_iUnion (fun i j hij => (hpw hij).mono Set.inter_subset_left
      Set.inter_subset_left)
      (fun q => (hmeas q).inter (show MeasurableSet {ω | (ξ ω).shift q ∈ A} from
        h.sigma_le _ _ (Tape.measurable_shift q hA))),
    measure_iUnion hpw hmeas, ← ENNReal.tsum_mul_right]
  exact tsum_congr hind

end NLAlib.Ops
