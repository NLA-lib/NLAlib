/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Static
public import NLAlib.Ops.Logic.Writes
public import NLAlib.Ops.Tape
public import NLAlib.Ops.RunMeasurable
public import NLAlib.Ops.TapeStopping

/-!
# Probabilistic block specifications

A randomized program meets its specification only on a good set of tapes. A **probabilistic block
specification** `NLAlib.Ops.PWrites` says: from every memory of the precondition, the run writes
only the footprint and ends in the postcondition for every tape of a good set, and under every
tape with the stream laws `law` the good set fails with probability at most $\varphi$. The good
set depends measurably on the memory and only on the tape from the current position on.

The rules mirror those of `NLAlib.Ops.Writes`, with failure probabilities that add: a
deterministic block has failure $0$ (`PWrites.of_writes`), a call whose result is wrong only on a
bad window of its own draws has the probability of that window (`PWrites.of_window`), and a
sequence, a branch, a counted loop and a loop with early exit add the failure probabilities of
their parts (`PWrites.seq`, `PWrites.ite`, `PWrites.whileFuel`). The union bound over adaptively
started calls is thus proved once, in `PWrites.seq`, from the strong Markov property of the tape
(`NLAlib.Ops.IsTapeLaw.measure_inter_shift_mem`, at the stopping time "end position of the
first part, `⊤` if it fails") and the measurability of runs
(`NLAlib.Ops.Interp.IsMeasurable.measurable_eval`); a program proof applies the rules and never
names the random state of a call.

## Main definitions

* `NLAlib.Ops.Interp.IsMeasurable` (memories are measurable through `NLAlib.Ops.Mem.obs`,
  `NLAlib.Ops.RunMeasurable`).
* `NLAlib.Ops.Tape.DeterminedFrom`: a set of tapes decided by the entries from a position on.
* `NLAlib.Ops.PWrites`.

## Main results

* `NLAlib.Ops.Interp.IsMeasurable.measurable_eval`: a run is measurable in its tape and memory.
* `NLAlib.Ops.PWrites.measureReal_not_writes_le`: the probability that the run misses the
  postcondition.
* `NLAlib.Ops.PStep.bind`: the union bound over the random end position of a first step, the
  core of `PWrites.seq` and `PWrites.whileFuel`.
* `NLAlib.Ops.PWrites.of_writes`, `.mono`, `.nonneg`, `.of_window`, `.seq`, `.ite`, `.whileFuel`.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- **A measurable interpretation**: the success flag and the result of every call are measurable
in the tape and the memory, and the success flag and the value of every test and index are
measurable in the memory. A machine whose operations are Borel functions gives one. -/
def Interp.IsMeasurable [Inhabited K] [MeasurableSpace K] (I : Interp Op Tst K) : Prop :=
  (∀ o d ins outs,
      Measurable (fun x : Tape K × Mem K => (I.call o d ins outs x.1 x.2).isSome) ∧
      Measurable (fun x : Tape K × Mem K => (I.call o d ins outs x.1 x.2).getD x.2)) ∧
    (∀ q d ins, Measurable (fun m : Mem K => (I.test q d ins m).isSome) ∧
      Measurable (fun m : Mem K => (I.test q d ins m).getD false)) ∧
    ∀ q ins, Measurable (fun m : Mem K => (I.index q ins m).isSome) ∧
      Measurable (fun m : Mem K => (I.index q ins m).getD 0)

/-- The call of the evaluator under a measurable interpretation is a measurable step: liveness
and the shape guard depend on the memory only through its observation. -/
theorem Interp.IsMeasurable.measurableRun_callS [Inhabited K] [MeasurableSpace K]
    {I : Interp Op Tst K} (hI : I.IsMeasurable) (o : Op) (d : List ℕ) (a b : List (ℕ × ℕ)) :
    MeasurableRun (I.callS o d a b) := by
  have e : I.callS o d a b = fun τ m => if m.Live (a ++ b) ∧ (I.call o d a b τ m).isSome = true ∧
      ((I.call o d a b τ m).getD m).store.shape = m.store.shape then
      some ((I.call o d a b τ m).getD m) else none := by
    funext τ m
    unfold Interp.callS
    by_cases hl : m.Live (a ++ b)
    · cases I.call o d a b τ m with
      | none => simp [hl]
      | some m' => by_cases hs : m'.store.shape = m.store.shape <;> simp [hl, hs]
    · simp [hl]
  rw [e]
  exact MeasurableRun.guard (g := fun x => (I.call o d a b x.1 x.2).getD x.2)
    ((measurable_snd (Mem.measurableSet_live _)).inter
      (((hI.1 o d a b).1 (measurableSet_singleton true)).inter
        (Mem.measurableSet_shape_eq (hI.1 o d a b).2 measurable_snd))) (hI.1 o d a b).2

/-- The test of a loop or a branch is measurable in the memory. -/
theorem Interp.IsMeasurable.measurable_testAt [Inhabited K] [MeasurableSpace K]
    {I : Interp Op Tst K} (hI : I.IsMeasurable) (q : Tst) (ds : List IExp) (ins : List Operand)
    (ρ : Env) : Measurable (fun m : Mem K => (I.testAt q ds ins ρ m).isSome) ∧
      Measurable (fun m : Mem K => (I.testAt q ds ins ρ m).getD false) := by
  unfold Interp.testAt
  cases IExp.evalList ρ.idx ds with
  | none => exact ⟨measurable_const, measurable_const⟩
  | some d =>
    cases Operand.evalList ρ ins with
    | none => exact ⟨measurable_const, measurable_const⟩
    | some a => exact hI.2.1 q d a

/-- **Runs are measurable**: under a measurable interpretation, the success flag and the final
memory of the run of a statement are measurable functions of the tape and the initial memory. -/
theorem Interp.IsMeasurable.measurable_eval [Inhabited K] [MeasurableSpace K]
    {I : Interp Op Tst K} (hI : I.IsMeasurable) (c : Stmt Op Tst) (ρ : Env) :
    Measurable (fun x : Tape K × Mem K => (eval I x.1 c ρ x.2).isSome) ∧
      Measurable (fun x : Tape K × Mem K => (eval I x.1 c ρ x.2).getD x.2) := by
  suffices h : ∀ ρ, MeasurableRun fun τ m => eval I τ c ρ m from h ρ
  induction c with
  | skip => exact fun _ => MeasurableRun.some_mem
  | abort => exact fun _ => MeasurableRun.none_mem
  | seq s t ihs iht => exact fun ρ => (ihs ρ).bind (iht ρ)
  | call o ds ins outs =>
    intro ρ
    simp only [eval]
    cases IExp.evalList ρ.idx ds with
    | none => exact MeasurableRun.none_mem
    | some d =>
      cases Operand.evalList ρ ins with
      | none => exact MeasurableRun.none_mem
      | some a =>
        cases Operand.evalList ρ outs with
        | none => exact MeasurableRun.none_mem
        | some b => exact hI.measurableRun_callS o d a b
  | ite q ds ins t e iht ihe =>
    intro ρ
    simp only [eval]
    cases IExp.evalList ρ.idx ds with
    | none => exact MeasurableRun.none_mem
    | some d =>
      cases Operand.evalList ρ ins with
      | none => exact MeasurableRun.none_mem
      | some a =>
        refine MeasurableRun.bind_value false ((hI.2.1 q d a).1.comp measurable_snd)
          ((hI.2.1 q d a).2.comp measurable_snd) fun b => ?_
        cases b
        · exact ihe ρ
        · exact iht ρ
  | whileFuel fuel q ds ins body k ih ihk =>
    intro ρ
    simp only [eval]
    cases fuel.eval ρ.idx with
    | none => exact MeasurableRun.none_mem
    | some n =>
      exact MeasurableRun.whileIter (fun i => hI.measurable_testAt q ds ins (ρ.pushIdx i))
        (fun i => ih (ρ.pushIdx i)) (fun j => ihk (ρ.pushIdx j)) n 0
  | bindIdx q ins bound body ih =>
    intro ρ
    simp only [eval]
    cases Operand.evalList ρ ins with
    | none => exact MeasurableRun.none_mem
    | some a =>
      cases bound.eval ρ.idx with
      | none => exact MeasurableRun.none_mem
      | some B =>
        simp only [Option.bind_some]
        exact MeasurableRun.bind_value 0 ((hI.2.2 q a).1.comp measurable_snd)
          ((hI.2.2 q a).2.comp measurable_snd) fun v =>
            MeasurableRun.ite (p := fun _ _ => v ≤ B) (MeasurableSet.const _) (ih _)
              MeasurableRun.none_mem
  | allocAs fmt len body ih =>
    intro ρ
    simp only [eval]
    cases len.eval ρ.idx with
    | none => exact MeasurableRun.none_mem
    | some n =>
      exact MeasurableRun.indexed (v := fun _ m => m.store.length)
        (Mem.measurable_length.comp measurable_snd) fun j =>
          ((ih (ρ.pushBuf j)).comp (h := fun _ m => ⟨m.store.push n, m.pos⟩)
            ((Mem.measurable_push n).comp measurable_snd)).map Mem.measurable_pop
  | loop n body ih =>
    intro ρ
    simp only [eval]
    cases n.eval ρ.idx with
    | none => exact MeasurableRun.none_mem
    | some k => exact MeasurableRun.iter (fun i => ih (ρ.pushIdx i)) k
  | frame ds args body ih =>
    intro ρ
    simp only [eval]
    cases IExp.evalList ρ.idx ds with
    | none => exact MeasurableRun.none_mem
    | some d =>
      cases Operand.evalList ρ args with
      | none => exact MeasurableRun.none_mem
      | some a =>
        exact MeasurableRun.ite (p := fun _ m => m.Live a)
          (measurable_snd (Mem.measurableSet_live a)) (ih _) MeasurableRun.none_mem

/-- A set of tapes is **determined from the position** `p`: two tapes that agree at every position
from `p` on are both in it or both not. -/
def Tape.DeterminedFrom (p : ℕ) (G : Set (Tape K)) : Prop :=
  ∀ τ τ' : Tape K, (∀ q, p ≤ q → τ q = τ' q) → (τ ∈ G ↔ τ' ∈ G)

/-- **A probabilistic block specification**: there are good sets of tapes `G m`, jointly
measurable in the memory and the tape and determined from the position of `m`, such that from
every memory `m` of the precondition the run of `c` writes only `F` and ends in `Post` for every
tape of `G m`, and under every tape with the stream laws `law` the tape misses `G m` with
probability at most $\varphi$. -/
def PWrites [Inhabited K] [MeasurableSpace K] (law : ℕ → Measure K) (I : Interp Op Tst K)
    (c : Stmt Op Tst) (ρ : Env) (F : Fp) (Pre Post : Mem K → Prop) (φ : ℝ) : Prop :=
  ∃ G : Mem K → Set (Tape K), MeasurableSet {x : Mem K × Tape K | x.2 ∈ G x.1} ∧
    (∀ m, Tape.DeterminedFrom m.pos (G m)) ∧
    ∀ m, Pre m → (∀ τ ∈ G m, Writes .total I τ c ρ F Post m) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (ξ : Ω → Tape K), IsTapeLaw law P ξ →
        P.real {ω | ξ ω ∉ G m} ≤ φ

/-- The probability that the tape misses a set that depends measurably on a parameter is
measurable in the parameter. -/
theorem IsTapeLaw.measurable_measure_notMem [MeasurableSpace K] {law : ℕ → Measure K}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape K} (hξ : IsTapeLaw law P ξ)
    {α : Type} [MeasurableSpace α] {G : α → Set (Tape K)}
    (hG : MeasurableSet {x : α × Tape K | x.2 ∈ G x.1}) :
    Measurable fun a => P {ω | ξ ω ∉ G a} := by
  have := hξ.isProbabilityMeasure
  convert measurable_measure_prodMk_left (ν := P.map ξ) hG.compl using 1
  funext a
  rw [Measure.map_apply hξ.measurable_tape (measurable_prodMk_left hG.compl)]
  rfl

/-! ### Probabilistic step specifications -/

/-- **A probabilistic step specification**: there are good sets of tapes `G m`, jointly
measurable in the memory and the tape and determined from the position of `m`, such that from
every memory `m` of the precondition the step `f` succeeds with a result `m'` related to `m` by
`Q m m'` for every tape of `G m`, and under every tape with the stream laws `law` the tape misses
`G m` with probability at most $\varphi$. `NLAlib.Ops.PWrites` is the case of a run. -/
def PStep [Inhabited K] [MeasurableSpace K] (law : ℕ → Measure K)
    (f : Tape K → Mem K → Option (Mem K)) (Pre : Mem K → Prop) (Q : Mem K → Mem K → Prop)
    (φ : ℝ) : Prop :=
  ∃ G : Mem K → Set (Tape K), MeasurableSet {x : Mem K × Tape K | x.2 ∈ G x.1} ∧
    (∀ m, Tape.DeterminedFrom m.pos (G m)) ∧
    ∀ m, Pre m → (∀ τ ∈ G m, ∃ m', f τ m = some m' ∧ Q m m') ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (ξ : Ω → Tape K), IsTapeLaw law P ξ →
        P.real {ω | ξ ω ∉ G m} ≤ φ

namespace PStep

variable [Inhabited K] [MeasurableSpace K] {law : ℕ → Measure K}
  {f g : Tape K → Mem K → Option (Mem K)} {Pre : Mem K → Prop} {Q : Mem K → Mem K → Prop}
  {φ : ℝ}

/-- **Consequence** for step specifications. -/
theorem mono {Pre' : Mem K → Prop} {Q' : Mem K → Mem K → Prop} {φ' : ℝ}
    (h : PStep law f Pre Q φ) (hPre : ∀ m, Pre' m → Pre m)
    (hQ : ∀ m m', Pre' m → Q m m' → Q' m m') (hφ : φ ≤ φ') : PStep law f Pre' Q' φ' := by
  obtain ⟨G, hGm, hGd, hG⟩ := h
  refine ⟨G, hGm, hGd, fun m hm => ⟨fun τ hτ => ?_,
    fun P ξ hξ => ((hG m (hPre m hm)).2 P ξ hξ).trans hφ⟩⟩
  obtain ⟨m', h1, h2⟩ := (hG m (hPre m hm)).1 τ hτ
  exact ⟨m', h1, hQ m m' hm h2⟩

/-- The probability of the bad set of the second step, at the memory after a first step that
reads the tape only up to its end position: it is at most $\varphi_2 \ge 0$. The union bound over
the end positions $q$ uses `NLAlib.Ops.IsTapeLaw.measure_past_shift_mem` at each $q$. -/
theorem measure_exists_bind_bad_le (hfm : MeasurableRun f) (hff : ∀ τ τ', Follows τ τ' (f τ) (f τ'))
    {G₂ : Mem K → Set (Tape K)} (hG₂m : MeasurableSet {x : Mem K × Tape K | x.2 ∈ G₂ x.1})
    (hG₂d : ∀ m, Tape.DeterminedFrom m.pos (G₂ m)) {Mid : Mem K → Prop} {φ₂ : ℝ} (hφ₂ : 0 ≤ φ₂)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape K} (hξ : IsTapeLaw law P ξ)
    (hG₂ : ∀ m', Mid m' → P.real {ω | ξ ω ∉ G₂ m'} ≤ φ₂) (m : Mem K) :
    P {ω | ∃ m', f (ξ ω) m = some m' ∧ Mid m' ∧ ξ ω ∉ G₂ m'} ≤ ENNReal.ofReal φ₂ := by
  have := hξ.isProbabilityMeasure
  have hξm := hξ.measurable_tape
  have hmeasF := hξ.measurable_measure_notMem hG₂m
  set M₂ := {m' : Mem K | P {ω | ξ ω ∉ G₂ m'} ≤ ENNReal.ofReal φ₂}
  have hM₂ : MeasurableSet M₂ := measurableSet_le hmeasF measurable_const
  have hmid : ∀ m', Mid m' → m' ∈ M₂ := fun m' hm' =>
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hφ₂).mpr (hG₂ m' hm')
  -- the state after the first step, read off the tape cut at `q`
  let X : ℕ → Ω → Bool × Mem K := fun q ω =>
    ((f ((ξ ω).cut q) m).isSome, (f ((ξ ω).cut q) m).getD m)
  have hX : ∀ q, Measurable[Tape.past ξ q] (X q) := fun q =>
    have hc : Measurable[Tape.past ξ q] fun ω => ((ξ ω).cut q, m) :=
      (Tape.measurable_cut q).prodMk measurable_const
    (hfm.1.comp hc).prodMk (hfm.2.comp hc)
  have hXm : ∀ q, Measurable (X q) := fun q => (hX q).mono (hξ.sigma_le _) le_rfl
  let B : ℕ → Set ((Bool × Mem K) × Tape K) := fun q =>
    {y | y.1.1 = true ∧ y.1.2.pos = q ∧ y.1.2 ∈ M₂ ∧ y.2.unshift q ∉ G₂ y.1.2}
  have hB : ∀ q, MeasurableSet (B q) := fun q =>
    (measurable_fst.fst (measurableSet_singleton true)).inter
      (((Mem.measurable_pos.comp measurable_fst.snd) (measurableSet_singleton q)).inter
        ((measurable_fst.snd hM₂).inter
          ((measurable_fst.snd.prodMk ((Tape.measurable_unshift q).comp measurable_snd))
            hG₂m.compl)))
  let Fq : ℕ → Set Ω := fun q => {ω | (X q ω).1 = true ∧ (X q ω).2.pos = q}
  have hFq : ∀ q, MeasurableSet (Fq q) := fun q => (hXm q)
    ((measurable_fst (measurableSet_singleton true)).inter
      ((Mem.measurable_pos.comp measurable_snd) (measurableSet_singleton q)))
  -- each end position contributes at most `φ₂` times its probability
  have hE : ∀ q, P {ω | (X q ω, (ξ ω).shift q) ∈ B q} ≤ ENNReal.ofReal φ₂ * P (Fq q) := by
    intro q
    rw [hξ.measure_past_shift_mem (hX q) (hB q), ← lintegral_indicator_const (hFq q)]
    refine lintegral_mono fun ω => ?_
    by_cases hω : ω ∈ Fq q
    · rw [Set.indicator_of_mem hω]
      by_cases hM : (X q ω).2 ∈ M₂
      · refine le_trans (measure_mono fun ω' hω' => ?_) hM
        obtain ⟨-, hpos, -, hn⟩ := hω'
        exact fun hmem => hn ((hG₂d _ _ _ fun j hj =>
          Tape.unshift_shift_of_le (ξ ω') (hpos ▸ hj)).mpr hmem)
      · exact (measure_mono (t := ∅) fun ω' (h : ω' ∈ {ω' | (X q ω, (ξ ω').shift q) ∈ B q}) =>
          (hM h.2.2.1).elim).trans (by simp)
    · rw [Set.indicator_of_notMem hω]
      exact (measure_mono (t := ∅) fun ω' (h : ω' ∈ {ω' | (X q ω, (ξ ω').shift q) ∈ B q}) =>
        (hω ⟨h.1, h.2.1⟩).elim).trans (by simp)
  -- the end positions are disjoint events
  let F' : ℕ → Set Ω := fun q =>
    {ω | (f (ξ ω) m).isSome = true ∧ ((f (ξ ω) m).getD m).pos = q}
  have hum : Measurable fun ω => (ξ ω, m) := hξm.prodMk measurable_const
  have hF' : ∀ q, MeasurableSet (F' q) := fun q =>
    ((hfm.1.comp hum) (measurableSet_singleton true)).inter
      ((Mem.measurable_pos.comp (hfm.2.comp hum)) (measurableSet_singleton q))
  have hsub : ∀ q, Fq q ⊆ F' q := by
    intro q ω ⟨h1, h2⟩
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h1
    have h2' : b.pos = q := by simpa [X, hb] using h2
    have := Follows.eq_of_cut hff hb h2'.le
    exact ⟨by simp [this], by simp [this, h2']⟩
  have hsum : ∑' q, P (Fq q) ≤ 1 := by
    calc ∑' q, P (Fq q) ≤ ∑' q, P (F' q) := ENNReal.tsum_le_tsum fun q => measure_mono (hsub q)
      _ = P (⋃ q, F' q) := (measure_iUnion (fun i j hij => Set.disjoint_left.mpr
          fun ω h1 h2 => hij (h1.2.symm.trans h2.2)) hF').symm
      _ ≤ 1 := prob_le_one
  -- the bad event lies in the union of the per-position events
  have hcov : {ω | ∃ m', f (ξ ω) m = some m' ∧ Mid m' ∧ ξ ω ∉ G₂ m'} ⊆
      ⋃ q, {ω | (X q ω, (ξ ω).shift q) ∈ B q} := by
    rintro ω ⟨m', hf', hmid', hn⟩
    refine Set.mem_iUnion.mpr ⟨m'.pos, ?_⟩
    have hc := Follows.cut_of_eq hff hf' le_rfl
    simp only [X, B, Set.mem_ofPred_eq, hc, Option.isSome_some, Option.getD_some, true_and]
    exact ⟨hmid m' hmid', fun hmem => hn ((hG₂d _ _ _ fun j hj =>
      Tape.unshift_shift_of_le (ξ ω) hj).mp hmem)⟩
  calc P {ω | ∃ m', f (ξ ω) m = some m' ∧ Mid m' ∧ ξ ω ∉ G₂ m'}
      ≤ ∑' q, P {ω | (X q ω, (ξ ω).shift q) ∈ B q} := (measure_mono hcov).trans
        (measure_iUnion_le _)
    _ ≤ ∑' q, ENNReal.ofReal φ₂ * P (Fq q) := ENNReal.tsum_le_tsum hE
    _ = ENNReal.ofReal φ₂ * ∑' q, P (Fq q) := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal φ₂ := by
        calc ENNReal.ofReal φ₂ * ∑' q, P (Fq q) ≤ ENNReal.ofReal φ₂ * 1 := by gcongr
          _ = ENNReal.ofReal φ₂ := mul_one _

/-- **Sequence of steps**: if the first step reads the tape only up to its end position and is
measurable, the failure probabilities add; the second must have $\varphi_2 \ge 0$. -/
theorem bind (hfm : MeasurableRun f) (hff : ∀ τ τ', Follows τ τ' (f τ) (f τ'))
    {Mid : Mem K → Prop} {Q₁ Q₂ : Mem K → Mem K → Prop} {φ₁ φ₂ : ℝ}
    (h₁ : PStep law f Pre Q₁ φ₁) (hmid : ∀ m m', Pre m → Q₁ m m' → Mid m')
    (h₂ : PStep law g Mid Q₂ φ₂) (hφ₂ : 0 ≤ φ₂) :
    PStep law (fun τ m => (f τ m).bind (g τ)) Pre (fun m m'' => ∃ m', Q₁ m m' ∧ Q₂ m' m'')
      (φ₁ + φ₂) := by
  obtain ⟨G₁, hG₁m, hG₁d, hG₁⟩ := h₁
  obtain ⟨G₂, hG₂m, hG₂d, hG₂⟩ := h₂
  refine ⟨fun m => {τ | τ ∈ G₁ m ∧ τ ∈ G₂ ((f τ m).getD m)}, ?_, ?_, fun m hm => ⟨?_, ?_⟩⟩
  · exact hG₁m.inter ((hfm.2.comp measurable_swap).prodMk measurable_snd hG₂m)
  · intro m τ τ' h
    have he := Follows.eq_of_agree hff h
    have hpos := Follows.pos_le_getD hff τ m
    simp only [Set.mem_ofPred_eq, ← he]
    exact and_congr (hG₁d m τ τ' h) (hG₂d _ τ τ' fun j hj => h j (hpos.trans hj))
  · rintro τ ⟨h1, h2⟩
    obtain ⟨m', hf', hq₁⟩ := (hG₁ m hm).1 τ h1
    rw [hf', Option.getD_some] at h2
    obtain ⟨m'', hg', hq₂⟩ := (hG₂ m' (hmid m m' hm hq₁)).1 τ h2
    exact ⟨m'', by simp [hf', hg'], m', hq₁, hq₂⟩
  · intro Ω _ P ξ hξ
    have := hξ.isProbabilityMeasure
    have hbad := measure_exists_bind_bad_le hfm hff hG₂m hG₂d hφ₂ hξ
      (fun m' hm' => (hG₂ m' hm').2 P ξ hξ) m
    have hcov : {ω | ξ ω ∉ {τ | τ ∈ G₁ m ∧ τ ∈ G₂ ((f τ m).getD m)}} ⊆
        {ω | ξ ω ∉ G₁ m} ∪ {ω | ∃ m', f (ξ ω) m = some m' ∧ Mid m' ∧ ξ ω ∉ G₂ m'} := by
      intro ω hω
      by_cases h1 : ξ ω ∈ G₁ m
      · obtain ⟨m', hf', hq₁⟩ := (hG₁ m hm).1 _ h1
        refine Or.inr ⟨m', hf', hmid m m' hm hq₁, fun h2 => hω ⟨h1, ?_⟩⟩
        rwa [hf', Option.getD_some]
      · exact Or.inl h1
    have hle : P {ω | ξ ω ∉ {τ | τ ∈ G₁ m ∧ τ ∈ G₂ ((f τ m).getD m)}} ≤
        P {ω | ξ ω ∉ G₁ m} + ENNReal.ofReal φ₂ :=
      (measure_mono hcov).trans ((measure_union_le _ _).trans (add_le_add_right hbad _))
    calc P.real {ω | ξ ω ∉ {τ | τ ∈ G₁ m ∧ τ ∈ G₂ ((f τ m).getD m)}}
        ≤ (P {ω | ξ ω ∉ G₁ m} + ENNReal.ofReal φ₂).toReal :=
          ENNReal.toReal_mono (by simp [measure_ne_top]) hle
      _ = P.real {ω | ξ ω ∉ G₁ m} + φ₂ := by
          rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hφ₂]
          rfl
      _ ≤ φ₁ + φ₂ := by linarith [(hG₁ m hm).2 P ξ hξ]

/-- **Branch on a measurable test** that succeeds from every memory of the precondition: the
failure bound is the larger of the two. -/
theorem bind_test {T : Mem K → Option Bool} (hT₁ : Measurable fun m => (T m).isSome)
    (hT₂ : Measurable fun m => (T m).getD false) {F : Bool → Tape K → Mem K → Option (Mem K)}
    {φ : Bool → ℝ} (htest : ∀ m, Pre m → ∃ b, T m = some b)
    (hF : ∀ b, PStep law (F b) (fun m => Pre m ∧ T m = some b) Q (φ b)) :
    PStep law (fun τ m => (T m).bind fun b => F b τ m) Pre Q (max (φ true) (φ false)) := by
  choose G hGm hGd hG using hF
  have hS : MeasurableSet {m : Mem K | T m = some true} := by
    have e : {m : Mem K | T m = some true} =
        {m | (T m).isSome = true} ∩ {m | (T m).getD false = true} := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      generalize T m = o
      cases o with
      | none => simp
      | some b => cases b <;> simp
    rw [e]
    exact (hT₁ (measurableSet_singleton true)).inter (hT₂ (measurableSet_singleton true))
  refine ⟨fun m => if T m = some true then G true m else G false m, ?_, fun m => ?_,
    fun m hm => ?_⟩
  · have e : {x : Mem K × Tape K | x.2 ∈ (fun m => if T m = some true then G true m
        else G false m) x.1} = (Prod.fst ⁻¹' {m | T m = some true} ∩ {x | x.2 ∈ G true x.1}) ∪
        (Prod.fst ⁻¹' {m | T m = some true}ᶜ ∩ {x | x.2 ∈ G false x.1}) := by
      ext x
      by_cases h : T x.1 = some true <;> simp [h]
    rw [e]
    exact ((measurable_fst hS).inter (hGm true)).union ((measurable_fst hS.compl).inter (hGm false))
  · dsimp only
    split_ifs
    exacts [hGd true m, hGd false m]
  · obtain ⟨b, hb⟩ := htest m hm
    obtain ⟨hW, hP⟩ := hG b m ⟨hm, hb⟩
    have hGb : (if T m = some true then G true m else G false m) = G b m := by
      cases b <;> simp [hb]
    simp only [hGb]
    refine ⟨fun τ hτ => by simpa [hb] using hW τ hτ, fun P ξ hξ => (hP P ξ hξ).trans ?_⟩
    cases b
    exacts [le_max_right _ _, le_max_left _ _]

end PStep

namespace PWrites

variable [Inhabited K] [MeasurableSpace K] {law : ℕ → Measure K} {I : Interp Op Tst K}
  {c : Stmt Op Tst} {ρ : Env} {F : Fp} {Pre Post : Mem K → Prop} {φ : ℝ}

/-- **The failure probability of a run**: under a tape with the stream laws, the run from a
memory of the precondition misses the postcondition (fails, writes outside the footprint, or ends
outside `Post`) with probability at most $\varphi$. -/
theorem measureReal_not_writes_le (h : PWrites law I c ρ F Pre Post φ) {m : Mem K} (hm : Pre m)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape K} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) c ρ F Post m} ≤ φ := by
  obtain ⟨G, -, -, hG⟩ := h
  obtain ⟨hW, hP⟩ := hG m hm
  have := hξ.isProbabilityMeasure
  refine (measureReal_mono fun ω hω => ?_).trans (hP P ξ hξ)
  exact fun hmem => hω (hW _ hmem)

/-- **Failure bounds are nonnegative** once a tape law exists and the precondition holds
somewhere. -/
theorem nonneg (h : PWrites law I c ρ F Pre Post φ) {m : Mem K} (hm : Pre m) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape K} (hξ : IsTapeLaw law P ξ) : 0 ≤ φ := by
  obtain ⟨G, -, -, hG⟩ := h
  exact measureReal_nonneg.trans ((hG m hm).2 P ξ hξ)

/-- **A deterministic block** is a probabilistic one with any failure bound $\varphi \ge 0$. -/
theorem of_writes (hφ : 0 ≤ φ) (h : ∀ m τ, Pre m → Writes .total I τ c ρ F Post m) :
    PWrites law I c ρ F Pre Post φ :=
  ⟨fun _ => Set.univ, by simp, fun _ _ _ _ => Iff.rfl,
    fun m hm => ⟨fun τ _ => h m τ hm, fun P ξ _ => by simpa using hφ⟩⟩

/-- **Consequence**: a stronger precondition, a weaker postcondition, a larger footprint and a
larger failure bound. -/
theorem mono {F' : Fp} {Pre' Post' : Mem K → Prop} {φ' : ℝ} (h : PWrites law I c ρ F Pre Post φ)
    (hPre : ∀ m, Pre' m → Pre m) (hF : F ≤ F') (hPost : ∀ m, Post m → Post' m) (hφ : φ ≤ φ') :
    PWrites law I c ρ F' Pre' Post' φ' := by
  obtain ⟨G, hGm, hGd, hG⟩ := h
  refine ⟨G, hGm, hGd, fun m hm => ⟨fun τ hτ => ?_,
    fun P ξ hξ => ((hG m (hPre m hm)).2 P ξ hξ).trans hφ⟩⟩
  exact ((hG m (hPre m hm)).1 τ hτ).mono hF fun m' _ hp => hPost m' hp

/-- **A call with a bad window**: if from every memory of the precondition the run ends in the
postcondition unless the window of `W` entries of the stream `s` at the current position lies in
a bad set `Bad m`, the bad sets are jointly measurable, and each has probability at most
$\varphi$ under the product law of the stream, then the block fails with probability at most
$\varphi$. -/
theorem of_window {s W : ℕ} {Bad : Mem K → Set (Fin W → K)}
    (hBad : MeasurableSet {x : Mem K × (Fin W → K) | x.2 ∈ Bad x.1})
    (hφ : ∀ m, Pre m → (Measure.pi fun _ : Fin W => law s).real (Bad m) ≤ φ)
    (h : ∀ m τ, Pre m → Tape.windowFn τ s m.pos W ∉ Bad m → Writes .total I τ c ρ F Post m) :
    PWrites law I c ρ F Pre Post φ := by
  have hwin : Measurable fun x : Mem K × Tape K => Tape.windowFn x.2 s x.1.pos W := by
    have hp : ∀ p : ℕ, Measurable fun x : Mem K × Tape K => Tape.windowFn x.2 s p W := fun p =>
      measurable_pi_lambda _ fun j =>
        (measurable_pi_apply s).comp ((measurable_pi_apply (p + j)).comp measurable_snd)
    exact (measurable_from_prod_countable_left (f := fun y : (Mem K × Tape K) × ℕ =>
      Tape.windowFn y.1.2 s y.2 W) hp).comp (measurable_id.prodMk
        (Mem.measurable_pos.comp measurable_fst))
  refine ⟨fun m => {τ | Tape.windowFn τ s m.pos W ∉ Bad m},
    (measurable_fst.prodMk hwin hBad).compl, fun m τ τ' hττ' => ?_, fun m hm =>
      ⟨fun τ hτ => h m τ hm hτ, fun P ξ hξ => ?_⟩⟩
  · have : Tape.windowFn τ s m.pos W = Tape.windowFn τ' s m.pos W :=
      funext fun j => by simp only [Tape.windowFn, hττ' (m.pos + j) (Nat.le_add_right _ _)]
    simp only [Set.mem_ofPred_eq, this]
  · have hξm : Measurable fun ω => Tape.windowFn (ξ ω) s m.pos W :=
      measurable_pi_lambda _ fun j => hξ.measurable _ _
    have hB : MeasurableSet (Bad m) := measurable_prodMk_left hBad
    calc P.real {ω | ξ ω ∉ {τ | Tape.windowFn τ s m.pos W ∉ Bad m}}
        = (P.map fun ω => Tape.windowFn (ξ ω) s m.pos W).real (Bad m) := by
          rw [map_measureReal_apply hξm hB]
          congr 1
          ext ω
          simp
      _ ≤ φ := by rw [hξ.map_windowFn]; exact hφ m hm

/-- **Sequence**: under a measurable interpretation whose operations read the tape only in their
windows, the failure probabilities of the two parts add. The bound of the second part must be
nonnegative: a negative bound is met vacuously when its precondition is empty, and the sum would
then undercut the first part. -/
theorem seq (hI : I.IsMeasurable) {win : Op → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {c₁ c₂ : Stmt Op Tst} {F₁ F₂ : Fp} {Mid : Mem K → Prop} {φ₁ φ₂ : ℝ} (hφ₂ : 0 ≤ φ₂)
    (h₁ : PWrites law I c₁ ρ F₁ Pre Mid φ₁) (h₂ : PWrites law I c₂ ρ F₂ Mid Post φ₂) :
    PWrites law I (.seq c₁ c₂) ρ (F₁ ⊔ F₂) Pre Post (φ₁ + φ₂) :=
  (PStep.bind (f := fun τ m => eval I τ c₁ ρ m) (g := fun τ m => eval I τ c₂ ρ m)
    (hI.measurable_eval c₁ ρ) (fun τ τ' => run_follows hloc τ τ' c₁ ρ) h₁
    (fun _ _ _ hq => hq.2) h₂ hφ₂).mono (fun _ hm => hm)
    (fun _ _ _ ⟨_, ⟨e₁, _⟩, ⟨e₂, hp⟩⟩ =>
      ⟨(e₁.mono fun _ _ h => Or.inl h).trans (e₂.mono fun _ _ h => Or.inr h), hp⟩) le_rfl

/-- **Reassociation**: a block of three parts has the same specification however it is
bracketed (the runs agree on every tape). -/
theorem seq_assoc_iff {a b c : Stmt Op Tst} :
    PWrites law I (.seq (.seq a b) c) ρ F Pre Post φ ↔
      PWrites law I (.seq a (.seq b c)) ρ F Pre Post φ := by
  have e : ∀ τ m, Writes .total I τ (.seq (.seq a b) c) ρ F Post m ↔
      Writes .total I τ (.seq a (.seq b c)) ρ F Post m := fun τ m => by
    simp only [Writes, Wp, eval, Option.bind_assoc]
  constructor <;> rintro ⟨G, hGm, hGd, hG⟩
  · exact ⟨G, hGm, hGd, fun m hm =>
      ⟨fun τ hτ => (e τ m).mp ((hG m hm).1 τ hτ), (hG m hm).2⟩⟩
  · exact ⟨G, hGm, hGd, fun m hm =>
      ⟨fun τ hτ => (e τ m).mpr ((hG m hm).1 τ hτ), (hG m hm).2⟩⟩

/-- **Branch**: if the test succeeds from every memory of the precondition, the failure bound of
the branch is the larger of the two. -/
theorem ite (hI : I.IsMeasurable) {q : Tst} {ds : List IExp} {ins : List Operand}
    {t e : Stmt Op Tst} {φ₁ φ₂ : ℝ}
    (htest : ∀ m, Pre m → ∃ b, I.testAt q ds ins ρ m = some b)
    (ht : PWrites law I t ρ F (fun m => Pre m ∧ I.testAt q ds ins ρ m = some true) Post φ₁)
    (he : PWrites law I e ρ F (fun m => Pre m ∧ I.testAt q ds ins ρ m = some false) Post φ₂) :
    PWrites law I (.ite q ds ins t e) ρ F Pre Post (max φ₁ φ₂) := by
  obtain ⟨Gt, hGtm, hGtd, hGt⟩ := ht
  obtain ⟨Ge, hGem, hGed, hGe⟩ := he
  have hT := hI.measurable_testAt q ds ins ρ
  have hS : MeasurableSet {m : Mem K | I.testAt q ds ins ρ m = some true} := by
    have e : {m : Mem K | I.testAt q ds ins ρ m = some true} =
        {m | (I.testAt q ds ins ρ m).isSome = true} ∩
          {m | (I.testAt q ds ins ρ m).getD false = true} := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      generalize I.testAt q ds ins ρ m = o
      cases o with
      | none => simp
      | some b => cases b <;> simp
    rw [e]
    exact (hT.1 (measurableSet_singleton true)).inter (hT.2 (measurableSet_singleton true))
  have hwr : ∀ {m : Mem K} {τ : Tape K} {b : Bool}, I.testAt q ds ins ρ m = some b →
      Writes .total I τ (if b then t else e) ρ F Post m →
        Writes .total I τ (.ite q ds ins t e) ρ F Post m := by
    intro m τ b hb hw
    obtain ⟨d, hd, hb⟩ := Option.bind_eq_some_iff.mp hb
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hb
    exact wp_ite hd ha hb hw
  refine ⟨fun m => if I.testAt q ds ins ρ m = some true then Gt m else Ge m, ?_, fun m => ?_,
    fun m hm => ?_⟩
  · have e : {x : Mem K × Tape K | x.2 ∈ (fun m => if I.testAt q ds ins ρ m = some true then Gt m
        else Ge m) x.1} = (Prod.fst ⁻¹' {m | I.testAt q ds ins ρ m = some true} ∩
          {x | x.2 ∈ Gt x.1}) ∪
        (Prod.fst ⁻¹' {m | I.testAt q ds ins ρ m = some true}ᶜ ∩ {x | x.2 ∈ Ge x.1}) := by
      ext x
      by_cases h : I.testAt q ds ins ρ x.1 = some true <;> simp [h]
    rw [e]
    exact ((measurable_fst hS).inter hGtm).union ((measurable_fst hS.compl).inter hGem)
  · dsimp only
    split_ifs
    exacts [hGtd m, hGed m]
  · obtain ⟨b, hb⟩ := htest m hm
    cases b with
    | false =>
      have hne : ¬ I.testAt q ds ins ρ m = some true := by simp [hb]
      obtain ⟨hW, hP⟩ := hGe m ⟨hm, hb⟩
      simp only [hne, if_false]
      exact ⟨fun τ hτ => hwr hb (hW τ hτ), fun P ξ hξ => (hP P ξ hξ).trans (le_max_right _ _)⟩
    | true =>
      obtain ⟨hW, hP⟩ := hGt m ⟨hm, hb⟩
      simp only [hb, if_true]
      exact ⟨fun τ hτ => hwr hb (hW τ hτ), fun P ξ hξ => (hP P ξ hξ).trans (le_max_left _ _)⟩

/-- **The loop with early exit**: with the fuel $N$, a round from the invariant `Inv i` with a
true test fails with probability at most $\varphi_i$, and the exit block from `Inv i` with a
false test, or at the cap, fails with probability at most $\psi$; then the loop fails with
probability at most $\sum_{i < N}\varphi_i + \psi$. This is the union bound over the rounds,
whose start positions are random. -/
theorem whileFuel (hI : I.IsMeasurable) {win : Op → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {fuel : IExp} {q : Tst} {ds : List IExp}
    {ins : List Operand} {body k : Stmt Op Tst} {N : ℕ} (hn : fuel.eval ρ.idx = some N)
    {G : Fp} (Inv : ℕ → Mem K → Prop) (φ : ℕ → ℝ) {ψ : ℝ} (hφ : ∀ i < N, 0 ≤ φ i)
    (hψ : 0 ≤ ψ) (h0 : ∀ m, Pre m → Inv 0 m)
    (htest : ∀ i < N, ∀ m, Inv i m → ∃ b, I.testAt q ds ins (ρ.pushIdx i) m = some b)
    (hbody : ∀ i < N, PWrites law I body (ρ.pushIdx i) F
      (fun m => Inv i m ∧ I.testAt q ds ins (ρ.pushIdx i) m = some true) (Inv (i + 1)) (φ i))
    (hexit : ∀ i ≤ N, PWrites law I k (ρ.pushIdx i) G
      (fun m => Inv i m ∧ (i = N ∨ I.testAt q ds ins (ρ.pushIdx i) m = some false)) Post ψ) :
    PWrites law I (.whileFuel fuel q ds ins body k) ρ (F ⊔ G) Pre Post
      (∑ i ∈ Finset.range N, φ i + ψ) := by
  let T : ℕ → Mem K → Option Bool := fun i m => I.testAt q ds ins (ρ.pushIdx i) m
  let Bd : ℕ → Tape K → Mem K → Option (Mem K) := fun i τ m => eval I τ body (ρ.pushIdx i) m
  let C : ℕ → Tape K → Mem K → Option (Mem K) := fun j τ m => eval I τ k (ρ.pushIdx j) m
  -- the loop from the round `i` with `r` rounds of fuel left
  let W : ℕ → ℕ → Tape K → Mem K → Option (Mem K) := fun r i τ m =>
    (NLAlib.Ops.whileIter (fun i m => (T i m).map fun b => (b, m)) (fun i => Bd i τ) r i m).bind
      fun jm => C jm.1 τ jm.2
  have hW : ∀ r i, i + r = N → PStep law (W r i) (Inv i)
      (fun m m'' => m.store.EqOff (F ⊔ G) m''.store ∧ Post m'')
      (∑ j ∈ Finset.Ico i N, φ j + ψ) := by
    intro r
    induction r with
    | zero =>
      intro i hi
      simp only [add_zero] at hi
      subst hi
      simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
      exact PStep.mono (hexit i le_rfl) (fun m hm => ⟨hm, Or.inl rfl⟩)
        (fun _ _ _ ⟨e, hp⟩ => ⟨e.mono fun _ _ h => Or.inr h, hp⟩) le_rfl
    | succ r ih =>
      intro i hi
      have hiN : i < N := by omega
      have e : W (r + 1) i = fun τ m => (T i m).bind fun b =>
          (if b then fun τ m => (Bd i τ m).bind (W r (i + 1) τ) else C i) τ m := by
        funext τ m
        simp only [W, NLAlib.Ops.whileIter]
        cases T i m with
        | none => rfl
        | some b => cases b <;> simp [Option.bind_assoc]
      rw [e]
      have hS : 0 ≤ ∑ j ∈ Finset.Ico (i + 1) N, φ j :=
        Finset.sum_nonneg fun j hj => hφ j (Finset.mem_Ico.mp hj).2
      have hsplit : ∑ j ∈ Finset.Ico i N, φ j = φ i + ∑ j ∈ Finset.Ico (i + 1) N, φ j :=
        Finset.sum_eq_sum_Ico_succ_bot hiN _
      refine (PStep.bind_test (hI.measurable_testAt q ds ins (ρ.pushIdx i)).1
        (hI.measurable_testAt q ds ins (ρ.pushIdx i)).2
        (φ := fun b => if b then φ i + (∑ j ∈ Finset.Ico (i + 1) N, φ j + ψ) else ψ)
        (htest i hiN) fun b => ?_).mono (fun _ h => h) (fun _ _ _ h => h) ?_
      · cases b
        · exact PStep.mono (hexit i hiN.le) (fun m hm => ⟨hm.1, Or.inr hm.2⟩)
            (fun _ _ _ ⟨e, hp⟩ => ⟨e.mono fun _ _ h => Or.inr h, hp⟩) le_rfl
        · exact (PStep.bind (f := Bd i) (g := W r (i + 1)) (hI.measurable_eval body _)
            (fun τ τ' => run_follows hloc τ τ' body _) (hbody i hiN) (fun _ _ _ hq => hq.2)
            (ih (i + 1) (by omega)) (by linarith)).mono (fun _ h => h)
            (fun _ _ _ ⟨_, ⟨e₁, _⟩, ⟨e₂, hp⟩⟩ => ⟨(e₁.mono fun _ _ h => Or.inl h).trans e₂, hp⟩)
            le_rfl
      · rw [hsplit]
        exact max_le (show φ i + _ ≤ _ by linarith) (show ψ ≤ _ by linarith [hφ i hiN])
  have e : (fun τ m => eval I τ (.whileFuel fuel q ds ins body k) ρ m) = W N 0 := by
    funext τ m
    simp only [eval, hn, Option.bind_some]
    rfl
  change PStep law (fun τ m => eval I τ (.whileFuel fuel q ds ins body k) ρ m) Pre _ _
  rw [e, Finset.range_eq_Ico]
  exact (hW N 0 (zero_add N)).mono h0 (fun _ _ _ h => h) le_rfl

/-! ### Planned rules (drafted statements, PL3f and PL6) -/

/-- **The counted loop** (PL3f-loop): if round `i` from `Inv i` ends in `Inv (i + 1)`, writing
only `F`, with failure probability at most $\varphi_i \ge 0$, the loop of $N$ rounds fails with
probability at most $\sum_{i < N} \varphi_i$. With $N = 0$ the loop does nothing. -/
theorem loop (hI : I.IsMeasurable) {win : Op → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {n : IExp} {body : Stmt Op Tst} {N : ℕ} (hn : n.eval ρ.idx = some N)
    (Inv : ℕ → Mem K → Prop) (φ : ℕ → ℝ) (hφ : ∀ i < N, 0 ≤ φ i) (h0 : ∀ m, Pre m → Inv 0 m)
    (hbody : ∀ i < N, PWrites law I body (ρ.pushIdx i) F (Inv i) (Inv (i + 1)) (φ i))
    (hpost : ∀ m, Inv N m → Post m) :
    PWrites law I (.loop n body) ρ F Pre Post (∑ i ∈ Finset.range N, φ i) := by
  let f : ℕ → Tape K → Mem K → Option (Mem K) := fun i τ m => eval I τ body (ρ.pushIdx i) m
  have hk : ∀ k ≤ N, PStep law (fun τ m => NLAlib.Ops.iter (fun i => f i τ) k m) Pre
      (fun m m' => m.store.EqOff F m'.store ∧ Inv k m') (∑ i ∈ Finset.range k, φ i) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun _ => Set.univ, by simp, fun _ _ _ _ => Iff.rfl, fun m hm =>
        ⟨fun τ _ => ⟨m, rfl, Store.EqOff.refl _ _, h0 m hm⟩, fun P ξ hξ => ?_⟩⟩
      simp
    | succ k ih =>
      intro hkN
      refine (PStep.bind (f := fun τ m => NLAlib.Ops.iter (fun i => f i τ) k m) (g := f k)
        (MeasurableRun.iter (f := f) (fun i => hI.measurable_eval body (ρ.pushIdx i)) k)
        (fun τ τ' => Follows.iter (fun i => run_follows hloc τ τ' body (ρ.pushIdx i)) k)
        (ih (by omega)) (fun _ _ _ hq => hq.2) (hbody k (by omega)) (hφ k (by omega))).mono
        (fun _ h => h) (fun _ _ _ ⟨_, ⟨e₁, _⟩, ⟨e₂, hp⟩⟩ => ⟨e₁.trans e₂, hp⟩) ?_
      rw [Finset.sum_range_succ]
  change PStep law (fun τ m => eval I τ (.loop n body) ρ m) Pre _ _
  have e : (fun τ m => eval I τ (.loop n body) ρ m) =
      fun τ m => NLAlib.Ops.iter (fun i => f i τ) N m := by
    funext τ m
    simp only [eval, hn, Option.bind_some]
    rfl
  rw [e]
  exact (hk N le_rfl).mono (fun _ h => h) (fun _ _ _ h => ⟨h.1, hpost _ h.2⟩) le_rfl

/-- **The index binder** (PL3f-bindIdx): if from every memory of the precondition the index query
returns a number $v \le B$, and the body at every such $v$ fails with probability at most
$\varphi$ from the memories where the query returns $v$, the binder fails with probability at
most $\varphi$. -/
theorem bindIdx (hI : I.IsMeasurable) {q : Tst} {ins : List Operand} {bound : IExp}
    {body : Stmt Op Tst} {a : List (ℕ × ℕ)} {B : ℕ} (ha : Operand.evalList ρ ins = some a)
    (hB : bound.eval ρ.idx = some B) (hidx : ∀ m, Pre m → ∃ v ≤ B, I.index q a m = some v)
    (h : ∀ v ≤ B, PWrites law I body (ρ.pushIdx v) F (fun m => Pre m ∧ I.index q a m = some v)
      Post φ) :
    PWrites law I (.bindIdx q ins bound body) ρ F Pre Post φ := by
  have h' : ∀ v, PWrites law I body (ρ.pushIdx v) F
      (fun m => Pre m ∧ I.index q a m = some v ∧ v ≤ B) Post φ := fun v =>
    if hv : v ≤ B then (h v hv).mono (fun m hm => ⟨hm.1, hm.2.1⟩) le_rfl (fun _ h => h) le_rfl
    else ⟨fun _ => ∅, by simp, fun _ _ _ _ => Iff.rfl, fun m hm => absurd hm.2.2 hv⟩
  choose Gs hGm hGd hG using h'
  have hv : Measurable fun m : Mem K => (I.index q a m).getD 0 := (hI.2.2 q a).2
  refine ⟨fun m => Gs ((I.index q a m).getD 0) m, ?_, fun m => hGd _ m, fun m hm => ?_⟩
  · have e : {x : Mem K × Tape K | x.2 ∈ Gs ((I.index q a x.1).getD 0) x.1} =
        ⋃ j, (Prod.fst ⁻¹' {m | (I.index q a m).getD 0 = j}) ∩ {x | x.2 ∈ Gs j x.1} := by
      ext x
      simp
    rw [e]
    exact MeasurableSet.iUnion fun j => (measurable_fst (hv (measurableSet_singleton j))).inter
      (hGm j)
  · obtain ⟨v, hvB, hiv⟩ := hidx m hm
    obtain ⟨hW, hP⟩ := hG v m ⟨hm, hiv, hvB⟩
    simp only [hiv, Option.getD_some]
    exact ⟨fun τ hτ => writes_bindIdx ha hB hiv hvB (hW τ hτ), hP⟩

/-- **The index binder at a known value**: if from every memory of the precondition the index
query returns the same number $v \le B$, the binder fails with the probability of its body at
$v$. -/
theorem bindIdx_of_index_eq (hI : I.IsMeasurable) {q : Tst} {ins : List Operand}
    {bound : IExp} {body : Stmt Op Tst} {a : List (ℕ × ℕ)} {B v : ℕ}
    (ha : Operand.evalList ρ ins = some a) (hB : bound.eval ρ.idx = some B) (hvB : v ≤ B)
    (hidx : ∀ m, Pre m → I.index q a m = some v) (hφ : 0 ≤ φ)
    (h : PWrites law I body (ρ.pushIdx v) F Pre Post φ) :
    PWrites law I (.bindIdx q ins bound body) ρ F Pre Post φ := by
  refine bindIdx hI ha hB (fun m hm => ⟨v, hvB, hidx m hm⟩) fun v' _ => ?_
  by_cases hv : v' = v
  · subst hv; exact h.mono (fun m hm => hm.1) le_rfl (fun _ h => h) le_rfl
  · exact of_writes hφ fun m τ hm => by
      have := hm.2.symm.trans (hidx m hm.1); simp at this; omega

/-- **Scratch allocations** (PL3f-allocs, the mirror of `writes_allocs_preserving_post`): the
body runs on the memory with fresh buffers at the handles $L, L + 1, \dots$ above the
$L$ buffers of the memory, may write above $L$, and its postcondition survives the release of
the scratch buffers. The failure probability is the body's. -/
theorem allocs {lens : List IExp} {body : Stmt Op Tst} {ns : List ℕ}
    (hn : IExp.evalList ρ.idx lens = some ns) {Pre₁ : ℕ → Mem K → Prop}
    (hpre : ∀ m (s₁ : Store K), Pre m → s₁.length = m.store.length + ns.length →
      (∀ i (hi : i < ns.length), s₁.len (m.store.length + i) = ns[i]) →
      Store.Below m.store.length m.store s₁ → Pre₁ m.store.length ⟨s₁, m.pos⟩)
    (hkeep : ∀ m, Pre m → ∀ {s s' : Store K} {p : ℕ}, Store.Below m.store.length s s' →
      Post ⟨s, p⟩ → Post ⟨s', p⟩)
    (h : ∀ L, PWrites law I body ⟨ρ.idx, ρ.buf ++ (List.range ns.length).map (L + ·)⟩
      (F ⊔ Fp.above L) (Pre₁ L) Post φ) :
    PWrites law I (Stmt.allocs lens body) ρ F Pre Post φ := by
  choose Gs hGm hGd hG using h
  let A : Mem K → Mem K := fun m => ⟨m.store.pushAll ns, m.pos⟩
  have hA : Measurable A := Mem.measurable_pushAll ns
  refine ⟨fun m => Gs m.store.length (A m), ?_, fun m τ τ' hτ => hGd _ (A m) τ τ' hτ,
    fun m hm => ?_⟩
  · have e : {x : Mem K × Tape K | x.2 ∈ Gs x.1.store.length (A x.1)} =
        ⋃ L, (Prod.fst ⁻¹' {m : Mem K | m.store.length = L}) ∩
          ((fun x : Mem K × Tape K => (A x.1, x.2)) ⁻¹' {y | y.2 ∈ Gs L y.1}) := by
      ext x
      simp
    rw [e]
    exact .iUnion fun L =>
      (measurable_fst (Mem.measurable_length (measurableSet_singleton L))).inter
        (((hA.comp measurable_fst).prodMk measurable_snd) (hGm L))
  · have hP₁ : Pre₁ m.store.length (A m) := hpre m _ hm (Store.length_pushAll _ _)
      (fun i hi => Store.len_pushAll _ _ i hi) (Store.below_pushAll _ _)
    obtain ⟨hW, hPr⟩ := hG m.store.length (A m) hP₁
    refine ⟨fun τ hτ => ?_, hPr⟩
    obtain ⟨m'', he, hEq, hPost⟩ := hW τ hτ
    refine ⟨⟨Store.pop^[ns.length] m''.store, m''.pos⟩, by rw [eval_allocs hn, he]; rfl,
      hEq.iterate_pop, hkeep m hm (Store.below_iterate_pop _ ?_) hPost⟩
    rw [hEq.length_eq, Store.length_pushAll]

/-- **A procedure instance** (PL3f-frame): the body in the environment of the frame, from
memories in which the frame's operands are live. -/
theorem in_frame {ds : List IExp} {args : List Operand} {body : Stmt Op Tst} {d : List ℕ}
    {a : List (ℕ × ℕ)} (h : PWrites law I body (Env.frame d a) F Pre Post φ)
    (hd : IExp.evalList ρ.idx ds = some d) (ha : Operand.evalList ρ args = some a)
    (hl : ∀ m, Pre m → m.Live a) :
    PWrites law I (.frame ds args body) ρ F Pre Post φ := by
  obtain ⟨G, hGm, hGd, hG⟩ := h
  exact ⟨G, hGm, hGd, fun m hm =>
    ⟨fun τ hτ => Writes.in_frame ((hG m hm).1 τ hτ) hd ha (hl m hm), (hG m hm).2⟩⟩

/-- **The bridge to the law-level statements of `Ops/Law`** (PL6): if every successful run from
`m` is within the counts `B` and the workspace `M`, the run misses the counted postcondition
(`NLAlib.Ops.ConditionalRuns`) with probability at most $\varphi$. This is the hypothesis shape of
`NLAlib.Ops.Profile.Refines.measureReal_not_runs_le_of`, so the bound transfers through
linking. -/
theorem measureReal_not_conditionalRuns_le (h : PWrites law I c ρ F Pre Post φ) {m : Mem K}
    (hm : Pre m) {W : Op → List ℕ → ℕ} {B : Count Op Tst} {M : ℕ}
    (hcost : ∀ τ m', eval I τ c ρ m = some m' → ConditionalRuns I W τ c ρ m B M (· = m'))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape K} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ ConditionalRuns I W (ξ ω) c ρ m B M
      fun m' => m.store.EqOff F m'.store ∧ Post m'} ≤ φ := by
  obtain ⟨G, -, -, hG⟩ := h
  have := hξ.isProbabilityMeasure
  refine (measureReal_mono fun ω (hω : ω ∈ {ω | ¬ ConditionalRuns I W (ξ ω) c ρ m B M
      fun m' => m.store.EqOff F m'.store ∧ Post m'}) (hmem : ξ ω ∈ G m) => hω ?_).trans
    ((hG m hm).2 P ξ hξ)
  obtain ⟨m', he, hEq, hPost⟩ := (hG m hm).1 _ hmem
  obtain ⟨st', h1, h2, h3, h4⟩ := hcost _ m' he
  exact ⟨st', h1, h2, h3, h4 ▸ ⟨hEq, hPost⟩⟩

end PWrites

end NLAlib.Ops
