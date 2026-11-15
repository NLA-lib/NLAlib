/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Backward
public import NLAlib.Ops.Logic.Probabilistic

/-!
# Probabilistic backward steps

A **probabilistic backward step** `NLAlib.Ops.PBackwardStep` is the probabilistic form of
`NLAlib.Ops.BackwardStep`: there are good sets of tapes, as for `NLAlib.Ops.PWrites`, such that
from every memory holding a state `a` the run writes only its footprint and ends in a memory
holding a state reached from `a` with backward error at most $\varepsilon$, for every good tape;
the good set fails with probability at most $\varphi$. The good set depends on the memory only:
a good set for each state would have to be chosen measurably in the memory when a memory holds
several states, which fails in general, so the specification is not `∀ a, PWrites …`; it gives
one (`NLAlib.Ops.PBackwardStep.pwrites`).

The rules mirror those of `NLAlib.Ops.BackwardStep`: backward errors and failure probabilities
both add, and every failure bound that is added after another is nonnegative.

## Main definitions

* `NLAlib.Ops.PBackwardStep`.

## Main results

* `NLAlib.Ops.PBackwardStep.mono`, `.of_backwardStep`, `.pwrites`, `.seq`, `.loop`, `.ite`,
  `.whileFuel`.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib.Ops

variable {Op Tst K : Type} {α : Type*}

/-- **A probabilistic backward step**: there are good sets of tapes, as for
`NLAlib.Ops.PWrites`, such that from every memory holding a state `a` (`S a m`) the run of `c`
writes only `F` and ends in a memory holding a state `b` (`S' b ·`) reached from `a` with
backward error at most $\varepsilon$ (`R ε a b`) for every good tape, and the good set fails with
probability at most $\varphi$. The good set depends on the memory only, not on the state. -/
def PBackwardStep [Inhabited K] [MeasurableSpace K] (law : ℕ → Measure K)
    (I : Interp Op Tst K) (c : Stmt Op Tst) (ρ : Env) (F : Fp) (R : ℝ → α → α → Prop)
    (S S' : α → Mem K → Prop) (ε φ : ℝ) : Prop :=
  PStep law (fun τ m => eval I τ c ρ m) (fun m => ∃ a, S a m)
    (fun m m' => m.store.EqOff F m'.store ∧ ∀ a, S a m → ∃ b, R ε a b ∧ S' b m') φ

namespace PBackwardStep

variable [Inhabited K] [MeasurableSpace K] {law : ℕ → Measure K} {I : Interp Op Tst K}
  {ρ : Env} {c c' : Stmt Op Tst} {F G : Fp} {R : ℝ → α → α → Prop}
  {S S' S'' : α → Mem K → Prop} {ε ε' φ φ' : ℝ}

/-- **Weakening**: a larger footprint, larger bounds, a weaker final predicate. -/
theorem mono (hR : IsBackwardErrorRel R) (h : PBackwardStep law I c ρ F R S S' ε φ)
    (hF : F ≤ G) (hε : ε ≤ ε') (hφ : φ ≤ φ') (hS : ∀ b m, S' b m → S'' b m) :
    PBackwardStep law I c ρ G R S S'' ε' φ' :=
  PStep.mono h (fun _ h => h) (fun _ _ _ ⟨e, hq⟩ => ⟨e.mono hF, fun a ha =>
    let ⟨b, hab, hb⟩ := hq a ha
    ⟨b, hR.mono hε hab, hS b _ hb⟩⟩) hφ

/-- **A deterministic backward step on every tape** is a probabilistic one with failure $0$. -/
theorem of_backwardStep (h : ∀ τ, BackwardStep .total I τ c ρ F R S S' ε) :
    PBackwardStep law I c ρ F R S S' ε 0 := by
  refine ⟨fun _ => Set.univ, by simp, fun _ _ _ _ => Iff.rfl, fun m hm =>
    ⟨fun τ _ => ?_, fun P ξ hξ => by have := hξ.isProbabilityMeasure; simp⟩⟩
  obtain ⟨a₀, ha₀⟩ := hm
  obtain ⟨m', he, hEq, -⟩ := h τ a₀ m ha₀
  refine ⟨m', he, hEq, fun a ha => ?_⟩
  obtain ⟨m'', he', -, hb⟩ := h τ a m ha
  rw [he] at he'
  cases he'
  exact hb

/-- **Elimination**: from a memory holding a given state, a probabilistic backward step is a
probabilistic block specification. -/
theorem pwrites (h : PBackwardStep law I c ρ F R S S' ε φ) (a : α) :
    PWrites law I c ρ F (S a) (fun m' => ∃ b, R ε a b ∧ S' b m') φ :=
  PStep.mono h (fun _ hm => ⟨a, hm⟩) (fun _ _ hm ⟨e, hq⟩ => ⟨e, hq a hm⟩) le_rfl

/-- **Sequence**: backward errors and failure probabilities add; the second failure bound is
nonnegative. -/
theorem seq (hR : IsBackwardErrorRel R) (hI : I.IsMeasurable) {win : Op → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (h : PBackwardStep law I c ρ F R S S' ε φ)
    (h' : PBackwardStep law I c' ρ G R S' S'' ε' φ') (hφ' : 0 ≤ φ') :
    PBackwardStep law I (.seq c c') ρ (F ⊔ G) R S S'' (ε + ε') (φ + φ') :=
  (PStep.bind (f := fun τ m => eval I τ c ρ m) (g := fun τ m => eval I τ c' ρ m)
    (hI.measurable_eval c ρ) (fun τ τ' => run_follows hloc τ τ' c ρ) h
    (fun _ _ ⟨a, ha⟩ hq => let ⟨b, _, hb⟩ := hq.2 a ha; ⟨b, hb⟩) h' hφ').mono
    (fun _ h => h) (fun _ _ _ ⟨_, ⟨e₁, hq₁⟩, ⟨e₂, hq₂⟩⟩ =>
      ⟨(e₁.mono fun _ _ h => Or.inl h).trans (e₂.mono fun _ _ h => Or.inr h), fun a ha =>
        let ⟨b, hab, hb⟩ := hq₁ a ha
        let ⟨d, hbd, hd⟩ := hq₂ b hb
        ⟨d, hR.trans hab hbd, hd⟩⟩) le_rfl

/-- **The counted loop**: if round `i` is a probabilistic backward step from `S i` to
`S (i + 1)` with error $\varepsilon_i$ and failure $\varphi_i \ge 0$, the loop of $N$ rounds is one
with error $\sum_{i<N} \varepsilon_i$ and failure $\sum_{i<N} \varphi_i$. -/
theorem loop (hR : IsBackwardErrorRel R) (hI : I.IsMeasurable) {win : Op → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {n : IExp} {body : Stmt Op Tst} {N : ℕ}
    (hn : n.eval ρ.idx = some N) (S : ℕ → α → Mem K → Prop) (ε φ : ℕ → ℝ)
    (hφ : ∀ i < N, 0 ≤ φ i)
    (h : ∀ i < N, PBackwardStep law I body (ρ.pushIdx i) F R (S i) (S (i + 1)) (ε i) (φ i)) :
    PBackwardStep law I (.loop n body) ρ F R (S 0) (S N) (∑ i ∈ Finset.range N, ε i)
      (∑ i ∈ Finset.range N, φ i) := by
  let f : ℕ → Tape K → Mem K → Option (Mem K) := fun i τ m => eval I τ body (ρ.pushIdx i) m
  have hk : ∀ k ≤ N, PStep law (fun τ m => NLAlib.Ops.iter (fun i => f i τ) k m)
      (fun m => ∃ a, S 0 a m) (fun m m' => m.store.EqOff F m'.store ∧
        ∀ a, S 0 a m → ∃ b, R (∑ i ∈ Finset.range k, ε i) a b ∧ S k b m')
      (∑ i ∈ Finset.range k, φ i) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun _ => Set.univ, by simp, fun _ _ _ _ => Iff.rfl, fun m _ =>
        ⟨fun τ _ => ⟨m, rfl, Store.EqOff.refl _ _, fun a ha => ⟨a, by simpa using hR.refl a, ha⟩⟩,
          fun P ξ hξ => ?_⟩⟩
      simp
    | succ k ih =>
      intro hkN
      refine (PStep.bind (f := fun τ m => NLAlib.Ops.iter (fun i => f i τ) k m) (g := f k)
        (MeasurableRun.iter (f := f) (fun i => hI.measurable_eval body (ρ.pushIdx i)) k)
        (fun τ τ' => Follows.iter (fun i => run_follows hloc τ τ' body (ρ.pushIdx i)) k)
        (ih (by omega)) (fun _ _ ⟨a, ha⟩ hq => let ⟨b, _, hb⟩ := hq.2 a ha; ⟨b, hb⟩)
        (h k (by omega)) (hφ k (by omega))).mono (fun _ h => h)
        (fun _ _ _ ⟨_, ⟨e₁, hq₁⟩, ⟨e₂, hq₂⟩⟩ => ⟨e₁.trans e₂, fun a ha =>
          let ⟨b, hab, hb⟩ := hq₁ a ha
          let ⟨d, hbd, hd⟩ := hq₂ b hb
          ⟨d, by rw [Finset.sum_range_succ]; exact hR.trans hab hbd, hd⟩⟩) ?_
      rw [Finset.sum_range_succ]
  change PStep law (fun τ m => eval I τ (.loop n body) ρ m) _ _ _
  have e : (fun τ m => eval I τ (.loop n body) ρ m) =
      fun τ m => NLAlib.Ops.iter (fun i => f i τ) N m := by
    funext τ m
    simp only [eval, hn, Option.bind_some]
    rfl
  rw [e]
  exact hk N le_rfl

/-- **The branch**: if the test succeeds on the memories of `S`, and each arm is a probabilistic
backward step from `S` and its outcome, the branch is one. -/
theorem ite (hI : I.IsMeasurable) {q : Tst} {ds : List IExp} {ins : List Operand}
    {t e : Stmt Op Tst} (htest : ∀ a m, S a m → ∃ b, I.testAt q ds ins ρ m = some b)
    (ht : PBackwardStep law I t ρ F R (fun a m => S a m ∧ I.testAt q ds ins ρ m = some true) S'
      ε φ)
    (he : PBackwardStep law I e ρ F R (fun a m => S a m ∧ I.testAt q ds ins ρ m = some false) S'
      ε φ) :
    PBackwardStep law I (.ite q ds ins t e) ρ F R S S' ε φ := by
  have hT := hI.measurable_testAt q ds ins ρ
  have hbr : ∀ b : Bool, PStep law (fun τ m => if b then eval I τ t ρ m else eval I τ e ρ m)
      (fun m => (∃ a, S a m) ∧ I.testAt q ds ins ρ m = some b)
      (fun m m' => m.store.EqOff F m'.store ∧ ∀ a, S a m → ∃ b, R ε a b ∧ S' b m') φ := by
    intro b
    cases b
    · exact PStep.mono he (fun _ ⟨⟨a, ha⟩, hb⟩ => ⟨a, ha, hb⟩)
        (fun _ _ hm ⟨e, hq⟩ => ⟨e, fun a ha => hq a ⟨ha, hm.2⟩⟩) le_rfl
    · exact PStep.mono ht (fun _ ⟨⟨a, ha⟩, hb⟩ => ⟨a, ha, hb⟩)
        (fun _ _ hm ⟨e, hq⟩ => ⟨e, fun a ha => hq a ⟨ha, hm.2⟩⟩) le_rfl
  have hb := PStep.bind_test hT.1 hT.2 (fun m ⟨a, ha⟩ => htest a m ha) hbr
  rw [max_self] at hb
  change PStep law (fun τ m => eval I τ (.ite q ds ins t e) ρ m) _ _ _
  have ev : (fun τ m => eval I τ (.ite q ds ins t e) ρ m) = fun τ m =>
      (I.testAt q ds ins ρ m).bind fun b => if b then eval I τ t ρ m else eval I τ e ρ m := by
    funext τ m
    simp only [eval, Interp.testAt, Option.bind_assoc]
  rw [ev]
  exact hb

/-- **The loop with early exit of probabilistic backward steps** (PL5, the probabilistic
`NLAlib.Ops.BackwardStep.whileFuel`): with the fuel $N$, if the test at round $i < N$ succeeds
on the memories of `S i`, a round with a true test is a backward step to `S (i + 1)` with error
$\varepsilon_i \ge 0$ and failure $\varphi_i \ge 0$, and the continuation after a false test or at
the cap is one to `S'` with error $\varepsilon'$ and failure $\psi \ge 0$, then the loop is a
backward step with error $\sum_{i<N} \varepsilon_i + \varepsilon'$ and failure
$\sum_{i<N} \varphi_i + \psi$. -/
theorem whileFuel (hR : IsBackwardErrorRel R) (hI : I.IsMeasurable) {win : Op → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {fuel : IExp} {q : Tst} {ds : List IExp}
    {ins : List Operand} {body k : Stmt Op Tst} {N : ℕ} (hn : fuel.eval ρ.idx = some N)
    (S : ℕ → α → Mem K → Prop) (ε φ : ℕ → ℝ) {ψ : ℝ}
    (hε : ∀ i < N, 0 ≤ ε i) (hφ : ∀ i < N, 0 ≤ φ i) (hψ : 0 ≤ ψ)
    (htest : ∀ i < N, ∀ a m, S i a m → ∃ b, I.testAt q ds ins (ρ.pushIdx i) m = some b)
    (h : ∀ i < N, PBackwardStep law I body (ρ.pushIdx i) F R
      (fun a m => S i a m ∧ I.testAt q ds ins (ρ.pushIdx i) m = some true) (S (i + 1)) (ε i)
      (φ i))
    (hk : ∀ i < N, PBackwardStep law I k (ρ.pushIdx i) G R
      (fun a m => S i a m ∧ I.testAt q ds ins (ρ.pushIdx i) m = some false) S' ε' ψ)
    (hcap : PBackwardStep law I k (ρ.pushIdx N) G R (S N) S' ε' ψ) :
    PBackwardStep law I (.whileFuel fuel q ds ins body k) ρ (F ⊔ G) R (S 0) S'
      (∑ i ∈ Finset.range N, ε i + ε') (∑ i ∈ Finset.range N, φ i + ψ) := by
  let T : ℕ → Mem K → Option Bool := fun i m => I.testAt q ds ins (ρ.pushIdx i) m
  let Bd : ℕ → Tape K → Mem K → Option (Mem K) := fun i τ m => eval I τ body (ρ.pushIdx i) m
  let C : ℕ → Tape K → Mem K → Option (Mem K) := fun j τ m => eval I τ k (ρ.pushIdx j) m
  let W : ℕ → ℕ → Tape K → Mem K → Option (Mem K) := fun r i τ m =>
    (NLAlib.Ops.whileIter (fun i m => (T i m).map fun b => (b, m)) (fun i => Bd i τ) r i m).bind
      fun jm => C jm.1 τ jm.2
  have hW : ∀ r i, i + r = N → PStep law (W r i) (fun m => ∃ a, S i a m)
      (fun m m'' => m.store.EqOff (F ⊔ G) m''.store ∧ ∀ a, S i a m →
        ∃ b, R (∑ j ∈ Finset.Ico i N, ε j + ε') a b ∧ S' b m'')
      (∑ j ∈ Finset.Ico i N, φ j + ψ) := by
    intro r
    induction r with
    | zero =>
      intro i hi
      simp only [add_zero] at hi
      subst hi
      simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
      exact PStep.mono hcap (fun _ h => h)
        (fun _ _ _ ⟨e, hq⟩ => ⟨e.mono fun _ _ h => Or.inr h, hq⟩) le_rfl
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
      have hSε : 0 ≤ ∑ j ∈ Finset.Ico i N, ε j :=
        Finset.sum_nonneg fun j hj => hε j (Finset.mem_Ico.mp hj).2
      have hSφ : 0 ≤ ∑ j ∈ Finset.Ico (i + 1) N, φ j :=
        Finset.sum_nonneg fun j hj => hφ j (Finset.mem_Ico.mp hj).2
      have hsε := Finset.sum_eq_sum_Ico_succ_bot hiN ε
      have hsφ := Finset.sum_eq_sum_Ico_succ_bot hiN φ
      refine (PStep.bind_test (hI.measurable_testAt q ds ins (ρ.pushIdx i)).1
        (hI.measurable_testAt q ds ins (ρ.pushIdx i)).2
        (φ := fun b => if b then φ i + (∑ j ∈ Finset.Ico (i + 1) N, φ j + ψ) else ψ)
        (fun m ⟨a, ha⟩ => htest i hiN a m ha) fun b => ?_).mono (fun _ h => h)
        (fun _ _ _ h => h) ?_
      · cases b
        · exact PStep.mono (hk i hiN) (fun _ ⟨⟨a, ha⟩, hb⟩ => ⟨a, ha, hb⟩)
            (fun _ _ hm ⟨e, hq⟩ => ⟨e.mono fun _ _ h => Or.inr h, fun a ha =>
              let ⟨b, hab, hb⟩ := hq a ⟨ha, hm.2⟩
              ⟨b, hR.mono (by linarith) hab, hb⟩⟩) le_rfl
        · exact (PStep.bind (f := Bd i) (g := W r (i + 1)) (hI.measurable_eval body _)
            (fun τ τ' => run_follows hloc τ τ' body _) (h i hiN)
            (fun _ _ ⟨a, ha⟩ hq => let ⟨b, _, hb⟩ := hq.2 a ha; ⟨b, hb⟩)
            (ih (i + 1) (by omega)) (by linarith)).mono
            (fun _ ⟨⟨a, ha⟩, hb⟩ => ⟨a, ha, hb⟩)
            (fun _ _ hm ⟨_, ⟨e₁, hq₁⟩, ⟨e₂, hq₂⟩⟩ =>
              ⟨(e₁.mono fun _ _ h => Or.inl h).trans e₂, fun a ha =>
                let ⟨b, hab, hb⟩ := hq₁ a ⟨ha, hm.2⟩
                let ⟨d, hbd, hd⟩ := hq₂ b hb
                ⟨d, hR.mono (by linarith) (hR.trans hab hbd), hd⟩⟩) le_rfl
      · rw [hsφ]
        exact max_le (show φ i + _ ≤ _ by linarith) (show ψ ≤ _ by linarith [hφ i hiN])
  have e : (fun τ m => eval I τ (.whileFuel fuel q ds ins body k) ρ m) = W N 0 := by
    funext τ m
    simp only [eval, hn, Option.bind_some]
    rfl
  change PStep law (fun τ m => eval I τ (.whileFuel fuel q ds ins body k) ρ m) _ _ _
  rw [e]
  simpa only [Finset.range_eq_Ico] using hW N 0 (zero_add N)

end PBackwardStep

end NLAlib.Ops
