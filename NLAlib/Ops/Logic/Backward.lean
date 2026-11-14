/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Tactic.Ring
public import NLAlib.Ops.Logic.Loop

/-!
# Backward steps

A contract of the operation core is a forward statement about one run: the output words are a
function of the input words, up to a rounding error of each operation. Many algorithms are
analysed instead **backwards**: each step returns the exact result of a slightly perturbed input,
and the perturbations of the steps add. This file states that form once, for any notion of
perturbation, so that an algorithm built from backward steps gets its backward error by
composition, not by threading an error invariant through its proof by hand.

A **backward-error relation** (`NLAlib.Ops.IsBackwardErrorRel`) is a family of relations
$R_\varepsilon$ on states, with $R_0$ reflexive, $R_{\varepsilon_1}$ followed by
$R_{\varepsilon_2}$ contained in $R_{\varepsilon_1 + \varepsilon_2}$, and $R_\varepsilon$
increasing in $\varepsilon$. A perturbed unitary similarity is one
(`NLAlib.isBackwardErrorRel_isPerturbedUnitarySimilar`).

A **backward step** (`NLAlib.Ops.BackwardStep`) is a block specification (`NLAlib.Ops.Writes`):
from every memory that holds a state $a$ (the predicate `S`), the run writes only the footprint
and ends in a memory that holds a state $b$ (the predicate `S'`) with $R_\varepsilon(a, b)$. The
predicates `S`, `S'` carry everything a step needs and keeps besides the state: the parameter
words, the capacity and separation of the views, structural facts such as a Hessenberg form.
Exact arithmetic is $\varepsilon = 0$.

The rules compose backward steps with the statements of the program logic: a sequence adds the
backward errors, a counted loop sums them over the rounds, a branch keeps the bound of its arms,
the loop with early exit sums the rounds run and the continuation.

## Main definitions

* `NLAlib.Ops.IsBackwardErrorRel`: a backward-error relation.
* `NLAlib.Ops.BackwardStep`: a block specification with a backward error.

## Main results

* `NLAlib.Ops.BackwardStep.writes_add`: a step after an accumulated backward error.
* `NLAlib.Ops.BackwardStep.skip`, `NLAlib.Ops.BackwardStep.of_exact`: exact steps, error $0$.
* `NLAlib.Ops.BackwardStep.mono`: weakening.
* `NLAlib.Ops.BackwardStep.seq`, `NLAlib.Ops.BackwardStep.loop`, `NLAlib.Ops.BackwardStep.ite`,
  `NLAlib.Ops.BackwardStep.whileFuel`: composition; a branch and the loop with early exit pass
  the outcome of the test to the arm that runs.
* `NLAlib.Ops.BackwardStep.loop_rel`: a loop whose error per round is relative to a size of the
  state (geometric growth of the bound).
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type} {α : Type*}

/-- `R` is a backward-error relation: $R_\varepsilon(a, b)$ says that $b$ is reached from $a$
with backward error at most $\varepsilon$. Backward error $0$ is reflexive, backward errors add
along a chain, and a larger bound is weaker. -/
structure IsBackwardErrorRel (R : ℝ → α → α → Prop) : Prop where
  /-- Every state is reached from itself with backward error $0$. -/
  refl : ∀ a, R 0 a a
  /-- Backward errors add along a chain. -/
  trans : ∀ {ε₁ ε₂ : ℝ} {a b c : α}, R ε₁ a b → R ε₂ b c → R (ε₁ + ε₂) a c
  /-- A larger bound is weaker. -/
  mono : ∀ {ε ε' : ℝ} {a b : α}, ε ≤ ε' → R ε a b → R ε' a b

/-- A backward step: from every memory `m` holding a state `a` (`S a m`), the run of `c`
writes only the cells of `F` and ends in a memory holding a state `b` (`S' b ·`) reached from `a`
with backward error at most `ε` (`R ε a b`). -/
def BackwardStep (md : Mode) (I : Interp Op Tst K) (τ : Tape K) (c : Stmt Op Tst) (ρ : Env)
    (F : Fp) (R : ℝ → α → α → Prop) (S S' : α → Mem K → Prop) (ε : ℝ) : Prop :=
  ∀ a m, S a m → Writes md I τ c ρ F (fun m' => ∃ b, R ε a b ∧ S' b m') m

namespace BackwardStep

variable {md : Mode} {I : Interp Op Tst K} {τ : Tape K} {ρ : Env} {c c' : Stmt Op Tst}
  {F G : Fp} {R : ℝ → α → α → Prop} {S S' S'' : α → Mem K → Prop} {ε ε' : ℝ}

/-- A step after an accumulated backward error: if the memory holds a state `b` reached from
`a` with backward error `e`, a backward step with `ε` ends in a state reached from `a` with
`e + ε`. -/
theorem writes_add (hR : IsBackwardErrorRel R) (h : BackwardStep md I τ c ρ F R S S' ε)
    {e : ℝ} {a b : α} {m : Mem K} (hab : R e a b) (hS : S b m) :
    Writes md I τ c ρ F (fun m' => ∃ d, R (e + ε) a d ∧ S' d m') m :=
  (h b m hS).mono le_rfl fun _ _ ⟨d, hbd, hd⟩ => ⟨d, hR.trans hab hbd, hd⟩

/-- Weakening: a larger footprint, a larger backward error, a weaker final predicate. -/
theorem mono (hR : IsBackwardErrorRel R) (h : BackwardStep md I τ c ρ F R S S' ε) (hF : F ≤ G)
    (hε : ε ≤ ε') (hS : ∀ b m, S' b m → S'' b m) : BackwardStep md I τ c ρ G R S S'' ε' :=
  fun a m ha => (h a m ha).mono hF fun _ _ ⟨b, hab, hb⟩ => ⟨b, hR.mono hε hab, hS b _ hb⟩

/-- An exact step is a backward step with error $0$: a block specification that ends in a
memory holding the state `f a` is one, for every backward-error relation. -/
theorem of_exact (f : α → α)
    (h : ∀ a m, S a m → Writes md I τ c ρ F (S' (f a)) m)
    (hf : ∀ a, R 0 a (f a)) : BackwardStep md I τ c ρ F R S S' 0 :=
  fun a m ha => (h a m ha).mono le_rfl fun _ _ hb => ⟨f a, hf a, hb⟩

/-- Doing nothing is a backward step with error $0$, to any predicate that the memory already
satisfies. -/
theorem skip (hR : IsBackwardErrorRel R) (hS : ∀ a m, S a m → S' a m) :
    BackwardStep md I τ .skip ρ ⊥ R S S' 0 :=
  fun a m ha => Writes.skip ⟨a, hR.refl a, hS a m ha⟩

/-- Sequence: the backward errors add, the footprints are joined. -/
theorem seq (hR : IsBackwardErrorRel R) (h : BackwardStep md I τ c ρ F R S S' ε)
    (h' : BackwardStep md I τ c' ρ G R S' S'' ε') :
    BackwardStep md I τ (.seq c c') ρ (F ⊔ G) R S S'' (ε + ε') :=
  fun _ m ha => (h _ m ha).seq fun _ _ ⟨_, hab, hb⟩ => h'.writes_add hR hab hb

/-- The counted loop: if round `i` is a backward step from `S i` to `S (i + 1)` with error
`ε i`, the loop of `N` rounds is one from `S 0` to `S N` with error $\sum_{i < N} \varepsilon_i$. -/
theorem loop (hR : IsBackwardErrorRel R) {n : IExp} {body : Stmt Op Tst} {N : ℕ}
    (hn : n.eval ρ.idx = some N) (S : ℕ → α → Mem K → Prop) (ε : ℕ → ℝ)
    (h : ∀ i < N, BackwardStep md I τ body (ρ.pushIdx i) F R (S i) (S (i + 1)) (ε i)) :
    BackwardStep md I τ (.loop n body) ρ F R (S 0) (S N) (∑ i ∈ Finset.range N, ε i) :=
  fun a m ha => writes_loop hn (fun _ => F) (fun _ _ => le_rfl)
    (fun i m' => ∃ b, R (∑ j ∈ Finset.range i, ε j) a b ∧ S i b m')
    ⟨a, by simpa using hR.refl a, ha⟩ fun i hi _ _ ⟨_, hab, hb⟩ =>
      ((h i hi).writes_add hR hab hb).mono le_rfl fun _ _ hd => by
        rwa [Finset.sum_range_succ]

/-- The branch: if the test succeeds on the memories of `S` with an outcome `c` described by
`T c`, and each arm is a backward step with error `ε` from `S` and the outcome of its arm, the
branch is one. -/
theorem ite {q : Tst} {ds : List IExp} {ins : List Operand} {t e : Stmt Op Tst}
    (T : Bool → α → Mem K → Prop)
    (htest : ∀ a m, S a m → md.Holds (I.testAt q ds ins ρ m) fun c => T c a m)
    (ht : BackwardStep md I τ t ρ F R (fun a m => S a m ∧ T true a m) S' ε)
    (he : BackwardStep md I τ e ρ F R (fun a m => S a m ∧ T false a m) S' ε) :
    BackwardStep md I τ (.ite q ds ins t e) ρ F R S S' ε :=
  fun a m ha => writes_ite_holds ((htest a m ha).mono fun c hc => by
    cases c
    · exact he a m ⟨ha, hc⟩
    · exact ht a m ⟨ha, hc⟩)

/-- The loop with early exit: the test at round $i < N$ succeeds on the memories of `S i` with an
outcome `c` described by `T i c`. If the round is a backward step from `S i` and a true outcome
to `S (i + 1)` with error $\varepsilon_i \ge 0$, the continuation after a false outcome at round
$i < N$, and after the round $N$ from `S N`, are backward steps to `S'` with error `ε'`, the loop
is a backward step from `S 0` to `S'` with error $\sum_{i < N} \varepsilon_i + \varepsilon'$. -/
theorem whileFuel (hR : IsBackwardErrorRel R) {fuel : IExp} {q : Tst} {ds : List IExp}
    {ins : List Operand} {body k : Stmt Op Tst} {N : ℕ} (hn : fuel.eval ρ.idx = some N)
    (S : ℕ → α → Mem K → Prop) (T : ℕ → Bool → α → Mem K → Prop) (ε : ℕ → ℝ)
    (hε : ∀ i < N, 0 ≤ ε i)
    (htest : ∀ i < N, ∀ a m, S i a m →
      md.Holds (I.testAt q ds ins (ρ.pushIdx i) m) fun c => T i c a m)
    (h : ∀ i < N, BackwardStep md I τ body (ρ.pushIdx i) F R
      (fun a m => S i a m ∧ T i true a m) (S (i + 1)) (ε i))
    (hk : ∀ i < N, BackwardStep md I τ k (ρ.pushIdx i) G R
      (fun a m => S i a m ∧ T i false a m) S' ε')
    (hcap : BackwardStep md I τ k (ρ.pushIdx N) G R (S N) S' ε') :
    BackwardStep md I τ (.whileFuel fuel q ds ins body k) ρ (F ⊔ G) R (S 0) S'
      (∑ i ∈ Finset.range N, ε i + ε') := by
  intro a m ha
  have hsum : ∀ i ≤ N, ∑ j ∈ Finset.range i, ε j ≤ ∑ j ∈ Finset.range N, ε j := fun i hi =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hi)
      fun j hj _ => hε j (Finset.mem_range.mp hj)
  have hexit : ∀ i ≤ N, ∀ {P : α → Mem K → Prop}, BackwardStep md I τ k (ρ.pushIdx i) G R P S' ε' →
      ∀ b m', R (∑ j ∈ Finset.range i, ε j) a b → P b m' →
      Writes md I τ k (ρ.pushIdx i) G
        (fun m'' => ∃ d, R (∑ j ∈ Finset.range N, ε j + ε') a d ∧ S' d m'') m' :=
    fun i hi _ hki b m' hab hb => (hki.writes_add hR hab hb).mono le_rfl
      fun _ _ ⟨d, had, hd⟩ => ⟨d, hR.mono (by linarith [hsum i hi]) had, hd⟩
  refine writes_whileFuel hn (fun _ => F) (fun _ _ => le_rfl) G
    (fun i m' => ∃ b, R (∑ j ∈ Finset.range i, ε j) a b ∧ S i b m') _
    ⟨a, by simpa using hR.refl a, ha⟩ (fun i hi m' _ ⟨b, hab, hb⟩ => ?_)
    fun m' _ ⟨b, hab, hb⟩ => hexit N le_rfl hcap b m' hab hb
  refine (htest i hi b m' hb).mono fun c hc => ?_
  cases c
  · exact hexit i hi.le (hk i hi) b m' hab ⟨hb, hc⟩
  · exact ((h i hi).writes_add hR hab ⟨hb, hc⟩).mono le_rfl fun _ _ hd => by
      rwa [Finset.sum_range_succ]

/-- A counted loop with a relative backward error: let $g$ be a size of the states that grows by
at most the backward error ($R_\varepsilon(a, b)$ implies $g(b) \le g(a) + \varepsilon$). If round
$i$ is, for every bound $M$, a backward step from `S i` and $g \le M$ to `S (i + 1)` with error
$\nu M$, then $N$ rounds from `S 0` and $g \le M_0$ end in `S N` with
$g \le (1 + \nu)^N M_0$, with error $(1 + \nu)^N M_0 - M_0$. -/
theorem loop_rel (hR : IsBackwardErrorRel R) {n : IExp} {body : Stmt Op Tst} {N : ℕ}
    (hn : n.eval ρ.idx = some N) (S : ℕ → α → Mem K → Prop) (g : α → ℝ)
    (hg : ∀ {ε : ℝ} {a b : α}, R ε a b → g b ≤ g a + ε) (ν M₀ : ℝ)
    (h : ∀ i < N, ∀ M : ℝ, BackwardStep md I τ body (ρ.pushIdx i) F R
      (fun a m => S i a m ∧ g a ≤ M) (S (i + 1)) (ν * M)) :
    BackwardStep md I τ (.loop n body) ρ F R (fun a m => S 0 a m ∧ g a ≤ M₀)
      (fun b m => S N b m ∧ g b ≤ (1 + ν) ^ N * M₀) ((1 + ν) ^ N * M₀ - M₀) := by
  have hl := loop (F := F) hR hn (fun i a m => S i a m ∧ g a ≤ (1 + ν) ^ i * M₀)
    (fun i => ν * ((1 + ν) ^ i * M₀)) fun i hi a m ha =>
      (h i hi _ a m ha).mono le_rfl fun _ _ ⟨b, hab, hb⟩ =>
        have key : (1 + ν) ^ (i + 1) * M₀ = (1 + ν) ^ i * M₀ + ν * ((1 + ν) ^ i * M₀) := by
          ring
        ⟨b, hab, hb, by linarith [hg hab, ha.2]⟩
  have hsum : ∀ N : ℕ,
      ∑ i ∈ Finset.range N, ν * ((1 + ν) ^ i * M₀) = (1 + ν) ^ N * M₀ - M₀ := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  simpa [hsum] using hl

end BackwardStep

end NLAlib.Ops
