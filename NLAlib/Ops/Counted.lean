/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Rules

/-!
# Counts in the logic, where they depend on the data

The counts of a program are its static cost (`NLAlib.Ops.Runs.of_run`), and the logic `Wp` does
not carry them. The exception is a loop whose number of rounds depends on the data: its static
cost is the fuel, which is only an upper bound. `NLAlib.Ops.RunsFrom` is the judgment that
carries counts: a counted run from a state, within given counts and workspace. It has a rule for
`whileFuel` with the number of rounds bounded by the mathematics
(`NLAlib.Ops.RunsFrom.whileFuel`), a rule for sequences, and takes everything else from `Wp`
with its static cost (`NLAlib.Ops.RunsFrom.of_wp`). A `RunsFrom` from the initial state is a
`Runs` (`NLAlib.Ops.RunsFrom.runs`), which linking transfers as usual: the bound is an ordinary
count, whatever it depends on.

## Main results

* `NLAlib.Ops.RunsFrom.whileFuel`: a loop while a test holds, with its counts.
* `NLAlib.Ops.RunsFrom.of_wp`, `NLAlib.Ops.RunsFrom.seq`, `NLAlib.Ops.RunsFrom.runs`: the rest.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- **A counted run from a state**: the counted run of `s` from `st` succeeds, adds at most the
counts `c`, stays within the workspace `p` above the live cells, and `Q` holds of the final
memory. -/
def RunsFrom (I : Interp Op Tst K) (W : Op → List ℕ → ℕ) (τ : Tape K) (s : Stmt Op Tst) (ρ : Env)
    (st : St Op Tst K) (c : Count Op Tst) (p : ℕ) (Q : Mem K → Prop) : Prop :=
  ∃ st', exec I W τ s ρ st = some st' ∧ St.Within st st' c p ∧ Q st'.mem

namespace RunsFrom

variable {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} {τ : Tape K} {ρ : Env} {st : St Op Tst K}
  {c c' : Count Op Tst} {p p' : ℕ} {Q Q' : Mem K → Prop}

/-- Everything whose counts do not depend on the data: a total `Wp` and the static cost. -/
theorem of_wp {s : Stmt Op Tst} (h : Wp .total I τ s ρ Q st.mem) :
    RunsFrom I W τ s ρ st (staticCost s ρ.idx) (staticPeak W s ρ.idx) Q := by
  obtain ⟨m', hrun, hQ⟩ := h
  obtain ⟨st', hst, hm⟩ := exec_eq_some_of_run hrun W st rfl
  exact ⟨st', hst, exec_within hst, hm ▸ hQ⟩

theorem mono {s : Stmt Op Tst} (h : RunsFrom I W τ s ρ st c p Q) (hc : c ≤ c') (hp : p ≤ p')
    (hQ : ∀ m, Q m → Q' m) : RunsFrom I W τ s ρ st c' p' Q' := by
  obtain ⟨st', h1, h2, h3⟩ := h
  exact ⟨st', h1, h2.mono hc hp, hQ _ h3⟩

/-- Sequence: the counts add up, the workspaces take their maximum. -/
theorem seq {s t : Stmt Op Tst} (h : RunsFrom I W τ s ρ st c p Q')
    (h' : ∀ st', Q' st'.mem → RunsFrom I W τ t ρ st' c' p' Q) :
    RunsFrom I W τ (.seq s t) ρ st (c + c') (max p p') Q := by
  obtain ⟨st₁, h1, h2, h3⟩ := h
  obtain ⟨st₂, h4, h5, h6⟩ := h' st₁ h3
  exact ⟨st₂, by simp only [exec, h1, Option.bind_some, h4], h2.trans h5, h6⟩

theorem whileIter_runsFrom {q : Tst} {d : List ℕ} {a : List (ℕ × ℕ)}
    {body : St Op Tst K → Option (St Op Tst K)} {cb : Count Op Tst} {pb : ℕ}
    (Inv : ℕ → Mem K → Prop) {J : ℕ}
    (htest : ∀ i m, Inv i m → ∃ b, I.test q d a m = some b ∧ (b = true → i < J))
    (hbody : ∀ i st, Inv i st.mem → I.test q d a st.mem = some true →
      ∃ st', body st = some st' ∧ St.Within st st' cb pb ∧ Inv (i + 1) st'.mem) :
    ∀ (r i : ℕ) (st : St Op Tst K), i ≤ J → J - i ≤ r → Inv i st.mem →
      ∃ st', whileIter (fun s => I.test q d a s.mem) (fun s => s.tick q d) body r st = some st' ∧
        St.Within st st' ((J - i) • (Count.test q d + cb) + Count.test q d) pb ∧
        ∃ j ≤ J, Inv j st'.mem ∧ I.test q d a st'.mem = some false := by
  intro r
  induction r with
  | zero =>
    intro i st hiJ hr hi
    obtain ⟨b, hb, hlt⟩ := htest i st.mem hi
    cases b with
    | true => exact absurd (hlt rfl) (by omega)
    | false => exact ⟨st.tick q d, by simp [whileIter, hb],
        (St.Within.tick st q d).mono le_add_self (Nat.zero_le _), i, hiJ, hi, hb⟩
  | succ r ih =>
    intro i st hiJ hr hi
    obtain ⟨b, hb, hlt⟩ := htest i st.mem hi
    cases b with
    | false => exact ⟨st.tick q d, by simp [whileIter, hb],
        (St.Within.tick st q d).mono le_add_self (Nat.zero_le _), i, hiJ, hi, hb⟩
    | true =>
      have hiJ' := hlt rfl
      obtain ⟨st₁, h1, hw1, hi1⟩ := hbody i (st.tick q d) hi hb
      obtain ⟨st', h2, hw2, hpost⟩ := ih (i + 1) st₁ (by omega) (by omega) hi1
      refine ⟨st', by simp [whileIter, hb, h1, h2], ?_, hpost⟩
      refine (((St.Within.tick st q d).trans hw1).trans hw2).mono (le_of_eq ?_) (by simp)
      rw [show J - i = (J - (i + 1)) + 1 by omega, succ_nsmul]
      abel

/-- **A loop while a test holds, with its counts**: the test is used at most `J + 1` times and
the body runs at most `J` times, where `J` bounds the rounds under the invariant; the fuel only
has to be at least `J`. -/
theorem whileFuel {fuel : IExp} {q : Tst} {ds : List IExp} {ins : List Operand}
    {body : Stmt Op Tst} {k : ℕ} {d : List ℕ} {a : List (ℕ × ℕ)} {cb : Count Op Tst} {pb : ℕ}
    (hk : fuel.eval ρ.idx = some k) (hd : IExp.evalList ρ.idx ds = some d)
    (ha : Operand.evalList ρ ins = some a) (Inv : ℕ → Mem K → Prop) (J : ℕ) (hJ : J ≤ k)
    (h0 : Inv 0 st.mem)
    (htest : ∀ i m, Inv i m → ∃ b, I.test q d a m = some b ∧ (b = true → i < J))
    (hbody : ∀ i st, Inv i st.mem → I.test q d a st.mem = some true →
      RunsFrom I W τ body ρ st cb pb (Inv (i + 1))) :
    RunsFrom I W τ (.whileFuel fuel q ds ins body) ρ st
      (J • (Count.test q d + cb) + Count.test q d) pb
      (fun m => ∃ j ≤ J, Inv j m ∧ I.test q d a m = some false) := by
  obtain ⟨st', h1, h2, h3⟩ := whileIter_runsFrom Inv htest hbody k 0 st (Nat.zero_le _)
    (by omega) h0
  exact ⟨st', by simp only [exec, hk, hd, ha, Option.bind_some, h1], by simpa using h2, h3⟩

/-- A counted run from the initial state is a run within the budget. -/
theorem runs {s : Stmt Op Tst} {m : Mem K} (h : RunsFrom I W τ s ρ (St.init m) c p Q) :
    Runs I W τ s ρ m c p Q := by
  obtain ⟨st', h1, ⟨-, h2, h3⟩, h4⟩ := h
  exact ⟨st', h1, by simpa [St.init] using h2, by simpa [St.init] using h3, h4⟩

end RunsFrom

end NLAlib.Ops
