/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Tactic.Abel
public import NLAlib.Ops.Exec

/-!
# Static counts and workspace

The counts and the scratch cells of a run are bounded by functions of the tree and the values of
its index variables alone: `NLAlib.Ops.staticCost` and `NLAlib.Ops.staticPeak`. For a tree
without tests and index binders the count is exact; a branch counts the larger side, a `whileFuel`
its fuel, a `bindIdx` its worst value.

`NLAlib.Ops.exec_within`: every successful counted run stays within them. So a count is obtained
by evaluating a function on the tree, never by a proof about loops, and
`NLAlib.Ops.Runs.of_run` turns a statement about the memory (program logic) into the full
statement with counts and workspace.
## Main results

* `NLAlib.Ops.exec_within`: soundness of the static count and workspace.
* `NLAlib.Ops.Runs.of_run`: from a run to a run within its static budget.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op K : Type}

/-- The count of one use of `o` at the dimensions `ds`, when they evaluate. -/
noncomputable def useCost (o : Op) (ds : List IExp) (idx : List ℕ) : Count Op :=
  ((IExp.evalList idx ds).map (Count.one o)).getD 0

/-- **The static count** of a tree at the values `idx` of its index variables. -/
noncomputable def staticCost : Stmt Op → List ℕ → Count Op
  | .skip, _ => 0
  | .abort, _ => 0
  | .seq s t, idx => staticCost s idx + staticCost t idx
  | .call o ds _ _, idx => useCost o ds idx
  | .ite o ds _ t e, idx => useCost o ds idx + (staticCost t idx ⊔ staticCost e idx)
  | .whileFuel fuel o ds _ body, idx =>
      ((fuel.eval idx).getD 0) • (useCost o ds idx + staticCost body idx) + useCost o ds idx
  | .bindIdx o _ bound body, idx =>
      Count.one o [] +
        (Finset.range ((bound.eval idx).getD 0 + 1)).sup fun v => staticCost body (idx ++ [v])
  | .alloc _ body, idx => staticCost body idx
  | .loop n body, idx =>
      ∑ i ∈ Finset.range ((n.eval idx).getD 0), staticCost body (idx ++ [i])
  | .frame ds args body, idx =>
      match IExp.evalList idx ds, IExp.evalList idx (args.map Operand.off) with
      | some d, some o => staticCost body (d ++ o)
      | _, _ => 0

/-- **The static workspace** of a tree: a bound on the scratch cells above those live at its
start, with the workspace `W` of each call. -/
def staticPeak (W : Op → List ℕ → ℕ) : Stmt Op → List ℕ → ℕ
  | .skip, _ => 0
  | .abort, _ => 0
  | .seq s t, idx => max (staticPeak W s idx) (staticPeak W t idx)
  | .call o ds _ _, idx => ((IExp.evalList idx ds).map (W o)).getD 0
  | .ite _ _ _ t e, idx => max (staticPeak W t idx) (staticPeak W e idx)
  | .whileFuel _ _ _ _ body, idx => staticPeak W body idx
  | .bindIdx _ _ bound body, idx =>
      (Finset.range ((bound.eval idx).getD 0 + 1)).sup fun v => staticPeak W body (idx ++ [v])
  | .alloc len body, idx => (len.eval idx).getD 0 + staticPeak W body idx
  | .loop n body, idx =>
      (Finset.range ((n.eval idx).getD 0)).sup fun i => staticPeak W body (idx ++ [i])
  | .frame ds args body, idx =>
      match IExp.evalList idx ds, IExp.evalList idx (args.map Operand.off) with
      | some d, some o => staticPeak W body (d ++ o)
      | _, _ => 0

/-- The state `b` is reached from `a` within the counts `c` and the workspace `p`: same live
cells, at most `c` more counts, peak at most `p` above the live cells. -/
def St.Within (a b : St Op K) (c : Count Op) (p : ℕ) : Prop :=
  b.cur = a.cur ∧ b.cost ≤ a.cost + c ∧ b.peak ≤ max a.peak (a.cur + p)

namespace St.Within

theorem refl (a : St Op K) : St.Within a a 0 0 := ⟨rfl, by simp, by simp⟩

theorem trans {a b d : St Op K} {c c' : Count Op} {p p' : ℕ} (h : St.Within a b c p)
    (h' : St.Within b d c' p') : St.Within a d (c + c') (max p p') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨h1'.trans h1, ?_, ?_⟩
  · calc d.cost ≤ b.cost + c' := h2'
      _ ≤ a.cost + c + c' := by gcongr
      _ = a.cost + (c + c') := add_assoc _ _ _
  · rw [h1] at h3'
    omega

theorem mono {a b : St Op K} {c c' : Count Op} {p p' : ℕ} (h : St.Within a b c p) (hc : c ≤ c')
    (hp : p ≤ p') : St.Within a b c' p' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2.trans (by gcongr), by omega⟩

theorem tick (a : St Op K) (o : Op) (d : List ℕ) : St.Within a (a.tick o d) (Count.one o d) 0 :=
  ⟨rfl, le_rfl, by simp [St.tick]⟩

end St.Within

theorem iter_within {f : ℕ → St Op K → Option (St Op K)} {c : ℕ → Count Op} {p : ℕ → ℕ}
    (h : ∀ i a b, f i a = some b → St.Within a b (c i) (p i)) {k : ℕ} {s s' : St Op K}
    (hk : iter f k s = some s') :
    St.Within s s' (∑ i ∈ Finset.range k, c i) ((Finset.range k).sup p) := by
  induction k generalizing s' with
  | zero => cases hk; simpa using St.Within.refl s
  | succ k ih =>
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hk
    refine ((ih ha).trans (h k a s' hb)).mono (by rw [Finset.sum_range_succ]) ?_
    rw [Finset.range_add_one, Finset.sup_insert]
    exact le_of_eq (max_comm _ _)

theorem whileIter_within {test : St Op K → Option Bool} {tick : St Op K → St Op K}
    {body : St Op K → Option (St Op K)} {c cb : Count Op} {pb : ℕ}
    (ht : ∀ a, St.Within a (tick a) c 0) (h : ∀ a b, body a = some b → St.Within a b cb pb)
    {k : ℕ} {s s' : St Op K} (hk : whileIter test tick body k s = some s') :
    St.Within s s' (k • (c + cb) + c) pb := by
  induction k generalizing s with
  | zero =>
    obtain ⟨b, -, hb⟩ := Option.bind_eq_some_iff.mp hk
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hb
      exact hb ▸ (ht s).mono le_add_self zero_le
    | true => simp at hb
  | succ k ih =>
    obtain ⟨b, -, hb⟩ := Option.bind_eq_some_iff.mp hk
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hb
      exact hb ▸ (ht s).mono le_add_self zero_le
    | true =>
      simp only [if_true] at hb
      obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hb
      refine (((ht s).trans (h _ _ ha)).trans (ih hb)).mono (le_of_eq ?_) (by simp)
      rw [succ_nsmul]
      abel

/-- **Soundness of the static count and workspace**: a successful counted run keeps the live
cells, adds at most the static count and stays within the static workspace. -/
theorem exec_within {I : Interp Op K} {W : Op → List ℕ → ℕ} {τ : ℕ → K} {s : Stmt Op} {ρ : Env}
    {st st' : St Op K} (h : exec I W τ s ρ st = some st') :
    St.Within st st' (staticCost s ρ.idx) (staticPeak W s ρ.idx) := by
  induction s generalizing ρ st st' with
  | skip => cases h; exact St.Within.refl _
  | abort => cases h
  | seq s t ihs iht =>
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp h
    exact (ihs ha).trans (iht hb)
  | call o ds ins outs =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨m', -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨rfl, by simp [staticCost, useCost, hd], by simp [staticPeak, hd]⟩
  | ite o ds ins t e iht ihe =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
    have hu : useCost o ds ρ.idx = Count.one o d := by simp [useCost, hd]
    cases c
    · exact ((St.Within.tick st o d).trans (ihe h)).mono
        (by simp only [staticCost, hu]; gcongr; exact le_sup_right) (by simp [staticPeak])
    · exact ((St.Within.tick st o d).trans (iht h)).mono
        (by simp only [staticCost, hu]; gcongr; exact le_sup_left) (by simp [staticPeak])
  | whileFuel fuel o ds ins body ih =>
    obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    have hu : useCost o ds ρ.idx = Count.one o d := by simp [useCost, hd]
    simpa [staticCost, staticPeak, hk, hu] using
      whileIter_within (fun a => St.Within.tick a o d) (fun _ _ hb => ih hb) h
  | bindIdx o ins bound body ih =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B, hB, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h with hv
    have hmem : v ∈ Finset.range ((bound.eval ρ.idx).getD 0 + 1) := by
      simp only [hB, Option.getD_some, Finset.mem_range]
      omega
    refine ((St.Within.tick st o []).trans (ih h)).mono ?_ ?_
    · simp only [staticCost]
      gcongr
      exact Finset.le_sup (f := fun v => staticCost body (ρ.idx ++ [v])) hmem
    · simp only [staticPeak, zero_le, max_eq_right]
      exact Finset.le_sup (f := fun v => staticPeak W body (ρ.idx ++ [v])) hmem
  | alloc len body ih =>
    obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨-, h2, h3⟩ := ih h₂
    refine ⟨rfl, h2, ?_⟩
    simp only [staticPeak, hn, Option.getD_some, Env.idx_pushBuf] at h3 ⊢
    omega
  | loop n body ih =>
    obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.mp h
    simpa [staticCost, staticPeak, hk] using iter_within (fun i _ _ hb => ih hb) h
  | frame ds args body ih =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    simpa [staticCost, staticPeak, hd, Operand.evalList_off_of_evalList ha] using ih h

/-- **A run within a budget** (total correctness with accounting): from the memory `m`, the
counted run succeeds, its counts are at most `B`, its scratch cells at most `M`, and `Q` holds of
the final memory. -/
def Runs (I : Interp Op K) (W : Op → List ℕ → ℕ) (τ : ℕ → K) (s : Stmt Op) (ρ : Env) (m : Mem K)
    (B : Count Op) (M : ℕ) (Q : Mem K → Prop) : Prop :=
  ∃ st', exec I W τ s ρ (St.init m) = some st' ∧ st'.cost ≤ B ∧ st'.peak ≤ M ∧ Q st'.mem

/-- **A refinement statement** (partial correctness): if the run succeeds, `Q` holds of the final
memory. -/
def RunsL (I : Interp Op K) (τ : ℕ → K) (s : Stmt Op) (ρ : Env) (m : Mem K) (Q : Mem K → Prop) :
    Prop :=
  ∀ m', run I τ s ρ m = some m' → Q m'

/-- A successful run with `Q` is a run within the static count and workspace. -/
theorem Runs.of_run {I : Interp Op K} {τ : ℕ → K} {s : Stmt Op} {ρ : Env} {m m' : Mem K}
    {Q : Mem K → Prop} (h : run I τ s ρ m = some m') (hQ : Q m') (W : Op → List ℕ → ℕ) :
    Runs I W τ s ρ m (staticCost s ρ.idx) (staticPeak W s ρ.idx) Q := by
  obtain ⟨st', hst, hm⟩ := exec_eq_some_of_run h W (St.init m) rfl
  obtain ⟨-, h2, h3⟩ := exec_within hst
  exact ⟨st', hst, by simpa [St.init] using h2, by simpa [St.init] using h3, hm ▸ hQ⟩

theorem Runs.mono {I : Interp Op K} {W : Op → List ℕ → ℕ} {τ : ℕ → K} {s : Stmt Op} {ρ : Env}
    {m : Mem K} {B B' : Count Op} {M M' : ℕ} {Q Q' : Mem K → Prop} (h : Runs I W τ s ρ m B M Q)
    (hB : B ≤ B') (hM : M ≤ M') (hQ : ∀ m', Q m' → Q' m') : Runs I W τ s ρ m B' M' Q' := by
  obtain ⟨st', h1, h2, h3, h4⟩ := h
  exact ⟨st', h1, h2.trans hB, h3.trans hM, hQ _ h4⟩

end NLAlib.Ops
