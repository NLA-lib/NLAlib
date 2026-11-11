/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Tactic.Abel
public import NLAlib.Ops.Contract

/-!
# Static counts and workspace

The counts and the scratch payload bytes of a run are bounded by functions of the tree and the
  values of
its index variables alone: `NLAlib.Ops.stmtCost` and `NLAlib.Ops.stmtPeak`. For a tree
without tests and index binders the count is exact; a branch counts the larger side, a `whileFuel`
its fuel, a `bindIdx` its worst value.

`NLAlib.Ops.exec_within`: every successful counted run stays within them. So a count is obtained
by evaluating a function on the tree, never by a proof about loops, and
`NLAlib.Ops.ConditionalRuns.of_run` turns a statement about the memory (program logic) into the full
statement with counts and workspace.
## Main results

* `NLAlib.Ops.exec_within`: soundness of the static count and workspace.
* `NLAlib.Ops.ConditionalRuns.of_run`: from a run to a run within its static budget.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- The count of one use of `o` at the dimensions `ds`, when they evaluate. -/
noncomputable def useCost (o : Op) (ds : List IExp) (idx : List ℕ) : Count Op Tst :=
  ((IExp.evalList idx ds).map (Count.one o)).getD 0

/-- The count of one use of the query `q` at the dimensions `ds`, when they evaluate. -/
noncomputable def testCost (q : Tst) (ds : List IExp) (idx : List ℕ) : Count Op Tst :=
  ((IExp.evalList idx ds).map (Count.test q)).getD 0

/-- **The static count** of a tree at the values `idx` of its index variables. -/
noncomputable def stmtCost : Stmt Op Tst → List ℕ → Count Op Tst
  | .skip, _ => 0
  | .abort, _ => 0
  | .seq s t, idx => stmtCost s idx + stmtCost t idx
  | .call o ds _ _, idx => useCost o ds idx
  | .ite q ds _ t e, idx => testCost q ds idx + (stmtCost t idx ⊔ stmtCost e idx)
  | .whileFuel fuel q ds _ body k, idx =>
      ∑ i ∈ Finset.range ((fuel.eval idx).getD 0),
          (testCost q ds (idx ++ [i]) + stmtCost body (idx ++ [i])) +
        (Finset.range ((fuel.eval idx).getD 0 + 1)).sup fun j => stmtCost k (idx ++ [j])
  | .bindIdx q _ bound body, idx =>
      Count.test q [] +
        (Finset.range ((bound.eval idx).getD 0 + 1)).sup fun v => stmtCost body (idx ++ [v])
  | .allocAs _ _ body, idx => stmtCost body idx
  | .loop n body, idx =>
      ∑ i ∈ Finset.range ((n.eval idx).getD 0), stmtCost body (idx ++ [i])
  | .frame ds args body, idx =>
      match IExp.evalList idx ds, IExp.evalList idx (args.map Operand.off) with
      | some d, some o => stmtCost body (d ++ o)
      | _, _ => 0

/-- **The static workspace** of a tree: a bound on the scratch payload bytes above those live at its
start, with the workspace `W` of each call. -/
def stmtPeak (W : Op → List ℕ → ℕ) : Stmt Op Tst → List ℕ → ℕ
  | .skip, _ => 0
  | .abort, _ => 0
  | .seq s t, idx => max (stmtPeak W s idx) (stmtPeak W t idx)
  | .call o ds _ _, idx => ((IExp.evalList idx ds).map (W o)).getD 0
  | .ite _ _ _ t e, idx => max (stmtPeak W t idx) (stmtPeak W e idx)
  | .whileFuel fuel _ _ _ body k, idx =>
      max ((Finset.range ((fuel.eval idx).getD 0)).sup fun i => stmtPeak W body (idx ++ [i]))
        ((Finset.range ((fuel.eval idx).getD 0 + 1)).sup fun j => stmtPeak W k (idx ++ [j]))
  | .bindIdx _ _ bound body, idx =>
      (Finset.range ((bound.eval idx).getD 0 + 1)).sup fun v => stmtPeak W body (idx ++ [v])
  | .allocAs fmt len body, idx => fmt.bytes * (len.eval idx).getD 0 + stmtPeak W body idx
  | .loop n body, idx =>
      (Finset.range ((n.eval idx).getD 0)).sup fun i => stmtPeak W body (idx ++ [i])
  | .frame ds args body, idx =>
      match IExp.evalList idx ds, IExp.evalList idx (args.map Operand.off) with
      | some d, some o => stmtPeak W body (d ++ o)
      | _, _ => 0

/-- The state `b` is reached from `a` within the counts `c` and the workspace `p`: same live
payload bytes, at most `c` more counts, peak at most `p` above the live payload bytes. -/
def St.Within (a b : St Op Tst K) (c : Count Op Tst) (p : ℕ) : Prop :=
  b.cur = a.cur ∧ b.cost ≤ a.cost + c ∧ b.peak ≤ max a.peak (a.cur + p)

namespace St.Within

theorem refl (a : St Op Tst K) : St.Within a a 0 0 := ⟨rfl, by simp, by simp⟩

theorem trans {a b d : St Op Tst K} {c c' : Count Op Tst} {p p' : ℕ} (h : St.Within a b c p)
    (h' : St.Within b d c' p') : St.Within a d (c + c') (max p p') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨h1'.trans h1, ?_, ?_⟩
  · calc d.cost ≤ b.cost + c' := h2'
      _ ≤ a.cost + c + c' := by gcongr
      _ = a.cost + (c + c') := add_assoc _ _ _
  · rw [h1] at h3'
    omega

theorem mono {a b : St Op Tst K} {c c' : Count Op Tst} {p p' : ℕ} (h : St.Within a b c p)
    (hc : c ≤ c')
    (hp : p ≤ p') : St.Within a b c' p' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2.trans (by gcongr), by omega⟩

theorem tick (a : St Op Tst K) (q : Tst) (d : List ℕ) :
    St.Within a (a.tick q d) (Count.test q d) 0 :=
  ⟨rfl, le_rfl, by simp [St.tick]⟩

end St.Within

theorem iter_within {f : ℕ → St Op Tst K → Option (St Op Tst K)} {c : ℕ → Count Op Tst} {p : ℕ → ℕ}
    (h : ∀ i a b, f i a = some b → St.Within a b (c i) (p i)) {k : ℕ} {s s' : St Op Tst K}
    (hk : iter f k s = some s') :
    St.Within s s' (∑ i ∈ Finset.range k, c i) ((Finset.range k).sup p) := by
  induction k generalizing s' with
  | zero => cases hk; simpa using St.Within.refl s
  | succ k ih =>
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hk
    refine ((ih ha).trans (h k a s' hb)).mono (by rw [Finset.sum_range_succ]) ?_
    rw [Finset.range_add_one, Finset.sup_insert]
    exact le_of_eq (max_comm _ _)

/-- A loop with early exit stays within the sum over the rounds it may do of the counts `c i` of
one round (test and body), and within the largest workspace of a body. -/
theorem whileIter_within {test : ℕ → St Op Tst K → Option (Bool × St Op Tst K)}
    {body : ℕ → St Op Tst K → Option (St Op Tst K)} {ct cb : ℕ → Count Op Tst} {p : ℕ → ℕ}
    (ht : ∀ i a bs, test i a = some bs → St.Within a bs.2 (ct i) 0)
    (h : ∀ i a b, body i a = some b → St.Within a b (cb i) (p i)) {r i : ℕ}
    {s : St Op Tst K} {js : ℕ × St Op Tst K} (hk : whileIter test body r i s = some js) :
    St.Within s js.2 (∑ l ∈ Finset.range r, (ct (i + l) + cb (i + l)))
      ((Finset.range r).sup fun l => p (i + l)) := by
  induction r generalizing i s with
  | zero => cases hk; simpa using St.Within.refl s
  | succ r ih =>
    obtain ⟨bs, hbs, hb⟩ := Option.bind_eq_some_iff.mp hk
    have hsum : ct i + cb i + ∑ l ∈ Finset.range r, (ct (i + 1 + l) + cb (i + 1 + l)) =
        ∑ l ∈ Finset.range (r + 1), (ct (i + l) + cb (i + l)) := by
      rw [Finset.sum_range_succ', add_comm]
      simp [Nat.add_assoc, Nat.add_comm 1]
    have hsup : max (p i) ((Finset.range r).sup fun l => p (i + 1 + l)) ≤
        (Finset.range (r + 1)).sup fun l => p (i + l) := by
      refine max_le (Finset.le_sup (f := fun l => p (i + l)) (b := 0) (by simp)) ?_
      refine Finset.sup_le fun l hl => ?_
      have := Finset.le_sup (f := fun l => p (i + l)) (s := Finset.range (r + 1)) (b := l + 1)
        (by simpa using Finset.mem_range.mp hl)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this
    split_ifs at hb with hc
    · obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hb
      refine (((ht i s bs hbs).trans (h i _ a ha)).trans (ih hb)).mono (le_of_eq hsum) ?_
      simpa using hsup
    · cases hb
      refine (ht i s bs hbs).mono ?_ (Nat.zero_le _)
      rw [← hsum, add_assoc]
      exact le_self_add

/-- **Soundness of the static count and workspace**: a successful counted run keeps the live
cells, adds at most the static count and stays within the static workspace. -/
theorem exec_within {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} {τ : Tape K} {s : Stmt Op Tst}
    {ρ : Env}
    {st st' : St Op Tst K} (h : evalCounted I W τ s ρ st = some st') :
    St.Within st st' (stmtCost s ρ.idx) (stmtPeak W s ρ.idx) := by
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
    exact ⟨rfl, by simp [stmtCost, useCost, hd], by simp [stmtPeak, hd]⟩
  | ite o ds ins t e iht ihe =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
    have hu : testCost (Op := Op) o ds ρ.idx = Count.test o d := by simp [testCost, hd]
    cases c
    · exact ((St.Within.tick st o d).trans (ihe h)).mono
        (by simp only [stmtCost, hu]; gcongr; exact le_sup_right) (by simp [stmtPeak])
    · exact ((St.Within.tick st o d).trans (iht h)).mono
        (by simp only [stmtCost, hu]; gcongr; exact le_sup_left) (by simp [stmtPeak])
  | whileFuel fuel o ds ins body k ih ihk =>
    obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨jst, hw, h⟩ := Option.bind_eq_some_iff.mp h
    have hj := (whileIter_rel (R := fun _ _ : St Op Tst K => True) (fun _ => trivial)
      (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) hw).2.2
    have ht : ∀ i a bs, I.testSt o ds ins (ρ.pushIdx i) a = some bs →
        St.Within a bs.2 (testCost o ds (ρ.idx ++ [i])) 0 := fun i a bs hbs => by
      obtain ⟨d, hd, -, e⟩ := Interp.testSt_eq_some hbs
      have hu : testCost (Op := Op) o ds (ρ.idx ++ [i]) = Count.test o d := by
        simp only [testCost]
        rw [show ρ.idx ++ [i] = (ρ.pushIdx i).idx from rfl, hd]
        rfl
      rw [e, hu]
      exact St.Within.tick a o d
    have hb : ∀ i a b, evalCounted I W τ body (ρ.pushIdx i) a = some b →
        St.Within a b (stmtCost body (ρ.idx ++ [i])) (stmtPeak W body (ρ.idx ++ [i])) :=
      fun i a b hb => ih (ρ := ρ.pushIdx i) hb
    have hk : St.Within jst.2 st' (stmtCost k (ρ.idx ++ [jst.1]))
        (stmtPeak W k (ρ.idx ++ [jst.1])) := ihk (ρ := ρ.pushIdx jst.1) h
    have hmem : jst.1 ∈ Finset.range (n + 1) := by
      simp only [Finset.mem_range]
      omega
    refine ((whileIter_within ht hb hw).trans hk).mono ?_ ?_
    · simp only [stmtCost, hn, Option.getD_some, zero_add]
      gcongr
      exact Finset.le_sup (f := fun j => stmtCost k (ρ.idx ++ [j])) hmem
    · simp only [stmtPeak, hn, Option.getD_some, zero_add]
      exact max_le_max le_rfl
        (Finset.le_sup (f := fun j => stmtPeak W k (ρ.idx ++ [j])) hmem)
  | bindIdx o ins bound body ih =>
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨B, hB, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h with hv
    have hmem : v ∈ Finset.range ((bound.eval ρ.idx).getD 0 + 1) := by
      simp only [hB, Option.getD_some, Finset.mem_range]
      omega
    refine ((St.Within.tick st o []).trans (ih h)).mono ?_ ?_
    · simp only [stmtCost]
      gcongr
      exact Finset.le_sup (f := fun v => stmtCost body (ρ.idx ++ [v])) hmem
    · simp only [stmtPeak, zero_le, max_eq_right]
      exact Finset.le_sup (f := fun v => stmtPeak W body (ρ.idx ++ [v])) hmem
  | allocAs fmt len body ih =>
    obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨st₂, h₂, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨-, h2, h3⟩ := ih h₂
    refine ⟨rfl, h2, ?_⟩
    simp only [stmtPeak, hn, Option.getD_some, Env.idx_pushBuf] at h3 ⊢
    omega
  | loop n body ih =>
    obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.mp h
    simpa [stmtCost, stmtPeak, hk] using iter_within (fun i _ _ hb => ih hb) h
  | frame ds args body ih =>
    obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h
    simpa [stmtCost, stmtPeak, hd, Operand.evalList_off_of_evalList ha] using ih h

/-- **A run within a budget** (total correctness with accounting): from the memory `m`, the
counted run succeeds, its counts are at most `B`, its scratch payload bytes at most `M`, and `Q`
  holds of
the final memory. -/
def ConditionalRuns (I : Interp Op Tst K) (W : Op → List ℕ → ℕ) (τ : Tape K) (s : Stmt Op Tst) (ρ
  : Env)
    (m : Mem K)
    (B : Count Op Tst) (M : ℕ) (Q : Mem K → Prop) : Prop :=
  ∃ st', evalCounted I W τ s ρ (St.init m) = some st' ∧ st'.cost ≤ B ∧ st'.peak ≤ M ∧ Q st'.mem

/-- **A run whose postcondition sees the counts**: from the memory `m`, the counted run succeeds
within the workspace `M`, and `Q` holds of the final counts and the final memory. This is the
form of a statement whose bound on the counts depends on the data, or is a weighted bound. -/
def ConditionalRunsW (I : Interp Op Tst K) (W : Op → List ℕ → ℕ) (τ : Tape K) (s : Stmt Op Tst) (ρ
  : Env)
    (m : Mem K) (M : ℕ) (Q : Count Op Tst → Mem K → Prop) : Prop :=
  ∃ st', evalCounted I W τ s ρ (St.init m) = some st' ∧ st'.peak ≤ M ∧ Q st'.cost st'.mem

/-- A run within a budget is a run whose counts are within the budget. -/
theorem runs_iff_runsW {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} {τ : Tape K}
    {s : Stmt Op Tst} {ρ : Env} {m : Mem K} {B : Count Op Tst} {M : ℕ} {Q : Mem K → Prop} :
    ConditionalRuns I W τ s ρ m B M Q ↔ ConditionalRunsW I W τ s ρ m M fun c m' => c ≤ B ∧ Q m' :=
  ⟨fun ⟨st', h1, h2, h3, h4⟩ => ⟨st', h1, h3, h2, h4⟩,
    fun ⟨st', h1, h3, h2, h4⟩ => ⟨st', h1, h2, h3, h4⟩⟩

theorem ConditionalRunsW.mono {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} {τ : Tape K} {s : Stmt
  Op Tst}
    {ρ : Env} {m : Mem K} {M M' : ℕ} {Q Q' : Count Op Tst → Mem K → Prop}
    (h : ConditionalRunsW I W τ s ρ m M Q) (hM : M ≤ M') (hQ : ∀ c m', Q c m' → Q' c m') :
    ConditionalRunsW I W τ s ρ m M' Q' := by
  obtain ⟨st', h1, h2, h3⟩ := h
  exact ⟨st', h1, h2.trans hM, hQ _ _ h3⟩

/-- **A refinement statement** (partial correctness): if the run succeeds, `Q` holds of the final
memory. -/
def ConditionalRunsL (I : Interp Op Tst K) (τ : Tape K) (s : Stmt Op Tst) (ρ : Env) (m : Mem K)
    (Q : Mem K → Prop) :
    Prop :=
  ∀ m', eval I τ s ρ m = some m' → Q m'

/-- A successful run with `Q` is a run within the static count and workspace. -/
theorem ConditionalRuns.of_run {I : Interp Op Tst K} {τ : Tape K} {s : Stmt Op Tst} {ρ : Env} {m
  m' : Mem K}
    {Q : Mem K → Prop} (h : eval I τ s ρ m = some m') (hQ : Q m') (W : Op → List ℕ → ℕ) :
    ConditionalRuns I W τ s ρ m (stmtCost s ρ.idx) (stmtPeak W s ρ.idx) Q := by
  obtain ⟨st', hst, hm⟩ := exec_eq_some_of_run h W (St.init m) rfl
  obtain ⟨-, h2, h3⟩ := exec_within hst
  exact ⟨st', hst, by simpa [St.init] using h2, by simpa [St.init] using h3, hm ▸ hQ⟩

theorem ConditionalRuns.mono {I : Interp Op Tst K} {W : Op → List ℕ → ℕ} {τ : Tape K} {s : Stmt Op
  Tst}
    {ρ : Env}
    {m : Mem K} {B B' : Count Op Tst} {M M' : ℕ} {Q Q' : Mem K → Prop} (h : ConditionalRuns I W τ
      s ρ m B M Q)
    (hB : B ≤ B') (hM : M ≤ M') (hQ : ∀ m', Q m' → Q' m') : ConditionalRuns I W τ s ρ m B' M' Q'
      := by
  obtain ⟨st', h1, h2, h3, h4⟩ := h
  exact ⟨st', h1, h2.trans hB, h3.trans hM, hQ _ h4⟩

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

/-- Total certification of this fixed program against an independently specified model and
claim. A target can require this proposition directly, fixing the program before every runtime
size and input. Realizability is already required by the type of the model. -/
def Runs {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}
    (p : Program Op Tst r b) (M : AccessModel Op Tst P) (S : Specification Op Tst P) : Prop :=
  ∀ d, P.valid d → ∀ (x : P.Input d) (I : Interp Op Tst K), M.contracts d x I → ∀ τ,
    ∃ st, exec p I M.resources P.formats τ d (P.initial d x) = some st ∧
      st.peak ≤ S.scratch d ∧ st.cost ≤ S.budget d ∧
        M.resources.work st.cost ≤ S.work d ∧ M.resources.span st.cost ≤ S.span d ∧
          P.initialBytes d x + st.peak ≤ S.memory d ∧ S.good d x τ st.cost st.mem


/-- Certification is the canonical total run proposition for one fixed tree and model. -/
abbrev Program.Certifies {Op Tst K : Type} {r b : ℕ} {P : Problem K r b}
    (p : Program Op Tst r b) (M : AccessModel Op Tst P) (S : Specification Op Tst P) : Prop :=
  Runs p M S

/-- Full canonical static count, including index expressions and control. -/
noncomputable def staticCost {r b : ℕ} (p : Program Op Tst r b) (d : Fin r → ℕ) :
    Count (Op ⊕ Bookkeeping) Tst :=
  stmtCost p.body.instrument (Program.environment (b := b) d).idx

/-- Conservative scratch bytes: explicit/primitive peak plus the largest query reservation. -/
noncomputable def staticPeak {r b : ℕ} (R : ResourceModel Op Tst)
    (p : Program Op Tst r b) (d : Fin r → ℕ) : ℕ :=
  stmtPeak (instrumentWorkspace R.workspace) p.body.instrument
    (Program.environment (b := b) d).idx + R.queryReserve (staticCost p d)

/-- Structural counters require no scratch payload bytes. -/
theorem stmtPeak_tally (W : Op → List ℕ → ℕ) (ks : List Bookkeeping) (idx : List ℕ) :
    stmtPeak (instrumentWorkspace W) (tally (Tst := Tst) ks) idx = 0 := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [tally, stmtPeak, IExp.evalList, instrumentWorkspace, ih]
/-- Mandatory structural accounting preserves the source scratch bound exactly. -/
theorem stmtPeak_instrument (W : Op → List ℕ → ℕ) (s : Stmt Op Tst) (idx : List ℕ) :
    stmtPeak (instrumentWorkspace W) s.instrument idx = stmtPeak W s idx := by
  induction s generalizing idx with
  | skip => exact stmtPeak_tally ..
  | abort => rfl
  | seq s t ihs iht => simp [Stmt.instrument, stmtPeak, stmtPeak_tally, ihs, iht]
  | call o ds ins outs =>
    simp only [Stmt.instrument, stmtPeak, stmtPeak_tally, zero_max]
    rfl
  | ite q ds ins t e iht ihe => simp [Stmt.instrument, stmtPeak, stmtPeak_tally, iht, ihe]
  | whileFuel fuel q ds ins body k ih ihk =>
    simp [Stmt.instrument, stmtPeak, stmtPeak_tally, ih, ihk]
  | bindIdx q ins bound body ih => simp [Stmt.instrument, stmtPeak, stmtPeak_tally, ih]
  | allocAs fmt len body ih =>
    simp only [Stmt.instrument, stmtPeak, stmtPeak_tally, ih, IExp.evalList, zero_max,
      show (IExp.const fmt.bytes).eval idx = some fmt.bytes from rfl]
    cases len.eval idx <;> simp [instrumentWorkspace]
  | loop n body ih => simp [Stmt.instrument, stmtPeak, stmtPeak_tally, ih]
  | frame ds args body ih =>
    simp only [Stmt.instrument, stmtPeak, stmtPeak_tally, zero_max]
    cases IExp.evalList idx ds <;> cases IExp.evalList idx (args.map Operand.off) <;>
      simp [ih]

/-- The allocation/primitive part of the byte bound is unchanged by structural elaboration. -/
theorem staticPeak_eq {r b : ℕ} (R : ResourceModel Op Tst) (p : Program Op Tst r b)
    (d : Fin r → ℕ) : staticPeak R p d =
      stmtPeak R.workspace p.body (Program.environment (b := b) d).idx +
        R.queryReserve (staticCost p d) := by
  rw [staticPeak, stmtPeak_instrument]

/-- Canonical byte and instruction bounds cover every successful format-checked execution. -/
theorem exec_static {r b : ℕ} {p : Program Op Tst r b} {I : Interp Op Tst K}
    {R : ResourceModel Op Tst} {formats : Fin b → StorageFormat} {τ : Tape K}
    {d : Fin r → ℕ} {m : Mem K} {st : St (Op ⊕ Bookkeeping) Tst K}
    (h : exec p I R formats τ d m = some st) :
    st.cost ≤ staticCost p d ∧ st.peak ≤ staticPeak R p d := by
  unfold exec at h
  split_ifs at h
  obtain ⟨raw, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨-, hc, hp⟩ := exec_within hr
  have hc' : raw.cost ≤ staticCost p d := by simpa [St.init, staticCost] using hc
  refine ⟨hc', ?_⟩
  have hp' : raw.peak ≤ stmtPeak (instrumentWorkspace R.workspace) p.body.instrument
      (Program.environment (b := b) d).idx := by simpa [St.init] using hp
  exact Nat.add_le_add hp' (R.queryReserve_mono hc')

end NLAlib.Ops
