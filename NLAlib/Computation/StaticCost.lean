/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.FirstOrder

/-!
# Static resource bounds for first-order programs

The fixed first-order tree determines an upper bound on counts and additional live workspace.
Branches use pointwise maxima, bounded loops sum the actual index-dependent body costs, fuel-bounded
loops include every possible comparison, and an index binder takes the maximum of its body over
every value up to its bound (`NLAlib.Computation.StaticCost.supRange`). Scoped allocations add
workspace only while their body runs. These bounds apply to successful execution under arbitrary
scalar semantics and oracles; they do not assert successful execution or charge memory hidden inside
an external scalar operation or oracle implementation.

## Main results

* `NLAlib.Computation.StaticCost.Bounds.trans`: sequential resource composition.
* `NLAlib.Computation.FStmt.bounds_staticCost_of_exec_eq_some`: static bounds for actual runs.
* `NLAlib.Computation.Prog.runsWithin_staticCost_of_exec_eq_some`: existing budget interface.

Read-only storage is separate from additional live workspace. The program budget bridge adds
it to the cell peak exactly as the existing resource interface requires.
-/

@[expose] public section

namespace NLAlib.Computation

/-- An upper bound on incremental operation counts and additional simultaneously live
workspace, in cells per tag and in bits. Read-only storage is accounted for separately. -/
structure StaticCost (P ι : Type) where
  /-- Incremental count bound, by operation kind. -/
  count : OpCount P ι
  /-- Additional simultaneously live cells at each tag. -/
  cells : P → ℕ
  /-- Additional simultaneously live bits over all tags. -/
  bits : ℕ

namespace StaticCost

variable {P ι K : Type}

/-- The empty resource summary. -/
def zero : StaticCost P ι := ⟨0, fun _ => 0, 0⟩

/-- A charged operation with no additional interpreter-visible workspace. -/
def step (c : OpCount P ι) : StaticCost P ι := ⟨c, fun _ => 0, 0⟩

/-- Sequential summaries add counts and reuse workspace. -/
noncomputable def seq (a b : StaticCost P ι) : StaticCost P ι :=
  ⟨a.count + b.count, fun p => max (a.cells p) (b.cells p), max a.bits b.bits⟩

/-- A branch summary bounds both alternatives by pointwise maxima. The comparison charge is
added separately by the statement fold. -/
noncomputable def branch (a b : StaticCost P ι) : StaticCost P ι :=
  ⟨a.count ⊔ b.count, fun p => max (a.cells p) (b.cells p), max a.bits b.bits⟩

/-- A scoped allocation adds its live cells and bits to its body's workspace. -/
def alloc [DecidableEq P] (p : P) (len : ℕ) (width : P → ℕ)
    (body : StaticCost P ι) : StaticCost P ι :=
  ⟨body.count, fun q => (if q = p then len else 0) + body.cells q,
    len * width p + body.bits⟩

/-- A conservative bound on at most $n$ repetitions. Workspace is bounded by the body
workspace even when $n=0$, while counts are multiplied by $n$. -/
noncomputable def repetitions (n : ℕ) (body : StaticCost P ι) : StaticCost P ι :=
  ⟨n • body.count, body.cells, body.bits⟩

/-- The summary of an ordered finite sequence, allowing index-dependent body summaries. -/
noncomputable def sequence {α : Type} : List α → (α → StaticCost P ι) → StaticCost P ι
  | [], _ => zero
  | x :: xs, cost => seq (cost x) (sequence xs cost)

/-- The **supremum over a range**: a summary that bounds each of `f 0`, …, `f (m - 1)`, the
pointwise maxima of their counts and workspaces (`NLAlib.Computation.StaticCost.branch` folded over
the range). It bounds a body that runs at an index value below `m` not known statically. -/
noncomputable def supRange (m : ℕ) (f : ℕ → StaticCost P ι) : StaticCost P ι :=
  (List.range m).foldr (fun k c => (f k).branch c) zero

/-- A resource summary bounds an actual transition: counts grow by at most its charge,
current memory is restored, and peaks allow its additional workspace above initial current
memory. No assumption on scalar arithmetic or store contents is part of this predicate. -/
structure Bounds (c : StaticCost P ι) (st st' : St P K (OpCount P ι)) : Prop where
  /-- Upper bound on the final counts. -/
  count : st'.cnt ≤ st.cnt + c.count
  /-- Current cell memory is restored. -/
  cur : st'.cur = st.cur
  /-- Current bit memory is restored. -/
  curW : st'.curW = st.curW
  /-- Per-tag cell peak bound. -/
  peak : ∀ p, st'.peak p ≤ max (st.peak p) (st.cur p + c.cells p)
  /-- Bit peak bound. -/
  peakW : st'.peakW ≤ max st.peakW (st.curW + c.bits)

/-- An unchanged state uses the empty resource summary. -/
theorem Bounds.refl (st : St P K (OpCount P ι)) : zero.Bounds st st := by
  refine ⟨by simp [zero], rfl, rfl, fun p => ?_, ?_⟩
  · exact le_max_left _ _
  · exact le_max_left _ _

/-- A resource bound remains valid after increasing all three summary fields. -/
theorem Bounds.mono {a b : StaticCost P ι} {st st' : St P K (OpCount P ι)}
    (h : a.Bounds st st') (hc : a.count ≤ b.count)
    (hm : ∀ p, a.cells p ≤ b.cells p) (hw : a.bits ≤ b.bits) : b.Bounds st st' := by
  refine ⟨?_, h.cur, h.curW, fun p => ?_, ?_⟩
  · intro k
    exact (h.count k).trans (Nat.add_le_add_left (hc k) _)
  · exact (h.peak p).trans (max_le_max_left _ (Nat.add_le_add_left (hm p) _))
  · exact h.peakW.trans (max_le_max_left _ (Nat.add_le_add_left hw _))

/-- Sequential execution adds counts and takes the maximum of the two workspace bounds,
since each transition restores current memory. -/
theorem Bounds.trans {a b : StaticCost P ι} {st st₁ st₂ : St P K (OpCount P ι)}
    (h : a.Bounds st st₁) (h' : b.Bounds st₁ st₂) : (a.seq b).Bounds st st₂ := by
  refine ⟨?_, h'.cur.trans h.cur, h'.curW.trans h.curW, fun p => ?_, ?_⟩
  · intro k
    have h₁ := h.count k
    have h₂ := h'.count k
    simp only [Finsupp.add_apply] at h₁ h₂
    change st₂.cnt k ≤ st.cnt k + (a.count k + b.count k)
    omega
  · have h₁ := h.peak p
    have h₂ := h'.peak p
    rw [h.cur] at h₂
    change st₂.peak p ≤ max (st.peak p) (st.cur p + max (a.cells p) (b.cells p))
    omega
  · have h₁ := h.peakW
    have h₂ := h'.peakW
    rw [h.curW] at h₂
    change st₂.peakW ≤ max st.peakW (st.curW + max a.bits b.bits)
    omega

/-- The first alternative is bounded by the branch summary. -/
theorem Bounds.branch_left {a b : StaticCost P ι} {st st' : St P K (OpCount P ι)}
    (h : a.Bounds st st') : (a.branch b).Bounds st st' :=
  h.mono le_sup_left (fun _ => le_max_left _ _) (le_max_left _ _)

/-- The second alternative is bounded by the branch summary. -/
theorem Bounds.branch_right {a b : StaticCost P ι} {st st' : St P K (OpCount P ι)}
    (h : b.Bounds st st') : (a.branch b).Bounds st st' :=
  h.mono le_sup_right (fun _ => le_max_right _ _) (le_max_right _ _)

/-- An unchanged state obeys any nonnegative resource summary. -/
theorem Bounds.id (c : StaticCost P ι) (st : St P K (OpCount P ι)) : c.Bounds st st :=
  (Bounds.refl st).mono zero_le (fun _ => Nat.zero_le _) (Nat.zero_le _)

/-- A summary of an index below the range bounds the supremum over the range. -/
theorem Bounds.supRange {f : ℕ → StaticCost P ι} {m k : ℕ} (hk : k < m)
    {st st' : St P K (OpCount P ι)} (h : (f k).Bounds st st') : (supRange m f).Bounds st st' := by
  unfold StaticCost.supRange
  suffices ∀ l : List ℕ, k ∈ l → (l.foldr (fun k c => (f k).branch c) zero).Bounds st st' from
    this _ (List.mem_range.mpr hk)
  intro l hl
  induction l with
  | nil => exact absurd hl List.not_mem_nil
  | cons j l ih =>
    rcases List.mem_cons.mp hl with rfl | hl
    · exact h.branch_left
    · exact (ih hl).branch_right

/-- One charged store/tape update has no additional workspace. -/
theorem Bounds.step (st : St P K (OpCount P ι)) (s : Store P K) (pos : Dist → ℕ)
    (c : OpCount P ι) : (step c).Bounds st
      { st with
        store := s
        pos := pos
        cnt := st.cnt + c } := by
  exact ⟨le_rfl, rfl, rfl, fun _ => le_max_left _ _, le_max_left _ _⟩

private theorem repeat_succ (n : ℕ) (c : StaticCost P ι) :
    repetitions (n + 1) c = c.seq (repetitions n c) := by
  cases c
  simp [repetitions, seq, succ_nsmul, add_comm]

/-- A successful option fold obeys the ordered composition of its per-element summaries. -/
theorem Bounds.foldlM {α σ : Type} (π : σ → St P K (OpCount P ι))
    (f : σ → α → Option σ) (cost : α → StaticCost P ι) :
    ∀ (xs : List α), (∀ x ∈ xs, ∀ a b, f a x = some b → (cost x).Bounds (π a) (π b)) →
    ∀ {a b}, xs.foldlM f a = some b → (sequence xs cost).Bounds (π a) (π b)
  | [], _, a, b, h => by cases h; exact Bounds.refl _
  | x :: xs, hf, a, b, h => by
    obtain ⟨a', h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    exact (hf x List.mem_cons_self a a' h₁).trans
      (Bounds.foldlM π f cost xs (fun y hy => hf y (List.mem_cons_of_mem x hy)) h₂)

/-- A successful option fold whose every transition uses the same upper bound obeys the
length-times-count repetition summary, regardless of early inactive iterations. -/
theorem Bounds.foldlM_repeat {α σ : Type} (π : σ → St P K (OpCount P ι))
    (f : σ → α → Option σ) (cost : StaticCost P ι) :
    ∀ (xs : List α), (∀ x ∈ xs, ∀ a b, f a x = some b → cost.Bounds (π a) (π b)) →
    ∀ {a b}, xs.foldlM f a = some b → (repetitions xs.length cost).Bounds (π a) (π b)
  | [], _, a, b, h => by cases h; exact Bounds.id _ _
  | x :: xs, hf, a, b, h => by
    obtain ⟨a', h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    rw [List.length_cons, repeat_succ]
    exact (hf x List.mem_cons_self a a' h₁).trans
      (Bounds.foldlM_repeat π f cost xs (fun y hy => hf y (List.mem_cons_of_mem x hy)) h₂)

/-- Scoped allocation composition: include the allocation while its body runs, then restore
current memory when popping the buffer. The bound holds for every initial current/peak pair. -/
theorem Bounds.alloc [DecidableEq P] (width : P → ℕ) (p : P) (len : ℕ)
    {cost : StaticCost P ι} {st out : St P K (OpCount P ι)}
    (h : cost.Bounds
      { st with
        store := st.store.push (p, Array.replicate len none)
        cur := Function.update st.cur p (st.cur p + len)
        peak := Function.update st.peak p (max (st.peak p) (st.cur p + len))
        curW := st.curW + len * width p
        peakW := max st.peakW (st.curW + len * width p) } out) :
    (StaticCost.alloc p len width cost).Bounds st
      { out with
        store := Array.pop out.store
        cur := Function.update out.cur p (out.cur p - len)
        curW := out.curW - len * width p } := by
  refine ⟨h.count, ?_, ?_, fun q => ?_, ?_⟩
  · change Function.update out.cur p (out.cur p - len) = st.cur
    have hc : out.cur = Function.update st.cur p (st.cur p + len) := h.cur
    rw [hc, Function.update_self, Nat.add_sub_cancel, Function.update_idem,
      Function.update_eq_self]
  · change out.curW - len * width p = st.curW
    have hc : out.curW = st.curW + len * width p := h.curW
    rw [hc, Nat.add_sub_cancel]
  · have hp := h.peak q
    change out.peak q ≤ max
      (Function.update st.peak p (max (st.peak p) (st.cur p + len)) q)
      (Function.update st.cur p (st.cur p + len) q + cost.cells q) at hp
    by_cases hq : q = p
    · subst q
      simp only [Function.update_self] at hp
      change out.peak p ≤ max (st.peak p) (st.cur p + ((if p = p then len else 0) + _))
      simp only [ite_true]
      omega
    · simp only [Function.update_of_ne hq] at hp
      simpa only [StaticCost.alloc, hq, ite_false, zero_add] using hp
  · have hp := h.peakW
    change out.peakW ≤ max (max st.peakW (st.curW + len * width p))
      (st.curW + len * width p + cost.bits) at hp
    change out.peakW ≤ max st.peakW (st.curW + (len * width p + cost.bits))
    omega

/-- Evaluating one operation-kind count of a sequence gives the sum of its element counts. -/
@[simp] theorem sequence_count_apply {α : Type} (xs : List α)
    (cost : α → StaticCost P ι) (k : OpKind P ι) :
    (sequence xs cost).count k = (xs.map fun x => (cost x).count k).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sequence, seq, Finsupp.add_apply, List.map_cons,
      List.sum_cons, ih]

/-- A sequence with the same cell workspace in each element needs that workspace exactly
when the sequence is nonempty; its count and bit fields may vary. -/
@[simp] theorem sequence_cells_mk {α : Type} (xs : List α)
    (count : α → OpCount P ι) (cells : P → ℕ) (bits : α → ℕ) (p : P) :
    (sequence xs (fun x => ⟨count x, cells, bits x⟩)).cells p =
      if xs = [] then 0 else cells p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change max (cells p) ((sequence xs (fun x => ⟨count x, cells, bits x⟩)).cells p) = _
    rw [ih]
    simp only [List.cons_ne_nil, ite_false]
    split_ifs <;> simp

/-- A sequence with the same bit workspace in each element needs that workspace exactly
when nonempty; its count and per-tag cell fields may vary. -/
@[simp] theorem sequence_bits_mk {α : Type} (xs : List α)
    (count : α → OpCount P ι) (cells : α → P → ℕ) (bits : ℕ) :
    (sequence xs (fun x => ⟨count x, cells x, bits⟩)).bits =
      if xs = [] then 0 else bits := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change max bits (sequence xs (fun x => ⟨count x, cells x, bits⟩)).bits = _
    rw [ih]
    simp only [List.cons_ne_nil, ite_false]
    split_ifs <;> simp

/-- Uniform per-element cell workspace bounds also bound the sequence workspace. -/
theorem sequence_cells_le {α : Type} (xs : List α) (cost : α → StaticCost P ι)
    (p : P) (m : ℕ) (h : ∀ x ∈ xs, (cost x).cells p ≤ m) :
    (sequence xs cost).cells p ≤ m := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact max_le (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

/-- Uniform per-element bit workspace bounds also bound the sequence workspace. -/
theorem sequence_bits_le {α : Type} (xs : List α) (cost : α → StaticCost P ι)
    (m : ℕ) (h : ∀ x ∈ xs, (cost x).bits ≤ m) : (sequence xs cost).bits ≤ m := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact max_le (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

end StaticCost

variable {P ι : Type} [DecidableEq P]

/-- The resource summary of a fixed first-order tree in a natural-valued index environment.
It uses only charges, widths and index values: neither scalar data nor handle values. -/
noncomputable def FStmt.staticCost (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) :
    {nb ni : ℕ} → FStmt P ι nb ni → (Fin ni → ℕ) → StaticCost P ι
  | _, _, .skip, _ => StaticCost.zero
  | _, _, .seq s t, ρI => (s.staticCost charge width ρI).seq (t.staticCost charge width ρI)
  | _, _, .instr i, _ =>
      StaticCost.step (charge (i.subst (fun _ => 0) (fun _ => .const 0)).kind)
  | _, _, .apply o p _ _ _ _ cols, ρI =>
      StaticCost.step (charge (.load p o) + cols.evalIn ρI • charge (.matvec p o))
  | _, _, .rom p _ _, _ => StaticCost.step (charge (.rom p))
  | _, _, .alloc p len body, ρI =>
      StaticCost.alloc p (len.evalIn ρI) width (body.staticCost charge width ρI)
  | _, _, .loop n body, ρI => StaticCost.sequence (List.range (n.evalIn ρI))
      (fun i => body.staticCost charge width (Fin.snoc (α := fun _ => ℕ) ρI i))
  | _, _, .whileFuel fuel p _ _ _ body, ρI =>
      StaticCost.repetitions (fuel.evalIn ρI) ((StaticCost.step (charge (.cmp p))).seq
        (body.staticCost charge width ρI))
  | _, _, .ite p _ _ _ t e, ρI => (StaticCost.step (charge (.cmp p))).seq
      ((t.staticCost charge width ρI).branch (e.staticCost charge width ρI))
  -- Eliminate the first-order label; no named program node is constructed by the analysis.
  | _, _, FStmt.named _ _ body, ρI => body.staticCost charge width ρI
  | _, _, .kcall o p dims _ _, ρI => StaticCost.step (charge (.kcall p o (dims.map (·.evalIn ρI))))
  | _, _, .bindIdx p _ bound body, ρI => (StaticCost.step (charge (.toNat p))).seq
      (StaticCost.supRange (bound.evalIn ρI + 1)
        fun k => body.staticCost charge width (Fin.snoc (α := fun _ => ℕ) ρI k))

/-- The static resource summary of a program at its declared sizes. -/
noncomputable def Prog.staticCost {r b : ℕ} (prog : Prog P ι r b)
    (charge : OpKind P ι → OpCount P ι) (width : P → ℕ) (N : ℕ) (n : Fin r → ℕ) :
    StaticCost P ι := FStmt.staticCost charge width prog (Fin.cons N n)

variable {K : Type} (I : Interp P ι K (OpCount P ι))

/-- A successful comparison consumes its existing charge and no additional workspace. -/
theorem StaticCost.bounds_of_cmpStep_eq_some {p : P} {c : CmpOp} {x y : Cell ℕ ℕ}
    {st : St P K (OpCount P ι)} {r : Bool × St P K (OpCount P ι)}
    (h : cmpStep I p c x y st = some r) :
    (StaticCost.step (I.charge (.cmp p))).Bounds st r.2 := by
  rw [snd_of_cmpStep_eq_some h]
  exact StaticCost.Bounds.step st st.store st.pos _

private theorem bounds_ite {nb ni : ℕ} (p : P) (c : CmpOp)
    (x y : Cell (Fin nb) (Fin ni)) (t e : FStmt P ι nb ni)
    (ρB : Fin nb → ℕ) (ρI : Fin ni → ℕ)
    (ht : ∀ a b, t.exec I ρB ρI a = some b →
      (t.staticCost I.charge I.width ρI).Bounds a b)
    (he : ∀ a b, e.exec I ρB ρI a = some b →
      (e.staticCost I.charge I.width ρI).Bounds a b)
    {st st' : St P K (OpCount P ι)}
    (h : (FStmt.ite p c x y t e).exec I ρB ρI st = some st') :
    ((FStmt.ite p c x y t e).staticCost I.charge I.width ρI).Bounds st st' := by
  obtain ⟨r, hr, hb⟩ := Option.bind_eq_some_iff.mp h
  have hc := StaticCost.bounds_of_cmpStep_eq_some I hr
  split_ifs at hb
  · exact hc.trans ((ht _ _ hb).branch_left)
  · exact hc.trans ((he _ _ hb).branch_right)

private theorem bounds_whileFuel {nb ni : ℕ} (fuel : IExp (Fin ni)) (p : P) (c : CmpOp)
    (x y : Cell (Fin nb) (Fin ni)) (body : FStmt P ι nb ni)
    (ρB : Fin nb → ℕ) (ρI : Fin ni → ℕ)
    (hb : ∀ a b, body.exec I ρB ρI a = some b →
      (body.staticCost I.charge I.width ρI).Bounds a b)
    {st st' : St P K (OpCount P ι)}
    (h : (FStmt.whileFuel fuel p c x y body).exec I ρB ρI st = some st') :
    ((FStmt.whileFuel fuel p c x y body).staticCost I.charge I.width ρI).Bounds st st' := by
  obtain ⟨r, hfold, hfinish⟩ := Option.bind_eq_some_iff.mp h
  split_ifs at hfinish
  cases hfinish
  change (StaticCost.repetitions (fuel.evalIn ρI) _).Bounds st r.1
  have hlen : (List.range (fuel.evalIn ρI)).length = fuel.evalIn ρI := List.length_range
  rw [← hlen]
  refine StaticCost.Bounds.foldlM_repeat Prod.fst _ _ _ (fun _ _ a b hab => ?_) hfold
  split_ifs at hab
  · obtain ⟨r', hc, hbranch⟩ := Option.bind_eq_some_iff.mp hab
    have hcmp := StaticCost.bounds_of_cmpStep_eq_some I hc
    split_ifs at hbranch
    · obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hbranch
      exact hcmp.trans (hb _ _ hout)
    · cases hbranch
      exact hcmp.trans (StaticCost.Bounds.id _ _)
  · cases hab
    exact StaticCost.Bounds.id _ _

/-- Every successful execution of a fixed first-order tree satisfies its static operation,
cell-peak and bit-peak bounds, and restores current memory. The analysis reads only the tree,
charges, widths and index values; scalar semantics, tapes, oracles and initial stores are
arbitrary. Success itself must be established separately. -/
theorem FStmt.bounds_staticCost_of_exec_eq_some :
    ∀ {nb ni : ℕ} (s : FStmt P ι nb ni) (ρB : Fin nb → ℕ) (ρI : Fin ni → ℕ)
      {st st' : St P K (OpCount P ι)}, s.exec I ρB ρI st = some st' →
      (s.staticCost I.charge I.width ρI).Bounds st st'
  | _, _, .skip, _, _, _, _, h => by cases h; exact StaticCost.Bounds.refl _
  | _, _, .seq s t, ρB, ρI, _, _, h => by
    obtain ⟨st₁, hs, ht⟩ := Option.bind_eq_some_iff.mp h
    exact (s.bounds_staticCost_of_exec_eq_some ρB ρI hs).trans
      (t.bounds_staticCost_of_exec_eq_some ρB ρI ht)
  | _, _, .instr i, ρB, ρI, st, _, h => by
    obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp h
    have hk : Instr.kind (ι := ι) (i.subst ρB (fun v => .const (ρI v))) =
        (i.subst (fun _ => 0) (fun _ => .const 0)).kind := by cases i <;> rfl
    simpa only [FStmt.staticCost, hk] using StaticCost.Bounds.step st r.1 r.2
      (I.charge (i.subst ρB (fun v => .const (ρI v))).kind)
  | _, _, .apply o p dst dOff src sOff cols, ρB, ρI, st, _, h => by
    rw [FStmt.exec] at h
    split_ifs at h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, -, _, -, out, -, rfl⟩ := h
    exact StaticCost.Bounds.step st out st.pos _
  | _, _, .rom p dst i, ρB, ρI, st, _, h => by
    simp only [FStmt.exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, -, out, -, rfl⟩ := h
    exact StaticCost.Bounds.step st out st.pos _
  | _, _, .alloc p len body, ρB, ρI, st, _, h => by
    obtain ⟨out, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (body.bounds_staticCost_of_exec_eq_some _ ρI hb).alloc I.width p (len.evalIn ρI)
  | _, _, .loop n body, ρB, ρI, _, _, h => by
    exact StaticCost.Bounds.foldlM id _ _ (List.range (n.evalIn ρI))
      (fun i _ _ _ hi => body.bounds_staticCost_of_exec_eq_some ρB
        (Fin.snoc (α := fun _ => ℕ) ρI i) hi) h
  | _, _, .whileFuel fuel p c x y body, ρB, ρI, _, _, h =>
    bounds_whileFuel I fuel p c x y body ρB ρI
      (fun _ _ hb => body.bounds_staticCost_of_exec_eq_some ρB ρI hb) h
  | _, _, .ite p c x y t e, ρB, ρI, _, _, h =>
    bounds_ite I p c x y t e ρB ρI
      (fun _ _ ht => t.bounds_staticCost_of_exec_eq_some ρB ρI ht)
      (fun _ _ he => e.bounds_staticCost_of_exec_eq_some ρB ρI he) h
  | _, _, .named _ _ body, ρB, ρI, _, _, h => body.bounds_staticCost_of_exec_eq_some ρB ρI h
  | _, _, .kcall o p dims ins outs, ρB, ρI, st, _, h => by
    obtain ⟨out, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact StaticCost.Bounds.step st out st.pos _
  | _, _, .bindIdx p x bound body, ρB, ρI, st, _, h => by
    obtain ⟨r, hr, hb⟩ := Option.bind_eq_some_iff.mp h
    have hc : (StaticCost.step (I.charge (.toNat p))).Bounds st r.2 := by
      rw [snd_of_toNatStep_eq_some hr]
      exact StaticCost.Bounds.step st st.store st.pos _
    split_ifs at hb with hle
    exact hc.trans (StaticCost.Bounds.supRange (Nat.lt_succ_of_le hle)
      (body.bounds_staticCost_of_exec_eq_some ρB _ hb))

/-- A successful execution of a program satisfies the count, cell-peak and bit-peak summary
obtained from its fixed first-order tree at the declared sizes. -/
theorem Prog.bounds_staticCost_of_exec_eq_some {r b : ℕ} (prog : Prog P ι r b)
    (N : ℕ) (n : Fin r → ℕ) {st st' : St P K (OpCount P ι)}
    (h : prog.exec I N n st = some st') :
    (prog.staticCost I.charge I.width N n).Bounds st st' :=
  FStmt.bounds_staticCost_of_exec_eq_some I prog _ _ h

/-- A successful unit-charge run satisfies any count, cell and bit budget dominating its
static summary. The count estimate is stated at the canonical unit charge, so callers reuse
one syntax-derived estimate without repeating a function-extensionality rewrite. Cell and bit
estimates retain the actual interpretation and word widths. This proves accounting only;
successful execution is a premise. No printed source. -/
theorem Prog.bounds_of_exec_eq_some_of_staticCost_le {r b : ℕ} (prog : Prog P ι r b)
    (N : ℕ) (n : Fin r → ℕ) (hc : IsUnitCharge I)
    (count : OpCount P ι) (cells : P → ℕ) (bits : ℕ)
    (hcount : (prog.staticCost (fun k => Finsupp.single k 1) I.width N n).count ≤ count)
    (hcells : (prog.staticCost I.charge I.width N n).cells ≤ cells)
    (hbits : (prog.staticCost I.charge I.width N n).bits ≤ bits)
    {st st' : St P K (OpCount P ι)} (h : prog.exec I N n st = some st') :
    (StaticCost.mk count cells bits).Bounds st st' := by
  rw [← hc.charge_eq] at hcount
  exact (prog.bounds_staticCost_of_exec_eq_some I N n h).mono hcount hcells hbits

/-- Successful execution supplies the existing program budget interface using the static
count and workspace bounds. Constant read-only storage is added once to each cell peak;
the postcondition retains the actual final state. The start state holds exactly the declared
buffers. This theorem does not establish success. -/
theorem Prog.runsWithin_staticCost_of_exec_eq_some {r b : ℕ} (prog : Prog P ι r b)
    (N : ℕ) (n : Fin r → ℕ) {st st' : St P K (OpCount P ι)} (hsize : st.store.size = b)
    (h : prog.exec I N n st = some st') :
    prog.RunsWithin I N n st (prog.staticCost I.charge I.width N n).count
      (fun p => max (st.peak p) (st.cur p +
        (prog.staticCost I.charge I.width N n).cells p) + I.romSize p)
      (fun out => out = st') := by
  have hb := prog.bounds_staticCost_of_exec_eq_some I N n h
  exact ⟨hsize, st', h, hb.count, fun p => Nat.add_le_add_right (hb.peak p) _, rfl⟩

end NLAlib.Computation
