/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.GivensLog
public import NLAlib.Matrix.Perturbation.BackwardClosed
public import NLAlib.Ops.Logic.ProbabilisticFamily

/-!
# A stored log read back is a measurable event

A randomized program that records its rotations in a slotted log (`NLAlib.HoldsSlottedLog`) ends,
on its good tapes, in a memory holding a closed log. To carry that log through a probabilistic
step whose good set must not depend on the input (`NLAlib.Ops.PWrites.pstep_of_forall`), the
log is named by the memory itself: the slots read back (`NLAlib.slottedLogRead`). The event "the
first `j` slots read back hold as a closed log, with planes below `N`" is measurable, and every
stored closed log of `j` slots is that event (up to padding, which does not change the unitary).

## Main definitions

* `NLAlib.HoldsReadLog`: the first `j` slots read back hold as a closed log.

## Main results

* `NLAlib.HoldsSlottedLog.holdsReadLog`: a stored closed log is its read.
* `NLAlib.HoldsSlottedLog.slotEntries_slottedLogRead`: the valid entries of the read are those of
  the stored log.
* `NLAlib.measurableSet_holdsReadLog`: the event is measurable.
* `NLAlib.isClosed_setOf_isPerturbedUnitarySimilarBy`: perturbed unitary similarity by a named
  unitary is a closed relation.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Ops

/-! ### Padding and the read -/

/-- Padding the accepted slots of a stored log keeps it stored. -/
theorem HoldsSlottedLog.map_padEntries {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {s : Store ℝ}
    (h : HoldsSlottedLog lg ns w L P s) :
    HoldsSlottedLog lg ns w (L.map (Option.map (padEntries w))) P s := by
  obtain ⟨hLn, hPw, hc, hp, hf⟩ := h
  refine ⟨by simpa using hLn, hPw, fun j hj => ?_, by simpa using hp, by simpa using hf⟩
  rw [List.length_map] at hj
  obtain ⟨v, hv, hm⟩ := hc j hj
  refine ⟨v, hv, ?_⟩
  rw [List.getElem_map]
  rcases hL : L[j] with _ | es
  · rw [hL] at hm
    exact hm
  · rw [hL] at hm
    obtain ⟨h0, hl, hb⟩ := hm
    refine ⟨h0, by simp [padEntries]; omega, by rw [padEntries_padEntries]; exact hb⟩

/-- The first slots read back from a stored closed log are its slots, padded. -/
theorem HoldsSlottedLog.slottedLogRead_take {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {s : Store ℝ} (h : HoldsSlottedLog lg ns w L [] s) :
    (slottedLogRead lg ns w s).take L.length = L.map (Option.map (padEntries w)) := by
  have hL := h.1
  rw [h.close.slottedLogRead_eq (by simp; omega), List.map_append,
    List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]

/-- The valid entries read back from a stored closed log are its own, up to padding. -/
theorem HoldsSlottedLog.slotEntries_slottedLogRead {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {s : Store ℝ} (h : HoldsSlottedLog lg ns w L [] s) :
    slotEntries w (slottedLogRead lg ns w s) = slotEntries w L := by
  have hL := h.1
  rw [h.close.slottedLogRead_eq (by simp; omega), slotEntries_map_padEntries,
    slotEntries_append_replicate_none]

/-- Rejecting `k` more slots, still open and zero-filled, extends a closed log by `k` rejected
slots. -/
theorem HoldsSlottedLog.reject_replicate {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {s : Store ℝ} (h : HoldsSlottedLog lg ns w L [] s)
    {k : ℕ} (hk : L.length + k ≤ ns) :
    HoldsSlottedLog lg ns w (L ++ List.replicate k none) [] s := by
  induction k generalizing L with
  | zero => simpa using h
  | succ k ih =>
    have := ih (h.reject (by omega)) (by simp; omega)
    rwa [List.append_assoc, List.singleton_append, ← List.replicate_succ] at this

/-- A log with no open slot holds whatever its pending entries: they are not stored. -/
theorem HoldsSlottedLog.of_length_eq {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {s : Store ℝ}
    (h : HoldsSlottedLog lg ns w L P s) (hL : L.length = ns) :
    HoldsSlottedLog lg ns w L [] s := by
  obtain ⟨hLn, -, hc, -, hf⟩ := h
  exact ⟨hLn, Nat.zero_le _, hc, fun h => absurd h (by omega), hf⟩

/-- Closing the pending slot and `k` more as rejected: a log with pending entries and room for
$k + 1$ more slots holds, with them rejected, as a closed log. -/
theorem HoldsSlottedLog.reject_pending {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {s : Store ℝ}
    (h : HoldsSlottedLog lg ns w L P s) {k : ℕ} (hk : L.length + (k + 1) ≤ ns) :
    HoldsSlottedLog lg ns w (L ++ List.replicate (k + 1) none) [] s := by
  have := (h.reject (by omega)).reject_replicate (k := k) (by simp; omega)
  rwa [List.append_assoc, List.singleton_append, ← List.replicate_succ] at this

/-- **The stored log as read**: the first `j` slots read back from the region at `lg` (`ns` slots
of `w` entries, `NLAlib.slottedLogRead`) hold there as a closed log, and the planes of their
valid entries are below $N - 1$. -/
def HoldsReadLog (lg : ℕ × ℕ) (ns w j N : ℕ) (s : Store ℝ) : Prop :=
  HoldsSlottedLog lg ns w ((slottedLogRead lg ns w s).take j) [] s ∧
    ∀ e ∈ slotEntries w ((slottedLogRead lg ns w s).take j), e.1 + 1 < N

/-- A stored closed log is its read. -/
theorem HoldsSlottedLog.holdsReadLog {lg : ℕ × ℕ} {ns w N : ℕ}
    {L : List (Option (List GivensEntry))} {s : Store ℝ} (h : HoldsSlottedLog lg ns w L [] s)
    (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < N) : HoldsReadLog lg ns w L.length N s := by
  rw [HoldsReadLog, h.slottedLogRead_take, slotEntries_map_padEntries]
  exact ⟨h.map_padEntries, hpl⟩

/-! ### Measurability -/

/-- A word equal to a measurable function of the memory is a measurable event. -/
theorem Mem.measurableSet_get_eq_fun (z : ℕ × ℕ) {g : Mem ℝ → ℝ} (hg : Measurable g) :
    MeasurableSet {m : Mem ℝ | m.store.get z.1 z.2 = some (g m)} := by
  have e : {m : Mem ℝ | m.store.get z.1 z.2 = some (g m)} =
      {m | (m.store.get z.1 z.2).isSome} ∩ {m | (m.store.get z.1 z.2).getD 0 = g m} := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    cases m.store.get z.1 z.2 <;> simp
  rw [e]
  exact ((measurable_fst.comp (Mem.measurable_cell z)) (measurableSet_singleton true)).inter
    (measurableSet_eq_fun (measurable_get_getD z.1 z.2) hg)

/-- A block equal to a measurable list of words of the memory is a measurable event. -/
theorem Mem.measurableSet_readBlock_eq_fun (b o n : ℕ) {f : Mem ℝ → List ℝ}
    (hlen : ∀ m, (f m).length = n) (hf : ∀ t < n, Measurable fun m => (f m).getD t 0) :
    MeasurableSet {m : Mem ℝ | m.store.readBlock b o n = some (f m)} := by
  have e : {m : Mem ℝ | m.store.readBlock b o n = some (f m)} =
      ⋂ t : Fin n, {m | m.store.get b (o + t) = some ((f m).getD t 0)} := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Store.readBlock_eq_some_iff, hlen, true_and]
    constructor
    · intro h t
      rw [h t t.isLt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hlen]; exact t.isLt)]
      rfl
    · intro h t ht
      rw [h ⟨t, ht⟩, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hlen]; exact ht)]
      rfl
  rw [e]
  exact .iInter fun t => Mem.measurableSet_get_eq_fun (b, o + t) (hf t t.isLt)

/-- The entries of slot `j` decoded from the memory, as in `NLAlib.slottedLogRead`. -/
private noncomputable def readSlot (lg : ℕ × ℕ) (w j : ℕ) (m : Mem ℝ) : List GivensEntry :=
  (List.range w).map fun i =>
    let x := fun t => (m.store.get lg.1 (lg.2 + j * (1 + 5 * w) + t)).getD 0
    (⌊x (1 + 5 * i + 0)⌋₊, ⟨x (1 + 5 * i + 1), x (1 + 5 * i + 2)⟩,
      ⟨x (1 + 5 * i + 3), x (1 + 5 * i + 4)⟩)

private theorem slottedLogRead_getElem (lg : ℕ × ℕ) (ns w : ℕ) (m : Mem ℝ) {j : ℕ}
    (hj : j < (slottedLogRead lg ns w m.store).length) :
    (slottedLogRead lg ns w m.store)[j] =
      if 0 < (m.store.get lg.1 (lg.2 + j * (1 + 5 * w))).getD 0 then
        some (readSlot lg w j m) else none := by
  simp only [slottedLogRead, List.getElem_map, List.getElem_range, Nat.add_zero, readSlot]

private theorem length_readSlot (lg : ℕ × ℕ) (w j : ℕ) (m : Mem ℝ) :
    (readSlot lg w j m).length = w := by
  simp [readSlot]

private theorem measurable_getD_readSlot (lg : ℕ × ℕ) (w j : ℕ) {t : ℕ} (ht : t < 5 * w) :
    Measurable fun m => ((readSlot lg w j m).flatMap entryWords).getD t 0 := by
  have e : (fun m => ((readSlot lg w j m).flatMap entryWords).getD t 0) =
      fun m => (entryWords ((readSlot lg w j m)[t / 5]'(by rw [length_readSlot]; omega))).getD
        (t % 5) 0 := by
    funext m
    rw [← getD_flatMap_entryWords _ (by rw [length_readSlot]; omega) (Nat.mod_lt _ (by omega)),
      Nat.div_add_mod]
  rw [e]
  have hx (c : ℕ) := measurable_get_getD lg.1 (lg.2 + j * (1 + 5 * w) + (1 + 5 * (t / 5) + c))
  have hc : t % 5 < 5 := Nat.mod_lt _ (by omega)
  interval_cases h : t % 5 <;>
    simp only [readSlot, List.getElem_map, List.getElem_range, entryWords, List.getD_cons_zero,
      List.getD_cons_succ]
  · exact measurable_from_nat.comp (Measurable.nat_floor (hx 0))
  · exact hx 1
  · exact hx 2
  · exact hx 3
  · exact hx 4

/-- The elementary form of `NLAlib.HoldsReadLog`. -/
private def ReadLogWords (lg : ℕ × ℕ) (ns w j N : ℕ) (m : Mem ℝ) : Prop :=
  (∀ jj < j, (m.store.get lg.1 (lg.2 + jj * (1 + 5 * w))).isSome ∧
    ((m.store.get lg.1 (lg.2 + jj * (1 + 5 * w))).getD 0 ≤ 0 ∨
      (0 < (m.store.get lg.1 (lg.2 + jj * (1 + 5 * w))).getD 0 ∧
        m.store.readBlock lg.1 (lg.2 + jj * (1 + 5 * w) + 1) (5 * w) =
          some ((readSlot lg w jj m).flatMap entryWords) ∧
        ∀ e ∈ readSlot lg w jj m, e.1 + 1 < N))) ∧
  ∀ jj, j ≤ jj → jj < ns → m.store.get lg.1 (lg.2 + jj * (1 + 5 * w)) = some 0 ∧
    m.store.readBlock lg.1 (lg.2 + jj * (1 + 5 * w) + 1) (5 * w) =
      some (List.replicate (5 * w) 0)

private theorem measurableSet_readLogWords (lg : ℕ × ℕ) (ns w j N : ℕ) :
    MeasurableSet {m : Mem ℝ | ReadLogWords lg ns w j N m} := by
  have hx (t : ℕ) := measurable_get_getD lg.1 t
  have hA : ∀ jj, MeasurableSet {m : Mem ℝ |
      (m.store.get lg.1 (lg.2 + jj * (1 + 5 * w))).isSome ∧
      ((m.store.get lg.1 (lg.2 + jj * (1 + 5 * w))).getD 0 ≤ 0 ∨
        (0 < (m.store.get lg.1 (lg.2 + jj * (1 + 5 * w))).getD 0 ∧
          m.store.readBlock lg.1 (lg.2 + jj * (1 + 5 * w) + 1) (5 * w) =
            some ((readSlot lg w jj m).flatMap entryWords) ∧
          ∀ e ∈ readSlot lg w jj m, e.1 + 1 < N))} := by
    intro jj
    have hpl : MeasurableSet {m : Mem ℝ | ∀ e ∈ readSlot lg w jj m, e.1 + 1 < N} := by
      have e : {m : Mem ℝ | ∀ e ∈ readSlot lg w jj m, e.1 + 1 < N} = ⋂ i : Fin w,
          {m | ⌊(m.store.get lg.1 (lg.2 + jj * (1 + 5 * w) + (1 + 5 * i + 0))).getD 0⌋₊ + 1 <
            N} := by
        ext m
        simp only [readSlot, List.mem_map, List.mem_range, Set.mem_ofPred_eq, Set.mem_iInter,
          forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, add_zero]
        exact ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i, hi⟩⟩
      rw [e]
      exact .iInter fun i => (Measurable.nat_floor (hx _)) (MeasurableSet.of_discrete
        (s := {k : ℕ | k + 1 < N}))
    simp only [Set.ofPred_and, Set.ofPred_or]
    refine MeasurableSet.inter ?_ (MeasurableSet.union
      (measurableSet_le (hx (lg.2 + jj * (1 + 5 * w))) measurable_const)
      ((measurableSet_lt measurable_const (hx (lg.2 + jj * (1 + 5 * w)))).inter
        ((Mem.measurableSet_readBlock_eq_fun lg.1 (lg.2 + jj * (1 + 5 * w) + 1) (5 * w)
          (fun m => by rw [length_flatMap_entryWords, length_readSlot])
          fun t ht => measurable_getD_readSlot lg w jj ht).inter hpl)))
    exact (measurable_fst.comp (Mem.measurable_cell (lg.1, lg.2 + jj * (1 + 5 * w))))
      (measurableSet_singleton true)
  have hZ : ∀ jj, MeasurableSet {m : Mem ℝ |
      m.store.get lg.1 (lg.2 + jj * (1 + 5 * w)) = some 0 ∧
      m.store.readBlock lg.1 (lg.2 + jj * (1 + 5 * w) + 1) (5 * w) =
        some (List.replicate (5 * w) 0)} := fun jj =>
    (Mem.measurableSet_get_eq (lg.1, lg.2 + jj * (1 + 5 * w)) 0).inter
      (Mem.measurableSet_readBlock_eq_fun lg.1 (lg.2 + jj * (1 + 5 * w) + 1) (5 * w)
        (f := fun _ => List.replicate (5 * w) 0)
        (fun _ => by simp) fun _ _ => measurable_const)
  have e : {m : Mem ℝ | ReadLogWords lg ns w j N m} =
      (⋂ jj : Fin j, {m : Mem ℝ |
        (m.store.get lg.1 (lg.2 + jj * (1 + 5 * w))).isSome ∧
        ((m.store.get lg.1 (lg.2 + jj * (1 + 5 * w))).getD 0 ≤ 0 ∨
          (0 < (m.store.get lg.1 (lg.2 + jj * (1 + 5 * w))).getD 0 ∧
            m.store.readBlock lg.1 (lg.2 + jj * (1 + 5 * w) + 1) (5 * w) =
              some ((readSlot lg w jj m).flatMap entryWords) ∧
            ∀ e ∈ readSlot lg w jj m, e.1 + 1 < N))}) ∩
      ⋂ jj : Fin ns, {m : Mem ℝ | j ≤ (jj : ℕ) →
        m.store.get lg.1 (lg.2 + jj * (1 + 5 * w)) = some 0 ∧
        m.store.readBlock lg.1 (lg.2 + jj * (1 + 5 * w) + 1) (5 * w) =
          some (List.replicate (5 * w) 0)} := by
    ext m
    simp only [ReadLogWords, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact and_congr ⟨fun h jj => h jj jj.isLt, fun h jj hjj => h ⟨jj, hjj⟩⟩
      ⟨fun h jj hj => h jj hj jj.isLt, fun h jj hj hjn => h ⟨jj, hjn⟩ hj⟩
  rw [e]
  refine (MeasurableSet.iInter fun jj : Fin j => hA jj).inter
    (MeasurableSet.iInter fun jj : Fin ns => ?_)
  by_cases h : j ≤ (jj : ℕ)
  · simpa [h] using hZ jj
  · simp [h]

private theorem padEntries_readSlot (lg : ℕ × ℕ) (w j : ℕ) (m : Mem ℝ) :
    padEntries w (readSlot lg w j m) = readSlot lg w j m := by
  simp [padEntries, length_readSlot]

/-- The first `j ≤ ns` slots read back are `j` slots. -/
theorem length_take_slottedLogRead {lg : ℕ × ℕ} {ns w j : ℕ} (hj : j ≤ ns) (s : Store ℝ) :
    ((slottedLogRead lg ns w s).take j).length = j := by
  simp [slottedLogRead]; omega

/-- A valid entry of the first slots read back is an entry of an accepted slot. -/
private theorem mem_slotEntries_take_slottedLogRead {lg : ℕ × ℕ} {ns w j : ℕ} (hj : j ≤ ns)
    {m : Mem ℝ} {e : GivensEntry}
    (he : e ∈ slotEntries w ((slottedLogRead lg ns w m.store).take j)) :
    ∃ jj < j, 0 < (m.store.get lg.1 (lg.2 + jj * (1 + 5 * w))).getD 0 ∧
      e ∈ readSlot lg w jj m := by
  simp only [slotEntries, List.mem_flatMap] at he
  obtain ⟨o, ho, he⟩ := he
  obtain ⟨jj, hjj, rfl⟩ := List.getElem_of_mem ho
  have hjj' : jj < j := by rwa [length_take_slottedLogRead hj] at hjj
  rw [List.getElem_take, slottedLogRead_getElem] at he
  split_ifs at he with h0
  · rw [Option.map_some, Option.getD_some, padEntries_readSlot] at he
    exact ⟨jj, hjj', h0, he⟩
  · simp at he

/-- The stored log as read, in words. -/
private theorem holdsReadLog_iff {lg : ℕ × ℕ} {ns w j N : ℕ} (hj : j ≤ ns) (m : Mem ℝ) :
    HoldsReadLog lg ns w j N m.store ↔ ReadLogWords lg ns w j N m := by
  have hr := length_take_slottedLogRead (lg := lg) (w := w) hj m.store
  unfold HoldsReadLog HoldsSlottedLog ReadLogWords
  constructor
  · rintro ⟨⟨-, -, hc, hp, hf⟩, hpl⟩
    rw [hr] at hp hf
    refine ⟨fun jj hjj => ?_, fun jj h1 h2 => ?_⟩
    · obtain ⟨v, hv, hm⟩ := hc jj (by rw [hr]; exact hjj)
      rw [List.getElem_take, slottedLogRead_getElem, hv, Option.getD_some] at hm
      refine ⟨by rw [hv]; rfl, ?_⟩
      rw [hv, Option.getD_some]
      split_ifs at hm with h0
      · obtain ⟨-, -, hb⟩ := hm
        rw [padEntries_readSlot] at hb
        refine Or.inr ⟨h0, hb, fun e he => hpl e ?_⟩
        simp only [slotEntries, List.mem_flatMap]
        refine ⟨_, List.getElem_mem (by rw [hr]; exact hjj), ?_⟩
        rw [List.getElem_take, slottedLogRead_getElem, hv, Option.getD_some, if_pos h0,
          Option.map_some, Option.getD_some, padEntries_readSlot]
        exact he
      · exact Or.inl hm
    · rcases Nat.lt_or_eq_of_le h1 with h1 | rfl
      · exact hf jj h1 h2
      · obtain ⟨h0, hb⟩ := hp h2
        exact ⟨h0, by rw [hb, flatMap_entryWords_padEntries_nil]⟩
  · rintro ⟨hA, hZ⟩
    refine ⟨⟨by rw [hr]; omega, by simp, fun jj hjj => ?_, fun hjn => ?_,
      fun jj h1 h2 => hZ jj (by rw [hr] at h1; omega) h2⟩, fun e he => ?_⟩
    · rw [hr] at hjj
      obtain ⟨hsome, hor⟩ := hA jj hjj
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
      refine ⟨v, hv, ?_⟩
      rw [List.getElem_take, slottedLogRead_getElem, hv, Option.getD_some]
      rw [hv, Option.getD_some] at hor
      split_ifs with h0
      · rcases hor with hor | ⟨-, hb, -⟩
        · exact absurd hor (not_le.mpr h0)
        · exact ⟨h0, by rw [length_readSlot], by rw [padEntries_readSlot]; exact hb⟩
      · exact not_lt.mp h0
    · rw [hr] at hjn ⊢
      obtain ⟨h0, hb⟩ := hZ j le_rfl hjn
      exact ⟨h0, by rw [hb, flatMap_entryWords_padEntries_nil]⟩
    · obtain ⟨jj, hjj, h0, he⟩ := mem_slotEntries_take_slottedLogRead hj he
      rcases (hA jj hjj).2 with h | ⟨-, -, hpl⟩
      · exact absurd h (not_le.mpr h0)
      · exact hpl e he

/-- **The stored log as read is a measurable event**: the memories whose first `j \le n_s` slots
read back hold there as a closed log with planes below $N - 1$. -/
theorem measurableSet_holdsReadLog (lg : ℕ × ℕ) {ns : ℕ} (w : ℕ) {j : ℕ} (N : ℕ) (hj : j ≤ ns) :
    MeasurableSet {m : Mem ℝ | HoldsReadLog lg ns w j N m.store} := by
  simp only [holdsReadLog_iff hj]
  exact measurableSet_readLogWords lg ns w j N

/-! ### Similarity by a named unitary is closed -/

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Perturbed unitary similarity by a named unitary is a closed relation: for every
$\varepsilon$ the triples $(\mathbf{V}, \mathbf{A}, \mathbf{B})$ with $\mathbf{V}$ of orthonormal
columns and $\mathbf{B} = \mathbf{V}^{\mathsf H}(\mathbf{A} + \mathbf{E})\mathbf{V}$ for some
$\|\mathbf{E}\|_2 \le \varepsilon$ form a closed set (the perturbation is
$\mathbf{V}\mathbf{B}\mathbf{V}^{\mathsf H} - \mathbf{A}$). -/
theorem isClosed_setOf_isPerturbedUnitarySimilarBy (ε : ℝ) :
    IsClosed {p : Matrix n n 𝕜 × Matrix n n 𝕜 × Matrix n n 𝕜 |
      IsPerturbedUnitarySimilarBy p.1 p.2.1 p.2.2 ε} := by
  have hO : IsClosed {p : Matrix n n 𝕜 × Matrix n n 𝕜 × Matrix n n 𝕜 |
      HasOrthonormalCols p.1} :=
    isCompact_setOf_hasOrthonormalCols.isClosed.preimage continuous_fst
  have hE : IsClosed {p : Matrix n n 𝕜 × Matrix n n 𝕜 × Matrix n n 𝕜 |
      specNorm (p.1 * p.2.2 * p.1ᴴ - p.2.1) ≤ ε} :=
    isClosed_le (continuous_specNorm.comp (((continuous_fst.matrix_mul
      (continuous_snd.comp continuous_snd)).matrix_mul continuous_fst.matrix_conjTranspose).sub
      (continuous_fst.comp continuous_snd))) continuous_const
  convert hO.inter hE using 1
  ext ⟨V, A, B⟩
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, IsPerturbedUnitarySimilarBy]
  constructor
  · rintro ⟨hV, E, hE, rfl⟩
    have hV' : V * Vᴴ = 1 := hV.mul_conjTranspose_self
    refine ⟨hV, ?_⟩
    have : V * (Vᴴ * (A + E) * V) * Vᴴ = A + E := by
      simp only [← Matrix.mul_assoc, hV', Matrix.one_mul]
      rw [Matrix.mul_assoc, hV', Matrix.mul_one]
    simpa [this] using hE
  · rintro ⟨hV, hE⟩
    have hV' : Vᴴ * V = 1 := hV
    refine ⟨hV, V * B * Vᴴ - A, hE, ?_⟩
    rw [add_sub_cancel]
    simp only [← Matrix.mul_assoc, hV', Matrix.one_mul]
    rw [Matrix.mul_assoc, hV', Matrix.mul_one]

end NLAlib
