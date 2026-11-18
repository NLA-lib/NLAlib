/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.GivensPrograms
public import NLAlib.Matrix.FinitePrecision.GivensCoefficients
public import NLAlib.Matrix.FinitePrecision.GivensChain
public import NLAlib.Matrix.Perturbation.UnitarySimilarity
public import NLAlib.Ops.Catalog.Index
public import NLAlib.Ops.Catalog.Compare
public import NLAlib.Ops.RunMeasurable
public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.Logic.IndexLiteral
public import NLAlib.ForMathlib.MeasureTheory.Matrix
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Slotted logs of Givens rotations and their replay

A program that applies Givens rotations records each committed rotation as a self-describing
entry $(r, p, q)$: the plane $r$ (rows or columns $r, r + 1$) and the two inputs $p, q$ of the
coefficient program `NLAlib.coefficients`. The entries live in a **slotted static log**: `ns` slots
of $1 + 5w$ words, a valid word (positive iff the slot was accepted) and $w$ entries of five words
$(r, \Re p, \Im p, \Re q, \Im q)$. There is no count word: the layout is static, the only natural
written is the plane, and an unused entry is the zero fill $(0, 0, 0)$, whose rotation is the
identity (`NLAlib.givensAt_zero`). A trial writes straight into its own slot (the pending entries);
acceptance validates the slot. The exact unitary of a log is `NLAlib.givensLog` of its valid
entries (`NLAlib.slotEntries`). A replay recomputes the coefficients from the stored inputs and
applies the rotations to the rows or the columns of another matrix; on every tape each replayed
rotation moves its operand by at most $24\boldsymbol{u}$ times its norm from the exact product.

## Main definitions

* `NLAlib.GivensEntry`, `NLAlib.slotEntries`, `NLAlib.padEntries`, `NLAlib.HoldsSlottedLog`.
* `NLAlib.slottedLogRead`: the log read back from a store (for measurability).
* `NLAlib.slottedLogOpen`, `NLAlib.slottedLogWrite`, `NLAlib.slottedLogValidate`: zero-fill the
  log, write an entry of a slot, validate a slot.
* `NLAlib.givensReplayRows`, `NLAlib.givensReplayColumns`: replay the valid slots.

## Main results

* `NLAlib.slottedLogOpen_writes`, `NLAlib.slottedLogWrite_writes`,
  `NLAlib.slottedLogValidate_writes`: the log programs move the stored log.
* `NLAlib.givensReplayColumns_specNorm_sub_le`, `NLAlib.givensReplayRows_specNorm_sub_le`: the
  replay is within $(1 + 24\boldsymbol{u})^{R} - 1$ of the exact product, on every tape.
* `NLAlib.one_add_mul_pow_sub_one_le`: from the identity, within
  $27R\boldsymbol{u}$ when $24R\boldsymbol{u} \le 1/8$.
-/

@[expose] public section

namespace NLAlib

open Ops
open scoped Matrix

/-! ### The log -/

/-- A log entry $(r, p, q)$: the plane $r$ (rows or columns $r, r + 1$) and the two inputs of the
coefficient program. -/
abbrev GivensEntry := ℕ × ℂ × ℂ

/-- The five words of an entry: the plane, then $p$ and $q$ as pairs. -/
def entryWords (e : GivensEntry) : List ℝ :=
  [(e.1 : ℝ), e.2.1.re, e.2.1.im, e.2.2.re, e.2.2.im]

/-- An accepted slot padded to `w` entries by the zero fill $(0, 0, 0)$. -/
def padEntries (w : ℕ) (es : List GivensEntry) : List GivensEntry :=
  es ++ List.replicate (w - es.length) (0, 0, 0)

/-- The entries of the accepted slots, in slot order, each slot padded to `w` entries. -/
def slotEntries (w : ℕ) (L : List (Option (List GivensEntry))) : List GivensEntry :=
  L.flatMap fun o => (o.map (padEntries w)).getD []

/-- The padding entry is the identity rotation. -/
@[simp] theorem givensAt_zero (n : ℕ) : givensAt n (0, 0, 0) = 1 := by
  unfold givensAt
  split_ifs <;> simp [givensCoeffs, givens]

/-- Padding does not change the unitary of a log. -/
theorem givensLog_padEntries (n w : ℕ) (es : List GivensEntry) :
    givensLog n (padEntries w es) = givensLog n es := by
  simp [padEntries, givensLog_append, givensLog, List.map_replicate, List.prod_replicate]

/-- The words of the zero fill: `w` zero entries are $5w$ zero words. -/
theorem flatMap_entryWords_padEntries_nil (w : ℕ) :
    (padEntries w []).flatMap entryWords = List.replicate (5 * w) 0 := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [padEntries, List.nil_append, List.length_nil, Nat.sub_zero,
      List.replicate_succ, List.flatMap_cons] at ih ⊢
    rw [ih, show 5 * (w + 1) = 5 + 5 * w by ring, List.replicate_add]
    simp [entryWords]

/-- The words of a list of entries: five per entry. -/
@[simp] theorem length_flatMap_entryWords (es : List GivensEntry) :
    (es.flatMap entryWords).length = 5 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [ih, entryWords]; ring

/-- The words of a padded slot: the words of its entries, then zeros. -/
theorem flatMap_entryWords_padEntries {w : ℕ} {P : List GivensEntry} :
    (padEntries w P).flatMap entryWords =
      P.flatMap entryWords ++ List.replicate (5 * (w - P.length)) 0 := by
  have h := flatMap_entryWords_padEntries_nil (w - P.length)
  simp only [padEntries, List.nil_append, List.length_nil, Nat.sub_zero] at h
  rw [padEntries, List.flatMap_append, h]

/-- The end of slot `j` is at most the start of slot `k > j`. -/
theorem slot_end_le {w j k : ℕ} (hj : j < k) : j * (1 + 5 * w) + 1 + 5 * w ≤ k * (1 + 5 * w) := by
  have := Nat.mul_le_mul_right (1 + 5 * w) (show j + 1 ≤ k by omega)
  rw [Nat.add_mul, one_mul] at this
  omega

/-- **The stored slotted log**: the slots `L` (closed: `none` rejected, `some es` accepted with
at most `w` entries) and the pending entries `P` of slot `L.length` are held at `lg`. A slot
occupies $1 + 5w$ words: the valid word (positive iff accepted) and $w$ entries; a rejected slot
and the unused entries hold the zero fill (or a rejected trial's words, which are never read). -/
def HoldsSlottedLog (lg : ℕ × ℕ) (ns w : ℕ) (L : List (Option (List GivensEntry)))
    (P : List GivensEntry) (s : Store ℝ) : Prop :=
  L.length ≤ ns ∧ P.length ≤ w ∧
  (∀ j (hj : j < L.length), ∃ v : ℝ, s.get lg.1 (lg.2 + j * (1 + 5 * w)) = some v ∧
    match L[j] with
    | none => v ≤ 0
    | some es => 0 < v ∧ es.length ≤ w ∧
        s.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) =
          some ((padEntries w es).flatMap entryWords)) ∧
  (L.length < ns → s.get lg.1 (lg.2 + L.length * (1 + 5 * w)) = some 0 ∧
    s.readBlock lg.1 (lg.2 + L.length * (1 + 5 * w) + 1) (5 * w) =
      some ((padEntries w P).flatMap entryWords)) ∧
  (∀ j, L.length < j → j < ns → s.get lg.1 (lg.2 + j * (1 + 5 * w)) = some 0 ∧
    s.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) =
      some (List.replicate (5 * w) 0))

/-- A stored log reads only the words of its region. -/
theorem readsOnly_holdsSlottedLog (lg : ℕ × ℕ) (ns w : ℕ)
    (L : List (Option (List GivensEntry))) (P : List GivensEntry) :
    Store.ReadsOnly (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (HoldsSlottedLog lg ns w L P) := by
  intro s s' hg ⟨hLn, hPw, hc, hp, hf⟩
  have hget (j : ℕ) (hj : j < ns) :
      s'.get lg.1 (lg.2 + j * (1 + 5 * w)) = s.get lg.1 (lg.2 + j * (1 + 5 * w)) := by
    have := slot_end_le (w := w) hj
    exact hg _ _ ⟨rfl, by omega, by omega⟩
  have hblk (j : ℕ) (hj : j < ns) :
      s'.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) =
        s.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) := by
    have := slot_end_le (w := w) hj
    exact Store.readBlock_congr fun t ht => hg _ _ ⟨rfl, by omega, by omega⟩
  refine ⟨hLn, hPw, fun j hj => ?_, fun h => ?_, fun j hj hjn => ?_⟩
  · obtain ⟨v, hv, hm⟩ := hc j hj
    refine ⟨v, by rw [hget j (by omega)]; exact hv, ?_⟩
    split at hm
    · exact hm
    · exact ⟨hm.1, hm.2.1, by rw [hblk j (by omega)]; exact hm.2.2⟩
  · rw [hget _ h, hblk _ h]; exact hp h
  · rw [hget _ hjn, hblk _ hjn]; exact hf j hj hjn

/-- A stored log is kept by a store that agrees below a boundary above its buffer. -/
theorem HoldsSlottedLog.of_below {lg : ℕ × ℕ} {ns w B : ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {s s' : Store ℝ}
    (h : HoldsSlottedLog lg ns w L P s) (hB : Store.Below B s s') (hlg : lg.1 < B) :
    HoldsSlottedLog lg ns w L P s' :=
  readsOnly_holdsSlottedLog lg ns w L P s s' (fun b i hb => by
    obtain ⟨rfl, -⟩ := hb; exact (hB lg.1 hlg).2 i) h

/-- Rejecting the pending slot closes it as `none`; nothing is written (its valid word is
already zero). -/
theorem HoldsSlottedLog.reject {lg : ℕ × ℕ} {ns w : ℕ} {L : List (Option (List GivensEntry))}
    {P : List GivensEntry} {s : Store ℝ} (h : HoldsSlottedLog lg ns w L P s)
    (hL : L.length < ns) : HoldsSlottedLog lg ns w (L ++ [none]) [] s := by
  obtain ⟨-, -, hc, hp, hf⟩ := h
  refine ⟨by simp; omega, by simp, fun j hj => ?_, fun hj => ?_, fun j hj hjn => ?_⟩
  · simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · obtain ⟨v, hv, hm⟩ := hc j hj
      exact ⟨v, hv, by rwa [List.getElem_append_left hj]⟩
    · exact ⟨0, (hp hL).1, by simp⟩
  · simp only [List.length_append, List.length_singleton] at hj ⊢
    obtain ⟨h1, h2⟩ := hf (L.length + 1) (by omega) hj
    exact ⟨h1, by rw [h2, flatMap_entryWords_padEntries_nil]⟩
  · simp only [List.length_append, List.length_singleton] at hj
    exact hf j (by omega) hjn

/-- Writing an entry: a store that agrees with a stored log off the five words of entry
`P.length` of the pending slot, and holds the words of `e` there, holds the log with `e` appended
to the pending entries. -/
theorem HoldsSlottedLog.of_write_entry {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {s s' : Store ℝ}
    {e : GivensEntry} (h : HoldsSlottedLog lg ns w L P s) (hL : L.length < ns)
    (hP : P.length < w)
    (hfr : s.EqOff (Store.inBlock lg.1 (lg.2 + L.length * (1 + 5 * w) + 1 + 5 * P.length) 5) s')
    (hr : s'.readBlock lg.1 (lg.2 + L.length * (1 + 5 * w) + 1 + 5 * P.length) 5 =
      some (entryWords e)) :
    HoldsSlottedLog lg ns w L (P ++ [e]) s' := by
  obtain ⟨hLn, -, hc, hp, hf⟩ := h
  refine ⟨hLn, by simp; omega, fun j hj => ?_, fun _ => ?_, fun j hj hjn => ?_⟩
  · have he := slot_end_le (w := w) hj
    obtain ⟨v, hv, hm⟩ := hc j hj
    refine ⟨v, by rw [hfr.get_eq (fun hin => by obtain ⟨-, h1, -⟩ := hin; omega)]; exact hv, ?_⟩
    split at hm
    · exact hm
    · exact ⟨hm.1, hm.2.1, hfr.readBlock_of hm.2.2 fun t ht hin => by
        obtain ⟨-, h1, -⟩ := hin; omega⟩
  · obtain ⟨hv, hb⟩ := hp hL
    refine ⟨by rw [hfr.get_eq (fun hin => by obtain ⟨-, h1, -⟩ := hin; omega)]; exact hv, ?_⟩
    rw [flatMap_entryWords_padEntries] at hb
    rw [flatMap_entryWords_padEntries, List.flatMap_append, List.flatMap_singleton]
    have h1 := Store.readBlock_sub hb (o := 0) (n := 5 * P.length) (by omega)
    have h3 := Store.readBlock_sub hb (o := 5 * P.length + 5) (n := 5 * (w - P.length) - 5)
      (by omega)
    simp only [Nat.add_zero, List.drop_zero] at h1
    rw [List.take_left' (by rw [length_flatMap_entryWords])] at h1
    have e3 : List.take (5 * (w - P.length) - 5) (List.drop (5 * P.length + 5)
        (P.flatMap entryWords ++ List.replicate (5 * (w - P.length)) 0)) =
        List.replicate (5 * (w - P.length) - 5) 0 := by
      rw [List.drop_append, List.drop_eq_nil_of_le (by rw [length_flatMap_entryWords]; omega),
        List.nil_append, length_flatMap_entryWords, List.drop_replicate, List.take_replicate]
      congr 1
      omega
    rw [e3] at h3
    have h1' := hfr.readBlock_of h1 fun t ht hin => by obtain ⟨-, h5, -⟩ := hin; omega
    have h3' := hfr.readBlock_of h3 fun t ht hin => by obtain ⟨-, -, h6⟩ := hin; omega
    rw [← Nat.add_assoc] at h3'
    have h4 := Store.readBlock_add (Store.readBlock_add h1' hr) h3'
    rw [show 5 * P.length + 5 + (5 * (w - P.length) - 5) = 5 * w by omega] at h4
    rw [h4]
    congr 3
    simp only [List.length_append, List.length_singleton]
    omega
  · have he := slot_end_le (w := w) (show L.length < j by omega)
    obtain ⟨h1, h2⟩ := hf j (by omega) hjn
    exact ⟨by rw [hfr.get_eq (fun hin => by obtain ⟨-, -, h2⟩ := hin; omega)]; exact h1,
      hfr.readBlock_of h2 fun t ht hin => by obtain ⟨-, -, h2⟩ := hin; omega⟩

/-- Validating the pending slot: a store that agrees with a stored log off the valid word of
the pending slot, and holds a positive word there, holds the log with the pending slot accepted. -/
theorem HoldsSlottedLog.of_validate {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {s s' : Store ℝ} {v : ℝ}
    (h : HoldsSlottedLog lg ns w L P s) (hL : L.length < ns)
    (hfr : s.EqOff (Store.inBlock lg.1 (lg.2 + L.length * (1 + 5 * w)) 1) s')
    (hv : s'.get lg.1 (lg.2 + L.length * (1 + 5 * w)) = some v) (hv0 : 0 < v) :
    HoldsSlottedLog lg ns w (L ++ [some P]) [] s' := by
  obtain ⟨-, hPw, hc, hp, hf⟩ := h
  refine ⟨by simp; omega, Nat.zero_le _, fun j hj => ?_, fun hj => ?_, fun j hj hjn => ?_⟩
  · simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have he := slot_end_le (w := w) hj
      obtain ⟨u, hu, hm⟩ := hc j hj
      refine ⟨u, by rw [hfr.get_eq (fun hin => by obtain ⟨-, h1, -⟩ := hin; omega)]; exact hu,
        ?_⟩
      rw [List.getElem_append_left hj]
      split at hm
      · exact hm
      · exact ⟨hm.1, hm.2.1, hfr.readBlock_of hm.2.2 fun t ht hin => by
          obtain ⟨-, h1, -⟩ := hin; omega⟩
    · refine ⟨v, hv, ?_⟩
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero]
      exact ⟨hv0, hPw, hfr.readBlock_of (hp hL).2 fun t ht hin => by
        obtain ⟨-, -, h2⟩ := hin; omega⟩
  · simp only [List.length_append, List.length_singleton] at hj ⊢
    have he := slot_end_le (w := w) (show L.length < L.length + 1 by omega)
    obtain ⟨h1, h2⟩ := hf (L.length + 1) (by omega) hj
    refine ⟨by rw [hfr.get_eq (fun hin => by obtain ⟨-, -, h2⟩ := hin; omega)]; exact h1, ?_⟩
    rw [flatMap_entryWords_padEntries_nil]
    exact hfr.readBlock_of h2 fun t ht hin => by obtain ⟨-, -, h2⟩ := hin; omega
  · simp only [List.length_append, List.length_singleton] at hj
    have he := slot_end_le (w := w) (show L.length < j by omega)
    obtain ⟨h1, h2⟩ := hf j (by omega) hjn
    exact ⟨by rw [hfr.get_eq (fun hin => by obtain ⟨-, -, h2⟩ := hin; omega)]; exact h1,
      hfr.readBlock_of h2 fun t ht hin => by obtain ⟨-, -, h2⟩ := hin; omega⟩

/-- **The log read from a store**: the `ns` slots of `w` entries at `lg`, a slot accepted (`some`)
iff its valid word is positive, each entry decoded from its five words (the plane by
`Nat.floor`). Unwritten words read as $0$. -/
noncomputable def slottedLogRead (lg : ℕ × ℕ) (ns w : ℕ) (s : Store ℝ) :
    List (Option (List GivensEntry)) :=
  (List.range ns).map fun j =>
    let b := lg.2 + j * (1 + 5 * w)
    let x := fun t => (s.get lg.1 (b + t)).getD 0
    if 0 < x 0 then
      some ((List.range w).map fun i =>
        (⌊x (1 + 5 * i + 0)⌋₊, ⟨x (1 + 5 * i + 1), x (1 + 5 * i + 2)⟩,
          ⟨x (1 + 5 * i + 3), x (1 + 5 * i + 4)⟩))
    else none

/-- Padding twice is padding once. -/
theorem padEntries_padEntries (w : ℕ) (es : List GivensEntry) :
    padEntries w (padEntries w es) = padEntries w es := by
  simp only [padEntries, List.length_append, List.length_replicate]
  rw [show w - (es.length + (w - es.length)) = 0 by omega]
  simp

/-- Padding the accepted slots does not change the entries of a log. -/
theorem slotEntries_map_padEntries (w : ℕ) (L : List (Option (List GivensEntry))) :
    slotEntries w (L.map (Option.map (padEntries w))) = slotEntries w L := by
  simp only [slotEntries, List.flatMap_map]
  congr 1
  funext o
  cases o <;> simp [padEntries_padEntries]

/-- Word $5i + k$ of the words of a list of entries is word $k$ of entry $i$. -/
theorem getD_flatMap_entryWords (es : List GivensEntry) {i k : ℕ} (hi : i < es.length)
    (hk : k < 5) : (es.flatMap entryWords).getD (5 * i + k) 0 = (entryWords es[i]).getD k 0 := by
  induction es generalizing i with
  | nil => simp at hi
  | cons e es ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, List.getD_eq_getElem?_getD, Nat.mul_zero, Nat.zero_add,
        List.getElem_cons_zero]
      rw [List.getElem?_append_left (by simp [entryWords]; omega)]
    | succ i =>
      simp only [List.length_cons] at hi
      simp only [List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem_cons_succ] at ih ⊢
      rw [List.getElem?_append_right (by simp [entryWords]; omega)]
      have h5 : (entryWords e).length = 5 := rfl
      rw [h5, show 5 * (i + 1) + k - 5 = 5 * i + k by omega]
      exact ih (by omega)

/-- The entries decoded from their stored words. -/
private theorem decode_entries {s : Store ℝ} {b off w : ℕ} {es : List GivensEntry}
    (hl : es.length = w) (h : s.readBlock b (off + 1) (5 * w) = some (es.flatMap entryWords)) :
    ((List.range w).map fun i =>
      (⌊(s.get b (off + (1 + 5 * i + 0))).getD 0⌋₊,
        (⟨(s.get b (off + (1 + 5 * i + 1))).getD 0, (s.get b (off + (1 + 5 * i + 2))).getD 0⟩ : ℂ),
        (⟨(s.get b (off + (1 + 5 * i + 3))).getD 0, (s.get b (off + (1 + 5 * i + 4))).getD 0⟩ :
          ℂ))) = es := by
  have hg (i k : ℕ) (hi : i < w) (hk : k < 5) :
      (s.get b (off + (1 + 5 * i + k))).getD 0 = (entryWords es[i]).getD k 0 := by
    rw [show off + (1 + 5 * i + k) = off + 1 + (5 * i + k) by ring,
      Store.get_of_readBlock h (by omega) 0, Option.getD_some,
      getD_flatMap_entryWords es (by omega) hk]
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  simp only [List.length_map, List.length_range] at h1
  rw [hg i 0 h1 (by omega), hg i 1 h1 (by omega), hg i 2 h1 (by omega), hg i 3 h1 (by omega),
    hg i 4 h1 (by omega)]
  simp [entryWords]

/-- A stored closed log reads back as its slots, each accepted slot padded. -/
theorem HoldsSlottedLog.slottedLogRead_eq {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {s : Store ℝ} (h : HoldsSlottedLog lg ns w L [] s)
    (hL : L.length = ns) : slottedLogRead lg ns w s = L.map (Option.map (padEntries w)) := by
  apply List.ext_getElem (by simp [slottedLogRead, hL])
  intro j h1 h2
  simp only [List.length_map] at h2
  obtain ⟨v, hv, hm⟩ := h.2.2.1 j h2
  simp only [slottedLogRead, List.getElem_map, List.getElem_range, Nat.add_zero, hv,
    Option.getD_some]
  split at hm
  · next he => rw [he, if_neg (by linarith)]; rfl
  · next es he =>
    obtain ⟨hv0, hes, hb⟩ := hm
    rw [he, if_pos hv0, Option.map_some]
    congr 1
    exact decode_entries (by simp [padEntries]; omega) hb

/-- A stored closed log is read back up to padding: its valid entries are those of the read. -/
theorem HoldsSlottedLog.slotEntries_read {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {s : Store ℝ} (h : HoldsSlottedLog lg ns w L [] s)
    (hL : L.length = ns) (hpl : ∀ e ∈ slotEntries w L, (e.1 : ℝ) = e.1) :
    slotEntries w L = slotEntries w (slottedLogRead lg ns w s) := by
  rw [h.slottedLogRead_eq hL, slotEntries_map_padEntries]

/-- The Givens coefficients are a measurable function of the pair. -/
theorem measurable_givensCoeffs : Measurable fun z : ℂ × ℂ => givensCoeffs z.1 z.2 := by
  unfold givensCoeffs
  refine Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) measurable_const ?_
  have hs : Measurable fun z : ℂ × ℂ => ((√(‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) : ℝ) : ℂ) := by fun_prop
  exact ((continuous_star.measurable.comp measurable_fst).div hs).prodMk
    ((continuous_star.measurable.comp measurable_snd).div hs)

/-- The rotation of an entry is a measurable function of the entry. -/
theorem measurable_givensAt (n : ℕ) : Measurable (givensAt n) := by
  refine measurable_from_prod_countable_right fun k => ?_
  unfold givensAt
  dsimp only
  split_ifs
  · have hg : Continuous fun cs : ℂ × ℂ =>
        givens (⟨k, by omega⟩ : Fin n) ⟨k + 1, by omega⟩ cs.1 cs.2 := by
      unfold givens; fun_prop
    exact hg.measurable.comp measurable_givensCoeffs
  · exact measurable_const

/-- The unitary of a concatenation of logs is the product of their unitaries. -/
theorem givensLog_flatMap {α : Type*} (n : ℕ) (f : α → List GivensEntry) (L : List α) :
    givensLog n (L.flatMap f) = (L.map fun a => givensLog n (f a)).prod := by
  induction L with
  | nil => rfl
  | cons a L ih => rw [List.flatMap_cons, givensLog_append, ih, List.map_cons, List.prod_cons]

/-- A word of a memory, read as $0$ when unwritten, is measurable. -/
theorem measurable_get_getD (b i : ℕ) :
    Measurable fun m : Mem ℝ => (m.store.get b i).getD 0 :=
  measurable_snd.comp (Mem.measurable_cell (b, i))

/-- A finite product of measurable matrix-valued maps is measurable. -/
private theorem measurable_list_prod {X : Type*} [MeasurableSpace X] {n : ℕ} {ι : Type*}
    (l : List ι) {f : ι → X → Matrix (Fin n) (Fin n) ℂ} (hf : ∀ i ∈ l, Measurable (f i)) :
    Measurable fun x => (l.map fun i => f i x).prod := by
  induction l with
  | nil => exact measurable_const
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hf a (by simp)).mul (ih fun i hi => hf i (by simp [hi]))

/-- The unitary of a slot read under a measurable validity test is measurable. -/
private theorem measurable_givensLog_slot {n w : ℕ} {p : Mem ℝ → Prop} [DecidablePred p]
    (hp : MeasurableSet {m | p m}) {f : Mem ℝ → List GivensEntry}
    (hf : Measurable fun m => givensLog n (padEntries w (f m))) :
    Measurable fun m =>
      givensLog n ((Option.map (padEntries w) (if p m then some (f m) else none)).getD []) := by
  have e : (fun m => givensLog n ((Option.map (padEntries w)
      (if p m then some (f m) else none)).getD [])) =
      fun m => if p m then givensLog n (padEntries w (f m)) else 1 := by
    funext m
    split_ifs <;> rfl
  rw [e]
  exact Measurable.ite hp hf measurable_const

/-- The unitary of the read log is a measurable function of the memory. -/
theorem measurable_givensLog_slottedLogRead (lg : ℕ × ℕ) (ns w n : ℕ) :
    Measurable fun m : Mem ℝ => givensLog n (slotEntries w (slottedLogRead lg ns w m.store)) := by
  simp only [slotEntries, slottedLogRead, List.flatMap_map, givensLog_flatMap]
  refine measurable_list_prod _ fun j _ => ?_
  have hx (t : ℕ) := measurable_get_getD lg.1 (lg.2 + j * (1 + 5 * w) + t)
  refine measurable_givensLog_slot (measurableSet_lt measurable_const (hx 0)) ?_
  simp only [padEntries, List.length_map, List.length_range,
    Nat.sub_self, List.replicate_zero, List.append_nil, givensLog, List.map_map]
  refine measurable_list_prod _ fun i _ => ?_
  refine (continuous_star.measurable.comp (measurable_givensAt n)).comp ?_
  refine (Measurable.nat_floor (hx _)).prodMk (Measurable.prodMk ?_ ?_)
  · exact Complex.equivRealProdCLM.symm.continuous.measurable.comp ((hx _).prodMk (hx _))
  · exact Complex.equivRealProdCLM.symm.continuous.measurable.comp ((hx _).prodMk (hx _))

/-! ### The log programs -/

section Programs

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O]

/-- Zero-fill a log of `ns` slots of `w` entries: `[ns, w] () → (Lg)`. -/
def slottedLogOpen : Impl O Q := opsImpl% [ns, w] () → (Lg) {
  for t < ns * (1 + 5 * w) {
    call (Has.inj (ScalarOp.lit 0)) [] () → (Lg[t])
  }
}

/-- Write entry `i` of slot `j`: the plane `r` as a literal, then the pairs at the views `Pw`,
`Qw`. `[w, j, i, r] (Pw, Qw) → (Lg)`. The producer passes the plane as a dimension and $p, q$ as
views of words it already holds. -/
def slottedLogWrite : Impl O Q := opsImpl% [w, j, i, r] (Pw, Qw) → (Lg) {
  call (Has.inj IndexOp.lit) [r] () → (Lg[j * (1 + 5 * w) + 1 + 5 * i]);
  call (Has.inj ScalarOp.copy) [] (Pw) → (Lg[j * (1 + 5 * w) + 2 + 5 * i]);
  call (Has.inj ScalarOp.copy) [] (Pw[1]) → (Lg[j * (1 + 5 * w) + 3 + 5 * i]);
  call (Has.inj ScalarOp.copy) [] (Qw) → (Lg[j * (1 + 5 * w) + 4 + 5 * i]);
  call (Has.inj ScalarOp.copy) [] (Qw[1]) → (Lg[j * (1 + 5 * w) + 5 + 5 * i])
}

/-- Validate slot `j`: write the literal one to its valid word. `[w, j] () → (Lg)`. -/
def slottedLogValidate : Impl O Q := opsImpl% [w, j] () → (Lg) {
  call (Has.inj IndexOp.lit) [1] () → (Lg[j * (1 + 5 * w)])
}

end Programs

section Specs

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Inhabited ℝ]

/-- A zero-filled log region holds the empty log. -/
theorem holdsSlottedLog_nil_of_readBlock {lg : ℕ × ℕ} {ns w : ℕ} {s : Store ℝ}
    (h : s.readBlock lg.1 lg.2 (ns * (1 + 5 * w)) = some (List.replicate (ns * (1 + 5 * w)) 0)) :
    HoldsSlottedLog lg ns w [] [] s := by
  have hslot (j : ℕ) (hj : j < ns) : s.get lg.1 (lg.2 + j * (1 + 5 * w)) = some 0 ∧
      s.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1) (5 * w) =
        some ((padEntries w []).flatMap entryWords) := by
    have hle : j * (1 + 5 * w) + 1 + 5 * w ≤ ns * (1 + 5 * w) := by
      have := Nat.mul_le_mul_right (1 + 5 * w) (show j + 1 ≤ ns by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
    refine ⟨?_, ?_⟩
    · rw [Store.get_of_readBlock h (j := j * (1 + 5 * w)) (by omega) 0]
      simp
    · rw [flatMap_entryWords_padEntries_nil, add_assoc lg.2,
        Store.readBlock_sub h (o := j * (1 + 5 * w) + 1) (n := 5 * w) (by omega)]
      simp only [List.drop_replicate, List.take_replicate]
      congr 2
      omega
  refine ⟨Nat.zero_le _, Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero _),
    fun hn => hslot 0 hn, fun j _ hj => ?_⟩
  obtain ⟨h1, h2⟩ := hslot j hj
  exact ⟨h1, by rw [h2, flatMap_entryWords_padEntries_nil]⟩

omit [Has IndexOp O] in
/-- Opening a log stores the empty log. -/
theorem slottedLogOpen_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) {ns w : ℕ} {lg : ℕ × ℕ} {τ : Tape ℝ}
    {μ : Mem ℝ} (hl : μ.Live [lg]) (hroom : lg.2 + ns * (1 + 5 * w) ≤ μ.store.len lg.1) :
    Writes .total I τ (slottedLogOpen (O := O) (Q := Q)).body (Env.frame [ns, w] [lg])
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsSlottedLog lg ns w [] [] μ'.store) μ := by
  have h0 : Mch.lit 0 = 0 := by simpa using hM.lit 0
  unfold slottedLogOpen
  refine (writes_fill (v := fun _ => (0 : ℝ)) (pos := fun _ => μ.pos) rfl rfl
    fun i hi m' hfr _ hp => ?_).mono le_rfl ?_
  · refine (writes_call_const (hS (.lit 0)) rfl trivial ?_).mono le_rfl ?_
    · dsimp only; rw [hfr.len_eq]; omega
    · exact fun m'' _ ⟨hp', hg⟩ => ⟨by simpa [h0] using hg, hp'.trans hp⟩
  · rintro μ' - ⟨hv, hp⟩
    refine ⟨hp, holdsSlottedLog_nil_of_readBlock ?_⟩
    rw [Store.holdsVec_iff_readBlock.mp hv]
    simp

/-- Writing an entry appends it to the pending slot. The plane is an exact natural below
`nmax` (`hNat`); this hypothesis belongs to the log, not to the producer. -/
theorem slottedLogWrite_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I)
    (hL : IsIndexLit Mch I) {nmax : ℕ} (hNat : IsExactNatLit id Mch nmax) {ns w r : ℕ}
    (hr : r ≤ nmax) {lg pw qw : ℕ × ℕ} {L : List (Option (List GivensEntry))}
    {P : List GivensEntry} {p q : ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (h : HoldsSlottedLog lg ns w L P μ.store) (hL : L.length < ns) (hP : P.length < w)
    (hp : μ.store.readBlock pw.1 pw.2 2 = some [p.re, p.im])
    (hq : μ.store.readBlock qw.1 qw.2 2 = some [q.re, q.im]) (hl : μ.Live [pw, qw, lg])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock pw.1 pw.2 2 ⊔ Store.inBlock qw.1 qw.2 2)) :
    Writes .total I τ (slottedLogWrite (O := O) (Q := Q)).body
      (Env.frame [w, L.length, P.length, r] [pw, qw, lg])
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsSlottedLog lg ns w L (P ++ [(r, p, q)]) μ'.store) μ := by
  set o := lg.2 + L.length * (1 + 5 * w) + 1 + 5 * P.length with ho
  have hout (k : ℕ) (e : IExp) (he : e.eval [w, L.length, P.length, r, pw.2, qw.2, lg.2] =
      some (o + k)) :
      Operand.evalList (Env.frame [w, L.length, P.length, r] [pw, qw, lg]) [⟨2, e⟩] =
        some [(lg.1, o + k)] := by
    simp [Operand.evalList, Operand.eval, Env.frame, he]
  have hend := slot_end_le (w := w) hL
  have hlen : o + 5 ≤ μ.store.len lg.1 := by
    have := Store.le_len_of_readBlock (h.2.2.2.1 hL).2 (by omega)
    omega
  have hsub (k : ℕ) (hk : k < 5) : Store.inBlock lg.1 (o + k) 1 ≤ Store.inBlock lg.1 o 5 :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hdk (k : ℕ) (hk : k < 5) : Fp.Disj (Store.inBlock lg.1 (o + k) 1)
      (Store.inBlock pw.1 pw.2 2 ⊔ Store.inBlock qw.1 qw.2 2) :=
    hd.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) le_rfl
  have hRO := (Store.readsOnly_readBlock pw.1 pw.2 2 [p.re, p.im]).and
    (Store.readsOnly_readBlock qw.1 qw.2 2 [q.re, q.im])
  have hcell (k k' : ℕ) (hk : k < k') : Fp.Disj (Store.inBlock lg.1 (o + k') 1)
      (Store.inBlock lg.1 (o + k) 1) := Fp.disj_inBlock_of_le (by omega) |>.symm
  have hgp (s : Store ℝ) (h : s.readBlock pw.1 pw.2 2 = some [p.re, p.im] ∧
      s.readBlock qw.1 qw.2 2 = some [q.re, q.im]) :
      s.get pw.1 pw.2 = some p.re ∧ s.get pw.1 (pw.2 + 1) = some p.im ∧
      s.get qw.1 qw.2 = some q.re ∧ s.get qw.1 (qw.2 + 1) = some q.im :=
    ⟨by simpa using Store.get_of_readBlock h.1 (j := 0) (by omega) 0,
      by simpa using Store.get_of_readBlock h.1 (j := 1) (by omega) 0,
      by simpa using Store.get_of_readBlock h.2 (j := 0) (by omega) 0,
      by simpa using Store.get_of_readBlock h.2 (j := 1) (by omega) 0⟩
  have W : Writes .total I τ (slottedLogWrite (O := O) (Q := Q)).body
      (Env.frame [w, L.length, P.length, r] [pw, qw, lg]) (Store.inBlock lg.1 o 5)
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock lg.1 o 5 = some (entryWords (r, p, q))) μ := by
    unfold slottedLogWrite
    refine (writes_indexLit (M := Mch) (by assumption) (n := r) (z := (lg.1, o + 0)) rfl
      (by simp [Operand.eval, Env.frame, ho]) (by dsimp only; omega)).seq_le (hsub 0 (by omega))
      fun m₁ hf₁ ⟨p₁, g₀⟩ => ?_
    have i₁ := hf₁.keep hRO (hdk 0 (by omega)) ⟨hp, hq⟩
    refine (writes_call_un (hS .copy) rfl (hout 1 _ (by simp [IExp.eval, ho]; omega)) trivial
      (hgp _ i₁).1 rfl (by dsimp only; rw [hf₁.len_eq]; omega)).seq_le (hsub 1 (by omega))
      fun m₂ hf₂ ⟨p₂, g₁⟩ => ?_
    have i₂ := hf₂.keep hRO (hdk 1 (by omega)) i₁
    refine (writes_call_un (hS .copy) rfl (hout 2 _ (by simp [IExp.eval, ho]; omega)) trivial
      (hgp _ i₂).2.1 rfl (by dsimp only; rw [hf₂.len_eq, hf₁.len_eq]; omega)).seq_le
      (hsub 2 (by omega)) fun m₃ hf₃ ⟨p₃, g₂⟩ => ?_
    have i₃ := hf₃.keep hRO (hdk 2 (by omega)) i₂
    refine (writes_call_un (hS .copy) rfl (hout 3 _ (by simp [IExp.eval, ho]; omega)) trivial
      (hgp _ i₃).2.2.1 rfl (by dsimp only; rw [hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; omega)).seq_le
      (hsub 3 (by omega)) fun m₄ hf₄ ⟨p₄, g₃⟩ => ?_
    have i₄ := hf₄.keep hRO (hdk 3 (by omega)) i₃
    refine (writes_call_un (hS .copy) rfl (hout 4 _ (by simp [IExp.eval, ho]; omega)) trivial
      (hgp _ i₄).2.2.2 rfl
      (by dsimp only; rw [hf₄.len_eq, hf₃.len_eq, hf₂.len_eq, hf₁.len_eq]; omega)).mono
      (hsub 4 (by omega)) fun m₅ hf₅ ⟨p₅, g₄⟩ => ?_
    have k₀ := hf₅.keep (Store.readsOnly_get _ _ _) (hcell 0 4 (by omega)) <|
      hf₄.keep (Store.readsOnly_get _ _ _) (hcell 0 3 (by omega)) <|
      hf₃.keep (Store.readsOnly_get _ _ _) (hcell 0 2 (by omega)) <|
      hf₂.keep (Store.readsOnly_get _ _ _) (hcell 0 1 (by omega)) g₀
    have k₁ := hf₅.keep (Store.readsOnly_get _ _ _) (hcell 1 4 (by omega)) <|
      hf₄.keep (Store.readsOnly_get _ _ _) (hcell 1 3 (by omega)) <|
      hf₃.keep (Store.readsOnly_get _ _ _) (hcell 1 2 (by omega)) g₁
    have k₂ := hf₅.keep (Store.readsOnly_get _ _ _) (hcell 2 4 (by omega)) <|
      hf₄.keep (Store.readsOnly_get _ _ _) (hcell 2 3 (by omega)) g₂
    have k₃ := hf₅.keep (Store.readsOnly_get _ _ _) (hcell 3 4 (by omega)) g₃
    have hr' : (Mch.lit (r : ℚ)) = (r : ℝ) := hNat r hr
    refine ⟨p₅.trans (p₄.trans (p₃.trans (p₂.trans p₁))),
      Store.readBlock_eq_some_iff.mpr ⟨rfl, fun t ht => ?_⟩⟩
    interval_cases t
    · simpa [entryWords, hr'] using k₀
    · simpa [entryWords] using k₁
    · simpa [entryWords] using k₂
    · simpa [entryWords] using k₃
    · simpa [entryWords] using g₄
  refine W.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) fun μ' hfr hr => ?_
  exact ⟨hr.1, h.of_write_entry hL hP hfr hr.2⟩

/-- Validating the pending slot closes it as accepted, on a machine whose literal one is
positive. -/
theorem slottedLogValidate_writes_of_pos {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit Mch I) (h1 : 0 < Mch.lit 1) {ns w : ℕ} {lg : ℕ × ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {τ : Tape ℝ} {μ : Mem ℝ}
    (h : HoldsSlottedLog lg ns w L P μ.store) (hL' : L.length < ns) :
    Writes .total I τ (slottedLogValidate (O := O) (Q := Q)).body
      (Env.frame [w, L.length] [lg]) (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsSlottedLog lg ns w (L ++ [some P]) [] μ'.store) μ := by
  have hle := slot_end_le (w := w) hL'
  unfold slottedLogValidate
  refine (writes_indexLit hL (n := 1) (z := (lg.1, lg.2 + L.length * (1 + 5 * w))) rfl rfl
    (Store.lt_len_of_get (h.2.2.2.1 hL').1)).mono
    (Fp.inBlock_le_inBlock (by omega) (by omega)) fun μ' hfr ⟨hp, hg⟩ => ?_
  exact ⟨hp, h.of_validate hL' hfr hg (by simpa using h1)⟩

/-- Validating the pending slot closes it as accepted. -/
theorem slottedLogValidate_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hL : IsIndexLit Mch I) (hM : StdModel u id Mch) (hu : u < 1) {ns w : ℕ} {lg : ℕ × ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {τ : Tape ℝ} {μ : Mem ℝ}
    (h : HoldsSlottedLog lg ns w L P μ.store) (hL' : L.length < ns) (hl : μ.Live [lg]) :
    Writes .total I τ (slottedLogValidate (O := O) (Q := Q)).body
      (Env.frame [w, L.length] [lg]) (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsSlottedLog lg ns w (L ++ [some P]) [] μ'.store) μ := by
  have h1 : 0 < Mch.lit 1 := by
    have := abs_le.mp (hM.lit 1)
    simp only [id, Rat.cast_one, abs_one, mul_one] at this
    linarith [this.1]
  exact slottedLogValidate_writes_of_pos hL h1 h hL'

end Specs

/-! ### Replay -/

section Replay

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- Rotate rows `r, r + 1` of the leading-dimension-`ld` matrix over the columns
`j0, …, j0 + nc - 1`: `[ld, r, j0, nc] (A, C, S, T) → (A)`. `NLAlib.rotateRowsWithScratch` is
the full range `[n, k, 0, n]`. -/
def rotateRowsOn : Impl O Q := opsImpl% [ld, r, j0, nc] (A, C, S, T) → (A) {
  for j < nc {
    run (rotateLeftWithScratch (Op := O) (Tst := Q)).body []
      (C, S, A[2 * ((j0 + j) * ld + r)], A[2 * ((j0 + j) * ld + r + 1)], T,
        A[2 * ((j0 + j) * ld + r)], A[2 * ((j0 + j) * ld + r + 1)])
  }
}

/-- Rotate columns `c, c + 1` over the rows `i0, …, i0 + nr - 1`:
`[ld, c, i0, nr] (A, C, S, T) → (A)`. -/
def rotateColumnsOn : Impl O Q := opsImpl% [ld, c, i0, nr] (A, C, S, T) → (A) {
  for i < nr {
    run (rotateRightWithScratch (Op := O) (Tst := Q)).body []
      (C, S, A[2 * (c * ld + i0 + i)], A[2 * ((c + 1) * ld + i0 + i)], T,
        A[2 * (c * ld + i0 + i)], A[2 * ((c + 1) * ld + i0 + i)])
  }
}

/-- **Replay a log on rows**: for the valid slots in order (`ns` slots of `w` entries), recompute
each entry's coefficients and rotate the rows `lo + r, lo + r + 1` of `A` over the columns
`j0, …, j0 + nc - 1`. The plane is read with the bound `ld`.
`[ld, lo, j0, nc, ns, w] (Lg, A) → (A)`. -/
def givensReplayRows : Impl O Q := opsImpl% [ld, lo, j0, nc, ns, w] (Lg, A) → (A) {
  let Cf ← alloc 4;
  let T ← alloc 10;
  for s < ns {
    if (Has.inj CmpTst.isPos) [] (Lg[s * (1 + 5 * w)]) {
      for i < w {
        let r ← index (Has.inj IdxTst.toNat) (Lg[s * (1 + 5 * w) + 1 + 5 * i]) ≤ ld;
        run (coefficients (Op := O) (Tst := Q)).body []
          (Lg[s * (1 + 5 * w) + 2 + 5 * i], Lg[s * (1 + 5 * w) + 4 + 5 * i], Cf, Cf[2]);
        run (rotateRowsOn (O := O) (Q := Q)).body [ld, lo + r, j0, nc] (A, Cf, Cf[2], T, A)
      }
    } else { skip }
  }
}

/-- **Replay a log on columns** (right multiplication by the computed adjoint rotations) over the
rows `i0, …, i0 + nr - 1`. `[ld, lo, i0, nr, ns, w] (Lg, A) → (A)`. -/
def givensReplayColumns : Impl O Q := opsImpl% [ld, lo, i0, nr, ns, w] (Lg, A) → (A) {
  let Cf ← alloc 4;
  let T ← alloc 10;
  for s < ns {
    if (Has.inj CmpTst.isPos) [] (Lg[s * (1 + 5 * w)]) {
      for i < w {
        let r ← index (Has.inj IdxTst.toNat) (Lg[s * (1 + 5 * w) + 1 + 5 * i]) ≤ ld;
        run (coefficients (Op := O) (Tst := Q)).body []
          (Lg[s * (1 + 5 * w) + 2 + 5 * i], Lg[s * (1 + 5 * w) + 4 + 5 * i], Cf, Cf[2]);
        run (rotateColumnsOn (O := O) (Q := Q)).body [ld, lo + r, i0, nr] (A, Cf, Cf[2], T, A)
      }
    } else { skip }
  }
}

end Replay

section ReplaySpecs

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]
  [Inhabited ℝ]

/-- **The column replay on every tape**: the stored matrix moves from $\mathbf{X}$ to within
$((1 + 24\boldsymbol{u})^{m} - 1)\|\mathbf{X}\|_2$ of $\mathbf{X}\widetilde{\mathbf{V}}$, where
$\widetilde{\mathbf{V}}$ acts by the log's unitary on the range $[lo, lo + d)$ and $m$ is the
capacity $ns \cdot w$ (each replayed rotation, padding included, costs at most
$24\boldsymbol{u}$; [Higham2002, Lemma 19.8]). Needs only exact naturals up to the order. -/
theorem givensReplayColumns_specNorm_sub_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hQ : IsToNat id I) (hC : IsCmp id I) {N lo d ns w : ℕ} (hN : lo + d ≤ N)
    {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < d ∨ e = (0, 0, 0)) {lg x : ℕ × ℕ}
    {X : Matrix (Fin N) (Fin N) ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hlog : HoldsSlottedLog lg ns w L P μ.store) (hlen : L.length = ns)
    (hX : HoldsMatrix x X μ.store) (hl : μ.Live [lg, x])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock x.1 x.2 (2 * (N * N)))) :
    Writes .total I τ (givensReplayColumns (O := O) (Q := Q)).body
      (Env.frame [N, lo, 0, N, ns, w] [lg, x, x]) (Store.inBlock x.1 x.2 (2 * (N * N)))
      (fun μ' => ∃ X' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix x X' μ'.store ∧
        specNorm (X' - X * embedBlock lo (givensLog d (slotEntries w L))) ≤
          ((1 + 24 * u) ^ (ns * w) - 1) * specNorm X) μ := sorry

/-- **The row replay on a column range on every tape**: the columns outside
$[j_0, j_0 + n_c)$ are kept and, on the range, the stored matrix is within
$((1 + 24\boldsymbol{u})^{ns\,w} - 1)\|\mathbf{X}\|_2$ of $\widetilde{\mathbf{V}}^{\mathsf H}
\mathbf{X}$. -/
theorem givensReplayRows_specNorm_sub_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hQ : IsToNat id I) (hC : IsCmp id I) {N lo d j0 nc ns w : ℕ} (hN : lo + d ≤ N)
    (hj : j0 + nc ≤ N) {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < d ∨ e = (0, 0, 0)) {lg x : ℕ × ℕ}
    {X : Matrix (Fin N) (Fin N) ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hlog : HoldsSlottedLog lg ns w L P μ.store) (hlen : L.length = ns)
    (hX : HoldsMatrix x X μ.store) (hl : μ.Live [lg, x])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock x.1 x.2 (2 * (N * N)))) :
    Writes .total I τ (givensReplayRows (O := O) (Q := Q)).body
      (Env.frame [N, lo, j0, nc, ns, w] [lg, x, x]) (Store.inBlock x.1 x.2 (2 * (N * N)))
      (fun μ' => ∃ X' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix x X' μ'.store ∧
        (∀ i j : Fin N, ¬(j0 ≤ (j : ℕ) ∧ (j : ℕ) < j0 + nc) → X' i j = X i j) ∧
        specNorm (Matrix.of fun i j : Fin N => if j0 ≤ (j : ℕ) ∧ (j : ℕ) < j0 + nc then
          (X' - (embedBlock lo (givensLog d (slotEntries w L)))ᴴ * X :
            Matrix (Fin N) (Fin N) ℂ) i j else 0) ≤
          ((1 + 24 * u) ^ (ns * w) - 1) * specNorm X) μ := sorry

/-- **The accumulated product from the identity**: with $24R\boldsymbol{u} \le 1/8$,
$(1 + 24\boldsymbol{u})^R - 1 \le 27R\boldsymbol{u}$. -/
theorem one_add_mul_pow_sub_one_le {u : ℝ} {R : ℕ} (hu : 0 ≤ u) (hR : 24 * R * u ≤ 1 / 8) :
    (1 + 24 * u) ^ R - 1 ≤ 27 * R * u := by
  have h := one_add_pow_sub_one_le (x := 24 * u) (n := R) (by positivity) (by nlinarith)
  have hR : 0 ≤ (R : ℝ) * (24 * u) := by positivity
  nlinarith

end ReplaySpecs

end NLAlib
