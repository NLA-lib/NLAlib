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

/-- Opening a log stores the empty log. -/
theorem slottedLogOpen_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) {ns w : ℕ} {lg : ℕ × ℕ} {τ : Tape ℝ}
    {μ : Mem ℝ} (hl : μ.Live [lg]) (hroom : lg.2 + ns * (1 + 5 * w) ≤ μ.store.len lg.1) :
    Writes .total I τ (slottedLogOpen (O := O) (Q := Q)).body (Env.frame [ns, w] [lg])
      (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => HoldsSlottedLog lg ns w [] [] μ'.store) μ := sorry

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
      (fun μ' => HoldsSlottedLog lg ns w L (P ++ [(r, p, q)]) μ'.store) μ := sorry

/-- Validating the pending slot closes it as accepted. -/
theorem slottedLogValidate_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hL : IsIndexLit Mch I) (hM : StdModel u id Mch) (hu : u < 1) {ns w : ℕ} {lg : ℕ × ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {τ : Tape ℝ} {μ : Mem ℝ}
    (h : HoldsSlottedLog lg ns w L P μ.store) (hL' : L.length < ns) (hl : μ.Live [lg]) :
    Writes .total I τ (slottedLogValidate (O := O) (Q := Q)).body
      (Env.frame [w, L.length] [lg]) (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => HoldsSlottedLog lg ns w (L ++ [some P]) [] μ'.store) μ := sorry

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
