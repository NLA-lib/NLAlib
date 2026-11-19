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
# Slotted logs of Givens rotations

A program that applies Givens rotations records each committed rotation as a self-describing
entry $(r, p, q)$: the plane $r$ (rows or columns $r, r + 1$) and the two inputs $p, q$ of the
coefficient program `NLAlib.coefficients`. The entries live in a **slotted static log**: `ns` slots
of $1 + 5w$ words, a valid word (positive iff the slot was accepted) and $w$ entries of five words
$(r, \Re p, \Im p, \Re q, \Im q)$. There is no count word: the layout is static, the only natural
written is the plane, and an unused entry is the zero fill $(0, 0, 0)$, whose rotation is the
identity (`NLAlib.givensAt_zero`). A trial writes straight into its own slot (the pending entries);
acceptance validates the slot. The exact unitary of a log is `NLAlib.givensLog` of its valid
entries (`NLAlib.slotEntries`). Its replay is `NLAlib.Matrix.FinitePrecision.GivensReplay`.

## Main definitions

* `NLAlib.GivensEntry`, `NLAlib.slotEntries`, `NLAlib.padEntries`, `NLAlib.HoldsSlottedLog`.
* `NLAlib.slottedLogRead`: the log read back from a store (for measurability).
* `NLAlib.slottedLogOpen`, `NLAlib.slottedLogWrite`, `NLAlib.slottedLogValidate`: zero-fill the
  log, write an entry of a slot, validate a slot.

## Main results

* `NLAlib.slottedLogOpen_writes`, `NLAlib.slottedLogWrite_writes`,
  `NLAlib.slottedLogValidate_writes`: the log programs move the stored log.
* `NLAlib.isRoundedRowRotation_machineRowRotation`,
  `NLAlib.isRoundedColRotation_machineColRotation`: the rotations computed from rounded
  coefficients are rounded Givens rotations.
-/

@[expose] public section

namespace NLAlib

open Ops
open scoped Matrix

/-! ### Machine rotations are rounded rotations -/

section MachineRound

variable {M : Machine ℝ} {u : ℝ} {n : ℕ} {i j : Fin n}

/-- **The machine row rotation is a rounded rotation**: on a machine with the standard model at
$0 \le \boldsymbol{u} \le 1/100$, rotating the rows $i \ne j$ of $\mathbf{Z}$ by the coefficients
computed from $(p, q)$ is within $12\boldsymbol{u}$, per column pair, of the exact Givens rotation
of $(p, q)$. [Higham2002, Lemma 19.8]. -/
theorem isRoundedRowRotation_machineRowRotation (hM : StdModel u id M) (hu : 0 ≤ u)
    (hu' : u ≤ 1 / 100) (hij : i ≠ j) (p q : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    IsRoundedRowRotation (12 * u) i j (givensCoeffs p q).1 (givensCoeffs p q).2 Z
      (machineRowRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2 Z) := by
  obtain ⟨h1, h2⟩ := hM.norm_roundedGivensCoeffs_sub_le hu hu' p q
  refine ⟨fun r k hri hrj => machineRowRotation_apply_of_ne hri hrj k, fun k => ?_⟩
  have hneg (r : ℝ) : M.neg r = -r := hM.neg r
  set c := (roundedGivensCoeffs M p q).1
  set s := (roundedGivensCoeffs M p q).2
  have e1 : (⟨M.neg s.re, s.im⟩ : ℂ) = -star s := by apply Complex.ext <;> simp [hneg]
  have e2 : (⟨c.re, M.neg c.im⟩ : ℂ) = star c := by apply Complex.ext <;> simp [hneg]
  rw [machineRowRotation_apply_left, machineRowRotation_apply_right hij,
    givens_mul_apply_left hij, givens_mul_apply_right hij, e1, e2]
  exact hM.norm_linearWords_rotation_sub_le hu hu' (norm_givensCoeffs_fst_sq_add p q) h1 h2 _ _

/-- **The machine column rotation is a rounded rotation**: on a machine with the standard model
at $0 \le \boldsymbol{u} \le 1/100$, rotating the columns $i \ne j$ of $\mathbf{Z}$ by the
adjoint of the rotation of the coefficients computed from $(p, q)$ is within $12\boldsymbol{u}$,
per row pair, of the adjoint of the exact Givens rotation of $(p, q)$. [Higham2002, Lemma 19.8]. -/
theorem isRoundedColRotation_machineColRotation (hM : StdModel u id M) (hu : 0 ≤ u)
    (hu' : u ≤ 1 / 100) (hij : i ≠ j) (p q : ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    IsRoundedColRotation (12 * u) i j (givensCoeffs p q).1 (givensCoeffs p q).2 Z
      (machineColRotation M i j (roundedGivensCoeffs M p q).1 (roundedGivensCoeffs M p q).2 Z) := by
  obtain ⟨h1, h2⟩ := hM.norm_roundedGivensCoeffs_sub_le hu hu' p q
  refine ⟨fun r k hki hkj => machineColRotation_apply_of_ne hki hkj r, fun r => ?_⟩
  have hneg (r : ℝ) : M.neg r = -r := hM.neg r
  set c := (roundedGivensCoeffs M p q).1
  set s := (roundedGivensCoeffs M p q).2
  set c₀ := (givensCoeffs p q).1
  set s₀ := (givensCoeffs p q).2
  have e1 : (⟨c.re, M.neg c.im⟩ : ℂ) = star c := by apply Complex.ext <;> simp [hneg]
  have e2 : (⟨s.re, M.neg s.im⟩ : ℂ) = star s := by apply Complex.ext <;> simp [hneg]
  have e3 : (⟨M.neg s.re, M.neg s.im⟩ : ℂ) = -s := by apply Complex.ext <;> simp [hneg]
  have g1 : (Z * (givens i j c₀ s₀)ᴴ) r i = star c₀ * Z r i + star s₀ * Z r j := by
    rw [conjTranspose_givens, mul_givens_apply_left hij]
    simp only [star_neg]
    ring
  have g2 : (Z * (givens i j c₀ s₀)ᴴ) r j = -s₀ * Z r i + c₀ * Z r j := by
    rw [conjTranspose_givens, mul_givens_apply_right hij, star_star]
    ring
  rw [machineColRotation_apply_left, machineColRotation_apply_right hij, g1, g2, e1, e2, e3]
  have h := hM.norm_linearWords_rotation_sub_le hu hu'
    (a := star c) (b := star s) (α := star c₀) (β := star s₀)
    (by rw [norm_star, norm_star]; exact norm_givensCoeffs_fst_sq_add p q)
    (by rw [← star_sub, norm_star, norm_star]; exact h1)
    (by rw [← star_sub, norm_star, norm_star]; exact h2) (Z r i) (Z r j)
  simp only [star_star] at h
  exact h

/-- Under the standard model a rounded complex linear combination of two zeros is zero. -/
theorem linearComplex_zero_zero (hM : StdModel u id M) (a b : ℂ) :
    linearComplex M a b 0 0 = 0 := by
  have hmul : ∀ x : ℝ, M.mul x 0 = 0 := fun x => by simpa using hM.mul x 0
  have hadd : M.add 0 0 = 0 := by simpa using hM.add 0 0
  have hsub : M.sub 0 0 = 0 := by simpa using hM.sub 0 0
  apply Complex.ext <;> simp [linearComplex, Pair.linearWords, hmul, hadd, hsub]

end MachineRound

/-! ### Embedded blocks -/

section EmbedBlock

variable {N lo d : ℕ}

/-- The embedded identity is the identity. -/
@[simp] theorem embedBlock_one :
    embedBlock (N := N) lo (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext i j
  simp only [embedBlock, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- Embedding commutes with the adjoint. -/
theorem embedBlock_conjTranspose (V : Matrix (Fin d) (Fin d) ℂ) :
    (embedBlock (N := N) lo V)ᴴ = embedBlock lo Vᴴ := by
  ext i j
  simp only [embedBlock, Matrix.conjTranspose_apply, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

/-- Embedding is multiplicative when the range fits: $\widetilde{\mathbf{A}\mathbf{B}} =
\widetilde{\mathbf{A}}\widetilde{\mathbf{B}}$ for $lo + d \le N$. -/
theorem embedBlock_mul (hN : lo + d ≤ N) (A B : Matrix (Fin d) (Fin d) ℂ) :
    embedBlock (N := N) lo (A * B) = embedBlock lo A * embedBlock lo B := by
  ext i k
  rw [Matrix.mul_apply]
  by_cases hi : lo ≤ (i : ℕ) ∧ (i : ℕ) < lo + d
  · by_cases hk : lo ≤ (k : ℕ) ∧ (k : ℕ) < lo + d
    · simp only [embedBlock, Matrix.of_apply, dif_pos hi, dif_pos hk, Matrix.mul_apply]
      refine Fintype.sum_of_injective (fun j : Fin d => (⟨lo + j, by omega⟩ : Fin N))
        (fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)) _ _
        (fun j hj => ?_) (fun j => ?_)
      · rw [dif_neg fun hj' => hj ⟨⟨(j : ℕ) - lo, by omega⟩, Fin.ext (by simp; omega)⟩,
          zero_mul]
      · simp only [dif_pos (show lo ≤ lo + (j : ℕ) ∧ lo + (j : ℕ) < lo + d by omega)]
        congr 2 <;> exact Fin.ext (by simp)
    · simp only [embedBlock, Matrix.of_apply, dif_pos hi, dif_neg hk]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      by_cases hj : lo ≤ (j : ℕ) ∧ (j : ℕ) < lo + d
      · rw [dif_pos hj, dif_pos hj, mul_zero]
      · rw [dif_neg hj, zero_mul]
  · simp only [embedBlock, Matrix.of_apply, dif_neg hi]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj), zero_mul])
      (by simp), if_pos rfl, one_mul, dif_neg hi]

/-- The rotation of an entry inside the block, embedded, is the rotation of the shifted entry. -/
theorem embedBlock_givensAt (hN : lo + d ≤ N) {e : ℕ × ℂ × ℂ} (he : e.1 + 1 < d) :
    embedBlock (N := N) lo (givensAt d e) = givensAt N (lo + e.1, e.2) := by
  have hij : (⟨e.1, by omega⟩ : Fin d) ≠ ⟨e.1 + 1, he⟩ := Fin.ne_of_val_ne (by simp)
  have hij' : (⟨lo + e.1, by omega⟩ : Fin N) ≠ ⟨lo + e.1 + 1, by omega⟩ :=
    Fin.ne_of_val_ne (by simp)
  ext a b
  simp only [embedBlock, givensAt, dif_pos he, dif_pos (show lo + e.1 + 1 < N by omega),
    Matrix.of_apply, givens_apply hij, givens_apply hij', Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The block of the whole range is the matrix itself. -/
@[simp] theorem embedBlock_zero_self (V : Matrix (Fin N) (Fin N) ℂ) :
    embedBlock (N := N) 0 V = V := by
  ext i j
  simp [embedBlock]

end EmbedBlock

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

/-- The entries of a concatenation of slots. -/
@[simp] theorem slotEntries_append (w : ℕ) (L L' : List (Option (List GivensEntry))) :
    slotEntries w (L ++ L') = slotEntries w L ++ slotEntries w L' := by
  simp [slotEntries]

/-- The entries of one accepted slot are its padded entries. -/
@[simp] theorem slotEntries_some (w : ℕ) (es : List GivensEntry) :
    slotEntries w [some es] = padEntries w es := by
  simp [slotEntries]

/-- A rejected slot has no entries. -/
@[simp] theorem slotEntries_none (w : ℕ) : slotEntries w [none] = [] := by
  simp [slotEntries]

/-- The padding entry is the identity rotation. -/
@[simp] theorem givensAt_zero (n : ℕ) : givensAt n (0, 0, 0) = 1 := by
  unfold givensAt
  split_ifs <;> simp [givensCoeffs, givens]

/-- Padding does not change the unitary of a log. -/
theorem givensLog_padEntries (n w : ℕ) (es : List GivensEntry) :
    givensLog n (padEntries w es) = givensLog n es := by
  simp [padEntries, givensLog, List.map_replicate, List.prod_replicate]

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

/-- An entry has five words. -/
@[simp] theorem length_entryWords (e : GivensEntry) : (entryWords e).length = 5 := rfl

/-- The words of a list of entries: five per entry. -/
theorem length_flatMap_entryWords (es : List GivensEntry) :
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

/-- A stored log has at most `w` entries per closed slot. -/
theorem HoldsSlottedLog.length_slotEntries_le {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {s : Store ℝ}
    (h : HoldsSlottedLog lg ns w L P s) : (slotEntries w L).length ≤ L.length * w := by
  have hc : ∀ o ∈ L, ∀ es, o = some es → es.length ≤ w := by
    intro o ho es hes
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ho
    obtain ⟨v, -, hm⟩ := h.2.2.1 j hj
    rw [hes] at hm
    exact hm.2.1
  clear h
  induction L with
  | nil => simp [slotEntries]
  | cons o L ih =>
    rw [show o :: L = [o] ++ L from rfl, slotEntries_append]
    simp only [List.length_append, List.length_singleton]
    have h2 := ih fun o' ho' => hc o' (by simp [ho'])
    have h1 : (slotEntries w [o]).length ≤ w := by
      cases o with
      | none => simp
      | some es =>
        have := hc _ (by simp) es rfl
        simp [padEntries]; omega
    rw [Nat.add_mul, one_mul]
    omega

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

/-- Rejecting every slot still open closes the log. -/
theorem HoldsSlottedLog.close {lg : ℕ × ℕ} {ns w : ℕ} {L : List (Option (List GivensEntry))}
    {s : Store ℝ} (h : HoldsSlottedLog lg ns w L [] s) :
    HoldsSlottedLog lg ns w (L ++ List.replicate (ns - L.length) none) [] s := by
  obtain ⟨k, hk⟩ : ∃ k, ns - L.length = k := ⟨_, rfl⟩
  rw [hk]
  induction k generalizing L with
  | zero => simpa using h
  | succ k ih =>
    have hlt : L.length < ns := by omega
    have := ih (h.reject hlt) (by simp; omega)
    rwa [List.append_assoc, List.singleton_append, ← List.replicate_succ] at this

/-- Rejected slots have no entries. -/
theorem slotEntries_append_replicate_none (w k : ℕ)
    (L : List (Option (List GivensEntry))) :
    slotEntries w (L ++ List.replicate k none) = slotEntries w L := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ', ← List.append_assoc, slotEntries_append, ih, slotEntries_none,
      List.append_nil]

/-- The unitary of a log of accepted slots is the unitary of their entries, padding aside. -/
theorem givensLog_slotEntries_map_some (n w : ℕ) (Ls : List (List GivensEntry)) :
    givensLog n (slotEntries w (Ls.map some)) = givensLog n Ls.flatten := by
  induction Ls with
  | nil => rfl
  | cons es Ls ih =>
    rw [List.map_cons, show some es :: Ls.map some = [some es] ++ Ls.map some from rfl,
      slotEntries_append, slotEntries_some, givensLog_append, ih, givensLog_padEntries,
      List.flatten_cons, givensLog_append]

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

/-- The five words of entry `i` of an accepted slot `j` of a stored log. -/
theorem HoldsSlottedLog.readBlock_entry {lg : ℕ × ℕ} {ns w : ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {s : Store ℝ}
    (h : HoldsSlottedLog lg ns w L P s) {j : ℕ} (hj : j < L.length) {es : List GivensEntry}
    (hes : L[j] = some es) {i : ℕ} (hi : i < w) :
    ∃ hi' : i < (padEntries w es).length,
      s.readBlock lg.1 (lg.2 + j * (1 + 5 * w) + 1 + 5 * i) 5 =
        some (entryWords ((padEntries w es)[i]'hi')) := by
  obtain ⟨v, -, hm⟩ := h.2.2.1 j hj
  rw [hes] at hm
  obtain ⟨-, hl, hb⟩ := hm
  have hpl : (padEntries w es).length = w := by simp [padEntries]; omega
  refine ⟨by omega, Store.readBlock_eq_some_iff.mpr ⟨rfl, fun t ht => ?_⟩⟩
  have := Store.get_of_readBlock hb (j := 5 * i + t) (by omega) 0
  rw [show lg.2 + j * (1 + 5 * w) + 1 + (5 * i + t) = lg.2 + j * (1 + 5 * w) + 1 + 5 * i + t by
    ring, getD_flatMap_entryWords _ (by omega) ht] at this
  rw [this, List.getElem?_eq_getElem (by simp [entryWords]; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < (entryWords _).length by
    simp [entryWords]; omega)]

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
    (hL : L.length = ns) :
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

omit [Inhabited ℝ] in
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

omit [Has IndexOp O] [Inhabited ℝ] in
/-- Opening a log stores the empty log. -/
theorem slottedLogOpen_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) {ns w : ℕ} {lg : ℕ × ℕ} {τ : Tape ℝ}
    {μ : Mem ℝ} (hroom : lg.2 + ns * (1 + 5 * w) ≤ μ.store.len lg.1) :
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

omit [Inhabited ℝ] in
/-- Writing an entry appends it to the pending slot. The plane is an exact natural below
`nmax` (`hNat`); this hypothesis belongs to the log, not to the producer. -/
theorem slottedLogWrite_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar Mch I)
    (hL : IsIndexLit Mch I) {nmax : ℕ} (hNat : IsExactNatLit id Mch nmax) {ns w r : ℕ}
    (hr : r ≤ nmax) {lg pw qw : ℕ × ℕ} {L : List (Option (List GivensEntry))}
    {P : List GivensEntry} {p q : ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (h : HoldsSlottedLog lg ns w L P μ.store) (hL : L.length < ns) (hP : P.length < w)
    (hp : μ.store.readBlock pw.1 pw.2 2 = some [p.re, p.im])
    (hq : μ.store.readBlock qw.1 qw.2 2 = some [q.re, q.im])
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

omit [Has ScalarOp O] [Inhabited ℝ] in
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

omit [Has ScalarOp O] [Inhabited ℝ] in
/-- Validating the pending slot closes it as accepted. -/
theorem slottedLogValidate_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hL : IsIndexLit Mch I) (hM : StdModel u id Mch) (hu : u < 1) {ns w : ℕ} {lg : ℕ × ℕ}
    {L : List (Option (List GivensEntry))} {P : List GivensEntry} {τ : Tape ℝ} {μ : Mem ℝ}
    (h : HoldsSlottedLog lg ns w L P μ.store) (hL' : L.length < ns) :
    Writes .total I τ (slottedLogValidate (O := O) (Q := Q)).body
      (Env.frame [w, L.length] [lg]) (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsSlottedLog lg ns w (L ++ [some P]) [] μ'.store) μ := by
  have h1 : 0 < Mch.lit 1 := by
    have := abs_le.mp (hM.lit 1)
    simp only [id, Rat.cast_one, abs_one, mul_one] at this
    linarith [this.1]
  exact slottedLogValidate_writes_of_pos hL h1 h hL'

end Specs

/-- The unitary of a log with one more accepted slot. -/
theorem givensLog_slotEntries_append_some (N w : ℕ) (Ls : List (Option (List GivensEntry)))
    (es : List GivensEntry) :
    givensLog N (slotEntries w (Ls ++ [some es])) =
      givensLog N (slotEntries w Ls) * givensLog N es := by
  rw [show slotEntries w (Ls ++ [some es]) = slotEntries w Ls ++ padEntries w es by
    simp [slotEntries], givensLog_append, givensLog_padEntries]

/-- The planes of a log with one more accepted slot. -/
theorem planes_slotEntries_append_some {N w : ℕ} {Ls : List (Option (List GivensEntry))}
    {es : List GivensEntry} (hN : 1 < N) (hLs : ∀ e ∈ slotEntries w Ls, e.1 + 1 < N)
    (hes : ∀ e ∈ es, e.1 + 1 < N) : ∀ e ∈ slotEntries w (Ls ++ [some es]), e.1 + 1 < N := by
  intro e he
  simp only [slotEntries, List.flatMap_append, List.mem_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, Option.map_some, Option.getD_some, padEntries,
    List.mem_replicate] at he
  rcases he with he | he | ⟨-, rfl⟩
  exacts [hLs e he, hes e he, by change 0 + 1 < N; omega]

/-- Appending an entry to a log multiplies the conjugate transpose of its unitary on the left by
the entry's rotation. -/
theorem conjTranspose_givensLog_concat (n : ℕ) (es : List GivensEntry) (e : GivensEntry) :
    (givensLog n (es ++ [e]))ᴴ = givensAt n e * (givensLog n es)ᴴ := by
  rw [givensLog_append, Matrix.conjTranspose_mul]
  simp [givensLog]

end NLAlib
