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
* `NLAlib.isRoundedRowRotation_machineRowRotation`,
  `NLAlib.isRoundedColRotation_machineColRotation`: the rotations computed from rounded
  coefficients are rounded Givens rotations.
* `NLAlib.givensReplayColumns_specNorm_sub_le`, `NLAlib.givensReplayRows_specNorm_sub_le`: the
  replay is within $(1 + 24\boldsymbol{u})^{R} - 1$ of the exact product, on every tape.
* `NLAlib.one_add_mul_pow_sub_one_le`: from the identity, within
  $27R\boldsymbol{u}$ when $24R\boldsymbol{u} \le 1/8$.
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
@[simp] theorem slotEntries_append_replicate_none (w k : ℕ)
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
    (hL : L.length = ns) (_hpl : ∀ e ∈ slotEntries w L, (e.1 : ℝ) = e.1) :
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
    {μ : Mem ℝ} (_hl : μ.Live [lg]) (hroom : lg.2 + ns * (1 + 5 * w) ≤ μ.store.len lg.1) :
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
    (hq : μ.store.readBlock qw.1 qw.2 2 = some [q.re, q.im]) (_hl : μ.Live [pw, qw, lg])
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
    (h : HoldsSlottedLog lg ns w L P μ.store) (hL' : L.length < ns) (_hl : μ.Live [lg]) :
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

/-- **Replay a log with a rotation routine** `Rot` of interface `[ld, k, j0, nc] (A, C, S, T) → (A)`
(planes $k, k + 1$, a range $j_0, \dots, j_0 + n_c - 1$): for the valid slots in order (`ns`
slots of `w` entries), recompute each entry's coefficients and call `Rot` at the plane
`lo + r`. The plane is read with the bound `ld`. `[ld, lo, j0, nc, ns, w] (Lg, A) → (A)`. -/
def givensReplayWith (Rot : Impl O Q) : Impl O Q :=
    opsImpl% [ld, lo, j0, nc, ns, w] (Lg, A) → (A) {
  let Cf ← alloc 4;
  let T ← alloc 10;
  for s < ns {
    if (Has.inj CmpTst.isPos) [] (Lg[s * (1 + 5 * w)]) {
      for i < w {
        let r ← index (Has.inj IdxTst.toNat) (Lg[s * (1 + 5 * w) + 1 + 5 * i]) ≤ ld;
        run (coefficients (Op := O) (Tst := Q)).body []
          (Lg[s * (1 + 5 * w) + 2 + 5 * i], Lg[s * (1 + 5 * w) + 4 + 5 * i], Cf, Cf[2]);
        run Rot.body [ld, lo + r, j0, nc] (A, Cf, Cf[2], T, A)
      }
    } else { skip }
  }
}

/-- **Replay a log on rows**: rotate the rows `lo + r, lo + r + 1` of `A` over the columns
`j0, …, j0 + nc - 1` (`NLAlib.rotateRowsOn`). `[ld, lo, j0, nc, ns, w] (Lg, A) → (A)`. -/
def givensReplayRows : Impl O Q := givensReplayWith (rotateRowsOn (Op := O) (Tst := Q))

/-- **Replay a log on columns** (right multiplication by the computed adjoint rotations) over the
rows `i0, …, i0 + nr - 1` (`NLAlib.rotateColumnsOn`). `[ld, lo, i0, nr, ns, w] (Lg, A) → (A)`. -/
def givensReplayColumns : Impl O Q := givensReplayWith (rotateColumnsOn (Op := O) (Tst := Q))

end Replay

/-! ### The replayed words and their error -/

section ReplayWords

/-- A product of square matrices with orthonormal columns has orthonormal columns. -/
theorem hasOrthonormalCols_list_prod {n : ℕ} (l : List (Matrix (Fin n) (Fin n) ℂ))
    (h : ∀ U ∈ l, HasOrthonormalCols U) : HasOrthonormalCols l.prod := by
  induction l with
  | nil => exact hasOrthonormalCols_one
  | cons U l ih =>
    rw [List.prod_cons]
    exact (h U (by simp)).mul (ih fun V hV => h V (by simp [hV]))

/-- Errors along right multiplications by unitaries add up relatively: if each step $f$
moves $\mathbf{Y}$ to within $\eta\|\mathbf{Y}\|_2$ of $\mathbf{Y}\mathbf{U}_a$, $\mathbf{U}_a$
unitary, then $k$ steps from $\mathbf{X}$ end within $((1 + \eta)^k - 1)\|\mathbf{X}\|_2$ of
$\mathbf{X}\mathbf{U}_{a_1}\cdots\mathbf{U}_{a_k}$. -/
theorem specNorm_foldl_sub_mul_prod_le {α : Type*} {n : ℕ}
    (f : Matrix (Fin n) (Fin n) ℂ → α → Matrix (Fin n) (Fin n) ℂ)
    (U : α → Matrix (Fin n) (Fin n) ℂ) {η : ℝ} (hη : 0 ≤ η) (as : List α)
    (hU : ∀ a ∈ as, HasOrthonormalCols (U a))
    (hf : ∀ a ∈ as, ∀ Y, specNorm (f Y a - Y * U a) ≤ η * specNorm Y)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    specNorm (as.foldl f X - X * (as.map U).prod) ≤ ((1 + η) ^ as.length - 1) * specNorm X := by
  induction as using List.reverseRecOn with
  | nil => simp
  | append_singleton as a ih =>
    have ih := ih (fun b hb => hU b (by simp [hb])) (fun b hb => hf b (by simp [hb]))
    set Y := as.foldl f X
    set P := (as.map U).prod
    have ha := hf a (by simp) Y
    have hY : specNorm Y ≤ specNorm X + ((1 + η) ^ as.length - 1) * specNorm X := by
      have e : Y = (Y - X * P) + X * P := by abel
      have := specNorm_add_le (Y - X * P) (X * P)
      rw [← e] at this
      have hP : HasOrthonormalCols P := hasOrthonormalCols_list_prod _ fun V hV => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hV
        exact hU b (by simp [hb])
      rw [hP.specNorm_mul_right] at this
      linarith
    have e : f Y a - X * (P * U a) = (f Y a - Y * U a) + (Y - X * P) * U a := by
      rw [Matrix.sub_mul, Matrix.mul_assoc]; abel
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append, List.map_cons,
      List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, Matrix.mul_one,
      List.length_append, List.length_singleton]
    rw [e]
    refine (specNorm_add_le _ _).trans ?_
    rw [(hU a (by simp)).specNorm_mul_right]
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hY hη, specNorm_nonneg X]

/-- Errors along left multiplications by unitaries add up relatively: the mirror of
`NLAlib.specNorm_foldl_sub_mul_prod_le`, each step within $\eta\|\mathbf{Y}\|_2$ of
$\mathbf{U}_a^{\mathsf H}\mathbf{Y}$. -/
theorem specNorm_foldl_sub_prod_mul_le {α : Type*} {n : ℕ}
    (f : Matrix (Fin n) (Fin n) ℂ → α → Matrix (Fin n) (Fin n) ℂ)
    (U : α → Matrix (Fin n) (Fin n) ℂ) {η : ℝ} (hη : 0 ≤ η) (as : List α)
    (hU : ∀ a ∈ as, HasOrthonormalCols (U a))
    (hf : ∀ a ∈ as, ∀ Y, specNorm (f Y a - (U a)ᴴ * Y) ≤ η * specNorm Y)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    specNorm (as.foldl f X - ((as.map U).prod)ᴴ * X) ≤
      ((1 + η) ^ as.length - 1) * specNorm X := by
  have hg := specNorm_foldl_sub_mul_prod_le (fun Y a => (f Yᴴ a)ᴴ) U hη as hU (fun a ha Y => by
    have e : (f Yᴴ a)ᴴ - Y * U a = (f Yᴴ a - (U a)ᴴ * Yᴴ)ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
    rw [e, specNorm_conjTranspose, ← specNorm_conjTranspose Y]
    exact hf a ha Yᴴ) Xᴴ
  have hfold : ∀ (bs : List α) (Z : Matrix (Fin n) (Fin n) ℂ),
      bs.foldl (fun Y a => (f Yᴴ a)ᴴ) Zᴴ = (bs.foldl f Z)ᴴ := by
    intro bs
    induction bs with
    | nil => intro Z; rfl
    | cons b bs ih => intro Z; simp only [List.foldl_cons, Matrix.conjTranspose_conjTranspose, ih]
  rw [hfold, specNorm_conjTranspose] at hg
  have e : (as.foldl f X)ᴴ - Xᴴ * (as.map U).prod = (as.foldl f X - ((as.map U).prod)ᴴ * X)ᴴ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rwa [e, specNorm_conjTranspose] at hg

/-- One replayed entry on the columns, as the machine computes it: the coefficients rounded from
$(p, q)$, then the machine rotation of the columns $lo + r, lo + r + 1$ over the rows
$i_0, \dots, i_0 + n_r - 1$; nothing out of range. -/
noncomputable def replayColumnStep (M : Machine ℝ) {N : ℕ} (lo i0 nr : ℕ)
    (X : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) : Matrix (Fin N) (Fin N) ℂ :=
  if h : lo + e.1 + 1 < N then
    machineColRotationOn M ⟨lo + e.1, by omega⟩ ⟨lo + e.1 + 1, h⟩
      (roundedGivensCoeffs M e.2.1 e.2.2).1 (roundedGivensCoeffs M e.2.1 e.2.2).2 i0 nr X
  else X

/-- One replayed entry on the rows $lo + r, lo + r + 1$ over the columns
$j_0, \dots, j_0 + n_c - 1$, as the machine computes it; nothing out of range. -/
noncomputable def replayRowStep (M : Machine ℝ) {N : ℕ} (lo j0 nc : ℕ)
    (X : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) : Matrix (Fin N) (Fin N) ℂ :=
  if h : lo + e.1 + 1 < N then
    machineRowRotationOn M ⟨lo + e.1, by omega⟩ ⟨lo + e.1 + 1, h⟩
      (roundedGivensCoeffs M e.2.1 e.2.2).1 (roundedGivensCoeffs M e.2.1 e.2.2).2 j0 nc X
  else X

/-- The embedded rotation of an entry inside the block, or of the zero fill, is the Givens
rotation of the shifted plane. -/
theorem embedBlock_givensAt_eq_givens {N lo d : ℕ} (hN : lo + d ≤ N) {e : GivensEntry}
    (he : lo + e.1 + 1 < N) (he' : e.1 + 1 < d ∨ e = (0, 0, 0)) :
    embedBlock (N := N) lo (givensAt d e) = givens (⟨lo + e.1, by omega⟩ : Fin N)
      ⟨lo + e.1 + 1, he⟩ (givensCoeffs e.2.1 e.2.2).1 (givensCoeffs e.2.1 e.2.2).2 := by
  rcases he' with he' | rfl
  · rw [embedBlock_givensAt hN he']
    simp only [givensAt, dif_pos (show lo + e.1 + 1 < N from he)]
  · rw [givensAt_zero, embedBlock_one]
    simp [givensCoeffs, givens]

/-- The embedded unitary of a log is the product of the embedded adjoint rotations. -/
theorem prod_map_embedBlock_givensAt {N lo d : ℕ} (hN : lo + d ≤ N) (es : List GivensEntry) :
    (es.map fun e => (embedBlock (N := N) lo (givensAt d e))ᴴ).prod =
      embedBlock lo (givensLog d es) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    rw [List.map_cons, List.prod_cons, ih, embedBlock_conjTranspose, ← embedBlock_mul hN]
    rfl

/-- The column replay of one entry is within $24\boldsymbol{u}\|\mathbf{Y}\|_2$ of the product by
the embedded exact adjoint rotation. [Higham2002, Lemma 19.8]. -/
theorem specNorm_replayColumnStep_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) {N lo d : ℕ} (hN : lo + d ≤ N) {e : GivensEntry}
    (he : lo + e.1 + 1 < N) (he' : e.1 + 1 < d ∨ e = (0, 0, 0)) (Y : Matrix (Fin N) (Fin N) ℂ) :
    specNorm (replayColumnStep M lo 0 N Y e - Y * (embedBlock lo (givensAt d e))ᴴ) ≤
      24 * u * specNorm Y := by
  have hij : (⟨lo + e.1, by omega⟩ : Fin N) ≠ ⟨lo + e.1 + 1, he⟩ := Fin.ne_of_val_ne (by simp)
  have hon : replayColumnStep M lo 0 N Y e = machineColRotation M (⟨lo + e.1, by omega⟩ : Fin N)
      ⟨lo + e.1 + 1, he⟩
      (roundedGivensCoeffs M e.2.1 e.2.2).1 (roundedGivensCoeffs M e.2.1 e.2.2).2 Y := by
    ext r t
    simp [replayColumnStep, he, machineColRotationOn]
  rw [hon, embedBlock_givensAt_eq_givens hN he he']
  have h := (isRoundedColRotation_machineColRotation hM hu0 hu hij e.2.1 e.2.2 Y).specNorm_sub_le
    (by positivity)
  linarith

/-- The row replay of one entry over all columns is within $24\boldsymbol{u}\|\mathbf{Y}\|_2$ of
the product by the embedded exact rotation. [Higham2002, Lemma 19.8]. -/
theorem specNorm_replayRowStep_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) {N lo d : ℕ} (hN : lo + d ≤ N) {e : GivensEntry}
    (he : lo + e.1 + 1 < N) (he' : e.1 + 1 < d ∨ e = (0, 0, 0)) (Y : Matrix (Fin N) (Fin N) ℂ) :
    specNorm (replayRowStep M lo 0 N Y e - embedBlock lo (givensAt d e) * Y) ≤
      24 * u * specNorm Y := by
  have hij : (⟨lo + e.1, by omega⟩ : Fin N) ≠ ⟨lo + e.1 + 1, he⟩ := Fin.ne_of_val_ne (by simp)
  have hon : replayRowStep M lo 0 N Y e = machineRowRotation M (⟨lo + e.1, by omega⟩ : Fin N)
      ⟨lo + e.1 + 1, he⟩
      (roundedGivensCoeffs M e.2.1 e.2.2).1 (roundedGivensCoeffs M e.2.1 e.2.2).2 Y := by
    ext r t
    simp [replayRowStep, he, machineRowRotationOn]
  rw [hon, embedBlock_givensAt_eq_givens hN he he']
  have h := (isRoundedRowRotation_machineRowRotation hM hu0 hu hij e.2.1 e.2.2 Y).specNorm_sub_le
    (by positivity)
  linarith

/-- The column replay of a log on the machine is within
$((1 + 24\boldsymbol{u})^{R} - 1)\|\mathbf{X}\|_2$ of $\mathbf{X}\widetilde{\mathbf{V}}$, $R$ the
number of entries and $\widetilde{\mathbf{V}}$ the log's unitary on $[lo, lo + d)$; every entry
is inside the block or the zero fill, with its two columns in range. -/
theorem specNorm_foldl_replayColumnStep_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) {N lo d : ℕ} (hN : lo + d ≤ N) (es : List GivensEntry)
    (hes : ∀ e ∈ es, lo + e.1 + 1 < N ∧ (e.1 + 1 < d ∨ e = (0, 0, 0)))
    (X : Matrix (Fin N) (Fin N) ℂ) :
    specNorm (es.foldl (replayColumnStep M lo 0 N) X - X * embedBlock lo (givensLog d es)) ≤
      ((1 + 24 * u) ^ es.length - 1) * specNorm X := by
  rw [← prod_map_embedBlock_givensAt hN]
  refine specNorm_foldl_sub_mul_prod_le _ _ (by positivity) es (fun e he => ?_)
    (fun e he Y => specNorm_replayColumnStep_sub_le hM hu0 hu hN (hes e he).1 (hes e he).2 Y) X
  rw [embedBlock_givensAt_eq_givens hN (hes e he).1 (hes e he).2]
  exact (hasOrthonormalCols_givens (Fin.ne_of_val_ne (by simp))
    (norm_givensCoeffs_fst_sq_add _ _)).conjTranspose

/-- The row replay of a log over all columns on the machine is within
$((1 + 24\boldsymbol{u})^{R} - 1)\|\mathbf{X}\|_2$ of
$\widetilde{\mathbf{V}}^{\mathsf H}\mathbf{X}$, under the conditions of
`NLAlib.specNorm_foldl_replayColumnStep_sub_le`. -/
theorem specNorm_foldl_replayRowStep_sub_le {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M)
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100) {N lo d : ℕ} (hN : lo + d ≤ N) (es : List GivensEntry)
    (hes : ∀ e ∈ es, lo + e.1 + 1 < N ∧ (e.1 + 1 < d ∨ e = (0, 0, 0)))
    (X : Matrix (Fin N) (Fin N) ℂ) :
    specNorm (es.foldl (replayRowStep M lo 0 N) X - (embedBlock lo (givensLog d es))ᴴ * X) ≤
      ((1 + 24 * u) ^ es.length - 1) * specNorm X := by
  rw [← prod_map_embedBlock_givensAt hN]
  refine specNorm_foldl_sub_prod_mul_le _ _ (by positivity) es (fun e he => ?_)
    (fun e he Y => by
      rw [Matrix.conjTranspose_conjTranspose]
      exact specNorm_replayRowStep_sub_le hM hu0 hu hN (hes e he).1 (hes e he).2 Y) X
  rw [embedBlock_givensAt_eq_givens hN (hes e he).1 (hes e he).2]
  exact (hasOrthonormalCols_givens (Fin.ne_of_val_ne (by simp))
    (norm_givensCoeffs_fst_sq_add _ _)).conjTranspose

/-- The diagonal projection on the columns $j_0, \dots, j_0 + n_c - 1$. -/
noncomputable def colMask (N j0 nc : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun t => if j0 ≤ (t : ℕ) ∧ (t : ℕ) < j0 + nc then 1 else 0

/-- The column mask is an orthogonal projection. -/
theorem isStarProjection_colMask (N j0 nc : ℕ) : IsStarProjection (colMask N j0 nc) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, colMask, Matrix.diagonal_mul_diagonal]
    congr 1; funext t
    by_cases h : j0 ≤ (t : ℕ) ∧ (t : ℕ) < j0 + nc
    · rw [if_pos h, mul_one]
    · rw [if_neg h, mul_zero]
  · rw [IsSelfAdjoint, colMask, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext t
    by_cases h : j0 ≤ (t : ℕ) ∧ (t : ℕ) < j0 + nc
    · simp only [Pi.star_apply, if_pos h, star_one]
    · simp only [Pi.star_apply, if_neg h, star_zero]

/-- A row replay on a column range, masked to the range, is the replay over all columns of the
masked matrix: the machine rotation acts column by column and keeps zero columns. -/
theorem replayRowStep_mul_colMask {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) {N : ℕ}
    (lo j0 nc : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) :
    replayRowStep M lo j0 nc X e * colMask N j0 nc =
      replayRowStep M lo 0 N (X * colMask N j0 nc) e := by
  ext a t
  by_cases h : lo + e.1 + 1 < N
  · simp only [replayRowStep, dif_pos h, colMask, Matrix.mul_diagonal, machineRowRotationOn,
      Matrix.of_apply, machineRowRotation]
    by_cases ht : j0 ≤ (t : ℕ) ∧ (t : ℕ) < j0 + nc
    · simp [ht]
    · simp only [ht, if_false, mul_zero, Nat.zero_le, zero_add, t.isLt, and_self, if_true]
      split_ifs <;> simp [linearComplex_zero_zero hM]
  · simp [replayRowStep, h]

/-- A row replay on a column range keeps the other columns. -/
theorem replayRowStep_apply_of_not_mem {M : Machine ℝ} {N : ℕ} {lo j0 nc : ℕ}
    (X : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) (i t : Fin N)
    (ht : ¬(j0 ≤ (t : ℕ) ∧ (t : ℕ) < j0 + nc)) : replayRowStep M lo j0 nc X e i t = X i t := by
  unfold replayRowStep
  split_ifs
  · simp [machineRowRotationOn, ht]
  · rfl

/-- The masked row replay of a log is the full row replay of the masked matrix. -/
theorem foldl_replayRowStep_mul_colMask {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) {N : ℕ}
    (lo j0 nc : ℕ) (es : List GivensEntry) (X : Matrix (Fin N) (Fin N) ℂ) :
    es.foldl (replayRowStep M lo j0 nc) X * colMask N j0 nc =
      es.foldl (replayRowStep M lo 0 N) (X * colMask N j0 nc) := by
  induction es generalizing X with
  | nil => rfl
  | cons e es ih => simp only [List.foldl_cons, ih, replayRowStep_mul_colMask hM]

/-- The row replay of a log on a column range keeps the other columns. -/
theorem foldl_replayRowStep_apply_of_not_mem {M : Machine ℝ} {N : ℕ} {lo j0 nc : ℕ}
    (es : List GivensEntry) (X : Matrix (Fin N) (Fin N) ℂ) (i t : Fin N)
    (ht : ¬(j0 ≤ (t : ℕ) ∧ (t : ℕ) < j0 + nc)) :
    es.foldl (replayRowStep M lo j0 nc) X i t = X i t := by
  induction es generalizing X with
  | nil => rfl
  | cons e es ih => rw [List.foldl_cons, ih, replayRowStep_apply_of_not_mem _ _ _ _ ht]

end ReplayWords

section ReplaySpecs

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]
  [Inhabited ℝ]

/-- The replay of one entry, as it appears in `NLAlib.givensReplayWith`: the plane read with the
bound `ld`, the coefficients, the rotation. -/
private def replayEntryStmt (Rot : Impl O Q) : Stmt O Q :=
  Stmt.bindIdx (Has.inj IdxTst.toNat)
    [{ buf := 0, off := IExp.var 6 + IExp.var 9 * (IExp.const 1 + IExp.const 5 * IExp.var 5) +
      IExp.const 1 + IExp.const 5 * IExp.var 10 }]
    (IExp.var 0)
    ((Stmt.frame []
        [{ buf := 0, off := IExp.var 6 + IExp.var 9 * (IExp.const 1 + IExp.const 5 * IExp.var 5) +
            IExp.const 2 + IExp.const 5 * IExp.var 10 },
          { buf := 0, off := IExp.var 6 + IExp.var 9 * (IExp.const 1 + IExp.const 5 * IExp.var 5) +
            IExp.const 4 + IExp.const 5 * IExp.var 10 },
          { buf := 3, off := IExp.const 0 }, { buf := 3, off := IExp.const 2 }]
        (coefficients (Op := O) (Tst := Q)).body).seq
      (Stmt.frame [IExp.var 0, IExp.var 1 + IExp.var 11, IExp.var 2, IExp.var 3]
        [{ buf := 1, off := IExp.var 7 }, { buf := 3, off := IExp.const 0 },
          { buf := 3, off := IExp.const 2 }, { buf := 4, off := IExp.const 0 },
          { buf := 1, off := IExp.var 7 }]
        Rot.body))

omit [Has IndexOp O] [Inhabited ℝ] in
/-- The replay of one entry whose two planes are in range stores the rotation word of the
coefficients rounded from the entry. -/
private theorem replayEntryStmt_writes {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hQ : IsToNat id I) (hC : IsCmp id I) {Rot : Impl O Q}
    {N lo j0 nc ns w : ℕ} {lg x : ℕ × ℕ}
    {rotWord : ℕ → ℂ → ℂ → Matrix (Fin N) (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ}
    (hRot : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {k : ℕ} {c s t : ℕ × ℕ} {Y : Matrix (Fin N) (Fin N) ℂ}
      {cv sv : ℂ}, k + 1 < N → HoldsMatrix x Y μ.store →
      μ.store.readBlock c.1 c.2 2 = some [cv.re, cv.im] →
      μ.store.readBlock s.1 s.2 2 = some [sv.re, sv.im] →
      Fp.Disj (Store.inBlock x.1 x.2 (2 * (N * N))) (Store.inBlock c.1 c.2 2) →
      Fp.Disj (Store.inBlock x.1 x.2 (2 * (N * N))) (Store.inBlock s.1 s.2 2) →
      t.1 ≠ x.1 → t.1 ≠ c.1 → t.1 ≠ s.1 → t.2 + 10 ≤ μ.store.len t.1 →
      Writes .total I τ Rot.body (Env.frame [N, k, j0, nc] [x, c, s, t, x])
        (Store.inBlock x.1 x.2 (2 * (N * N)) ⊔ Store.inBlock t.1 t.2 10)
        (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix x (rotWord k cv sv Y) μ'.store) μ)
    {ρ : Env} {sl i Lc : ℕ} (hidx : ρ.idx = [N, lo, j0, nc, ns, w, lg.2, x.2, x.2, sl, i])
    (hbuf : ρ.buf = [lg.1, x.1, x.1, Lc, Lc + 1]) {e : GivensEntry} (he : lo + e.1 + 1 < N)
    {τ : Tape ℝ} {μ : Mem ℝ}
    (hw : μ.store.readBlock lg.1 (lg.2 + sl * (1 + 5 * w) + 1 + 5 * i) 5 = some (entryWords e))
    {Y : Matrix (Fin N) (Fin N) ℂ} (hY : HoldsMatrix x Y μ.store) (hlen : μ.store.length = Lc + 2)
    (hL0 : μ.store.len Lc = 4) (hL1 : μ.store.len (Lc + 1) = 10) (hxL : x.1 < Lc) :
    Writes .total I τ (replayEntryStmt Rot) ρ
      (Store.inBlock x.1 x.2 (2 * (N * N)) ⊔ Store.inBlock Lc 0 4 ⊔ Store.inBlock (Lc + 1) 0 10)
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix x (rotWord (lo + e.1)
        (roundedGivensCoeffs Mch e.2.1 e.2.2).1 (roundedGivensCoeffs Mch e.2.1 e.2.2).2 Y)
          μ'.store) μ := by
  set o := lg.2 + sl * (1 + 5 * w) + 1 + 5 * i with ho
  have hg (k : ℕ) (hk : k < 5) : μ.store.get lg.1 (o + k) = some ((entryWords e).getD k 0) :=
    Store.get_of_readBlock hw hk 0
  have hXC : Fp.Disj (Store.inBlock x.1 x.2 (2 * (N * N))) (Store.inBlock Lc 0 4) :=
    Fp.disj_inBlock_of_ne (by omega)
  have hcs : Fp.Disj (Store.inBlock Lc 0 2) (Store.inBlock Lc 2 2) := Fp.disj_inBlock_of_le le_rfl
  have h1 : Store.inBlock Lc 0 2 ≤ Store.inBlock Lc 0 4 := Fp.inBlock_le_inBlock le_rfl (by omega)
  have h2 : Store.inBlock Lc 2 2 ≤ Store.inBlock Lc 0 4 :=
    Fp.inBlock_le_inBlock (by omega) (by omega)
  have hc4 : Fp.blocks [(Lc, 0), (Lc, 2)] [2, 2] ≤ Store.inBlock Lc 0 4 := by
    simpa only [Fp.blocks, sup_bot_eq] using sup_le h1 h2
  have hgl : lg.1 < Lc + 2 := hlen ▸ Store.lt_length_of_get (hg 0 (by omega))
  unfold replayEntryStmt
  refine writes_bindIdx_of_decode_nat hQ (x := (lg.1, o + 0)) (w := (e.1 : ℝ)) (B := N)
    (by simp [Operand.eval, hidx, hbuf, IExp.eval, ho]) (by simp [IExp.eval, hidx])
    (by simpa [entryWords] using hg 0 (by omega)) rfl (by omega) ?_
  refine (coefficients_writes_word (τ := τ) (a := (lg.1, o + 1)) (b := (lg.1, o + 3))
    (c := (Lc, 0)) (s := (Lc, 2)) (u := e.2.1) (v := e.2.2) hS hC hcs
    (by simpa [entryWords] using hg 1 (by omega)) (by simpa [entryWords] using hg 2 (by omega))
    (by simpa [entryWords] using hg 3 (by omega)) (by simpa [entryWords] using hg 4 (by omega))
    (by simp [hL0]) (by simp [hL0])).frame_seq_le rfl
    (by simp [Operand.evalList, Operand.eval, Env.pushIdx, hidx, hbuf, IExp.eval, ho]; omega)
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> simp only [hlen] <;> omega)
    (hc4.trans (le_sup_right.trans le_sup_left)) ?_
  rintro μ₁ hfr₁ ⟨hp₁, hcs₁⟩
  have hc₁ := (Mem.readBlocks_cons_iff.mp hcs₁).1
  have hs₁ := (Mem.readBlocks_cons_iff.mp (Mem.readBlocks_cons_iff.mp hcs₁).2).1
  refine ((hRot (τ := τ) (k := lo + e.1) (t := (Lc + 1, 0)) he
    (hY.of_eqOff hfr₁ (hXC.symm.mono hc4 le_rfl)) hc₁ hs₁
    (hXC.mono le_rfl (Fp.inBlock_le_inBlock le_rfl (by omega)))
    (hXC.mono le_rfl (Fp.inBlock_le_inBlock (by omega) (by omega))) (by simp; omega)
    (by simp) (by simp) (by simp [hfr₁.len_eq, hL1])).in_frame
    (by simp [IExp.evalList, IExp.eval, Env.pushIdx, hidx])
    (by simp [Operand.evalList, Operand.eval, Env.pushIdx, hidx, hbuf, IExp.eval])
    (by intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp only [hfr₁.length_eq, hlen] <;>
          omega)).mono
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right) ?_
  rintro μ₂ - ⟨hp₂, hY₂⟩
  exact ⟨hp₂.trans hp₁, hY₂⟩

omit [Has IndexOp O] [Inhabited ℝ] in
/-- A replay with any rotation routine stores the replayed word: if `Rot` at the plane $k$
stores `rotWord k c s` of the matrix for the coefficients $(c, s)$, the replay of a closed log
whose entries have their two planes in range stores the left fold of `rotWord` over the valid
entries, with the coefficients rounded from each entry. -/
theorem givensReplayWith_writes_word {Mch : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar Mch I) (hQ : IsToNat id I) (hC : IsCmp id I) {Rot : Impl O Q}
    {N lo j0 nc ns w : ℕ} {lg x : ℕ × ℕ}
    (rotWord : ℕ → ℂ → ℂ → Matrix (Fin N) (Fin N) ℂ → Matrix (Fin N) (Fin N) ℂ)
    (hRot : ∀ {τ : Tape ℝ} {μ : Mem ℝ} {k : ℕ} {c s t : ℕ × ℕ} {Y : Matrix (Fin N) (Fin N) ℂ}
      {cv sv : ℂ}, k + 1 < N → HoldsMatrix x Y μ.store →
      μ.store.readBlock c.1 c.2 2 = some [cv.re, cv.im] →
      μ.store.readBlock s.1 s.2 2 = some [sv.re, sv.im] →
      Fp.Disj (Store.inBlock x.1 x.2 (2 * (N * N))) (Store.inBlock c.1 c.2 2) →
      Fp.Disj (Store.inBlock x.1 x.2 (2 * (N * N))) (Store.inBlock s.1 s.2 2) →
      t.1 ≠ x.1 → t.1 ≠ c.1 → t.1 ≠ s.1 → t.2 + 10 ≤ μ.store.len t.1 →
      Writes .total I τ Rot.body (Env.frame [N, k, j0, nc] [x, c, s, t, x])
        (Store.inBlock x.1 x.2 (2 * (N * N)) ⊔ Store.inBlock t.1 t.2 10)
        (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix x (rotWord k cv sv Y) μ'.store) μ)
    {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hrow : ∀ e ∈ slotEntries w L, lo + e.1 + 1 < N) {X : Matrix (Fin N) (Fin N) ℂ}
    {τ : Tape ℝ} {μ : Mem ℝ}
    (hlog : HoldsSlottedLog lg ns w L P μ.store) (hlen : L.length = ns)
    (hX : HoldsMatrix x X μ.store) (hl : μ.Live [lg, x])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock x.1 x.2 (2 * (N * N)))) :
    Writes .total I τ (givensReplayWith Rot).body
      (Env.frame [N, lo, j0, nc, ns, w] [lg, x, x]) (Store.inBlock x.1 x.2 (2 * (N * N)))
      (fun μ' => μ'.pos = μ.pos ∧ HoldsMatrix x ((slotEntries w L).foldl (fun Y e =>
        rotWord (lo + e.1) (roundedGivensCoeffs Mch e.2.1 e.2.2).1
          (roundedGivensCoeffs Mch e.2.1 e.2.2).2 Y) X) μ'.store) μ := by
  set F := fun (Y : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) => rotWord (lo + e.1)
    (roundedGivensCoeffs Mch e.2.1 e.2.2).1 (roundedGivensCoeffs Mch e.2.1 e.2.2).2 Y with hF
  have hxl : x.1 < μ.store.length := hl x (by simp)
  have hgl : lg.1 < μ.store.length := hl lg (by simp)
  unfold givensReplayWith
  change Writes .total I τ (Stmt.allocs [.const 4, .const 10] _) _ _ _ μ
  refine writes_allocs_preserving_post (ns := [4, 10]) rfl
    (fun hBelow ⟨hp, hW⟩ => ⟨hp, hW.of_below hBelow hxl⟩) ?_
  intro s₁ hlen₁ hlens hBelow
  set Lc := μ.store.length with hLc
  simp only [List.length_cons, List.length_nil] at hlen₁
  set G := Store.inBlock x.1 x.2 (2 * (N * N)) ⊔ Store.inBlock Lc 0 4 ⊔
    Store.inBlock (Lc + 1) 0 10 with hG
  set St : List GivensEntry → Mem ℝ → Prop := fun es μ' => μ'.pos = μ.pos ∧
    μ'.store.length = Lc + 2 ∧ μ'.store.len Lc = 4 ∧ μ'.store.len (Lc + 1) = 10 ∧
    HoldsMatrix x (es.foldl F X) μ'.store ∧ HoldsSlottedLog lg ns w L P μ'.store with hSt
  have hGL : Fp.Disj G (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w))) :=
    Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨hd.symm, Fp.disj_inBlock_of_ne (by omega)⟩,
      Fp.disj_inBlock_of_ne (by omega)⟩
  have hstart : St [] ⟨s₁, μ.pos⟩ :=
    ⟨rfl, by omega, by simpa using hlens 0 (by simp), by simpa using hlens 1 (by simp),
      hX.of_below hBelow hxl, hlog.of_below hBelow hgl⟩
  have hGle : G ≤ Store.inBlock x.1 x.2 (2 * (N * N)) ⊔ Fp.above Lc := by
    rintro b z ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (h.1 ▸ le_rfl)
    · exact Or.inr (h.1 ▸ Nat.le_succ Lc)
  refine (writes_loop (N := ns) rfl (fun _ => G) (fun _ _ => le_rfl)
    (fun k μ' => St (slotEntries w (L.take k)) μ') (by simpa [slotEntries] using hstart)
    ?_).mono hGle ?_
  · intro k hk μ' _ ⟨hp, hlen', hL0, hL1, hW, hlog'⟩
    obtain ⟨v, hv, hm⟩ := hlog'.2.2.1 k (by omega)
    have htake : L.take (k + 1) = L.take k ++ [L[k]'(by omega)] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
    refine writes_ite (a := [(lg.1, lg.2 + k * (1 + 5 * w))]) rfl
      (by simp [Operand.evalList, Operand.eval, Env.pushIdx, Env.frame, IExp.eval])
      (hC.test_isPos (x := (lg.1, lg.2 + k * (1 + 5 * w))) hv) ?_
    split at hm
    · next hn =>
      rw [if_neg (by simpa using hm)]
      have hW' : HoldsMatrix x ((slotEntries w (L.take (k + 1))).foldl F X) μ'.store := by
        rwa [htake, slotEntries_append, hn, slotEntries_none, List.append_nil]
      exact (Writes.skip (P := fun μ'' => St (slotEntries w (L.take (k + 1))) μ'')
        ⟨hp, hlen', hL0, hL1, hW', hlog'⟩).mono bot_le fun _ _ h => h
    · next es hn =>
      rw [if_pos (by simpa using hm.1)]
      refine (writes_loop (N := w) rfl (fun _ => G) (fun _ _ => le_rfl)
        (fun i μ'' => St (slotEntries w (L.take k) ++ (padEntries w es).take i) μ'')
        (by simpa using (⟨hp, hlen', hL0, hL1, hW, hlog'⟩ : St _ μ')) ?_).mono le_rfl ?_
      · intro i hi μ'' _ ⟨hp'', hlen'', hL0'', hL1'', hW'', hlog''⟩
        obtain ⟨hi', hwd⟩ := hlog''.readBlock_entry (j := k) (by omega) hn hi
        have he : lo + ((padEntries w es)[i]'hi').1 + 1 < N := hrow _ (by
          rw [slotEntries, List.mem_flatMap]
          exact ⟨some es, hn ▸ List.getElem_mem (by omega), by simp [List.getElem_mem]⟩)
        refine (replayEntryStmt_writes hS hQ hC hRot (N := N) (lo := lo) (j0 := j0) (nc := nc)
          (ns := ns) (w := w) (lg := lg) (x := x) (sl := k) (i := i) (Lc := Lc)
          (by simp [Env.pushIdx, Env.frame]) (by simp [Env.pushIdx, Env.frame, List.range_succ])
          he hwd hW''
          hlen'' hL0'' hL1'' hxl).mono le_rfl ?_
        rintro μ₃ hfr₃ ⟨hp₃, hW₃⟩
        refine ⟨hp₃.trans hp'', by rw [hfr₃.length_eq, hlen''], by rw [hfr₃.len_eq, hL0''],
          by rw [hfr₃.len_eq, hL1''], ?_, hfr₃.keep (readsOnly_holdsSlottedLog _ _ _ _ _) hGL
          hlog''⟩
        rw [List.take_add_one, List.getElem?_eq_getElem hi', ← List.append_assoc,
          List.foldl_append]
        exact hW₃
      · rintro μ₃ - ⟨hp₃, hlen₃, hL0₃, hL1₃, hW₃, hlog₃⟩
        refine ⟨hp₃, hlen₃, hL0₃, hL1₃, ?_, hlog₃⟩
        have hpl : (padEntries w es).length = w := by
          have := hm.2.1; simp [padEntries]; omega
        rw [htake, slotEntries_append, hn, slotEntries_some, List.foldl_append]
        simpa [List.take_of_length_le (le_of_eq hpl)] using hW₃
  · rintro μ' - ⟨hp, -, -, -, hW, -⟩
    exact ⟨hp, by simpa [List.take_of_length_le (le_of_eq hlen)] using hW⟩

omit [Inhabited ℝ] in
/-- The entries of a log inside a block, or the zero fill when the rows `lo, lo + 1` exist, have
their two planes in range. -/
theorem slotEntries_planes {N lo d w : ℕ} {L : List (Option (List GivensEntry))}
    (hN : lo + d ≤ N) (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < d ∨ e = (0, 0, 0))
    (hlo : slotEntries w L = [] ∨ lo + 1 < N) :
    ∀ e ∈ slotEntries w L, lo + e.1 + 1 < N ∧ (e.1 + 1 < d ∨ e = (0, 0, 0)) := by
  intro e he
  refine ⟨?_, hpl e he⟩
  rcases hpl e he with h | rfl
  · omega
  · rcases hlo with h | h
    · rw [h] at he; simp at he
    · simpa using h

omit [Has IndexOp O] [Inhabited ℝ] in
/-- **The column replay on every tape**: the stored matrix moves from $\mathbf{X}$ to within
$((1 + 24\boldsymbol{u})^{m} - 1)\|\mathbf{X}\|_2$ of $\mathbf{X}\widetilde{\mathbf{V}}$, where
$\widetilde{\mathbf{V}}$ acts by the log's unitary on the range $[lo, lo + d)$ and $m$ is the
capacity $ns \cdot w$ (each replayed rotation, padding included, costs at most
$24\boldsymbol{u}$; [Higham2002, Lemma 19.8]). Needs only exact naturals up to the order. -/
theorem givensReplayColumns_specNorm_sub_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hQ : IsToNat id I) (hC : IsCmp id I) {N lo d ns w : ℕ} (hN : lo + d ≤ N)
    {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < d ∨ e = (0, 0, 0))
    (hlo : slotEntries w L = [] ∨ lo + 1 < N) {lg x : ℕ × ℕ}
    {X : Matrix (Fin N) (Fin N) ℂ} {τ : Tape ℝ} {μ : Mem ℝ}
    (hlog : HoldsSlottedLog lg ns w L P μ.store) (hlen : L.length = ns)
    (hX : HoldsMatrix x X μ.store) (hl : μ.Live [lg, x])
    (hd : Fp.Disj (Store.inBlock lg.1 lg.2 (ns * (1 + 5 * w)))
      (Store.inBlock x.1 x.2 (2 * (N * N)))) :
    Writes .total I τ (givensReplayColumns (O := O) (Q := Q)).body
      (Env.frame [N, lo, 0, N, ns, w] [lg, x, x]) (Store.inBlock x.1 x.2 (2 * (N * N)))
      (fun μ' => ∃ X' : Matrix (Fin N) (Fin N) ℂ, HoldsMatrix x X' μ'.store ∧
        specNorm (X' - X * embedBlock lo (givensLog d (slotEntries w L))) ≤
          ((1 + 24 * u) ^ (ns * w) - 1) * specNorm X) μ := by
  have hes := slotEntries_planes hN hpl hlo
  refine (givensReplayWith_writes_word hS hQ hC (fun k cv sv Y => if h : k + 1 < N then
      machineColRotationOn Mch ⟨k, by omega⟩ ⟨k + 1, h⟩ cv sv 0 N Y else Y)
    (fun hk hY hc hs hca hsa hta htc hts ht => by
      simpa only [dif_pos hk] using rotateColumnsOn_writes_word hS hk (by omega) hY hc hs hca
        hsa hta htc hts ht) (fun e he => (hes e he).1) hlog hlen hX hl hd).mono le_rfl ?_
  rintro μ' - ⟨-, hW⟩
  refine ⟨_, hW, ?_⟩
  have e : (fun (Y : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) =>
      (fun k cv sv Y => if h : k + 1 < N then
        machineColRotationOn Mch ⟨k, by omega⟩ ⟨k + 1, h⟩ cv sv 0 N Y else Y)
        (lo + e.1) (roundedGivensCoeffs Mch e.2.1 e.2.2).1 (roundedGivensCoeffs Mch e.2.1 e.2.2).2
        Y) = replayColumnStep Mch lo 0 N := rfl
  rw [e]
  refine (specNorm_foldl_replayColumnStep_sub_le hM hu0 hu hN _ hes X).trans
    (mul_le_mul_of_nonneg_right ?_ (specNorm_nonneg X))
  gcongr
  · linarith
  · exact hlen ▸ hlog.length_slotEntries_le

omit [Has IndexOp O] [Inhabited ℝ] in
/-- **The row replay on a column range on every tape**: the columns outside
$[j_0, j_0 + n_c)$ are kept and, on the range, the stored matrix is within
$((1 + 24\boldsymbol{u})^{ns\,w} - 1)\|\mathbf{X}\|_2$ of $\widetilde{\mathbf{V}}^{\mathsf H}
\mathbf{X}$. -/
theorem givensReplayRows_specNorm_sub_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hQ : IsToNat id I) (hC : IsCmp id I) {N lo d j0 nc ns w : ℕ} (hN : lo + d ≤ N)
    (hj : j0 + nc ≤ N) {L : List (Option (List GivensEntry))} {P : List GivensEntry}
    (hpl : ∀ e ∈ slotEntries w L, e.1 + 1 < d ∨ e = (0, 0, 0))
    (hlo : slotEntries w L = [] ∨ lo + 1 < N) {lg x : ℕ × ℕ}
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
          ((1 + 24 * u) ^ (ns * w) - 1) * specNorm X) μ := by
  have hes := slotEntries_planes hN hpl hlo
  refine (givensReplayWith_writes_word hS hQ hC (fun k cv sv Y => if h : k + 1 < N then
      machineRowRotationOn Mch ⟨k, by omega⟩ ⟨k + 1, h⟩ cv sv j0 nc Y else Y)
    (fun hk hY hc hs hca hsa hta htc hts ht => by
      simpa only [dif_pos hk] using rotateRowsOn_writes_word hS hk hj hY hc hs hca
        hsa hta htc hts ht) (fun e he => (hes e he).1) hlog hlen hX hl hd).mono le_rfl ?_
  rintro μ' - ⟨-, hW⟩
  have e : (fun (Y : Matrix (Fin N) (Fin N) ℂ) (e : GivensEntry) =>
      (fun k cv sv Y => if h : k + 1 < N then
        machineRowRotationOn Mch ⟨k, by omega⟩ ⟨k + 1, h⟩ cv sv j0 nc Y else Y)
        (lo + e.1) (roundedGivensCoeffs Mch e.2.1 e.2.2).1 (roundedGivensCoeffs Mch e.2.1 e.2.2).2
        Y) = replayRowStep Mch lo j0 nc := rfl
  rw [e] at hW
  refine ⟨_, hW, fun i t ht => foldl_replayRowStep_apply_of_not_mem _ _ _ _ ht, ?_⟩
  set V := embedBlock (N := N) lo (givensLog d (slotEntries w L))
  have hD := isStarProjection_colMask N j0 nc
  have hm : (Matrix.of fun i j : Fin N => if j0 ≤ (j : ℕ) ∧ (j : ℕ) < j0 + nc then
      ((slotEntries w L).foldl (replayRowStep Mch lo j0 nc) X - Vᴴ * X) i j else 0) =
      (slotEntries w L).foldl (replayRowStep Mch lo 0 N) (X * colMask N j0 nc) -
        Vᴴ * (X * colMask N j0 nc) := by
    rw [← foldl_replayRowStep_mul_colMask hM, ← Matrix.mul_assoc, ← Matrix.sub_mul]
    ext i j
    simp [colMask, Matrix.mul_diagonal]
  rw [hm]
  refine (specNorm_foldl_replayRowStep_sub_le hM hu0 hu hN _ hes _).trans ?_
  have hpow : (1 + 24 * u) ^ (slotEntries w L).length ≤ (1 + 24 * u) ^ (ns * w) :=
    pow_le_pow_right₀ (by linarith) (hlen ▸ hlog.length_slotEntries_le)
  have h1 : (1 : ℝ) ≤ (1 + 24 * u) ^ (slotEntries w L).length := one_le_pow₀ (by linarith)
  have hXD := hD.specNorm_mul_right_le X
  nlinarith [specNorm_nonneg (X * colMask N j0 nc)]

omit [Inhabited ℝ] in
/-- **The accumulated product from the identity**: with $24R\boldsymbol{u} \le 1/8$,
$(1 + 24\boldsymbol{u})^R - 1 \le 27R\boldsymbol{u}$. -/
theorem one_add_mul_pow_sub_one_le {u : ℝ} {R : ℕ} (hu : 0 ≤ u) (hR : 24 * R * u ≤ 1 / 8) :
    (1 + 24 * u) ^ R - 1 ≤ 27 * R * u := by
  have h := one_add_pow_sub_one_le (x := 24 * u) (n := R) (by positivity) (by nlinarith)
  have hR : 0 ≤ (R : ℝ) * (24 * u) := by positivity
  nlinarith

end ReplaySpecs

end NLAlib
