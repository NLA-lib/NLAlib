/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.IndexLiteral

/-!
# Stored prefixes of bounded index logs

These storage lemmas concern actual initialized words and their decoded natural indices.
An uncommitted suffix need not be initialized. A one-cell frame updates exactly one finite
log entry, and a completed prefix supplies the ordinary contiguous output block. Pivoted LU
and diagonal-pivoted Cholesky use the same rules.

## Main results

* `NLAlib.Ops.Store.indexPrefix_update`: append one actual recorded index.
* `NLAlib.Ops.Store.indexPrefix_readBlock`: materialize a completely initialized index log.
-/

@[expose] public section

namespace NLAlib.Ops.Store

variable {K : Type} {N : ℕ}

/-- The committed part of an index log depends only on its initialized prefix cells. -/
theorem readsOnly_indexPrefix_committed (dec : K → ℝ) (p : Fin N → Fin N)
    (count : ℕ) (H : ℕ × ℕ) :
    ReadsOnly (inBlock H.1 H.2 (min count N)) (fun s => ∀ j : Fin N, j.val < count →
      ∃ w : K, s.get H.1 (H.2 + j.val) = some w ∧ dec w = (p j).val) := by
  intro s s' he h j hj
  obtain ⟨w, hw, hd⟩ := h j hj
  have hjm : j.val < min count N := lt_min hj j.isLt
  exact ⟨w, (he _ _ ⟨rfl, by omega, by omega⟩).trans hw, hd⟩

/-- A prefix of decoded finite indices depends only on its ordinary declared log block. -/
theorem readsOnly_indexPrefix (dec : K → ℝ) (p : Fin N → Fin N) (count : ℕ) (H : ℕ × ℕ) :
    ReadsOnly (inBlock H.1 H.2 N) (fun s => ∀ j : Fin N, j.val < count →
      ∃ w : K, s.get H.1 (H.2 + j.val) = some w ∧ dec w = (p j).val) :=
  (readsOnly_indexPrefix_committed dec p count H).mono
    (Fp.inBlock_le_inBlock le_rfl (Nat.add_le_add_left (Nat.min_le_right count N) H.2))

/-- Append an actual decoded index when earlier prefix words have already been retained in
the final store. This supports a whole matrix step whose frame also contains the new cell. -/
theorem indexPrefix_succ_of_kept {dec : K → ℝ} {p : Fin N → Fin N} {H : ℕ × ℕ}
    {s : Store K} (k r : Fin N)
    (h : ∀ j : Fin N, j.val < k.val → ∃ w : K,
      s.get H.1 (H.2 + j.val) = some w ∧ dec w = (p j).val) {w : K}
    (hw : s.get H.1 (H.2 + k.val) = some w) (hd : dec w = r.val) :
    ∀ j : Fin N, j.val < k.val + 1 → ∃ v : K,
      s.get H.1 (H.2 + j.val) = some v ∧ dec v = (Function.update p k r j).val := by
  intro j hj
  by_cases he : j = k
  · subst j
    exact ⟨w, hw, by simpa only [Function.update_self] using hd⟩
  · have hjk : j.val < k.val := by have := Fin.ext_iff.not.mp he; omega
    obtain ⟨v, hv, hvd⟩ := h j hjk
    exact ⟨v, hv, by simpa only [Function.update_of_ne he] using hvd⟩

/-- A write confined to the next cell appends that actual decoded index and preserves every
earlier entry. Future entries of the finite index function remain unobserved. -/
theorem indexPrefix_update {dec : K → ℝ} {p : Fin N → Fin N} {H : ℕ × ℕ}
    {s s' : Store K} (k r : Fin N)
    (h : ∀ j : Fin N, j.val < k.val → ∃ w : K,
      s.get H.1 (H.2 + j.val) = some w ∧ dec w = (p j).val)
    (hfr : s.EqOff (inBlock H.1 (H.2 + k.val) 1) s') {w : K}
    (hw : s'.get H.1 (H.2 + k.val) = some w) (hd : dec w = r.val) :
    ∀ j : Fin N, j.val < k.val + 1 → ∃ v : K,
      s'.get H.1 (H.2 + j.val) = some v ∧ dec v = (Function.update p k r j).val := by
  apply indexPrefix_succ_of_kept k r ?_ hw hd
  intro j hj
  obtain ⟨v, hv, hvd⟩ := h j hj
  refine ⟨v, ?_, hvd⟩
  rw [hfr.get_eq (by rintro ⟨_, hlo, hhi⟩; omega)]
  exact hv

/-- Every cell of a complete index prefix is initialized, so its actual contiguous word
block exists and decodes entrywise to the recorded finite indices, including order zero. -/
theorem indexPrefix_readBlock [Inhabited K] {dec : K → ℝ} {p : Fin N → Fin N}
    {H : ℕ × ℕ} {s : Store K}
    (h : ∀ j : Fin N, ∃ w : K, s.get H.1 (H.2 + j.val) = some w ∧ dec w = (p j).val) :
    ∃ hs : List K, s.readBlock H.1 H.2 N = some hs ∧
      ∀ j : Fin N, dec (vec hs j.val) = (p j).val := by
  classical
  let words : Fin N → K := fun j => (h j).choose
  have hw (j : Fin N) : s.get H.1 (H.2 + j.val) = some (words j) ∧
      dec (words j) = (p j).val := (h j).choose_spec
  refine ⟨List.ofFn words, readBlock_eq_some_iff.mpr ⟨by simp, ?_⟩, ?_⟩
  · intro i hi
    simpa only [List.getElem?_ofFn, dif_pos hi] using (hw ⟨i, hi⟩).1
  · intro j
    simpa only [vec, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos j.isLt,
      Fin.eta, Option.getD_some] using (hw j).2

end NLAlib.Ops.Store
