/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Hermitian
public import NLAlib.Ops.Logic.EntryRows

/-!
# Completing a Hermitian matrix from stored upper entries

Mirroring reads the upper triangle and writes the lower triangle of the same matrix buffer.
The variable-row fill rule handles the loops, and ordinary disjoint-region framing preserves
the upper entries. No initialization of the unused lower triangle is assumed.

## Main results

* `NLAlib.Ops.Hermitian.writes_mirror_lower`: actual lower-triangle words after execution.
* `NLAlib.Ops.Hermitian.writes_mirror`: the complete stored matrix, including preserved diagonal.
-/

@[expose] public section

namespace NLAlib.Ops.Hermitian

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Complete a word matrix by preserving its upper triangle and copying/negating transposed
lower entries. Its diagonal is preserved exactly, including its stored imaginary words. -/
def completeUpper (M : Machine K) (A : ℕ → ℕ → K × K) : ℕ → ℕ → K × K :=
  fun i j => if i ≤ j then A i j else ((A j i).1, M.neg (A j i).2)

/-- Mirroring fills precisely the strict lower triangle with the machine conjugates of the
stored upper entries, preserves all other cells, and consumes no random words. Output capacity
covers the square matrix; the input handle is live even when its dimension is zero. -/
theorem writes_mirror_lower {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {n : ℕ} {y : ℕ × ℕ}
    (A : ℕ → ℕ → K × K) (hl : y.1 < m.store.length)
    (hz : y.2 + 2 * (n * n) ≤ m.store.len y.1)
    (hu : m.store.HoldsRowEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
      (fun j => j + 1) A) :
    Writes md I τ (mirror (Op := Op) (Tst := Tst)).body (Env.frame [n] [y, y])
      ((EntryCodec.pair K).regionFp y.1 y.2 n (fun i j => i * n + j) (fun j => j))
      (fun m' => m'.store.HoldsEntryRegion (EntryCodec.pair K) y.1 y.2 n
        (fun i j => i * n + j) (fun j => j) (fun i j => ((A i j).1, M.neg (A i j).2)) ∧
        m'.pos = m.pos) m := by
  let C := EntryCodec.pair K
  have hdis := C.disj_regionFp_triangles n y.1 y.2
  refine writes_fillEntryRegion C y.1 y.2 n (fun i j => i * n + j) (fun j => j)
    ?_ rfl (fun _ => rfl) (fun i j => ((A i j).1, M.neg (A i j).2))
    (fun _ _ => m.pos) rfl (fun _ _ => rfl) ?_
  · intro p hp q hq he
    have hd := congrArg (· / n) he
    have hm := congrArg (· % n) he
    simp only [Idx.div_add hp.1, Idx.div_add hq.1] at hd
    simp only [Idx.mod_add hp.1, Idx.mod_add hq.1] at hm
    exact Prod.ext hd hm
  · intro j hj i hi m' hfr hp
    have hupper := (hfr.mono (C.regionUpto_le_regionFp y.1 y.2 n
      (fun i j => i * n + j) (fun j => j) hj hi.le)).keep
      (Store.readsOnly_holdsRowEntries C ⟨y.1, y.2, n, n, n⟩ (fun j => j + 1) A) hdis hu
    have hxr := hupper j hj i (Nat.lt_succ_of_lt hi) 0
    have hxi := hupper j hj i (Nat.lt_succ_of_lt hi) 1
    have hspace : y.2 + 2 * (i * n + j) + 2 ≤ m'.store.len y.1 := by
      have hz' : y.2 + 2 * (n * n) ≤ m'.store.len y.1 := by
        rw [hfr.len_eq]
        exact hz
      exact C.room_entry (L := ⟨y.1, y.2, n, n, n⟩) le_rfl hj (hi.trans hj) hz'
    have hl' : y.1 < m'.store.length := by rw [hfr.length_eq]; exact hl
    refine writes_frame rfl rfl (by simp [Mem.Live, hl']) ?_
    have hw := writes_pair_of_wp (md := md) (I := I) (τ := τ) (m := m')
      (z := (y.1, y.2 + 2 * (i * n + j))) (v := ((A i j).1, M.neg (A i j).2))
      (wp_conjugatePair hI (m := m') (x := (y.1, y.2 + 2 * (j * n + i)))
        (z := (y.1, y.2 + 2 * (i * n + j))) hxr hxi hspace
      (Or.inr (by omega)) (Q := fun m'' => m'' = m'.updBlock
        (y.1, y.2 + 2 * (i * n + j)) [(A i j).1, M.neg (A i j).2]) rfl) hspace
    exact hw.mono le_rfl fun _ _ hm => ⟨hm.1, hm.2.trans hp⟩

/-- Mirroring completes the full matrix from a readable upper triangle. The stored diagonal
is preserved; a zero-imaginary diagonal or numerical Hermitian interpretation is a separate
property of the supplied upper entries and scalar machine. -/
theorem writes_mirror {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {n : ℕ} {y : ℕ × ℕ}
    (A : ℕ → ℕ → K × K) (hl : y.1 < m.store.length)
    (hz : y.2 + 2 * (n * n) ≤ m.store.len y.1)
    (hu : m.store.HoldsRowEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
      (fun j => j + 1) A) :
    Writes md I τ (mirror (Op := Op) (Tst := Tst)).body (Env.frame [n] [y, y])
      ((EntryCodec.pair K).regionFp y.1 y.2 n (fun i j => i * n + j) (fun j => j))
      (fun m' => m'.store.HoldsEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (completeUpper M A) ∧ m'.pos = m.pos) m := by
  refine ((writes_mirror_lower hI A hl hz hu).keep
    (Store.readsOnly_holdsRowEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
      (fun j => j + 1) A) ((EntryCodec.pair K).disj_regionFp_triangles n y.1 y.2) hu).mono le_rfl ?_
  intro m' _ ⟨⟨hlower, hp⟩, hupper⟩
  refine ⟨?_, hp⟩
  intro i hi j hj z
  by_cases hij : i ≤ j
  · simpa only [completeUpper, if_pos hij] using hupper j hj i (Nat.lt_succ_of_le hij) z
  · have hji : j < i := by omega
    simpa only [completeUpper, if_neg hij] using hlower i hi j hji z

end NLAlib.Ops.Hermitian
