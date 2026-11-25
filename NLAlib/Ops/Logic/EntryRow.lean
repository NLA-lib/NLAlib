/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Layout
public import NLAlib.Ops.Logic.View
public import NLAlib.Ops.Logic.EntryLayout

/-!
# Replacing one stored matrix row

A row occupies a strided view in a column-major layout. Its precise frame preserves every
other row, even when the leading dimension includes padding. The scalar and pivoted LU
drivers use this rule when they materialize an upper row.

## Main results

* `NLAlib.Ops.Store.HoldsMat.update_row_of_frame`: reconstruct the matrix after a row write.
-/

@[expose] public section

namespace NLAlib.Ops.Store

variable {K : Type}

/-- A one-word scalar codec expresses exactly the ordinary word-matrix predicate. This bridge
lets word-level row frames use the shared entry-codec column reconstruction rules. -/
theorem holdsMat_iff_holdsEntries_scalar {s : Store K} {L : MatLayout}
    {A : ℕ → ℕ → K} : s.HoldsMat L A ↔ s.HoldsEntries (EntryCodec.scalar K) L A := by
  constructor
  · intro h i hi j hj z
    have hz : z = 0 := Subsingleton.elim _ _
    subst z
    simpa [MatLayout.cell, EntryCodec.scalar, Nat.add_assoc] using h i hi j hj
  · intro h i hi j hj
    simpa [MatLayout.cell, EntryCodec.scalar, Nat.add_assoc] using h i hi j hj (0 : Fin 1)

/-- Read a suffix of one stored row as its actual words. The suffix may be empty; padding
between columns is skipped by the view's leading-dimension increment. -/
theorem HoldsMat.readView_row_suffix {s : Store K} {L : MatLayout}
    {A : ℕ → ℕ → K} (h : s.HoldsMat L A) {i : ℕ} (hi : i < L.rows) (start : ℕ) :
    s.readView L.buf (L.off + start * L.ld + i)
      ⟨1, some (L.cols - start, L.ld)⟩ =
      some ((List.range (L.cols - start)).map fun j => A i (start + j)) := by
  apply readView_eq_some_iff.mpr
  refine ⟨by simp, fun j hj => ?_⟩
  have hj' : j < L.cols - start := by simpa using hj
  have hg := h i hi (start + j) (by omega)
  simpa [MatLayout.cell, View.offset_runs_one, hj', Nat.add_mul, Nat.mul_add,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using hg

/-- Replace one matrix row from its final strided read and preserve every other entry through
the row frame. Padding is unrestricted and the entries are arbitrary words. -/
theorem HoldsMat.update_row_of_frame {s s' : Store K} {L : MatLayout}
    {A : ℕ → ℕ → K} (h : s.HoldsMat L A) (hL : L.Valid) {k : ℕ} (hk : k < L.rows)
    (hfr : s.EqOff (Fp.inView L.buf (L.off + k) ⟨1, some (L.cols, L.ld)⟩) s')
    (v : ℕ → K)
    (hv : s'.readView L.buf (L.off + k) ⟨1, some (L.cols, L.ld)⟩ =
      some ((List.range L.cols).map v)) :
    s'.HoldsMat L (fun i j => if i = k then v j else A i j) := by
  intro i hi j hj
  change s'.get L.buf (L.cell i j) = some (if i = k then v j else A i j)
  by_cases hik : i = k
  · subst i
    have hg := (readView_eq_some_iff.mp hv).2 j (by simpa using hj)
    simpa [MatLayout.cell, Nat.add_assoc, Nat.add_comm, Nat.mul_comm, hj] using hg
  · rw [if_neg hik, hfr.get_eq ?_]
    · exact h i hi j hj
    · intro hf
      obtain ⟨-, q, hq, he⟩ := Fp.inView_apply.mp hf
      have he' : j * L.ld + i = L.ld * q + k := by
        simp only [MatLayout.cell, View.offset_runs_one] at he
        omega
      have hir : i < L.ld := hi.trans_le hL
      have hkr : k < L.ld := hk.trans_le hL
      have hemod := congrArg (fun t => t % L.ld) he'
      have hik' : i = k := by
        simpa [Nat.add_mod, Nat.mod_eq_of_lt hir, Nat.mod_eq_of_lt hkr] using hemod
      exact hik hik'

/-- Replace a suffix of one matrix row. Earlier columns of that row and every other row
retain their original words. An empty suffix is allowed, including a start past the end. -/
theorem HoldsMat.update_row_suffix_of_frame [Inhabited K] {s s' : Store K} {L : MatLayout}
    {A : ℕ → ℕ → K} (h : s.HoldsMat L A) (hL : L.Valid) {k : ℕ} (hk : k < L.rows)
    (start : ℕ) {ys : List K}
    (hfr : s.EqOff
      (Fp.inView L.buf (L.off + start * L.ld + k) ⟨1, some (L.cols - start, L.ld)⟩) s')
    (hy : s'.readView L.buf (L.off + start * L.ld + k)
      ⟨1, some (L.cols - start, L.ld)⟩ = some ys) :
    s'.HoldsMat L (fun i j => if i = k ∧ start ≤ j then vec ys (j - start) else A i j) := by
  let v := fun j => if start ≤ j then vec ys (j - start) else A k j
  have hsub : Fp.inView L.buf (L.off + start * L.ld + k)
      ⟨1, some (L.cols - start, L.ld)⟩ ≤
      Fp.inView L.buf (L.off + k) ⟨1, some (L.cols, L.ld)⟩ := by
    intro b o ho
    obtain ⟨rfl, t, ht, he⟩ := Fp.inView_apply.mp ho
    have ht' : t < L.cols - start := by simpa using ht
    apply Fp.inView_apply.mpr
    refine ⟨rfl, start + t, by simpa using (show start + t < L.cols by omega), ?_⟩
    simpa [View.offset_runs_one, Nat.add_mul, Nat.mul_add, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using he
  have hread : s'.readView L.buf (L.off + k) ⟨1, some (L.cols, L.ld)⟩ =
      some ((List.range L.cols).map v) := by
    apply readView_eq_some_iff.mpr
    refine ⟨by simp, fun j hj => ?_⟩
    have hj' : j < L.cols := by simpa using hj
    have hg : s'.get L.buf (L.off + k + L.ld * j) = some (v j) := by
      by_cases hs : start ≤ j
      · have hq : j - start < L.cols - start := by omega
        have hget := (readView_eq_some_iff.mp hy).2 (j - start) (by simpa using hq)
        have hget' : s'.get L.buf (L.off + k + L.ld * j) = ys[j - start]? := by
          have hm : L.ld * start + L.ld * (j - start) = L.ld * j := by
            rw [← Nat.mul_add]
            congr 1
            omega
          have he : L.off + start * L.ld + k + L.ld * (j - start) =
              L.off + k + L.ld * j := by
            rw [Nat.mul_comm start L.ld]
            omega
          simpa only [View.offset_runs_one, he] using hget
        have hl := length_of_readView hy
        have hql : j - start < ys.length := by simpa [hl] using hq
        simpa only [v, if_pos hs, vec, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hql, Option.getD_some] using hget'
      · rw [hfr.get_eq ?_]
        · simpa [v, hs, MatLayout.cell, Nat.add_assoc, Nat.add_comm, Nat.mul_comm] using
            h k hk j hj'
        · intro hf
          obtain ⟨_, t, _, he⟩ := Fp.inView_apply.mp hf
          have he' : L.off + k + j * L.ld = L.off + k + (start + t) * L.ld := by
            simpa [View.offset_runs_one, Nat.mul_add, Nat.add_mul, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using he
          have hld : 0 < L.ld := (Nat.zero_le k).trans_lt (hk.trans_le hL)
          have hjt := Nat.eq_of_mul_eq_mul_right hld
            (Nat.add_left_cancel he')
          omega
    simpa [View.offset_runs_one, hj'] using hg
  have hnew := h.update_row_of_frame hL hk (hfr.mono hsub) v hread
  intro i hi j hj
  have hg := hnew i hi j hj
  by_cases hik : i = k <;> by_cases hsj : start ≤ j <;>
    simpa [v, hik, hsj] using hg

end NLAlib.Ops.Store
