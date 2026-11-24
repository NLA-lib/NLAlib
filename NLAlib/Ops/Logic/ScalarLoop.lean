/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Catalog.Scalar

/-!
# Loops of one scalar call over the cells of a block

A loop whose round $t$ applies one scalar operation to the cell $o + t$ of a block, in place,
stores in each cell the machine value of the operation on its old word. The rule states the
footprint (the block) and the stored words, for any tree in which the loop occurs.

## Main results

* `NLAlib.Ops.writes_loop_mul_cell`: the in-place scaling of a block by a cell outside it.
-/

@[expose] public section

namespace NLAlib.Ops

variable {Op Tst K : Type}

/-- **An in-place scaling loop**: the loop of $N$ rounds whose round $t$ multiplies the cell
$o + t$ of the buffer $b$ by a cell $y$ outside the block, in place, stores in each cell of the
block the machine product of its old word with the word of $y$; it writes only the block and keeps
the tape position. -/
theorem writes_loop_mul_cell [Has ScalarOp Op] {M : Machine K}
    {I : Interp Op Tst K} (hS : IsScalar M I) {τ : Tape K} {ρ : Env} {m : Mem K}
    {n : IExp} {N b o : ℕ} {y : ℕ × ℕ} {X Y : Operand} {r : K} (hn : n.eval ρ.idx = some N)
    (hX : ∀ t < N, Operand.evalList (ρ.pushIdx t) [X, Y] = some [(b, o + t), y])
    (hX' : ∀ t < N, Operand.evalList (ρ.pushIdx t) [X] = some [(b, o + t)])
    (hl : m.Live [(b, o), y]) (hv : ∀ t < N, ∃ w, m.store.get b (o + t) = some w)
    (hy : m.store.get y.1 y.2 = some r) (hyb : ¬ Store.inBlock b o N y.1 y.2) :
    Writes .total I τ (.loop n (.call (Has.inj ScalarOp.mul) [] [X, Y] [X])) ρ (Store.inBlock b o N)
      (fun m' => m'.pos = m.pos ∧ ∀ t < N, ∀ w, m.store.get b (o + t) = some w →
        m'.store.get b (o + t) = some (M.mul w r)) m := by
  refine (writes_loop hn (fun i => Store.inBlock b o i)
    (fun i _ => Fp.inBlock_le_inBlock le_rfl (by omega))
    (fun i m' => m'.pos = m.pos ∧ ∀ t < i, ∀ w, m.store.get b (o + t) = some w →
      m'.store.get b (o + t) = some (M.mul w r)) ⟨rfl, fun t ht => absurd ht (by omega)⟩
    fun i hi m' hfr ⟨hpos, hdone⟩ => ?_).mono le_rfl fun _ _ h => h
  have hlen := hfr.len_eq b
  obtain ⟨w, hw⟩ := hv i hi
  have hroom : o + i < m.store.len b := Store.lt_len_of_get hw
  have hw' : m'.store.get b (o + i) = some w := by
    rw [hfr.2 b (o + i) (by simp [Store.inBlock]), hw]
  have hy' : m'.store.get y.1 y.2 = some r := by
    rw [hfr.2 y.1 y.2 fun h => hyb ⟨h.1, h.2.1, by have := h.2.2; omega⟩, hy]
  have hl' : m'.Live [(b, o + i), y, (b, o + i)] := by
    have h0 := hl.congr hfr.length_eq
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact h0 (b, o) (by simp)
    · exact h0 x (by simp)
    · exact h0 (b, o) (by simp)
  refine (writes_call_bin (hS .mul) (hX i hi) (hX' i hi) trivial hw' hy' rfl
    fun _ => ⟨hl', show o + i < m'.store.len b by rw [hlen]; exact hroom⟩).mono
    (show Store.inBlock b (o + i) 1 ≤ Store.inBlock b o (i + 1) from
      Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  rintro m'' hfr' ⟨hp, hg⟩
  refine ⟨hp.trans hpos, fun t ht v hv => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
  · rw [hfr'.2 b (o + t) (by simp [Store.inBlock]; omega), hdone t ht v hv]
  · rw [hg, Option.some.inj (hw.symm.trans hv)]

end NLAlib.Ops
