/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.View

/-!
# Packed views and ordinary blocks

A packed rectangular view has exactly the cells of an ordinary contiguous block. Unit-stride
vectors are the one-row case. This identity lets a strided-copy routine compose with contiguous
BLAS without a second copying proof or a change of data representation.

## Main results

* `NLAlib.Ops.Store.readView_packedMatrix`: packed rectangular reads are contiguous.
* `NLAlib.Ops.Store.readView_unitStride`: unit-stride and contiguous reads agree.
-/

@[expose] public section

namespace NLAlib.Ops.View

/-- A packed rectangular view visits consecutive cells, also when its row count is zero. -/
@[simp] theorem offset_packedMatrix (rows cols k : ℕ) :
    (⟨rows, some (cols, rows)⟩ : View).offset k = k := by
  rw [offset_runs, Nat.div_add_mod]

end NLAlib.Ops.View

namespace NLAlib.Ops.Store

variable {K : Type}

/-- Packed rectangular views and their contiguous word blocks have identical reads. -/
@[simp] theorem readView_packedMatrix (s : Store K) (b off rows cols : ℕ) :
    s.readView b off ⟨rows, some (cols, rows)⟩ = s.readBlock b off (rows * cols) := by
  apply Option.ext
  intro xs
  simp only [readView_eq_some_iff, readBlock_eq_some_iff,
    View.cells_runs, View.offset_packedMatrix, Nat.mul_comm]

/-- Reading singleton runs at period one is precisely the ordinary block read, including
empty blocks and failed reads. This is the one-row case of the packed-view identity. -/
theorem readView_unitStride (s : Store K) (b off n : ℕ) :
    s.readView b off ⟨1, some (n, 1)⟩ = s.readBlock b off n := by
  simpa only [Nat.one_mul] using readView_packedMatrix s b off 1 n

/-- An in-range cell of a readable view is its list entry, for any chosen default word.
The bound prevents the default from being used. -/
theorem getD_of_readView {s : Store K} {b off : ℕ} {v : View} {xs : List K}
    (h : s.readView b off v = some xs) {k : ℕ} (hk : k < v.cells) (d : K) :
    s.get b (off + v.offset k) = some (xs.getD k d) := by
  have hlen := length_of_readView h
  rw [get_of_readView h hk, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega), Option.getD_some]

end NLAlib.Ops.Store

namespace NLAlib.Ops.Fp

/-- The actual footprint of a packed rectangular view is its contiguous word block. -/
@[simp, fpNF] theorem inView_packedMatrix (b off rows cols : ℕ) :
    inView b off ⟨rows, some (cols, rows)⟩ = Store.inBlock b off (rows * cols) := by
  funext b' i
  apply propext
  rw [inView_apply]
  simp only [View.cells_runs, View.offset_packedMatrix]
  constructor
  · rintro ⟨hb, k, hk, rfl⟩
    have hk' : k < rows * cols := by simpa only [Nat.mul_comm] using hk
    exact ⟨hb, by omega, by omega⟩
  · rintro ⟨hb, hlo, hhi⟩
    refine ⟨hb, i - off, ?_, by omega⟩
    simpa only [Nat.mul_comm] using (show i - off < rows * cols from by omega)

/-- Singleton runs at period one write precisely the cells of the corresponding block. -/
theorem inView_unitStride (b off n : ℕ) :
    inView b off ⟨1, some (n, 1)⟩ = Store.inBlock b off n := by
  simpa only [Nat.one_mul] using inView_packedMatrix b off 1 n

end NLAlib.Ops.Fp
