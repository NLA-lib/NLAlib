/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.EntryRow
public import NLAlib.Ops.Logic.EntryColumn
public import NLAlib.Ops.Logic.ViewBlock

/-!
# Matrix entries and rectangular word views

The existing scalar matrix layout and a rectangular routine view describe the same logical
entries, including padding between columns. These bridges let packed scalar kernels read and
write submatrices through the routine interface without repeating coordinate proofs.

## Main results

* `NLAlib.Ops.Store.HoldsMat.readView`: a rectangular view reads packed logical entries.
* `NLAlib.Ops.Store.holdsMat_of_readView`: a readable rectangular view supplies matrix entries.
-/

@[expose] public section

namespace NLAlib.Ops.Store

variable {K : Type}

/-- A rectangular view in a caller-owned buffer is preserved when fresh buffers are added
or released. The handle bound is independent of the logical matrix shape. -/
theorem Below.readView_of {s s' : Store K} {L b off : ℕ} {v : View} {xs : List K}
    (h : Below L s s') (hb : b < L) (hr : s.readView b off v = some xs) :
    s'.readView b off v = some xs :=
  (readView_congr (fun _ _ => (h b hb).2 _)).trans hr

/-- A rectangular view of a stored scalar matrix reads its packed logical entries and skips
the padding between columns. No validity or nonempty-shape hypothesis is needed. -/
theorem HoldsMat.readView {s : Store K} {L : MatLayout} {A : ℕ → ℕ → K}
    (h : s.HoldsMat L A) :
    s.readView L.buf L.off ⟨L.rows, some (L.cols, L.ld)⟩ =
      some ((EntryCodec.scalar K).packMatrix L.rows L.cols A) := by
  apply readView_eq_some_iff.mpr
  constructor
  · simp only [EntryCodec.length_packMatrix, EntryCodec.scalar, Nat.mul_one, View.cells_runs]
  · intro q hq
    have hr : 0 < L.rows := by
      change q < L.cols * L.rows at hq
      exact Nat.pos_of_ne_zero fun he => by
        simp only [he, Nat.mul_zero] at hq
        exact Nat.not_lt_zero q hq
    have hi := Nat.mod_lt q hr
    have hj : q / L.rows < L.cols := (Nat.div_lt_iff_lt_mul hr).mpr hq
    have hq' : q < L.rows * L.cols := by
      simpa only [View.cells_runs, Nat.mul_comm] using hq
    simpa [MatLayout.cell, View.offset_runs, EntryCodec.packMatrix, EntryCodec.scalar_pack,
      hq', Nat.mul_comm, Nat.add_assoc] using h (q % L.rows) hi (q / L.rows) hj

/-- A successful rectangular read supplies the scalar matrix entries at its leading
dimension. Only in-range entries are asserted, so the padding default is never read. -/
theorem holdsMat_of_readView [Inhabited K] {s : Store K} {L : MatLayout} {xs : List K}
    (h : s.readView L.buf L.off ⟨L.rows, some (L.cols, L.ld)⟩ = some xs) :
    s.HoldsMat L (fun i j => vec xs (j * L.rows + i)) := by
  intro i hi j hj
  have hk := Idx.add_lt_mul hj hi
  have hg := getD_of_readView h hk default
  simpa only [MatLayout.cell, View.offset_runs, Idx.div_add hi, Idx.mod_add hi,
    Nat.mul_comm, Nat.add_assoc] using hg

end NLAlib.Ops.Store
