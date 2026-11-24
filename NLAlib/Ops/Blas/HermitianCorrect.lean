/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.HermitianUpper
public import NLAlib.Ops.Blas.HermitianMirror
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax

/-!
# Functional correctness of Hermitian scalar kernels

Upper-entry computations and mirroring compose through one shared completion theorem. The
computed words use the supplied scalar machine, including its literal zero and every rounded
division. Numerical accuracy and Hermitian decoding require the machine's numerical model;
functional execution itself makes neither assumption.

## Main results

* `NLAlib.Ops.Hermitian.shiftRoutine`, `NLAlib.Ops.Hermitian.scaleRoutine`,
  `NLAlib.Ops.Hermitian.averageRoutine`: the three completions as routines
  `[n] (X : 2 n n, c : 1) → (Y : 2 n n)`, on the trees `NLAlib.Ops.Hermitian.shift`,
  `NLAlib.Ops.Hermitian.scale`, `NLAlib.Ops.Hermitian.average`.
* `NLAlib.Ops.Hermitian.shiftRoutine_meets`, `NLAlib.Ops.Hermitian.scaleRoutine_meets`,
  `NLAlib.Ops.Hermitian.averageRoutine_meets`: their judgments, on any scalar machine.
* `NLAlib.Ops.Hermitian.shift_writes`, `NLAlib.Ops.Hermitian.scale_writes`,
  `NLAlib.Ops.Hermitian.average_writes`: the runs stated on the entries of the stored matrix.
-/

@[expose] public section

namespace NLAlib.Ops.Hermitian

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- An upper-region implementation followed by the common mirror procedure returns the
complete matrix. The mirror's framing, buffer liveness and capacity transport are shared by
all three entrywise transformations. -/
theorem complete_writes {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} (up : Stmt Op Tst) {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K}
    (U : ℕ → ℕ → K × K) (hy : y.1 < m.store.length)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1)
    (hu : Writes .total I τ up (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsRowEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (fun j => j + 1) U ∧ μ.pos = m.pos) m) :
    Writes .total I τ (complete up) (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (completeUpper M U) ∧ μ.pos = m.pos) m := by
  refine hu.seq_le le_rfl fun μ hfr hp => ?_
  have hy' : y.1 < μ.store.length := by rw [hfr.length_eq]; exact hy
  have hY' : y.2 + 2 * (n * n) ≤ μ.store.len y.1 := by rw [hfr.len_eq]; exact hY
  have hw := mirror_writes (md := .total) (τ := τ) hI U hy' hY' hp.1
  refine (writes_frame rfl rfl (by simp [Mem.Live, hy']) hw).mono ?_ ?_
  · exact (EntryCodec.pair K).regionFp_le_inBlock y.1 y.2 n (n * n)
      (fun i j => i * n + j) id (fun j hj i hi => Idx.add_lt_mul (hi.trans hj) hj)
  · intro μ' _ h
    exact ⟨h.1, h.2.trans hp.2⟩

/-- A shifted Hermitian matrix is computed from copied upper entries and actual rounded
real diagonal differences. Disjoint input/output regions may belong to the same arena.
The run stated on the entries of the stored matrix: a step in the proof of
`NLAlib.Ops.Hermitian.shiftRoutine_meets`, and the form from which
`NLAlib.Ops.Hermitian.shift_writes_packed` reads the result on a floating point machine. -/
theorem shift_writes {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K} {A : ℕ → ℕ → K × K} {d : K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A)
    (hc : m.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1) (hl : m.Live [x, c, y]) :
    Writes .total I τ (shift (Op := Op) (Tst := Tst)) (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (completeUpper M (fun i j => if i = j then
          (M.sub (A i i).1 d, M.lit 0) else A i j)) ∧ μ.pos = m.pos) m :=
  complete_writes hI shiftUpper _ (hl y (by simp)) hY
    (shiftUpper_writes hI hxy hcy hX hc hY hl)

/-- Scalar division and Hermitian completion return the actual rounded word matrix.
A nonzero decoded divisor is needed for numerical error estimates, rather than this
functional execution theorem.
The run stated on the entries of the stored matrix: a step in the proof of
`NLAlib.Ops.Hermitian.scaleRoutine_meets`, and the form from which
`NLAlib.Ops.Hermitian.scale_writes_packed` reads the result on a floating point machine. -/
theorem scale_writes {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K} {A : ℕ → ℕ → K × K} {d : K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A)
    (hc : m.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1) (hl : m.Live [x, c, y]) :
    Writes .total I τ (scale (Op := Op) (Tst := Tst)) (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (completeUpper M (fun i j => if i = j then (M.div (A i i).1 d, M.lit 0)
          else (M.div (A i j).1 d, M.div (A i j).2 d))) ∧ μ.pos = m.pos) m :=
  complete_writes hI scaleUpper _ (hl y (by simp)) hY
    (scaleUpper_writes hI hxy hcy hX hc hY hl)

/-- Rounded addition/subtraction of transposed entries, rounded division, and completion
return the actual Hermitian-averaged word matrix with imaginary diagonal zero.
The run stated on the entries of the stored matrix: a step in the proof of
`NLAlib.Ops.Hermitian.averageRoutine_meets`, and the form from which
`NLAlib.Ops.Hermitian.average_writes_packed` reads the result on a floating point machine. -/
theorem average_writes {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K} {A : ℕ → ℕ → K × K} {d : K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A)
    (hc : m.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1) (hl : m.Live [x, c, y]) :
    Writes .total I τ (average (Op := Op) (Tst := Tst)) (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (completeUpper M (fun i j => if i = j then
          (M.div (M.add (A i i).1 (A i i).1) d, M.lit 0)
          else (M.div (M.add (A i j).1 (A j i).1) d,
            M.div (M.sub (A i j).2 (A j i).2) d))) ∧ μ.pos = m.pos) m :=
  complete_writes hI averageUpper _ (hl y (by simp)) hY
    (averageUpper_writes hI hxy hcy hX hc hY hl)

/-- The upper entries of a shifted matrix: the stored real diagonal minus `d` with imaginary
word the literal zero, and the stored entries off the diagonal. -/
def shiftEntries (M : Machine K) (A : ℕ → ℕ → K × K) (d : K) : ℕ → ℕ → K × K :=
  fun i j => if i = j then (M.sub (A i i).1 d, M.lit 0) else A i j

/-- The upper entries of a scaled matrix: every word divided by `d`, with imaginary diagonal
the literal zero. -/
def scaleEntries (M : Machine K) (A : ℕ → ℕ → K × K) (d : K) : ℕ → ℕ → K × K :=
  fun i j => if i = j then (M.div (A i i).1 d, M.lit 0)
    else (M.div (A i j).1 d, M.div (A i j).2 d)

/-- The upper entries of a Hermitian average: the entry plus the conjugate of its transpose,
divided by `d`, with imaginary diagonal the literal zero. -/
def averageEntries (M : Machine K) (A : ℕ → ℕ → K × K) (d : K) : ℕ → ℕ → K × K :=
  fun i j => if i = j then (M.div (M.add (A i i).1 (A i i).1) d, M.lit 0)
    else (M.div (M.add (A i j).1 (A j i).1) d, M.div (M.sub (A i j).2 (A j i).2) d)

/-- The written block packs the Hermitian completion `NLAlib.Ops.Hermitian.completeUpper` of
the upper entries `U` computed from the entries of the block read and the stored scalar. -/
def completedSpec [Inhabited K] (M : Machine K)
    (U : (ℕ → ℕ → K × K) → K → ℕ → ℕ → K × K) : Routine.Spec K :=
  spec% [n] (xs, [d]) → (ys) ensures
    ys = (EntryCodec.pair K).packFinMatrix (Matrix.of fun (i j : Fin n) =>
      completeUpper M (U (fun i j => (EntryCodec.pair K).entry xs (j * n + i)) d) i j)

/-- Subtract a stored scalar times the identity and complete:
`[n] (X : 2 n n, c : 1) → (Y : 2 n n)`, the output apart from the matrix and the scalar. -/
def shiftRoutine : Routine Op Tst :=
  routine% [n] (X : 2 * (n * n), c : 1) → (Y : 2 * (n * n)) by blocks := shift

/-- Divide by a stored scalar and complete: `[n] (X : 2 n n, c : 1) → (Y : 2 n n)`, the output
apart from the matrix and the scalar. -/
def scaleRoutine : Routine Op Tst :=
  routine% [n] (X : 2 * (n * n), c : 1) → (Y : 2 * (n * n)) by blocks := scale

/-- Add the conjugate transpose, divide by a stored scalar and complete:
`[n] (X : 2 n n, c : 1) → (Y : 2 n n)`, the output apart from the matrix and the scalar. -/
def averageRoutine : Routine Op Tst :=
  routine% [n] (X : 2 * (n * n), c : 1) → (Y : 2 * (n * n)) by blocks := average

/-- The shifted completion meets its specification on any scalar machine. -/
theorem shiftRoutine_meets [Inhabited K] {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) :
    (shiftRoutine (Op := Op) (Tst := Tst)).Meets I (completedSpec M (shiftEntries M)) := by
  routine_intro [n] (x, c, y) reads (xs, cs)
  obtain ⟨d, hc, rfl⟩ := Store.readBlock_one_eq_some.mp hcs
  have hd : Fp.Disj (Store.inBlock y.1 y.2 (2 * (n * n))) (Store.inBlock x.1 x.2 (2 * (n * n))) ∧
      Fp.Disj (Store.inBlock y.1 y.2 (2 * (n * n))) (Store.inBlock c.1 c.2 1) := by
    have h : Fp.Disj (Fp.blocks [y] [2 * (n * n)]) (Fp.blocks [x, c] [2 * (n * n), 1]) :=
      hblocks.2.1
    exact Fp.disj_sup_right.mp (by simpa [Fp.blocks] using h)
  have hB := Store.holdsEntries_of_readBlock (C := EntryCodec.pair K) (L := ⟨x.1, x.2, n, n, n⟩)
    rfl (by simpa only [Nat.mul_comm] using hxs)
  refine (shift_writes hI hd.1.symm hd.2.symm hB hc hroom hlive).mono (by fp_sub)
    fun μ _ ⟨hout, hpos⟩ => ?_
  have hread := hout.readBlock_packFinMatrix rfl
  exact ⟨hpos, [_], Mem.readBlocks_of_cons (by rw [Nat.mul_comm 2 (n * n)]; exact hread) rfl,
    rfl⟩

/-- The scaled completion meets its specification on any scalar machine; a nonzero decoded
divisor matters only for accuracy. -/
theorem scaleRoutine_meets [Inhabited K] {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) :
    (scaleRoutine (Op := Op) (Tst := Tst)).Meets I (completedSpec M (scaleEntries M)) := by
  routine_intro [n] (x, c, y) reads (xs, cs)
  obtain ⟨d, hc, rfl⟩ := Store.readBlock_one_eq_some.mp hcs
  have hd : Fp.Disj (Store.inBlock y.1 y.2 (2 * (n * n))) (Store.inBlock x.1 x.2 (2 * (n * n))) ∧
      Fp.Disj (Store.inBlock y.1 y.2 (2 * (n * n))) (Store.inBlock c.1 c.2 1) := by
    have h : Fp.Disj (Fp.blocks [y] [2 * (n * n)]) (Fp.blocks [x, c] [2 * (n * n), 1]) :=
      hblocks.2.1
    exact Fp.disj_sup_right.mp (by simpa [Fp.blocks] using h)
  have hB := Store.holdsEntries_of_readBlock (C := EntryCodec.pair K) (L := ⟨x.1, x.2, n, n, n⟩)
    rfl (by simpa only [Nat.mul_comm] using hxs)
  refine (scale_writes hI hd.1.symm hd.2.symm hB hc hroom hlive).mono (by fp_sub)
    fun μ _ ⟨hout, hpos⟩ => ?_
  have hread := hout.readBlock_packFinMatrix rfl
  exact ⟨hpos, [_], Mem.readBlocks_of_cons (by rw [Nat.mul_comm 2 (n * n)]; exact hread) rfl,
    rfl⟩

/-- The averaged completion meets its specification on any scalar machine. -/
theorem averageRoutine_meets [Inhabited K] {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) :
    (averageRoutine (Op := Op) (Tst := Tst)).Meets I (completedSpec M (averageEntries M)) := by
  routine_intro [n] (x, c, y) reads (xs, cs)
  obtain ⟨d, hc, rfl⟩ := Store.readBlock_one_eq_some.mp hcs
  have hd : Fp.Disj (Store.inBlock y.1 y.2 (2 * (n * n))) (Store.inBlock x.1 x.2 (2 * (n * n))) ∧
      Fp.Disj (Store.inBlock y.1 y.2 (2 * (n * n))) (Store.inBlock c.1 c.2 1) := by
    have h : Fp.Disj (Fp.blocks [y] [2 * (n * n)]) (Fp.blocks [x, c] [2 * (n * n), 1]) :=
      hblocks.2.1
    exact Fp.disj_sup_right.mp (by simpa [Fp.blocks] using h)
  have hB := Store.holdsEntries_of_readBlock (C := EntryCodec.pair K) (L := ⟨x.1, x.2, n, n, n⟩)
    rfl (by simpa only [Nat.mul_comm] using hxs)
  refine (average_writes hI hd.1.symm hd.2.symm hB hc hroom hlive).mono (by fp_sub)
    fun μ _ ⟨hout, hpos⟩ => ?_
  have hread := hout.readBlock_packFinMatrix rfl
  exact ⟨hpos, [_], Mem.readBlocks_of_cons (by rw [Nat.mul_comm 2 (n * n)]; exact hread) rfl,
    rfl⟩

end NLAlib.Ops.Hermitian
