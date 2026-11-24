/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Matrix
public import NLAlib.Ops.Blas.HermitianEntry
public import NLAlib.Ops.Logic.EntryRows
public import NLAlib.Ops.Logic.RoutineIntro

/-!
# Stored correctness of interleaved matrix transformations

Conjugate transpose is a scalar entry conjugation at an injective target-index map. Region
fill maintains all output entries and the ordinary frame rule retains readable input entries,
including disjoint input and output regions in the same buffer.

## Main definitions

* `NLAlib.Ops.PairMatrix.copySpec`: what copying an interleaved matrix writes.

## Main results

* `NLAlib.Ops.PairMatrix.copyRoutine_meets`: the copy meets its specification.
* `NLAlib.Ops.PairMatrix.conjTranspose_writes`: the actual stored conjugate transpose.
-/

@[expose] public section

namespace NLAlib.Ops.PairMatrix

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Copying an interleaved matrix is the generic unary map of scalar copy, including
exact in-place operands and spatially disjoint regions of a shared buffer.
A step in the proof of `NLAlib.Ops.PairMatrix.copyRoutine_meets`. -/
private theorem copy_wp_any [Inhabited K] {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {rows cols : ℕ} {x y : ℕ × ℕ} {xs : List K}
    (hl : m.Live [x, y])
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (rows * cols)))
      (Store.inBlock y.1 y.2 (2 * (rows * cols))) ∨ x = y)
    (hx : m.store.readBlock x.1 x.2 (2 * (rows * cols)) = some xs)
    (hy : y.2 + 2 * (rows * cols) ≤ m.store.len y.1)
    {Q : Mem K → Prop} (hQ : Q (m.updBlock y xs)) :
    Wp md I τ (copy (Op := Op) (Tst := Tst))
      (Env.frame [rows, cols] [x, y]) Q m := by
  refine wp_frame rfl rfl hl
    (unaryMap_wp_of_disj_or_eq (hI .copy) (f := id) hxy hx hy ?_)
  simpa using hQ

/-- Copy writes exactly its stored input block, frames every other cell, and consumes no
random words. No source/output buffer inequality is required.
A step in the proof of `NLAlib.Ops.PairMatrix.copyRoutine_meets`. -/
private theorem copy_writes_any [Inhabited K] {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {rows cols : ℕ} {x y : ℕ × ℕ} {xs : List K}
    (hl : m.Live [x, y])
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (rows * cols)))
      (Store.inBlock y.1 y.2 (2 * (rows * cols))) ∨ x = y)
    (hx : m.store.readBlock x.1 x.2 (2 * (rows * cols)) = some xs)
    (hy : y.2 + 2 * (rows * cols) ≤ m.store.len y.1) :
    Writes md I τ (copy (Op := Op) (Tst := Tst))
      (Env.frame [rows, cols] [x, y]) (Store.inBlock y.1 y.2 (2 * (rows * cols)))
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock y.1 y.2 (2 * (rows * cols)) = some xs) m := by
  have hw := Writes.of_wp_eq_updBlock (copy_wp_any hI (md := md) (τ := τ) hl hxy hx hy
    (Q := fun m' => m' = m.updBlock y xs) rfl)
  have hlen := Store.length_of_readBlock hx
  rw [hlen] at hw
  refine hw.mono le_rfl fun m' _ he => ?_
  subst m'
  have hr := Store.readBlock_updBlock_self (s := m.store) (b := y.1) (off := y.2)
    (xs := xs) (by simpa [hlen] using hy)
  exact ⟨rfl, by simpa [hlen] using hr⟩

/-- The written block is the block read. -/
def copySpec : Routine.Spec K :=
  spec% [rows, cols] (xs) → (ys) ensures ys = xs

/-- Copying an interleaved matrix meets its specification under the scalar copy, for blocks
that are apart, including two regions of one buffer. -/
theorem copyRoutine_meets [Inhabited K] {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) : (copyRoutine (Op := Op) (Tst := Tst)).Meets I (copySpec (K := K)) := by
  routine_intro [rows, cols] (x, y) reads (xs)
  have hd : Fp.Disj (Store.inBlock x.1 x.2 (2 * (rows * cols)))
      (Store.inBlock y.1 y.2 (2 * (rows * cols))) := by
    have h : Fp.Disj (Fp.blocks [y] [2 * (rows * cols)]) (Fp.blocks [x] [2 * (rows * cols)]) :=
      hsep.2.1
    simpa [Fp.blocks] using h.symm
  refine (copy_writes_any hI hlive (.inl hd) hxs hrooms.1).mono (by fp_sub) fun m' _ h => ?_
  exact ⟨h.1, [xs], Mem.readBlocks_of_cons h.2 rfl, rfl⟩

/-- The judgment of `NLAlib.Ops.PairMatrix.copyRoutine` read at operands: the copy writes the
block read. A corollary of `NLAlib.Ops.PairMatrix.copyRoutine_meets`, kept because the
block-sequence rule `NLAlib.Ops.Writes.seq_readBlock` takes its statement in this form. -/
theorem copy_writes [Inhabited K] {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {m : Mem K} {rows cols : ℕ} {x y : ℕ × ℕ} {xs : List K}
    (hl : m.Live [x, y])
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (rows * cols)))
      (Store.inBlock y.1 y.2 (2 * (rows * cols))))
    (hx : m.store.readBlock x.1 x.2 (2 * (rows * cols)) = some xs)
    (hy : y.2 + 2 * (rows * cols) ≤ m.store.len y.1) :
    Writes .total I τ (copy (Op := Op) (Tst := Tst))
      (Env.frame [rows, cols] [x, y]) (Store.inBlock y.1 y.2 (2 * (rows * cols)))
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock y.1 y.2 (2 * (rows * cols)) = some xs) m := by
  have hroom : m.Room [y] [2 * (rows * cols)] := by
    simpa only [Mem.room_cons, Mem.room_nil, and_true] using hy
  have h := copyRoutine_meets (Op := Op) (Tst := Tst) hI [rows, cols] [x, y] τ m [xs] rfl rfl
    hl (by routine_sep) (Mem.readBlocks_of_cons hx rfl) trivial hroom
  refine h.mono (by fp_sub) fun m' _ ⟨hpos, ys, hys, hpost⟩ => ?_
  routine_nf at hys hpos
  split_reads hys as (zs)
  obtain rfl : zs = xs := hpost
  exact ⟨hpos, hzs⟩

/-- Conjugate transpose writes the machine-negated imaginary words and copied real words of
the actual input matrix. Input and output word blocks are disjoint, including when they share
a buffer. No initialized output words, numerical model or successful-run premise is assumed.
A fragment of the tree `NLAlib.SpectralBisection.compress`. -/
theorem conjTranspose_writes {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {r c : ℕ} {x y : ℕ × ℕ}
    (A : ℕ → ℕ → K × K) (hl : m.Live [x, y])
    (hx : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, r, c, r⟩ A)
    (hy : y.2 + 2 * (r * c) ≤ m.store.len y.1)
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (c * r)))
      (Store.inBlock y.1 y.2 (2 * (r * c)))) :
    Writes md I τ (conjTranspose (Op := Op) (Tst := Tst))
      (Env.frame [r, c] [x, y]) (Store.inBlock y.1 y.2 (2 * (r * c)))
      (fun m' => m'.store.HoldsEntries (EntryCodec.pair K) ⟨y.1, y.2, c, r, c⟩
        (fun i j => ((A j i).1, M.neg (A j i).2)) ∧ m'.pos = m.pos) m := by
  let C := EntryCodec.pair K
  have hbound : ∀ j < c, ∀ i < r, i * c + j < r * c :=
    fun j hj i hi => Idx.add_lt_mul hi hj
  have hfp := C.regionFp_le_inBlock y.1 y.2 c (r * c)
    (fun i j => i * c + j) (fun _ => r) hbound
  suffices hfill : Writes md I τ (conjTranspose (Op := Op) (Tst := Tst))
      (Env.frame [r, c] [x, y])
      (C.regionFp y.1 y.2 c (fun i j => i * c + j) (fun _ => r))
      (fun m' => m'.store.HoldsEntryRegion C y.1 y.2 c (fun i j => i * c + j)
        (fun _ => r) (fun i j => ((A i j).1, M.neg (A i j).2)) ∧ m'.pos = m.pos) m by
    exact hfill.mono hfp fun m' _ hp => ⟨fun i hi j hj z => hp.1 i hi j hj z, hp.2⟩
  refine writes_fillEntryRegion C y.1 y.2 c (fun i j => i * c + j) (fun _ => r)
    ?_ rfl (fun _ => rfl) (fun i j => ((A i j).1, M.neg (A i j).2))
    (fun _ _ => m.pos) rfl (fun _ _ => rfl) ?_
  · intro p hp q hq he
    have hd := congrArg (· / c) he
    have hm := congrArg (· % c) he
    simp only [Idx.div_add hp.1, Idx.div_add hq.1] at hd
    simp only [Idx.mod_add hp.1, Idx.mod_add hq.1] at hm
    exact Prod.ext hd hm
  · intro j hj i hi m' hfr hp
    have hfull := (hfr.mono (C.regionUpto_le_regionFp y.1 y.2 c
      (fun i j => i * c + j) (fun _ => r) hj hi.le)).mono hfp
    have hinput := hfull.keep
      (Store.readsOnly_holdsEntries C ⟨x.1, x.2, r, c, r⟩ A le_rfl) hxy.symm hx
    have hxr := hinput i hi j hj 0
    have hxi := hinput i hi j hj 1
    have hy' : y.2 + 2 * (r * c) ≤ m'.store.len y.1 := by rw [hfr.len_eq]; exact hy
    have hspace : y.2 + 2 * (i * c + j) + 2 ≤ m'.store.len y.1 :=
      C.room_entry (L := ⟨y.1, y.2, c, r, c⟩) le_rfl hj hi hy'
    have hprotect : x.1 ≠ y.1 ∨ x.2 + 2 * (j * r + i) + 1 ≠ y.2 + 2 * (i * c + j) := by
      by_cases hb : x.1 = y.1
      · right
        intro he
        have hxidx := Idx.add_lt_mul hj hi
        have hyidx := hbound j hj i hi
        exact hxy x.1 (x.2 + 2 * (j * r + i) + 1)
          ⟨rfl, by omega, by omega⟩ ⟨hb, by omega, by omega⟩
      · exact Or.inl hb
    have hwp := Hermitian.conjugatePair_wp hI (md := md) (τ := τ) (m := m')
      (x := (x.1, x.2 + 2 * (j * r + i))) (z := (y.1, y.2 + 2 * (i * c + j)))
      hxr hxi hspace hprotect
      (Q := fun m'' => m'' = m'.updBlock (y.1, y.2 + 2 * (i * c + j))
        [(A i j).1, M.neg (A i j).2]) rfl
    have hentry := Hermitian.pair_writes_of_wp (md := md) (I := I) (τ := τ) (m := m')
      (z := (y.1, y.2 + 2 * (i * c + j))) (v := ((A i j).1, M.neg (A i j).2)) hwp hspace
    refine writes_frame rfl rfl (by simpa [Mem.Live] using hl.congr hfr.length_eq) ?_
    exact hentry.mono le_rfl fun _ _ h => ⟨h.1, h.2.trans hp⟩

end NLAlib.Ops.PairMatrix
