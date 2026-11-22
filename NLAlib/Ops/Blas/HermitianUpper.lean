/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Hermitian
public import NLAlib.Ops.Logic.EntryRows

/-!
# Upper-triangle matrix transformations

The scalar entry rules compose through the common variable-length entry-fill rule. Kernel
proofs state the mathematical entries; the fill rule preserves the previously written entries.

## Main results

* `NLAlib.Ops.Hermitian.copyTriangle_writes` copies the actual strict-upper stored word pairs.
-/

@[expose] public section

namespace NLAlib.Ops.Hermitian

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Copying the strict upper triangle returns the same stored entries and preserves every
other cell. Input and output blocks are disjoint, including within one live arena buffer.
An end statement in operand form: no other declaration of the library is proved from it. -/
theorem copyTriangle_writes {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {n : ℕ} {x y : ℕ × ℕ} {m : Mem K} {A : ℕ → ℕ → K × K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1) (hl : m.Live [x, y]) :
    Writes .total I τ (copyTriangle (Op := Op) (Tst := Tst)) (Env.frame [n] [x, y])
      ((EntryCodec.pair K).rowsFp ⟨y.1, y.2, n, n, n⟩ id)
      (fun m' => m'.store.HoldsRowEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩ id A ∧
        m'.pos = m.pos) m := by
  refine writes_fillEntryRows (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩ le_rfl id
    (fun _ hj => hj.le) rfl (fun _ => rfl) A (fun _ _ => m.pos) rfl
    (fun _ _ => rfl) ?_
  intro j hj i hi m' hfr hp
  change j < n at hj
  change i < j at hi
  let C := EntryCodec.pair K
  have hfrY : m.store.EqOff (Store.inBlock y.1 y.2 (2 * (n * n))) m'.store :=
    hfr.mono ((C.regionUpto_le_regionFp y.1 y.2 n (fun i j => j * n + i) id
      hj hi.le).trans (C.regionFp_le_inBlock y.1 y.2 n (n * n)
        (fun i j => j * n + i) id (fun j hj i hi => Idx.add_lt_mul hj (hi.trans hj))))
  have hinput := hfrY.keep
    (Store.readsOnly_holdsEntries C ⟨x.1, x.2, n, n, n⟩ A le_rfl) hxy.symm hX
  have hread (u : Fin 2) :
      m'.store.get x.1 (x.2 + 2 * (j * n + i) + u) =
        some ((EntryCodec.pair K).words (A i j) u) := by
    exact hinput i (hi.trans hj) j hj u
  have hflat : j * n + i < n * n := Idx.add_lt_mul hj (hi.trans hj)
  have hmul := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hflat)
  have hroom : y.2 + 2 * (j * n + i) + 2 ≤ m'.store.len y.1 := by
    rw [hfr.len_eq y.1]
    omega
  have hpair := hxy.mono (C.entryBlock_le_inBlock x.1 x.2 (n * n) hflat)
    (C.entryBlock_le_inBlock y.1 y.2 (n * n) hflat)
  have hentry := pair_writes_of_wp (md := .total) (τ := τ) (copyPair_wp_of_disj hI
    (x := (x.1, x.2 + 2 * (j * n + i))) (z := (y.1, y.2 + 2 * (j * n + i)))
    hpair (hread 0) (hread 1) hroom rfl) hroom
  refine (writes_frame rfl rfl ?_ hentry).mono le_rfl ?_
  · simpa [Mem.Live, hfr.length_eq] using hl
  · intro m'' _ he
    exact ⟨he.1, he.2.trans hp⟩

omit [Has ScalarOp Op] in
/-- A triangular entry procedure needs only a word-level transition specification. The shared
matrix rule supplies its actual entry, transposed entry, scalar, output room, and all framing.
The procedure is fixed before matrix sizes and values are chosen.
Shared by the trees of `NLAlib.Ops.Hermitian.copyTriangle`, `NLAlib.Ops.Hermitian.diagonal`,
`NLAlib.Ops.Hermitian.upper` and 4 more. -/
theorem triangle_writes {I : Interp Op Tst K} {τ : Tape K} (entry : Stmt Op Tst)
    (F : (K × K) → (K × K) → K → K × K)
    (hentry : ∀ (μ : Mem K) (x xt c z : ℕ × ℕ) (a aT : K × K) (d : K),
      Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock z.1 z.2 2) →
      Fp.Disj (Store.inBlock xt.1 xt.2 2) (Store.inBlock z.1 z.2 2) →
      Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock z.1 z.2 2) →
      μ.Live [x, xt, c, z] →
      μ.store.get x.1 x.2 = some a.1 → μ.store.get x.1 (x.2 + 1) = some a.2 →
      μ.store.get xt.1 xt.2 = some aT.1 → μ.store.get xt.1 (xt.2 + 1) = some aT.2 →
      μ.store.get c.1 c.2 = some d → z.2 + 2 ≤ μ.store.len z.1 →
      Wp .total I τ entry (Env.frame [] [x, xt, c, z])
        (fun μ' => μ' = μ.updBlock z [(F a aT d).1, (F a aT d).2]) μ)
    {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K} {A : ℕ → ℕ → K × K} {d : K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A)
    (hc : m.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1) (hl : m.Live [x, c, y]) :
    Writes .total I τ (triangle entry) (Env.frame [n] [x, c, y])
      ((EntryCodec.pair K).rowsFp ⟨y.1, y.2, n, n, n⟩ id)
      (fun m' => m'.store.HoldsRowEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩ id
        (fun i j => F (A i j) (A j i) d) ∧ m'.pos = m.pos) m := by
  refine writes_fillEntryRows (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩ le_rfl id
    (fun _ hj => hj.le) rfl (fun _ => rfl) (fun i j => F (A i j) (A j i) d)
    (fun _ _ => m.pos) rfl (fun _ _ => rfl) ?_
  intro j hj i hi μ hfr hp
  change j < n at hj
  change i < j at hi
  have hfull := (EntryCodec.pair K).regionFp_le_inBlock y.1 y.2 n (n * n)
    (fun i j => j * n + i) id (fun k hk r hr => Idx.add_lt_mul hk (hr.trans hk))
  have hfrY := hfr.mono (((EntryCodec.pair K).regionUpto_le_regionFp y.1 y.2 n
    (fun i j => j * n + i) id hj hi.le).trans hfull)
  have hX' := hfrY.keep (Store.readsOnly_holdsEntries (EntryCodec.pair K)
    ⟨x.1, x.2, n, n, n⟩ A le_rfl) hxy.symm hX
  have hread (r k : ℕ) (hr : r < n) (hk : k < n) (u : Fin 2) :
      μ.store.get x.1 (x.2 + 2 * (k * n + r) + u) =
        some ((EntryCodec.pair K).words (A r k) u) := by
    exact hX' r hr k hk u
  have hc' := hfrY.keep (Store.readsOnly_get c.1 c.2 d) hcy.symm hc
  have hroom : y.2 + 2 * (j * n + i) + 2 ≤ μ.store.len y.1 := by
    rw [hfr.len_eq]
    exact (EntryCodec.pair K).room_entry (L := ⟨y.1, y.2, n, n, n⟩)
      le_rfl (hi.trans hj) hj hY
  have hl' : μ.Live [(x.1, x.2 + 2 * (j * n + i)),
      (x.1, x.2 + 2 * (i * n + j)), c, (y.1, y.2 + 2 * (j * n + i))] := by
    simpa [Mem.Live, hfr.length_eq] using hl
  have hsub (r k : ℕ) (hr : r < n) (hk : k < n) (b off : ℕ) :=
    (EntryCodec.pair K).entryBlock_le_inBlock b off (n * n) (Idx.add_lt_mul hk hr)
  have he := hentry μ (x.1, x.2 + 2 * (j * n + i))
    (x.1, x.2 + 2 * (i * n + j)) c (y.1, y.2 + 2 * (j * n + i))
    (A i j) (A j i) d
    (hxy.mono (hsub i j (hi.trans hj) hj x.1 x.2) (hsub i j (hi.trans hj) hj y.1 y.2))
    (hxy.mono (hsub j i hj (hi.trans hj) x.1 x.2) (hsub i j (hi.trans hj) hj y.1 y.2))
    (hcy.mono le_rfl (hsub i j (hi.trans hj) hj y.1 y.2)) hl'
    (hread i j (hi.trans hj) hj 0) (hread i j (hi.trans hj) hj 1)
    (hread j i hj (hi.trans hj) 0) (hread j i hj (hi.trans hj) 1) hc' hroom
  have hw := pair_writes_of_wp (md := .total) (τ := τ) he hroom
  exact (writes_frame rfl rfl hl' hw).mono le_rfl fun _ _ h => ⟨h.1, h.2.trans hp⟩

omit [Has ScalarOp Op] in
/-- A diagonal entry procedure is lifted to all diagonal positions by the injective-region
rule. Its matrix-level proof supplies no partial-output invariant or component framing.
Shared by the trees of `NLAlib.ShiftedQR.stepComptau`,
`NLAlib.ShiftedQR.RandomDecouplingRoutineContract`, `NLAlib.ShiftedQR.replicatePair` and 16 more. -/
theorem diagonal_writes {I : Interp Op Tst K} {τ : Tape K} (entry : Stmt Op Tst)
    (F : (K × K) → K → K × K)
    (hentry : ∀ (μ : Mem K) (x c z : ℕ × ℕ) (a : K × K) (d : K),
      Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock z.1 z.2 2) →
      Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock z.1 z.2 2) →
      μ.Live [x, c, z] →
      μ.store.get x.1 x.2 = some a.1 → μ.store.get x.1 (x.2 + 1) = some a.2 →
      μ.store.get c.1 c.2 = some d → z.2 + 2 ≤ μ.store.len z.1 →
      Wp .total I τ entry (Env.frame [] [x, c, z])
        (fun μ' => μ' = μ.updBlock z [(F a d).1, (F a d).2]) μ)
    {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K} {A : ℕ → ℕ → K × K} {d : K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A)
    (hc : m.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1) (hl : m.Live [x, c, y]) :
    Writes .total I τ (diagonal entry) (Env.frame [n] [x, c, y])
      ((EntryCodec.pair K).regionFp y.1 y.2 n (fun _ j => j * n + j) (fun _ => 1))
      (fun m' => m'.store.HoldsEntryRegion (EntryCodec.pair K) y.1 y.2 n
        (fun _ j => j * n + j) (fun _ => 1) (fun _ j => F (A j j) d) ∧
        m'.pos = m.pos) m := by
  refine writes_fillEntryRegion (EntryCodec.pair K) y.1 y.2 n
    (fun _ j => j * n + j) (fun _ => 1) ?_ rfl (fun _ => rfl)
    (fun _ j => F (A j j) d) (fun _ _ => m.pos) rfl (fun _ _ => rfl) ?_
  · intro p hp q hq he
    change p.2 < n ∧ p.1 < 1 at hp
    change q.2 < n ∧ q.1 < 1 at hq
    change p.2 * n + p.2 = q.2 * n + q.2 at he
    have hc : p.2 = q.2 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have := Nat.mul_le_mul_right n hlt.le; omega
      · have := Nat.mul_le_mul_right n hgt.le; omega
    exact Prod.ext (by omega) hc
  · intro j hj i hi μ hfr hp
    have hfull := (EntryCodec.pair K).regionFp_le_inBlock y.1 y.2 n (n * n)
      (fun _ j => j * n + j) (fun _ => 1) (fun k hk _ _ => Idx.add_lt_mul hk hk)
    have hfrY := hfr.mono (((EntryCodec.pair K).regionUpto_le_regionFp y.1 y.2 n
      (fun _ j => j * n + j) (fun _ => 1) hj hi.le).trans hfull)
    have hX' := hfrY.keep (Store.readsOnly_holdsEntries (EntryCodec.pair K)
      ⟨x.1, x.2, n, n, n⟩ A le_rfl) hxy.symm hX
    have hread (u : Fin 2) :
        μ.store.get x.1 (x.2 + 2 * (j * n + j) + u) =
          some ((EntryCodec.pair K).words (A j j) u) := by
      exact hX' j hj j hj u
    have hc' := hfrY.keep (Store.readsOnly_get c.1 c.2 d) hcy.symm hc
    have hroom : y.2 + 2 * (j * n + j) + 2 ≤ μ.store.len y.1 := by
      rw [hfr.len_eq]
      exact (EntryCodec.pair K).room_entry (L := ⟨y.1, y.2, n, n, n⟩) le_rfl hj hj hY
    have hl' : μ.Live [(x.1, x.2 + 2 * (j * n + j)), c,
        (y.1, y.2 + 2 * (j * n + j))] := by
      simpa [Mem.Live, hfr.length_eq] using hl
    have hsub (b off : ℕ) := (EntryCodec.pair K).entryBlock_le_inBlock b off (n * n)
      (Idx.add_lt_mul hj hj)
    have he := hentry μ (x.1, x.2 + 2 * (j * n + j)) c
      (y.1, y.2 + 2 * (j * n + j)) (A j j) d
      (hxy.mono (hsub x.1 x.2) (hsub y.1 y.2)) (hcy.mono le_rfl (hsub y.1 y.2))
      hl' (hread 0) (hread 1) hc' hroom
    have hw := pair_writes_of_wp (md := .total) (τ := τ) he hroom
    exact (writes_frame rfl rfl hl' hw).mono le_rfl fun _ _ h => ⟨h.1, h.2.trans hp⟩

omit [Has ScalarOp Op] in
/-- Strict-upper and diagonal procedure specifications compose into one inclusive upper
matrix specification. Region disjointness preserves the strict-upper entries automatically.
Shared by the trees of `NLAlib.Schur.RandomRegularizerContract`,
`NLAlib.Schur.HessenbergReducerContract`, `NLAlib.Schur.TerminatingSchurCore` and 27 more. -/
theorem upper_writes {I : Interp Op Tst K} {τ : Tape K}
    (offDiagonal diagonalEntry : Stmt Op Tst) {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K}
    (U : ℕ → ℕ → K × K) (D : ℕ → K × K)
    {A : ℕ → ℕ → K × K} {d : K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A)
    (hc : m.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1) (hl : m.Live [x, c, y])
    (hu : Writes .total I τ (triangle offDiagonal) (Env.frame [n] [x, c, y])
      ((EntryCodec.pair K).rowsFp ⟨y.1, y.2, n, n, n⟩ id)
      (fun μ => μ.store.HoldsRowEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩ id U ∧
        μ.pos = m.pos) m)
    (hd : ∀ μ,
      μ.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A →
      μ.store.get c.1 c.2 = some d → y.2 + 2 * (n * n) ≤ μ.store.len y.1 →
      μ.Live [x, c, y] →
      Writes .total I τ (diagonal diagonalEntry) (Env.frame [n] [x, c, y])
        ((EntryCodec.pair K).regionFp y.1 y.2 n (fun _ j => j * n + j) (fun _ => 1))
        (fun μ' => μ'.store.HoldsEntryRegion (EntryCodec.pair K) y.1 y.2 n
          (fun _ j => j * n + j) (fun _ => 1) (fun _ j => D j) ∧ μ'.pos = μ.pos) μ) :
    Writes .total I τ (upper offDiagonal diagonalEntry) (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsRowEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (fun j => j + 1) (fun i j => if i = j then D i else U i j) ∧ μ.pos = m.pos) m := by
  have hfull := (EntryCodec.pair K).regionFp_le_inBlock y.1 y.2 n (n * n)
    (fun i j => j * n + i) id (fun k hk r hr => Idx.add_lt_mul hk (hr.trans hk))
  have hdiagFull := (EntryCodec.pair K).regionFp_le_inBlock y.1 y.2 n (n * n)
    (fun _ j => j * n + j) (fun _ => 1) (fun k hk _ _ => Idx.add_lt_mul hk hk)
  refine hu.seq_le hfull fun μ hfr hp => ?_
  have hfrY := hfr.mono hfull
  have hX' := hfrY.keep (Store.readsOnly_holdsEntries (EntryCodec.pair K)
    ⟨x.1, x.2, n, n, n⟩ A le_rfl) hxy.symm hX
  have hc' := hfrY.keep (Store.readsOnly_get c.1 c.2 d) hcy.symm hc
  have hY' : y.2 + 2 * (n * n) ≤ μ.store.len y.1 := by rw [hfr.len_eq]; exact hY
  have hl' : μ.Live [x, c, y] := by simpa [Mem.Live, hfr.length_eq] using hl
  refine ((hd μ hX' hc' hY' hl').keep
    (Store.readsOnly_holdsRowEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩ id U)
    ((EntryCodec.pair K).disj_regionFp_upper_diagonal n y.1 y.2).symm hp.1).mono hdiagFull ?_
  intro μ' _ h
  exact ⟨Store.HoldsRowEntries.of_upper_and_diagonal h.2 h.1.1, h.1.2.trans hp.2⟩

/-- Shifting the upper triangle writes the copied strict-upper words and the machine-rounded
diagonal difference, with zero imaginary diagonal. Disjoint regions of one arena are allowed.
A fragment of the tree `NLAlib.Ops.Hermitian.shift`. -/
theorem shiftUpper_writes {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K} {A : ℕ → ℕ → K × K} {d : K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A)
    (hc : m.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1) (hl : m.Live [x, c, y]) :
    Writes .total I τ (shiftUpper (Op := Op) (Tst := Tst)) (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsRowEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (fun j => j + 1) (fun i j => if i = j then (M.sub (A i i).1 d, M.lit 0) else A i j) ∧
        μ.pos = m.pos) m := by
  have ht := triangle_writes (I := I) (τ := τ) copyEntry (fun a _ _ => a) (by
    intro μ x xt c z a aT d hxz _ _ hl hr hi _ _ _ hz
    exact wp_frame rfl rfl
      (by simpa [Mem.Live] using And.intro (hl x (by simp)) (hl z (by simp)))
      (copyPair_wp_of_disj hI hxz hr hi hz rfl)) hxy hcy hX hc hY hl
  refine upper_writes copyEntry shiftDiagonal (fun i j => A i j)
    (fun i => (M.sub (A i i).1 d, M.lit 0)) hxy hcy hX hc hY hl ht ?_
  intro μ hX' hc' hY' hl'
  exact diagonal_writes shiftDiagonal (fun a d => (M.sub a.1 d, M.lit 0)) (by
    intro μ x c z a d _ _ _ hr _ hc hz
    exact shiftDiagonal_wp hI hr hc hz rfl) hxy hcy hX' hc' hY' hl'

/-- Scaling the upper triangle writes actual rounded quotients and zero imaginary diagonal.
Input/output matrices may share an arena when their word regions are disjoint.
A fragment of the tree `NLAlib.Ops.Hermitian.scale`. -/
theorem scaleUpper_writes {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K} {A : ℕ → ℕ → K × K} {d : K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A)
    (hc : m.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1) (hl : m.Live [x, c, y]) :
    Writes .total I τ (scaleUpper (Op := Op) (Tst := Tst)) (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsRowEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (fun j => j + 1) (fun i j => if i = j then (M.div (A i i).1 d, M.lit 0)
          else (M.div (A i j).1 d, M.div (A i j).2 d)) ∧ μ.pos = m.pos) m := by
  have ht := triangle_writes (I := I) (τ := τ) scaleEntry
    (fun a _ d => (M.div a.1 d, M.div a.2 d)) (by
      intro μ x xt c z a aT d hxz _ hcz hl hr hi _ _ hc hz
      exact wp_frame rfl rfl (by
        simpa [Mem.Live] using ⟨hl x (by simp), hl c (by simp), hl z (by simp)⟩)
        (scalePair_wp hI hxz hcz hr hi hc hz rfl)) hxy hcy hX hc hY hl
  refine upper_writes scaleEntry scaleDiagonal
    (fun i j => (M.div (A i j).1 d, M.div (A i j).2 d))
    (fun i => (M.div (A i i).1 d, M.lit 0)) hxy hcy hX hc hY hl ht ?_
  intro μ hX' hc' hY' hl'
  exact diagonal_writes scaleDiagonal (fun a d => (M.div a.1 d, M.lit 0)) (by
    intro μ x c z a d _ _ _ hr _ hc hz
    exact scaleDiagonal_wp hI hr hc hz rfl) hxy hcy hX' hc' hY' hl'

/-- Hermitian averaging writes the two actual rounded operations per component, with zero
imaginary diagonal. Every transposed input word belongs to the same supplied matrix.
A fragment of the tree `NLAlib.Ops.Hermitian.average`. -/
theorem averageUpper_writes {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {τ : Tape K} {n : ℕ} {x c y : ℕ × ℕ} {m : Mem K} {A : ℕ → ℕ → K × K} {d : K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 (2 * (n * n)))
      (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hcy : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock y.1 y.2 (2 * (n * n))))
    (hX : m.store.HoldsEntries (EntryCodec.pair K) ⟨x.1, x.2, n, n, n⟩ A)
    (hc : m.store.get c.1 c.2 = some d)
    (hY : y.2 + 2 * (n * n) ≤ m.store.len y.1) (hl : m.Live [x, c, y]) :
    Writes .total I τ (averageUpper (Op := Op) (Tst := Tst)) (Env.frame [n] [x, c, y])
      (Store.inBlock y.1 y.2 (2 * (n * n)))
      (fun μ => μ.store.HoldsRowEntries (EntryCodec.pair K) ⟨y.1, y.2, n, n, n⟩
        (fun j => j + 1) (fun i j => if i = j then
          (M.div (M.add (A i i).1 (A i i).1) d, M.lit 0)
          else (M.div (M.add (A i j).1 (A j i).1) d,
            M.div (M.sub (A i j).2 (A j i).2) d)) ∧ μ.pos = m.pos) m := by
  have ht := triangle_writes (I := I) (τ := τ) averagePair
    (fun a b d => (M.div (M.add a.1 b.1) d, M.div (M.sub a.2 b.2) d)) (by
      intro μ x xt c z a aT d hxz htz hcz _ hr hi htr hti hc hz
      exact averagePair_wp hI hxz htz hcz hr hi htr hti hc hz rfl) hxy hcy hX hc hY hl
  refine upper_writes averagePair averageDiagonal
    (fun i j => (M.div (M.add (A i j).1 (A j i).1) d,
      M.div (M.sub (A i j).2 (A j i).2) d))
    (fun i => (M.div (M.add (A i i).1 (A i i).1) d, M.lit 0))
    hxy hcy hX hc hY hl ht ?_
  intro μ hX' hc' hY' hl'
  exact diagonal_writes averageDiagonal (fun a d => (M.div (M.add a.1 a.1) d, M.lit 0)) (by
    intro μ x c z a d _ hcz _ hr _ hc hz
    exact averageDiagonal_wp hI hcz hr hc hz rfl) hxy hcy hX' hc' hY' hl'

end NLAlib.Ops.Hermitian
