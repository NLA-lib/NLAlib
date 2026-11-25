/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.SchurMixed
public import NLAlib.Matrix.Factorizations.LU.Schur
public import NLAlib.Ops.Blas.Guarded

/-!
# Saved-pivot elimination under rejecting arithmetic

The existing scalar trees succeed from local acceptance of the exact primitive targets.
Their outputs, scoped scratch and memory frames are those of the ordinary word judgments.
Numerical input bounds establish these local conditions before the routines are called.

## Main results

* `NLAlib.LU.schurStep_meets_guarded`: guarded success of the actual Schur tree.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Inhabited K]

/-- Acceptance of the coefficient product and the subsequent multiply-add targets. -/
def schurColumnGuardedSpec (M : Machine K) (dec : K → ℝ) (safe : ℝ → Prop) :
    Routine.Spec K :=
  spec% [n] ([a], xs, [b], zs) → (ws) requires
    (safe (dec a * dec b) ∧
      (∀ i < n, safe (dec (M.mul a b) * dec (vec xs i))) ∧
      ∀ i < n, safe (dec (vec zs i) + dec (M.mul (M.mul a b) (vec xs i)))) ensures
    ws = axpyF M (M.mul a b) (vec xs) (vec zs) n

/-- The actual saved-pivot column succeeds under the stated local primitive contracts. -/
theorem schurColumn_meets_guarded {M : Machine K} {dec : K → ℝ} {safe : ℝ → Prop}
    {I : Interp Op Tst K} (hI : IsGuardedScalar M dec safe I) :
    (schurColumn (Op := Op) (Tst := Tst)).Meets I (schurColumnGuardedSpec M dec safe) := by
  classical
  routine_intro [n] (a, x, y, z) reads (as, xs, ys, zs)
  obtain ⟨av, ha, rfl⟩ := Store.readBlock_one_eq_some.mp has
  obtain ⟨bv, hb, rfl⟩ := Store.readBlock_one_eq_some.mp hys
  obtain ⟨hla, hlx, hly, hlz⟩ := hl
  change Writes .total I τ _ (Env.frame [n] [a, x, y, z, z]) (Fp.blocks [z] [n]) _ m
  alloc as t
  have htz : t ≠ z.1 := by
    change m.store.length ≠ z.1
    exact Nat.ne_of_gt hlz
  step (hI .mul) [Machine.guardedFn, hpre.1] as m₁ hfr₁ ⟨hpos₁, v, hv, he⟩
  change ((if safe (dec av * dec bv) then some (M.mul av bv) else none).map
    (fun w => [[w]])) = some [[v]] at he
  rw [if_pos hpre.1] at he
  simp only [Option.map_some, Option.some.injEq, List.cons.injEq, and_true] at he
  subst v
  call (axpyLoopRoutine_meets_guarded hI) [n] ((t, 0), x, z)
    (pre := hpre.2)
    as m₂ hfr₂ hpos₂ (ws) hpost
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change m.store.length < m₁.store.length ∧ x.1 < m₁.store.length ∧ z.1 < m₁.store.length
    simp only [List.length_singleton] at hlen_t
    exact ⟨by omega, by omega, by omega⟩
  change m₁.pos = m.pos + 0 at hpos₁
  intro s₂ hs₂ hB₂
  refine ⟨?_, [ws], Mem.readBlocks_of_cons ?_ rfl, hpost⟩
  · change m₂.pos = m.pos + 0
    omega
  · exact Store.Below.readBlock_of hB₂ hlz hws

/-- Acceptance of all row products and multiply-add targets of a matrix update. -/
def rankOneGuardedSpec (M : Machine K) (dec : K → ℝ) (safe : ℝ → Prop) : Routine.Spec K :=
  spec% [rows, cols] ([a], xs, ys, As) → (Bs) requires
    (∀ j < cols, safe (dec a * dec (vec ys j)) ∧
      (∀ i < rows, safe (dec (M.mul a (vec ys j)) * dec (vec xs i))) ∧
      ∀ i < rows, safe (dec (vec As (j * rows + i)) +
        dec (M.mul (M.mul a (vec ys j)) (vec xs i)))) ensures
    Bs = (EntryCodec.scalar K).packMatrix rows cols
      (rankOneValues M a (vec xs) (vec ys) (fun i j => vec As (j * rows + i)))

/-- The scalar rank-one routine meets its functional word specification on every machine,
including empty matrix dimensions. Only the matrix is changed, and no tape is consumed. -/
theorem rankOne_meets_guarded {M : Machine K} {dec : K → ℝ} {safe : ℝ → Prop}
    {I : Interp Op Tst K} (hI : IsGuardedScalar M dec safe I) :
    (rankOne (Op := Op) (Tst := Tst)).Meets I (rankOneGuardedSpec M dec safe) := by
  routine_intro [rows, cols] (a, x, y, A) reads (as, xs, ys, As)
  obtain ⟨av, ha, rfl⟩ := Store.readBlock_one_eq_some.mp has
  let C := EntryCodec.scalar K
  let L : MatLayout := ⟨A.1, A.2, rows, cols, rows⟩
  let old := fun i j => vec As (j * rows + i)
  let new := rankOneValues M av (vec xs) (vec ys) old
  have hAs' : m.store.readBlock A.1 A.2 (cols * rows) = some As := by
    simpa only [Nat.mul_comm] using hAs
  have hstart : m.store.HoldsEntries C L old := by
    simpa only [C, L, EntryCodec.scalar_entry, Nat.mul_one] using
      (Store.holdsEntries_of_readBlock (C := C) (L := L) rfl
        (by simpa only [C, L, Nat.mul_one] using hAs'))
  loop_inv (fun _ => Fp.blocks [A] [rows * cols])
    (fun j m' => m'.pos = m.pos ∧ m'.store.HoldsEntries C L
      (fun i c => if c < j then new i c else old i c))
    with j hj m₁ hfr hP
  case round =>
    obtain ⟨hp, hmatrix⟩ := hP
    have ha₁ : m₁.store.readBlock a.1 a.2 1 = some [av] := by keep
    have hx₁ : m₁.store.readBlock x.1 x.2 rows = some xs := by keep
    have hy₁ : m₁.store.readBlock y.1 y.2 cols = some ys := by keep
    have hyj := Store.readBlock_one_of_get (Store.get_of_readBlock hy₁ hj default)
    have hcol : m₁.store.readBlock A.1 (A.2 + j * rows) rows =
        some (C.pack rows fun i => old i j) := by
      simpa only [C, L, Nat.one_mul, Nat.mul_one, if_neg (Nat.lt_irrefl j)] using
        hmatrix.readBlock_column hj
    have hcolroom : A.2 + j * rows + rows ≤ m₁.store.len A.1 := by
      rw [hfr.len_eq]
      have hm := Nat.mul_le_mul_right rows (Nat.succ_le_of_lt hj)
      rw [Nat.succ_mul] at hm
      nlinarith [hroom]
    call (schurColumn_meets_guarded hI) [rows] (a, x, (y.1, y.2 + j), (A.1, A.2 + j * rows))
      as m₂ hfr₂ hpos₂ (bs) hpost
    case' hpre =>
      obtain ⟨hrow, hprod, hadd⟩ := hpre j hj
      change safe (dec av * dec (vec ys j)) ∧
        (∀ i < rows, safe (dec (M.mul av (vec ys j)) * dec (vec xs i))) ∧
        ∀ i < rows, safe (dec (vec (C.pack rows (fun i => old i j)) i) +
          dec (M.mul (M.mul av (vec ys j)) (vec xs i)))
      refine ⟨hrow, hprod, fun i hi => ?_⟩
      simpa [C, old, EntryCodec.scalar_pack, vec, List.getD_eq_getElem?_getD,
        List.getElem?_ofFn, hi] using hadd i hi
    case' hle =>
      routine_nf
      simp only [Fp.blocks, sup_bot_eq]
      simpa only [L, Fp.blocks, sup_bot_eq, Nat.mul_comm] using
        (L.col_fp hj).trans (MatLayout.fp_le_inBlock le_rfl)
    have hwords : bs = C.pack rows (fun i => new i j) := by
      rw [hpost]
      exact axpyF_column M (M.mul av (vec ys j)) (vec xs) old rows j
    have hnew := hmatrix.update_column_of_frame (hL := le_rfl) (j := j) (F := ⊥)
      (by simp) (by simpa only [C, L, Fp.blocks, Nat.one_mul, Nat.mul_one,
        sup_bot_eq] using hfr₂)
      (fun i => new i j) (by simpa only [C, L, Nat.one_mul, Nat.mul_one, hwords] using hbs)
    refine ⟨hpos₂.trans hp, fun i hi c hc z => ?_⟩
    have hh := hnew i hi c hc z
    by_cases hcj : c = j
    · subst c
      simpa only [if_pos rfl, ite_true, if_pos (Nat.lt_succ_self j)] using hh
    · by_cases hlt : c < j
      · simpa only [if_neg hcj, if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)] using hh
      · simpa only [if_neg hcj, if_neg hlt, if_neg (show ¬c < j + 1 by omega)] using hh
  case exit =>
    rintro m₁ _ ⟨hp, hmatrix⟩
    have hm : m₁.store.HoldsEntries C L new := by
      intro i hi c hc z
      have hc' : c < cols := hc
      simpa only [if_pos hc'] using hmatrix i hi c hc z
    refine ⟨hp, [C.packMatrix rows cols new], Mem.readBlocks_of_cons ?_ rfl, rfl⟩
    simpa only [C, L, Nat.mul_one, Nat.mul_comm] using hm.readBlock rfl

/-- Local acceptance conditions for all scalar operations of saved-pivot elimination. -/
def schurStepGuardedSpec (M : Machine K) (dec : K → ℝ) (safe : ℝ → Prop) : Routine.Spec K :=
  spec% [n, k] (As) → (Bs) requires
    (k < n ∧ IsSchurSafe M dec safe (fun i j => vec As (j * n + i)) n k) ensures
    Bs = (EntryCodec.scalar K).packMatrix n n
      (schurValues M (fun i j => vec As (j * n + i)) k)

/-- The full scalar routine writes the stated Schur words and retains every other buffer,
the original buffer shapes and the tape position. Its proof derives the actual run from
scalar contracts, without assuming it succeeds. -/
theorem schurStep_meets_guarded {M : Machine K} {dec : K → ℝ} {safe : ℝ → Prop}
    {I : Interp Op Tst K} (hI : IsGuardedScalar M dec safe I) :
    (schurStep (Op := Op) (Tst := Tst)).Meets I (schurStepGuardedSpec M dec safe) := by
  classical
  routine_intro [n, k] (A) reads (As)
  change Writes .total I τ _ (Env.frame [n, k] [A, A]) (Fp.blocks [A] [n * n]) _ m
  alloc as c r a
  have hAc : A.1 ≠ c := by change A.1 ≠ m.store.length + 0; omega
  have hAr : A.1 ≠ r := by change A.1 ≠ m.store.length + 1; omega
  have hAa : A.1 ≠ a := by change A.1 ≠ m.store.length + 2; omega
  have hcr : c ≠ r := by change m.store.length + 0 ≠ m.store.length + 1; omega
  have hca : c ≠ a := by change m.store.length + 0 ≠ m.store.length + 2; omega
  have hra : r ≠ a := by change m.store.length + 1 ≠ m.store.length + 2; omega
  have hAs₀ := Store.Below.readBlock_of hbelow_c hl hAs
  call (pivotSaved_meets_of_isFn (hI .copy)) [n, k] (A, (c, 0), (r, 0)) (pre := hpre.1)
    as m₁ hfr₁ hpos₁ (cs, rs) hsaved
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change A.1 < s_c.length ∧ m.store.length < s_c.length ∧ m.store.length + 1 < s_c.length
    simp only [List.length_cons, List.length_nil] at hlen_c
    exact ⟨by omega, by omega, by omega⟩
  case' hroom =>
    change (0 + n ≤ s_c.len c) ∧ (0 + n ≤ s_c.len r) ∧ True
    exact ⟨by simpa only [Nat.zero_add] using hc.ge,
      by simpa only [Nat.zero_add] using hr_1.ge, trivial⟩
  obtain ⟨rfl, rfl⟩ := hsaved
  have hAs₁ : m₁.store.readBlock A.1 A.2 (n * n) = some As := by keep
  have hlitfn : M.guardedFn dec safe (.lit (-1)) = BlockFn.const (M.lit (-1)) := by
    have hacc : safe (-1) := hpre.2.literal
    simp only [Machine.guardedFn, Machine.fn, Rat.cast_neg, Rat.cast_one, if_pos hacc]
  have hconst : I.IsFn .total (Has.inj (ScalarOp.lit (-1))) (.const (M.lit (-1)))
      AnyOperands := by simpa only [hlitfn] using hI (.lit (-1))
  step hconst as m₂ hfr₂ ⟨hpos₂, v, hv, rfl⟩
  change Store.EqOff (Store.inBlock a 0 1) m₁.store m₂.store at hfr₂
  have hcs₂ : m₂.store.readBlock c 0 n = some (pivotColumnWords As n k) := by keep
  have hrs₂ : m₂.store.readBlock r 0 n = some (pivotRowWords As n k) := by keep
  have hAs₂ : m₂.store.readBlock A.1 A.2 (n * n) = some As := by keep
  have hpivot := Store.get_of_readBlock hAs₂ (Idx.add_lt_mul hpre.1 hpre.1) default
  have hpivot' : m₂.store.get A.1 (A.2 + k * n + k) = some (vec As (k * n + k)) := by
    simpa only [Nat.add_assoc] using hpivot
  have hguard := And.intro hpre.2.pivot_ne hpre.2.coefficient
  step (hI .div) [Machine.guardedFn] as m₃ hfr₃ ⟨hpos₃, q, hq, he⟩
  case' hdom =>
    exact ⟨[[M.div (M.lit (-1)) (vec As (k * n + k))]],
      by simpa [Machine.guardedFn, BlockFn.bin] using hguard, rfl⟩
  change ((if dec (vec As (k * n + k)) ≠ 0 ∧
    safe (dec (M.lit (-1)) / dec (vec As (k * n + k))) then
      some (M.div (M.lit (-1)) (vec As (k * n + k))) else none).map
        (fun w => [[w]])) = some [[q]] at he
  rw [if_pos hguard] at he
  simp only [Option.map_some, Option.some.injEq, List.cons.injEq, and_true] at he
  subst q
  change m₃.pos = m₂.pos + 0 at hpos₃
  change Store.EqOff (Store.inBlock a 0 1) m₂.store m₃.store at hfr₃
  have hcs₃ : m₃.store.readBlock c 0 n = some (pivotColumnWords As n k) := by keep
  have hrs₃ : m₃.store.readBlock r 0 n = some (pivotRowWords As n k) := by keep
  have hAs₃ : m₃.store.readBlock A.1 A.2 (n * n) = some As := by keep
  call (rankOne_meets_guarded hI) [n, n] ((a, 0), (c, 0), (r, 0), A)
    (pre := by
      intro j hj
      simp only [pivotColumnWords, pivotRowWords, vec_map_range _ hj]
      refine ⟨hpre.2.row j hj, ?_, ?_⟩
      · intro i hi
        simpa only [vec_map_range _ hi] using hpre.2.product i hi j hj
      · intro i hi
        simpa only [vec_map_range _ hi] using hpre.2.add i hi j hj)
    as m₄ hfr₄ hpos₄ (Bs) hpost
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change m.store.length + 2 < m₃.store.length ∧ m.store.length < m₃.store.length ∧
      m.store.length + 1 < m₃.store.length ∧ A.1 < m₃.store.length
    simp only [List.length_cons, List.length_nil] at hlen_c
    exact ⟨by omega, by omega, by omega, by omega⟩
  intro s₂ hs₂ hB₂
  refine ⟨?_, [Bs], Mem.readBlocks_of_cons ?_ rfl, ?_⟩
  · change m₄.pos = m.pos + 0
    omega
  · exact Store.Below.readBlock_of hB₂ hl hBs
  · rw [hpost]
    exact rankOne_savedWords M As n k

end NLAlib.LU
