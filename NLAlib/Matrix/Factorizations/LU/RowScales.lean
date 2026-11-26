/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.List.GetD
public import NLAlib.Ops.Blas.MaxAbs
public import NLAlib.Ops.Blas.Fill
public import NLAlib.Ops.Blas.Dot
public import NLAlib.Ops.Logic.EntryRow
public import NLAlib.Ops.Logic.VectorUpdate
public import NLAlib.Ops.Catalog.Orth

/-!
# Fixed original row scales

Each scale is the existing finite Pi supremum norm of one decoded original matrix row. The
rectangular initializer uses actual strided scalar maxima, with no index words, products or
divisions. Zero rows and empty column sets receive zero, and empty row sets execute no call.
These fixed scales follow row exchanges during scaled pivoting; they are never recomputed
from the evolving residual.

## Main results

* `NLAlib.LU.rowScales_meets`: actual rectangular row-norm initialization.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- Initialize all row scales and replace each by its actual strided maximum when columns
exist. Disjoint matrix and scale windows may share a buffer. Empty row sets skip every call;
empty column sets write only zero scales and never frame the source handle. -/
def rowScales : Routine Op Tst :=
  routine% [m, n] (A : m * n) → (scales : m) by blocks {
    ifPos m {
      run (fillRoutine (Has.inj (ScalarOp.lit 0))) [m] (scales);
      ifPos n {
        for i < m {
          run maxAbsValue [n, m] (A[i], scales[i])
        }
      }
    }
  }

variable [Inhabited K]

/-- Every actual output word decodes to its original row's Pi supremum norm. No strict
positivity assumption is imposed on any row scale. -/
def rowScalesSpec (dec : K → ℝ) : Routine.Spec K :=
  spec% [m, n] (as) → (ss) ensures
    ∀ i : Fin m, dec (vec ss i.val) = ‖decodeMatrix dec m n as i‖

private def IsRowScalesPrefix (dec : K → ℝ) (m n : ℕ) (as : List K) (covered : ℕ)
    (scales : ℕ × ℕ) (s : Store K) : Prop :=
  ∃ f : ℕ → K, s.HoldsVec scales.1 scales.2 m f ∧ ∀ i : Fin m,
    dec (f i.val) = if i.val < covered then ‖decodeMatrix dec m n as i‖ else 0

private theorem rowScales_initial {M : Machine K} {dec : K → ℝ} {m n : ℕ} {as : List K}
    {scales : ℕ × ℕ} {s : Store K} (hzero : dec (M.lit 0) = 0)
    (h : s.readBlock scales.1 scales.2 m = some (List.replicate m (M.lit 0))) :
    IsRowScalesPrefix dec m n as 0 scales s := by
  refine ⟨fun _ => M.lit 0, ?_, ?_⟩
  · intro i hi
    have hg := Store.get_of_readBlock h hi default
    simpa only [List.getD_replicate (α := K) (x := M.lit 0) (h := hi)] using hg
  · intro i
    simpa only [Nat.not_lt_zero, if_false] using hzero

private theorem rowScales_next {dec : K → ℝ} {m n i : ℕ} {as : List K}
    {scales : ℕ × ℕ} {s s' : Store K} {w : K} (hi : i < m)
    (h : IsRowScalesPrefix dec m n as i scales s)
    (hfr : s.EqOff (Store.inBlock scales.1 (scales.2 + i) 1) s')
    (hw : s'.get scales.1 (scales.2 + i) = some w)
    (hd : dec w = ‖decodeMatrix dec m n as ⟨i, hi⟩‖) :
    IsRowScalesPrefix dec m n as (i + 1) scales s' := by
  obtain ⟨f, hf, hdec⟩ := h
  refine ⟨Function.update f i w, hf.update_of_eqOff hfr hw, ?_⟩
  intro j
  by_cases hji : j.val = i
  · have he : j = ⟨i, hi⟩ := Fin.ext hji
    subst j
    simpa only [Function.update_self, Nat.lt_succ_self, if_true] using hd
  · rw [Function.update_of_ne hji, hdec j]
    have he : (j.val < i + 1) ↔ j.val < i := by omega
    simp only [he]

private theorem rowScales_finish {dec : K → ℝ} {m n : ℕ} {as : List K}
    {scales : ℕ × ℕ} {s : Store K} (h : IsRowScalesPrefix dec m n as m scales s) :
    ∃ ss : List K, s.readBlock scales.1 scales.2 m = some ss ∧
      ∀ i : Fin m, dec (vec ss i.val) = ‖decodeMatrix dec m n as i‖ := by
  obtain ⟨f, hf, hd⟩ := h
  refine ⟨(List.range m).map f, Store.holdsVec_iff_readBlock.mp hf, ?_⟩
  intro i
  rw [Ops.vec_map_range f i.isLt]
  simpa only [if_pos i.isLt] using hd i

omit [Inhabited K] in
private theorem rowScales_source_fp {A : ℕ × ℕ} {m n i : ℕ} (hi : i < m) :
    Fp.inView A.1 (A.2 + i) ⟨1, some (n, m)⟩ ≤ Store.inBlock A.1 A.2 (m * n) := by
  intro b z hz
  obtain ⟨rfl, j, hj, rfl⟩ := Fp.inView_apply.mp hz
  have hj' : j < n := by simpa using hj
  refine ⟨rfl, by simp only [View.offset_runs_one]; omega, ?_⟩
  have he := Nat.add_lt_add_left (Idx.add_lt_mul hj' hi) A.2
  simpa only [View.offset_runs_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.mul_comm] using he

private theorem rowScales_maxAbs_separated {A scales : ℕ × ℕ} {m n i : ℕ} (hi : i < m)
    (hd : Fp.Disj (Store.inBlock scales.1 scales.2 m) (Store.inBlock A.1 A.2 (m * n))) :
    (maxAbsValue (Op := Op) (Tst := Tst)).SeparatedAt [n, m]
      [(A.1, A.2 + i), (scales.1, scales.2 + i)] := by
  apply Routine.separatedAt_of_blocks rfl
  change Fp.ApartViews [(scales.1, scales.2 + i)] [View.block 1] ∧
    Fp.Disj (Fp.views [(scales.1, scales.2 + i)] [View.block 1])
      (Fp.views [(A.1, A.2 + i)] [⟨1, some (n, m)⟩]) ∧ True ∧ Fp.Disj ⊥ _
  refine ⟨by simp [Fp.ApartViews, Fp.views], ?_, trivial, Fp.disj_bot_left _⟩
  simpa only [Fp.views, Fp.inView_block, sup_bot_eq] using
    hd.mono (Fp.inBlock_le_inBlock (by omega) (by omega)) (rowScales_source_fp hi)

/-- The actual row maxima are exact under only exact negation and zero-literal decoding.
No division, multiplication, bounded index-literal model, or positive-scale premise is used. -/
theorem rowScales_meets {M : Machine K} {I : Interp Op Tst K} {dec : K → ℝ}
    (hI : IsScalar M I) (hcmp : IsCmp dec I)
    (hneg : ∀ a, dec (M.neg a) = -dec a) (hzero : dec (M.lit 0) = 0) :
    (rowScales (Op := Op) (Tst := Tst)).Meets I (rowScalesSpec dec) := by
  routine_intro [m, n] (A, scales) reads (as)
  have hdis : Fp.Disj (Store.inBlock scales.1 scales.2 m)
      (Store.inBlock A.1 A.2 (m * n)) := by
    simpa only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] using hblocks.2.1
  refine writes_ifPos rfl ?_
  by_cases hm : 0 < m
  · rw [if_pos hm]
    call (fillRoutine_meets (hI (.lit 0))) [m] (scales)
      as m₁ hfr₁ hpos₁ (ss) hfill
    have he : ss = List.replicate m (M.lit 0) := hfill
    subst ss
    simp only [Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq] at hfr₁
    have hstart := rowScales_initial (n := n) (as := as) hzero hss
    have has₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) hdis has
    refine writes_ifPos rfl ?_
    by_cases hn : 0 < n
    · rw [if_pos hn]
      loop_inv (fun _ => Store.inBlock scales.1 scales.2 m)
        (fun k μ => μ.pos = m₁.pos ∧ IsRowScalesPrefix dec m n as k scales μ.store)
        with i hi m₂ hfr hP
      case round =>
        obtain ⟨hp, hstate⟩ := hP
        have has₂ := hfr.keep (Store.readsOnly_readBlock _ _ _ _) hdis has₁
        have has₂' : m₂.store.readBlock A.1 A.2 (n * m) = some as := by
          simpa only [Nat.mul_comm] using has₂
        have hmat := Store.holdsMat_of_readBlock (L := ⟨A.1, A.2, m, n, m⟩) rfl has₂' 
        have hrow := hmat.readView_row_suffix hi 0
        let words := (List.range n).map fun j => vec as (j * m + i)
        call (maxAbsValue_meets hI hcmp hneg hzero) [n, m]
          ((A.1, A.2 + i), (scales.1, scales.2 + i))
          as m₃ hfr₃ hpos₃ (vs) hvalue
        case' hcall => exact [words]
        case' hr =>
          refine Mem.readViews_of_cons ?_ rfl
          simpa only [Port.view, Port.every, Port.read, Option.map_some, List.getD_cons_zero,
            List.getD_cons_succ, Nat.sub_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add] using hrow
        case' hsep => exact rowScales_maxAbs_separated hi hdis
        obtain ⟨w, hw, rfl⟩ := Store.readBlock_one_eq_some.mp hvs
        have hd : dec w = ‖decodeMatrix dec m n as ⟨i, hi⟩‖ := by
          have he : (fun j : Fin n => dec (vec words j.val)) =
              decodeMatrix dec m n as ⟨i, hi⟩ := by
            funext j
            simp only [words, Ops.vec_map_range _ j.isLt, decodeMatrix_apply]
          change dec w = ‖fun j : Fin n => dec (vec words j.val)‖ at hvalue
          simpa only [he] using hvalue
        refine ⟨hpos₃.trans hp, ?_⟩
        apply rowScales_next hi hstate _ hw hd
        simpa only [Fp.views, Fp.inView_block, sup_bot_eq] using hfr₃
      case exit =>
        rintro m₂ _ ⟨hp, hstate⟩
        obtain ⟨ss, hss, hout⟩ := rowScales_finish hstate
        exact ⟨hp.trans hpos₁, [ss], Mem.readBlocks_of_cons hss rfl, hout⟩
    · rw [if_neg hn]
      have he : n = 0 := by omega
      subst n
      refine ⟨hpos₁, [List.replicate m (M.lit 0)], Mem.readBlocks_of_cons hss rfl, ?_⟩
      intro i
      have hv : vec (List.replicate m (M.lit 0)) i.val = M.lit 0 :=
        List.getD_replicate (α := K) (x := M.lit 0) (h := i.isLt)
      rw [hv, hzero]
      symm
      exact norm_eq_zero.mpr (funext fun j => Fin.elim0 j)
  · rw [if_neg hm]
    have he : m = 0 := by omega
    subst m
    exact ⟨rfl, [[]], Mem.readBlocks_of_cons (Store.readBlock_zero _ _ _) rfl,
      fun i => Fin.elim0 i⟩

end NLAlib.LU
