/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.FindRitzLoop
public import NLAlib.Eigensolvers.ShiftedQR.FindRitzCopy

/-!
# Exact correctness of the scalar Ritz binary search

The actual scalar implementation initializes its natural index words, performs every bounded
search level, then copies the selected stored candidate. Its numerical theorem assumes the
mathematical nonsingularity of the supplied shifts. The enclosing strategy derives this fact
from its earlier failed acceptance trials, using the existing eigenvalue-shift acceptance result.

## Main results

* `NLAlib.ShiftedQR.findRitzSearchWithScratch_writes`: the actual caller-scratch search.
* `NLAlib.ShiftedQR.findRitzSearch_writes`: scoped scalar search equals `findRitz` exactly.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
  [Has CmpTst Tst] [Has IdxTst Tst]

/-- Actual initialization, bounded-index levels and final copies return the mathematical
binary search result. The supplied determinant condition is mathematical and local to this
search phase. [BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem findRitzSearchWithScratch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    (hL : IsIndexLit M I) (hToNat : IsToNat id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n levels k : ℕ} {b ss r z : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store) (hlen : shifts.length = k)
    (hk : k = 2 ^ levels) (hdet : ∀ shift ∈ shifts, (H - shift • 1).det ≠ 0)
    (hra : r.1 ≠ b.1) (hrs : r.1 ≠ ss.1) (hr : r.2 + 6 ≤ m.store.len r.1)
    (hsep : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * k)) (Store.inBlock z.1 z.2 2))
    (hz : z.2 + 2 ≤ m.store.len z.1) :
    Writes .total I τ findRitzSearchWithScratch.body (Env.frame [n + 1, levels, k] [b, ss, r, z])
      (Store.inBlock r.1 r.2 6 ⊔ Store.inBlock z.1 z.2 2)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 2 =
        some [(findRitz H levels 1 shifts).re, (findRitz H levels 1 shifts).im]) m := by
  have hkpos : 0 < k := by rw [hk]; exact pow_pos (by omega : 0 < 2) levels
  have hbl := Store.lt_length_of_get (hB.get_re (0 : Fin (n + 1)) 0)
  have hsl := Store.lt_length_of_get (HoldsVector.get_re hSS (⟨0, hkpos⟩ : Fin k))
  have hrl : r.1 < m.store.length := Store.lt_length_of_lt_len (by omega : r.2 < _)
  have hzl : z.1 < m.store.length := Store.lt_length_of_lt_len (by omega : z.2 < _)
  have hlInit : m.Live [r, r] := by simpa [Mem.Live] using hrl
  have hlLevels : m.Live [b, ss, r, r] := by simp [Mem.Live, hbl, hsl, hrl]
  have hlCopy : m.Live [ss, r, z] := by simp [Mem.Live, hsl, hrl, hzl]
  have hw := findRitzInitialize_writes hL hE (τ := τ) (m := m) (k := k) (r := r)
    (by omega : r.2 + 3 ≤ _)
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hw.in_frame rfl rfl hlInit) (by fp_sub)
    fun m' hfr ⟨hp, hwords⟩ => ?_
  have hB' := hB.of_eqOff hfr (Fp.disj_inBlock_of_ne hra)
  have hSS' := hfr.keep (readsOnly_holdsVector ss (fun i : Fin k => shifts.getD i 0))
    (Fp.disj_inBlock_of_ne hrs) hSS
  have hlp := findRitzLevels_writes hS hE hL hCmp hToNat (τ := τ)
    hH hB' hSS' hlen hk hwords hdet hra hrs (hlLevels.congr hfr.length_eq)
    (by rw [hfr.len_eq]; exact hr)
  refine Writes.seq_le (hlp.in_frame rfl rfl (hlLevels.congr hfr.length_eq)) (by fp_sub)
    fun m'' hfr' ⟨hp', _, hSS'', hwords'⟩ => ?_
  have hlast := searchStart_last H shifts levels (hlen.trans hk)
  have ha : searchStart H shifts levels levels < k := by rw [← hlen]; exact hlast.1
  have hc := findRitzCopy_writes hS hToNat (τ := τ) hSS'' hwords'.1 ha hsep
    (by rw [hfr'.len_eq, hfr.len_eq]; exact hz)
  refine (hc.in_frame rfl rfl
    (hlCopy.congr (hfr'.length_eq.trans hfr.length_eq))).mono le_sup_right ?_
  intro m''' _ ⟨hp'', hread⟩
  exact ⟨hp''.trans (hp'.trans hp), by simpa only [hlast.2] using hread⟩

/-- The complete scoped implementation returns exactly the mathematical Ritz binary search
on the actual supplied shift list. All numerical steps are explicit scalar programs; the
standard index and comparison models govern the actual bounded index reads.
[BanksGarzaVargasSrivastava2021, §4.3]. -/
theorem findRitzSearch_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    (hL : IsIndexLit M I) (hToNat : IsToNat id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n levels k : ℕ} {b ss z : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store) (hlen : shifts.length = k)
    (hk : k = 2 ^ levels) (hdet : ∀ shift ∈ shifts, (H - shift • 1).det ≠ 0)
    (hsep : Fp.Disj (Store.inBlock ss.1 ss.2 (2 * k)) (Store.inBlock z.1 z.2 2))
    (hz : z.2 + 2 ≤ m.store.len z.1) :
    Writes .total I τ findRitzSearch.body (Env.frame [n + 1, levels, k] [b, ss, z])
      (Store.inBlock z.1 z.2 2)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 2 =
        some [(findRitz H levels 1 shifts).re, (findRitz H levels 1 shifts).im]) m := by
  have hkpos : 0 < k := by rw [hk]; exact pow_pos (by omega : 0 < 2) levels
  have hbl := Store.lt_length_of_get (hB.get_re (0 : Fin (n + 1)) 0)
  have hsl := Store.lt_length_of_get (HoldsVector.get_re hSS (⟨0, hkpos⟩ : Fin k))
  have hzl : z.1 < m.store.length := Store.lt_length_of_lt_len (by omega : z.2 < _)
  apply writes_allocs_readBlock (lens := [.const 6]) (ns := [6]) rfl hzl
  intro store hlen' hlens hBelow
  have hlength : store.length = m.store.length + 1 := by simpa using hlen'
  let r : ℕ × ℕ := (m.store.length, 0)
  let m₁ : Mem ℝ := ⟨store, m.pos⟩
  have hr : r.2 + 6 ≤ store.len r.1 := by simpa [r] using (hlens 0 (by simp)).ge
  have hl : m₁.Live [b, ss, r, z] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx <;> subst x
    all_goals change _ < store.length
    all_goals try dsimp only [r, Prod.fst]
    all_goals omega
  have hw := findRitzSearchWithScratch_writes hS hE hCmp hL hToNat (τ := τ) (m := m₁)
    hH (hB.of_below hBelow hbl) (hSS.of_below hBelow hsl) hlen hk hdet
    (by dsimp [r]; omega) (by dsimp [r]; omega) hr hsep
    (by change z.2 + 2 ≤ store.len z.1; rw [(hBelow z.1 hzl).1]; exact hz)
  exact (hw.in_frame rfl rfl hl).mono (by fp_sub [r]) (fun _ _ h => h)

end NLAlib.ShiftedQR
