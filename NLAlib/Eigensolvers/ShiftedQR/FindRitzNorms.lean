/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.FindRitzRegisters

/-!
# The two actual half norms of a Ritz search window

The total half-norm routine may report singularity. In this search phase its caller has
already excluded every singular candidate mathematically, so both reports are clear and their
actual numeric outputs are the two squared norms. The three natural indices are retained.

## Main results

* `NLAlib.ShiftedQR.halfNormAtRegister_writes`: one computed norm and retained search words.
* `NLAlib.ShiftedQR.findRitzNorms_writes`: both actual window norms.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

private theorem halfNormResult_exact {n : ℕ} {z f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ} {a h e : ℕ} {s : Store ℝ}
    (hresult : HalfNormResult z f H (halfSegment shifts a h) e s)
    (hdet : ∀ shift ∈ shifts, (H - shift • 1).det ≠ 0) :
    s.get z.1 z.2 = some (halfNormSq H shifts a h e) := by
  rcases hresult with ⟨_, _, shift, hmem, heq⟩ | ⟨_, hnorm⟩
  · exact (hdet shift (List.mem_of_mem_drop (List.mem_of_mem_take hmem)) heq).elim
  · exact hnorm

variable {Op Tst : Type} [Has ScalarOp Op] [Has CmpTst Tst]

/-- A total half-norm call gives its exact numeric branch under the caller's mathematical
nonsingularity condition. It preserves the source blocks and three index words. -/
theorem halfNormAtRegister_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k a h e start size exponent j : ℕ} {b ss r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store)
    (hwords : SearchWords r start size exponent m.store)
    (hdet : ∀ shift ∈ shifts, (H - shift • 1).det ≠ 0)
    (hak : a + h ≤ k) (hal : a + h ≤ shifts.length) (hj : j = 3 ∨ j = 4)
    (hra : r.1 ≠ b.1) (hrs : r.1 ≠ ss.1) (hl : m.Live [b, ss, r, r])
    (hr : r.2 + 6 ≤ m.store.len r.1) :
    Writes .total I τ halfNorm.body
      (Env.frame [n + 1, k, a, h, e] [b, ss, (r.1, r.2 + j), (r.1, r.2 + 5)])
      (Store.inBlock r.1 (r.2 + j) 1 ⊔ Store.inBlock r.1 (r.2 + 5) 1)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix b H m'.store ∧
        HoldsShifts (k := k) ss shifts m'.store ∧ SearchWords r start size exponent m'.store ∧
        m'.store.get r.1 (r.2 + j) = some (halfNormSq H shifts a h e)) m := by
  have hj' : 3 ≤ j ∧ j + 1 ≤ 5 := by rcases hj with rfl | rfl <;> omega
  have hl' : m.Live [b, ss, (r.1, r.2 + j), (r.1, r.2 + 5)] := by
    simpa [Mem.Live] using hl
  have hw := halfNorm_writes hS hE hCmp (τ := τ) (a := a) (h := h) (e := e)
    hH hB hSS hak hal hl' (Fp.disj_inBlock_of_ne hra) (Fp.disj_inBlock_of_ne hrs)
    (Fp.disj_inBlock_of_le (by omega))
    (by change r.2 + j + 1 ≤ m.store.len r.1; omega)
    (by change r.2 + 5 + 1 ≤ m.store.len r.1; omega)
  refine hw.mono le_rfl ?_
  intro m' hfr ⟨hp, hresult⟩
  refine ⟨hp, hB.of_eqOff hfr
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne hra, Fp.disj_inBlock_of_ne hra⟩),
    hfr.keep (readsOnly_holdsVector ss (fun i : Fin k => shifts.getD i 0))
      (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne hrs, Fp.disj_inBlock_of_ne hrs⟩) hSS,
    hfr.keep (readsOnly_searchWords r start size exponent)
      (Fp.disj_sup_left.mpr ⟨(Fp.disj_inBlock_of_le (by omega)).symm,
        (Fp.disj_inBlock_of_le (by omega)).symm⟩) hwords,
    halfNormResult_exact hresult hdet⟩

/-- Both actual half-norm calls retain the source blocks and search indices and store the
same two squared norms compared by the mathematical search. -/
theorem findRitzNorms_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hCmp : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {n k a h e : ℕ} {b ss r : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {shifts : List ℂ}
    (hH : IsUpperHessenberg H) (hB : HoldsMatrix b H m.store)
    (hSS : HoldsShifts (k := k) ss shifts m.store) (hwords : SearchWords r a h e m.store)
    (hdet : ∀ shift ∈ shifts, (H - shift • 1).det ≠ 0)
    (hak : a + 2 * h ≤ k) (hal : a + 2 * h ≤ shifts.length)
    (hra : r.1 ≠ b.1) (hrs : r.1 ≠ ss.1) (hl : m.Live [b, ss, r, r])
    (hr : r.2 + 6 ≤ m.store.len r.1) :
    Writes .total I τ findRitzNorms.body (Env.frame [n + 1, k, a, h, e] [b, ss, r, r])
      (Store.inBlock r.1 r.2 6)
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix b H m'.store ∧
        HoldsShifts (k := k) ss shifts m'.store ∧ SearchWords r a h e m'.store ∧
        m'.store.get r.1 (r.2 + 3) = some (halfNormSq H shifts a h e) ∧
        m'.store.get r.1 (r.2 + 4) = some (halfNormSq H shifts (a + h) h e)) m := by
  have hw := halfNormAtRegister_writes hS hE hCmp (τ := τ) (j := 3)
    (a := a) (h := h) (e := e) hH hB hSS hwords hdet (by omega) (by omega)
    (Or.inl rfl) hra hrs hl hr
  have hlLeft : m.Live [b, ss, (r.1, r.2 + 3), (r.1, r.2 + 5)] := by
    simpa [Mem.Live] using hl
  change Writes .total I τ (.seq _ _) _ _ _ m
  refine Writes.seq_le (hw.in_frame rfl rfl hlLeft) (by fp_sub)
    fun m' hfr ⟨hp, hB', hSS', hwords', hleft⟩ => ?_
  have hn := halfNormAtRegister_writes hS hE hCmp (τ := τ) (j := 4)
    (a := a + h) (h := h) (e := e) hH hB' hSS' hwords' hdet (by omega) (by omega)
    (Or.inr rfl) hra hrs (hl.congr hfr.length_eq) (by rw [hfr.len_eq]; exact hr)
  have hlRight : m'.Live [b, ss, (r.1, r.2 + 4), (r.1, r.2 + 5)] := by
    simpa [Mem.Live] using hl.congr hfr.length_eq
  refine (hn.in_frame rfl rfl hlRight).mono (by fp_sub) ?_
  intro m'' hfr' ⟨hp', hB'', hSS'', hwords'', hright⟩
  exact ⟨hp'.trans hp, hB'', hSS'', hwords'',
    hfr'.keep (Store.readsOnly_get _ _ _)
      (Fp.disj_sup_left.mpr ⟨(Fp.disj_inBlock_of_le (by omega)).symm,
        (Fp.disj_inBlock_of_le (by omega)).symm⟩) hleft, hright⟩

end NLAlib.ShiftedQR
