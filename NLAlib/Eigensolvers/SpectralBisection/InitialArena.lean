/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.SolveLayout
public import NLAlib.Eigensolvers.SpectralBisection.InitialLevel
public import NLAlib.Ops.Logic.BlockPartition

/-!
# Initialization on complete solver arenas

The ordinary initialization read tuple represents the mathematical root level and leaves all
future size slots zero. The parameter input remains available to every downward level.

## Main results

* `NLAlib.SpectralBisection.writes_initializeArenas_stored`: actual initialized mathematical data.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

private theorem initializeFp_le_arenas {n L : ℕ}
    (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ) :
    Fp.blocks [c, sz, ma, lv] [5, n * (L + 2) + 1, 2 * (n * n), 2] ≤
      Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L) := by
  let source := [c, sz, ma, lv]
  let lengths := [5, n * (L + 2) + 1, 2 * (n * n), 2]
  let parent : Fin 4 → Fin 11 := ![0, 5, 1, 8]
  have hm := Nat.le_mul_of_pos_right (2 * (n * n)) (show 0 < L + 2 by omega)
  have hv (i : Fin 4) :
      Store.inBlock (source.getD i (0, 0)).1 (source.getD i (0, 0)).2 (lengths.getD i 0) ≤
      Store.inBlock
        ((arenaOperands c ma ua qa ea sz kd kp lv su sg).getD (parent i) (0, 0)).1
        ((arenaOperands c ma ua qa ea sz kd kp lv su sg).getD (parent i) (0, 0)).2
        ((arenaLengths n L).getD (parent i) 0) := by
    fin_cases i <;> apply Fp.inBlock_le_inBlock <;>
      simp [source, lengths, parent, arenaOperands, arenaLengths]; omega
  apply Fp.blocks_le_of_forall_getD
  intro i hi
  have hi' : i < 4 := by simpa using hi
  exact (hv ⟨i, hi'⟩).trans (Fp.inBlock_getD_le_blocks
    (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)
    (i := parent ⟨i, hi'⟩) (by simp [arenaOperands, arenaLengths]))

/-- Actual initialization stores the mathematical root, future zeros and shared constants.
Its input parameter block is retained and its write frame stays inside the eleven arenas. -/
theorem writes_initializeArenas_stored {K Op Tst : Type} [Inhabited K]
    [Has ScalarOp Op] [Has IndexOp Op] (M : Machine K) (F : FloatMachine K ℕ ℕ)
    (fuel : ℕ) (R0 eps beta : K) {n L : ℕ}
    (A : Matrix (Fin n) (Fin n) (K × K)) {I : Interp Op Tst K}
    (hS : IsScalar M I) (hIndex : IsIndexLit M I) {τ : Tape K} {μ : Mem K}
    {a par c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ}
    (hl : μ.Live [a, par, c, ma, sz, lv])
    (hRoom : μ.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hSource : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock par.1 par.2 3))
    (hProtect : Fp.Disj (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg)
      (arenaLengths n L)) (Fp.blocks [a, par] [2 * (n * n), 3]))
    (hA : μ.store.readBlock a.1 a.2 (2 * (n * n)) = some ((EntryCodec.pair K).packFinMatrix A))
    (hPar : μ.store.readBlock par.1 par.2 3 = some [R0, eps, beta]) :
    Writes .total I τ initializeArenas.body (Env.frame [n, L] [a, par, c, ma, sz, lv])
      (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
      (fun ν => ν.pos = μ.pos ∧ ν.store.readBlock par.1 par.2 3 = some [R0, eps, beta] ∧
        ν.store.readBlock c.1 c.2 5 =
          some [M.lit 1, M.lit 2, M.div (M.lit 1) (M.lit 2), M.neg (M.lit 1), M.sqrtHalf] ∧
        StoresLevel M F n fuel R0 beta ⟨n, A, R0, eps, L⟩ 0 ma sz lv ν ∧
        ∀ e, 1 ≤ e → e ≤ L + 1 → ∀ lo < n,
          ν.store.get sz.1 (sz.2 + n * e + lo) = some (M.lit 0)) μ := by
  have hCaps := room_initialize_of_arenas hRoom
  simp only [Mem.Room, and_true] at hCaps
  have hPar2 : μ.store.readBlock par.1 par.2 2 = some [R0, eps] := by
    simpa using Store.readBlock_sub hPar (o := 0) (n := 2) (by omega)
  have hW := writes_initializeArenas (τ := τ) hS hIndex ((EntryCodec.pair K).packFinMatrix A)
    R0 eps hl (apart_initialize_of_arenas hAP hSource hProtect) hA hPar2
    hCaps.1 hCaps.2.1 hCaps.2.2.1 hCaps.2.2.2
  have hSub := initializeFp_le_arenas (n := n) (L := L) c ma ua qa ea sz kd kp lv su sg
  refine hW.mono hSub ?_
  intro ν hfr h
  have hC := Mem.readBlocks_getD h.2 (i := 0) (by simp)
  have hSizes := Mem.readBlocks_getD h.2 (i := 1) (by simp)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hC hSizes
  have hPar' := hfr.keep (Store.readsOnly_readBlock par.1 par.2 3 _)
    (hProtect.mono hSub (fun _ _ hp => Or.inr (Or.inl hp))) hPar
  exact ⟨h.1, hPar', hC, storesLevel_zero_of_initialize_read M F fuel R0 eps beta A h.2,
    fun e he heL lo hlo => futureSize_zero_of_initialize_read M hSizes e he heL lo hlo⟩

end NLAlib.SpectralBisection
