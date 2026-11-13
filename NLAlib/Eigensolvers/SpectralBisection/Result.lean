/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.EntryLayout
public import NLAlib.Ops.Logic.BlockSequence
public import NLAlib.Ops.Logic.IndependentLoop

/-!
# Stored mathematical bisection results

A node result is an ordinary matrix/eigenvalue pair. Its representation is one tuple of
actual packed reads from the basis and eigenvalue arenas. This predicate describes final
mathematical outputs and is independent of traversal stages or execution histories.

## Main results

* `NLAlib.SpectralBisection.StoresResult`: packed storage of a mathematical result pair.
* `NLAlib.SpectralBisection.readsOnly_storesResult`: its exact local read footprint.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Matrix and eigenvalue locations of a node result in the two level arenas. -/
def resultOperands (n d lo : ℕ) (u e : ℕ × ℕ) : List (ℕ × ℕ) :=
  [(u.1, u.2 + 2 * (n * n) * d + 2 * n * lo), (e.1, e.2 + n * d + lo)]

/-- The two packed word lengths of a dimension-k matrix/eigenvalue result. -/
def resultLengths (k : ℕ) : List ℕ := [2 * (k * k), k]

/-- Matrix and eigenvalue payloads occupied by every node result in one level. -/
def resultLevelFootprint (n d : ℕ) (ks : ℕ → ℕ) (u e : ℕ × ℕ) : Fp :=
  Fp.loopPrefix (fun lo => Fp.blocks (resultOperands n d lo u e) (resultLengths (ks lo))) n

/-- A level's result payloads stay below any boundary containing its two arena handles. -/
theorem disj_resultLevelFootprint_above {n d L : ℕ} {ks : ℕ → ℕ} {u e : ℕ × ℕ}
    (hu : u.1 < L) (he : e.1 < L) :
    Fp.Disj (resultLevelFootprint n d ks u e) (Fp.above L) := by
  rintro b i ⟨lo, _, hcell⟩ habove
  simp only [resultOperands, resultLengths, Fp.blocks] at hcell
  rcases hcell with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | hfalse
  · exact Nat.not_le_of_lt hu habove
  · exact Nat.not_le_of_lt he habove
  · exact False.elim hfalse

/-- Store a mathematical matrix/eigenvalue pair in its actual arena regions. The artificial
zero tape position is immaterial: block reads depend only on the store. -/
def StoresResult {K : Type} {k : ℕ} (n d lo : ℕ) (u e : ℕ × ℕ)
    (result : Matrix (Fin k) (Fin k) (K × K) × (Fin k → K)) (s : Store K) : Prop :=
  (Mem.mk s 0).readBlocks (resultOperands n d lo u e) (resultLengths k) =
    some [(EntryCodec.pair K).packFinMatrix result.1, List.ofFn result.2]

/-- A collected actual read tuple supplies the result representation at any tape position. -/
theorem storesResult_iff_readBlocks {K : Type} {k n d lo : ℕ} {u e : ℕ × ℕ}
    {result : Matrix (Fin k) (Fin k) (K × K) × (Fin k → K)} {m : Mem K} :
    StoresResult n d lo u e result m.store ↔
      m.readBlocks (resultOperands n d lo u e) (resultLengths k) =
        some [(EntryCodec.pair K).packFinMatrix result.1, List.ofFn result.2] := by
  unfold StoresResult
  rw [Mem.readBlocks_congr (m' := Mem.mk m.store 0) (m := m) rfl]

/-- Read the actual packed basis of a represented mathematical result. -/
theorem StoresResult.matrix_read {K : Type} {k n d lo : ℕ} {u e : ℕ × ℕ}
    {result : Matrix (Fin k) (Fin k) (K × K) × (Fin k → K)} {s : Store K}
    (h : StoresResult n d lo u e result s) :
    s.readBlock u.1 (u.2 + 2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) =
      some ((EntryCodec.pair K).packFinMatrix result.1) := by
  simpa [StoresResult, resultOperands, resultLengths] using
    Mem.readBlocks_getD h (i := 0) (by simp [resultOperands, resultLengths])

/-- Read the actual packed eigenvalue vector of a represented mathematical result. -/
theorem StoresResult.values_read {K : Type} {k n d lo : ℕ} {u e : ℕ × ℕ}
    {result : Matrix (Fin k) (Fin k) (K × K) × (Fin k → K)} {s : Store K}
    (h : StoresResult n d lo u e result s) :
    s.readBlock e.1 (e.2 + n * d + lo) k = some (List.ofFn result.2) := by
  simpa [StoresResult, resultOperands, resultLengths] using
    Mem.readBlocks_getD h (i := 1) (by simp [resultOperands, resultLengths])

/-- The result predicate reads only its two matrix/vector payloads. -/
theorem readsOnly_storesResult {K : Type} {k : ℕ} (n d lo : ℕ) (u e : ℕ × ℕ)
    (result : Matrix (Fin k) (Fin k) (K × K) × (Fin k → K)) :
    Store.ReadsOnly (Fp.blocks (resultOperands n d lo u e) (resultLengths k))
      (StoresResult n d lo u e result) := by
  intro s s' hagree hr
  have hu := Mem.readBlocks_getD hr (i := 0) (by simp [resultOperands, resultLengths])
  have he := Mem.readBlocks_getD hr (i := 1) (by simp [resultOperands, resultLengths])
  simp only [resultOperands, resultLengths, List.getD_cons_zero, List.getD_cons_succ] at hu he
  have hu' := Store.readsOnly_readBlock _ _ _ _ s s'
    (fun b i hi => hagree b i (Or.inl hi)) hu
  have he' := Store.readsOnly_readBlock _ _ _ _ s s'
    (fun b i hi => hagree b i (Or.inr (Or.inl hi))) he
  simp [StoresResult, resultOperands, resultLengths, Mem.readBlocks, hu', he']

/-- Disjoint writes preserve the complete mathematical output pair. -/
theorem StoresResult.of_eqOff {K : Type} {k n d lo : ℕ} {u e : ℕ × ℕ}
    {result : Matrix (Fin k) (Fin k) (K × K) × (Fin k → K)} {s s' : Store K} {F : Fp}
    (hfr : s.EqOff F s')
    (hdis : Fp.Disj F (Fp.blocks (resultOperands n d lo u e) (resultLengths k)))
    (h : StoresResult n d lo u e result s) : StoresResult n d lo u e result s' :=
  hfr.keep (readsOnly_storesResult n d lo u e result) hdis h

/-- Empty-dimensional mathematical outputs require no initialized cells. -/
theorem storesResult_zero {K : Type} (n d lo : ℕ) (u e : ℕ × ℕ)
    (result : Matrix (Fin 0) (Fin 0) (K × K) × (Fin 0 → K)) (s : Store K) :
    StoresResult n d lo u e result s := by
  simp [StoresResult, resultOperands, resultLengths, Mem.readBlocks, EntryCodec.packFinMatrix]

/-- A zero-dimensional result, with its dimension expressed by an equality, reads no cells. -/
theorem storesResult_of_eq_zero {K : Type} {k : ℕ} (hk : k = 0) (n d lo : ℕ)
    (u e : ℕ × ℕ) (result : Matrix (Fin k) (Fin k) (K × K) × (Fin k → K)) (s : Store K) :
    StoresResult n d lo u e result s := by
  subst k
  exact storesResult_zero n d lo u e result s

/-- Agreement below the surviving handles preserves the complete mathematical result. -/
theorem StoresResult.of_below {K : Type} {k n d lo L : ℕ} {u e : ℕ × ℕ}
    {result : Matrix (Fin k) (Fin k) (K × K) × (Fin k → K)} {s s' : Store K}
    (hBelow : Store.Below L s s') (hu : u.1 < L) (he : e.1 < L)
    (h : StoresResult n d lo u e result s) : StoresResult n d lo u e result s' := by
  refine hBelow.keep (readsOnly_storesResult n d lo u e result) ?_ h
  intro b i hi
  simp only [resultOperands, resultLengths, Fp.blocks] at hi
  rcases hi with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | hfalse
  · exact hu
  · exact he
  · exact False.elim hfalse

end NLAlib.SpectralBisection
