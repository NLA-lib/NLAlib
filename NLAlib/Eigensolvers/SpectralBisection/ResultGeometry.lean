/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Result
public import NLAlib.Eigensolvers.SpectralBisection.Arena
public import NLAlib.Eigensolvers.SpectralBisection.ArenaLayout

/-!
# Spatial geometry of stored node results

The basis and eigenvalue fields use the same disjoint mathematical slot intervals. The
geometry applies at every reserved level, including the final level where no QR or kind
storage is required.

## Main results

* `NLAlib.SpectralBisection.disj_resultSlots`: disjoint slots give disjoint result payloads.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The basis, eigenvalue and size reservations at a valid level are separated arena subviews. -/
theorem apart_resultLevel_size_of_arenas {n L d : ℕ} (hd : d ≤ L + 1)
    (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ)
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Apart [(ua.1, ua.2 + 2 * (n * n) * d), (ea.1, ea.2 + n * d),
      (sz.1, sz.2 + n * d)] [2 * (n * n), n, n] := by
  have hInjective : Function.Injective (![2, 4, 5] : Fin 3 → Fin 11) := by decide
  have hdu := Nat.mul_le_mul_left (2 * (n * n)) hd
  have hde := Nat.mul_le_mul_left n hd
  have hv := hAP.subviews (fun i : Fin 3 => (![2, 4, 5] : Fin 3 → Fin 11) i)
    ![2 * (n * n) * d, n * d, n * d] ![2 * (n * n), n, n]
    (by intro i; fin_cases i <;> simp [arenaOperands, arenaLengths] <;> nlinarith)
    (fun i j hij he => False.elim (hij (hInjective he)))
  simpa [arenaOperands, arenaLengths] using hv

/-- The full basis and eigenvalue reservations of a valid level are separated. -/
theorem apart_resultLevelSpan_of_arenas {n L d : ℕ} (hd : d ≤ L + 1)
    (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ)
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Apart [(ua.1, ua.2 + 2 * (n * n) * d), (ea.1, ea.2 + n * d)]
      [2 * (n * n), n] := by
  have h := apart_resultLevel_size_of_arenas hd c ma ua qa ea sz kd kp lv su sg hAP
  simpa using (h.take_drop (by simp) 2).1

/-- A square basis payload fits inside the full matrix reservation at its level. -/
theorem resultMatrix_le_level {n d lo k : ℕ} (hslot : lo + k ≤ n) (u : ℕ × ℕ) :
    Store.inBlock u.1 (u.2 + 2 * (n * n) * d + 2 * n * lo) (2 * (k * k)) ≤
      Store.inBlock u.1 (u.2 + 2 * (n * n) * d) (2 * (n * n)) := by
  apply Fp.inBlock_le_inBlock (by omega)
  have hkk := Nat.mul_le_mul_left k (show k ≤ n by omega)
  have hn := Nat.mul_le_mul_left n hslot
  nlinarith

/-- An eigenvalue payload fits inside the full vector reservation at its level. -/
theorem resultValues_le_level {n d lo k : ℕ} (hslot : lo + k ≤ n) (e : ℕ × ℕ) :
    Store.inBlock e.1 (e.2 + n * d + lo) k ≤ Store.inBlock e.1 (e.2 + n * d) n :=
  Fp.inBlock_le_inBlock (by omega) (by omega)

/-- Ordered slots give disjoint matrix/vector result tuples in separated level spans. -/
theorem disj_resultSlots_of_le {n d lo k j r : ℕ}
    (hslot : lo + k ≤ n) (hslot' : j + r ≤ n) (hsep : lo + k ≤ j)
    (u e : ℕ × ℕ)
    (hUE : Fp.Disj (Store.inBlock u.1 (u.2 + 2 * (n * n) * d) (2 * (n * n)))
      (Store.inBlock e.1 (e.2 + n * d) n)) :
    Fp.Disj (Fp.blocks (resultOperands n d lo u e) (resultLengths k))
      (Fp.blocks (resultOperands n d j u e) (resultLengths r)) := by
  simp only [resultOperands, resultLengths, Fp.blocks_cons, Fp.blocks_nil, sup_bot_eq,
    Fp.disj_sup_left, Fp.disj_sup_right]
  refine ⟨⟨?_, hUE.symm.mono (resultValues_le_level (d := d) hslot e)
      (resultMatrix_le_level (d := d) hslot' u)⟩,
    hUE.mono (resultMatrix_le_level (d := d) hslot u)
      (resultValues_le_level (d := d) hslot' e), ?_⟩
  · apply Fp.disj_inBlock_of_le
    have hkk := Nat.mul_le_mul_left k (show k ≤ n by omega)
    have hsep' := Nat.mul_le_mul_left (2 * n) hsep
    nlinarith
  · exact Fp.disj_inBlock_of_le (by omega)

/-- Disjoint mathematical slot intervals separate both stored result fields. -/
theorem disj_resultSlots {n d lo k j r : ℕ}
    (hslot : lo + k ≤ n) (hslot' : j + r ≤ n)
    (hsep : Disjoint (Finset.Ico lo (lo + k)) (Finset.Ico j (j + r)))
    (u e : ℕ × ℕ)
    (hUE : Fp.Disj (Store.inBlock u.1 (u.2 + 2 * (n * n) * d) (2 * (n * n)))
      (Store.inBlock e.1 (e.2 + n * d) n)) :
    Fp.Disj (Fp.blocks (resultOperands n d lo u e) (resultLengths k))
      (Fp.blocks (resultOperands n d j u e) (resultLengths r)) := by
  by_cases hk : k = 0
  · subst k
    disjoint [resultOperands, resultLengths]
  by_cases hr : r = 0
  · subst r
    disjoint [resultOperands, resultLengths]
  have ho : lo + k ≤ j ∨ j + r ≤ lo := by
    by_contra h
    push Not at h
    exact Finset.disjoint_left.mp hsep
      (Finset.mem_Ico.mpr ⟨le_max_left _ _, by omega⟩)
      (Finset.mem_Ico.mpr ⟨le_max_right _ _, by omega⟩)
  exact ho.elim (fun h => disj_resultSlots_of_le hslot hslot' h u e hUE)
    (fun h => (disj_resultSlots_of_le hslot' hslot h u e hUE).symm)

end NLAlib.SpectralBisection
