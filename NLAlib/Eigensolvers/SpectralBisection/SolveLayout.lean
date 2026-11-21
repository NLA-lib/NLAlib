/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.ArenaLayout
public import NLAlib.Ops.Logic.BlockSequence

/-!
# Solver input and output views

The initial matrix/parameter copy and the final result copy use subviews of the same arena
layout. Output views may overlap the original inputs: the final copies run after every
traversal read of those inputs.

## Main results

* `NLAlib.SpectralBisection.apart_initialize_of_arenas`: separation of the initialization views.
* `NLAlib.SpectralBisection.apart_rootCopy_of_arenas`: root and supplied output views.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {n L : ℕ} {a par u dv c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ}

/-- Arenas that are apart give the separation the initializer needs: its four output views are
pairwise apart and apart from the two source blocks. The two sources are only read, so they may
overlap. -/
theorem apart_initialize_of_arenas
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hProtect : Fp.Disj (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg)
      (arenaLengths n L)) (Fp.blocks [a, par] [2 * (n * n), 3])) :
    Fp.Apart [c, sz, ma, lv] [5, n * (L + 2) + 1, 2 * (n * n), 2] ∧
      Fp.Disj (Fp.blocks [c, sz, ma, lv] [5, n * (L + 2) + 1, 2 * (n * n), 2])
        (Fp.blocks [a, par] [2 * (n * n), 2]) := by
  have hn := Nat.le_mul_of_pos_right (2 * (n * n)) (show 0 < L + 2 by omega)
  have hInjective : Function.Injective (![0, 5, 1, 8] : Fin 4 → Fin 11) := by decide
  have hv := hAP.subviews (fun i : Fin 4 => (![0, 5, 1, 8] : Fin 4 → Fin 11) i)
    (fun _ => 0) ![5, n * (L + 2) + 1, 2 * (n * n), 2]
    (by
      intro i
      fin_cases i <;> simp [arenaOperands, arenaLengths]
      omega)
    (fun i j hij he => False.elim (hij (hInjective he)))
  have hle (i : ℕ) (hi : i < 11) := Fp.inBlock_getD_le_blocks
    (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L) (i := i)
    (by simpa [arenaOperands, arenaLengths] using hi)
  have h0 := hle 0 (by omega)
  have h1 := hle 1 (by omega)
  have h5 := hle 5 (by omega)
  have h8 := hle 8 (by omega)
  simp only [arenaOperands, arenaLengths, List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h5 h8
  have hsub : Fp.blocks [c, sz, ma, lv] [5, n * (L + 2) + 1, 2 * (n * n), 2] ≤
      Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L) := by
    simp only [Fp.blocks]
    exact sup_le h0 (sup_le h5 (sup_le ((Fp.inBlock_le_inBlock le_rfl (by omega)).trans h1)
      (sup_le ((Fp.inBlock_le_inBlock le_rfl (by omega)).trans h8) bot_le)))
  have hsrc : Fp.blocks [a, par] [2 * (n * n), 2] ≤ Fp.blocks [a, par] [2 * (n * n), 3] := by
    simp only [Fp.blocks]
    exact sup_le_sup_left (sup_le_sup_right (Fp.inBlock_le_inBlock le_rfl (by omega)) _) _
  exact ⟨by simpa [arenaOperands, arenaLengths, List.ofFn_succ] using hv,
    hProtect.mono hsub hsrc⟩

/-- Arena capacities supply the four initialization output capacities. -/
theorem room_initialize_of_arenas {K : Type} {m : Mem K}
    (hRoom : m.Room (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    m.Room [c, ma, sz, lv] [5, 2 * (n * n), n * (L + 2) + 1, 2] := by
  have hn := Nat.le_mul_of_pos_right (2 * (n * n)) (show 0 < L + 2 by omega)
  have hv := hRoom.subviews (fun i : Fin 4 => (![0, 1, 5, 8] : Fin 4 → Fin 11) i)
    (fun _ => 0) ![5, 2 * (n * n), n * (L + 2) + 1, 2]
    (by
      intro i
      fin_cases i <;> simp [arenaOperands, arenaLengths]
      omega)
  simpa [arenaOperands, arenaLengths, List.ofFn_succ] using hv

/-- Separate supplied outputs and protected arenas give all final-copy separation facts. -/
theorem apart_rootCopy_of_arenas
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hOutput : Fp.Disj (Store.inBlock u.1 u.2 (2 * (n * n))) (Store.inBlock dv.1 dv.2 n))
    (hProtect : Fp.Disj (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg)
      (arenaLengths n L)) (Fp.blocks [u, dv] [2 * (n * n), n])) :
    Fp.Apart [ua, ea, u, dv] [2 * (n * n), n, 2 * (n * n), n] := by
  have ho : Fp.Apart [u, dv] [2 * (n * n), n] := by simpa [Fp.Apart, Fp.blocks] using hOutput
  have hwrite : Fp.Disj (Fp.blocks [u, dv] [2 * (n * n), n])
      (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :=
    hProtect.symm
  have hall := ho.append hAP (by rfl) hwrite
  have hInjective : Function.Injective (![4, 6, 0, 1] : Fin 4 → Fin 13) := by decide
  have hn := Nat.le_mul_of_pos_right n (show 0 < L + 2 by omega)
  have hN := Nat.le_mul_of_pos_right (2 * (n * n)) (show 0 < L + 2 by omega)
  have hv := hall.subviews (fun i : Fin 4 => (![4, 6, 0, 1] : Fin 4 → Fin 13) i)
    (fun _ => 0) ![2 * (n * n), n, 2 * (n * n), n]
    (by intro i; fin_cases i <;> simp [arenaOperands, arenaLengths] <;> omega)
    (fun i j hij he => False.elim (hij (hInjective he)))
  simpa [arenaOperands, arenaLengths, List.ofFn_succ] using hv

end NLAlib.SpectralBisection
