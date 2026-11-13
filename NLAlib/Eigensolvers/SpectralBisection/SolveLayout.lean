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

* `NLAlib.SpectralBisection.apart_initialize_of_arenas`: source and initialization views.
* `NLAlib.SpectralBisection.apart_rootCopy_of_arenas`: root and supplied output views.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

variable {n L : ℕ} {a par u dv c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ}

/-- Separate source blocks and protected arenas give all initializer separation facts. -/
theorem apart_initialize_of_arenas
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
    (hSource : Fp.Disj (Store.inBlock a.1 a.2 (2 * (n * n))) (Store.inBlock par.1 par.2 3))
    (hProtect : Fp.Disj (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg)
      (arenaLengths n L)) (Fp.blocks [a, par] [2 * (n * n), 3])) :
    Fp.Apart [a, par, c, ma, sz, lv]
      [2 * (n * n), 2, 5, 2 * (n * n), n * (L + 2) + 1, 2] := by
  have hi : Fp.Apart [a, par] [2 * (n * n), 3] := by simpa [Fp.Apart, Fp.blocks] using hSource
  have hread : Fp.Disj (Fp.blocks [a, par] [2 * (n * n), 3])
      (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :=
    hProtect.symm
  have hall := hi.append hAP (by rfl) hread
  have hInjective : Function.Injective (![0, 1, 2, 3, 7, 10] : Fin 6 → Fin 13) := by decide
  have hn := Nat.le_mul_of_pos_right (2 * (n * n)) (show 0 < L + 2 by omega)
  have hv := hall.subviews (fun i : Fin 6 => (![0, 1, 2, 3, 7, 10] : Fin 6 → Fin 13) i)
    (fun _ => 0) ![2 * (n * n), 2, 5, 2 * (n * n), n * (L + 2) + 1, 2]
    (by
      intro i
      fin_cases i <;> simp [arenaOperands, arenaLengths]
      omega)
    (fun i j hij he => False.elim (hij (hInjective he)))
  simpa [arenaOperands, arenaLengths, List.ofFn_succ] using hv

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
