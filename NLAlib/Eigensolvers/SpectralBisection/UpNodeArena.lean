/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpArenaGeometry
public import NLAlib.Ops.Logic.Allocation

/-!
# Upward node regions from the complete arena layout

The parent outputs, child reservations, basis, metadata and fresh two-word workspace are
subviews of the allocated arenas. Repeated views of a basis or eigenvalue arena use adjacent
levels; distinct arenas inherit their declared spatial separation.

## Main results

* `NLAlib.SpectralBisection.apart_upNode_of_arenas`: all local reconstruction separation facts.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- Every local upward node region follows from complete arena apartness and a fresh scratch
handle. No buffer inequality is imposed between caller-owned arenas. -/
theorem apart_upNode_of_arenas {K : Type} {m : Mem K} {n L d lo k : ℕ}
    (hd : d ≤ L) (hlo : lo < n) (hslot : lo + k ≤ n)
    (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ)
    (hl : m.Live (arenaOperands c ma ua qa ea sz kd kp lv su sg))
    (h : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Apart (upNodeRegions n d lo ua qa ea kd kp (m.store.length, 0))
      (upNodeRegionLengths n k) := by
  have hx : Fp.Apart [(m.store.length, 0)] [2] := ⟨Fp.disj_bot_right _, trivial⟩
  have hcross : Fp.Disj
      (Fp.blocks (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L))
      (Fp.blocks [(m.store.length, 0)] [2]) := by
    refine (Fp.blocks_disj_above hl).mono le_rfl ?_
    rintro b i (⟨rfl, _, _⟩ | hf)
    · exact le_rfl
    · exact False.elim hf
  have hp := h.append hx (by rfl) hcross
  let role : Fin 8 → Fin 12 := ![2, 4, 2, 4, 3, 6, 7, 11]
  let parent : Fin 8 → Fin (min
      ((arenaOperands c ma ua qa ea sz kd kp lv su sg) ++ [(m.store.length, 0)]).length
      ((arenaLengths n L) ++ [2]).length) := fun a => ⟨(role a).val, by
        simp [arenaOperands, arenaLengths]⟩
  let offset : Fin 8 → ℕ :=
    ![2 * (n * n) * d + 2 * n * lo, n * d + lo,
      2 * (n * n) * (d + 1) + 2 * n * lo, n * (d + 1) + lo,
      2 * (n * n) * d + 2 * n * lo, n * d + lo, n * d + lo, 0]
  let len : Fin 8 → ℕ := ![2 * (k * k), k, 2 * n * k, k, 2 * (k * k), 1, 1, 2]
  have hk : k ≤ n := by omega
  have hkk := Nat.mul_le_mul_left k hk
  have hksq := Nat.mul_self_le_mul_self hk
  have hn := Nat.mul_le_mul_left n hslot
  have hU := Nat.mul_le_mul_left (2 * (n * n)) (show d + 2 ≤ L + 2 by omega)
  have hQ := Nat.mul_le_mul_left (2 * (n * n)) (show d + 1 ≤ L + 1 by omega)
  have hE := Nat.mul_le_mul_left n (show d + 2 ≤ L + 2 by omega)
  have hK := Nat.mul_le_mul_left n (show d + 1 ≤ L + 1 by omega)
  have hv := hp.subviews parent offset len (by
    intro a
    fin_cases a <;> simp [parent, role, offset, len, arenaLengths] <;> nlinarith)
    (by
      intro a b hab he
      fin_cases a <;> fin_cases b <;>
        simp [parent, role, offset, len, Nat.mul_add] at hab he ⊢ <;> omega)
  simpa [parent, role, offset, len, arenaOperands, arenaLengths, List.ofFn_succ,
    upNodeRegions, resultOperands, upNodeRegionLengths, Nat.add_assoc] using hv

end NLAlib.SpectralBisection
