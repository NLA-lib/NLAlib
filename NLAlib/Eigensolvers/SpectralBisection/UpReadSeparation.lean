/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.UpArenaGeometry
public import NLAlib.Ops.Logic.BlockPartition

/-!
# Deeper reconstruction preserves shallow inputs and outcomes

The complete arena collection supplies cross-arena separation. The only matching read/write
arenas are the basis and eigenvalue arenas, where strict depth order gives disjoint level
intervals. This proves all shallow data remains available under the completed upward prefix.

## Main results

* `NLAlib.SpectralBisection.disj_resultLevelSpan_upReadRegion`: full-level separation.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- A completed deeper result level is spatially separate from every shallow input or stored
outcome read. Caller-owned arenas may share a buffer in disjoint intervals. -/
theorem disj_resultLevelSpan_upReadRegion {n L d e : ℕ}
    (hd : d ≤ L) (he : e ≤ L + 1) (hde : d < e)
    (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ)
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Disj (resultLevelSpan n e ua ea) (upReadRegion n d ma lv ua qa ea sz kd kp c) := by
  let leftRole : Fin 2 → Fin 11 := ![2, 4]
  let rightRole : Fin 11 → Fin 11 := ![1, 2, 3, 4, 5, 6, 7, 1, 5, 8, 0]
  let left : Fin 2 → Fin (min
      (arenaOperands c ma ua qa ea sz kd kp lv su sg).length (arenaLengths n L).length) :=
    fun a => ⟨(leftRole a).val, by
      simp [arenaOperands, arenaLengths]⟩
  let right : Fin 11 → Fin (min
      (arenaOperands c ma ua qa ea sz kd kp lv su sg).length (arenaLengths n L).length) :=
    fun a => ⟨(rightRole a).val, by
      simp [arenaOperands, arenaLengths]⟩
  let lo : Fin 2 → ℕ := ![2 * (n * n) * e, n * e]
  let llen : Fin 2 → ℕ := ![2 * (n * n), n]
  let ro : Fin 11 → ℕ :=
    ![2 * (n * n) * (d + 1), 2 * (n * n) * d, 2 * (n * n) * d, n * d,
      n * (d + 1), n * d, n * d, 2 * (n * n) * d, n * d, 2 * d, 1]
  let rlen : Fin 11 → ℕ :=
    ![2 * (n * n), 2 * (n * n), 2 * (n * n), n, n, n, n, 2 * (n * n), n + 1, 2, 1]
  have hU := Nat.mul_le_mul_left (2 * (n * n)) (show d + 2 ≤ L + 2 by omega)
  have hQ := Nat.mul_le_mul_left (2 * (n * n)) (show d + 1 ≤ L + 1 by omega)
  have hS := Nat.mul_le_mul_left n (show d + 2 ≤ L + 2 by omega)
  have hK := Nat.mul_le_mul_left n (show d + 1 ≤ L + 1 by omega)
  have hEU := Nat.mul_le_mul_left (2 * (n * n)) (show e + 1 ≤ L + 2 by omega)
  have hEE := Nat.mul_le_mul_left n (show e + 1 ≤ L + 2 by omega)
  have hSepU := Nat.mul_le_mul_left (2 * (n * n)) (show d + 1 ≤ e by omega)
  have hSepE := Nat.mul_le_mul_left n (show d + 1 ≤ e by omega)
  have hv := hAP.disj_subviews left right lo llen ro rlen (by
    intro a
    fin_cases a <;> simp [left, leftRole, lo, llen, arenaLengths] <;> nlinarith) (by
    intro b
    fin_cases b <;> simp [right, rightRole, ro, rlen, arenaLengths] <;> nlinarith) (by
    intro a b hp
    fin_cases a <;> fin_cases b <;>
      dsimp only [left, right, leftRole, rightRole, lo, llen, ro, rlen] at hp ⊢ <;>
        simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
          Matrix.cons_val] at hp ⊢ <;>
        norm_num at hp <;>
        exact Or.inr (by nlinarith))
  simpa [left, right, leftRole, rightRole, lo, llen, ro, rlen,
    arenaOperands, arenaLengths, List.ofFn_succ,
    resultLevelSpan, upReadRegion, downLevelRegion, downArenaOrigins, downArenaStride,
    Fp.blocks, sup_assoc, Nat.mul_assoc] using hv

/-- The entire completed reverse-depth prefix preserves the next shallow level's reads. -/
theorem disj_upwardPrefix_upReadRegion {n L r : ℕ} (hr : r ≤ L)
    (ks : ℕ → ℕ → ℕ) (hslot : ∀ d ≤ L, ∀ lo < n, lo + ks d lo ≤ n)
    (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ)
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Disj
      (Fp.loopPrefix (fun j => resultLevelFootprint n (L - j) (ks (L - j)) ua ea) r)
      (upReadRegion n (L - r) ma lv ua qa ea sz kd kp c) := by
  rintro b i ⟨j, hj, hc⟩ hread
  have hsub := resultLevelFootprint_le_span (d := L - j) (hslot (L - j) (by omega)) ua ea
  exact disj_resultLevelSpan_upReadRegion (by omega) (by omega) (by omega)
    c ma ua qa ea sz kd kp lv su sg hAP b i (hsub b i hc) hread

/-- Parent reconstruction and a deeper child result level occupy disjoint payloads. -/
theorem disj_resultLevelSpans {n L d e : ℕ} (hd : d ≤ L) (he : e ≤ L + 1) (hde : d < e)
    (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ)
    (hAP : Fp.Apart (arenaOperands c ma ua qa ea sz kd kp lv su sg) (arenaLengths n L)) :
    Fp.Disj (resultLevelSpan n d ua ea) (resultLevelSpan n e ua ea) :=
  ((disj_resultLevelSpan_upReadRegion hd he hde c ma ua qa ea sz kd kp lv su sg hAP).mono
    le_rfl (resultLevelSpan_le_upReadRegion n d ma lv ua qa ea sz kd kp c)).symm

end NLAlib.SpectralBisection
