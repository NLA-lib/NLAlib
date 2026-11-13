/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Storage

/-!
# Mathematical node lookup by level and slot

The pure path traversal determines a node at a slot. Empty slots have a zero-dimensional
fallback. This lookup is mathematical specification data: the actual program continues to
read its size words through bounded index queries. Canonical root geometry supplies bounded,
disjoint slot ranges, and the global storage predicates supply the actual input words.

## Main results

* `NLAlib.SpectralBisection.nodeAtSlot`: a typed mathematical node for each slot.
* `NLAlib.SpectralBisection.nodeAtSlot_k_le`: its canonical root size bound.
* `NLAlib.SpectralBisection.disjoint_nodeAtSlot_intervals`: the level partition invariant.
* `NLAlib.SpectralBisection.StoresLevel.nodeAtSlot_size`: the actual stored size word.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- A pure mathematical node at a level's slot, with an empty-dimensional fallback. The
fallback has the level's common parameters and requires no distinguished matrix entry. -/
noncomputable def nodeAtSlot {K : Type} (F : FloatMachine K ℕ ℕ) (n fuel : ℕ)
    (R0 beta : K) (root : EighNode K) (d lo : ℕ) : EighNode K := by
  classical
  exact if h : ∃ x : EighNode K, ∃ a : List Bool, a.length = d ∧
      eighLoc F n fuel R0 beta 0 0 root a = some (lo, x) then Classical.choose h
    else ⟨0, Matrix.of (fun i _ => i.elim0),
      (eighLevelParams F R0 root.ε root.ℓ d).1,
      (eighLevelParams F R0 root.ε root.ℓ d).2, root.ℓ + d⟩

/-- A nonempty lookup has a path witness at exactly the requested level and slot. -/
theorem nodeAtSlot_spec {K : Type} {F : FloatMachine K ℕ ℕ} {n fuel d lo : ℕ}
    {R0 beta : K} {root : EighNode K}
    (h : ∃ x : EighNode K, ∃ a : List Bool, a.length = d ∧
      eighLoc F n fuel R0 beta 0 0 root a = some (lo, x)) :
    ∃ a : List Bool, a.length = d ∧ eighLoc F n fuel R0 beta 0 0 root a =
      some (lo, nodeAtSlot F n fuel R0 beta root d lo) := by
  classical
  simpa only [nodeAtSlot, dif_pos h] using Classical.choose_spec h

/-- An absent mathematical slot has dimension zero. -/
theorem nodeAtSlot_k_eq_zero_of_absent {K : Type} {F : FloatMachine K ℕ ℕ}
    {n fuel d lo : ℕ} {R0 beta : K} {root : EighNode K}
    (h : ¬∃ x : EighNode K, ∃ a : List Bool, a.length = d ∧
      eighLoc F n fuel R0 beta 0 0 root a = some (lo, x)) :
    (nodeAtSlot F n fuel R0 beta root d lo).k = 0 := by
  simp only [nodeAtSlot, dif_neg h]

/-- A positive-dimensional lookup always denotes an actual reached mathematical node. -/
theorem exists_eighLoc_of_nodeAtSlot_k_pos {K : Type} {F : FloatMachine K ℕ ℕ}
    {n fuel d lo : ℕ} {R0 beta : K} {root : EighNode K}
    (hp : 0 < (nodeAtSlot F n fuel R0 beta root d lo).k) :
    ∃ a : List Bool, a.length = d ∧ eighLoc F n fuel R0 beta 0 0 root a =
      some (lo, nodeAtSlot F n fuel R0 beta root d lo) := by
  classical
  apply nodeAtSlot_spec
  by_contra h
  have hz := nodeAtSlot_k_eq_zero_of_absent h
  omega

/-- Reached positive nodes at one slot and one depth are equal. Pure interval separation
rules out distinct paths; no accuracy or sample-law assumption is required. -/
theorem eq_of_eighLoc_eq_some {K : Type} {F : FloatMachine K ℕ ℕ} {n fuel : ℕ}
    {R0 eps beta : K} {ell : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)}
    {a b : List Bool} {lo : ℕ} {x y : EighNode K} (hlen : a.length = b.length)
    (hx : eighLoc F n fuel R0 beta 0 0 ⟨n, A, R0, eps, ell⟩ a = some (lo, x))
    (hy : eighLoc F n fuel R0 beta 0 0 ⟨n, A, R0, eps, ell⟩ b = some (lo, y))
    (hpos : 0 < x.k) : x = y := by
  by_cases hab : a = b
  · subst b
    exact (Prod.mk.inj (Option.some.inj (hx.symm.trans hy))).2
  · have hn : 1 ≤ n := by have := (add_k_le_and_of_eighLoc hx).1; omega
    have hpy := (add_k_le_and_of_eighLoc hy).2 hn
    have hsep := eighLoc_disjoint hlen hab hx hy
    omega

/-- At an occupied positive slot, lookup returns exactly the node reached along its path. -/
theorem nodeAtSlot_eq_of_eighLoc {K : Type} {F : FloatMachine K ℕ ℕ} {n fuel d lo : ℕ}
    {R0 eps beta : K} {ell : ℕ} {A : Matrix (Fin n) (Fin n) (K × K)}
    {a : List Bool} {x : EighNode K} (ha : a.length = d)
    (hx : eighLoc F n fuel R0 beta 0 0 ⟨n, A, R0, eps, ell⟩ a = some (lo, x))
    (hp : 0 < x.k) : nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo = x := by
  obtain ⟨b, hb, hy⟩ := nodeAtSlot_spec ⟨x, a, ha, hx⟩
  exact (eq_of_eighLoc_eq_some (ha.trans hb.symm) hx hy hp).symm

/-- Every canonical-root lookup fits the remaining root slots, including an empty fallback. -/
theorem nodeAtSlot_k_le {K : Type} (F : FloatMachine K ℕ ℕ) (n fuel : ℕ)
    (R0 eps beta : K) (ell : ℕ) (A : Matrix (Fin n) (Fin n) (K × K)) (d lo : ℕ) :
    (nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo).k ≤ n - lo := by
  classical
  by_cases h : ∃ x : EighNode K, ∃ a : List Bool, a.length = d ∧
      eighLoc F n fuel R0 beta 0 0 ⟨n, A, R0, eps, ell⟩ a = some (lo, x)
  · obtain ⟨a, _, hx⟩ := nodeAtSlot_spec h
    have := (add_k_le_and_of_eighLoc hx).1
    omega
  · rw [nodeAtSlot_k_eq_zero_of_absent h]
    exact Nat.zero_le _

/-- Every slot uses the mathematical level's common radius, tolerance and depth counter. -/
theorem nodeAtSlot_params {K : Type} (F : FloatMachine K ℕ ℕ) (n fuel : ℕ)
    (R0 eps beta : K) (ell : ℕ) (A : Matrix (Fin n) (Fin n) (K × K)) (d lo : ℕ) :
    let x := nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo
    x.R = (eighLevelParams F R0 eps ell d).1 ∧
      x.ε = (eighLevelParams F R0 eps ell d).2 ∧ x.ℓ = ell + d := by
  classical
  by_cases h : ∃ x : EighNode K, ∃ a : List Bool, a.length = d ∧
      eighLoc F n fuel R0 beta 0 0 ⟨n, A, R0, eps, ell⟩ a = some (lo, x)
  · obtain ⟨a, ha, hx⟩ := nodeAtSlot_spec h
    simpa only [ha] using eighLoc_params hx
  · simp only [nodeAtSlot, dif_neg h, and_true]

/-- Distinct slot lookups occupy disjoint root-slot intervals. Empty slots are included. -/
theorem disjoint_nodeAtSlot_intervals {K : Type} (F : FloatMachine K ℕ ℕ) (n fuel : ℕ)
    (R0 eps beta : K) (ell : ℕ) (A : Matrix (Fin n) (Fin n) (K × K)) (d lo lo' : ℕ)
    (hne : lo ≠ lo') :
    Disjoint (Finset.Ico lo (lo + (nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo).k))
      (Finset.Ico lo' (lo' + (nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo').k)) := by
  by_cases hz : (nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo).k = 0
  · simp [hz]
  by_cases hz' : (nodeAtSlot F n fuel R0 beta ⟨n, A, R0, eps, ell⟩ d lo').k = 0
  · simp [hz']
  obtain ⟨a, ha, hx⟩ := exists_eighLoc_of_nodeAtSlot_k_pos (Nat.pos_of_ne_zero hz)
  obtain ⟨b, hb, hy⟩ := exists_eighLoc_of_nodeAtSlot_k_pos (Nat.pos_of_ne_zero hz')
  have hab : a ≠ b := by
    intro heq
    subst b
    exact hne (Prod.mk.inj (Option.some.inj (hx.symm.trans hy))).1
  have hsep := eighLoc_disjoint (ha.trans hb.symm) hab hx hy
  apply Finset.disjoint_left.mpr
  intro i hi hi'
  have hleft := Finset.mem_Ico.mp hi
  have hright := Finset.mem_Ico.mp hi'
  omega

/-- The actual size word is the literal of the typed mathematical slot lookup. -/
theorem StoresLevel.nodeAtSlot_size {K : Type} {M : Machine K} {F : FloatMachine K ℕ ℕ}
    {n fuel d lo : ℕ} {R0 beta : K} {root : EighNode K} {ma sz lv : ℕ × ℕ} {m : Mem K}
    (h : StoresLevel M F n fuel R0 beta root d ma sz lv m) (hlo : lo < n) :
    m.store.get sz.1 (sz.2 + n * d + lo) =
      some (M.lit ((nodeAtSlot F n fuel R0 beta root d lo).k : ℚ)) := by
  classical
  by_cases hex : ∃ x : EighNode K, ∃ a : List Bool, a.length = d ∧
      eighLoc F n fuel R0 beta 0 0 root a = some (lo, x)
  · obtain ⟨a, ha, hx⟩ := nodeAtSlot_spec hex
    exact (h.1 a lo _ ha hx).1
  · have hzero := h.2.1 lo hlo (fun a x ha hx => hex ⟨x, a, ha, hx⟩)
    simpa only [nodeAtSlot_k_eq_zero_of_absent hex, Nat.cast_zero] using hzero

/-- A positive slot's actual packed matrix is the matrix of its typed mathematical lookup. -/
theorem StoresLevel.nodeAtSlot_matrix {K : Type} {M : Machine K} {F : FloatMachine K ℕ ℕ}
    {n fuel d lo : ℕ} {R0 beta : K} {root : EighNode K} {ma sz lv : ℕ × ℕ} {m : Mem K}
    (h : StoresLevel M F n fuel R0 beta root d ma sz lv m)
    (hp : 0 < (nodeAtSlot F n fuel R0 beta root d lo).k) :
    m.store.readBlock ma.1 (ma.2 + 2 * (n * n) * d + 2 * n * lo)
      (2 * ((nodeAtSlot F n fuel R0 beta root d lo).k *
        (nodeAtSlot F n fuel R0 beta root d lo).k)) =
      some ((EntryCodec.pair K).packFinMatrix (nodeAtSlot F n fuel R0 beta root d lo).A) := by
  obtain ⟨a, ha, hx⟩ := exists_eighLoc_of_nodeAtSlot_k_pos hp
  exact (h.1 a lo _ ha hx).2

/-- Pointwise actual raw-word outcomes for positive typed slot lookups give the global
indexed-tape record representation. The lookup is specification data only. -/
theorem storesRecords_of_nodeAtSlot_steps {K : Type} [Inhabited K]
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (n base : ℕ) (τ : Tape K) (fuel : ℕ) (R0 eps beta : K) (ell : ℕ)
    (A : Matrix (Fin n) (Fin n) (K × K)) (d : ℕ)
    (ma ua qa ea sz kd kp : ℕ × ℕ) (m : Mem K)
    (hSlots : ∀ lo < n,
      let x := nodeAtSlot (tapeMachine M dec mm qr n base τ) n fuel R0 beta
        ⟨n, A, R0, eps, ell⟩ d lo
      0 < x.k → StoresStep M x.R n d lo ma ua qa ea sz kd kp
        (eighStep (M.toFloatMachine dec mm qr M.mul
          (fun z : K × K => M.normalWords z.1 z.2)) n fuel R0 beta x.A x.R x.ε x.ℓ
          (storedNodeSample n lo (vec (levelUniformWords n base τ d) lo)
            (levelGaussianMatrix n base τ d))) m) :
    StoresRecords M (tapeMachine M dec mm qr n base τ) n fuel R0 beta
      ⟨n, A, R0, eps, ell⟩ d ma ua qa ea sz kd kp m := by
  apply storesRecords_of_word_steps M dec mm qr n base τ fuel R0 eps beta ell A
    d ma ua qa ea sz kd kp m
  intro a lo x ha hx hpos
  have hlo : lo < n := by have := (add_k_le_and_of_eighLoc hx).1; omega
  have hnode := nodeAtSlot_eq_of_eighLoc ha hx hpos
  have hs := hSlots lo hlo
  dsimp only at hs
  rw [hnode] at hs
  exact hs hpos

end NLAlib.SpectralBisection
