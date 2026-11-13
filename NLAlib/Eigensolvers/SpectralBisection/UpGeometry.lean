/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import NLAlib.Ops.Logic.BlockPartition
public import NLAlib.Ops.Logic.Footprint
public import NLAlib.Ops.Tactic

/-!
# Operand views for upward bisection reconstruction

One separation invariant covers parent outputs, child slot reservations, parent basis,
metadata and scalar workspace. Actual branch operands are subviews of those same regions.

## Main results

* `NLAlib.SpectralBisection.apart_upShift`: the copy-and-shift operands.
* `NLAlib.SpectralBisection.apart_upSplit`: both parent outputs and all split inputs.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The one-child reconstruction's five operands are views of the common arena regions. -/
theorem apart_upShift {n k : ℕ} (hk : k ≤ n) {u e uc ec q kind split t : ℕ × ℕ}
    (h : Fp.Apart [u, e, uc, ec, q, kind, split, t]
      [2 * (k * k), k, 2 * n * k, k, 2 * (k * k), 1, 1, 2]) (side : Bool) :
    Fp.Apart [u, e, uc, ec, (t.1, t.2 + if side then 0 else 1)]
      [2 * (k * k), k, 2 * (k * k), k, 1] := by
  have hmul := Nat.mul_le_mul_left (2 * k) hk
  have hv := h.subviews (![0, 1, 2, 3, 7] : Fin 5 → Fin 8)
    ![0, 0, 0, 0, if side then 0 else 1] ![2 * (k * k), k, 2 * (k * k), k, 1]
    (by intro i; fin_cases i <;> cases side <;> simp <;> nlinarith)
    (by intro a b hab hp; fin_cases a <;> fin_cases b <;> simp at hab hp ⊢)
  simpa [List.ofFn_succ] using hv

/-- Both split outputs and all seven inputs are disjoint subviews of the common arena
regions. This includes zero-size children and shared-buffer consecutive slot reservations. -/
theorem apart_upSplit {n k r : ℕ} (hk : k ≤ n) (hr : r ≤ k)
    {u e uc ec q kind split t : ℕ × ℕ}
    (h : Fp.Apart [u, e, uc, ec, q, kind, split, t]
      [2 * (k * k), k, 2 * n * k, k, 2 * (k * k), 1, 1, 2]) :
    Fp.Apart [u, (u.1, u.2 + 2 * (k * r)), e, (e.1, e.2 + r),
      q, (q.1, q.2 + 2 * (k * r)), uc, (uc.1, uc.2 + 2 * n * r),
      ec, (ec.1, ec.2 + r), t]
      [r * k * 2, (k - r) * k * 2, r, k - r, r * k * 2, (k - r) * k * 2,
        r * r * 2, (k - r) * (k - r) * 2, r, k - r, 1] := by
  have hsum := Nat.sub_add_cancel hr
  have hleft := Nat.mul_le_mul_left (2 * r) (hr.trans hk)
  have hright := Nat.mul_le_mul_left (2 * (k - r)) ((Nat.sub_le k r).trans hk)
  have hv := h.subviews (![0, 0, 1, 1, 4, 4, 2, 2, 3, 3, 7] : Fin 11 → Fin 8)
    ![0, 2 * (k * r), 0, r, 0, 2 * (k * r), 0, 2 * n * r, 0, r, 0]
    ![r * k * 2, (k - r) * k * 2, r, k - r, r * k * 2, (k - r) * k * 2,
      r * r * 2, (k - r) * (k - r) * 2, r, k - r, 1]
    (by intro i; fin_cases i <;> simp <;> nlinarith)
    (by
      intro a b hab hp
      fin_cases a <;> fin_cases b <;>
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ne_eq,
          not_true_eq_false, Fin.mk_one, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one,
          not_false_eq_true, List.length_cons, List.length_nil, Matrix.cons_val_zero,
          Matrix.cons_val_one, zero_add, nonpos_iff_eq_zero, Nat.add_eq_zero_iff, mul_eq_zero,
          OfNat.ofNat_ne_zero, false_or, or_false, Fin.reduceFinMk, Fin.reduceEq,
          Matrix.cons_val, Fin.one_eq_zero_iff, Std.le_refl, true_or, or_true, or_self]
          at hab hp ⊢ <;> first | nlinarith | (left; nlinarith) | (right; nlinarith))
  simpa [List.ofFn_succ] using hv

/-- The two product blocks and two value blocks fit the complete parent output capacities. -/
theorem room_upSplit {K : Type} {m : Mem K} {k r : ℕ} (hr : r ≤ k) {u e : ℕ × ℕ}
    (hu : u.2 + 2 * (k * k) ≤ m.store.len u.1) (he : e.2 + k ≤ m.store.len e.1) :
    m.Room [u, (u.1, u.2 + 2 * (k * r)), e, (e.1, e.2 + r)]
      [r * k * 2, (k - r) * k * 2, r, k - r] := by
  have hsum := Nat.sub_add_cancel hr
  have hmul := Nat.mul_le_mul_left (2 * k) hr
  simp only [Mem.room_cons, Mem.room_nil]
  exact ⟨by nlinarith, by nlinarith, by omega, by omega, trivial⟩

/-- Reconstructed split subblocks occupy exactly the two complete parent output regions. -/
theorem fp_upSplit_eq {k r : ℕ} (hr : r ≤ k) (u e : ℕ × ℕ) :
    Fp.blocks [u, (u.1, u.2 + 2 * (k * r)), e, (e.1, e.2 + r)]
      [r * k * 2, (k - r) * k * 2, r, k - r] = Fp.blocks [u, e] [2 * (k * k), k] := by
  have hsum : r * k * 2 + (k - r) * k * 2 = 2 * (k * k) := by
    have := Nat.sub_add_cancel hr
    nlinarith
  have h := Fp.blocks_pair_adjacent u e (r * k * 2) ((k - r) * k * 2) r (k - r)
  rw [hsum, Nat.add_sub_of_le hr] at h
  simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

end NLAlib.SpectralBisection
