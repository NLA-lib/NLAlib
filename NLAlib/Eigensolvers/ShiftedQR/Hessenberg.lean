/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.Storage
public import NLAlib.Matrix.Factorizations.Hessenberg
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.EntryRows
public import NLAlib.Ops.Blas.HermitianEntry

/-!
# Removing structural fill from stored Hessenberg matrices

The in-place pass writes literal zero to the real and imaginary words strictly below the first
subdiagonal. It retains all other words. Its semantics require only a scalar machine and an
exact zero literal, so the pass applies to rounded arithmetic without an exact arithmetic model.

The pass is an entry projection, not a similarity. Its consumer must account for the deleted
fill in its numerical error estimate. The pure projection contracts Frobenius distance to a
Hessenberg target; no spectral-norm contraction or unchanged rounded QR error bound is claimed.

## Main results

* `NLAlib.ShiftedQR.clearBelowSubdiagonal`: the scalar in-place pass.
* `NLAlib.ShiftedQR.clearBelowSubdiagonal_writes`: actual stored profile projection.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Initialize one interleaved complex entry with two visible scalar zero-literal calls. -/
def clearComplexEntry : Impl Op Tst := opsImpl% [] () → (Z) {
  call (Has.inj (ScalarOp.lit 0)) [] () → (Z);
  call (Has.inj (ScalarOp.lit 0)) [] () → (Z[1])
}

/-- Replace only entries strictly below the first subdiagonal by two scalar zero literals.
The supplied matrix is modified in place; no scratch buffer or numerical test is needed. -/
def clearBelowSubdiagonal : Impl Op Tst := opsImpl% [n] () → (A) {
  for i < n {
    for j < i - 1 {
      run clearComplexEntry.body [] (A[2 * (j * n + i)])
    }
  }
}

private theorem clearComplexEntry_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {z : ℕ × ℕ}
    (hz : z.2 + 2 ≤ m.store.len z.1) :
    Writes .total I τ (clearComplexEntry (Op := Op) (Tst := Tst)).body (Env.frame [] [z])
      (Store.inBlock z.1 z.2 2)
      (fun m' => (∀ u : Fin 2, m'.store.get z.1 (z.2 + u) =
        some ((EntryCodec.pair ℝ).words (M.lit 0, M.lit 0) u)) ∧
        m'.pos = m.pos) m := by
  apply Hermitian.writes_pair_of_wp (v := (M.lit 0, M.lit 0)) ?_ hz
  refine wp_seq (wp_call_const (hS (.lit 0)) rfl rfl rfl trivial
    (by simpa using (show z.2 < m.store.len z.1 by omega)) ?_)
  refine wp_call_const (hS (.lit 0)) rfl rfl rfl trivial ?_ ?_
  · simpa only [Mem.store_upd, Store.len_upd] using
      (show z.2 + 1 < m.store.len z.1 by omega)
  · rfl

private theorem clearBelowSubdiagonal_region {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {a : ℕ × ℕ}
    (hl : m.Live [a]) (ha : a.2 + 2 * (n * n) ≤ m.store.len a.1) :
    Writes .total I τ (clearBelowSubdiagonal (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [a])
      ((EntryCodec.pair ℝ).regionFp a.1 a.2 n (fun j i => j * n + i) (fun i => i - 1))
      (fun m' => m'.store.HoldsEntryRegion (EntryCodec.pair ℝ) a.1 a.2 n
        (fun j i => j * n + i) (fun i => i - 1) (fun _ _ => (M.lit 0, M.lit 0)) ∧
        m'.pos = m.pos) m := by
  refine writes_fillEntryRegion (EntryCodec.pair ℝ) a.1 a.2 n
    (fun j i => j * n + i) (fun i => i - 1) ?_ rfl (fun _ => rfl)
    (fun _ _ => (M.lit 0, M.lit 0)) (fun _ _ => m.pos) rfl (fun _ _ => rfl) ?_
  · intro p hp q hq he
    have hp' : p.2 < n := hp.1
    have hq' : q.2 < n := hq.1
    have hd := congrArg (· / n) he
    have hm := congrArg (· % n) he
    simp only [Idx.div_add hp', Idx.div_add hq'] at hd
    simp only [Idx.mod_add hp', Idx.mod_add hq'] at hm
    exact Prod.ext hd hm
  · intro i hi j hj μ hfr hp
    have hflat : j * n + i < n * n := Idx.add_lt_mul (by omega) hi
    have hmul := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt hflat)
    have hroom : a.2 + 2 * (j * n + i) + 2 ≤ μ.store.len a.1 := by
      rw [hfr.len_eq]
      omega
    refine (writes_frame rfl rfl ?_
      (clearComplexEntry_writes (m := μ) (z := (a.1, a.2 + 2 * (j * n + i)))
        hS hroom)).mono le_rfl ?_
    · simpa [Mem.Live, hfr.length_eq] using hl
    · intro μ' _ h
      exact ⟨h.1, h.2.trans hp⟩

/-- The stored pass removes exactly the structural fill and preserves every other entry.
Only literal zero must be exact; all other scalar operations of the machine may be rounded.
The position on the random tape is unchanged. Deletion error is not absorbed into a QR bound. -/
theorem clearBelowSubdiagonal_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hzero : M.lit 0 = 0) {τ : Tape ℝ} {m : Mem ℝ}
    {n : ℕ} {a : ℕ × ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hl : m.Live [a]) (hA : HoldsMatrix a A m.store)
    (ha : a.2 + 2 * (n * n) ≤ m.store.len a.1) :
    Writes .total I τ (clearBelowSubdiagonal (Op := Op) (Tst := Tst)).body
      (Env.frame [n] [a]) (Store.inBlock a.1 a.2 (2 * (n * n)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (upperHessenbergPart A) m'.store ∧
        IsUpperHessenberg (upperHessenbergPart A)) m := by
  let C := EntryCodec.pair ℝ
  let region := C.regionFp a.1 a.2 n (fun j i => j * n + i) (fun i => i - 1)
  have hsub : region ≤ Store.inBlock a.1 a.2 (2 * (n * n)) :=
    C.regionFp_le_inBlock a.1 a.2 n (n * n) (fun j i => j * n + i)
      (fun i => i - 1) (fun i hi j hj => Idx.add_lt_mul (by omega) hi)
  refine (clearBelowSubdiagonal_region hS hl ha).mono hsub fun m' hfr h => ?_
  refine ⟨h.2, HoldsMatrix.of_get ?_ ?_, isUpperHessenberg_upperHessenbergPart A⟩
  all_goals
    intro i j
    by_cases hij : (j : ℕ) + 1 < (i : ℕ)
    · have hentry := h.1 i i.isLt j (by change (j : ℕ) < (i : ℕ) - 1; omega)
      first
      | simpa [upperHessenbergPart, hij, hzero] using hentry 0
      | simpa [upperHessenbergPart, hij, hzero, Nat.add_assoc] using hentry 1
    · have hdis : Fp.Disj region (C.entryBlock a.1 a.2 (j * n + i)) := by
        rintro b x ⟨c, r, hr | ⟨_, hc⟩, hx⟩ hentry
        · have hcr : c < r - 1 := hr.2
          have hne : c * n + r ≠ j * n + i := by
            intro he
            have hd := congrArg (· / n) he
            have hm := congrArg (· % n) he
            simp only [Idx.div_add hr.1, Idx.div_add i.isLt] at hd
            simp only [Idx.mod_add hr.1, Idx.mod_add i.isLt] at hm
            omega
          exact C.disj_entryBlock_of_ne hne b x hx hentry
        · omega
      have hr := hfr.keep (Store.readsOnly_readBlock _ _ _ _) hdis (hA.read_entry i j)
      first
      | simpa [upperHessenbergPart, hij] using
          (Store.get_of_readBlock hr (j := 0) (by norm_num) (0 : ℝ))
      | simpa [upperHessenbergPart, hij, Nat.add_assoc] using
          (Store.get_of_readBlock hr (j := 1) (by norm_num) (0 : ℝ))

end NLAlib.ShiftedQR
