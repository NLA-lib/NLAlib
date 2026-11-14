/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.StorageNorm
public import NLAlib.Eigensolvers.ShiftedQR.RowSolveStorage
public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.Logic.Loop

/-!
# Basis initialization and row-vector norms

The last basis vector is initialized by actual scalar literals. The squared vector norm
uses the existing fully scalar Euclidean-norm lowering and one scalar multiplication. Its
internal norm workspace is allocated and released by that lowering; the supplied scratch
view holds the intermediate norm word.

## Main results

* `NLAlib.ShiftedQR.lastBasisVector_writes`: exact last basis-vector initialization.
* `NLAlib.ShiftedQR.vectorNormSquared_writes`: exact squared Euclidean norm from actual words.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

variable {Op Tst : Type} [Has ScalarOp Op]

/-- Fill every component with zero, then set the last real component to one. -/
def lastBasisVector : Impl Op Tst := opsImpl% [n] () → (V) {
  for q < 2 * n { call (Has.inj (ScalarOp.lit 0)) [] () → (V[q]) };
  call (Has.inj (ScalarOp.lit 1)) [] () → (V[2 * (n - 1)])
}

/-- Initialize the last complex basis vector of a nonempty finite space from uninitialized
capacity. Every stored component is written by an actual scalar literal call. -/
theorem lastBasisVector_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n : ℕ} {v : ℕ × ℕ} (hv : v.2 + 2 * (n + 1) ≤ m.store.len v.1) :
    Writes .total I τ lastBasisVector.body (Env.frame [n + 1] [v])
      (Store.inBlock v.1 v.2 (2 * (n + 1)))
      (fun μ => μ.pos = m.pos ∧
        HoldsVector v (Pi.single (Fin.last n) (1 : ℂ)) μ.store) m := by
  have hzero : Writes .total I τ
      (.loop (.const 2 * .var 0)
        (.call (Has.inj (ScalarOp.lit 0)) [] [] [⟨0, .var 1 + .var 2⟩]))
      (Env.frame [n + 1] [v]) (Store.inBlock v.1 v.2 (2 * (n + 1)))
      (fun μ => μ.store.HoldsVec v.1 v.2 (2 * (n + 1)) (fun _ => 0) ∧ μ.pos = m.pos) m := by
    refine (writes_fill (N := 2 * (n + 1)) rfl (fun _ => M.lit 0) (fun _ => m.pos) rfl
      (fun q hq μ hfr _ hp => ?_)).mono le_rfl ?_
    · refine (writes_call_const (hS (.lit 0)) (z := (v.1, v.2 + q)) rfl trivial
        (by dsimp; rw [hfr.len_eq]; omega)).mono le_rfl ?_
      intro μ' _ ⟨hp', hget⟩
      exact ⟨hget, hp'.trans hp⟩
    · intro μ _ ⟨hget, hp⟩
      have hz : M.lit 0 = 0 := by simpa using hE.lit 0
      exact ⟨by simpa only [hz] using hget, hp⟩
  refine hzero.seq_le le_rfl ?_
  intro μ hfr ⟨hzeros, hp⟩
  refine (writes_call_const (hS (.lit 1)) (z := (v.1, v.2 + 2 * n)) rfl trivial
    (by dsimp; rw [hfr.len_eq]; omega)).mono (Fp.inBlock_le_inBlock (by omega) (by omega)) ?_
  intro μ' hlast ⟨hp', hone⟩
  have hOne : M.lit 1 = 1 := by simpa using hE.lit 1
  refine ⟨hp'.trans hp, ?_⟩
  apply HoldsVector.of_get
  · intro i
    by_cases hi : i = Fin.last n
    · subst i
      simpa [hOne] using hone
    have hval : (i : ℕ) ≠ n := fun he => hi (Fin.ext he)
    have hget := (hlast.get_eq (b := v.1) (i := v.2 + 2 * i)
      (by rintro ⟨_, hlo, hhi⟩; omega)).trans (hzeros (2 * i) (by omega))
    simpa [Pi.single_apply, hi] using hget
  · intro i
    have hget := (hlast.get_eq (b := v.1) (i := v.2 + 2 * i + 1)
      (by rintro ⟨_, hlo, hhi⟩; omega)).trans (hzeros (2 * i + 1) (by omega))
    by_cases hi : i = Fin.last n
    · subst i
      simpa using hget
    · simpa [Pi.single_apply, hi] using hget

/-- Compute the scalar norm of the actual vector words and square its retained scratch word. -/
def vectorNormSquared : Impl Op Tst := opsImpl% [n] (V, T) → (Norm) {
  run matrixNorm.body [n, 1] (V, T);
  call (Has.inj ScalarOp.mul) [] (T, T) → (Norm)
}

/-- The existing real-word norm lowering and one multiplication return the squared complex
Euclidean norm. The supplied scratch view is separate from the vector. -/
theorem vectorNormSquared_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) {τ : Tape ℝ} {m : Mem ℝ}
    {n : ℕ} {v t z : ℕ × ℕ} {w : Fin n → ℂ}
    (hl : m.Live [v, t, z]) (hV : HoldsVector v w m.store)
    (htv : t.1 ≠ v.1)
    (ht : t.2 + 3 ≤ m.store.len t.1) (hz : z.2 + 1 ≤ m.store.len z.1) :
    Writes .total I τ vectorNormSquared.body (Env.frame [n] [v, t, z])
      (Store.inBlock t.1 t.2 3 ⊔ Store.inBlock z.1 z.2 1)
      (fun μ => μ.pos = m.pos ∧ μ.store.get z.1 z.2 = some (‖WithLp.toLp 2 w‖ ^ 2)) m := by
  have hlive : v.1 < m.store.length ∧ t.1 < m.store.length ∧ z.1 < m.store.length := by
    simpa [Mem.Live] using hl
  have hn := matrixNorm_writes (τ := τ) hS hE (by simp [Mem.Live]; omega) hV
    (by omega) htv.symm
  refine hn.frame_seq_le rfl rfl (by simp [Mem.Live]; omega) (by fp_sub) ?_
  intro μ hfr ⟨hp, hnorm⟩
  refine (writes_call_bin (hS .mul) (x := t) (y := t) (z := z)
    rfl rfl trivial hnorm hnorm rfl
    (fun _ => ⟨by simp [Mem.Live, hfr.length_eq]; omega,
      by rw [hfr.len_eq]; omega⟩)).mono le_sup_right ?_
  intro μ' _ ⟨hp', hout⟩
  have hnormsq : frobNorm (vectorColumn w) ^ 2 = ‖WithLp.toLp 2 w‖ ^ 2 := by
    simp [frobNorm_sq_eq_sum, vectorColumn, EuclideanSpace.norm_sq_eq]
  have hm : M.mul (frobNorm (vectorColumn w)) (frobNorm (vectorColumn w)) =
      ‖WithLp.toLp 2 w‖ ^ 2 := by
    simpa only [id_eq, ← pow_two, hnormsq] using
      hE.mul (frobNorm (vectorColumn w)) (frobNorm (vectorColumn w))
  exact ⟨hp'.trans hp, hm ▸ hout⟩

end NLAlib.ShiftedQR
