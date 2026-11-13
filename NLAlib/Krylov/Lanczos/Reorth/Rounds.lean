/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.AdvanceState

/-!
# Successful capped Lanczos rounds with early breakdown

The stored squared-norm guard stops before another round when the current vector is zero.
Initialized output tails then agree with the total pure recurrence. Neither a nonbreakdown
assumption nor a bound on the requested cap is required.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.rounds_writes` returns a complete packed recurrence prefix.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- Every cap executes successfully from an initialized state. Exact breakdown returns the
recurrence's zero tail, including breakdown before the first round. -/
theorem rounds_writes {M : Machine K} {dec : K → ℝ} {n cap L B V C bo vo co : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ}
    {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hAT : A.IsHermitian)
    {τ : Tape K} {μ : Mem K}
    (hVL : V < L) (hCL : C < L) (hVC : V ≠ C)
    (hlen : μ.store.length = L + 3) (hp : μ.store.len L = n)
    (hw : μ.store.len (L + 1) = n) (ht : μ.store.len (L + 2) = 2)
    (hv : vo + (cap + 1) * n ≤ μ.store.len V)
    (hc : co + 3 * cap + 2 ≤ μ.store.len C)
    (hs : State dec A b cap 0 (V, vo) (C, co) L μ.store) :
    Writes .total I τ rounds ⟨[n, cap, bo, vo, co], [B, V, C, L, L + 1, L + 2]⟩
      (Fp.blocks [(V, vo), (C, co)] [(cap + 1) * n, 3 * cap + 2] ⊔ Fp.above L)
      (fun μ' => μ'.pos = μ.pos ∧ Prefix dec A b cap cap (V, vo) (C, co) μ'.store ∧
        ∀ j < cap, StoresCell dec (C, co + 2 * cap + 2 + j) (nuValue A b cap j) μ'.store) μ := by
  let F := Fp.blocks [(V, vo), (C, co)] [(cap + 1) * n, 3 * cap + 2] ⊔ Fp.above L
  let Inv := fun i (μ' : Mem K) => μ'.pos = μ.pos ∧ State dec A b cap i (V, vo) (C, co) L μ'.store
  refine (writes_whileFuel rfl (fun _ => F) (fun _ _ => le_rfl) ⊥ Inv _
    ⟨rfl, hs⟩ ?_ ?_).mono (by simp [F]) (fun _ _ h => h)
  · intro i hi μ' hfr ⟨hpos, hstate⟩
    obtain ⟨σ, hσ, _, hiff⟩ := hstate.guard
    refine ⟨_, (Interp.testAt_eq rfl rfl).trans (hCmp.test_isPos hσ), ?_⟩
    by_cases ha : 0 < dec σ
    · simp only [ha, decide_true, ite_true]
      have hcol : (i + 1) * n + n ≤ (cap + 1) * n :=
        Idx.mul_add_le_mul (by omega) n
      refine (advance_state_writes hS hM hB hok hA hCmp hAT hi hVL hCL hVC
        (by simpa only [hfr.length_eq] using hlen)
        (by simpa only [hfr.len_eq] using hp) (by simpa only [hfr.len_eq] using hw)
        (by simpa only [hfr.len_eq] using ht) (by simpa only [hfr.len_eq] using hv)
        (by simpa only [hfr.len_eq] using hc) hstate).mono
        (by dsimp [advanceFp, Lanczos.advanceFp, F]; fp_sub) ?_
      rintro μ'' _ ⟨hpos', hstate'⟩
      exact ⟨hpos'.trans hpos, hstate'⟩
    · simp only [ha, decide_false, Bool.false_eq_true, ite_false]
      have hz : (lanczosState A b i).cur = 0 := not_ne_iff.mp (mt hiff.mpr ha)
      exact Writes.skip ⟨hpos, hstate.stopped (by omega) hz⟩
  · intro μ' _ ⟨hpos, hstate⟩
    exact Writes.skip ⟨hpos, hstate.toPrefix, hstate.nu⟩

end NLAlib.Krylov.Lanczos.Reorth
