/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.Reorth.Advance

/-!
# Capped full-reorthogonalized CG with successful early convergence

The invariant contains the exact CG state, its initialized residual history, and the retained
residual self-product. Positive definiteness rules out active breakdown. A zero residual exits
before the next round, so the cap can exceed the Krylov grade.

## Main results

* `NLAlib.Krylov.CG.Reorth.rounds_writes`: total execution at every cap.
-/

@[expose] public section

namespace NLAlib.Krylov.CG.Reorth

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- Any cap terminates at the smaller of the cap and grade, including initially solved inputs. -/
theorem rounds_writes {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec (fun _ => True) I)
    {n cap L : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsExactMatvec dec A I)
    (hCmp : IsCmp dec I) (hPos : A.PosDef) {τ : Tape K} {μ : Mem K}
    {b x r p : ℕ × ℕ} {bs x₀ : Fin n → ℝ}
    (hxr : x.1 ≠ r.1) (hxp : x.1 ≠ p.1) (hrp : r.1 ≠ p.1)
    (hxL : x.1 < L) (hrL : r.1 < L) (hpL : p.1 < L)
    (hl : μ.store.length = L + 2) (hQ : μ.store.len L = cap * n)
    (hv : μ.store.len (L + 1) = 1) (hz : μ.Room [x, r, p] [n, n, n])
    (hs : HSCG.StoresState dec n x r p (cgState A bs x₀ 0) μ)
    (hrho : ∃ rr, μ.store.get (L + 1) 0 = some rr ∧
      dec rr = (cgState A bs x₀ 0).r ⬝ᵥ (cgState A bs x₀ 0).r) :
    Writes .total I τ rounds
      ⟨[n, cap, b.2, x.2, x.2, r.2, p.2], [b.1, x.1, x.1, r.1, p.1, L, L + 1]⟩
      (Fp.blocks [x, r, p] [n, n, n] ⊔ Fp.above L)
      (fun μ' => μ'.pos = μ.pos ∧ HSCG.StoresState dec n x r p
        (cgState A bs x₀ (min cap (krylovGrade A (bs - A *ᵥ x₀)))) μ') μ := by
  classical
  let grade := krylovGrade A (bs - A *ᵥ x₀)
  let F := Fp.blocks [x, r, p] [n, n, n] ⊔ Fp.above L
  let Inv := fun i μ' => μ'.pos = μ.pos ∧ i ≤ grade ∧
    HSCG.StoresState dec n x r p (cgState A bs x₀ i) μ' ∧
    StoresHistory dec n (L, 0) (fun j => (cgState A bs x₀ j).r) i μ' ∧
    ∃ rr, μ'.store.get (L + 1) 0 = some rr ∧
      dec rr = (cgState A bs x₀ i).r ⬝ᵥ (cgState A bs x₀ i).r
  refine Writes.mono (writes_whileFuel rfl (fun _ => F) (fun _ _ => le_rfl) ⊥ Inv _
    ⟨rfl, Nat.zero_le _, hs, storesHistory_zero _ _ _ _ _, hrho⟩ ?_ ?_)
    (by simp [F]) (fun _ _ h => h)
  · intro i hi μ' hfr ⟨hpos, hig, hstate, hhist, rr, hrr, hrrd⟩
    refine ⟨_, (Interp.testAt_eq rfl rfl).trans (hCmp.test_isPos hrr), ?_⟩
    by_cases ha : 0 < dec rr
    · simp only [ha, decide_true, ite_true]
      have hrne : (cgState A bs x₀ i).r ≠ 0 := by
        intro hzero
        rw [hzero, zero_dotProduct] at hrrd
        exact ha.ne' hrrd
      have hig' : i < grade := Nat.lt_of_not_ge fun h =>
        hrne ((hPos.cgState_r_eq_zero_iff bs x₀ i).mpr h)
      refine (advance_writes hS hM hB hA hPos hi hig' hxr hxp hrp hxL hrL hpL
        (by rw [hfr.length_eq]; exact hl) (by rw [hfr.len_eq]; exact hQ)
        (by rw [hfr.len_eq]; exact hv) (by simpa [Mem.Room, hfr.len_eq] using hz)
        hstate hhist).mono le_rfl ?_
      rintro μ'' _ ⟨hpos', hstate', hhist', hrho'⟩
      exact ⟨hpos'.trans hpos, Nat.succ_le_of_lt hig', hstate', hhist', hrho'⟩
    · simp only [ha, decide_false, Bool.false_eq_true, ite_false]
      have hnonneg : 0 ≤ (cgState A bs x₀ i).r ⬝ᵥ (cgState A bs x₀ i).r :=
        Finset.sum_nonneg fun _ _ => mul_self_nonneg _
      have hrzero : (cgState A bs x₀ i).r = 0 :=
        dotProduct_self_eq_zero.mp (by linarith)
      have hgi : grade ≤ i := (hPos.cgState_r_eq_zero_iff bs x₀ i).mp hrzero
      have hmin : min cap grade = i := by omega
      exact Writes.skip ⟨hpos, hmin.symm ▸ hstate⟩
  · intro μ' _ ⟨hpos, hcap, hstate, _⟩
    exact Writes.skip ⟨hpos, (Nat.min_eq_left hcap).symm ▸ hstate⟩

end NLAlib.Krylov.CG.Reorth
