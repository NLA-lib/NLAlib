/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.RoundedRun

/-!
# All rounded reorthogonalized Lanczos rounds with safe early exit

An exact comparison of the actual rounded self-dot controls continuation. Every active round
extends the same actual numerical history; an early exit has a zero last coupling. Initialized
padding remains storage, never additional steps of a positive-length run.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Rounded.rounds_writes`: complete capped rounded loop.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Rounded

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- The whole capped loop succeeds from its derived initial state, including zero cap, zero
input and a terminal last coefficient. No future nonbreakdown premise is used. -/
theorem rounds_writes {M : Machine K} {dec : K → ℝ} {n cap L B V C bo vo co : ℕ}
    {em u E : ℝ} {e : Blas1Err} {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ}
    {I : Interp Op Tst K} {ok : ℕ → Prop} {z : Lanczos.Rounded.Values n} {nus : ℕ → ℝ}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec e ok I)
    (hok : ok n) (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
    (hprec : Lanczos.Rounded.Precision em u E e n)
    {τ : Tape K} {μ : Mem K}
    (hVL : V < L) (hCL : C < L) (hVC : V ≠ C)
    (hlen : μ.store.length = L + 3) (hp : μ.store.len L = n)
    (hw : μ.store.len (L + 1) = n) (ht : μ.store.len (L + 2) = 2)
    (hv : vo + (cap + 1) * n ≤ μ.store.len V)
    (hc : co + 3 * cap + 2 ≤ μ.store.len C)
    (hs : State dec A rhs em u E e cap 0 (V, vo) (C, co) L z nus μ.store) :
    Writes .total I τ rounds ⟨[n, cap, bo, vo, co], [B, V, C, L, L + 1, L + 2]⟩
      (Fp.blocks [(V, vo), (C, co)] [(cap + 1) * n, 3 * cap + 2] ⊔ Fp.above L)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ done ≤ cap, ∃ z' nus',
        Prefix dec A rhs em u E e cap done (V, vo) (C, co) z' nus' μ'.store ∧
        (done < cap → (if done = 0 then z'.initialNorm else z'.beta done) = 0)) μ := by
  let F := Fp.blocks [(V, vo), (C, co)] [(cap + 1) * n, 3 * cap + 2] ⊔ Fp.above L
  let Inv := fun i (m : Mem K) => m.pos = μ.pos ∧ ∃ z nus,
    State dec A rhs em u E e cap i (V, vo) (C, co) L z nus m.store
  refine (writes_whileFuel rfl (fun _ => F) (fun _ _ => le_rfl) ⊥ Inv _
    ⟨rfl, z, nus, hs⟩ ?_ ?_).mono (by simp [F]) (fun _ _ h => h)
  · rintro i hi m hfr ⟨hpos, z, nus, hstate⟩
    obtain ⟨sigma, hsig, _, hiff⟩ := hstate.guard
    refine ⟨_, (Interp.testAt_eq rfl rfl).trans (hCmp.test_isPos hsig), ?_⟩
    by_cases hactive : 0 < dec sigma
    · simp only [hactive, decide_true, ite_true]
      have hcol := Idx.mul_add_le_mul (show i + 1 < cap + 1 by omega) n
      refine (advance_state_writes hS hM hB hok hA hCmp hprec hi hVL hCL hVC
        (by simpa only [hfr.length_eq] using hlen)
        (by simpa only [hfr.len_eq] using hp) (by simpa only [hfr.len_eq] using hw)
        (by simpa only [hfr.len_eq] using ht) (by simpa only [hfr.len_eq] using hv)
        (by simpa only [hfr.len_eq] using hc) hstate (hiff.mp hactive)).mono
          (by dsimp [Reorth.advanceFp, Lanczos.advanceFp, F]; fp_sub) ?_
      rintro m' _ ⟨hpos', z', nus', hs'⟩
      exact ⟨hpos'.trans hpos, z', nus', hs'⟩
    · simp only [hactive, decide_false, Bool.false_eq_true, ite_false]
      have hzero := not_ne_iff.mp (mt hiff.mpr hactive)
      exact Writes.skip ⟨hpos, i, Nat.le_of_lt hi, z, nus, hstate.toPrefix, fun _ => hzero⟩
  · rintro m _ ⟨hpos, z, nus, hstate⟩
    exact Writes.skip ⟨hpos, cap, le_rfl, z, nus, hstate.toPrefix, by omega⟩

end NLAlib.Krylov.Lanczos.Reorth.Rounded
