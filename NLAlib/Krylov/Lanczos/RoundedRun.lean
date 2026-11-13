/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedAdvance
public import NLAlib.Krylov.Lanczos.RoundedRecurrence

/-!
# Actual rounded Lanczos steps extend the same archived run

Every active round derives its local defects, including the rounded matrix-vector product,
from primitive contracts. The initial direction and every archived output remain attached to
the same numerical run. The last coefficient may be zero; another step then cannot be appended.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.advance_state_writes`: actual complete round and run extension.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- A positive squared-norm guard permits an actual next step and extends precisely the active
run. Initialized tails remain zero, including a zero last direction after terminal breakdown. -/
theorem advance_state_writes {M : Machine K} {dec : K → ℝ} {n cap done L B V C bo vo co : ℕ}
    {em u E : ℝ} {e : Blas1Err} {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ}
    {I : Interp Op Tst K} {ok : ℕ → Prop} {z : Values n}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec e ok I)
    (hok : ok n) (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
    (hAT : Aᵀ = A) (hprec : Precision em u E e n)
    {τ : Tape K} {μ : Mem K} (hd : done < cap)
    (hVL : V < L) (hCL : C < L) (hVC : V ≠ C)
    (hlen : μ.store.length = L + 3) (hp : μ.store.len L = n)
    (hw : μ.store.len (L + 1) = n) (ht : μ.store.len (L + 2) = 2)
    (hv : vo + (cap + 1) * n ≤ μ.store.len V)
    (hc : co + 2 * cap + 2 ≤ μ.store.len C)
    (hs : State dec A rhs E cap done (V, vo) (C, co) L z μ.store)
    (hactive : (if done = 0 then z.initialNorm else z.beta done) ≠ 0) :
    Writes .total I τ advance ⟨[n, cap, bo, vo, co, done], [B, V, C, L, L + 1, L + 2]⟩
      (advanceFp n cap done L (V, vo) (C, co))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ z', State dec A rhs E cap (done + 1)
        (V, vo) (C, co) L z' μ'.store) μ := by
  obtain ⟨ps, hps, hpvec⟩ := hs.prev
  obtain ⟨qs, hqs, hqvec⟩ := hs.packed.basis done le_rfl
  obtain ⟨β, hβ, hbvec⟩ := hs.packed.beta done le_rfl
  obtain ⟨next, hnext, hnextzero⟩ := hs.packed.basis_zero (done + 1) (by omega) (by omega)
  obtain ⟨β₀, hβ₀, hβzero⟩ := hs.packed.beta_zero (done + 1) (by omega) (by omega)
  have hcol := Idx.mul_add_le_mul (show done + 1 < cap + 1 by omega) n
  refine (advance_writes hS hM hprec.scalar_lt hprec.dot_lt hB hok hA hCmp hVL hCL hVC
    hlen hp hw ht (by omega) (by omega) (by omega) hps hqs
    (by simpa only [Nat.add_assoc] using hβ) hnext
    (by simpa only [Nat.add_assoc] using hβ₀) hnextzero hβzero).mono le_rfl ?_
  rintro μ' hfr ⟨hpos, first, raw, ys, a, b, sigma, hprev, hys, ha, hb, hsig,
    hbounds, hnorm, hscaled, hzero, hdot⟩
  have hbounds' : UpdateBounds em (e.dot n) e.axpy A (z.v done) (z.v (done + 1))
      (decv dec n first) (decv dec n raw) (z.beta done) (dec a) := by
    simpa only [hpvec, hqvec, hbvec] using hbounds
  obtain ⟨hbn, hdefect, hunit⟩ := hprec.norm_bounds hnorm hscaled
  have hrun := hs.exists_run_next hAT hprec hactive hbounds' hdefect hbn hunit
  have hguard := hprec.guard_iff hnorm hdot
  have hnext0 : dec b = 0 → decv dec n ys = 0 := by
    intro hb0
    apply hzero
    by_contra hne
    exact (hnorm.dec_pos_of_ne_zero hprec.dot_lt hprec.scalar_lt hne).ne' hb0
  refine ⟨hpos, z.next done (decv dec n ys) (dec a) (dec b), ⟨⟨⟨hs.norm_nonneg,
    ?_, hs.norm_zero, ?_, ?_, ?_, ?_, ?_, Or.inr hrun⟩, ?_⟩, ?_, ?_⟩⟩
  · simpa only [Values.next, Function.update_of_ne (show 1 ≠ done + 2 by omega)] using
      hs.initial_error
  · simpa only [Values.next, Function.update_of_ne (show 1 ≠ done + 2 by omega)] using
      hs.initial_unit
  · simpa only [Values.next, Function.update_of_ne (show 1 ≠ done + 2 by omega)] using
      hs.initial_zero
  · intro j hj
    simpa only [Values.next, Function.update_of_ne (show j ≠ done + 2 by omega)] using
      hs.future_v j (by omega)
  · intro j hj
    simpa only [Values.next, Function.update_of_ne (show j ≠ done + 1 by omega)] using
      hs.future_coeff j (by omega)
  · intro hb0
    right
    have hb0' : dec b = 0 := by simpa only [Values.next, Function.update_self] using hb0
    simpa only [Values.next, show done + 1 + 1 = done + 2 by omega,
      Function.update_self] using hnext0 hb0'
  · exact hs.packed.advance hd hVC hVL hCL hfr ⟨ys, hys, rfl⟩ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  · refine ⟨qs, hprev, ?_⟩
    simpa only [Values.next, Function.update_of_ne (show done + 1 ≠ done + 2 by omega)] using
      hqvec
  · refine ⟨sigma, hsig, hguard.1, ?_⟩
    simpa only [if_neg (show done + 1 ≠ 0 by omega), Values.next, Function.update_self] using
      hguard.2

end NLAlib.Krylov.Lanczos.Rounded
