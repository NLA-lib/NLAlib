/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedAdvance
public import NLAlib.Krylov.Lanczos.RoundedBounds
public import NLAlib.Krylov.Processes.LanczosProgramRoundedRun

/-!
# Actual rounded Lanczos execution as an established finite-precision run

The imported run constructor is pure numerical mathematics: its only dependency is the
existing `LanczosRun` record. The execution proof here uses Ops throughout. Actual dot, axpy,
norm and reciprocal-scaling contracts imply the constructor's local-error premises.

This first-step bridge permits terminal breakdown. It assumes a nearly unit input direction
and explicit primitive-error budgets; it does not claim a whole rounded solver transfer.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.first_round_writes` returns an actual `LanczosRun n 1`.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- Explicit input direction and primitive precision bounds suffice for successful execution
of the first rounded Paige round and an existing LanczosRun tied to its computed output.
The new coefficient may be zero; its vector is required nearly unit only when it is nonzero. -/
theorem first_round_writes {M : Machine K} {dec : K → ℝ} {n cap L B V C bo vo co : ℕ}
    {u E : ℝ} {ε : Blas1Err} {A : Matrix (Fin n) (Fin n) ℝ}
    {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec ε ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I)
    (hSymm : Aᵀ = A) (hE : 0 ≤ E) (hsmall : E ≤ 1 / 100)
    (hed : 0 ≤ ε.dot n) (hu : 0 ≤ u) (hea : 0 ≤ ε.axpy) (hec : 0 ≤ ε.scal)
    (hg : ε.dot n + u * (1 + ε.dot n) < 1)
    (hEa : ε.axpy ≤ E) (hEd : ε.dot n ≤ E) (hEc : ε.scal ≤ E)
    (hEu : let g := ε.dot n + u * (1 + ε.dot n)
      let t := (ε.scal + g) / (1 - g); t * (2 + t) ≤ E)
    {τ : Tape K} {μ : Mem K} {ps qs next : List K} {β β₀ : K}
    (hVL : V < L) (hCL : C < L) (hVC : V ≠ C)
    (hlen : μ.store.length = L + 3) (hp : μ.store.len L = n)
    (hw : μ.store.len (L + 1) = n) (ht : μ.store.len (L + 2) = 2)
    (ha : co < μ.store.len C) (hb : co + cap + 1 < μ.store.len C)
    (hnroom : vo + n + n ≤ μ.store.len V)
    (hps : μ.store.readBlock L 0 n = some ps)
    (hqs : μ.store.readBlock V vo n = some qs)
    (hβ : μ.store.get C (co + cap) = some β) (hβzero : dec β = 0)
    (hnext : μ.store.readBlock V (vo + n) n = some next)
    (hβ₀ : μ.store.get C (co + cap + 1) = some β₀)
    (hnextzero : decv dec n next = 0) (hβ₀zero : dec β₀ = 0)
    (hq : |‖WithLp.toLp 2 (decv dec n qs)‖ ^ 2 - 1| ≤ E) :
    Writes .total I τ advance ⟨[n, cap, bo, vo, co, 0], [B, V, C, L, L + 1, L + 2]⟩
      (advanceFp n cap 0 L (V, vo) (C, co))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys α β', ∃ R : LanczosRun n 1,
        μ'.store.readBlock V (vo + n) n = some ys ∧
        μ'.store.get C co = some α ∧ μ'.store.get C (co + cap + 1) = some β' ∧
        R.H = A ∧ R.ε = E ∧ R.v 1 = decv dec n qs ∧ R.v 2 = decv dec n ys ∧
        R.α 1 = dec α ∧ R.β 1 = dec β') μ := by
  have hd1 : ε.dot n < 1 := by
    nlinarith [mul_nonneg hu (by linarith : 0 ≤ 1 + ε.dot n)]
  have hu1 : u < 1 := by nlinarith [mul_nonneg hu hed]
  refine (advance_writes (j := 0) hS hM hu1 hd1 hB hok hA hCmp hVL hCL hVC
    hlen hp hw ht (by simpa using ha) (by simpa using hb) (by simpa using hnroom)
    hps (by simpa using hqs) (by simpa using hβ) (by simpa using hnext)
    (by simpa using hβ₀) hnextzero hβ₀zero).mono le_rfl ?_
  rintro μ' _ ⟨hpos, first, raw, ys, α, β', σ, _, hys, hα, hβ', _, hbounds,
    hnorm, hscaled, _, _⟩
  have hwbound := norm_sub_add_smul_le_of_componentwise (a := (0 : ℝ))
    (x := decv dec n ps) (y := A *ᵥ decv dec n qs) (z := decv dec n first) hea
    (fun i => by simpa [hβzero, abs_sub_comm] using hbounds.1 i)
  simp only [zero_smul, add_zero, abs_zero, zero_mul] at hwbound
  have hzbound := norm_sub_add_smul_le_of_componentwise (a := -dec α)
    (x := decv dec n qs) (y := decv dec n first) (z := decv dec n raw) hea
    (fun i => by
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul,
        abs_neg, ← sub_eq_add_neg]
      simpa only [abs_sub_comm] using hbounds.2.2 i)
  have habound := abs_dotProduct_sub_le_of_componentwise
    (x := decv dec n qs) (y := decv dec n first) (α := dec α) hed
    (by simpa only [abs_sub_comm] using hbounds.2.1)
  obtain ⟨hβnonneg, hδ, hunit⟩ := nrm2_scal_bounds hed hu hec hnorm hscaled hg
  obtain ⟨R, hH, hε, hv, hαR, hβR⟩ := LanczosImplementation.exists_lanczosRun_one A hSymm
    E hE hsmall (decv dec n qs) (A *ᵥ decv dec n qs) (decv dec n first)
    (decv dec n raw) (decv dec n ys) (dec α) (dec β') hq
    (by simp only [sub_self, WithLp.toLp_zero, norm_zero]; positivity)
    (by simpa using hwbound.trans (mul_le_mul_of_nonneg_right hEa (norm_nonneg _)))
    (habound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hEd (norm_nonneg _)) (norm_nonneg _)))
    (by simpa only [neg_smul, ← sub_eq_add_neg, abs_neg] using
      (hzbound.trans (mul_le_mul_of_nonneg_right hEa (by positivity))))
    (hδ.trans (mul_le_mul_of_nonneg_right hEc (norm_nonneg _))) hβnonneg
    (fun hb => (hunit hb).trans hEu)
  refine ⟨hpos, ys, α, β', R, by simpa using hys,
    by simpa using hα, by simpa using hβ', hH, hε, ?_, ?_, ?_, ?_⟩
  · simp [hv]
  · simp [hv]
  · simp [hαR]
  · simp [hβR]

end NLAlib.Krylov.Lanczos.Rounded
