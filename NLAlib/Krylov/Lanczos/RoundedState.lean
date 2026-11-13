/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedPrecision
public import NLAlib.Krylov.Lanczos.State
public import NLAlib.Krylov.FinitePrecision.LanczosRun

/-!
# Actual stored prefixes of rounded Lanczos

A packed prefix records every requested basis/coefficient cell, including its initialized zero
tail. The active run has exactly the number of executed rounds. Initial normalization remains
attached to the actual right-hand side rather than an assumed exact direction.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.Packed.advance`: one round preserves the complete archive.
* `NLAlib.Krylov.Lanczos.Rounded.State.abs_norm_sq_sub_one_le`: active directions
  are derived nearly unit.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops

/-- Mathematical names of the physically archived basis and coefficients. -/
structure Values (n : ℕ) where
  /-- Basis vectors, with index one for the first direction. -/
  v : ℕ → Fin n → ℝ
  /-- Diagonal coefficients, starting at one. -/
  alpha : ℕ → ℝ
  /-- Coupling coefficients, with beta zero at index zero. -/
  beta : ℕ → ℝ
  /-- Computed initial norm. -/
  initialNorm : ℝ

/-- Extend the mathematical names at exactly the cells written by the next round. -/
noncomputable def Values.next {n : ℕ} (z : Values n) (done : ℕ)
    (q : Fin n → ℝ) (a b : ℝ) : Values n :=
  ⟨Function.update z.v (done + 2) q, Function.update z.alpha (done + 1) a,
    Function.update z.beta (done + 1) b, z.initialNorm⟩

variable {K : Type} [Inhabited K]

/-- Full initialized output storage, separating active entries from zero tails. -/
structure Packed (dec : K → ℝ) {n : ℕ} (cap done : ℕ) (V C : ℕ × ℕ)
    (z : Values n) (s : Store K) : Prop where
  /-- Actual basis prefix. -/
  basis : ∀ j ≤ done, StoresVec dec (V.1, V.2 + j * n) (z.v (j + 1)) s
  /-- Initialized basis tail. -/
  basis_zero : ∀ j, done < j → j ≤ cap → StoresVec dec (V.1, V.2 + j * n) (0 : Fin n → ℝ) s
  /-- Actual diagonal prefix. -/
  alpha : ∀ j < done, StoresCell dec (C.1, C.2 + j) (z.alpha (j + 1)) s
  /-- Initialized diagonal tail. -/
  alpha_zero : ∀ j, done ≤ j → j < cap → StoresCell dec (C.1, C.2 + j) 0 s
  /-- Actual coupling prefix, including beta zero. -/
  beta : ∀ j ≤ done, StoresCell dec (C.1, C.2 + (cap + j)) (z.beta j) s
  /-- Initialized coupling tail. -/
  beta_zero : ∀ j, done < j → j ≤ cap → StoresCell dec (C.1, C.2 + (cap + j)) 0 s
  /-- Actual initial norm. -/
  initialNorm : StoresCell dec (C.1, C.2 + (2 * cap + 1)) z.initialNorm s

/-- An arbitrary round footprint preserves the archive when it is disjoint from every
unchanged basis and ordinary coefficient entry. Extra suffix writes are permitted. -/
theorem Packed.advance_of_disjoint {dec : K → ℝ} {n cap done : ℕ} {V C : ℕ × ℕ}
    {z : Values n} {s s' : Store K} (h : Packed dec cap done V C z s)
    (hd : done < cap) {F : Fp} (hf : s.EqOff F s')
    (hFb : ∀ j, j ≠ done + 1 →
      Fp.Disj F (Store.inBlock V.1 (V.2 + j * n) n))
    (hFc : ∀ i, i < 2 * cap + 2 → i ≠ done → i ≠ cap + done + 1 →
      Fp.Disj F (Store.inBlock C.1 (C.2 + i) 1))
    {q : Fin n → ℝ} {a b : ℝ}
    (hq : StoresVec dec (V.1, V.2 + (done + 1) * n) q s')
    (ha : StoresCell dec (C.1, C.2 + done) a s')
    (hb : StoresCell dec (C.1, C.2 + cap + done + 1) b s') :
    Packed dec cap (done + 1) V C (z.next done q a b) s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases he : j = done + 1
    · subst j; simpa [Values.next, Nat.add_assoc] using hq
    · have hj' : j ≤ done := by omega
      simpa only [Values.next, Function.update_of_ne (show j + 1 ≠ done + 2 by omega)] using
        (h.basis j hj').keep hf (hFb j he)
  · intro j hj hcap
    exact (h.basis_zero j (by omega) hcap).keep hf (hFb j (by omega))
  · intro j hj
    by_cases he : j = done
    · subst j; simpa [Values.next] using ha
    · have hj' : j < done := by omega
      simpa only [Values.next, Function.update_of_ne (show j + 1 ≠ done + 1 by omega)] using
        (h.alpha j hj').keep hf (hFc j (by omega) he (by omega))
  · intro j hj hcap
    exact (h.alpha_zero j (by omega) hcap).keep hf
      (hFc j (by omega) (by omega) (by omega))
  · intro j hj
    by_cases he : j = done + 1
    · subst j; simpa [Values.next, Nat.add_assoc] using hb
    · have hj' : j ≤ done := by omega
      simpa only [Values.next, Function.update_of_ne he] using
        (h.beta j hj').keep hf
          (hFc (cap + j) (by omega) (by omega) (by omega))
  · intro j hj hcap
    exact (h.beta_zero j (by omega) hcap).keep hf
      (hFc (cap + j) (by omega) (by omega) (by omega))
  · exact h.initialNorm.keep hf
      (hFc (2 * cap + 1) (by omega) (by omega) (by omega))

/-- A round changes only the next basis/diagonal/coupling entries and scratch. The same
footprint rule preserves initialized tails and arbitrary old mathematical values. -/
theorem Packed.advance {dec : K → ℝ} {n cap done L : ℕ} {V C : ℕ × ℕ}
    {z : Values n} {s s' : Store K} (h : Packed dec cap done V C z s)
    (hd : done < cap) (hvc : V.1 ≠ C.1) (hv : V.1 < L) (hc : C.1 < L)
    (hf : s.EqOff (advanceFp n cap done L V C) s')
    {q : Fin n → ℝ} {a b : ℝ}
    (hq : StoresVec dec (V.1, V.2 + (done + 1) * n) q s')
    (ha : StoresCell dec (C.1, C.2 + done) a s')
    (hb : StoresCell dec (C.1, C.2 + cap + done + 1) b s') :
    Packed dec cap (done + 1) V C (z.next done q a b) s' := by
  exact h.advance_of_disjoint hd hf
    (fun _ he => advanceFp_disj_basis hvc hv he)
    (fun _ _ ha hb => advanceFp_disj_coeff hvc hc ha hb) hq ha hb

/-- The numerical meaning of an active prefix, independently of its storage representation. -/
structure Outcome {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (rhs : Fin n → ℝ)
    (E : ℝ) (done : ℕ) (z : Values n) : Prop where
  /-- The computed initial norm is nonnegative. -/
  norm_nonneg : 0 ≤ z.initialNorm
  /-- Initial normalization error relative to the actual input. -/
  initial_error : ‖WithLp.toLp 2 (rhs - z.initialNorm • z.v 1)‖ ≤ E * ‖WithLp.toLp 2 rhs‖
  /-- The initial norm detects zero input. -/
  norm_zero : z.initialNorm = 0 ↔ rhs = 0
  /-- Initial near-unit direction follows from normalization when the input is nonzero. -/
  initial_unit : z.initialNorm ≠ 0 → |‖WithLp.toLp 2 (z.v 1)‖ ^ 2 - 1| ≤ E
  /-- Zero input has an actually zero initial direction. -/
  initial_zero : rhs = 0 → z.v 1 = 0
  /-- Ghost basis values beyond the active prefix are zero, matching initialized padding. -/
  future_v : ∀ j, done + 1 < j → z.v j = 0
  /-- Ghost coefficients beyond the active prefix are zero. -/
  future_coeff : ∀ j, done < j → z.alpha j = 0 ∧ z.beta j = 0
  /-- A terminal coupling has a physically zero next direction. -/
  terminal_zero : z.beta done = 0 → done = 0 ∨ z.v (done + 1) = 0
  /-- Either the initialized zero-step prefix, or the same positive-length existing run. -/
  run : (done = 0 ∧ z.v = Function.update (0 : ℕ → Fin n → ℝ) 1 (z.v 1) ∧
      z.alpha = 0 ∧ z.beta = 0) ∨
    ∃ R : LanczosRun n done, R.H = A ∧ R.ε = E ∧
      R.v = z.v ∧ R.α = z.alpha ∧ R.β = z.beta

/-- Numerical prefix and all its physically archived output cells. -/
structure Prefix (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (rhs : Fin n → ℝ)
    (E : ℝ) (cap done : ℕ) (V C : ℕ × ℕ) (z : Values n) (s : Store K)
    extends Outcome A rhs E done z where
  /-- Every requested output cell is physically accounted for. -/
  packed : Packed dec cap done V C z s

/-- Prefix plus the previous-vector scratch and the actual squared-norm continuation guard. -/
structure State (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (rhs : Fin n → ℝ)
    (E : ℝ) (cap done : ℕ) (V C : ℕ × ℕ) (L : ℕ) (z : Values n) (s : Store K)
    extends Prefix dec A rhs E cap done V C z s where
  /-- Previous physical direction. -/
  prev : StoresVec dec (L, 0) (z.v done) s
  /-- Positivity means the initial norm or the latest coupling is nonzero. -/
  guard : ∃ sigma, s.get (L + 2) 0 = some sigma ∧ 0 ≤ dec sigma ∧
    (0 < dec sigma ↔ (if done = 0 then z.initialNorm else z.beta done) ≠ 0)

/-- A continuing state has a nearly unit current vector, including the first round. -/
theorem State.abs_norm_sq_sub_one_le {dec : K → ℝ} {n cap done L : ℕ} {V C : ℕ × ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {E : ℝ} {z : Values n} {s : Store K}
    (h : State dec A rhs E cap done V C L z s)
    (ha : (if done = 0 then z.initialNorm else z.beta done) ≠ 0) :
    |‖WithLp.toLp 2 (z.v (done + 1))‖ ^ 2 - 1| ≤ E := by
  rcases h.run with ⟨rfl, _, _, _⟩ | ⟨R, _, he, hv, _, hb⟩
  · exact h.initial_unit (by simpa using ha)
  · have hd : done ≠ 0 := Nat.ne_of_gt R.k_pos
    rw [if_neg hd] at ha
    simpa only [he, hv] using R.abs_norm_v_succ_sq_sub_one_le (by rwa [hb])

end NLAlib.Krylov.Lanczos.Rounded
