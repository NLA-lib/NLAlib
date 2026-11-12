/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.RoundedState

/-!
# Reading executed rounded reorthogonalized steps from the final history

Each local numerical transition is exposed against the final archived basis and coefficient
sequences. Later rounds preserve every argument used by an earlier transition. Analyses can
therefore consume the completed output without reconstructing execution or intermediate stores.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Rounded.Local.congr`: unchanged archive prefix transport.
* `NLAlib.Krylov.Lanczos.Reorth.Rounded.History.local`: every executed final-archive transition.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Rounded

open Ops

variable {K : Type} [Inhabited K] {dec : K → ℝ} {n : ℕ}
variable {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {em u E : ℝ} {e : Blas1Err}

/-- A numerical transition uses only its current basis prefix and previous coupling. -/
theorem Local.congr {done : ℕ} {z z' : Lanczos.Rounded.Values n}
    {q : Fin n → ℝ} {a b nu : ℝ} (h : Local dec A em u e done z q a b nu)
    (hv : ∀ j ≤ done + 1, z.v j = z'.v j) (hb : z.beta done = z'.beta done) :
    Local dec A em u e done z' q a b nu := by
  obtain ⟨ps, qs, basis, first, raw, reduced, ys, beta, alpha, norm, beta',
    hps, hqs, hbeta, hQ, hq, ha, hbn, hnu, hbounds, hnorm, hpasses, hn, hs, hz⟩ := h
  exact ⟨ps, qs, basis, first, raw, reduced, ys, beta, alpha, norm, beta',
    hps.trans (hv done (by omega)), hqs.trans (hv (done + 1) le_rfl), hbeta.trans hb,
    fun j hj => (hQ j hj).trans (hv (j + 1) (by omega)),
    hq, ha, hbn, hnu, hbounds, hnorm, hpasses, hn, hs, hz⟩

/-- Every executed step has its actual local rounding witnesses expressed using the final
archived basis, alpha, beta and saved raw norm. No successful-execution premise is required. -/
theorem History.local {done : ℕ} {z : Lanczos.Rounded.Values n} {nus : ℕ → ℝ}
    (h : History dec A rhs em u E e done z nus) :
    ∀ j < done, Local dec A em u e j z (z.v (j + 2))
      (z.alpha (j + 1)) (z.beta (j + 1)) (nus (j + 1)) := by
  induction h with
  | initial h => intro j hj; omega
  | @next done z nus q a b nu h hactive hstep ih =>
    intro j hj
    by_cases he : j = done
    · subst j
      have hv : ∀ i ≤ done + 1, z.v i = (z.next done q a b).v i := by
        intro i hi
        simp only [Lanczos.Rounded.Values.next,
          Function.update_of_ne (show i ≠ done + 2 by omega)]
      have hb : z.beta done = (z.next done q a b).beta done := by
        simp only [Lanczos.Rounded.Values.next,
          Function.update_of_ne (show done ≠ done + 1 by omega)]
      simpa only [Lanczos.Rounded.Values.next, Function.update_self] using hstep.congr hv hb
    · have hj' : j < done := by omega
      have hv : ∀ i ≤ j + 1, z.v i = (z.next done q a b).v i := by
        intro i hi
        simp only [Lanczos.Rounded.Values.next,
          Function.update_of_ne (show i ≠ done + 2 by omega)]
      have hb : z.beta j = (z.next done q a b).beta j := by
        simp only [Lanczos.Rounded.Values.next,
          Function.update_of_ne (show j ≠ done + 1 by omega)]
      simpa only [Lanczos.Rounded.Values.next,
        Function.update_of_ne (show j + 2 ≠ done + 2 by omega),
        Function.update_of_ne (show j + 1 ≠ done + 1 by omega)] using (ih j hj').congr hv hb

/-- The original rounded initialization remains attached to the final history, including
the input norm, initial direction, zero previous vector and initial coupling. -/
theorem History.initial_outcome {done : ℕ} {z : Lanczos.Rounded.Values n} {nus : ℕ → ℝ}
    (h : History dec A rhs em u E e done z nus) :
    ∃ initial : Lanczos.Rounded.Values n, Lanczos.Rounded.Outcome A rhs E 0 initial ∧
      z.initialNorm = initial.initialNorm ∧ z.v 0 = initial.v 0 ∧
      z.v 1 = initial.v 1 ∧ z.beta 0 = initial.beta 0 := by
  induction h with
  | initial h => exact ⟨_, h, rfl, rfl, rfl, rfl⟩
  | @next done z nus q a b nu h hactive hstep ih =>
    obtain ⟨initial, hinit, hn, hv0, hv1, hb0⟩ := ih
    refine ⟨initial, hinit, hn, ?_, ?_, ?_⟩
    · simpa only [Lanczos.Rounded.Values.next,
        Function.update_of_ne (show 0 ≠ done + 2 by omega)] using hv0
    · simpa only [Lanczos.Rounded.Values.next,
        Function.update_of_ne (show 1 ≠ done + 2 by omega)] using hv1
    · simpa only [Lanczos.Rounded.Values.next,
        Function.update_of_ne (show 0 ≠ done + 1 by omega)] using hb0

/-- A positive executed history began with a nonzero computed input norm. This follows
from the actual first continuation guard, rather than an assumption on successful execution. -/
theorem History.initialNorm_ne_zero {done : ℕ} {z : Lanczos.Rounded.Values n} {nus : ℕ → ℝ}
    (h : History dec A rhs em u E e done z nus) (hpos : 0 < done) : z.initialNorm ≠ 0 := by
  induction h with
  | initial h => omega
  | @next done z nus q a b nu h hactive hstep ih =>
    by_cases hd : done = 0
    · simpa only [hd, ↓reduceIte, Lanczos.Rounded.Values.next] using hactive
    · exact ih (Nat.pos_of_ne_zero hd)

/-- The actual history retains zero initial previous vector and coupling, and a positive
history has a derived nearly unit first direction. -/
theorem History.initial_data {done : ℕ} {z : Lanczos.Rounded.Values n} {nus : ℕ → ℝ}
    (h : History dec A rhs em u E e done z nus) :
    z.v 0 = 0 ∧ z.beta 0 = 0 ∧
      (0 < done → |‖WithLp.toLp 2 (z.v 1)‖ ^ 2 - 1| ≤ E) := by
  obtain ⟨initial, hi, hn, hv0, hv1, hb0⟩ := h.initial_outcome
  have hz : initial.v 0 = 0 ∧ initial.beta 0 = 0 := by
    rcases hi.run with ⟨_, hv, _, hb⟩ | ⟨R, _⟩
    · rw [hv, hb]
      simp only [Function.update_of_ne (by omega : (0 : ℕ) ≠ 1), Pi.zero_apply,
        and_self]
    · exact (Nat.not_lt_zero _ R.k_pos).elim
  refine ⟨hv0.trans hz.1, hb0.trans hz.2, ?_⟩
  intro hpos
  rw [hv1]
  exact hi.initial_unit (by rw [← hn]; exact h.initialNorm_ne_zero hpos)

end NLAlib.Krylov.Lanczos.Reorth.Rounded
