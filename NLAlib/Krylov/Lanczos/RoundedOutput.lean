/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedState

/-!
# Packed outputs of the actual rounded Lanczos run

Every physical basis and coefficient entry agrees with the same numerical prefix. Values
beyond its active length are genuinely initialized zero padding. The input norm and initial
direction mismatch are part of the numerical outcome.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.Prefix.readback`: packed actual outputs.
* `NLAlib.Krylov.Lanczos.Rounded.Output`: numerical outcome and all physical decoded ties.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops

variable {K : Type} [Inhabited K]

/-- Every entry of the two actual packed output blocks has its archived numerical value. -/
structure PackedOutput (dec : K → ℝ) {n : ℕ} (cap : ℕ) (z : Values n)
    (vs cs : List K) : Prop where
  /-- Basis columns, including initialized zeros beyond the active run. -/
  basis : ∀ j ≤ cap, ∀ i : Fin n, dec (vec vs (j * n + i)) = z.v (j + 1) i
  /-- Diagonal coefficients. -/
  alpha : ∀ j < cap, dec (vec cs j) = z.alpha (j + 1)
  /-- Coupling coefficients, including the initial zero. -/
  beta : ∀ j ≤ cap, dec (vec cs (cap + j)) = z.beta j
  /-- Initial computed norm. -/
  initialNorm : dec (vec cs (2 * cap + 1)) = z.initialNorm

/-- Full physical readback follows from the initialized archive and its zero ghost suffix. -/
theorem Prefix.readback {dec : K → ℝ} {n cap done : ℕ} {V C : ℕ × ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {E : ℝ} {z : Values n} {s : Store K}
    (h : Prefix dec A rhs E cap done V C z s) :
    ∃ vs cs, s.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
      s.readBlock C.1 C.2 (2 * cap + 2) = some cs ∧ PackedOutput dec cap z vs cs := by
  have hv : ∀ j ≤ cap, StoresVec dec (V.1, V.2 + j * n) (z.v (j + 1)) s := by
    intro j hj
    by_cases hd : j ≤ done
    · exact h.packed.basis j hd
    · rw [h.future_v (j + 1) (by omega)]
      exact h.packed.basis_zero j (by omega) hj
  have ha : ∀ j < cap, StoresCell dec (C.1, C.2 + j) (z.alpha (j + 1)) s := by
    intro j hj
    by_cases hd : j < done
    · exact h.packed.alpha j hd
    · rw [(h.future_coeff (j + 1) (by omega)).1]
      exact h.packed.alpha_zero j (by omega) hj
  have hb : ∀ j ≤ cap, StoresCell dec (C.1, C.2 + (cap + j)) (z.beta j) s := by
    intro j hj
    by_cases hd : j ≤ done
    · exact h.packed.beta j hd
    · rw [(h.future_coeff j (by omega)).2]
      exact h.packed.beta_zero j (by omega) hj
  have hc : ∀ i < 2 * cap + 2, StoresCell dec (C.1, C.2 + i)
      (if i < cap then z.alpha (i + 1) else if i ≤ 2 * cap then z.beta (i - cap)
        else z.initialNorm) s := by
    intro i hi
    split_ifs with hα hβ
    · exact ha i hα
    · simpa only [show cap + (i - cap) = i by omega] using hb (i - cap) (by omega)
    · have : i = 2 * cap + 1 := by omega
      subst i
      exact h.packed.initialNorm
  obtain ⟨vs, hvs⟩ := exists_readBlock_of_storesVec (k := cap + 1) (fun j hj => hv j (by omega))
  obtain ⟨cs, hcs⟩ := exists_coeff_readBlock hc
  exact ⟨vs, cs, hvs, hcs, ⟨fun j hj i => (hv j hj).dec_vec_eq_of_readBlock hvs (by omega) i,
    fun j hj => (ha j hj).dec_vec_eq_of_readBlock hcs (by omega),
    fun j hj => (hb j hj).dec_vec_eq_of_readBlock hcs (by omega),
    h.packed.initialNorm.dec_vec_eq_of_readBlock hcs (by omega)⟩⟩

/-- The same actual stored output contains either the initialized zero-step case or an
existing positive-length LanczosRun, with early stopping only at zero norm/coupling. -/
def Output (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (rhs : Fin n → ℝ)
    (E : ℝ) (cap : ℕ) (vs cs : List K) : Prop :=
  ∃ done ≤ cap, ∃ z : Values n, Outcome A rhs E done z ∧ PackedOutput dec cap z vs cs ∧
    (done < cap → (if done = 0 then z.initialNorm else z.beta done) = 0)

end NLAlib.Krylov.Lanczos.Rounded
