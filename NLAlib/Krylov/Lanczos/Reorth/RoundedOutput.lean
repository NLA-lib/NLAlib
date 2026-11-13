/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.RoundedState
public import NLAlib.Krylov.Lanczos.RoundedOutput

/-!
# Packed output of rounded fully reorthogonalized Lanczos

Every requested basis and coefficient word is tied to the same executed local history.
The output includes each saved raw residual norm and the initialized zero tails.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Rounded.Prefix.readback`: complete physical packed outputs.
* `NLAlib.Krylov.Lanczos.Reorth.Rounded.Output`: unconditional rounded history and outputs.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Rounded

open Ops

variable {K : Type} [Inhabited K]

/-- Packed ordinary coefficients and the additional raw-norm suffix of the same history. -/
structure PackedOutput (dec : K → ℝ) {n : ℕ} (cap done : ℕ)
    (z : Lanczos.Rounded.Values n) (nus : ℕ → ℝ) (vs cs : List K) : Prop
    extends Lanczos.Rounded.PackedOutput dec cap z vs cs where
  /-- Saved raw residual norms, with initialized zeros after the executed prefix. -/
  nu : ∀ j < cap, dec (vec cs (2 * cap + 2 + j)) =
    if j < done then nus (j + 1) else 0

/-- Complete physical packed output follows from the archive and its initialized zero tails. -/
theorem Prefix.readback {dec : K → ℝ} {n cap done : ℕ} {V C : ℕ × ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {em u E : ℝ} {e : Blas1Err}
    {z : Lanczos.Rounded.Values n} {nus : ℕ → ℝ} {s : Store K}
    (h : Prefix dec A rhs em u E e cap done V C z nus s) :
    ∃ vs cs, s.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
      s.readBlock C.1 C.2 (3 * cap + 2) = some cs ∧
      PackedOutput dec cap done z nus vs cs := by
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
  let cv : ℕ → ℝ := fun i => if i < cap then z.alpha (i + 1)
    else if i ≤ 2 * cap then z.beta (i - cap)
    else if i = 2 * cap + 1 then z.initialNorm
    else if i - (2 * cap + 2) < done then nus (i - (2 * cap + 2) + 1) else 0
  have hc : ∀ i < 3 * cap + 2, StoresCell dec (C.1, C.2 + i) (cv i) s := by
    intro i hi
    simp only [cv]
    split_ifs with hα hβ hn hd
    · exact ha i hα
    · simpa only [show cap + (i - cap) = i by omega] using hb (i - cap) (by omega)
    · subst i; exact h.packed.initialNorm
    all_goals
      have he : C.2 + 2 * cap + 2 + (i - (2 * cap + 2)) = C.2 + i := by omega
      simpa only [he, hd, ↓reduceIte] using h.packed.nu (i - (2 * cap + 2)) (by omega)
  obtain ⟨vs, hvs⟩ := exists_readBlock_of_storesVec (k := cap + 1) (fun j hj => hv j (by omega))
  obtain ⟨cs, hcs⟩ := exists_coeff_readBlock hc
  refine ⟨vs, cs, hvs, hcs, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj i
    exact (hv j hj).dec_vec_eq_of_readBlock hvs (by omega) i
  · intro j hj
    simpa only [cv, if_pos hj] using (hc j (by omega)).dec_vec_eq_of_readBlock hcs (by omega)
  · intro j hj
    simpa only [cv, if_neg (by omega : ¬cap + j < cap), if_pos (by omega : cap + j ≤ 2 * cap),
      Nat.add_sub_cancel_left] using
      (hc (cap + j) (by omega)).dec_vec_eq_of_readBlock hcs (by omega)
  · simpa only [cv, if_neg (by omega : ¬2 * cap + 1 < cap),
      if_neg (by omega : ¬2 * cap + 1 ≤ 2 * cap), ↓reduceIte] using
      (hc (2 * cap + 1) (by omega)).dec_vec_eq_of_readBlock hcs (by omega)
  · intro j hj
    simpa only [cv, if_neg (by omega : ¬2 * cap + 2 + j < cap),
      if_neg (by omega : ¬2 * cap + 2 + j ≤ 2 * cap),
      if_neg (by omega : ¬2 * cap + 2 + j = 2 * cap + 1), Nat.add_sub_cancel_left] using
      (hc (2 * cap + 2 + j) (by omega)).dec_vec_eq_of_readBlock hcs (by omega)

/-- The actual rounded output is a numerical history of exactly the executed rounds, with
all packed values and an early exit only when the last computed norm is zero. -/
def Output (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (rhs : Fin n → ℝ)
    (em u E : ℝ) (e : Blas1Err) (cap : ℕ) (vs cs : List K) : Prop :=
  ∃ done ≤ cap, ∃ z : Lanczos.Rounded.Values n, ∃ nus : ℕ → ℝ,
    History dec A rhs em u E e done z nus ∧ PackedOutput dec cap done z nus vs cs ∧
    (done < cap → (if done = 0 then z.initialNorm else z.beta done) = 0)

end NLAlib.Krylov.Lanczos.Reorth.Rounded
