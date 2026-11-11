/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.State

/-!
# Assembly of the initial stored Lanczos state

After zeroing all output cells, normalization changes only the first basis column and the
input-norm cell. Every other initialized output cell remains zero, including any extra
coefficient suffix. These storage facts assemble the loop invariant without unfolding a run.

## Main results

* `NLAlib.Krylov.Lanczos.state_zero_of_normalize` assembles initialization and its zero suffix.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops

variable {K : Type} [Inhabited K]

/-- The output footprint of initial normalization is the first column and input-norm cell. -/
def normalizeFp (n cap : ℕ) (V C : ℕ × ℕ) : Fp :=
  Fp.blocks [(V.1, V.2), (C.1, C.2 + 2 * cap + 1)] [n, 1]

/-- Initial normalization preserves every basis column after the first. -/
theorem normalizeFp_disj_basis {n cap j : ℕ} {V C : ℕ × ℕ}
    (hvc : V.1 ≠ C.1) (hj : 0 < j) :
    Fp.Disj (normalizeFp n cap V C) (Store.inBlock V.1 (V.2 + j * n) n) := by
  simp only [normalizeFp, Fp.blocks, Fp.disj_sup_left, Fp.disj_bot_left, and_true]
  refine ⟨Fp.disj_inBlock_of_le ?_, Fp.disj_inBlock_of_ne hvc.symm⟩
  have := Idx.mul_add_le_mul hj n
  omega

/-- Initial normalization preserves every coefficient cell except the input norm. -/
theorem normalizeFp_disj_coeff {n cap i : ℕ} {V C : ℕ × ℕ}
    (hvc : V.1 ≠ C.1) (hi : i ≠ 2 * cap + 1) :
    Fp.Disj (normalizeFp n cap V C) (Store.inBlock C.1 (C.2 + i) 1) := by
  simp only [normalizeFp, Fp.blocks, Fp.disj_sup_left, Fp.disj_bot_left, and_true]
  refine ⟨Fp.disj_inBlock_of_ne hvc, ?_⟩
  rintro z k ⟨_, h₁, h₂⟩ ⟨_, h₃, h₄⟩
  omega

/-- Zeroed output blocks, a normalized first column, the input norm, and a readable valid
guard establish the initial loop state. Additional coefficient cells remain initialized zero. -/
theorem state_zero_of_normalize {dec : K → ℝ} {n cap clen L : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {V C : ℕ × ℕ} {s s' : Store K}
    (hlen : 2 * cap + 2 ≤ clen) (hvc : V.1 ≠ C.1) (hv : V.1 < L) (hc : C.1 < L)
    (hV : StoresVec dec V (0 : Fin ((cap + 1) * n) → ℝ) s)
    (hC : StoresVec dec C (0 : Fin clen → ℝ) s)
    (hprev : StoresVec dec (L, 0) (0 : Fin n → ℝ) s)
    (hf : s.EqOff (normalizeFp n cap V C) s')
    (hq : StoresVec dec V (lanczosState A b 0).cur s')
    (hnorm : StoresCell dec (C.1, C.2 + 2 * cap + 1) ‖WithLp.toLp 2 b‖ s')
    (hguard : ∃ σ, s'.get (L + 2) 0 = some σ ∧ 0 ≤ dec σ ∧ (0 < dec σ ↔ b ≠ 0)) :
    State dec A b cap 0 V C L s' ∧
      ∀ i, 2 * cap + 2 ≤ i → i < clen → StoresCell dec (C.1, C.2 + i) 0 s' := by
  have hcoeff : ∀ i < clen, i ≠ 2 * cap + 1 → StoresCell dec (C.1, C.2 + i) 0 s' := by
    intro i hi he
    exact (hC.cell ⟨i, hi⟩).keep hf (normalizeFp_disj_coeff hvc he)
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, fun i hi hi' => hcoeff i hi' (by omega)⟩
  · intro j hj
    rw [basisValue_zero]
    by_cases he : j = 0
    · subst j
      simpa only [↓reduceIte, Nat.zero_mul, Nat.add_zero, Prod.mk.eta] using hq
    · rw [if_neg he]
      have hbound : j * n + n ≤ (cap + 1) * n :=
        Idx.mul_add_le_mul (by omega) n
      exact (hV.zero_sub hbound).keep hf (normalizeFp_disj_basis hvc (by omega))
  · intro i hi
    rw [coeffValue_zero]
    by_cases he : i = 2 * cap + 1
    · subst i
      simpa only [↓reduceIte, Nat.add_assoc] using hnorm
    · rw [if_neg he]
      exact hcoeff i (by omega) he
  · change StoresVec dec (L, 0) (0 : Fin n → ℝ) s'
    refine hprev.keep hf ?_
    simp only [normalizeFp, Fp.blocks, Fp.disj_sup_left, Fp.disj_bot_left, and_true]
    exact ⟨Fp.disj_inBlock_of_ne (by omega), Fp.disj_inBlock_of_ne (by omega)⟩
  · obtain ⟨σ, hσ, hn, hp⟩ := hguard
    refine ⟨σ, hσ, hn, ?_⟩
    rw [ne_eq, lanczosState_zero_cur_eq_zero_iff]
    exact hp

end NLAlib.Krylov.Lanczos
