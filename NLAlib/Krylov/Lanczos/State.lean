/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Storage
public import NLAlib.Krylov.Lanczos.Math.Prefix

/-!
# Stored prefixes and loop states for Lanczos

The loop invariant records initialized basis and coefficient outputs, the previous vector,
and a nonnegative guard whose positivity detects a nonzero current vector. A stopped prefix
already describes the complete output because the pure recurrence has a zero tail.

## Main results

* `NLAlib.Krylov.Lanczos.Prefix.stopped` completes a prefix after breakdown.
* `NLAlib.Krylov.Lanczos.Prefix.readback` produces the complete packed output.
* `NLAlib.Krylov.Lanczos.Prefix.advance` updates a prefix through one active round.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops

variable {K : Type} [Inhabited K]

/-- All requested output cells contain the initialized mathematical prefix. -/
structure Prefix (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (cap done : ℕ) (V C : ℕ × ℕ) (s : Store K) : Prop where
  /-- Basis columns through the cap, including initialized zero columns. -/
  basis : ∀ j ≤ cap, StoresVec dec (V.1, V.2 + j * n) (basisValue A b done j) s
  /-- The shared coefficient prefix, allowing an arbitrary unused suffix. -/
  coeff : ∀ i < 2 * cap + 2, StoresCell dec (C.1, C.2 + i) (coeffValue A b cap done i) s

/-- Prefix outputs together with the previous vector and a valid loop guard. -/
structure State (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (cap done : ℕ) (V C : ℕ × ℕ) (L : ℕ) (s : Store K)
    extends Prefix dec A b cap done V C s where
  /-- Caller scratch retains the recurrence's previous vector. -/
  prev : StoresVec dec (L, 0) (lanczosState A b done).prev s
  /-- The squared-norm guard is readable, nonnegative, and positive exactly before breakdown. -/
  guard : ∃ σ, s.get (L + 2) 0 = some σ ∧ 0 ≤ dec σ ∧
    (0 < dec σ ↔ (lanczosState A b done).cur ≠ 0)

/-- A zero current vector completes the initialized prefix through the cap. -/
theorem Prefix.stopped {dec : K → ℝ} {n cap done : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {V C : ℕ × ℕ} {s : Store K}
    (h : Prefix dec A b cap done V C s) (hd : done ≤ cap)
    (hc : (lanczosState A b done).cur = 0) : Prefix dec A b cap cap V C s := by
  have hb := lanczosState_beta_eq_zero_of_cur_eq_zero A b hc
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · rw [← basisValue_eq_of_cur_beta_zero A b hd hc hb j]
    exact h.basis j hj
  · rw [← coeffValue_eq_of_cur_beta_zero A b hc hb i]
    exact h.coeff i hi

/-- A completed prefix yields actual reads of the basis and shared coefficient block and
satisfies the packed mathematical output contract. -/
theorem Prefix.readback {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {V C : ℕ × ℕ} {s : Store K}
    (h : Prefix dec A b cap cap V C s) :
    ∃ vs cs, s.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
      s.readBlock C.1 C.2 (2 * cap + 2) = some cs ∧ Output dec A b cap vs cs := by
  obtain ⟨vs, hv⟩ := exists_readBlock_of_storesVec (k := cap + 1) (fun j hj => h.basis j (by omega))
  obtain ⟨cs, hc⟩ := exists_coeff_readBlock h.coeff
  refine ⟨vs, cs, hv, hc, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro j hj i
    have he := (h.basis j hj).dec_vec_eq_of_readBlock hv (by omega) i
    simpa only [basisValue_of_le A b hj] using he
  · intro j hj
    have he := (h.coeff j (by omega)).dec_vec_eq_of_readBlock hc (by omega)
    simpa only [coeffValue_alpha A b hj, if_pos hj] using he
  · intro j hj
    have he := (h.coeff (cap + j) (by omega)).dec_vec_eq_of_readBlock hc (by omega)
    simpa only [coeffValue_beta A b hj, if_pos hj] using he
  · exact (h.coeff (2 * cap + 1) (by omega)).dec_vec_eq_of_readBlock hc (by omega) |>.trans
      (coeffValue_norm A b cap cap)

/-- One active round writes the next basis column, current diagonal coefficient, next
coupling coefficient, and caller scratch from handle L on. -/
def advanceFp (n cap done L : ℕ) (V C : ℕ × ℕ) : Fp :=
  Fp.blocks [(V.1, V.2 + (done + 1) * n), (C.1, C.2 + done),
    (C.1, C.2 + cap + done + 1)] [n, 1, 1] ⊔ Fp.above L

/-- The active-round footprint preserves all other basis columns. -/
theorem advanceFp_disj_basis {n cap done L j : ℕ} {V C : ℕ × ℕ}
    (hvc : V.1 ≠ C.1) (hv : V.1 < L) (hj : j ≠ done + 1) :
    Fp.Disj (advanceFp n cap done L V C) (Store.inBlock V.1 (V.2 + j * n) n) := by
  simp only [advanceFp, Fp.blocks, Fp.disj_sup_left, Fp.disj_bot_left, and_true]
  refine ⟨⟨?_, Fp.disj_inBlock_of_ne hvc.symm, Fp.disj_inBlock_of_ne hvc.symm⟩, ?_⟩
  · rcases lt_or_gt_of_ne hj with hj | hj
    · apply Fp.Disj.symm
      apply Fp.disj_inBlock_of_le
      have := Idx.mul_add_le_mul hj n
      omega
    · apply Fp.disj_inBlock_of_le
      have := Idx.mul_add_le_mul hj n
      omega
  · rintro z i hz ⟨rfl, _, _⟩
    exact Nat.not_le_of_lt hv hz

/-- The active-round footprint preserves all coefficient cells except its two updates. -/
theorem advanceFp_disj_coeff {n cap done L i : ℕ} {V C : ℕ × ℕ}
    (hvc : V.1 ≠ C.1) (hc : C.1 < L) (ha : i ≠ done) (hb : i ≠ cap + done + 1) :
    Fp.Disj (advanceFp n cap done L V C) (Store.inBlock C.1 (C.2 + i) 1) := by
  simp only [advanceFp, Fp.blocks, Fp.disj_sup_left, Fp.disj_bot_left, and_true]
  refine ⟨⟨Fp.disj_inBlock_of_ne hvc, ?_, ?_⟩, ?_⟩
  · rintro z k ⟨_, h₁, h₂⟩ ⟨_, h₃, h₄⟩
    omega
  · rintro z k ⟨_, h₁, h₂⟩ ⟨_, h₃, h₄⟩
    omega
  · rintro z k hz ⟨rfl, _, _⟩
    exact Nat.not_le_of_lt hc hz

/-- One active round preserves the other initialized entries and writes exactly the next
prefix values. Scratch may change freely above L. -/
theorem Prefix.advance {dec : K → ℝ} {n cap done L : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {V C : ℕ × ℕ} {s s' : Store K}
    (h : Prefix dec A b cap done V C s) (hd : done < cap)
    (hvc : V.1 ≠ C.1) (hv : V.1 < L) (hc : C.1 < L)
    (hf : s.EqOff (advanceFp n cap done L V C) s')
    (hq : StoresVec dec (V.1, V.2 + (done + 1) * n)
      (lanczosState A b (done + 1)).cur s')
    (ha : StoresCell dec (C.1, C.2 + done)
      (lanczosAlpha A (lanczosState A b done)) s')
    (hb : StoresCell dec (C.1, C.2 + cap + done + 1)
      (lanczosState A b (done + 1)).beta s') : Prefix dec A b cap (done + 1) V C s' := by
  refine ⟨fun j hj => ?_, fun i hi => ?_⟩
  · rw [basisValue_succ]
    by_cases he : j = done + 1
    · subst j
      simpa only [↓reduceIte] using hq
    · rw [if_neg he]
      exact (h.basis j hj).keep hf (advanceFp_disj_basis hvc hv he)
  · rw [coeffValue_succ A b hd]
    by_cases he : i = done
    · subst i
      simpa only [↓reduceIte] using ha
    · rw [if_neg he]
      by_cases he' : i = cap + done + 1
      · subst i
        simpa only [↓reduceIte, Nat.add_assoc] using hb
      · rw [if_neg he']
        exact (h.coeff i hi).keep hf (advanceFp_disj_coeff hvc hc he he')

end NLAlib.Krylov.Lanczos
