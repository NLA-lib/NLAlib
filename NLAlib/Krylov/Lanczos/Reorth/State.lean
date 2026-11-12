/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.State
public import NLAlib.Krylov.Lanczos.Reorth.Spec

/-!
# Stored prefixes for reorthogonalized Lanczos

The ordinary basis and coefficient prefix are shared. An additional suffix retains the raw
residual norms. For Hermitian exact arithmetic these norms equal the next coupling, as proved
by the existing pure reorthogonalized recurrence.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.State.stopped` completes a prefix after breakdown.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops

variable {K : Type} [Inhabited K]

/-- Completed raw residual norms equal the following couplings in exact Hermitian Lanczos;
future norms are initialized zero. -/
noncomputable def nuValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (done j : ℕ) : ℝ := if j < done then (lanczosState A b (j + 1)).beta else 0

/-- The shared Lanczos state plus the preorthogonalization norm suffix. -/
structure State (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n → ℝ) (cap done : ℕ) (V C : ℕ × ℕ) (L : ℕ) (s : Store K)
    extends Lanczos.State dec A b cap done V C L s where
  /-- Raw residual norms are retained in the extra coefficient segment. -/
  nu : ∀ j < cap, StoresCell dec (C.1, C.2 + 2 * cap + 2 + j) (nuValue A b done j) s

/-- A stopped state has its complete raw-norm suffix already initialized. -/
theorem State.stopped {dec : K → ℝ} {n cap done L : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {V C : ℕ × ℕ} {s : Store K}
    (h : State dec A b cap done V C L s) (hd : done ≤ cap)
    (hc : (lanczosState A b done).cur = 0) :
    Prefix dec A b cap cap V C s ∧
      ∀ j < cap, StoresCell dec (C.1, C.2 + 2 * cap + 2 + j) (nuValue A b cap j) s := by
  refine ⟨h.toPrefix.stopped hd hc, fun j hj => ?_⟩
  have hb := lanczosState_beta_eq_zero_of_cur_eq_zero A b hc
  by_cases hdone : j < done
  · simpa only [nuValue, if_pos hdone, if_pos hj] using h.nu j hj
  · have hzero := (lanczosState_cur_beta_zero_of_le A b (show done ≤ j + 1 by omega) hc hb).2
    simpa only [nuValue, if_neg hdone, if_pos hj, hzero] using h.nu j hj

/-- A completed shared prefix and raw-norm suffix give actual packed output reads and the
existing exact reorthogonalized recurrence for Hermitian matrices. -/
theorem readback {dec : K → ℝ} {n cap : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {V C : ℕ × ℕ} {s : Store K}
    (h : Prefix dec A b cap cap V C s) (hA : A.IsHermitian)
    (hν : ∀ j < cap, StoresCell dec (C.1, C.2 + 2 * cap + 2 + j) (nuValue A b cap j) s) :
    ∃ vs cs, s.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
      s.readBlock C.1 C.2 (3 * cap + 2) = some cs ∧ Output dec A b cap vs cs := by
  classical
  obtain ⟨vs, hv⟩ := exists_readBlock_of_storesVec (k := cap + 1) (fun j hj => h.basis j (by omega))
  let cv : ℕ → ℝ := fun i => if i < 2 * cap + 2 then coeffValue A b cap cap i
    else (lanczosState A b (i - (2 * cap + 2) + 1)).beta
  have hcells : ∀ i < 3 * cap + 2, StoresCell dec (C.1, C.2 + i) (cv i) s := by
    intro i hi
    by_cases hp : i < 2 * cap + 2
    · simpa only [cv, if_pos hp] using h.coeff i hp
    · have hj : i - (2 * cap + 2) < cap := by omega
      have he : C.2 + 2 * cap + 2 + (i - (2 * cap + 2)) = C.2 + i := by omega
      simpa only [cv, if_neg hp, nuValue, if_pos hj, he] using hν (i - (2 * cap + 2)) hj
  obtain ⟨cs, hc⟩ := exists_coeff_readBlock hcells
  refine ⟨vs, cs, hv, hc, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj i
    have he := (h.basis j hj).dec_vec_eq_of_readBlock hv (by omega) i
    have hold : dec (vec vs (j * n + i)) = (lanczosState A b j).cur i :=
      by simpa only [basisValue_of_le A b hj] using he
    exact hold.trans (congrFun (congrArg LanczosState.cur
      (hA.lanczosReorthState_toLanczosState b j).1) i).symm
  · intro j hj
    have he := (hcells j (by omega)).dec_vec_eq_of_readBlock hc (by omega)
    simpa only [cv, if_pos (by omega : j < 2 * cap + 2), coeffValue_alpha A b hj, if_pos hj,
      (hA.lanczosReorthState_toLanczosState b j).1] using he
  · intro j hj
    have he := (hcells (cap + j) (by omega)).dec_vec_eq_of_readBlock hc (by omega)
    have hold : dec (vec cs (cap + j)) = (lanczosState A b j).beta := by
      simpa only [cv, if_pos (by omega : cap + j < 2 * cap + 2), coeffValue_beta A b hj,
        if_pos hj] using he
    exact hold.trans (congrArg LanczosState.beta
      (hA.lanczosReorthState_toLanczosState b j).1).symm
  · have he := (hcells (2 * cap + 1) (by omega)).dec_vec_eq_of_readBlock hc (by omega)
    simpa only [cv, if_pos (by omega : 2 * cap + 1 < 2 * cap + 2), coeffValue_norm] using he
  · intro j hj
    have hνj : StoresCell dec (C.1, C.2 + (2 * cap + 2 + j)) (nuValue A b cap j) s := by
      simpa only [Nat.add_assoc] using hν j hj
    have he := hνj.dec_vec_eq_of_readBlock (i := 2 * cap + 2 + j) hc (by omega)
    have hold : dec (vec cs (2 * cap + 2 + j)) = (lanczosState A b (j + 1)).beta := by
      simpa only [nuValue, if_pos hj, Nat.add_assoc] using he
    exact hold.trans ((congrArg LanczosState.beta
      (hA.lanczosReorthState_toLanczosState b (j + 1)).1).symm.trans
        (hA.lanczosReorthState_nu b j).symm)

/-- A round additionally writes its preorthogonalization norm in the suffix. -/
def advanceFp (n cap done L : ℕ) (V C : ℕ × ℕ) : Fp :=
  Lanczos.advanceFp n cap done L V C ⊔ Store.inBlock C.1 (C.2 + 2 * cap + 2 + done) 1

/-- The extended footprint preserves every other basis column. -/
theorem advanceFp_disj_basis {n cap done L j : ℕ} {V C : ℕ × ℕ}
    (hvc : V.1 ≠ C.1) (hv : V.1 < L) (hj : j ≠ done + 1) :
    Fp.Disj (advanceFp n cap done L V C) (Store.inBlock V.1 (V.2 + j * n) n) := by
  exact Fp.disj_sup_left.mpr ⟨Lanczos.advanceFp_disj_basis hvc hv hj,
    Fp.disj_inBlock_of_ne hvc.symm⟩

/-- The extra norm write is outside the ordinary coefficient prefix. -/
theorem advanceFp_disj_coeff {n cap done L i : ℕ} {V C : ℕ × ℕ}
    (hvc : V.1 ≠ C.1) (hc : C.1 < L) (hi : i < 2 * cap + 2)
    (ha : i ≠ done) (hb : i ≠ cap + done + 1) :
    Fp.Disj (advanceFp n cap done L V C) (Store.inBlock C.1 (C.2 + i) 1) := by
  refine Fp.disj_sup_left.mpr ⟨Lanczos.advanceFp_disj_coeff hvc hc ha hb, ?_⟩
  rintro z k ⟨_, h₁, h₂⟩ ⟨_, h₃, h₄⟩
  omega

/-- All other raw-norm suffix cells are preserved. -/
theorem advanceFp_disj_nu {n cap done L j : ℕ} {V C : ℕ × ℕ}
    (hvc : V.1 ≠ C.1) (hc : C.1 < L) (hd : done < cap) (hj : j ≠ done) :
    Fp.Disj (advanceFp n cap done L V C)
      (Store.inBlock C.1 (C.2 + 2 * cap + 2 + j) 1) := by
  refine Fp.disj_sup_left.mpr ⟨?_, ?_⟩
  · simpa only [Nat.add_assoc] using
      Lanczos.advanceFp_disj_coeff (n := n) (cap := cap) (done := done) (L := L)
        (i := 2*cap+2+j) (V := V) (C := C) hvc hc (by omega) (by omega)
  · rintro z k ⟨_, h₁, h₂⟩ ⟨_, h₃, h₄⟩
    omega

/-- Actual next-state reads and the exact footprint advance every initialized output prefix.
No future trajectory or successful-execution hypothesis is involved. -/
theorem State.advance {dec : K → ℝ} {n cap done L : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {V C : ℕ × ℕ} {s s' : Store K}
    (h : State dec A b cap done V C L s) (hd : done < cap)
    (hvc : V.1 ≠ C.1) (hv : V.1 < L) (hc : C.1 < L)
    (hf : s.EqOff (advanceFp n cap done L V C) s')
    (hq : StoresVec dec (V.1, V.2 + (done + 1) * n) (lanczosState A b (done + 1)).cur s')
    (ha : StoresCell dec (C.1, C.2 + done) (lanczosAlpha A (lanczosState A b done)) s')
    (hb : StoresCell dec (C.1, C.2 + cap + done + 1) (lanczosState A b (done + 1)).beta s')
    (hν : StoresCell dec (C.1, C.2 + 2 * cap + 2 + done) (lanczosState A b (done + 1)).beta s')
    (hp : StoresVec dec (L, 0) (lanczosState A b (done + 1)).prev s')
    (hg : ∃ σ, s'.get (L + 2) 0 = some σ ∧ 0 ≤ dec σ ∧
      (0 < dec σ ↔ (lanczosState A b (done + 1)).cur ≠ 0)) :
    State dec A b cap (done + 1) V C L s' := by
  refine ⟨⟨⟨fun j hj => ?_, fun i hi => ?_⟩, hp, hg⟩, fun j hj => ?_⟩
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
        exact (h.coeff i hi).keep hf (advanceFp_disj_coeff hvc hc hi he he')
  · by_cases he : j = done
    · subst j
      simpa only [nuValue, Nat.lt_succ_self, ↓reduceIte] using hν
    · have hcmp : (j < done + 1) = (j < done) := propext (by omega)
      simp only [nuValue, hcmp]
      exact (h.nu j hj).keep hf (advanceFp_disj_nu hvc hc hd he)

end NLAlib.Krylov.Lanczos.Reorth
