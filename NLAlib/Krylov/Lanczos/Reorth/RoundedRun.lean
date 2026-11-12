/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.RoundedState

/-!
# Advancing the actual rounded reorthogonalized history

Local operation contracts supply the executed transition and all physical archived entries.
This step needs no matrix symmetry, orthogonality or future nonbreakdown assumption.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Rounded.advance_state_writes`: total history advancement.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Rounded

open Ops

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- The actual local output extends both the numerical history and complete packed archive. -/
theorem advance_state_writes {M : Machine K} {dec : K → ℝ}
    {n cap j L B V C bo vo co : ℕ} {em u E : ℝ} {e : Blas1Err}
    {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {I : Interp Op Tst K}
    {ok : ℕ → Prop} {z : Lanczos.Rounded.Values n} {nus : ℕ → ℝ}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec e ok I)
    (hok : ok n) (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
    (hprec : Lanczos.Rounded.Precision em u E e n)
    {τ : Tape K} {μ : Mem K} (hj : j < cap) (hVL : V < L) (hCL : C < L) (hVC : V ≠ C)
    (hlen : μ.store.length = L + 3) (hp : μ.store.len L = n) (hw : μ.store.len (L + 1) = n)
    (ht : μ.store.len (L + 2) = 2) (hv : vo + (cap + 1) * n ≤ μ.store.len V)
    (hc : co + 3 * cap + 2 ≤ μ.store.len C)
    (h : State dec A rhs em u E e cap j (V, vo) (C, co) L z nus μ.store)
    (hactive : (if j = 0 then z.initialNorm else z.beta j) ≠ 0) :
    Writes .total I τ advance ⟨[n, cap, bo, vo, co, j], [B, V, C, L, L + 1, L + 2]⟩
      (Reorth.advanceFp n cap j L (V, vo) (C, co))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ z' nus',
        State dec A rhs em u E e cap (j + 1) (V, vo) (C, co) L z' nus' μ'.store) μ := by
  obtain ⟨ps, hps, hpsdec⟩ := h.prev
  obtain ⟨qs, hqs, hqsdec⟩ := h.packed.basis j le_rfl
  obtain ⟨next, hnext, hnextzero⟩ := h.packed.basis_zero (j + 1) (by omega) (by omega)
  obtain ⟨beta, hbeta, hbetadec⟩ := h.packed.beta j le_rfl
  obtain ⟨beta0, hbeta0, hbeta0zero⟩ := h.packed.beta_zero (j + 1) (by omega) (by omega)
  obtain ⟨nu0, hnu0, hnu0zero⟩ := h.packed.nu j hj
  have hnu0zero' : dec nu0 = 0 := by simpa only [Nat.lt_irrefl, ↓reduceIte] using hnu0zero
  obtain ⟨basis, hbasis⟩ := exists_readBlock_of_storesVec (k := j + 1) (V := (V, vo))
    (fun l hl => h.packed.basis l (by omega))
  have hbasisdec : ∀ l < j + 1,
      (fun i : Fin n => dec (vec basis (l * n + i))) = z.v (l + 1) := by
    intro l hl
    funext i
    exact (h.packed.basis l (by omega)).dec_vec_eq_of_readBlock hbasis hl i
  have hnroom : vo + (j + 1) * n + n ≤ μ.store.len V := by
    have hmul := Nat.mul_le_mul_right n (show j + 2 ≤ cap + 1 by omega)
    calc
      _ = vo + (j + 2) * n := by ring
      _ ≤ μ.store.len V := by omega
  have hfp : Fp.blocks [(L, 0), (L + 1, 0), (L + 2, 0), (C, co + j),
      (C, co + cap + j + 1), (C, co + 2 * cap + 2 + j), (V, vo + (j + 1) * n)]
      [n, n, 2, 1, 1, 1, n] ≤ Reorth.advanceFp n cap j L (V, vo) (C, co) := by
    intro b i hb
    simp only [Fp.blocks, Pi.sup_apply, sup_Prop_eq, Pi.bot_apply] at hb
    simp only [Reorth.advanceFp, Lanczos.advanceFp, Fp.blocks, Fp.above, Pi.sup_apply,
      sup_Prop_eq, Pi.bot_apply]
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb
    · rcases hb with ⟨rfl, _, _⟩; exact Or.inl (Or.inr le_rfl)
    · rcases hb with ⟨rfl, _, _⟩; exact Or.inl (Or.inr (by omega))
    · rcases hb with ⟨rfl, _, _⟩; exact Or.inl (Or.inr (by omega))
    all_goals tauto
  refine (advance_writes (B := B) (bo := bo) hS hM hB hok hA hCmp
    hprec.scalar_lt hprec.dot_lt hj hVL hCL hVC hlen hw hp ht hc hps hqs hbasis hnext
    hnroom (by simpa only [Nat.add_assoc] using hbeta)
    (by simpa only [Nat.add_assoc] using hbeta0) hnu0 hnextzero hbeta0zero hnu0zero').mono
      hfp ?_
  rintro μ' hfr ⟨hpos, first, raw, reduced, ys, alpha, nu, beta',
    hprev, hred, hys, halpha, hnu, hbeta', hbounds, hnormnu, hpasses,
    hnormbeta, hscaled, hzero, sigma, hsigma, hdot⟩
  have hlocal : Local dec A em u e j z (decv dec n ys) (dec alpha) (dec beta') (dec nu) :=
    ⟨ps, qs, basis, first, raw, reduced, ys, beta, alpha, nu, beta',
      hpsdec, hqsdec, hbetadec, hbasisdec, rfl, rfl, rfl, rfl,
      hbounds, hnormnu, hpasses, hnormbeta, hscaled, hzero⟩
  have hguard := hprec.guard_iff hnormbeta hdot
  refine ⟨hpos, z.next j (decv dec n ys) (dec alpha) (dec beta'),
    Function.update nus (j + 1) (dec nu), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact h.history.next hactive hlocal
  · exact h.packed.advance hj hVC hVL hCL (hfr.mono hfp)
      ⟨ys, hys, rfl⟩ ⟨alpha, halpha, rfl⟩ ⟨beta', hbeta', rfl⟩ ⟨nu, hnu, rfl⟩
  · intro l hl
    simpa only [Lanczos.Rounded.Values.next,
      Function.update_of_ne (show l ≠ j + 2 by omega)] using h.future_v l (by omega)
  · intro l hl
    simpa only [Lanczos.Rounded.Values.next,
      Function.update_of_ne (show l ≠ j + 1 by omega)] using h.future_coeff l (by omega)
  · refine ⟨qs, hprev, ?_⟩
    simpa only [Lanczos.Rounded.Values.next,
      Function.update_of_ne (show j + 1 ≠ j + 2 by omega)] using hqsdec
  · exact ⟨sigma, hsigma, hguard.1, by
      simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
        Lanczos.Rounded.Values.next, Function.update_self] using hguard.2⟩

end NLAlib.Krylov.Lanczos.Reorth.Rounded
