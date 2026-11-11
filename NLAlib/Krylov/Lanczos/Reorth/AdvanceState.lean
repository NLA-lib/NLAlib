/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.Advance
public import NLAlib.Krylov.Lanczos.Reorth.State

/-!
# A reorthogonalized Lanczos round advances its stored prefix

The existing Hermitian exact-reorthogonalization mathematics identifies the concrete sweep
with the ordinary canonical recurrence. All read and guard facts concern actual output words.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.advance_state_writes`: total advancement of the loop state.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- The total exact round advances the initialized prefix and its zero-detecting guard. -/
theorem advance_state_writes {M : Machine K} {dec : K → ℝ}
    {n cap j L B V C bo vo co : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ}
    {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I) (hAT : A.IsHermitian)
    {τ : Tape K} {μ : Mem K} (hj : j < cap) (hVL : V < L) (hCL : C < L) (hVC : V ≠ C)
    (hlen : μ.store.length = L + 3) (hp : μ.store.len L = n) (hw : μ.store.len (L + 1) = n)
    (ht : μ.store.len (L + 2) = 2) (hvroom : vo + (cap + 1) * n ≤ μ.store.len V)
    (hcroom : co + 3 * cap + 2 ≤ μ.store.len C)
    (h : State dec A b cap j (V, vo) (C, co) L μ.store) :
    Writes .total I τ advance ⟨[n, cap, bo, vo, co, j], [B, V, C, L, L + 1, L + 2]⟩
      (advanceFp n cap j L (V, vo) (C, co))
      (fun μ' => μ'.pos = μ.pos ∧ State dec A b cap (j + 1) (V, vo) (C, co) L μ'.store) μ := by
  obtain ⟨ps, hps, hpsdec⟩ := h.prev
  have hcur : StoresVec dec (V, vo + j * n) (lanczosState A b j).cur μ.store := by
    simpa only [basisValue_of_le A b le_rfl] using h.basis j (Nat.le_of_lt hj)
  obtain ⟨qs, hqs, hqsdec⟩ := hcur
  have hnew : StoresVec dec (V, vo + (j + 1) * n) (0 : Fin n → ℝ) μ.store := by
    simpa only [basisValue_of_lt A b (Nat.lt_succ_self j)] using h.basis (j + 1) (by omega)
  obtain ⟨next, hnext, hnextzero⟩ := hnew
  obtain ⟨β, hβ, hβdec⟩ := h.coeff (cap + j) (by omega)
  have hβold : dec β = (lanczosState A b j).beta := by
    simpa only [coeffValue_beta A b (Nat.le_of_lt hj), if_pos le_rfl] using hβdec
  obtain ⟨β₀, hβ₀, hβzero⟩ := h.coeff (cap + (j + 1)) (by omega)
  have hβzero' : dec β₀ = 0 := by
    simpa only [coeffValue_beta A b (show j + 1 ≤ cap by omega),
      if_neg (show ¬j + 1 ≤ j by omega)] using hβzero
  obtain ⟨ν₀, hν₀, hνzero⟩ := h.nu j hj
  have hνzero' : dec ν₀ = 0 := by simpa only [nuValue, Nat.lt_irrefl, ↓reduceIte] using hνzero
  obtain ⟨basis, hbasis⟩ := exists_basis_readBlock (k := j + 1) (V := (V, vo))
    (fun l hl => h.basis l (by omega))
  have hbasisdec : ∀ l < j + 1, (fun i : Fin n => dec (vec basis (l * n + i))) =
      (lanczosReorthState A b j).vecs l := by
    intro l hl
    funext i
    have he := (h.basis l (by omega)).entry_of_basis_readBlock hbasis hl i
    have hold : dec (vec basis (l * n + i)) = (lanczosState A b l).cur i := by
      simpa only [basisValue_of_le A b (show l ≤ j by omega)] using he
    have hvec := congrFun ((hAT.lanczosReorthState_toLanczosState b j).2 l) i
    have hvec' : (lanczosReorthState A b j).vecs l i = (lanczosState A b l).cur i := by
      simpa only [if_pos (show l ≤ j by omega)] using hvec
    exact hold.trans hvec'.symm
  have hnroom : vo + (j + 1) * n + n ≤ μ.store.len V := by
    have hmul := Nat.mul_le_mul_right n (show j + 2 ≤ cap + 1 by omega)
    calc
      _ = vo + (j + 2) * n := by ring
      _ ≤ μ.store.len V := by omega
  have hfp : Fp.blocks [(L, 0), (L + 1, 0), (L + 2, 0), (C, co + j), (C, co + cap + j + 1),
      (C, co + 2 * cap + 2 + j), (V, vo + (j + 1) * n)] [n, n, 2, 1, 1, 1, n] ≤
      advanceFp n cap j L (V, vo) (C, co) := by
    intro z i hz
    simp only [Fp.blocks, Pi.sup_apply, sup_Prop_eq, Pi.bot_apply] at hz
    simp only [advanceFp, Lanczos.advanceFp, Fp.blocks, Fp.above, Pi.sup_apply,
      sup_Prop_eq, Pi.bot_apply]
    rcases hz with hz | hz | hz | hz | hz | hz | hz | hz
    · rcases hz with ⟨rfl, _, _⟩; exact Or.inl (Or.inr le_rfl)
    · rcases hz with ⟨rfl, _, _⟩; exact Or.inl (Or.inr (by omega))
    · rcases hz with ⟨rfl, _, _⟩; exact Or.inl (Or.inr (by omega))
    all_goals tauto
  refine (advance_writes (B := B) (bo := bo) hS hM hB hok hA hCmp hj hVL hCL hVC
    hlen hw hp ht hcroom hps hqs hbasis hnext hnroom
    (by simpa only [Nat.add_assoc] using hβ)
    (by simpa only [Nat.add_assoc] using hβ₀) hν₀ hnextzero hβzero' hνzero').mono hfp ?_
  rintro μ' hfr ⟨hpos, raw, reduced, ys, α, ν, β', hprev, hred, hys, hα, hν, hβ',
    hαdec, hraw, hnormν, hpasses, hnormalized, hnormβ, σ, hσ, hσdec⟩
  have hαold : dec α = lanczosAlpha A (lanczosState A b j) := by
    simpa only [hpsdec, hqsdec, hβold] using hαdec
  have hrawold : decv dec n raw = A *ᵥ (lanczosState A b j).cur -
      (lanczosState A b j).beta • (lanczosState A b j).prev -
      lanczosAlpha A (lanczosState A b j) • (lanczosState A b j).cur := by
    simpa only [hpsdec, hqsdec, hβold, hαold] using hraw
  have hs := (hAT.lanczosReorthState_toLanczosState b j).1
  have hrawreorth : decv dec n raw = A *ᵥ (lanczosReorthState A b j).cur -
      (lanczosReorthState A b j).beta • (lanczosReorthState A b j).prev -
      lanczosAlpha A (lanczosReorthState A b j).toLanczosState •
        (lanczosReorthState A b j).cur := by
    have hc' : (lanczosReorthState A b j).cur = (lanczosState A b j).cur :=
      congrArg LanczosState.cur hs
    have hp' : (lanczosReorthState A b j).prev = (lanczosState A b j).prev :=
      congrArg LanczosState.prev hs
    have hb' : (lanczosReorthState A b j).beta = (lanczosState A b j).beta :=
      congrArg LanczosState.beta hs
    rw [hc', hp', hb', hs]
    exact hrawold
  obtain ⟨hnextR, hβR⟩ := hpasses.next_eq (initial := next) (σ := σ) (β₀ := β₀)
    hbasisdec hrawreorth ⟨hnormalized, hnormβ⟩
  change decv dec n ys = (lanczosReorthState A b (j + 1)).cur at hnextR
  change dec β' = (lanczosReorthState A b (j + 1)).beta at hβR
  have hs' := (hAT.lanczosReorthState_toLanczosState b (j + 1)).1
  have hnextold := hnextR.trans (congrArg LanczosState.cur hs')
  have hβold' := hβR.trans (congrArg LanczosState.beta hs')
  have hνold : dec ν = (lanczosState A b (j + 1)).beta := by
    simpa [lanczosState, lanczosStep, hrawold] using hnormν
  have hσnorm : dec σ = ‖WithLp.toLp 2 (decv dec n reduced)‖ ^ 2 :=
    hσdec.trans (EuclideanSpace.norm_toLp_sq_eq_dotProduct_self _).symm
  have hzero : ‖WithLp.toLp 2 (decv dec n reduced)‖ = 0 ↔
      (lanczosState A b (j + 1)).cur = 0 := by
    rw [← hnextold, hnormalized]
    simp only [smul_eq_zero, inv_eq_zero, norm_eq_zero, WithLp.toLp_eq_zero, or_self]
  refine ⟨hpos, h.advance hj hVC hVL hCL (hfr.mono hfp) ⟨ys, hys, hnextold⟩
    ⟨α, hα, hαold⟩ ⟨β', hβ', hβold'⟩ ⟨ν, hν, hνold⟩
    ⟨qs, hprev, by simpa only [lanczosState, lanczosStep] using hqsdec⟩
    ⟨σ, hσ, by rw [hσnorm]; positivity, ?_⟩⟩
  rw [hσnorm]
  exact sq_pos_iff.trans (not_congr hzero)
end NLAlib.Krylov.Lanczos.Reorth
