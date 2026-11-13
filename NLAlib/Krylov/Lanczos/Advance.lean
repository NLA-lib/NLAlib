/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Update
public import NLAlib.Krylov.Lanczos.NormalizationInterface
public import NLAlib.Krylov.Lanczos.State

/-!
# Successful ordinary Lanczos rounds

The Paige update, residual self-dot, previous-vector copy and guarded normalization compose
without a nonbreakdown hypothesis. The normalized zero residual initializes a stopped state,
and all untouched output cells retain their prefix values.

## Main results

* `NLAlib.Krylov.Lanczos.advance_writes` exposes exact reads after one complete round.
* `NLAlib.Krylov.Lanczos.advance_state_writes` advances the stored loop state.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- One complete round succeeds for readable inputs and initialized zero next outputs.
Its actual readback exposes the raw residual, normalized direction, and squared-norm guard. -/
theorem advance_writes {M : Machine K} {dec : K → ℝ} {n cap j L B V C bo vo co : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I)
    {τ : Tape K} {μ : Mem K} {ps qs next : List K} {β β₀ : K}
    (hVL : V < L) (hCL : C < L) (hVC : V ≠ C)
    (hlen : μ.store.length = L + 3) (hp : μ.store.len L = n)
    (hw : μ.store.len (L + 1) = n) (ht : μ.store.len (L + 2) = 2)
    (ha : co + j < μ.store.len C) (hb : co + cap + j + 1 < μ.store.len C)
    (hnroom : vo + (j + 1) * n + n ≤ μ.store.len V)
    (hps : μ.store.readBlock L 0 n = some ps)
    (hqs : μ.store.readBlock V (vo + j * n) n = some qs)
    (hβ : μ.store.get C (co + cap + j) = some β)
    (hnext : μ.store.readBlock V (vo + (j + 1) * n) n = some next)
    (hβ₀ : μ.store.get C (co + cap + j + 1) = some β₀)
    (hnextzero : decv dec n next = 0) (hβzero : dec β₀ = 0) :
    Writes .total I τ advance ⟨[n, cap, bo, vo, co, j], [B, V, C, L, L + 1, L + 2]⟩
      (advanceFp n cap j L (V, vo) (C, co))
      (fun μ' => μ'.pos = μ.pos ∧ ∃ raw ys α β' σ,
        μ'.store.readBlock L 0 n = some qs ∧
        μ'.store.readBlock V (vo + (j + 1) * n) n = some ys ∧
        μ'.store.get C (co + j) = some α ∧
        μ'.store.get C (co + cap + j + 1) = some β' ∧
        μ'.store.get (L + 2) 0 = some σ ∧
        dec α = lanczosAlpha A ⟨decv dec n ps, decv dec n qs, dec β⟩ ∧
        decv dec n raw = A *ᵥ decv dec n qs - dec β • decv dec n ps - dec α • decv dec n qs ∧
        decv dec n ys = ‖WithLp.toLp 2 (decv dec n raw)‖⁻¹ • decv dec n raw ∧
        dec β' = ‖WithLp.toLp 2 (decv dec n raw)‖ ∧
        dec σ = decv dec n raw ⬝ᵥ decv dec n raw) μ := by
  unfold advanceFp
  refine Writes.seq_le (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true]; omega)
    (update_writes hS hM hB hok hA hVC hVL hCL hCL hlen hw ht ha hps hqs hβ))
    (by fp_sub) ?_
  rintro μ₁ hfr₁ ⟨hpos₁, raw, α, hraw, hα, hαdec, hrawdec⟩
  step hB.dot as μ₂ hfr₂ ⟨hpos₂, σ, hσ, hdot⟩
  step hB.copy as μ₃ hfr₃ ⟨hpos₃, copied, hcopied, hcopy⟩
  subst copied
  refine (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₃.length_eq,
      hfr₂.length_eq, hfr₁.length_eq]; omega)
    (normalize_writes hS hM hB hok hCmp (by omega) (by omega) (by omega) (by omega)
      (by omega) hVC (by
        simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₃.length_eq,
          hfr₂.length_eq, hfr₁.length_eq]; omega)
      (by kept) (by kept) (by kept) (by kept) (dotExactRel_decoded hdot)
      hnextzero hβzero (by
        simp only [Mem.room_cons, Mem.room_nil, and_true, hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]
        exact ⟨hnroom, by omega⟩))).mono (by fp_sub) ?_
  rintro μ₄ hfr₄ ⟨hpos₄, ys, β', hys, hβ', hnormalized, hnormβ⟩
  exact ⟨by simp [hpos₄, hpos₃, hpos₂, hpos₁], raw, ys, α, β', σ,
    by kept, hys, by kept, hβ', by kept, hαdec, hrawdec,
    hnormalized, hnormβ, dotExactRel_decoded hdot⟩

/-- An initialized stored Lanczos state advances successfully, including a round whose raw
residual vanishes. No spectral assumption or execution-success premise is required. -/
theorem advance_state_writes {M : Machine K} {dec : K → ℝ} {n cap j L B V C bo vo co : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I)
    {τ : Tape K} {μ : Mem K}
    (hj : j < cap) (hVL : V < L) (hCL : C < L) (hVC : V ≠ C)
    (hlen : μ.store.length = L + 3) (hp : μ.store.len L = n)
    (hw : μ.store.len (L + 1) = n) (ht : μ.store.len (L + 2) = 2)
    (hroomV : vo + (cap + 1) * n ≤ μ.store.len V)
    (hroomC : co + 2 * cap + 2 ≤ μ.store.len C)
    (hs : State dec A b cap j (V, vo) (C, co) L μ.store) :
    Writes .total I τ advance ⟨[n, cap, bo, vo, co, j], [B, V, C, L, L + 1, L + 2]⟩
      (advanceFp n cap j L (V, vo) (C, co))
      (fun μ' => μ'.pos = μ.pos ∧ State dec A b cap (j + 1) (V, vo) (C, co) L μ'.store) μ := by
  obtain ⟨ps, hps, heps⟩ := hs.prev
  obtain ⟨qs, hqs, heqs⟩ := hs.basis j (by omega)
  rw [basisValue_of_le A b le_rfl] at heqs
  obtain ⟨β, hβ, heβ⟩ := hs.coeff (cap + j) (by omega)
  rw [coeffValue_beta A b (by omega), if_pos le_rfl] at heβ
  obtain ⟨next, hnext, henext⟩ := hs.basis (j + 1) (by omega)
  rw [basisValue_of_lt A b (Nat.lt_succ_self j)] at henext
  obtain ⟨β₀, hβ₀, heβ₀⟩ := hs.coeff (cap + (j + 1)) (by omega)
  rw [coeffValue_beta A b (by omega), if_neg (by omega : ¬j + 1 ≤ j)] at heβ₀
  have hnroom : vo + (j + 1) * n + n ≤ μ.store.len V := by
    have := Idx.mul_add_le_mul (by omega : j + 1 < cap + 1) n
    omega
  have hstate : (⟨decv dec n ps, decv dec n qs, dec β⟩ : LanczosState ℝ (Fin n)) =
      lanczosState A b j := by
    cases he : lanczosState A b j
    simp only [he, LanczosState.mk.injEq] at heps heqs heβ ⊢
    exact ⟨heps, heqs, heβ⟩
  refine (advance_writes hS hM hB hok hA hCmp hVL hCL hVC hlen hp hw ht
    (by omega) (by omega) hnroom hps hqs (by simpa [Nat.add_assoc] using hβ)
    hnext (by simpa [Nat.add_assoc] using hβ₀) henext heβ₀).mono le_rfl ?_
  rintro μ' hfr ⟨hpos, raw, ys, α, β', σ, hprev, hys, hα, hβ', hσ,
    hαdec, hraw, hnormalized, hnormβ, hdot⟩
  rw [hstate] at hαdec
  have hwdec : decv dec n raw = A *ᵥ (lanczosState A b j).cur -
      (lanczosState A b j).beta • (lanczosState A b j).prev -
      lanczosAlpha A (lanczosState A b j) • (lanczosState A b j).cur := by
    simpa only [heps, heqs, heβ, hαdec] using hraw
  have hcur : decv dec n ys = (lanczosState A b (j + 1)).cur := by
    simpa only [lanczosState, lanczosStep, RCLike.ofReal_real_eq_id, id_eq, ← hwdec]
      using hnormalized
  have hbeta : dec β' = (lanczosState A b (j + 1)).beta := by
    simpa only [lanczosState, lanczosStep, RCLike.ofReal_real_eq_id, id_eq, ← hwdec] using hnormβ
  have hzero : (lanczosState A b (j + 1)).cur = 0 ↔ decv dec n raw = 0 := by
    change (lanczosStep A (lanczosState A b j)).cur = 0 ↔ _
    rw [lanczosStep_cur_eq_zero_iff_beta_eq_zero]
    change ‖WithLp.toLp 2 _‖ = 0 ↔ _
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [← hwdec, norm_eq_zero, WithLp.toLp_eq_zero]
  refine ⟨hpos, ⟨hs.toPrefix.advance hj hVC hVL hCL hfr
    ⟨ys, hys, hcur⟩ ⟨α, hα, hαdec⟩ ⟨β', by simpa [Nat.add_assoc] using hβ', hbeta⟩,
    ⟨qs, hprev, heqs⟩, σ, hσ, ?_, ?_⟩⟩
  · rw [hdot]
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  · rw [hdot, ne_eq, hzero]
    simpa using (Matrix.dotProduct_star_self_pos_iff (v := decv dec n raw))

end NLAlib.Krylov.Lanczos
