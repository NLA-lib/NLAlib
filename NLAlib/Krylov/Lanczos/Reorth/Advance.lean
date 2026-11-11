/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.PreNorm
public import NLAlib.Krylov.Lanczos.Reorth.StepMath
public import NLAlib.Krylov.Lanczos.Update
public import NLAlib.Krylov.Lanczos.NormalizationInterface

/-!
# Composing a full exact reorthogonalized Lanczos round

The raw Paige update, saved preorthogonalization norm, two classical passes and guarded
normalization use the driver workspace. The result exposes the actual stored words and
local witnesses for a surrounding prefix invariant.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.advance_writes`: total exact reorthogonalized round.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- The raw update and both classical passes execute without a nonbreakdown premise. -/
theorem updateAndSweep_writes {M : Machine K} {dec : K → ℝ} {n cap j L B V C bo vo co : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I)
    {τ : Tape K} {μ : Mem K} {ps qs basis : List K} {β ν₀ : K}
    (hj : j < cap) (hVL : V < L) (hCL : C < L) (hVC : V ≠ C)
    (hlen : μ.store.length = L + 3) (hw : μ.store.len (L + 1) = n)
    (ht : μ.store.len (L + 2) = 2) (hroom : co + 3 * cap + 2 ≤ μ.store.len C)
    (hps : μ.store.readBlock L 0 n = some ps)
    (hqs : μ.store.readBlock V (vo + j * n) n = some qs)
    (hbasis : μ.store.readBlock V vo ((j + 1) * n) = some basis)
    (hβ : μ.store.get C (co + cap + j) = some β)
    (hν₀ : μ.store.get C (co + 2 * cap + 2 + j) = some ν₀) (hνzero : dec ν₀ = 0) :
    Writes .total I τ updateAndSweep ⟨[n, cap, bo, vo, co, j], [B, V, C, L, L + 1, L + 2]⟩
      (Fp.blocks [(L + 1, 0), (L + 2, 0), (C, co + j), (C, co + 2 * cap + 2 + j)] [n, 2, 1, 1])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ raw reduced α ν,
        μ'.store.readBlock (L + 1) 0 n = some reduced ∧
        μ'.store.get C (co + j) = some α ∧ μ'.store.get C (co + 2 * cap + 2 + j) = some ν ∧
        dec α = lanczosAlpha A ⟨decv dec n ps, decv dec n qs, dec β⟩ ∧
        decv dec n raw = A *ᵥ decv dec n qs - dec β • decv dec n ps - dec α • decv dec n qs ∧
        dec ν = ‖WithLp.toLp 2 (decv dec n raw)‖ ∧
        TwoPassOut dec 0 0 n (j + 1) basis raw reduced) μ := by
  refine Writes.seq_le (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true]; omega)
    (Lanczos.update_writes hS hM hB hok hA hVC hVL hCL hCL hlen hw ht (by dsimp; omega)
      hps hqs hβ)) (by fp_sub) ?_
  rintro μ₁ hfr₁ ⟨hpos₁, raw, α, hraw, hα, hαdec, hrawdec⟩
  refine Writes.seq_le (preNorm_writes (ed := fun _ => 0) hS hM.toStdModel_zero (by norm_num)
    hB.dot_zero hok hCmp hCL (by simpa only [hfr₁.length_eq] using hlen)
    (by simpa only [hfr₁.len_eq] using ht) (by simp only [hfr₁.len_eq]; omega)
    (by kept) (by kept) hνzero) (by fp_sub) ?_
  rintro μ₂ hfr₂ ⟨hpos₂, σ₀, ν, hσ₀, hν, hdot₀, hnormν⟩
  refine Writes.mono (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₂.length_eq, hfr₁.length_eq]; omega)
    (cgs2_writes_exact (qs := basis) (ws := raw) hS hM hB hok (by omega)
      (by simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₂.length_eq, hfr₁.length_eq]; omega)
      (by kept) (by kept) (by
        simp only [Mem.room_cons, Mem.room_nil, and_true, Nat.zero_add,
          hfr₂.len_eq, hfr₁.len_eq, hw]; exact le_rfl))) (by fp_sub) ?_
  rintro μ₃ hfr₃ ⟨hpos₃, reduced, hreduced, hpasses⟩
  exact ⟨by simp [hpos₃, hpos₂, hpos₁], raw, reduced, α, ν,
    hreduced, by kept, by kept, hαdec, hrawdec, hnormν.eq_norm, hpasses⟩

omit [Has OperatorOp Op] in
/-- Saving the previous vector and guarded normalization are total, including zero residual. -/
theorem saveAndNormalize_writes {M : Machine K} {dec : K → ℝ} {n cap j L B V C bo vo co : ℕ}
    {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hCmp : IsCmp dec I)
    {τ : Tape K} {μ : Mem K} {qs reduced next : List K} {β₀ : K}
    (hVL : V < L) (hCL : C < L) (hVC : V ≠ C)
    (hlen : μ.store.length = L + 3) (hp : μ.store.len L = n)
    (ht : μ.store.len (L + 2) = 2)
    (hroom : co + cap + j + 1 < μ.store.len C)
    (hqs : μ.store.readBlock V (vo + j * n) n = some qs)
    (hreduced : μ.store.readBlock (L + 1) 0 n = some reduced)
    (hnext : μ.store.readBlock V (vo + (j + 1) * n) n = some next)
    (hnroom : vo + (j + 1) * n + n ≤ μ.store.len V)
    (hβ₀ : μ.store.get C (co + cap + j + 1) = some β₀)
    (hnextzero : decv dec n next = 0) (hβzero : dec β₀ = 0) :
    Writes .total I τ saveAndNormalize ⟨[n, cap, bo, vo, co, j], [B, V, C, L, L + 1, L + 2]⟩
      (Fp.blocks [(L, 0), (L + 2, 0), (C, co + cap + j + 1), (V, vo + (j + 1) * n)] [n, 2, 1, n])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ ys β',
        μ'.store.readBlock L 0 n = some qs ∧
        μ'.store.readBlock V (vo + (j + 1) * n) n = some ys ∧
        μ'.store.get C (co + cap + j + 1) = some β' ∧
        decv dec n ys = ‖WithLp.toLp 2 (decv dec n reduced)‖⁻¹ • decv dec n reduced ∧
        dec β' = ‖WithLp.toLp 2 (decv dec n reduced)‖ ∧ ∃ σ,
          μ'.store.get (L + 2) 0 = some σ ∧
          dec σ = decv dec n reduced ⬝ᵥ decv dec n reduced) μ := by
  step hB.dot as μ₁ hfr₁ ⟨hpos₁, σ, hσ, hdot⟩
  step hB.copy as μ₂ hfr₂ ⟨hpos₂, copied, hcopied, hcopy⟩
  subst copied
  refine Writes.mono (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₂.length_eq, hfr₁.length_eq]; omega)
    (normalize_writes hS hM hB hok hCmp (by omega) (by omega) (by omega) (by omega)
      (by omega) hVC (by
        simp only [Mem.live_cons, Mem.live_nil, and_true, hfr₂.length_eq, hfr₁.length_eq]; omega)
      (by kept) (by kept) (by kept) (by kept) (dotExactRel_decoded hdot)
      hnextzero hβzero (by
        simp only [Mem.room_cons, Mem.room_nil, and_true, hfr₂.len_eq, hfr₁.len_eq]
        exact ⟨hnroom, by omega⟩))) (by fp_sub) ?_
  rintro μ₃ hfr₃ ⟨hpos₃, ys, β', hys, hβ', hnormalized, hnormβ⟩
  exact ⟨by simp [hpos₃, hpos₂, hpos₁], ys, β', by kept, hys, hβ', hnormalized, hnormβ,
    σ, by kept, dotExactRel_decoded hdot⟩

/-- A full round executes for every initialized output column, including exact breakdown.
The output records the raw residual, both classical passes, and the final normalization. -/
theorem advance_writes {M : Machine K} {dec : K → ℝ} {n cap j L B V C bo vo co : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hA : IsExactMatvec dec A I) (hCmp : IsCmp dec I)
    {τ : Tape K} {μ : Mem K} {ps qs basis next : List K} {β β₀ ν₀ : K}
    (hj : j < cap) (hVL : V < L) (hCL : C < L) (hVC : V ≠ C)
    (hlen : μ.store.length = L + 3) (hw : μ.store.len (L + 1) = n)
    (hp : μ.store.len L = n)
    (ht : μ.store.len (L + 2) = 2) (hroom : co + 3 * cap + 2 ≤ μ.store.len C)
    (hps : μ.store.readBlock L 0 n = some ps)
    (hqs : μ.store.readBlock V (vo + j * n) n = some qs)
    (hbasis : μ.store.readBlock V vo ((j + 1) * n) = some basis)
    (hnext : μ.store.readBlock V (vo + (j + 1) * n) n = some next)
    (hnroom : vo + (j + 1) * n + n ≤ μ.store.len V)
    (hβ : μ.store.get C (co + cap + j) = some β)
    (hβ₀ : μ.store.get C (co + cap + j + 1) = some β₀)
    (hν₀ : μ.store.get C (co + 2 * cap + 2 + j) = some ν₀)
    (hnextzero : decv dec n next = 0) (hβzero : dec β₀ = 0) (hνzero : dec ν₀ = 0) :
    Writes .total I τ advance ⟨[n, cap, bo, vo, co, j], [B, V, C, L, L + 1, L + 2]⟩
      (Fp.blocks [(L, 0), (L + 1, 0), (L + 2, 0), (C, co + j), (C, co + cap + j + 1),
        (C, co + 2 * cap + 2 + j), (V, vo + (j + 1) * n)] [n, n, 2, 1, 1, 1, n])
      (fun μ' => μ'.pos = μ.pos ∧ ∃ raw reduced ys α ν β',
        μ'.store.readBlock L 0 n = some qs ∧
        μ'.store.readBlock (L + 1) 0 n = some reduced ∧
        μ'.store.readBlock V (vo + (j + 1) * n) n = some ys ∧
        μ'.store.get C (co + j) = some α ∧ μ'.store.get C (co + 2 * cap + 2 + j) = some ν ∧
        μ'.store.get C (co + cap + j + 1) = some β' ∧
        dec α = lanczosAlpha A ⟨decv dec n ps, decv dec n qs, dec β⟩ ∧
        decv dec n raw = A *ᵥ decv dec n qs - dec β • decv dec n ps - dec α • decv dec n qs ∧
        dec ν = ‖WithLp.toLp 2 (decv dec n raw)‖ ∧
        TwoPassOut dec 0 0 n (j + 1) basis raw reduced ∧
        decv dec n ys = ‖WithLp.toLp 2 (decv dec n reduced)‖⁻¹ • decv dec n reduced ∧
        dec β' = ‖WithLp.toLp 2 (decv dec n reduced)‖ ∧ ∃ σ,
          μ'.store.get (L + 2) 0 = some σ ∧
          dec σ = decv dec n reduced ⬝ᵥ decv dec n reduced) μ := by
  refine Writes.seq_le (updateAndSweep_writes (n := n) (cap := cap) (j := j) (L := L)
    (B := B) (V := V) (C := C) (bo := bo) (vo := vo) (co := co) (τ := τ)
    (μ := μ) (ps := ps) (qs := qs) (basis := basis) (β := β) (ν₀ := ν₀)
    hS hM hB hok hA hCmp hj hVL hCL hVC
    hlen hw ht hroom hps hqs hbasis hβ hν₀ hνzero) (by
      intro b i h
      simp only [Fp.blocks, Pi.sup_apply, sup_Prop_eq, Pi.bot_apply] at h ⊢
      tauto) ?_
  rintro μ₁ hfr₁ ⟨hpos₁, raw, reduced, α, ν, hreduced, hα, hν, hαdec, hraw, hnormν, hpasses⟩
  refine Writes.mono (saveAndNormalize_writes (n := n) (cap := cap) (j := j) (L := L)
    (B := B) (V := V) (C := C) (bo := bo) (vo := vo) (co := co) (τ := τ)
    (μ := μ₁) (qs := qs) (reduced := reduced) (next := next) (β₀ := β₀)
    hS hM hB hok hCmp hVL hCL hVC
    (by simpa only [hfr₁.length_eq] using hlen) (by simpa only [hfr₁.len_eq] using hp)
    (by simpa only [hfr₁.len_eq] using ht) (by simp only [hfr₁.len_eq]; omega)
    (by kept) hreduced (by kept) (by simpa only [hfr₁.len_eq] using hnroom)
    (by kept) hnextzero hβzero) (by
      intro b i h
      simp only [Fp.blocks, Pi.sup_apply, sup_Prop_eq, Pi.bot_apply] at h ⊢
      tauto) ?_
  rintro μ₂ hfr₂ ⟨hpos₂, ys, β', hprev, hys, hβ', hnormalized, hnormβ, σ, hσ, hdot⟩
  exact ⟨hpos₂.trans hpos₁, raw, reduced, ys, α, ν, β', hprev, by kept, hys, by kept,
    by kept, hβ', hαdec, hraw, hnormν, hpasses, hnormalized, hnormβ, σ, hσ, hdot⟩

end NLAlib.Krylov.Lanczos.Reorth
