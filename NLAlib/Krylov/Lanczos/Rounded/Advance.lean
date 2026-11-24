/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Rounded.Update
public import NLAlib.Krylov.Lanczos.Rounded.Normalization
public import NLAlib.Krylov.Lanczos.State

/-!
# Successful rounded Lanczos rounds

The Paige update, residual self-dot, previous-vector copy and guarded normalization compose
under explicit relative-error bounds for the self-dot and square root. Actual intermediates
and output words retain the local rounding relations; no successful-execution premise is used.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.advance_writes` exposes local bounds after a complete round.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- One complete round succeeds for readable inputs and initialized zero next outputs.
Its actual readback exposes the raw residual, normalized direction, and squared-norm guard.

A fragment of `NLAlib.Krylov.Lanczos.solveRoutine`: one round of its loop, on the scratch the
solver allocates and the columns of `V` and `C` at the round index. -/
theorem advance_writes {M : Machine K} {dec : K → ℝ} {n cap j L B V C bo vo co : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    {em u : ℝ} {ε : Blas1Err}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hu : u < 1) (hd : ε.dot n < 1)
    (hB : IsBlas1 dec ε ok I)
    (hok : ok n) (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
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
      (fun μ' => μ'.pos = μ.pos ∧ ∃ first raw ys α β' σ,
        μ'.store.readBlock L 0 n = some qs ∧
        μ'.store.readBlock V (vo + (j + 1) * n) n = some ys ∧
        μ'.store.get C (co + j) = some α ∧
        μ'.store.get C (co + cap + j + 1) = some β' ∧
        μ'.store.get (L + 2) 0 = some σ ∧
        UpdateBounds em (ε.dot n) ε.axpy A (decv dec n ps) (decv dec n qs)
          (decv dec n first) (decv dec n raw) (dec β) (dec α) ∧
        IsNrm2Err dec (ε.dot n) u n (vec raw) β' ∧
        IsScalErr dec ε.scal n β' (vec raw) (vec ys) ∧
        (decv dec n raw = 0 → decv dec n ys = 0) ∧
        IsDotErr dec (ε.dot n) n (vec raw) (vec raw) σ) μ := by
  unfold advanceFp
  refine Writes.seq_le (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true]; omega)
    (update_writes hS hM hB hok hA hVC hVL hCL hCL hlen hw ht ha hps hqs hβ))
    (by fp_sub) ?_
  rintro μ₁ hfr₁ ⟨hpos₁, first, raw, α, hraw, hα, hbounds⟩
  step hB.dot as μ₂ hfr₂ ⟨hpos₂, σ, hσ, hdot⟩
  step hB.copy as μ₃ hfr₃ ⟨hpos₃, copied, hcopied, hcopy⟩
  subst copied
  have hWV : L + 1 ≠ V := by omega
  have hWC : L + 1 ≠ C := by omega
  have hTV : L + 2 ≠ V := by omega
  have hTC : L + 2 ≠ C := by omega
  have hsrc : μ₃.store.readBlock (L + 1) 0 n = some raw := by kept
  have hsig : μ₃.store.readBlock (L + 2) 0 1 = some [σ] :=
    Store.readBlock_one_of_get (by kept)
  have hnxt : μ₃.store.readBlock V (vo + (j + 1) * n) n = some next := by kept
  have hcpl : μ₃.store.readBlock C (co + cap + j + 1) 1 = some [β₀] :=
    Store.readBlock_one_of_get (by kept)
  call (normalizeRoutine_meets_rounded (Op := Op) (Tst := Tst) hS hM hu hd hB hok hCmp) [n]
    ((L + 1, 0), (L + 2, 0), (V, vo + (j + 1) * n), (C, co + cap + j + 1))
    (pre := ⟨rfl, hdot, hnextzero, hβzero⟩)
    as μ₄ hfr₄ hpos₄ (ys, cs) hpost
  obtain ⟨β', hβ', rfl⟩ := Store.readBlock_one_eq_some.mp hcs
  obtain ⟨hnormβ, hscaled, hzero⟩ := hpost
  exact ⟨by simp [hpos₄, hpos₃, hpos₂, hpos₁], first, raw, ys, α, β', σ,
    by kept, hys, by kept, hβ', by kept, hbounds, hnormβ, hscaled, hzero, hdot⟩

end NLAlib.Krylov.Lanczos.Rounded
