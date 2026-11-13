/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Zero
public import NLAlib.Krylov.Lanczos.NormalizationInterface
public import NLAlib.Krylov.Lanczos.InitialState

/-!
# Total initialization of a stored Lanczos recurrence

Zero-filled output tails support both immediate breakdown and early loop termination. The
coefficient allocation may have an extra suffix, which is initialized to zero for reuse by
reorthogonalized Lanczos.

## Main results

* `NLAlib.Krylov.Lanczos.initialize_writes` establishes the initial stored state.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos

open Ops
open scoped Matrix

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- The initializer succeeds even for a zero input, and leaves every extra coefficient cell
zero. Only its output blocks and the caller's scratch buffers may change. -/
theorem initialize_writes {M : Machine K} {dec : K → ℝ} {n cap clen L : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : ExactModel dec M) (hB : IsExactBlas1 dec ok I)
    (hok : ok n) (hCmp : IsCmp dec I) {τ : Tape K} {μ : Mem K}
    {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hBL : B.1 < L) (hVL : V.1 < L) (hCL : C.1 < L)
    (hlen : μ.store.length = L + 3) (hp : μ.store.len L = n)
    (ht : μ.store.len (L + 2) = 2) (hclen : 2 * cap + 2 ≤ clen)
    (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hv : V.2 + (cap + 1) * n ≤ μ.store.len V.1)
    (hc : C.2 + clen ≤ μ.store.len C.1) :
    Writes .total I τ initializeState
      (Env.frame [n, cap, clen] [B, V, C, (L, 0), (L + 2, 0)])
      (Fp.blocks [V, C] [(cap + 1) * n, clen] ⊔ Fp.above L)
      (fun μ' => μ'.pos = μ.pos ∧ State dec A (decv dec n bs) cap 0 V C L μ'.store ∧
        ∀ i, 2 * cap + 2 ≤ i → i < clen →
          StoresCell dec (C.1, C.2 + i) 0 μ'.store) μ := by
  refine Writes.seq_le (writes_frame rfl rfl (by simp [Mem.Live]; omega)
    (zero_writes hS (by omega) hv)) (by fp_sub) fun μ₁ hfr₁ ⟨hpos₁, hv₁⟩ => ?_
  have hc₁ : C.2 + clen ≤ μ₁.store.len C.1 := by simpa [hfr₁.len_eq] using hc
  refine Writes.seq_le (writes_frame rfl rfl (by simp [Mem.Live, hfr₁.length_eq]; omega)
    (zero_writes hS (by rw [hfr₁.length_eq]; omega) hc₁)) (by fp_sub)
    fun μ₂ hfr₂ ⟨hpos₂, hc₂⟩ => ?_
  have hp₂ : μ₂.store.len L = n := by rw [hfr₂.len_eq, hfr₁.len_eq]; exact hp
  refine Writes.seq_le (writes_frame rfl rfl (by
    simp [Mem.Live, hfr₂.length_eq, hfr₁.length_eq]; omega)
    (zero_writes hS (by rw [hfr₂.length_eq, hfr₁.length_eq]; omega)
      (by simpa only [Nat.zero_add] using hp₂.ge)))
    (by fp_sub) fun μ₃ hfr₃ ⟨hpos₃, hp₃⟩ => ?_
  step hB.dot as μ₄ hfr₄ ⟨hpos₄, σ, hσ, hself⟩
  have hV : StoresVec dec V (0 : Fin ((cap + 1) * n) → ℝ) μ₄.store :=
    StoresVec.of_zero_readBlock (by kept) (by simpa using hM.lit 0)
  have hC : StoresVec dec C (0 : Fin clen → ℝ) μ₄.store :=
    StoresVec.of_zero_readBlock (by kept) (by simpa using hM.lit 0)
  have hP : StoresVec dec (L, 0) (0 : Fin n → ℝ) μ₄.store :=
    StoresVec.of_zero_readBlock (by kept) (by simpa using hM.lit 0)
  obtain ⟨qs, hqs, hqzero⟩ := hV.zero_sub (n := n) (o := 0)
    (by simp only [Nat.add_mul, Nat.one_mul]; omega)
  obtain ⟨β₀, hβ₀, hbzero⟩ := hC.cell ⟨2 * cap + 1, by omega⟩
  have hσdec : dec σ = decv dec n bs ⬝ᵥ decv dec n bs := dotExactRel_decoded hself
  have hln : μ₄.Live [B, (L + 2, 0), V, (C.1, C.2 + 2 * cap + 1)] := by
    simp [Mem.Live, hfr₄.length_eq, hfr₃.length_eq, hfr₂.length_eq, hfr₁.length_eq]; omega
  have hn : n ≤ (cap + 1) * n := by
    simpa only [Nat.add_mul, Nat.one_mul] using Nat.le_add_left n (cap * n)
  have hzn : μ₄.Room [V, (C.1, C.2 + 2 * cap + 1)] [n, 1] := by
    simp only [Mem.room_cons, Mem.room_nil, and_true]
    simp only [hfr₄.len_eq, hfr₃.len_eq, hfr₂.len_eq, hfr₁.len_eq]
    constructor <;> omega
  refine (writes_frame rfl rfl (by
    simp only [Mem.live_cons, Mem.live_nil, and_true] at hln ⊢
    tauto)
    (normalize_writes (w := B) (s := (L + 2, 0)) (q := V)
      (b := (C.1, C.2 + 2 * cap + 1)) hS hM hB hok hCmp (by omega) hBV hBC (by omega) (by omega) hVC
      hln (by kept) hσ (by simpa using hqs) hβ₀ hσdec hqzero hbzero hzn)).mono
    (by fp_sub) ?_
  rintro μ₅ hfr₅ ⟨hpos₅, ys, β, hys, hβ, hnormq, hnormβ⟩
  have hguard : ∃ σ, μ₅.store.get (L + 2) 0 = some σ ∧ 0 ≤ dec σ ∧
      (0 < dec σ ↔ decv dec n bs ≠ 0) := by
    refine ⟨σ, by kept, ?_, ?_⟩
    · rw [hσdec]; exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    · rw [hσdec]
      constructor
      · intro hpos hz
        simp [hz] at hpos
      · intro hne
        exact lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
          (fun hz => hne (dotProduct_self_eq_zero.mp hz.symm))
  have hinit := state_zero_of_normalize (A := A) hclen hVC hVL hCL hV hC hP hfr₅
    ⟨ys, by simpa using hys, by simpa [lanczosState] using hnormq⟩
    ⟨β, hβ, hnormβ⟩ hguard
  exact ⟨by simp [hpos₅, hpos₄, hpos₃, hpos₂, hpos₁], hinit⟩

end NLAlib.Krylov.Lanczos
