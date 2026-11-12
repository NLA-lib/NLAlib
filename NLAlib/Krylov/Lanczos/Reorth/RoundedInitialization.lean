/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Reorth.RoundedState

/-!
# Initializing the rounded reorthogonalized Lanczos history

The ordinary rounded initializer also zeroes the raw-norm suffix. Its shared suffix theorem
supplies the full reorthogonalized archive without repeating initialization execution.

## Main results

* `NLAlib.Krylov.Lanczos.Reorth.Rounded.initialize_writes`: total initial history and archive.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Reorth.Rounded

open Ops

variable {K Op Tst : Type} [Inhabited K]
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

/-- Every requested output cell is initialized, including the raw-norm suffix. Zero input
uses guarded normalization; every cap, including zero, has a derived initial history. -/
theorem initialize_writes {M : Machine K} {dec : K → ℝ} {n cap L : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {em u E : ℝ} {e : Blas1Err}
    {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec e ok I)
    (hok : ok n) (hCmp : IsCmp dec I) (hprec : Lanczos.Rounded.Precision em u E e n)
    {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hBL : B.1 < L) (hVL : V.1 < L) (hCL : C.1 < L)
    (hlen : μ.store.length = L + 3) (hp : μ.store.len L = n)
    (ht : μ.store.len (L + 2) = 2)
    (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hv : V.2 + (cap + 1) * n ≤ μ.store.len V.1)
    (hc : C.2 + (3 * cap + 2) ≤ μ.store.len C.1) :
    Writes .total I τ initializeState
      (Env.frame [n, cap, 3 * cap + 2] [B, V, C, (L, 0), (L + 2, 0)])
      (Fp.blocks [V, C] [(cap + 1) * n, 3 * cap + 2] ⊔ Fp.above L)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ z nus,
        State dec A (decv dec n bs) em u E e cap 0 V C L z nus μ'.store) μ := by
  refine (Lanczos.Rounded.initialize_writes_with_suffix (A := A)
    hS hM hB hok hCmp hprec hBV hBC hVC hBL hVL hCL hlen hp ht (by omega)
    hb hv hc).mono le_rfl ?_
  rintro μ' _ ⟨hpos, z, hstate, hsuffix⟩
  refine ⟨hpos, z, 0, ⟨?_, ?_, hstate.future_v, hstate.future_coeff⟩,
    hstate.prev, hstate.guard⟩
  · exact History.initial hstate.toOutcome
  · refine ⟨hstate.packed, ?_⟩
    intro j hj
    simpa only [Nat.not_lt_zero, ↓reduceIte, Nat.add_assoc] using
      hsuffix (2 * cap + 2 + j) (by omega) (by omega)

end NLAlib.Krylov.Lanczos.Reorth.Rounded
