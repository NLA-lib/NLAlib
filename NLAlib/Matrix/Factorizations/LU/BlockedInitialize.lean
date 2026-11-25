/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.LU.Initialize

/-!
# Copy-first LU initialization with overlapping source

The ordinary initializer already copies the matrix before clearing its factors. This operand
judgment exposes that same tree with only residual scratch apart from the source and factors.
It supports an outer blocked routine whose source overlaps either reported factor.

## Main results

* `NLAlib.LU.initializeFactors_writes_of_scratch_apart`: the existing actual initializer,
  without source/factor separation.
-/

@[expose] public section

namespace NLAlib.LU

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Inhabited K]

/-- The existing copy-first initializer runs with source/factor overlap. Residual scratch is
separate from all caller operands, and the two factors remain separate from each other. -/
theorem initializeFactors_writes_of_scratch_apart {M : Machine K}
    {I : Interp Op Tst K} (hI : IsScalar M I) {N : ℕ} {τ : Tape K} {m : Mem K}
    {A R L U : ℕ × ℕ} {as : List K} (hlive : m.Live [A, R, L, U])
    (hRA : R.1 ≠ A.1) (hRL : R.1 ≠ L.1) (hRU : R.1 ≠ U.1) (hLU : L.1 ≠ U.1)
    (has : m.store.readBlock A.1 A.2 (N * N) = some as)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1)
    (hUroom : U.2 + N * N ≤ m.store.len U.1) :
    Writes .total I τ (initializeFactors (Op := Op) (Tst := Tst)).body
      (Env.frame [N] [A, R, L, U])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N) ⊔
        Store.inBlock U.1 U.2 (N * N))
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock R.1 R.2 (N * N) = some as ∧
        m'.store.readBlock L.1 L.2 (N * N) = some (List.replicate (N * N) (M.lit 0)) ∧
        m'.store.readBlock U.1 U.2 (N * N) = some (List.replicate (N * N) (M.lit 0))) m := by
  obtain ⟨hlA, hlR, hlL, hlU⟩ : A.1 < m.store.length ∧ R.1 < m.store.length ∧
      L.1 < m.store.length ∧ U.1 < m.store.length := by
    simpa only [Mem.live_cons, Mem.live_nil, and_true] using hlive
  have hAR : A.1 ≠ R.1 := hRA.symm
  call (copyLoopRoutine_meets hI (fun _ => True)) [N * N] (A, R)
    as m₁ hfr₁ hpos₁ (rs) hcopy
  have he : rs = as := (List.cons.inj hcopy).1
  subst rs
  call (fillRoutine_meets (hI (.lit 0))) [N * N] (L)
    as m₂ hfr₂ hpos₂ (ls) hfillL
  have hR₂ : m₂.store.readBlock R.1 R.2 (N * N) = some as := by keep
  have heL : ls = List.replicate (N * N) (M.lit 0) := hfillL
  subst ls
  call (fillRoutine_meets (hI (.lit 0))) [N * N] (U)
    as m₃ hfr₃ hpos₃ (us) hfillU
  have hR₃ : m₃.store.readBlock R.1 R.2 (N * N) = some as := by keep
  have hL₃ : m₃.store.readBlock L.1 L.2 (N * N) =
      some (List.replicate (N * N) (M.lit 0)) := by keep
  have heU : us = List.replicate (N * N) (M.lit 0) := hfillU
  exact ⟨by omega, hR₃, hL₃, by simpa only [heU] using hus⟩

end NLAlib.LU
