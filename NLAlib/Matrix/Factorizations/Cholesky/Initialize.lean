/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Level1
public import NLAlib.Ops.Blas.Fill

/-!
# Initial storage for right-looking Cholesky

The source is copied before the output factor is initialized with zero literals. Ordinary,
semidefinite and in-place Cholesky use this same scalar tree. Its word guarantee requires no
arithmetic accuracy law. The stronger operand-form statement permits source/output overlap;
the routine interface gives the usual separate-output layout of the same body.

## Main results

* `NLAlib.Cholesky.initializeLower_meets`: copied residual and literal-zero factor.
* `NLAlib.Cholesky.initializeLower_writes_of_scratch_apart`: the body at overlapping source/output.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Copy the source into residual scratch, then initialize the factor with zero literals. -/
def initializeLower : Routine Op Tst := routine% [n] (A : n * n) → (R : n * n, L : n * n) {
  run copyLoopRoutine [n * n] (A, R);
  run (fillRoutine (Has.inj (ScalarOp.lit 0))) [n * n] (L)
}

/-- The exact word result: a copied input and a completely initialized factor. -/
def initializeLowerSpec (M : Machine K) : Routine.Spec K :=
  spec% [n] (as) → (rs, ls) ensures
    rs = as ∧ ls = List.replicate (n * n) (M.lit 0)

variable [Inhabited K]

/-- The common initialization body with source and factor allowed to overlap. This is the
one-body/several-layouts exception: ordinary and in-place right-looking Cholesky run this
same tree, while only residual scratch must be apart. Source copying precedes every factor
write. No source/output admission predicate or successful-run premise is introduced. -/
theorem initializeLower_writes_of_scratch_apart {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) {N : ℕ} {τ : Tape K} {m : Mem K} {A R L : ℕ × ℕ} {as : List K}
    (hlive : m.Live [A, R, L]) (hRA : R.1 ≠ A.1) (hRL : R.1 ≠ L.1)
    (has : m.store.readBlock A.1 A.2 (N * N) = some as)
    (hRroom : R.2 + N * N ≤ m.store.len R.1)
    (hLroom : L.2 + N * N ≤ m.store.len L.1) :
    Writes .total I τ (initializeLower (Op := Op) (Tst := Tst)).body
      (Env.frame [N] [A, R, L])
      (Store.inBlock R.1 R.2 (N * N) ⊔ Store.inBlock L.1 L.2 (N * N))
      (fun m' => m'.pos = m.pos ∧
        m'.store.readBlock R.1 R.2 (N * N) = some as ∧
        m'.store.readBlock L.1 L.2 (N * N) =
          some (List.replicate (N * N) (M.lit 0))) m := by
  obtain ⟨hlA, hlR, hlL, -⟩ :=
    (show A.1 < m.store.length ∧ R.1 < m.store.length ∧ L.1 < m.store.length ∧ True from
      by simpa only [Mem.live_cons, Mem.live_nil] using hlive)
  call (copyLoopRoutine_meets hI (fun _ => True)) [N * N] (A, R)
    as m₁ hfr₁ hpos₁ (rs) hcopy
  have hcopy_eq : rs = as := (List.cons.inj hcopy).1
  rw [hcopy_eq] at hrs
  call (fillRoutine_meets (hI (.lit 0))) [N * N] (L)
    as m₂ hfr₂ hpos₂ (ls) hfill
  have hR₂ : m₂.store.readBlock R.1 R.2 (N * N) = some as := by keep
  have hfill_eq : ls = List.replicate (N * N) (M.lit 0) := hfill
  exact ⟨by omega, hR₂, by simpa only [hfill_eq] using hls⟩

/-- Initialization meets its complete word specification under scalar contracts alone. -/
theorem initializeLower_meets {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (initializeLower (Op := Op) (Tst := Tst)).Meets I (initializeLowerSpec M) := by
  routine_intro [n] (A, R, L) reads (as)
  obtain ⟨hRroom, hLroom⟩ := hroom
  refine (initializeLower_writes_of_scratch_apart hI hlive (Ne.symm hAR) hRL has
    hRroom hLroom).mono (by fp_sub) ?_
  intro m' hfr ⟨hpos, hR, hL⟩
  exact ⟨by omega, [as, List.replicate (n * n) (M.lit 0)],
    Mem.readBlocks_of_cons hR (Mem.readBlocks_of_cons hL rfl), rfl, rfl⟩

end NLAlib.Cholesky
