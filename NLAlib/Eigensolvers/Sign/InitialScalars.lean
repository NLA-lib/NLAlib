/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.Sign.Alg
public import NLAlib.Ops.Logic.Scalar

/-!
# Explicit arithmetic for the Newton–Schulz stopping threshold

The three actual scalar calls are evaluated as one straight-line block. The denominator is a
stored machine literal, including its rounding, and division is the machine's total word
function. Numerical nonzero and accuracy hypotheses belong to the numerical theorem.

## Main results

* `NLAlib.Sign.writes_initialScalars` computes the threshold and its signed bounds.
-/

@[expose] public section

namespace NLAlib.Sign

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] {M : Ops.Machine K}

/-- The executed scalar block stores the computed threshold, its negative and literal one.
No initial contents of the output region are needed. -/
theorem writes_initialScalars {I : Interp Op Tst K} (hS : IsScalar M I) {τ : Tape K}
    {eps den : K} {e d t : ℕ × ℕ} {m : Mem K}
    (he : m.store.get e.1 e.2 = some eps) (hd : m.store.get d.1 d.2 = some den)
    (ht : t.2 + 5 ≤ m.store.len t.1) :
    Writes .total I τ initialScalars.body (Env.frame [] [e, d, t])
      (Store.inBlock t.1 t.2 5)
      (fun μ => μ.pos = m.pos ∧ μ.store.get t.1 t.2 = some (M.div eps den) ∧
        μ.store.get t.1 (t.2 + 4) = some (M.neg (M.div eps den)) ∧
        μ.store.get t.1 (t.2 + 3) = some (M.lit 1)) m := by
  let xs : List (ScalarIns ScalarOp) :=
    [⟨.div, [⟨0, .var 0⟩, ⟨1, .var 1⟩], ⟨2, .var 2⟩⟩,
      ⟨.neg, [⟨2, .var 2⟩], ⟨2, .add (.var 2) (.const 4)⟩⟩,
      ⟨.lit 1, [], ⟨2, .add (.var 2) (.const 3)⟩⟩]
  let ws := [(t, M.div eps den), ((t.1, t.2 + 4), M.neg (M.div eps den)),
    ((t.1, t.2 + 3), M.lit 1)]
  have hev : ScalarIns.evalBlock M.eval (Env.frame [] [e, d, t]) xs m.store.cellFn = some ws := by
    simp [xs, ws, ScalarIns.evalBlock, Operand.evalList, Operand.eval, Env.frame,
      IExp.eval, Store.cellFn, Machine.eval, he, hd]
  have hr : ∀ w ∈ ws, w.1.2 < m.store.len w.1.1 := by
    intro w hw
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> dsimp <;> omega
  have h := writes_machineScalarBlock (τ := τ) hS hev hr
  change Writes .total I τ initialScalars.body _ _ _ m at h
  refine h.mono ?_ ?_
  · intro b i hi
    rcases t with ⟨tb, toff⟩
    simp only [ws, List.map_cons, List.map_nil, Fp.cells, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      exact ⟨rfl, by omega, by omega⟩
  · rintro μ _ rfl
    have h0 : t.2 < m.store.len t.1 := by omega
    have h3 : t.2 + 3 < m.store.len t.1 := by omega
    have h4 : t.2 + 4 < m.store.len t.1 := by omega
    simp [ws, Mem.updCells, Store.get_upd_self, Store.get_upd_of_ne, h0, h3, h4]

end NLAlib.Sign
