/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Node
public import NLAlib.Ops.Logic.ScalarOutput
public import NLAlib.Ops.Logic.BlockSequence
public import NLAlib.Ops.Logic.IndexLiteral
public import NLAlib.Ops.Logic.Step

/-!
# Actual rounded scalar setup of a bisection node

The node's scalar subprograms execute the displayed machine operations in order. Their
contracts concern the words actually read and written, independently of numerical accuracy.
Straight-line arithmetic uses the shared pure scalar-block evaluator and packed-output rule.

## Main results

* `NLAlib.SpectralBisection.writes_signParameters`: stored tolerance and doubled radius.
* `NLAlib.SpectralBisection.writes_nodeScalars`: five actual rounded scalar setup words.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops

/-- The sign parameters are the supplied tolerance and the actual product of the stored two
and radius words. Source and destination regions may lie in one buffer when disjoint. -/
theorem writes_signParameters {K Op Tst : Type} [Has ScalarOp Op]
    {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I)
    {τ : Tape K} {μ : Mem K} {d : ℕ} {lv par two sp : ℕ × ℕ} (R β t : K)
    (hR : μ.store.get lv.1 (lv.2 + 2 * d) = some R)
    (hβ : μ.store.get par.1 (par.2 + 2) = some β)
    (ht : μ.store.get two.1 two.2 = some t)
    (hroom : sp.2 + 2 ≤ μ.store.len sp.1)
    (hsep : Fp.Disj (Fp.cells [(lv.1, lv.2 + 2 * d), two])
      (Store.inBlock sp.1 sp.2 2)) :
    Writes .total I τ (signParameters (Op := Op) (Tst := Tst)).body
      (Env.frame [d] [lv, par, two, sp]) (Store.inBlock sp.1 sp.2 2)
      (fun μ' => μ'.pos = μ.pos ∧ μ'.store.readBlock sp.1 sp.2 2 =
        some [β, M.mul t R]) μ := by
  have hRt : (lv.1, lv.2 + 2 * d) ≠ (sp.1, sp.2) := by
    simpa only [ne_eq, Prod.mk.injEq, not_and_or] using
      hsep.ne_cells (b := lv.1) (i := lv.2 + 2 * d)
        (by simp [Fp.cells]) ⟨rfl, le_rfl, by omega⟩
  have htwo : two ≠ (sp.1, sp.2) := by
    change (two.1, two.2) ≠ (sp.1, sp.2)
    simpa only [ne_eq, Prod.mk.injEq, not_and_or] using
      hsep.ne_cells (b := two.1) (i := two.2)
        (by simp [Fp.cells]) ⟨rfl, le_rfl, by omega⟩
  let xs : List (ScalarIns ScalarOp) :=
    [⟨.copy, [⟨1, .var 2 + .const 2⟩], ⟨3, .var 4⟩⟩,
      ⟨.mul, [⟨2, .var 3⟩, ⟨0, .var 1 + .const 2 * .var 0⟩], ⟨3, .var 4 + .const 1⟩⟩]
  change Writes .total I τ (Stmt.scalarBlock (xs.map ScalarIns.lift)) _ _ _ _
  simpa only [List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, Nat.zero_add, ite_true,
    Nat.one_ne_zero, ite_false] using
    (writes_machineScalarBlock_readBlock hS (n := 2)
      (v := fun i => if i = 0 then β else M.mul t R) (by
        simp [xs, ScalarIns.evalBlock, Operand.evalList, Operand.eval, Env.frame, IExp.eval,
          Store.cellFn, Machine.eval, hR, hβ, ht, hRt, htwo, List.range_succ]) hroom)

/-- The first five scalar words of a node retain the rounded half-radius, its negation,
the machine literal of `L+d`, the rounded radius quotient and the sampled shift. All scalar
operations remain explicit; a division requires no meta-level successful-run assumption. -/
theorem writes_nodeScalars {K Op Tst : Type} [Has ScalarOp Op] [Has IndexOp Op]
    {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I) (hL : IsIndexLit M I)
    {τ : Tape K} {μ : Mem K} {L d lo : ℕ} {lv c su t : ℕ × ℕ} (R two U : K)
    (hR : μ.store.get lv.1 (lv.2 + 2 * d) = some R)
    (htwo : μ.store.get c.1 (c.2 + 1) = some two)
    (hU : μ.store.get su.1 (su.2 + lo) = some U)
    (hroom : t.2 + 5 ≤ μ.store.len t.1)
    (hsep : Fp.Disj (Store.inBlock t.1 t.2 5)
      (Fp.cells [(lv.1, lv.2 + 2 * d), (su.1, su.2 + lo)])) :
    Writes .total I τ (nodeScalars (Op := Op) (Tst := Tst)).body
      (Env.frame [L, d, lo] [lv, c, su, t])
      (Fp.blocks [t, (t.1, t.2 + 2), (t.1, t.2 + 3)] [2, 1, 2])
      (fun μ' => μ'.pos = μ.pos ∧
        μ'.readBlocks [t, (t.1, t.2 + 2), (t.1, t.2 + 3)] [2, 1, 2] =
          some [[M.div R two, M.neg (M.div R two)], [M.lit ((L + d : ℕ) : ℚ)],
            [M.div R (M.lit ((L + d : ℕ) : ℚ)),
              M.mul (M.div R (M.lit ((L + d : ℕ) : ℚ))) U]]) μ := by
  let half : K := M.div R two
  let level : K := M.lit ((L + d : ℕ) : ℚ)
  let quotient : K := M.div R level
  let xs : List (ScalarIns ScalarOp) :=
    [⟨.div, [⟨0, .var 3 + .const 2 * .var 1⟩, ⟨1, .var 4 + .const 1⟩], ⟨3, .var 6⟩⟩,
      ⟨.neg, [⟨3, .var 6⟩], ⟨3, .var 6 + .const 1⟩⟩]
  apply Writes.seq_assoc_iff.mp
  refine (writes_machineScalarBlock_readBlock hS (xs := xs) (z := t) (n := 2)
    (v := fun i => if i = 0 then half else M.neg half) ?_ (by room)).seq_readBlock
    (by disjoint) ?_
  · simp [xs, ScalarIns.evalBlock, Operand.evalList, Operand.eval, Env.frame, IExp.eval,
      Store.cellFn, Machine.eval, hR, htwo, List.range_succ, half]
  intro μ₁ hfr₁ hp₁ hhalf
  refine (writes_indexLit hL rfl rfl (by room)).readBlock_of_get.seq_readBlock
    (by disjoint) ?_
  intro μ₂ hfr₂ hp₂ hlevel
  have hframe : μ.store.EqOff (Store.inBlock t.1 t.2 5) μ₂.store :=
    (hfr₁.mono (by fp_sub)).trans (hfr₂.mono (by fp_sub))
  have hR₂ : μ₂.store.get lv.1 (lv.2 + 2 * d) = some R :=
    (hframe.get_eq (fun hf => hsep _ _ hf (by simp [Fp.cells]))).trans hR
  have hU₂ : μ₂.store.get su.1 (su.2 + lo) = some U :=
    (hframe.get_eq (fun hf => hsep _ _ hf (by simp [Fp.cells]))).trans hU
  have hlevel₂ : μ₂.store.get t.1 (t.2 + 2) = some level := by
    exact Store.get_of_readBlock hlevel (j := 0) Nat.zero_lt_one level
  have hUt : (su.1, su.2 + lo) ≠ (t.1, t.2 + 3) := by
    simpa only [ne_eq, Prod.mk.injEq, not_and_or] using
      hsep.symm.ne_cells (b := su.1) (i := su.2 + lo)
        (by simp [Fp.cells]) ⟨rfl, by omega, by omega⟩
  let ys : List (ScalarIns ScalarOp) :=
    [⟨.div, [⟨0, .var 3 + .const 2 * .var 1⟩, ⟨3, .var 6 + .const 2⟩],
        ⟨3, .var 6 + .const 3⟩⟩,
      ⟨.mul, [⟨3, .var 6 + .const 3⟩, ⟨2, .var 5 + .var 2⟩], ⟨3, .var 6 + .const 4⟩⟩]
  refine (writes_machineScalarBlock_readBlock hS (xs := ys)
    (z := (t.1, t.2 + 3)) (n := 2)
    (v := fun i => if i = 0 then quotient else M.mul quotient U) ?_
    (by room)).readBlocks_singleton
  simp [ys, ScalarIns.evalBlock, Operand.evalList, Operand.eval, Env.frame, IExp.eval,
    Store.cellFn, Machine.eval, hR₂, hU₂, hlevel₂, hUt, List.range_succ, quotient,
    Nat.add_assoc]

end NLAlib.SpectralBisection
