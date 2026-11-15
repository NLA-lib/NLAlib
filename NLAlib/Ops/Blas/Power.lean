/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.Logic.Loop
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Static

/-!
# Scalar powers by sequential multiplication

A literal one initializes the output, followed by the requested number of multiplications by
the unchanged input word. The word theorem holds for any scalar machine. Exact arithmetic
identifies the output with the ordinary natural power. Input and output are separated scalar
views, including views of one arena.

## Main results

* `NLAlib.Ops.scalarPower`: the computable scalar implementation.
* `NLAlib.Ops.writes_scalarPower`: its actual word-level result.
* `NLAlib.Ops.writes_scalarPower_exact`: its exact arithmetic specialization.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Initialize one output word to the machine literal one and multiply it by `X` `n` times. -/
def scalarPower : Impl Op Tst := opsImpl% [n] (X) → (Z) {
  call (Has.inj (ScalarOp.lit 1)) [] () → (Z);
  for i < n { call (Has.inj ScalarOp.mul) [] (Z, X) → (Z) }
}

/-- The scalar syntax performs one literal call and exactly `n` multiplication calls. -/
theorem stmtCost_scalarPower (n x z : ℕ) :
    stmtCost (scalarPower (Op := Op) (Tst := Tst)).body [n, x, z] =
      Count.one (Has.inj (ScalarOp.lit 1)) [] + n • Count.one (Has.inj ScalarOp.mul) [] := by
  simp [scalarPower, stmtCost, useCost]

/-- Sequential multiplication returns its actual machine word, preserving the input through
spatial separation. The output word need not be initialized and zero exponents are admitted. -/
theorem writes_scalarPower {M : Machine K} {I : Interp Op Tst K} (hS : IsScalar M I)
    {τ : Tape K} {m : Mem K} {n : ℕ} {x z : ℕ × ℕ} {v : K}
    (hx : m.store.get x.1 x.2 = some v) (hz : z.2 < m.store.len z.1)
    (hsep : Fp.Disj (Store.inBlock x.1 x.2 1) (Store.inBlock z.1 z.2 1)) :
    Writes .total I τ scalarPower.body (Env.frame [n] [x, z]) (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get z.1 z.2 = some ((fun y => M.mul y v)^[n] (M.lit 1))) m := by
  have hxl := Store.lt_length_of_get hx
  have hzl := Store.lt_length_of_lt_len hz
  unfold scalarPower
  refine (writes_call_const (hS (.lit 1)) rfl trivial hz).seq_le le_rfl ?_
  intro m₁ hfr₁ ⟨hp₁, hOne⟩
  have hx₁ := hfr₁.keep (Store.readsOnly_get _ _ _) hsep.symm hx
  refine (writes_loop (N := n) rfl (fun _ => Store.inBlock z.1 z.2 1)
    (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m₁.pos ∧
      m'.store.get z.1 z.2 = some ((fun y => M.mul y v)^[i] (M.lit 1)))
    (And.intro rfl hOne) ?_).mono le_rfl ?_
  · intro i _ m' hfr ⟨hp, hAcc⟩
    have hx' := hfr.keep (Store.readsOnly_get _ _ _) hsep.symm hx₁
    refine (writes_call_bin (hS .mul) rfl rfl trivial hAcc hx' rfl
      (fun _ => ⟨by room, by room⟩)).mono le_rfl ?_
    intro m'' _ ⟨hp', hMul⟩
    exact ⟨hp'.trans hp, by simpa only [Function.iterate_succ_apply'] using hMul⟩
  · intro m' _ h
    exact ⟨h.1.trans hp₁, h.2⟩

/-- Under the exact real arithmetic model the actual sequential power equals the mathematical
natural power, with no sign or nonzero assumption on its base. -/
theorem writes_scalarPower_exact {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M)
    {τ : Tape ℝ} {m : Mem ℝ} {n : ℕ} {x z : ℕ × ℕ} {v : ℝ}
    (hx : m.store.get x.1 x.2 = some v) (hz : z.2 < m.store.len z.1)
    (hsep : Fp.Disj (Store.inBlock x.1 x.2 1) (Store.inBlock z.1 z.2 1)) :
    Writes .total I τ scalarPower.body (Env.frame [n] [x, z]) (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get z.1 z.2 = some (v ^ n)) m := by
  have he : (fun y => M.mul y v)^[n] (M.lit 1) = v ^ n := by
    have hmul (a b : ℝ) : M.mul a b = a * b := hE.mul a b
    induction n with
    | zero => simpa using hE.lit 1
    | succ n ih => rw [Function.iterate_succ_apply', ih, hmul, pow_succ]
  exact (writes_scalarPower hS hx hz hsep).mono le_rfl (fun _ _ h => ⟨h.1, he ▸ h.2⟩)

end NLAlib.Ops
