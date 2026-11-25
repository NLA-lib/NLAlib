/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Cholesky.RightColumn
public import NLAlib.Ops.Blas.Guarded

/-!
# The Cholesky column under rejecting arithmetic

The existing column tree succeeds when its exact root and quotient targets are accepted.
Its output is the same actual machine-word list as under the total scalar interpretation.
The precondition is local primitive safety; the full finite-range factorization derives it
from its original input conditions and numerical residual invariant.

## Main results

* `NLAlib.Cholesky.rightColumn_meets_guarded`: actual column success and words.
-/

@[expose] public section

namespace NLAlib.Cholesky

open Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Inhabited K]

/-- Root and division targets required by the actual rejecting scalar column. -/
def rightColumnGuardedSpec (M : Machine K) (dec : K → ℝ) (safe : ℝ → Prop) : Routine.Spec K :=
  spec% [n] ([p], xs) → (ys) requires
    (0 ≤ dec p ∧ safe (Real.sqrt (dec p)) ∧ dec (M.sqrt p) ≠ 0 ∧
      ∀ i < n, safe (dec (vec xs i) / dec (M.sqrt p))) ensures
    ys = M.sqrt p :: scalF M (M.sqrt p) (vec xs) n

/-- The actual root, copies, and normalization succeed under their guarded contracts.
No total-machine success law is used for division or square root. -/
theorem rightColumn_meets_guarded {M : Machine K} {dec : K → ℝ} {safe : ℝ → Prop}
    {I : Interp Op Tst K} (hI : IsGuardedScalar M dec safe I) :
    (rightColumn (Op := Op) (Tst := Tst)).Meets I (rightColumnGuardedSpec M dec safe) := by
  classical
  routine_intro [n] (p, x, y) reads (ps, xs)
  obtain ⟨v, hv, rfl⟩ := Store.readBlock_one_eq_some.mp hps
  obtain ⟨hnonneg, hsafe, hnz, hquot⟩ := hpre
  obtain ⟨hlp, hlx, hly⟩ := hl
  change Writes .total I τ _ (Env.frame [n] [p, x, y]) (Fp.blocks [y] [n + 1]) _ m
  alloc as t
  have hty : t ≠ y.1 := by change m.store.length ≠ y.1; exact Nat.ne_of_gt hly
  step (hI .sqrt) [Machine.guardedFn, hnonneg, hsafe] as m₁ hfr₁ ⟨hpos₁, r, hr, he⟩
  change ((if 0 ≤ dec v ∧ safe (Real.sqrt (dec v)) then some (M.sqrt v) else none).map
    (fun w => [[w]])) = some [[r]] at he
  have hg : 0 ≤ dec v ∧ safe (Real.sqrt (dec v)) := ⟨hnonneg, hsafe⟩
  rw [if_pos hg] at he
  simp only [Option.map_some, Option.some.injEq,
    List.cons.injEq, and_true] at he
  subst r
  change m₁.pos = m.pos + 0 at hpos₁
  call (copyLoopRoutine_meets_guarded hI) [n] (x, (y.1, y.2 + 1))
    as m₂ hfr₂ hpos₂ (copied) hcopied
  have hec : copied = xs := (List.cons.inj hcopied).1
  subst copied
  call (scalLoopRoutine_meets_guarded hI) [n] ((t, 0), (y.1, y.2 + 1))
    (pre := ⟨hnz, hquot⟩) as m₃ hfr₃ hpos₃ (scaled) hscaled
  case' hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true]
    change m.store.length < m₂.store.length ∧ y.1 < m₂.store.length
    simp only [List.length_singleton] at hlen_t
    omega
  have hcopy : I.IsFn .total (Has.inj ScalarOp.copy) (.un fun w => some w) AnyOperands :=
    hI .copy
  step hcopy as m₄ hfr₄ ⟨hpos₄, root, hroot, rfl⟩
  have htail : m₄.store.readBlock y.1 (y.2 + 1) n = some scaled := by keep
  intro s₂ hs₂ hB₂
  refine ⟨?_, [M.sqrt v :: scaled], Mem.readBlocks_of_cons ?_ rfl, ?_⟩
  · change m₄.pos = m.pos + 0
    omega
  · have hd := Store.Below.get_of hB₂ hly hroot
    have ht := Store.Below.readBlock_of hB₂ hly htail
    simp only [Store.readBlock_succ, hd, ht, Option.bind_some, Option.map_some]
  · change M.sqrt v :: scaled = M.sqrt v :: scalF M (M.sqrt v) (vec xs) n
    exact congrArg (List.cons _) hscaled

end NLAlib.Cholesky
