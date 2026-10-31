/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Tactic.Abel

/-!
# Powers after subtracting a fixed idempotent

Upstream candidate for Mathlib's `Algebra/Ring/Idempotent.lean`. Subtracting an
idempotent fixed by multiplication on either side commutes with positive powers.

## Main results

* `IsIdempotentElem.sub_pow_succ`: the positive-power subtraction identity in any ring.
-/

@[expose] public section

namespace IsIdempotentElem

/-- If an idempotent $p$ satisfies $ap=pa=p$, then
$$(a-p)^{k+1}=a^{k+1}-p\,.$$
This algebraic identity transfers power convergence to convergence to an idempotent.
Adapted from `tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`,
`matrix_sub_projector_pow_succ`, generalized from matrices to any ring. -/
theorem sub_pow_succ {R : Type*} [Ring R] {p : R} (hp : IsIdempotentElem p)
    {a : R} (hap : a * p = p) (hpa : p * a = p) (k : ℕ) :
    (a - p) ^ (k + 1) = a ^ (k + 1) - p := by
  have hpow (j : ℕ) : a ^ j * p = p := by
    induction j with
    | zero => rw [pow_zero, one_mul]
    | succ j ih => rw [pow_succ, mul_assoc, hap, ih]
  induction k with
  | zero => simp only [zero_add, pow_one]
  | succ k ih =>
    rw [pow_succ, ih, sub_mul, mul_sub, mul_sub, hpow, hpa, hp.eq, ← pow_succ]
    abel

end IsIdempotentElem
