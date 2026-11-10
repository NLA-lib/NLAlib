/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Tactic.Linarith
public import NLAlib.Ops.Logic.Attr

/-!
# Index arithmetic

The facts that a program proof needs about offsets: a row (or column) of a block stored by rows
(or columns) is inside the block, the next row starts where the row ends, quotients and
remainders of a linear offset, positions of the tape after `i` rounds that each read `w` entries.
They are nonlinear in the sizes, so `omega` alone does not prove them; `idx` does, from the
bounds of the loop variables in the context.

**Phase A**: statements only (`sorry`); `idx` is declared with its goal shape and a provisional
implementation.

## Main results

* `NLAlib.Ops.Idx.mul_add_le_mul`: `i < k → i n + n ≤ k n`, the fact behind every row in bounds.
* `NLAlib.Ops.Idx.add_lt_mul`: `i < m → j < p → i p + j < m p`.
* `NLAlib.Ops.Idx.div_add`, `NLAlib.Ops.Idx.mod_add`: the row and column of a row-major offset.
-/

@[expose] public section

namespace NLAlib.Ops.Idx

/-- A row of length `n` that starts before row `k` ends at or before row `k`. -/
theorem mul_add_le_mul {i k : ℕ} (h : i < k) (n : ℕ) : i * n + n ≤ k * n := by sorry

/-- The same with the size on the left. -/
theorem mul_add_le_mul' {i k : ℕ} (h : i < k) (n : ℕ) : n * i + n ≤ n * k := by sorry

/-- An entry of an `m × p` block stored by rows is inside the block. -/
theorem add_lt_mul {i j m p : ℕ} (hi : i < m) (hj : j < p) : i * p + j < m * p := by sorry

/-- The row of a row-major offset. -/
@[idxNF] theorem div_add {i j p : ℕ} (hj : j < p) : (i * p + j) / p = i := by sorry

/-- The column of a row-major offset. -/
@[idxNF] theorem mod_add {i j p : ℕ} (hj : j < p) : (i * p + j) % p = j := by sorry

/-- Monotonicity of an offset in its row. -/
theorem mul_le_mul_of_le {i k : ℕ} (h : i ≤ k) (n : ℕ) : i * n ≤ k * n := Nat.mul_le_mul_right n h

/-- Tape positions: `i` rounds that each read `w` entries, from `p`, stay below `k` rounds. -/
theorem pos_add_le {p i k w : ℕ} (h : i < k) : p + i * w + w ≤ p + k * w := by sorry

end NLAlib.Ops.Idx

namespace NLAlib.Ops

/-- **`idx`**: a goal of linear or nonlinear natural-number arithmetic over offsets: `≤`, `<`,
`=`, `≠` between sums of products of variables and numerals, with `/` and `%` by a size.

Method (phase B): `omega`; then, for every hypothesis `i < k` (or `i ≤ k`) in the context and
every product `i * n` (or `n * i`) in the goal or the context, add `i * n + n ≤ k * n`
(`Idx.mul_add_le_mul`), normalise products to sums of monomials (`ring_nf`, monomials are atoms
for `omega`), rewrite `idxNF`, and run `omega` again; `nlinarith` as the last resort. It never
leaves a goal: it closes it or fails with the goal. It is the discharger of `store_side`,
`fp_mem` and `disjoint`, so every side condition with an offset goes through it. -/
syntax "idx" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| idx) => `(tactic| idx [])
  | `(tactic| idx [$ts,*]) => `(tactic| first
      | omega
      | (simp only [idxNF, $ts,*]; done)
      | (simp only [idxNF, $ts,*]; omega)
      | nlinarith
      | fail "idx: the index fact is not proved")

end NLAlib.Ops
