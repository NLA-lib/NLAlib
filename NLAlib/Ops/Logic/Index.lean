/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Tactic.Linarith
public meta import Lean.Elab.Tactic.Basic
public import NLAlib.Ops.Logic.Attr

/-!
# Index arithmetic

The facts that a program proof needs about offsets: a row (or column) of a block stored by rows
(or columns) is inside the block, the next row starts where the row ends, quotients and
remainders of a linear offset, positions of the tape after `i` rounds that each read `w` entries.
They are nonlinear in the sizes, so `omega` alone does not prove them; `idx` does, from the
bounds of the loop variables in the context.

## Main results

* `NLAlib.Ops.Idx.mul_add_le_mul`: `i < k → i n + n ≤ k n`, the fact behind every row in bounds.
* `NLAlib.Ops.Idx.add_lt_mul`: `i < m → j < p → i p + j < m p`.
* `NLAlib.Ops.Idx.div_add`, `NLAlib.Ops.Idx.mod_add`: the row and column of a row-major offset.
-/

@[expose] public section

namespace NLAlib.Ops.Idx

/-- A row of length `n` that starts before row `k` ends at or before row `k`. -/
theorem mul_add_le_mul {i k : ℕ} (h : i < k) (n : ℕ) : i * n + n ≤ k * n := by
  have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h)
  rwa [Nat.succ_mul] at this

/-- The same with the size on the left. -/
theorem mul_add_le_mul' {i k : ℕ} (h : i < k) (n : ℕ) : n * i + n ≤ n * k := by
  rw [Nat.mul_comm n i, Nat.mul_comm n k]
  exact mul_add_le_mul h n

/-- An entry of an `m × p` block stored by rows is inside the block. -/
theorem add_lt_mul {i j m p : ℕ} (hi : i < m) (hj : j < p) : i * p + j < m * p := by
  have := mul_add_le_mul hi p
  omega

/-- The row of a row-major offset. -/
@[idxNF] theorem div_add {i j p : ℕ} (hj : j < p) : (i * p + j) / p = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]

/-- The column of a row-major offset. -/
@[idxNF] theorem mod_add {i j p : ℕ} (hj : j < p) : (i * p + j) % p = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- Monotonicity of an offset in its row. -/
theorem mul_le_mul_of_le {i k : ℕ} (h : i ≤ k) (n : ℕ) : i * n ≤ k * n := Nat.mul_le_mul_right n h

/-- Tape positions: `i` rounds that each read `w` entries, from `p`, stay below `k` rounds. -/
theorem pos_add_le {p i k w : ℕ} (h : i < k) : p + i * w + w ≤ p + k * w := by
  have := mul_add_le_mul h w
  omega

end NLAlib.Ops.Idx

namespace NLAlib.Ops

/-- The products `x * y` of natural numbers in an expression, searched to depth `fuel`. -/
meta def Idx.productsAux : ℕ → Lean.Expr → Array (Lean.Expr × Lean.Expr)
  | 0, _ => #[]
  | fuel + 1, e =>
    let rest := e.getAppArgs.foldl (fun acc a => acc ++ Idx.productsAux fuel a) #[]
    match e.getAppFnArgs with
    | (``HMul.hMul, #[ty, _, _, _, x, y]) =>
      if ty.isConstOf ``Nat then rest.push (x, y) else rest
    | _ => rest

/-- The products `x * y` of natural numbers in an expression (to depth 64; goals are far
shallower). -/
meta def Idx.products (e : Lean.Expr) : Array (Lean.Expr × Lean.Expr) :=
  Idx.productsAux 64 e

open Lean Meta Elab Tactic in
/-- **Product generation** for `idx`: for every hypothesis `i < k` or `i ≤ k` on natural numbers
and every product `i * n` or `n * i` in the goal, add `i * n + n ≤ k * n` (resp. `i * n ≤ k * n`)
to the context, so that `omega`, which treats products as atoms, can use the bound. -/
elab "idx_prod" : tactic => withMainContext do
  let goal ← getMainTarget
  let prods := Idx.products (← instantiateMVars goal)
  let lctx ← getLCtx
  let mut facts : Array Expr := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    match ty.getAppFnArgs with
    | (``LT.lt, #[t, _, a, _]) =>
      if t.isConstOf ``Nat then
        for (x, y) in prods do
          if ← isDefEq x a then
            facts := facts.push (← mkAppM ``Idx.mul_add_le_mul #[d.toExpr, y])
          if ← isDefEq y a then
            facts := facts.push (← mkAppM ``Idx.mul_add_le_mul' #[d.toExpr, x])
    | (``LE.le, #[t, _, a, _]) =>
      if t.isConstOf ``Nat then
        for (x, y) in prods do
          if ← isDefEq x a then
            facts := facts.push (← mkAppM ``Nat.mul_le_mul_right #[y, d.toExpr])
          if ← isDefEq y a then
            facts := facts.push (← mkAppM ``Nat.mul_le_mul_left #[x, d.toExpr])
    | _ => pure ()
  let mut g ← getMainGoal
  for f in facts do
    let fty ← inferType f
    let (_, g') ← (← g.assert `hidx fty f).intro1P
    g := g'
  replaceMainGoal [g]

/-- **`idx`**: a goal of linear or nonlinear natural-number arithmetic over offsets: `≤`, `<`,
`=`, `≠` between sums of products of variables and numerals, with `/` and `%` by a size.

Method (phase B): `omega`; then, for every hypothesis `i < k` (or `i ≤ k`) in the context and
every product `i * n` (or `n * i`) in the goal or the context, add `i * n + n ≤ k * n`
(`Idx.mul_add_le_mul`), normalise products to sums of monomials (`ring_nf`, monomials are atoms
for `omega`), rewrite `idxNF` (side conditions by `omega`), and run `omega` again. `nlinarith`
only in `idx!`. It never
leaves a goal: it closes it or fails with the goal. It is the discharger of `store_side`,
`fp_mem` and `disjoint`, so every side condition with an offset goes through it. -/
syntax "idx" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| idx) => `(tactic| idx [])
  | `(tactic| idx [$ts,*]) => `(tactic| first
      | omega
      | (idx_prod; omega)
      | (simp (disch := omega) only [idxNF, $ts,*]; done)
      | (simp (disch := omega) only [idxNF, $ts,*]; omega)
      | fail "idx: the index fact is not proved")

/-- **`idx!`**: `idx`, then `nlinarith` (slow; for the goals that product generation misses). -/
syntax "idx!" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| idx!) => `(tactic| idx! [])
  | `(tactic| idx! [$ts,*]) => `(tactic| first
      | idx [$ts,*]
      | nlinarith
      | fail "idx!: the index fact is not proved")

end NLAlib.Ops

attribute [idxNF] Nat.add_mul Nat.mul_add Nat.one_mul Nat.mul_one
