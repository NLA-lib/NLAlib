/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import NLAlib.Ops.Catalog.Operator

/-!
# Catalog: the three operations of iterative refinement

One step of iterative refinement for a fixed square matrix $\mathbf{A}$ calls three vector
operations, each with its own accuracy, so that each can run in its own precision
[CarsonHigham2018]:

* `NLAlib.Ops.RefinementOp.residual [n] [b, x] [r]`: the residual
  $\mathbf{b} - \mathbf{A}\mathbf{x}$, in the residual precision;
* `NLAlib.Ops.RefinementOp.solve [n] [r] [d]`: the correction $\mathbf{A}^{-1}\mathbf{r}$, from
  factors computed in the factorization precision;
* `NLAlib.Ops.RefinementOp.update [n] [d, x] [x]`: the update $\mathbf{x} + \mathbf{d}$ in
  place, in the working precision.

The contracts are normwise, in the Euclidean norm of the decoded blocks. They say nothing about
how an operation is computed: an implementation in scalar arithmetic at a precision tag
(`NLAlib.Ops.Tagged`) is linked below these operations, and its accuracy theorem supplies the
parameter of the contract.

## Main results

* `NLAlib.Ops.IsRefinement`: the three operations satisfy their contracts.
* `NLAlib.Ops.exists_isRefinement`: the contracts can be satisfied together, by exact
  arithmetic.
-/

@[expose] public section

namespace NLAlib.Ops

open scoped Matrix

/-- The vector operations of one step of iterative refinement. -/
inductive RefinementOp where
  /-- `residual [n] [b, x] [r]` writes the residual of `x` for the right-hand side `b`. -/
  | residual
  /-- `solve [n] [r] [d]` writes the correction for the residual `r`. -/
  | solve
  /-- `update [n] [d, x] [x]` adds the correction `d` to the iterate `x` in place. -/
  | update
  deriving DecidableEq

variable {K Op Tst : Type} [Inhabited K]

/-- The dimension is the order of the matrix and the output is in another buffer than every
input. -/
@[admNF] def RefinementOperands (n : ℕ) : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun d ins outs => d = [n] ∧ ∀ x ∈ ins, ∀ y ∈ outs, x.1 ≠ y.1

/-- The output is the last input, and the other inputs are in other buffers. The admission
does not depend on the matrix: the update is the same operation at every order. -/
@[admNF] def RefinementUpdateOperands : List ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop :=
  fun _ ins outs => outs = ins.getLast?.toList ∧
    ∀ a ∈ ins.dropLast, ∀ z ∈ outs, a.1 ≠ z.1

/-- The computed residual $\mathbf{r}$ of $\mathbf{x}$ has error at most
$\zeta\|\mathbf{b} - \mathbf{A}\mathbf{x}\| + \eta(\|\mathbf{b}\| + \alpha\|\mathbf{x}\|)$ in
the Euclidean norm. The allowance $\alpha$ is a norm of the matrix chosen by the mathematical
application. -/
@[simps (attr := storeNF)]
def residualRel (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ζ η α : ℝ) :
    BlockRel K where
  nd := 1
  inLens d := [d.headD 0, d.headD 0]
  outLens d := [d.headD 0]
  rel _ X _ Y := match X, Y with
    | [bs, xs], [rs] =>
        ‖WithLp.toLp 2 (decv dec n bs - A *ᵥ decv dec n xs - decv dec n rs)‖ ≤
          ζ * ‖WithLp.toLp 2 (decv dec n bs - A *ᵥ decv dec n xs)‖ +
            η * (‖WithLp.toLp 2 (decv dec n bs)‖ + α * ‖WithLp.toLp 2 (decv dec n xs)‖)
    | _, _ => False

/-- The computed correction $\mathbf{d}$ for the residual $\mathbf{r}$ has error at most
$\theta\|\mathbf{A}^{-1}\mathbf{r}\|$ in the Euclidean norm. -/
@[simps (attr := storeNF)]
noncomputable def solveRel (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ) :
    BlockRel K where
  nd := 1
  inLens d := [d.headD 0]
  outLens d := [d.headD 0]
  rel _ X _ Y := match X, Y with
    | [rs], [ds] =>
        ‖WithLp.toLp 2 (A⁻¹ *ᵥ decv dec n rs - decv dec n ds)‖ ≤
          θ * ‖WithLp.toLp 2 (A⁻¹ *ᵥ decv dec n rs)‖
    | _, _ => False

/-- The updated iterate $\mathbf{x}'$ has error at most $\varepsilon\|\mathbf{x} + \mathbf{d}\|$
in the Euclidean norm, at the length given by the dimension of the call. -/
@[simps (attr := storeNF)]
def updateRel (dec : K → ℝ) (ε : ℝ) : BlockRel K where
  nd := 1
  inLens d := [d.headD 0, d.headD 0]
  outLens d := [d.headD 0]
  rel d X _ Y := match X, Y with
    | [ds, xs], [xs'] =>
        ‖WithLp.toLp 2 (decv dec (d.headD 0) xs + decv dec (d.headD 0) ds -
            decv dec (d.headD 0) xs')‖ ≤
          ε * ‖WithLp.toLp 2 (decv dec (d.headD 0) xs + decv dec (d.headD 0) ds)‖
    | _, _ => False

/-- **The three operations of iterative refinement satisfy their contracts** for the matrix
$\mathbf{A}$: the residual with accuracies $\zeta$, $\eta$ and matrix-norm allowance $\alpha$,
the correction with relative accuracy $\theta$, the update with relative accuracy
$\varepsilon$. -/
structure IsRefinement [Has RefinementOp Op] (dec : K → ℝ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (θ η ζ ε α : ℝ) (I : Interp Op Tst K) : Prop where
  /-- The residual operation satisfies its contract. -/
  residual : I.Satisfies .total (Has.inj RefinementOp.residual)
    ((residualRel dec A ζ η α).spec (RefinementOperands n))
  /-- The correction solve satisfies its contract. -/
  solve : I.Satisfies .total (Has.inj RefinementOp.solve)
    ((solveRel dec A θ).spec (RefinementOperands n))
  /-- The update satisfies its contract. -/
  update : I.Satisfies .total (Has.inj RefinementOp.update)
    ((updateRel dec ε).spec RefinementUpdateOperands)

/-! ### Witness -/

/-- The block functions of exact refinement over the real numbers. -/
noncomputable def exactRefinementFn {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    RefinementOp → BlockFn ℝ
  | .residual => .of2 1 (·.headD 0) (·.headD 0) (·.headD 0) fun d bs xs =>
      if d = [n] then some (List.ofFn (decv id n bs - A *ᵥ decv id n xs)) else none
  | .solve => .of1 1 (·.headD 0) (·.headD 0) fun d rs =>
      if d = [n] then some (List.ofFn (A⁻¹ *ᵥ decv id n rs)) else none
  | .update => .of2 1 (·.headD 0) (·.headD 0) (·.headD 0) fun d ds xs =>
      some (List.ofFn (decv id (d.headD 0) xs + decv id (d.headD 0) ds))

/-- Witness: for every matrix and nonnegative parameters the three contracts can be satisfied
together, by exact arithmetic over the real numbers. -/
theorem exists_isRefinement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {θ η ζ ε α : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hε : 0 ≤ ε) (hα : 0 ≤ α) :
    ∃ I : Interp RefinementOp Tst ℝ, IsRefinement id A θ η ζ ε α I := by
  let F := exactRefinementFn A
  refine ⟨Interp.ofFns F, ?_, ?_, ?_⟩
  · refine (Interp.ofFns_isFn (Tst := Tst) F .total .residual AnyOperands).satisfies_rel
      (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
    intro d w X μ ins outs hnd hw hadm hr hdom
    obtain ⟨rfl, -⟩ := hadm
    obtain ⟨_, _, bs, xs, rfl, hbs, hxs, rfl⟩ := Mem.readBlocks_two hr
    refine ⟨[List.ofFn (decv id n bs - A *ᵥ decv id n xs)],
      by simp [F, exactRefinementFn, BlockFn.of2], by simp [residualRel], ?_⟩
    change ‖WithLp.toLp 2 (decv id n bs - A *ᵥ decv id n xs -
      decv id n (List.ofFn (decv id n bs - A *ᵥ decv id n xs)))‖ ≤ _
    rw [decv_ofFn, sub_self, WithLp.toLp_zero, norm_zero]
    positivity
  · refine (Interp.ofFns_isFn (Tst := Tst) F .total .solve AnyOperands).satisfies_rel
      (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
    intro d w X μ ins outs hnd hw hadm hr hdom
    obtain ⟨rfl, -⟩ := hadm
    obtain ⟨_, rs, rfl, hrs, rfl⟩ := Mem.readBlocks_one hr
    refine ⟨[List.ofFn (A⁻¹ *ᵥ decv id n rs)],
      by simp [F, exactRefinementFn, BlockFn.of1], by simp [solveRel], ?_⟩
    change ‖WithLp.toLp 2 (A⁻¹ *ᵥ decv id n rs -
      decv id n (List.ofFn (A⁻¹ *ᵥ decv id n rs)))‖ ≤ _
    rw [decv_ofFn, sub_self, WithLp.toLp_zero, norm_zero]
    positivity
  · refine (Interp.ofFns_isFn (Tst := Tst) F .total .update AnyOperands).satisfies_rel
      (fun _ _ _ _ => trivial) rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
    intro d w X μ ins outs hnd hw hadm hr hdom
    obtain ⟨_, _, ds, xs, rfl, hds, hxs, rfl⟩ := Mem.readBlocks_two hr
    refine ⟨[List.ofFn (decv id (d.headD 0) xs + decv id (d.headD 0) ds)],
      by simp [F, exactRefinementFn, BlockFn.of2], by simp [updateRel], ?_⟩
    change ‖WithLp.toLp 2 (decv id (d.headD 0) xs + decv id (d.headD 0) ds -
      decv id (d.headD 0) (List.ofFn (decv id (d.headD 0) xs + decv id (d.headD 0) ds)))‖ ≤ _
    rw [decv_ofFn, sub_self, WithLp.toLp_zero, norm_zero]
    positivity

end NLAlib.Ops
