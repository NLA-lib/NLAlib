/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LinearSystems.Refinement.Model
public import NLAlib.LinearSystems.Refinement.Solve
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Ops.OperationCount

/-!
# Certified iterative refinement

The admitted inputs (`inputs`) are the invertible matrices whose contraction factor is less than
one, with any right-hand side and any start; the problem is derived from the routine
(`NLAlib.Ops.Routine.Domain`). The matrix is the declared unstored input, reached only through
the residual and the correction solve. The accuracies $\theta$ (correction), $\eta$, $\zeta$
(residual) and $\varepsilon$ (update) are parameters of the model: in refinement in three
precisions [CarsonHigham2018] they are given by the unit roundoffs of the factorization, of the
residual and of the working precision.

With unit weights (each of the three operations counts one) the work is a closed form computed
by the kernel from the tree. That count is in calls of the three vector operations, not in
scalar operations: the model has those as primitives.

## Main results

* `NLAlib.LinearSystems.Refinement.Certification.algorithm`: the certificate, with work at most
  `25 k + 15`.
* `NLAlib.LinearSystems.Refinement.Certification.oracles`: the residual and the correction solve are
  the oracles for the matrix.
* `NLAlib.LinearSystems.Refinement.Certification.algorithm_checked`: what it states, on the
  execution rules, with the forward error of the stored iterate.
-/

@[expose] public section

namespace NLAlib.LinearSystems.Refinement.Certification

open Ops
open scoped Matrix

variable (θ η ζ ε : ℝ) (domain : (Fin 2 → ℕ) → Prop) (admitted : ∃ d, domain d)

/-- The admitted systems: the matrix is invertible and the contraction factor of one step is
less than one. -/
def accepts (d : Fin 2 → ℕ)
    (x : Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ) × (Fin (d 0) → ℝ)) : Prop :=
  IsUnit x.1 ∧ refinementContractionFactor (pseudoConditionNumber x.1) θ η ζ ε < 1

variable (supply : ∀ d, domain d →
  ∃ x : Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ) × (Fin (d 0) → ℝ),
    accepts θ η ζ ε d x)

/-- The admitted inputs of iterative refinement: at the sizes of `domain`, every invertible
matrix whose contraction factor is less than one, with every right-hand side and every start.
The right-hand side is held by the first operand and the start by the second, which the run
updates in place; the residual and the correction are blank. The matrix is the declared unstored
input: it is in no buffer and is reached only through the residual and the correction solve
(`NLAlib.LinearSystems.Refinement.Certification.oracles`). -/
noncomputable def inputs : (solve (Op := RefinementOp) (Tst := Empty)).Domain ℝ 2 4 where
  valid := domain
  In d := Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ) × (Fin (d 0) → ℝ)
  accepts := accepts θ η ζ ε
  slot d := ![.stored (Codec.vector (d 0)) fun x => x.2.1,
    .stored (Codec.vector (d 0)) fun x => x.2.2, .blank (d 0), .blank (d 0)]
  fits := by domain_fits
  Unstored d := Matrix (Fin (d 0)) (Fin (d 0)) ℝ
  unstored _ x := x.1
  faithful d x y hu h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq]
      at h0 h1
    exact Prod.ext hu (Prod.ext ((Codec.vector (d 0)).encode_injective h0)
      ((Codec.vector (d 0)).encode_injective h1))
  admitted := admitted
  inhabited := supply

/-- The right-hand side, the start and two blank vectors: the problem of iterative
refinement. -/
noncomputable abbrev problem : Problem ℝ 2 4 := (inputs θ η ζ ε domain admitted supply).problem

/-- One fixed tree: the routine closed on the four buffers of the problem. -/
def program : Program RefinementOp Empty 2 4 := solve.close 2 4

variable (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hε : 0 ≤ ε)

/-- The weights under which each of the three operations counts one and uses no workspace. -/
noncomputable abbrev unitResources : ResourceModel RefinementOp Empty :=
  Model.resources (fun _ _ => 1) (fun _ _ => 0)

/-- The model of iterative refinement at the matrix of the input, with unit weights. -/
noncomputable abbrev model :
    AccessModel RefinementOp Empty (problem θ η ζ ε domain admitted supply) :=
  Model.model (problem θ η ζ ε domain admitted supply) (fun d => d 0) (fun _ X => X.val.1.1)
    hθ hη hζ hε unitResources

/-- The number of instructions at $k$ steps, at most; it does not depend on the order. -/
def operationCount (d : Fin 2 → ℕ) : ℕ := 25 * d 1 + 15

/-- The instruction polynomial of the program, evaluated by the kernel. -/
theorem countPoly_program : program.countPoly = [(15, []), (25, [1])] := by
  rfl

/-- The polynomial of the program at the sizes `d` is the operation count. -/
theorem eval_countPoly_program (d : Fin 2 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = operationCount d := by
  rw [countPoly_program]
  poly_eval [operationCount]

/-- Iterative refinement succeeds on every admitted system, within `25 k + 15` instructions of
the model with unit weights, and the stored iterate is the last iterate of a refinement run of
$k$ steps from the start. No success or numerical execution witness is an assumption. -/
noncomputable def algorithm :
    Algorithm (model θ η ζ ε domain admitted supply hθ hη hζ hε)
      ((solve (Op := RefinementOp) (Tst := Empty)).specification
        (P := problem θ η ζ ε domain admitted supply)
        (fun _ X => solveSpec id X.val.1.1 θ η ζ ε)
        (model θ η ζ ε domain admitted supply hθ hη hζ hε).resources
        (fun d X => (inputs θ η ζ ε domain admitted supply).blocks d X.val.1)
        (inputs θ η ζ ε domain admitted supply).bytes operationCount) :=
  (inputs θ η ζ ε domain admitted supply).certify (fun _ x => solveSpec id x.1 θ η ζ ε)
    operationCount
    (fun _ _ X _ hI => solve_meets (Model.laws hI) X.property.1.1 hθ hη hζ hε)
    (fun _ _ _ _ _ => rfl)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun q => nomatch q)
    (fun d _ => (eval_countPoly_program d).le)

/-- The oracles of the model. The matrix is the unstored input: it is in no buffer and is
reached only through the residual and the correction solve. The update has one contract at
every size and input, and the contracts of the residual and of the correction solve depend on
the input only through the matrix. The cost of the certificate is counted in calls of them. -/
noncomputable def oracles :
    (inputs θ η ζ ε domain admitted supply).Oracles
      (model θ η ζ ε domain admitted supply hθ hη hζ hε) where
  ops := [.residual, .solve]
  operation o ho d x d' x' := by
    cases o with
    | residual => exact absurd (by simp) ho
    | solve => exact absurd (by simp) ho
    | update => rfl
  query _ _ _ _ q := nomatch q
  through o _ d X Y h := by
    cases o with
    | residual =>
      change (residualRel id X.val.1.1 ζ η (specNorm X.val.1.1)).spec _ =
        (residualRel id Y.val.1.1 ζ η (specNorm Y.val.1.1)).spec _
      rw [show X.val.1.1 = Y.val.1.1 from h]
    | solve =>
      change (solveRel id X.val.1.1 θ).spec _ = (solveRel id Y.val.1.1 θ).spec _
      rw [show X.val.1.1 = Y.val.1.1 from h]
    | update => rfl

/-- **Forward error of certified iterative refinement.** What the certificate states, with no
reference to routines or contracts. For every invertible $\mathbf{A}$ of order $n$ whose
contraction factor $\varphi$ is less than one, every right-hand side $\mathbf{b}$ and start
$\mathbf{x}_0$, every interpretation of the residual, the correction solve and the update
within their accuracies $\eta$, $\zeta$, $\theta$, $\varepsilon$ for $\mathbf{A}$, and every
tape, the counted run of the fixed program from $\mathbf{b}$, $\mathbf{x}_0$ and two blank
vectors succeeds, executes at most $25 k + 15$ instructions (each of the three operations
counting one), keeps its resident memory within the payload of the four vectors plus the static
scratch of the tree, and the second vector then holds an iterate $\hat{\mathbf{x}}$ with, for
every solution $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$$\|\mathbf{x}_\star - \hat{\mathbf{x}}\| \le \varphi^k\|\mathbf{x}_\star - \mathbf{x}_0\| +
\frac{\xi}{1 - \varphi}\,\|\mathbf{x}_\star\|\,.$$
Here, with $\kappa = \kappa(\mathbf{A})$, the contraction factor is
the following, <!-- value refinementContractionFactor \kappa \theta \eta \zeta \varepsilon -->
$\varphi = (1+\varepsilon)(\theta+(1+\theta)\kappa(\zeta+\eta))$, and the accuracy bound is
the following, <!-- value refinementAccuracyBound \kappa \theta \eta \varepsilon -->
$\xi = (1+\varepsilon)(1+\theta)2\kappa\eta+\varepsilon$.
[CarsonHigham2018, Corollary 3.3]; stated there for three unit roundoffs in the $\infty$-norm,
here for the accuracies of the three operations in the Euclidean norm.

Note: the matrix is in no buffer. It is reached only through the residual and the correction
solve, and the work is counted in calls of them
(`NLAlib.LinearSystems.Refinement.Certification.oracles`); a reader must check that the two
contracts are the intended ones. The run behind the bound is `NLAlib.RefinementRun`. -/
theorem algorithm_checked (d : Fin 2 → ℕ) (hd : domain d)
    (A : Matrix (Fin (d 0)) (Fin (d 0)) ℝ) (rhs x₀ : Fin (d 0) → ℝ) (hA : IsUnit A)
    (hφ : refinementContractionFactor (pseudoConditionNumber A) θ η ζ ε < 1)
    (I : Interp RefinementOp Empty ℝ)
    (hI : (model θ η ζ ε domain admitted supply hθ hη hζ hε).contracts d
      ((inputs θ η ζ ε domain admitted supply).input d (A, rhs, x₀) ⟨hA, hφ⟩) I)
    (τ : Tape ℝ) :
    ∃ st, Reference.Execution program I
        (model θ η ζ ε domain admitted supply hθ hη hζ hε).resources
        (inputs θ η ζ ε domain admitted supply).formats τ d
        ((inputs θ η ζ ε domain admitted supply).memory d (A, rhs, x₀)) st ∧
      (model θ η ζ ε domain admitted supply hθ hη hζ hε).resources.work st.cost ≤
        25 * d 1 + 15 ∧
      (inputs θ η ζ ε domain admitted supply).bytes d + st.peak ≤
        (inputs θ η ζ ε domain admitted supply).bytes d +
          staticPeak (model θ η ζ ε domain admitted supply hθ hη hζ hε).resources program d ∧
      ∃ x : Fin (d 0) → ℝ, st.mem.Holds (Codec.vector (d 0)) 1 x ∧
        ∀ xstar : Fin (d 0) → ℝ, A *ᵥ xstar = rhs →
          ‖WithLp.toLp 2 (xstar - x)‖ ≤
            refinementContractionFactor (pseudoConditionNumber A) θ η ζ ε ^ d 1 *
                ‖WithLp.toLp 2 (xstar - x₀)‖ +
              refinementAccuracyBound (pseudoConditionNumber A) θ η ε /
                (1 - refinementContractionFactor (pseudoConditionNumber A) θ η ζ ε) *
                ‖WithLp.toLp 2 xstar‖ := by
  obtain ⟨st, hr, hw, hm, ys, hys, hpost⟩ :=
    (inputs θ η ζ ε domain admitted supply).checked_post
      (Sp := fun _ x => solveSpec id x.1 θ η ζ ε) (work := operationCount)
      (algorithm θ η ζ ε domain admitted supply hθ hη hζ hε) d hd (A, rhs, x₀) ⟨hA, hφ⟩ I hI τ
  refine ⟨st, hr, hw, hm, ?_⟩
  read_outputs hys as (xs')
  obtain ⟨R, h0, hk⟩ : ∃ R : RefinementRun A (decv id (d 0) (List.ofFn rhs)) θ η ζ ε (d 1),
      R.x 0 = decv id (d 0) (List.ofFn x₀) ∧ R.x (d 1) = decv id (d 0) xs' := hpost
  refine ⟨decv id (d 0) xs', Mem.holds_decode _ hxs', fun xstar hstar => ?_⟩
  have h := R.norm_sub_x_le (hstar.trans (decv_ofFn rhs).symm) hφ le_rfl
  rw [h0, hk, decv_ofFn] at h
  exact h

end NLAlib.LinearSystems.Refinement.Certification
