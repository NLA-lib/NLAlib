/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LinearSystems.Refinement.Rounded.Solve
public import NLAlib.Ops.OperationCount
public import NLAlib.Ops.Profiles.Confined
public import NLAlib.Ops.RoutineProblem

/-!
# Certified iterative refinement in three precisions

The certificate of the whole program `NLAlib.LinearSystems.Refinement.Rounded.solve`. The matrix,
the right-hand side and the start are stored in the three supplied buffers, and every operation
of the tree is a scalar operation at one of three precision tags or a cast between two of them.
The model has no oracle: it is uniform and confined, and each operation counts one.

The result is **normwise in the 2-norm**, and the three machines are in the **standard model**
of arithmetic: every operation has a relative error at most its unit roundoff, on all operands,
so overflow and underflow are not modelled.

## Main definitions

* `NLAlib.LinearSystems.Refinement.Rounded.Certification.valid`: the admitted sizes.
* `NLAlib.LinearSystems.Refinement.Rounded.Certification.accepts`: the admitted systems.
* `NLAlib.LinearSystems.Refinement.Rounded.Certification.inputs`: the problem data.
* `NLAlib.LinearSystems.Refinement.Rounded.Certification.model`: the operation model.
* `NLAlib.LinearSystems.Refinement.Rounded.Certification.program`: the fixed program.
* `NLAlib.LinearSystems.Refinement.Rounded.Certification.algorithm`: the certificate.

## Main results

* `NLAlib.LinearSystems.Refinement.Rounded.Certification.accepts_one`: at each admitted size the
  identity is an admitted matrix.
* `NLAlib.LinearSystems.Refinement.Rounded.Certification.algorithm_checked`: what the certificate
  states, on the execution rules.
-/

@[expose] public section

namespace NLAlib.LinearSystems.Refinement.Rounded.Certification

open Ops Computation
open scoped Matrix

/-- **The admitted sizes** $[n, k]$, for unit roundoffs $u_f$, $u$, $u_r$: $(n + 1) u_r < 1$,
and either $n = 0$ or the conditions on the matrix hold at condition number one, that is,
$24(n + 1)^2(u_f + u_f) \le 1$ and the contraction factor at $\kappa = 1$ is less than one.
Every positive definite matrix of order $n \ge 1$ has $\kappa \ge 1$. -/
def valid (uf u ur : ℝ) (d : Fin 2 → ℕ) : Prop :=
  ((d 0 : ℝ) + 1) * ur < 1 ∧ (d 0 = 0 ∨
    (24 * ((d 0 : ℝ) + 1) ^ 2 * (uf + uf) ≤ 1 ∧
      refinementContractionFactor 1 (24 * ((d 0 : ℝ) + 1) ^ 2 * (uf + uf))
        ((1 + u) * (((d 0 : ℝ) + 1) * roundingFactor (d 0 + 1) ur)) u u < 1))

/-- **The admitted systems** at size $[n, k]$: $\mathbf{A}$ is positive definite (so symmetric),
$24(n + 1)^2(u_f + u_f)\kappa(\mathbf{A}) \le 1$, and the contraction factor of one refinement
step, at $\theta = 24(n + 1)^2(u_f + u_f)\kappa(\mathbf{A})$,
$\eta = (1 + u)(n + 1)\gamma_{n+1}(u_r)$ and $\zeta = \varepsilon = u$, is less than one. Every
right-hand side and start are admitted. -/
def accepts (uf u ur : ℝ) (d : Fin 2 → ℕ)
    (x : Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ) × (Fin (d 0) → ℝ)) : Prop :=
  x.1.PosDef ∧ 24 * ((d 0 : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber x.1 ≤ 1 ∧
    refinementContractionFactor (pseudoConditionNumber x.1)
      (24 * ((d 0 : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber x.1)
      ((1 + u) * (((d 0 : ℝ) + 1) * roundingFactor (d 0 + 1) ur)) u u < 1

/-- The condition number of the identity of order $n$ is one, and zero for the empty matrix. -/
theorem pseudoConditionNumber_one_eq (n : ℕ) :
    pseudoConditionNumber (1 : Matrix (Fin n) (Fin n) ℝ) = if n = 0 then 0 else 1 := by
  rw [pseudoConditionNumber_of_isUnit isUnit_one, inv_one]
  split_ifs with h
  · subst h
    have h0 : (1 : Matrix (Fin 0) (Fin 0) ℝ) = 0 := by
      ext i
      exact i.elim0
    rw [h0, specNorm_zero, zero_mul]
  · have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩
    rw [specNorm_one, one_mul]

/-- The identity is admitted at every admitted size, with every right-hand side and start. -/
theorem accepts_one {uf u ur : ℝ} {d : Fin 2 → ℕ} (hd : valid uf u ur d)
    (b x : Fin (d 0) → ℝ) : accepts uf u ur d (1, b, x) := by
  refine ⟨Matrix.PosDef.one, ?_⟩
  change 24 * ((d 0 : ℝ) + 1) ^ 2 * (uf + uf) *
      pseudoConditionNumber (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ) ≤ 1 ∧
    refinementContractionFactor (pseudoConditionNumber (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ))
      (24 * ((d 0 : ℝ) + 1) ^ 2 * (uf + uf) *
        pseudoConditionNumber (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ))
      ((1 + u) * (((d 0 : ℝ) + 1) * roundingFactor (d 0 + 1) ur)) u u < 1
  rw [pseudoConditionNumber_one_eq]
  by_cases h0 : d 0 = 0
  · simp [h0, refinementContractionFactor]
  · rw [if_neg h0, mul_one]
    exact hd.2.resolve_left h0

/-- **The problem data of three-precision refinement**: at the sizes `valid`, the admitted
systems `accepts`, with $\mathbf{A}$ stored by columns in the first buffer, $\mathbf{b}$ in the
second and the start in the third, which the run updates in place. All scratch is allocated by
the program. The hypothesis $u_r < 1$ makes the order zero an admitted size. -/
noncomputable def inputs (uf u ur : ℝ) (hur1 : ur < 1) :
    (solve (Op := Signature) (Tst := CmpTst)).Domain ℝ 2 3 where
  valid := valid uf u ur
  In d := Matrix (Fin (d 0)) (Fin (d 0)) ℝ × (Fin (d 0) → ℝ) × (Fin (d 0) → ℝ)
  accepts := accepts uf u ur
  slot d := ![.stored (Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)) Prod.fst,
    .stored (Codec.vector (d 0)) fun x => x.2.1, .stored (Codec.vector (d 0)) fun x => x.2.2]
  fits := by domain_fits
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp only [Slot.input, Matrix.cons_val, Option.some.injEq] at h0 h1 h2
    exact Prod.ext ((Codec.matrix (EntryCodec.scalar ℝ) (d 0) (d 0)).encode_injective h0)
      (Prod.ext ((Codec.vector (d 0)).encode_injective h1)
        ((Codec.vector (d 0)).encode_injective h2))
  admitted := ⟨fun _ => 0, by simpa using hur1, Or.inl rfl⟩
  inhabited _ hd := ⟨(1, 0, 0), accepts_one hd 0 0⟩

/-- The system, stored and updated in three buffers: the problem of three-precision
refinement. -/
noncomputable abbrev problem (uf u ur : ℝ) (hur1 : ur < 1) : Problem ℝ 2 3 :=
  (inputs uf u ur hur1).problem

/-- The storage arities of the operations: those of scalar arithmetic at each tag, and one cell
to one cell for a cast. -/
def signature : Signature → OperandSignature
  | .f a | .w a | .r a => Standard.signature (.scalar a)
  | .castWF | .castFW | .castWR | .castRW => ⟨[.cell], [.cell]⟩

/-- Unit weights: each operation counts one and uses no workspace. -/
def resources : ResourceModel Signature CmpTst :=
  Functional.cellResources signature (fun _ _ => 1) (fun _ _ => 0)

/-- **The operation model**: the functions of three machines at the three tags and of the four
casts, on all operands, with unit weights. It has no oracle: the matrix is stored and is read
through scalar operations. Its contracts are realized jointly by the interpretation of these
functions (`NLAlib.Ops.Functional.model`, through `NLAlib.Ops.Interp.ofFns`). -/
noncomputable abbrev model (Mf Mw Mr : Machine ℝ) (cWF cFW cWR cRW : ℝ → ℝ) (uf u ur : ℝ)
    (hur1 : ur < 1) : AccessModel Signature CmpTst (problem uf u ur hur1) :=
  Functional.model (problem uf u ur hur1) id
    (fun _ _ => Signature.fn Mf Mw Mr cWF cFW cWR cRW) resources

instance charged_model (Mf Mw Mr : Machine ℝ) (cWF cFW cWR cRW : ℝ → ℝ) (uf u ur : ℝ)
    (hur1 : ur < 1) : (model Mf Mw Mr cWF cFW cWR cRW uf u ur hur1).Charged :=
  ⟨fun _ _ => Nat.one_pos, fun _ _ => Nat.one_pos, fun _ _ => Nat.one_pos⟩

/-- **The arithmetic of the certificate**: three machines in the standard model at the unit
roundoffs $u_f$, $u$, $u_r \ge 0$; the casts to the factorization precision and from the
residual precision round at $u_f$ and at $u$, and the two widening casts are exact. -/
structure IsArithmetic (Mf Mw Mr : Machine ℝ) (cWF cFW cWR cRW : ℝ → ℝ) (uf u ur : ℝ) :
    Prop where
  /-- The standard model at the factorization precision. -/
  stdF : StdModel uf id Mf
  /-- The standard model at the working precision. -/
  stdW : StdModel u id Mw
  /-- The standard model at the residual precision. -/
  stdR : StdModel ur id Mr
  /-- Narrowing to the factorization precision rounds at its unit roundoff. -/
  modelWF : CastModel uf id cWF
  /-- Widening from the factorization precision is exact. -/
  modelFW : CastModel 0 id cFW
  /-- Widening to the residual precision is exact. -/
  modelWR : CastModel 0 id cWR
  /-- Narrowing from the residual precision rounds at the working unit roundoff. -/
  modelRW : CastModel u id cRW
  /-- The factorization unit roundoff is nonnegative. -/
  huf : 0 ≤ uf
  /-- The working unit roundoff is nonnegative. -/
  hu : 0 ≤ u
  /-- The residual unit roundoff is nonnegative. -/
  hur : 0 ≤ ur

/-- An interpretation satisfying the model has the contracts of the judgment. -/
theorem isThreePrecision_of_contracts {Mf Mw Mr : Machine ℝ} {cWF cFW cWR cRW : ℝ → ℝ}
    {uf u ur : ℝ} {hur1 : ur < 1} (hS : IsArithmetic Mf Mw Mr cWF cFW cWR cRW uf u ur)
    {d : Fin 2 → ℕ} {X : (problem uf u ur hur1).Input d} {I : Interp Signature CmpTst ℝ}
    (hI : (model Mf Mw Mr cWF cFW cWR cRW uf u ur hur1).contracts d X I) :
    IsThreePrecision Mf Mw Mr cWF cFW cWR cRW uf u ur I where
  scalarF a := Functional.isFn hI (.f a)
  scalarW a := Functional.isFn hI (.w a)
  scalarR a := Functional.isFn hI (.r a)
  castWF := Functional.isFn hI .castWF
  castFW := Functional.isFn hI .castFW
  castWR := Functional.isFn hI .castWR
  castRW := Functional.isFn hI .castRW
  stdF := hS.stdF
  stdW := hS.stdW
  stdR := hS.stdR
  modelWF := hS.modelWF
  modelFW := hS.modelFW
  modelWR := hS.modelWR
  modelRW := hS.modelRW
  huf := hS.huf
  hu := hS.hu
  hur := hS.hur

/-- The fixed program: the routine closed on the three buffers of the problem. -/
def program : Program Signature CmpTst 2 3 := (solve (Tst := CmpTst)).close 2 3

/-- The number of instructions at order $n$ and $k$ rounds, at most:
$52 n^3 + 104 n^2 k + 97 n^2 + 125 n k + 38 n + 113 k + 119$. -/
def operationCount (d : Fin 2 → ℕ) : ℕ :=
  52 * d 0 ^ 3 + 104 * d 0 ^ 2 * d 1 + 97 * d 0 ^ 2 + 125 * d 0 * d 1 + 38 * d 0 + 113 * d 1 + 119

/-- The instruction polynomial of the program, computed by the kernel. -/
theorem countPoly_program : program.countPoly =
    [(104, [0, 0, 1]), (113, [1]), (125, [0, 1]), (52, [0, 0, 0]), (97, [0, 0]), (38, [0]),
      (119, [])] := by
  kernel_rfl

/-- The polynomial of the program at the sizes `d` is the operation count. -/
theorem eval_countPoly_program (d : Fin 2 → ℕ) :
    CountPoly.eval (List.ofFn d) program.countPoly = operationCount d := by
  rw [countPoly_program]
  poly_eval [operationCount]

/-- The word at the position of entry $(i, j)$ of a matrix stored by columns is the entry. -/
theorem vec_encode_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    vec ((Codec.matrix (EntryCodec.scalar ℝ) n n).encode A) (j * n + i) = A i j := by
  have h := congrFun (congrFun (EntryCodec.matrix_packFinMatrix (EntryCodec.scalar ℝ) A) i) j
  simp only [EntryCodec.matrix, EntryCodec.scalar_entry] at h
  exact h

/-- **The certificate of three-precision refinement.** On every admitted system the fixed
program succeeds within the stated number of instructions of the model with unit weights, and
the stored iterate is the last iterate of a refinement run. No success or numerical execution
witness is an assumption. The result is normwise in the 2-norm, and the machines are in the
standard model, so overflow and underflow are not modelled. -/
noncomputable def algorithm {Mf Mw Mr : Machine ℝ} {cWF cFW cWR cRW : ℝ → ℝ} {uf u ur : ℝ}
    (hS : IsArithmetic Mf Mw Mr cWF cFW cWR cRW uf u ur) (hur1 : ur < 1) :
    Algorithm (model Mf Mw Mr cWF cFW cWR cRW uf u ur hur1)
      ((solve (Op := Signature) (Tst := CmpTst)).specification
        (P := problem uf u ur hur1) (fun _ X => solveSpec X.val.1.1 uf u ur)
        (model Mf Mw Mr cWF cFW cWR cRW uf u ur hur1).resources
        (fun d X => (inputs uf u ur hur1).blocks d X.val.1)
        (inputs uf u ur hur1).bytes operationCount) :=
  (inputs uf u ur hur1).certify (fun _ x => solveSpec x.1 uf u ur) operationCount
    (fun _ _ X _ hI => solve_meets (isThreePrecision_of_contracts hS hI) X.val.1.1)
    (fun _ hd x hx _ => ⟨rfl, vec_encode_matrix x.1, hx.1, hd.1, hx.2.1⟩)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun d _ => (eval_countPoly_program d).le)

/-- **Forward error of certified three-precision refinement.** Let three machines be in the
standard model at unit roundoffs $u_f, u, u_r \ge 0$ with $u_r < 1$, the casts to the
factorization precision and from the residual precision round at $u_f$ and $u$, and the two
widening casts be exact. At an admitted size $[n, k]$, for every positive definite
$\mathbf{A}$ with $24(n + 1)^2(u_f + u_f)\kappa(\mathbf{A}) \le 1$ and contraction factor
$\varphi < 1$, every right-hand side $\mathbf{b}$ and start $\mathbf{x}_0$, every interpretation
of the operations satisfying the model, and every tape, the counted run of the fixed program
from the three stored inputs succeeds, executes at most
$52 n^3 + 104 n^2 k + 97 n^2 + 125 n k + 38 n + 113 k + 119$ instructions, keeps its resident
memory within the payload of the three buffers plus the static scratch of the tree, and the
third buffer then holds $\hat{\mathbf{x}}$ with, for every $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$,
$$\|\mathbf{x}_\star - \hat{\mathbf{x}}\| \le \varphi^k\|\mathbf{x}_\star - \mathbf{x}_0\| +
\frac{\xi}{1 - \varphi}\,\|\mathbf{x}_\star\|\,.$$
Here, with $\kappa = \kappa(\mathbf{A})$, $\theta = 24(n + 1)^2(u_f + u_f)\kappa$ and
$\eta = (1 + u)(n + 1)\gamma_{n+1}(u_r)$, the contraction factor is
the following, <!-- value refinementContractionFactor \kappa \theta \eta u u -->
$\varphi = (1+u)(\theta+(1+\theta)\kappa(u+\eta))$, and the accuracy bound is
the following, <!-- value refinementAccuracyBound \kappa \theta \eta u -->
$\xi = (1+u)(1+\theta)2\kappa\eta+u$.
[CarsonHigham2018, Corollary 3.3]; stated there in the $\infty$-norm, here **normwise in the
2-norm**, with the Cholesky factorization as the solver.

Note: the machines are in the standard model on all operands, so overflow and underflow are not
modelled. The matrix is stored and read through scalar operations: the model has no oracle.
Result: three-precision-iterative-refinement -/
theorem algorithm_checked {Mf Mw Mr : Machine ℝ} {cWF cFW cWR cRW : ℝ → ℝ} {uf u ur : ℝ}
    (hS : IsArithmetic Mf Mw Mr cWF cFW cWR cRW uf u ur) (hur1 : ur < 1)
    (d : Fin 2 → ℕ) (hd : valid uf u ur d)
    (A : Matrix (Fin (d 0)) (Fin (d 0)) ℝ) (rhs x₀ : Fin (d 0) → ℝ) (hA : A.PosDef)
    (hsmall : 24 * ((d 0 : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A ≤ 1)
    (hφ : refinementContractionFactor (pseudoConditionNumber A)
      (24 * ((d 0 : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A)
      ((1 + u) * (((d 0 : ℝ) + 1) * roundingFactor (d 0 + 1) ur)) u u < 1)
    (I : Interp Signature CmpTst ℝ)
    (hI : (model Mf Mw Mr cWF cFW cWR cRW uf u ur hur1).contracts d
      ((inputs uf u ur hur1).input d (A, rhs, x₀) ⟨hA, hsmall, hφ⟩) I)
    (τ : Tape ℝ) :
    ∃ st, Reference.Execution program I (model Mf Mw Mr cWF cFW cWR cRW uf u ur hur1).resources
        (inputs uf u ur hur1).formats τ d ((inputs uf u ur hur1).memory d (A, rhs, x₀)) st ∧
      (model Mf Mw Mr cWF cFW cWR cRW uf u ur hur1).resources.work st.cost ≤
        52 * d 0 ^ 3 + 104 * d 0 ^ 2 * d 1 + 97 * d 0 ^ 2 + 125 * d 0 * d 1 + 38 * d 0 +
          113 * d 1 + 119 ∧
      (inputs uf u ur hur1).bytes d + st.peak ≤
        (inputs uf u ur hur1).bytes d +
          staticPeak (model Mf Mw Mr cWF cFW cWR cRW uf u ur hur1).resources program d ∧
      ∃ x : Fin (d 0) → ℝ, st.mem.Holds (Codec.vector (d 0)) 2 x ∧
        ∀ xstar : Fin (d 0) → ℝ, A *ᵥ xstar = rhs →
          ‖WithLp.toLp 2 (xstar - x)‖ ≤
            refinementContractionFactor (pseudoConditionNumber A)
                (24 * ((d 0 : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A)
                ((1 + u) * (((d 0 : ℝ) + 1) * roundingFactor (d 0 + 1) ur)) u u ^ d 1 *
                ‖WithLp.toLp 2 (xstar - x₀)‖ +
              refinementAccuracyBound (pseudoConditionNumber A)
                  (24 * ((d 0 : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A)
                  ((1 + u) * (((d 0 : ℝ) + 1) * roundingFactor (d 0 + 1) ur)) u /
                (1 - refinementContractionFactor (pseudoConditionNumber A)
                  (24 * ((d 0 : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A)
                  ((1 + u) * (((d 0 : ℝ) + 1) * roundingFactor (d 0 + 1) ur)) u u) *
                ‖WithLp.toLp 2 xstar‖ := by
  obtain ⟨st, hr, hw, hm, ys, hys, hpost⟩ :=
    (inputs uf u ur hur1).checked_post (Sp := fun _ x => solveSpec x.1 uf u ur)
      (work := operationCount) (algorithm hS hur1) d hd (A, rhs, x₀) ⟨hA, hsmall, hφ⟩ I hI τ
  refine ⟨st, hr, hw, hm, ?_⟩
  read_outputs hys as (xs')
  obtain ⟨R, h0, hk⟩ : ∃ R : RefinementRun A (decv id (d 0) (List.ofFn rhs))
      (24 * ((d 0 : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A)
      ((1 + u) * (((d 0 : ℝ) + 1) * roundingFactor (d 0 + 1) ur)) u u (d 1),
      R.x 0 = decv id (d 0) (List.ofFn x₀) ∧ R.x (d 1) = decv id (d 0) xs' := hpost
  refine ⟨decv id (d 0) xs', Mem.holds_decode _ hxs', fun xstar hstar => ?_⟩
  have h := R.norm_sub_x_le (hstar.trans (decv_ofFn rhs).symm) hφ le_rfl
  rw [h0, hk, decv_ofFn] at h
  exact h

end NLAlib.LinearSystems.Refinement.Rounded.Certification
