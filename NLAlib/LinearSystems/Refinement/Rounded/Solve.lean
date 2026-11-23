/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LinearSystems.Refinement.Kernels
public import NLAlib.LinearSystems.Refinement.Rounded.Bounds
public import NLAlib.LinearSystems.Refinement.Rounded.Signature
public import NLAlib.Matrix.Factorizations.Cholesky.Routine
public import NLAlib.Matrix.Factorizations.TriangularSolve.Routine
public import NLAlib.Ops.Catalog.Operator

/-!
# Iterative refinement in three precisions, in scalar arithmetic

`NLAlib.LinearSystems.Refinement.Rounded.solve` is the whole program for a symmetric positive
definite system: it casts the matrix to the factorization precision, factors it by left-looking
Cholesky there, casts the matrix and the right-hand side to the residual precision, and runs $k$
rounds of residual (residual precision), correction solve with the computed factor
(factorization precision) and update (working precision), with a cast at each change of
precision. Every operation of the tree is a scalar operation at one of the three tags or a cast.

The judgment gives a `NLAlib.RefinementRun` whose last iterate is the stored output, with the
accuracies computed from the three unit roundoffs. The analysis is normwise in the 2-norm, and
the machines are in the standard model: no overflow or underflow is modelled.

## Main definitions

* `NLAlib.LinearSystems.Refinement.Rounded.setup`: the casts and the factorization.
* `NLAlib.LinearSystems.Refinement.Rounded.round`: one round of refinement.
* `NLAlib.LinearSystems.Refinement.Rounded.solve`: the program.
* `NLAlib.LinearSystems.Refinement.Rounded.IsThreePrecision`: its contracts and arithmetic.
* `NLAlib.LinearSystems.Refinement.Rounded.solveSpec`: its specification.

## Main results

* `NLAlib.LinearSystems.Refinement.Rounded.round_bounds`: the local bounds of a round, on values.
* `NLAlib.LinearSystems.Refinement.Rounded.setup_meets`: the setup meets its specification.
* `NLAlib.LinearSystems.Refinement.Rounded.round_meets`: one round meets its specification.
* `NLAlib.LinearSystems.Refinement.Rounded.solve_meets`: the program meets its specification.
-/

@[expose] public section

namespace NLAlib.LinearSystems.Refinement.Rounded

open Ops Computation
open scoped Matrix

variable {Op Tst : Type} [Has (Tagged FTag ScalarOp) Op] [Has (Tagged WTag ScalarOp) Op]
  [Has (Tagged RTag ScalarOp) Op] [Has (CastOp WTag FTag) Op] [Has (CastOp FTag WTag) Op]
  [Has (CastOp WTag RTag) Op] [Has (CastOp RTag WTag) Op]

/-! ### The routines -/

/-- **The setup of three-precision refinement**, a routine of
`NLAlib.LinearSystems.Refinement.Rounded.solve`: cast $\mathbf{A}$ to the factorization precision
and factor it there by left-looking Cholesky, then cast $\mathbf{A}$ and $\mathbf{b}$ to the
residual precision. -/
def setup : Routine Op Tst :=
  routine% [n] (A : n * n, b : n) → (LF : n * n, AR : n * n, bR : n) {
    run (castLoop WTag FTag (Op := Op) (Tst := Tst)) [n * n] (A, LF);
    run (@Cholesky.leftLooking Op Tst (Tagged.has FTag)) [n] (LF);
    run (castLoop WTag RTag (Op := Op) (Tst := Tst)) [n * n] (A, AR);
    run (castLoop WTag RTag (Op := Op) (Tst := Tst)) [n] (b, bR)
  }

/-- **One round of three-precision refinement**, a routine of
`NLAlib.LinearSystems.Refinement.Rounded.solve`: the residual at the residual precision, cast to
the working and then the factorization precision; forward and back substitution with the factor
at the factorization precision; the correction cast to the working precision and added to the
iterate there. -/
def round : Routine Op Tst :=
  routine% [n] (L : n * n, AR : n * n, bR : n, x : n) →
      (x, unreported xR : n, unreported rR : n, unreported rW : n, unreported dF : n,
        unreported dW : n) {
    run (castLoop WTag RTag (Op := Op) (Tst := Tst)) [n] (x, xR);
    run (@residualRows Op Tst (Tagged.has RTag)) [n] (AR, bR, xR, rR);
    run (castLoop RTag WTag (Op := Op) (Tst := Tst)) [n] (rR, rW);
    run (castLoop WTag FTag (Op := Op) (Tst := Tst)) [n] (rW, dF);
    run (@TriangularSolve.forward Op Tst (Tagged.has FTag)) [n] (L, dF);
    run (@TriangularSolve.backward Op Tst (Tagged.has FTag)) [n] (L, dF);
    run (castLoop FTag WTag (Op := Op) (Tst := Tst)) [n] (dF, dW);
    run (@addInPlace Op Tst (Tagged.has WTag)) [n] (dW, x)
  }

/-- **The $k$ rounds of three-precision refinement**, a routine of
`NLAlib.LinearSystems.Refinement.Rounded.solve`, on scratch supplied by it. -/
def rounds : Routine Op Tst :=
  routine% [n, k] (L : n * n, AR : n * n, bR : n, x : n) →
      (x, unreported xR : n, unreported rR : n, unreported rW : n, unreported dF : n,
        unreported dW : n) {
    for j < k {
      run (round (Op := Op) (Tst := Tst)) [n] (L, AR, bR, x, xR, rR, rW, dF, dW)
    }
  }

/-- **Iterative refinement in three precisions** for a symmetric positive definite system, in
scalar arithmetic at three precision tags: the setup, then $k$ rounds, on scratch allocated by
the routine. [CarsonHigham2018, Algorithm 1.1], with Cholesky as the factorization.
Algorithm: iterative-refinement-three-precision -/
def solve : Routine Op Tst :=
  routine% [n, k] (A : n * n, b : n, x : n) → (x) {
    let LF ← alloc n * n;
    let AR ← alloc n * n;
    let bR ← alloc n;
    let xR ← alloc n;
    let rR ← alloc n;
    let rW ← alloc n;
    let dF ← alloc n;
    let dW ← alloc n;
    run (setup (Op := Op) (Tst := Tst)) [n] (A, b, LF, AR, bR);
    run (rounds (Op := Op) (Tst := Tst)) [n, k] (LF, AR, bR, x, xR, rR, rW, dF, dW)
  }

/-! ### The model of the arithmetic -/

/-- **The contracts and the arithmetic of three-precision refinement**: the scalar operations at
each tag are the functions of a machine in the standard model at its unit roundoff; the casts
to the factorization precision and from the residual precision round at the unit roundoff of
their target, and the two widening casts are exact. -/
structure IsThreePrecision (Mf Mw Mr : Machine ℝ) (cWF cFW cWR cRW : ℝ → ℝ) (uf u ur : ℝ)
    (I : Interp Op Tst ℝ) : Prop where
  /-- Scalar arithmetic at the factorization precision. -/
  scalarF : IsScalarAt FTag Mf I
  /-- Scalar arithmetic at the working precision. -/
  scalarW : IsScalarAt WTag Mw I
  /-- Scalar arithmetic at the residual precision. -/
  scalarR : IsScalarAt RTag Mr I
  /-- The cast from the working to the factorization precision. -/
  castWF : IsCast WTag FTag cWF I
  /-- The cast from the factorization to the working precision. -/
  castFW : IsCast FTag WTag cFW I
  /-- The cast from the working to the residual precision. -/
  castWR : IsCast WTag RTag cWR I
  /-- The cast from the residual to the working precision. -/
  castRW : IsCast RTag WTag cRW I
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

/-- The state after the setup, for the matrix $\mathbf{A}$ and the right-hand side $\mathbf{b}$:
the words `Ls` are a Cholesky trace at unit roundoff $u_f$ on entries within relative error $u_f$
of $\mathbf{A}$, and the words `ARs`, `bRs` hold $\mathbf{A}$ and $\mathbf{b}$ exactly. -/
structure IsFactored {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (uf : ℝ)
    (Ls ARs bRs : List ℝ) : Prop where
  /-- The factor is a Cholesky trace on entries that are those of the matrix up to `uf`. -/
  chol : ∃ a : ℕ → ℕ → ℝ, IsCholTrace uf a (fun i j => vec Ls (j * n + i)) n ∧
    ∀ i j : Fin n, j ≤ i → |a i j - A i j| ≤ uf * |A i j|
  /-- The matrix in the residual precision, by columns. -/
  entryA : ∀ i j : Fin n, vec ARs (j * n + i) = A i j
  /-- The right-hand side in the residual precision. -/
  entryb : ∀ i : Fin n, vec bRs i = b i

/-! ### Specifications -/

/-- At the order of $\mathbf{A}$, with $\mathbf{A}$ stored by columns in the block read, the
blocks written are the state `NLAlib.LinearSystems.Refinement.Rounded.IsFactored`. -/
def setupSpec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (uf : ℝ) : Routine.Spec ℝ :=
  spec% [m] (As, bs) → (Ls, ARs, bRs)
    requires m = n ∧ ∀ i j : Fin n, vec As (j * n + i) = A i j
    ensures IsFactored A (decv id n bs) uf Ls ARs bRs

/-- From the state after the setup, for a positive definite $\mathbf{A}$ with
$(n + 1) u_r < 1$ and $24(n + 1)^2(u_f + u_f)\kappa(\mathbf{A}) \le 1$, one round computes a
residual, a correction and a next iterate that meet the three local bounds of a refinement
step. -/
def roundSpec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (uf u ur : ℝ) :
    Routine.Spec ℝ :=
  spec% [m] (Ls, ARs, bRs, xs) → (xs')
    requires m = n ∧ A.PosDef ∧ ((n : ℝ) + 1) * ur < 1 ∧
      24 * ((n : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A ≤ 1 ∧
      IsFactored A b uf Ls ARs bRs
    ensures ∃ r d : Fin n → ℝ,
      ‖WithLp.toLp 2 (b - A *ᵥ decv id n xs - r)‖ ≤ u * ‖WithLp.toLp 2 (b - A *ᵥ decv id n xs)‖ +
        (1 + u) * (((n : ℝ) + 1) * roundingFactor (n + 1) ur) *
          (‖WithLp.toLp 2 b‖ + specNorm A * ‖WithLp.toLp 2 (decv id n xs)‖) ∧
      ‖WithLp.toLp 2 (A⁻¹ *ᵥ r - d)‖ ≤
        24 * ((n : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A *
          ‖WithLp.toLp 2 (A⁻¹ *ᵥ r)‖ ∧
      ‖WithLp.toLp 2 (decv id n xs + d - decv id n xs')‖ ≤
        u * ‖WithLp.toLp 2 (decv id n xs + d)‖

/-- From the state after the setup, for a positive definite $\mathbf{A}$ with
$(n + 1) u_r < 1$ and $24(n + 1)^2(u_f + u_f)\kappa(\mathbf{A}) \le 1$, the iterate written after
$k$ rounds is the last iterate of a refinement run from the decoded start. -/
def roundsSpec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (uf u ur : ℝ) :
    Routine.Spec ℝ :=
  spec% [m, k] (Ls, ARs, bRs, xs) → (xs')
    requires m = n ∧ A.PosDef ∧ ((n : ℝ) + 1) * ur < 1 ∧
      24 * ((n : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A ≤ 1 ∧
      IsFactored A b uf Ls ARs bRs
    ensures ∃ R : RefinementRun A b
        (24 * ((n : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A)
        ((1 + u) * (((n : ℝ) + 1) * roundingFactor (n + 1) ur)) u u k,
      R.x 0 = decv id n xs ∧ R.x k = decv id n xs'

/-- **The specification of three-precision refinement.** At dimensions $[n, k]$, with the
positive definite $\mathbf{A}$ stored by columns in the first block, $(n + 1) u_r < 1$ and
$24(n + 1)^2(u_f + u_f)\kappa(\mathbf{A}) \le 1$, the iterate written is the last iterate of a
refinement run of $k$ steps from the decoded start, with
$\theta = 24(n + 1)^2(u_f + u_f)\kappa(\mathbf{A})$,
$\eta = (1 + u)(n + 1)\gamma_{n+1}(u_r)$, $\zeta = u$ and $\varepsilon = u$. -/
def solveSpec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (uf u ur : ℝ) : Routine.Spec ℝ :=
  spec% [m, k] (As, bs, xs) → (xs')
    requires m = n ∧ (∀ i j : Fin n, vec As (j * n + i) = A i j) ∧ A.PosDef ∧
      ((n : ℝ) + 1) * ur < 1 ∧
      24 * ((n : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A ≤ 1
    ensures ∃ R : RefinementRun A (decv id n bs)
        (24 * ((n : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A)
        ((1 + u) * (((n : ℝ) + 1) * roundingFactor (n + 1) ur)) u u k,
      R.x 0 = decv id n xs ∧ R.x k = decv id n xs'

/-! ### The local bounds, on values -/

/-- A row trace depends on its matrix, right-hand side and solution only at what it reads. -/
theorem isSubstRowTrace_congr {err : BinOp → ℝ → ℝ → Prop} {t t' : ℕ → ℕ → ℝ}
    {b b' x x' s : ℕ → ℝ} {i k : ℕ} (h : IsSubstRowTrace err t b x i k s)
    (ht : ∀ j < k, t i j = t' i j) (hb : b i = b' i) (hx : ∀ j < k, x j = x' j) :
    IsSubstRowTrace err t' b' x' i k s :=
  ⟨h.1.trans hb, fun j hj => by simpa only [ht j hj, hx j hj] using h.2 j hj⟩

/-- The three local bounds of one round, from the values its calls compute, for a positive
definite $\mathbf{A}$ with $(n + 1) u_r < 1$ and
$24(n + 1)^2(u_f + u_f)\kappa(\mathbf{A}) \le 1$: the residual as stored at the working
precision, the correction, and the update. -/
theorem round_bounds {Mf Mw Mr : Machine ℝ} {cWF cFW cWR cRW : ℝ → ℝ} {uf u ur : ℝ}
    {I : Interp Op Tst ℝ} (h : IsThreePrecision Mf Mw Mr cWF cFW cWR cRW uf u ur I) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {Ls ARs bRs xs xRs rRs rWs dFs ys ds dWs xs' :
      List ℝ} {τ₁ τ₂ τ₃ τ₄ τ₅ τ₆ τ₇ τ₈ : Tape ℝ} (hA : A.PosDef)
    (hn : ((n : ℝ) + 1) * ur < 1)
    (hsmall : 24 * ((n : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A ≤ 1)
    (hF : IsFactored A b uf Ls ARs bRs)
    (h₁ : (castLoopSpec cWR).post [n] τ₁ [xs] [xRs])
    (h₂ : (residualRowsSpec ur id).post [n] τ₂ [ARs, bRs, xRs] [rRs])
    (h₃ : (castLoopSpec cRW).post [n] τ₃ [rRs] [rWs])
    (h₄ : (castLoopSpec cWF).post [n] τ₄ [rWs] [dFs])
    (h₅ : (TriangularSolve.forwardSpec uf id).post [n] τ₅ [Ls, dFs] [ys])
    (h₆ : (TriangularSolve.backwardSpec uf id).post [n] τ₆ [Ls, ys] [ds])
    (h₇ : (castLoopSpec cFW).post [n] τ₇ [ds] [dWs])
    (h₈ : (addInPlaceSpec u id).post [n] τ₈ [dWs, xs] [xs']) :
    ∃ r d : Fin n → ℝ,
      ‖WithLp.toLp 2 (b - A *ᵥ decv id n xs - r)‖ ≤ u * ‖WithLp.toLp 2 (b - A *ᵥ decv id n xs)‖ +
        (1 + u) * (((n : ℝ) + 1) * roundingFactor (n + 1) ur) *
          (‖WithLp.toLp 2 b‖ + specNorm A * ‖WithLp.toLp 2 (decv id n xs)‖) ∧
      ‖WithLp.toLp 2 (A⁻¹ *ᵥ r - d)‖ ≤
        24 * ((n : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A *
          ‖WithLp.toLp 2 (A⁻¹ *ᵥ r)‖ ∧
      ‖WithLp.toLp 2 (decv id n xs + d - decv id n xs')‖ ≤
        u * ‖WithLp.toLp 2 (decv id n xs + d)‖ := by
  obtain rfl : xRs = (List.range n).map fun i => cWR (vec xs i) := h₁
  obtain rfl : rWs = (List.range n).map fun i => cRW (vec rRs i) := h₃
  obtain rfl : dFs = (List.range n).map fun i => cWF (vec ((List.range n).map
      fun i => cRW (vec rRs i)) i) := h₄
  obtain rfl : dWs = (List.range n).map fun i => cFW (vec ds i) := h₇
  obtain ⟨a, hchol, ha⟩ := hF.chol
  refine ⟨decv id n ((List.range n).map fun i => cRW (vec rRs i)),
    decv id n ((List.range n).map fun i => cFW (vec ds i)), ?_, ?_, ?_⟩
  · refine norm_sub_mulVec_sub_cast_le (rh := decv id n rRs) h.hu h.hur hn (fun i => ?_)
      (fun i => ?_)
    · obtain ⟨s, hs, hsn⟩ := h₂ i i.2
      refine ⟨s, isSubstRowTrace_congr hs (fun j hj => ?_) ?_ (fun j hj => ?_), hsn⟩
      · simpa [i.2, hj] using hF.entryA i ⟨j, hj⟩
      · simpa [i.2] using hF.entryb i
      · change vec _ j = if hj : j < n then decv id n xs ⟨j, hj⟩ else 0
        rw [TriangularSolve.vec_map_range _ hj, dif_pos hj]
        exact h.modelWR.eq_of_zero (vec xs j)
    · simpa [decv, TriangularSolve.vec_map_range _ i.2] using h.modelRW (vec rRs i)
  · refine norm_inv_mulVec_sub_correction_le hchol hA h.huf ha hsmall
      (rh := fun i => vec ((List.range n).map fun i => cWF (vec ((List.range n).map
        fun i => cRW (vec rRs i)) i)) i) (y := fun i => vec ys i) (d := fun i => vec ds i)
      (fun i => ?_) h₅ h₆ (fun i => ?_)
    · simpa [decv, TriangularSolve.vec_map_range _ i.2] using h.modelWF (vec ((List.range n).map
        fun i => cRW (vec rRs i)) i)
    · simpa [decv, TriangularSolve.vec_map_range _ i.2] using h.modelFW.eq_of_zero (vec ds i)
  · exact norm_add_sub_update_le h.hu fun i => h₈ i i.2

/-- The values the setup computes are the state
`NLAlib.LinearSystems.Refinement.Rounded.IsFactored`. -/
theorem isFactored_of_setup {Mf Mw Mr : Machine ℝ} {cWF cFW cWR cRW : ℝ → ℝ} {uf u ur : ℝ}
    {I : Interp Op Tst ℝ} (h : IsThreePrecision Mf Mw Mr cWF cFW cWR cRW uf u ur I) {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {As bs L₀ Ls ARs bRs : List ℝ}
    (hAs : ∀ i j : Fin n, vec As (j * n + i) = A i j)
    (hL₀ : L₀ = (List.range (n * n)).map fun i => cWF (vec As i))
    (hL : IsCholTrace uf (fun i j => vec L₀ (j * n + i)) (fun i j => vec Ls (j * n + i)) n)
    (hAR : ARs = (List.range (n * n)).map fun i => cWR (vec As i))
    (hbR : bRs = (List.range n).map fun i => cWR (vec bs i)) :
    IsFactored A (decv id n bs) uf Ls ARs bRs := by
  subst hL₀ hAR hbR
  refine ⟨⟨_, hL, fun i j _ => ?_⟩, fun i j => ?_, fun i => ?_⟩
  · have hlt := TriangularSolve.mul_add_lt_mul_self j.2 i.2
    change |vec _ (j * n + i) - A i j| ≤ _
    rw [TriangularSolve.vec_map_range _ hlt, hAs i j]
    exact h.modelWF (A i j)
  · have hlt := TriangularSolve.mul_add_lt_mul_self j.2 i.2
    rw [TriangularSolve.vec_map_range _ hlt, hAs i j]
    exact h.modelWR.eq_of_zero (A i j)
  · rw [TriangularSolve.vec_map_range _ i.2]
    exact h.modelWR.eq_of_zero (vec bs i)

/-! ### The judgments -/

/-- The setup meets its specification. -/
theorem setup_meets {Mf Mw Mr : Machine ℝ} {cWF cFW cWR cRW : ℝ → ℝ} {uf u ur : ℝ}
    {I : Interp Op Tst ℝ} (h : IsThreePrecision Mf Mw Mr cWF cFW cWR cRW uf u ur I) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (setup (Op := Op) (Tst := Tst)).Meets I (setupSpec A uf) := by
  routine_intro [n'] (Am, b, LF, AR, bR) reads (As, bs)
  obtain ⟨rfl, hAs⟩ := hpre
  call (castLoop_meets h.castWF) [n' * n'] (Am, LF) as m₁ hfr₁ hpos₁ (L₀) hpost₁
  call (@Cholesky.leftLooking_meets ℝ Op Tst (Tagged.has FTag) _ Mf I uf id
    h.scalarF.isScalar h.stdF) [n'] (LF) as m₂ hfr₂ hpos₂ (Ls) hpost₂
  call (castLoop_meets h.castWR) [n' * n'] (Am, AR) as m₃ hfr₃ hpos₃ (ARs) hpost₃
  call (castLoop_meets h.castWR) [n'] (b, bR) as m₄ hfr₄ hpos₄ (bRs) hpost₄
  routine_exit
  exact isFactored_of_setup h hAs hpost₁ hpost₂ hpost₃ hpost₄

/-- One round meets its specification. -/
theorem round_meets {Mf Mw Mr : Machine ℝ} {cWF cFW cWR cRW : ℝ → ℝ} {uf u ur : ℝ}
    {I : Interp Op Tst ℝ} (h : IsThreePrecision Mf Mw Mr cWF cFW cWR cRW uf u ur I) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (round (Op := Op) (Tst := Tst)).Meets I (roundSpec A b uf u ur) := by
  routine_intro [n'] (L, AR, bR, x, xR, rR, rW, dF, dW) reads (Ls, ARs, bRs, xs)
  obtain ⟨rfl, hA, hn, hsmall, hF⟩ := hpre
  obtain ⟨a, hchol, ha⟩ := hF.chol
  have hpiv : ∀ i < n', vec Ls (i * n' + i) ≠ 0 := fun i hi =>
    ((hchol.pos_and_specNorm_sub_le hA h.huf h.huf ha (by
      have hκ := pseudoConditionNumber_nonneg A
      have huf := h.huf
      have : 0 ≤ ((n' : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A := by positivity
      nlinarith)).1 i hi).ne'
  call (castLoop_meets h.castWR) [n'] (x, xR) as m₁ hfr₁ hpos₁ (xRs) hpost₁
  call (@residualRows_meets ℝ Op Tst (Tagged.has RTag) _ Mr I ur id h.scalarR.isScalar h.stdR)
    [n'] (AR, bR, xR, rR) as m₂ hfr₂ hpos₂ (rRs) hpost₂
  call (castLoop_meets h.castRW) [n'] (rR, rW) as m₃ hfr₃ hpos₃ (rWs) hpost₃
  call (castLoop_meets h.castWF) [n'] (rW, dF) as m₄ hfr₄ hpos₄ (dFs) hpost₄
  call (@TriangularSolve.forward_meets ℝ Op Tst (Tagged.has FTag) _ Mf I uf id
    h.scalarF.isScalar h.stdF) [n'] (L, dF) (pre := hpiv) as m₅ hfr₅ hpos₅ (ys) hpost₅
  call (@TriangularSolve.backward_meets ℝ Op Tst (Tagged.has FTag) _ Mf I uf id
    h.scalarF.isScalar h.stdF) [n'] (L, dF) (pre := hpiv) as m₆ hfr₆ hpos₆ (ds) hpost₆
  call (castLoop_meets h.castFW) [n'] (dF, dW) as m₇ hfr₇ hpos₇ (dWs) hpost₇
  call (@addInPlace_meets ℝ Op Tst (Tagged.has WTag) _ Mw I u id h.scalarW.isScalar h.stdW)
    [n'] (dW, x) as m₈ hfr₈ hpos₈ (xs') hpost₈
  routine_exit
  exact round_bounds h hA hn hsmall hF hpost₁ hpost₂ hpost₃ hpost₄ hpost₅ hpost₆ hpost₇ hpost₈

/-- The $k$ rounds meet their specification: each round extends the refinement run by the three
local bounds of `NLAlib.LinearSystems.Refinement.Rounded.round_meets`. -/
theorem rounds_meets {Mf Mw Mr : Machine ℝ} {cWF cFW cWR cRW : ℝ → ℝ} {uf u ur : ℝ}
    {I : Interp Op Tst ℝ} (h : IsThreePrecision Mf Mw Mr cWF cFW cWR cRW uf u ur I) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (rounds (Op := Op) (Tst := Tst)).Meets I (roundsSpec A b uf u ur) := by
  routine_intro [n', k] (L, AR, bR, x, xR, rR, rW, dF, dW) reads (Ls, ARs, bRs, xs)
  obtain ⟨rfl, hA, hn, hsmall, hF⟩ := hpre
  loop_inv (fun _ => Fp.blocks [x, xR, rR, rW, dF, dW] [n', n', n', n', n', n'])
    (fun j m' => m'.pos = m.pos ∧ ∃ (xs' : List ℝ)
      (R : RefinementRun A b (24 * ((n' : ℝ) + 1) ^ 2 * (uf + uf) * pseudoConditionNumber A)
        ((1 + u) * (((n' : ℝ) + 1) * roundingFactor (n' + 1) ur)) u u j),
      m'.store.readBlock x.1 x.2 n' = some xs' ∧ R.x 0 = decv id n' xs ∧
        R.x j = decv id n' xs')
    with j hj m₁ hfr hP
  case initial =>
    have hκ := pseudoConditionNumber_nonneg A
    have huf := h.huf
    have hu := h.hu
    have hur := h.hur
    have hur1 : ur < 1 := by
      have : (0 : ℝ) ≤ n' := Nat.cast_nonneg n'
      nlinarith
    have hγ := roundingFactor_nonneg (n := n' + 1) hur hur1
    exact ⟨rfl, xs, .start hA.isUnit (by positivity) (by positivity) hu hu _, hxs, rfl, rfl⟩
  case round =>
    obtain ⟨hpos₁, xs', R, hxs', h0, hxj⟩ := hP
    have hLs₁ : m₁.store.readBlock L.1 L.2 (n' * n') = some Ls := by keep
    have hARs₁ : m₁.store.readBlock AR.1 AR.2 (n' * n') = some ARs := by keep
    have hbRs₁ : m₁.store.readBlock bR.1 bR.2 n' = some bRs := by keep
    call (round_meets h A b) [n'] (L, AR, bR, x, xR, rR, rW, dF, dW)
      (pre := ⟨rfl, hA, hn, hsmall, hF⟩) as m₂ hfr₂ hpos₂ (xs'') hpost
    obtain ⟨r, d, hres, hsol, hupd⟩ := hpost
    rw [← hxj] at hres hupd
    exact ⟨hpos₂.trans hpos₁, xs'', R.extend r d (decv id n' xs'') hres hsol hupd, hxs'',
      (R.extend_x_of_le _ _ _ hres hsol hupd (Nat.zero_le j)).trans h0,
      R.extend_x_succ _ _ _ hres hsol hupd⟩
  case exit =>
    rintro m₁ - ⟨hpos₁, xs', R, hx, h0, hk⟩
    exact ⟨hpos₁, [xs'], Mem.readBlocks_of_cons hx rfl, R, h0, hk⟩

/-- Three-precision refinement meets its specification under the contracts and the
arithmetic `NLAlib.LinearSystems.Refinement.Rounded.IsThreePrecision`: the stored iterate is the
last iterate of a refinement run. The result is normwise in the 2-norm and the machines are in
the standard model, so no overflow or underflow is modelled. -/
theorem solve_meets {Mf Mw Mr : Machine ℝ} {cWF cFW cWR cRW : ℝ → ℝ} {uf u ur : ℝ}
    {I : Interp Op Tst ℝ} (h : IsThreePrecision Mf Mw Mr cWF cFW cWR cRW uf u ur I) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (solve (Op := Op) (Tst := Tst)).Meets I (solveSpec A uf u ur) := by
  routine_intro [n', k] (Am, b, x) reads (As, bs, xs)
  obtain ⟨rfl, hAe, hA, hn, hsmall⟩ := hpre
  change Writes .total I τ _ (Env.frame [n', k] [Am, b, x, x]) (Fp.blocks [x] [n']) _ m
  alloc as LF AR bR xR rR rW dF dW
  obtain ⟨hlA, hlb, hlx⟩ := hl
  have hAs₁ := Store.Below.readBlock_of hbelow_LF hlA hAs
  have hbs₁ := Store.Below.readBlock_of hbelow_LF hlb hbs
  have hxs₁ := Store.Below.readBlock_of hbelow_LF hlx hxs
  have hxroom : x.2 + n' ≤ s_LF.len x.1 := by
    rw [hbelow_LF.len_of x.1 hlx]
    exact hroom
  have hlen8 : s_LF.length = m.store.length + 8 := by simpa using hlen_LF
  have hLFr : s_LF.len LF = n' * n' := hLF
  have hARr : s_LF.len AR = n' * n' := hAR
  have hbRr : s_LF.len bR = n' := hbR
  have hxRr : s_LF.len xR = n' := hxR
  have hrRr : s_LF.len rR = n' := hrR
  have hrWr : s_LF.len rW = n' := hrW
  have hdFr : s_LF.len dF = n' := hdF
  have hdWr : s_LF.len dW = n' := hdW
  have hxLF : x.1 ≠ LF := by simp only [LF, Nat.add_eq]; omega
  have hxAR : x.1 ≠ AR := by simp only [AR, Nat.add_eq]; omega
  have hxbR : x.1 ≠ bR := by simp only [bR, Nat.add_eq]; omega
  call (setup_meets h A) [n'] (Am, b, (LF, 0), (AR, 0), (bR, 0)) (pre := ⟨rfl, hAe⟩)
    (sep := by
      refine Routine.separatedAt_of_apartAll ?_
      repeat' constructor
      all_goals (simp only [LF, AR, bR, Nat.add_eq]; omega))
    as m₁ hfr₁ hpos₁ (Ls, ARs, bRs) hF
  case hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true, LF, AR, bR, hlen8, Nat.add_eq]
    omega
  have hxs₂ : m₁.store.readBlock x.1 x.2 n' = some xs := by keep
  call (rounds_meets h A (decv id n' bs)) [n', k]
    ((LF, 0), (AR, 0), (bR, 0), x, (xR, 0), (rR, 0), (rW, 0), (dF, 0), (dW, 0))
    (pre := ⟨rfl, hA, hn, hsmall, hF⟩)
    (sep := by
      refine Routine.separatedAt_of_apartAll ?_
      repeat' constructor
      all_goals (simp only [LF, AR, bR, xR, rR, rW, dF, dW, Nat.add_eq]; omega))
    as m₂ hfr₂ hpos₂ (xs') hpost
  case hlive =>
    simp only [Mem.live_cons, Mem.live_nil, and_true, LF, AR, bR, xR, rR, rW, dF, dW, Nat.add_eq]
    omega
  intro s₂ _ hB
  obtain ⟨R, h0, hk⟩ := hpost
  exact ⟨by simp [hpos₂, hpos₁], [xs'],
    Mem.readBlocks_of_cons (Store.Below.readBlock_of hB hlx hxs') rfl, R, h0, hk⟩

end NLAlib.LinearSystems.Refinement.Rounded
