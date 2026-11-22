/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.CG.HSPCG.Rounded.StoredContext
public import NLAlib.Krylov.CG.HSPCG.Rounded.ZeroStart
public import NLAlib.Ops.RoutineData
public import NLAlib.Krylov.CG.HSPCG.Rounded.Prefix
public import NLAlib.Ops.Profiles.RoundedScalarBlas

/-!
# Rounded preconditioned conjugate gradient on stored matrices, in scalar operations

`NLAlib.Krylov.CG.HSPCG.Rounded.Stored.zeroStartRoutine` reads a system matrix and an inverse
preconditioner, each stored as `n * n` words, and a right-hand side, and writes the iterate, the
residual, the preconditioned residual and the direction of rounded preconditioned conjugate
gradient from the zero iterate. Its tree uses scalar operations only: the rounded zero-start
routine on stored data (`NLAlib.Krylov.CG.HSPCG.Rounded.Stored.solveRoutine`, both matrices
isolated operands forwarded to their products), then every vector operation expanded to scalar
loops (`NLAlib.Ops.RoundedScalarBlas.table`).

## Main definitions

* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.solveRoutine`,
  `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.solveSpec`: the routine at the vector level and its
  specification.
* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.zeroStartRoutine`,
  `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.zeroStartSpec`: the routine in scalar operations and its
  specification.
* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.PrefixOutput`: the output claim on a memory, as the
  certificates state it.

## Main results

* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.solveRoutine_meets`: the vector-level routine meets its
  specification.
* `NLAlib.Krylov.CG.HSPCG.Rounded.Stored.zeroStartRoutine_meets`: the routine meets its
  specification.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Krylov.CG.HSPCG.Rounded.Stored

open Ops

variable {M : Machine ℝ} {u E a₀ a₁ p₀ p₁ : ℝ}

/-- The vector-level routine: the rounded zero-start routine with the words of the system matrix
and of the inverse preconditioner, `n * n` each, new isolated leading operands forwarded to their
products. -/
def solveRoutine : Routine RCLikeBlas.Operation CmpTst :=
  (Rounded.zeroStartRoutine (Op := Signature) (Tst := CmpTst)).withData
    [fun d => d.headD 0 * d.headD 0, fun d => d.headD 0 * d.headD 0]
    (StoredContext.table 2 0 1)

/-- The vector-level tree. -/
abbrev blasBody : Stmt RCLikeBlas.Operation CmpTst := solveRoutine.body

/-- The scalar tree: the vector-level tree with every vector operation expanded to scalar loops.
Index variables: `n`, `cap`, then the offsets of `A`, `P`, `b`, `x`, `r`, `z`, `p`. -/
def scalarBody : Stmt ScalarOp CmpTst := blasBody.link RoundedScalarBlas.table

/-- The output claim: the four stored state vectors are a prefix of length at most `cap` of a
rounded preconditioned run for the stored matrices and the word-kernel preconditioner action,
and the residual is zero if the prefix stopped before the cap. -/
def PrefixOutput (hM : StdModel u id M) (hu : 0 ≤ u) (n : ℕ) (rawA rawP : List ℝ)
    (b : Fin n → ℝ) (E : ℝ) (cap : ℕ) (x r z p : ℕ × ℕ) (μ : Mem ℝ) : Prop :=
  ∃ m ≤ cap, ∃ s rho, StoresState id n x r z p s μ ∧
    RunPrefix (StoredOperator.denseMatrix n n rawA) (StoredOperator.denseMatrix n n rawP)
      (StoredContext.oracle hM hu n rawP) b E m s rho ∧ (m < cap → s.r = 0)

/-- A memory whose four output blocks satisfy the output claim satisfies it. -/
theorem PrefixOutput.of_values {hM : StdModel u id M} {hu : 0 ≤ u} {n : ℕ}
    {rawA rawP : List ℝ} {b : Fin n → ℝ} {cap : ℕ} {x r z p : ℕ × ℕ} {μ : Mem ℝ}
    {ys : List (List ℝ)} (hr : μ.readBlocks [x, r, z, p] [n, n, n, n] = some ys)
    (h : PrefixValues (StoredOperator.denseMatrix n n rawA) (StoredOperator.denseMatrix n n rawP)
      (StoredContext.oracle hM hu n rawP) b E cap ys) :
    PrefixOutput hM hu n rawA rawP b E cap x r z p μ := by
  obtain ⟨m, hm, s, rho, ⟨xs, rs, zs, ps, rfl, hs⟩, hrun, hstop⟩ := h
  exact ⟨m, hm, s, rho, ⟨xs, rs, zs, ps, hr, hs⟩, hrun, hstop⟩

/-- The specification of the vector-level routine at order `n`: for symmetric stored matrices
with spectra in the positive windows `[a₀, a₁]` and `[p₀, p₁]`, that of the rounded zero-start
routine at the decoded matrices and the word-kernel preconditioner action. -/
noncomputable def solveSpec (hM : StdModel u id M) (hu : 0 ≤ u) (n : ℕ) (E a₀ a₁ p₀ p₁ : ℝ) :
    Routine.Spec ℝ :=
  .onData 2
    (fun d raws => d.headD 0 = n ∧
      (StoredOperator.denseMatrix n n (raws.getD 0 []))ᵀ =
        StoredOperator.denseMatrix n n (raws.getD 0 []) ∧
      (StoredOperator.denseMatrix n n (raws.getD 1 []))ᵀ =
        StoredOperator.denseMatrix n n (raws.getD 1 []) ∧
      spectrum ℝ (StoredOperator.denseMatrix n n (raws.getD 0 [])) ⊆ Set.Icc a₀ a₁ ∧
      spectrum ℝ (StoredOperator.denseMatrix n n (raws.getD 1 [])) ⊆ Set.Icc p₀ p₁)
    (fun _ raws => Rounded.zeroStartSpec (StoredOperator.denseMatrix n n (raws.getD 0 []))
      (StoredOperator.denseMatrix n n (raws.getD 1 []))
      (StoredContext.oracle hM hu n (raws.getD 1 [])) E a₀ a₁ p₀ p₁)

/-- The vector-level routine meets its specification: it is the rounded zero-start routine on
stored data, and under the interpretation in which each product reads the stored words of its
matrix that routine meets its own specification at the decoded matrices
(`NLAlib.Ops.Routine.Meets.withData`). -/
theorem solveRoutine_meets {J : Interp RCLikeBlas.Operation CmpTst ℝ}
    (hS : IsScalar M J) (hM : StdModel u id M) (hu : 0 ≤ u)
    (hB : IsBlas1 id (Blas.seq.err u) (fun _ => True) J)
    (hDot : J.IsFn .total (Has.inj Blas1Op.dot) (dotSeqFn M) (OutApart (fun _ => True)))
    (hCmp : IsCmp id J) {n : ℕ}
    (hAccuracy : Standard.Accuracy (StoredContext.relativeError u n) u E (Blas.seq.err u) n)
    (ha₀ : 0 < a₀) (hp₀ : 0 < p₀) (hAp : 6 * E * a₁ ≤ a₀) (hPp : 6 * E * p₁ ≤ p₀) :
    solveRoutine.Meets J (solveSpec hM hu n E a₀ a₁ p₀ p₁) := by
  obtain ⟨_, hd, haa, _⟩ := Standard.Scheme.sequential.errors_nonneg hu n
  have hue : u ≤ E := by linarith [hAccuracy.scalar, hAccuracy.nonneg]
  have hde : (Blas.seq.err u).dot n ≤ E := by linarith [hAccuracy.dot, hAccuracy.nonneg]
  refine Routine.Meets.withData _ _
    (fun _ raws => StoredContext.relation M (Blas.seq.err u) u n (raws.getD 0 [])
      (raws.getD 1 []))
    (fun _ => StoredContext.admissible n)
    (fun _ raws => StoredContext.fallback (n := n) J M (raws.getD 0 []) (raws.getD 1 []))
    rfl rfl ?_ ?_
  · intro d ctx m raws hc hr hP
    obtain ⟨a, pm, rfl⟩ := List.length_eq_two.mp hc
    split_reads hr as (rawA, rawP)
    have hA : m.store.readBlock a.1 a.2 (n * n) = some rawA := by
      rw [← hP.1]
      exact hrawA
    have hPm : m.store.readBlock pm.1 pm.2 (n * n) = some rawP := by
      rw [← hP.1]
      exact hrawP
    exact StoredContext.guarded_satisfies hM hu hS hB [a, pm] ⟨0, by simp⟩ ⟨1, by simp⟩
      m.store rawA rawP (fun z hz => List.mem_map_of_mem hz) hA hPm
  · intro d ctx m raws hc hr hP
    obtain ⟨a, pm, rfl⟩ := List.length_eq_two.mp hc
    split_reads hr as (rawA, rawP)
    have hA : m.store.readBlock a.1 a.2 (n * n) = some rawA := by
      rw [← hP.1]
      exact hrawA
    have hPm : m.store.readBlock pm.1 pm.2 (n * n) = some rawP := by
      rw [← hP.1]
      exact hrawP
    obtain ⟨hs, hb', ha', hp', hc⟩ := StoredContext.guarded_laws hM hu hS hB hCmp [a, pm]
      ⟨0, by simp⟩ ⟨1, by simp⟩ m.store rawA rawP (fun z hz => List.mem_map_of_mem hz) hA hPm
    have hdot := StoredContext.guarded_dot (e := Blas.seq.err u) (u := u) hDot
      [a, pm] ⟨0, by simp⟩ ⟨1, by simp⟩ (· ∈ [a, pm].map Prod.fst) m.store n rawA rawP
    exact Rounded.zeroStartRoutine_meets hs hM hb' trivial ha' hp' hdot hc hP.2.1 hP.2.2.1 ha₀ hp₀
      hP.2.2.2.1 hP.2.2.2.2 hu hd haa hAccuracy.matvec hue hde hAccuracy.axpy hAccuracy.small
      hAccuracy.matvec hAp hPp

/-! ### The routine -/

/-- Rounded preconditioned conjugate gradient on stored matrices, in scalar operations: the words
of the two matrices are isolated, the right-hand side is read, and the iterate, the residual, the
preconditioned residual and the direction are written. -/
def zeroStartRoutine : Routine ScalarOp CmpTst :=
  routine% [n, k] (isolated A : n * n, isolated P : n * n, b : n) →
      (x : n, r : n, z : n, p : n) := scalarBody

/-- For symmetric stored matrices with spectra in the positive windows `[a₀, a₁]` and
`[p₀, p₁]`, and a cap within the precision window, the four written blocks are a prefix of the
rounded preconditioned run for the right-hand side read. -/
noncomputable def zeroStartSpec (hM : StdModel u id M) (hu : 0 ≤ u) (n : ℕ) (E a₀ a₁ p₀ p₁ : ℝ) :
    Routine.Spec ℝ :=
  spec% [m, cap] (rawA, rawP, bs) → (xs, rs, zs, ps)
    requires m = n ∧
      (StoredOperator.denseMatrix n n rawA)ᵀ = StoredOperator.denseMatrix n n rawA ∧
      (StoredOperator.denseMatrix n n rawP)ᵀ = StoredOperator.denseMatrix n n rawP ∧
      spectrum ℝ (StoredOperator.denseMatrix n n rawA) ⊆ Set.Icc a₀ a₁ ∧
      spectrum ℝ (StoredOperator.denseMatrix n n rawP) ⊆ Set.Icc p₀ p₁ ∧
      E * (1024 * (a₁ / a₀) * (p₁ / p₀)) ^ (cap + 1) ≤ 1 / 2
    ensures PrefixValues (StoredOperator.denseMatrix n n rawA)
      (StoredOperator.denseMatrix n n rawP) (StoredContext.oracle hM hu n rawP) (decv id n bs) E
      cap [xs, rs, zs, ps]

/-- Rounded preconditioned conjugate gradient on stored matrices meets its specification under
the standard model of scalar arithmetic and exact comparisons: the judgment of the vector-level
routine, `solveRoutine_meets`, transferred through the linking of its vector operations to scalar
loops. -/
theorem zeroStartRoutine_meets {I : Interp ScalarOp CmpTst ℝ}
    (hS : IsScalar M I) (hCmp : IsCmp id I) (hM : StdModel u id M) (hu : 0 ≤ u) {n : ℕ}
    (hAccuracy : Standard.Accuracy (StoredContext.relativeError u n) u E (Blas.seq.err u) n)
    (ha₀ : 0 < a₀) (hp₀ : 0 < p₀) (hAp : 6 * E * a₁ ≤ a₀) (hPp : 6 * E * p₁ ≤ p₀) :
    zeroStartRoutine.Meets I (zeroStartSpec hM hu n E a₀ a₁ p₀ p₁) := by
  routine_intro [n', cap] (a, pm, b, x, r, z, p) reads (rawA, rawP, bs)
  obtain ⟨hn, hAT, hPT, hsA, hsP, hwindow⟩ := hpre
  obtain rfl : n = n' := hn.symm
  obtain ⟨hS', hB⟩ := RoundedScalarBlas.laws hM hu hS
  have hD := RoundedScalarBlas.isFn_dot hS
  have h := (solveRoutine_meets hS' hM hu hB hD hCmp hAccuracy ha₀ hp₀ hAp hPp)
    [n, cap] [a, pm, b, x, r, z, p] τ m [rawA, rawP, bs] rfl rfl hlive (by routine_sep)
    (by reads) ⟨⟨rfl, hAT, hPT, hsA, hsP⟩, rfl, hwindow⟩ hrooms
  refine (Writes.link I RoundedScalarBlas.table h).mono le_rfl ?_
  rintro m' - ⟨hpos, ys, hys, hpost⟩
  refine ⟨hpos, ys, hys, ?_⟩
  split_reads hys as (xs, rs, zs, ps)
  exact hpost

end NLAlib.Krylov.CG.HSPCG.Rounded.Stored
