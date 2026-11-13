/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramRoundedHorizon

/-!
# The complete rounded preallocated CG program

The actual canonical initializer and requested guarded loop are composed without assuming
an initialized numerical state or local error bounds. The matrix and right-hand side are
the decodings of actual stored ROM/input words. Empty dimension, zero input and zero
iteration budget execute separately, and never create a zero-length CGRun.

## Main results

* `NLAlib.CGImplementation.exec_rounded_preallocated`: complete workspace execution.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation Computation.Builder
open scoped Matrix

variable {P ι K : Type} [DecidableEq P] {u : P → ℝ} {dec : P → K → ℝ}
    {storedMatrix : Bool} {mv : Builder P ι ℕ ℕ Unit}

/-- The actual initializer emits a certified composable prefix. This follows solely from
its existing statement-emitting atoms and certified composition, not arbitrary builders. -/
theorem executionComposable_rounded_initialization (I : Interp P ι K (OpCount P ι))
    (tag : P) (N : ℕ) :
    ExecutionComposable I (do
        forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
        ins (.lit tag ⟨7, 6⟩ 0)
        ins (.lit tag ⟨7, 7⟩ 1)
        ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
        ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
        forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
        copyv tag 0 0 2 0 (.const N)
        copyv tag 0 0 3 0 (.const N)
        dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
        ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
          (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())) := by
  change ExecutionComposable I ((do
    forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
    ins (.lit tag ⟨7, 6⟩ 0); ins (.lit tag ⟨7, 7⟩ 1)
    ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩); ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)) >>= fun _ => (do
      forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (.const N); copyv tag 0 0 3 0 (.const N)) >>= fun _ => (do
        dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
        ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
          (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())))
  exact (executionComposable_rounded_preload I tag N).bind
    ((executionComposable_rounded_vectors I tag N).bind
    ((executionComposable_single I (b := dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)) (fun _ => rfl)).bind
      (executionComposable_single I (fun _ => rfl))))

/-- The requested loop executes from the actual initializer output, with input-only
spectral precision. Zero budget and zero dimension require no next-curvature argument. -/
theorem exec_rounded_initialized_loop (I : Interp P ι K (OpCount P ι)) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (predot cached header : St P K (OpCount P ι)) (N q : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (ν flag : ℝ)
    (hctx : StoreContext tag dec N A b ⟨0, b, b⟩ ν (if ν = 0 then flag else 0) flag
      header.store storedMatrix)
    (horigin : header.store.read tag 7 0 = cached.store.read tag 7 0)
    (hpreShape : predot.store.shape = workspaceShape tag N storedMatrix)
    (hpreR : ∀ i : Fin N, ∃ w, predot.store.read tag 2 i = some w ∧ dec tag w = b i)
    (hinit : exec I (dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)).run predot = some cached)
    (hflag : 0 < flag) (hzero : ν = 0 ↔ b = 0)
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (horizon : (q : ℝ) ^ 2 * Real.sqrt q * cgImplementationRoundoffBound N (u tag) *
      (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hmv : IsMatvecRoutine I dec tag A (cgImplementationRoundoffBound N (u tag) *
      specNorm A) (fun store => if storedMatrix then HoldsDecoded store dec tag 5 0 A
      else True) 3 6 0 0 mv) :
    ∃ out,
      exec I (Builder.forRange (.const q) fun _ => Builder.ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
      (do
      mv
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)
      (Builder.ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
      (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) : Builder P ι ℕ ℕ Unit)
      (pure ())).run header = some out ∧
      RoundedHeader tag dec N A b (cgImplementationRoundoffBound N (u tag)) ν flag
        (cached.store.read tag 7 0) q out.store storedMatrix := by
  classical
  by_cases hq : q = 0
  · subst q
    refine ⟨header, ?_, Or.inl ⟨hctx, horigin, Or.inl rfl⟩⟩
    change exec I (.seq (.loop (.const 0) _) .skip) header = _
    rw [exec_seq_skip, exec_loop]
    rfl
  by_cases hN : N = 0
  · subst N
    have hb : b = 0 := by funext i; exact Fin.elim0 i
    have hν : ν = 0 := hzero.mpr hb
    have hc : StoreContext tag dec 0 A b ⟨0, b, b⟩ ν flag flag header.store storedMatrix := by
      simpa only [if_pos hν] using hctx
    refine ⟨{ header with cnt := header.cnt + q • I.charge (.cmp tag) }, ?_,
      Or.inl ⟨hctx, horigin, Or.inr hν⟩⟩
    exact exec_rounded_stopped_loop I tag hsem header _ 0 q A b _ ν flag flag hc hflag.ne'
  · have hherm : A.IsHermitian := by
      simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
    have hprec := hherm.three_mul_mul_le_of_cgPrecisionHorizon
      (Nat.pos_of_ne_zero hN) (Nat.pos_of_ne_zero hq)
      (cgImplementationRoundoffBound_nonneg N (hsem.nonneg trivial)) ha hspec horizon
    exact exec_rounded_loop (hmv := hmv) I tag hsem hz predot cached header N q A b ν flag
      hctx horigin
      hpreShape hpreR hinit hflag (Nat.pos_of_ne_zero hN) hsmall hA ha hspec hprec horizon

/-- Complete actual preallocated execution follows from scalar arithmetic and input-only
spectral precision. The result distinguishes zero active steps from a positive existing
CGRun tied to the actual decoded final vectors and cached residual. -/
theorem exec_rounded_preallocated (I : Interp P ι K (OpCount P ι)) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hu : u tag < 1) (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → K) (vals : ℕ → K)
    (hshape : st.store.shape = workspaceShape tag N)
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hrom : ∀ i < N * N, I.rom i = some (vals i))
    (hdecode : ∀ i j : Fin N, dec tag (vals (i + N * j)) = A i j)
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (horizon : (q : ℝ) ^ 2 * Real.sqrt q * cgImplementationRoundoffBound N (u tag) *
      (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    ∃ (out : St P K (OpCount P ι)) (ν flag : ℝ),
      exec I ((do
        forRange (IExp.const N * IExp.const N) fun i => stmt (.rom tag ⟨5, .var i⟩ (.var i))
        ins (.lit tag ⟨7, 6⟩ 0)
        ins (.lit tag ⟨7, 7⟩ 1)
        ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩)
        ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
        forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
        copyv tag 0 0 2 0 (.const N)
        copyv tag 0 0 3 0 (.const N)
        dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
        ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
          (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())) >>= fun _ =>
      (Builder.forRange (.const q) fun _ =>
      Builder.ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
      (do
      gemv tag (.const N) (.const N) 5 0 3 0 6 0
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)
      (Builder.ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
      (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) : Builder P ι ℕ ℕ Unit)
      (pure ()))).run st = some out ∧
      0 < flag ∧ |flag - 1| ≤ u tag ∧
      ((q = 0 ∨ (fun i => dec tag (b i)) = 0) ∧
        StoreContext tag dec N A (fun i => dec tag (b i))
          ⟨0, fun i => dec tag (b i), fun i => dec tag (b i)⟩ ν
          (if (fun i => dec tag (b i)) = 0 then flag else 0) flag out.store ∨
      ∃ (m : ℕ) (R : CGRun N m), m ≤ q ∧ R.A = A ∧ R.b = (fun i => dec tag (b i)) ∧
        R.ε = cgImplementationRoundoffBound N (u tag) ∧
        StoreContext tag dec N A (fun i => dec tag (b i)) ⟨R.x m, R.r m, R.p m⟩ (R.ν m)
          (if R.r m = 0 then flag else 0) flag out.store ∧ (m < q → R.r m = 0)) := by
  classical
  have hmat : (fun i j : Fin N => dec tag (vals (i + N * j))) = A := by
    funext i j
    exact hdecode i j
  obtain ⟨predot, cached, header, ν, θ, flag, einit, sh, hr, edot, origin, ctx,
      _, _, _, hzero, hflag, herr⟩ := exec_rounded_initialization I tag hsem hz hu hc
        st N b vals hshape hb hrom hsmall
  rw [hmat] at ctx
  have ctx' : StoreContext tag dec N A (fun i => dec tag (b i))
      ⟨0, fun i => dec tag (b i), fun i => dec tag (b i)⟩ ν
      (if ν = 0 then flag else 0) flag header.store := by simpa only [hzero] using ctx
  obtain ⟨out, eloop, hout⟩ := exec_rounded_initialized_loop
    (hmv := isMatvecRoutine_dense I tag hsem hz N A hsmall) I tag hsem hz predot cached header
    N q A (fun i => dec tag (b i)) ν flag ctx' origin sh hr edot hflag hzero
      hsmall hA ha hspec horizon
  refine ⟨out, ν, flag, ?_, hflag, herr, ?_⟩
  · rw [executionComposable_rounded_initialization I tag N, einit, Option.bind_some]
    exact eloop
  · rcases hout with ⟨hctx, _, hstop⟩ | ⟨m, R, hm, hRA, hRb, hRε, hctx, hstop⟩
    · refine Or.inl ⟨hstop.imp id hzero.mp, ?_⟩
      simpa only [hzero] using hctx
    · refine Or.inr ⟨m, R, hm, hRA, hRb, hRε, ?_, fun hlt => ?_⟩
      · simpa only [R.ν_eq_zero_iff le_rfl] using hctx
      · exact (R.ν_eq_zero_iff le_rfl).mp (hstop hlt)

end NLAlib.CGImplementation
