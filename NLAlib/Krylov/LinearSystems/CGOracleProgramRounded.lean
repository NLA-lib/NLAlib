/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramRounded
public import NLAlib.Krylov.LinearSystems.CGOracleProgramRoundedInitialization
public import NLAlib.Krylov.LinearSystems.CGOracleProgramStaticCost

/-!
# Rounded execution of the fixed oracle CG program

The external matvec accuracy contract supplies the backend of the common scalar, prefix
and loop analysis. The actual oracle tree, its guards and its resource bounds are retained.

## Main results

* `NLAlib.CGOracleImplementation.exec_rounded_compiled`: actual rounded oracle execution.
-/

@[expose] public section

namespace NLAlib.CGOracleImplementation

open Computation Computation.Builder CGImplementation
open scoped Matrix

variable {P ι K : Type} [DecidableEq P] {u : P → ℝ} {dec : P → K → ℝ}

/-- The actual oracle initializer composes with its loop without escaping allocations. -/
theorem executionComposable_rounded_initialization (I : Interp P ι K (OpCount P ι))
    (tag : P) (N : ℕ) :
    ExecutionComposable I (do
      ins (.lit tag ⟨7, 6⟩ 0); ins (.lit tag ⟨7, 7⟩ 1)
      ins (.un tag .neg ⟨7, 8⟩ ⟨7, 7⟩); ins (.copy tag ⟨4, 0⟩ ⟨7, 6⟩)
      forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
      copyv tag 0 0 2 0 (.const N); copyv tag 0 0 3 0 (.const N)
      dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)
      ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ())) := by
  exact (executionComposable_single I (fun _ => rfl)).bind
    ((executionComposable_single I (fun _ => rfl)).bind
    ((executionComposable_single I (fun _ => rfl)).bind
    ((executionComposable_single I (fun _ => rfl)).bind
    ((executionComposable_single I (fun _ => rfl)).bind
    ((executionComposable_single I (fun _ => rfl)).bind
    ((executionComposable_single I (fun _ => rfl)).bind
    ((executionComposable_single I (fun _ => rfl)).bind
      (executionComposable_single I (fun _ => rfl)))))))))

/-- Complete actual preallocated execution follows from the unbounded scalar relative-error
contract, exact addition of zero, an independently certified successful and accurate matvec
oracle, and the stated spectral precision and iteration-horizon bounds. The result distinguishes
zero active steps from a positive existing CGRun tied to the actual decoded final vectors
and cached residual. -/
theorem exec_rounded_preallocated (I : Interp P ι K (OpCount P ι)) (tag : P) (o : ι)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hu : u tag < 1) (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → K)
    (hshape : st.store.shape = workspaceShape tag N false)
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hmv : IsMatvecErr I o dec tag A (cgImplementationRoundoffBound N (u tag) * specNorm A))
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (horizon : CGPrecisionHorizon q (cgImplementationRoundoffBound N (u tag)) (a' / a)) :
    ∃ (out : St P K (OpCount P ι)) (ν flag : ℝ),
      exec I ((do
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
      stmt (.apply o tag 6 0 3 0 1)
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
          (if (fun i => dec tag (b i)) = 0 then flag else 0) flag out.store false ∨
      ∃ (m : ℕ) (R : CGRun N m), m ≤ q ∧ R.A = A ∧ R.b = (fun i => dec tag (b i)) ∧
        R.ε = cgImplementationRoundoffBound N (u tag) ∧
        StoreContext tag dec N A (fun i => dec tag (b i)) ⟨R.x m, R.r m, R.p m⟩ (R.ν m)
          (if R.r m = 0 then flag else 0) flag out.store false ∧ (m < q → R.r m = 0)) := by
  classical
  obtain ⟨predot, cached, header, ν, θ, flag, einit, sh, hr, edot, origin, ctx,
      _, _, _, hzero, hflag, herr⟩ := exec_rounded_initialization I tag hsem hz hu hc
        st N b A hshape hb hsmall
  have ctx' : StoreContext tag dec N A (fun i => dec tag (b i))
      ⟨0, fun i => dec tag (b i), fun i => dec tag (b i)⟩ ν
      (if ν = 0 then flag else 0) flag header.store false := by simpa only [hzero] using ctx
  obtain ⟨out, eloop, hout⟩ := exec_rounded_initialized_loop
    (hmv := hmv.isMatvecRoutine 3 6 0 0 (by omega)) I tag hsem hz predot cached header
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

/-- The actual registered tree executes and returns the release of an explicitly witnessed
workspace state. The witness contains either zero active steps or an existing positive-length
CGRun tied to the actual decoded final vectors, residual cache and termination status. -/
theorem exec_rounded_scoped (I : Interp P ι K (OpCount P ι)) (tag : P) (o : ι)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hu : u tag < 1) (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → K)
    (hshape : st.store.shape = #[(tag, N), (tag, N), (tag, N), (tag, N), (tag, 1)])
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hmv : IsMatvecErr I o dec tag A (cgImplementationRoundoffBound N (u tag) * specNorm A))
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (horizon : CGPrecisionHorizon q (cgImplementationRoundoffBound N (u tag)) (a' / a)) :
    ∃ (workout out : St P K (OpCount P ι)) (ν flag : ℝ),
      (cgOracleProg.compiled tag o).exec I N ![q] st = some out ∧
      out = releaseWorkspace tag 0 N (I.width tag) workout ∧
      0 < flag ∧ |flag - 1| ≤ u tag ∧
      ((q = 0 ∨ (fun i => dec tag (b i)) = 0) ∧
        StoreContext tag dec N A (fun i => dec tag (b i))
          ⟨0, fun i => dec tag (b i), fun i => dec tag (b i)⟩ ν
          (if (fun i => dec tag (b i)) = 0 then flag else 0) flag workout.store false ∨
      ∃ (m : ℕ) (R : CGRun N m), m ≤ q ∧ R.A = A ∧ R.b = (fun i => dec tag (b i)) ∧
        R.ε = cgImplementationRoundoffBound N (u tag) ∧
        StoreContext tag dec N A (fun i => dec tag (b i)) ⟨R.x m, R.r m, R.p m⟩ (R.ν m)
          (if R.r m = 0 then flag else 0) flag workout.store false ∧ (m < q → R.r m = 0)) := by
  have hsize : st.store.size = 5 := by
    simpa [Store.shape] using congrArg Array.size hshape
  let workspace := (((st.allocate tag 0 (I.width tag)).allocate tag N
    (I.width tag)).allocate tag 9 (I.width tag))
  obtain ⟨workout, ν, flag, hpre, hflag, herr, hpost⟩ := exec_rounded_preallocated I tag o
    hsem hz hu hc workspace N q A b (by simp only [workspace, St.shape_allocate, hshape]; rfl)
      (fun i => by
        rw [St.read_allocate_of_lt, St.read_allocate_of_lt, St.read_allocate_of_lt]
        · exact hb i
        all_goals simp [St.allocate, hsize])
      hmv hsmall hA ha hspec horizon
  let body (_A s scalars : ℕ) : Builder P ι ℕ ℕ Unit := do
    ins (.lit tag ⟨scalars, 6⟩ 0)
    ins (.lit tag ⟨scalars, 7⟩ 1)
    ins (.un tag .neg ⟨scalars, 8⟩ ⟨scalars, 7⟩)
    ins (.copy tag ⟨4, 0⟩ ⟨scalars, 6⟩)
    forRange (.const N) fun i => ins (.lit tag ⟨1, .var i⟩ 0)
    copyv tag 0 0 2 0 (.const N)
    copyv tag 0 0 3 0 (.const N)
    dot tag ⟨scalars, 0⟩ 2 0 2 0 (.const N)
    ifThenElse tag .eq ⟨scalars, 0⟩ ⟨scalars, 6⟩
      (ins (.copy tag ⟨4, 0⟩ ⟨scalars, 7⟩)) (pure ())
    forRange (.const q) fun _ => ifThenElse tag .eq ⟨4, 0⟩ ⟨scalars, 6⟩
      (do
        stmt (.apply o tag s 0 3 0 1)
        dot tag ⟨scalars, 2⟩ 3 0 s 0 (.const N)
        ifThenElse tag .lt ⟨scalars, 6⟩ ⟨scalars, 2⟩ (do
          ins (.bin tag .div ⟨scalars, 3⟩ ⟨scalars, 0⟩ ⟨scalars, 2⟩)
          axpy tag ⟨scalars, 3⟩ 3 0 1 0 (.const N)
          ins (.un tag .neg ⟨scalars, 5⟩ ⟨scalars, 3⟩)
          axpy tag ⟨scalars, 5⟩ s 0 2 0 (.const N)
          dot tag ⟨scalars, 1⟩ 2 0 2 0 (.const N)
          ins (.bin tag .div ⟨scalars, 4⟩ ⟨scalars, 1⟩ ⟨scalars, 0⟩)
          forRange (.const N) fun i => do
            ins (.bin tag .mul ⟨scalars, 2⟩ ⟨scalars, 4⟩ ⟨3, .var i⟩)
            ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨scalars, 2⟩)
          ins (.copy tag ⟨scalars, 0⟩ ⟨scalars, 1⟩)
          ifThenElse tag .eq ⟨scalars, 0⟩ ⟨scalars, 6⟩
            (ins (.copy tag ⟨4, 0⟩ ⟨scalars, 7⟩)) (pure ()))
          (ins (.copy tag ⟨4, 0⟩ ⟨scalars, 8⟩))) (pure ())
  have hbody : exec I (body 5 6 7).run workspace = some workout := by
    simpa only [body, bind_assoc] using hpre
  refine ⟨workout, releaseWorkspace tag 0 N (I.width tag) workout, ν, flag,
    ?_, rfl, hflag, herr, hpost⟩
  rw [Prog.exec_eq_exec_toStmt, cgOracleProg.toStmt_compiled]
  exact exec_scope_of_exec_eq_some I tag (0 : IExp ℕ) N st workout hsize body hbody

/-- The actual oracle CG program executes under an unbounded scalar relative-error
contract at unit roundoff $u$, exact addition of zero, and independent matvec error
$\eta\|\mathbf{A}\|_2\|\mathbf{x}\|_2$. Choose an analysis allowance $v\ge u$ and
$\eta\le\varepsilon$, with <!-- value cgImplementationRoundoffBound N v -->
$\varepsilon=4N^2v$. Assume $v<1$, $\varepsilon\le1/100$, symmetric decoded $\mathbf{A}$
with spectrum in $[a,a']$, $a>0$, and
$q^2\sqrt q\varepsilon(a'/a)^2\le10^{-5}$. The actual decoded iterate, residual and direction
belong to the existing CGRun model. Zero dimension/input/budget and terminal skipping are
included, with retained input, legal status and the original oracle resource bounds.
Backend storage and arithmetic are excluded from those bounds. -/
theorem exec_rounded_compiled (I : Interp P ι K (OpCount P ι)) (tag : P) (o : ι)
    (v : P → ℝ) (hv : ∀ p, u p ≤ v p) (η : ℝ)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hu : v tag < 1) (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → K)
    (hshape : st.store.shape = #[(tag, N), (tag, N), (tag, N), (tag, N), (tag, 1)])
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hmv : IsMatvecErr I o dec tag A (η * specNorm A))
    (hη : η ≤ cgImplementationRoundoffBound N (v tag))
    (hsmall : cgImplementationRoundoffBound N (v tag) ≤ 1 / 100)
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (horizon : CGPrecisionHorizon q (cgImplementationRoundoffBound N (v tag)) (a' / a)) :
    ∃ (out : St P K (OpCount P ι)) (flag : ℝ),
      (cgOracleProg.compiled tag o).exec I N ![q] st = some out ∧
      out.store.shape = #[(tag, N), (tag, N), (tag, N), (tag, N), (tag, 1)] ∧
      0 < flag ∧ |flag - 1| ≤ v tag ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 0 i = some w ∧ dec tag w = dec tag (b i)) ∧
      (StaticCost.mk (cgOracleCount tag o N q) (fun p => if p = tag then N + 10 else 0)
        ((N + 10) * I.width tag)).Bounds st out ∧
      (((q = 0 ∨ (fun i => dec tag (b i)) = 0) ∧
        (∀ i : Fin N, ∃ wx wr wp, out.store.read tag 1 i = some wx ∧ dec tag wx = 0 ∧
          out.store.read tag 2 i = some wr ∧ dec tag wr = dec tag (b i) ∧
          out.store.read tag 3 i = some wp ∧ dec tag wp = dec tag (b i)) ∧
        (∃ w, out.store.read tag 4 0 = some w ∧
          dec tag w = if (fun i => dec tag (b i)) = 0 then flag else 0)) ∨
      ∃ (m : ℕ) (R : CGRun N m), m ≤ q ∧ R.A = A ∧ R.b = (fun i => dec tag (b i)) ∧
        R.ε = cgImplementationRoundoffBound N (v tag) ∧
        (∀ i : Fin N, ∃ wx wr wp, out.store.read tag 1 i = some wx ∧ dec tag wx = R.x m i ∧
          out.store.read tag 2 i = some wr ∧ dec tag wr = R.r m i ∧
          out.store.read tag 3 i = some wp ∧ dec tag wp = R.p m i) ∧
        (∃ w, out.store.read tag 4 0 = some w ∧ dec tag w = if R.r m = 0 then flag else 0) ∧
        (m < q → R.r m = 0)) := by
  have hsemv := hsem.mono hv
  have hmvv := hmv.mono (mul_le_mul_of_nonneg_right hη (specNorm_nonneg A))
  obtain ⟨workout, out, ν, flag, hrun, hrelease, hflag, herr, hpost⟩ :=
    exec_rounded_scoped I tag o hsemv hz hu hc st N q A b hshape hb hmvv
      hsmall hA ha hspec horizon
  subst out
  have hcost := cgOracleProg.bounds_of_exec_eq_some I tag o N q hc hrun
  rcases hpost with ⟨hstop, hctx⟩ | ⟨m, R, hm, hRA, hRb, hRε, hctx, hstop⟩
  · obtain ⟨shape, input, vectors, status⟩ :=
      decoded_release_context tag N (I.width tag) workout A _ _ ν _ flag hctx
    exact ⟨_, flag, hrun, shape, hflag, herr, input, hcost, Or.inl ⟨hstop, vectors, status⟩⟩
  · obtain ⟨shape, input, vectors, status⟩ :=
      decoded_release_context tag N (I.width tag) workout A _ _ (R.ν m) _ flag hctx
    exact ⟨_, flag, hrun, shape, hflag, herr, input, hcost,
      Or.inr ⟨m, R, hm, hRA, hRb, hRε, vectors, status, hstop⟩⟩

end NLAlib.CGOracleImplementation
