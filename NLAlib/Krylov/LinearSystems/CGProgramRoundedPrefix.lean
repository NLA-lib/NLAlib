/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramRoundedInitialization

/-!
# Extending an extracted rounded CG prefix

The next run record appends defects already extracted from an actual canonical step.
Existing fields below the endpoint are retained. This is bookkeeping for `CGRun`, not
an alternate arithmetic or iteration model.

## Main results

* `NLAlib.CGImplementation.cgRun_succ_of_active_header`: extend an actual execution prefix.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open scoped Matrix

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {u : P → ℝ} {dec : P → K → ℝ} {storedMatrix : Bool}
  {mv : Computation.Builder P ι ℕ ℕ Unit}

open Computation

/-- An actual active header executes the complete next canonical step and extends its
previously extracted run. Positive curvature follows from spectral input precision and a
nonzero decoded direction; all new defects are conclusions of primitive execution. -/
theorem cgRun_succ_of_active_header (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K C) {N k : ℕ} (R : CGRun N k) (flag : ℝ)
    (h : StoreContext tag dec N R.A R.b ⟨R.x k, R.r k, R.p k⟩ (R.ν k) 0 flag
      st.store storedMatrix)
    (hε : R.ε = cgImplementationRoundoffBound N (u tag)) (hνpos : 0 < R.ν k)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ R.A ⊆ Set.Icc a a')
    (hprec : 3 * cgImplementationRoundoffBound N (u tag) * a' ≤ a) (hp : R.p k ≠ 0)
    (hmv : IsMatvecRoutine I dec tag R.A (cgImplementationRoundoffBound N (u tag) *
      specNorm R.A) (fun store => if storedMatrix then HoldsDecoded store dec tag 5 0 R.A
      else True) 3 6 0 0 mv) :
    ∃ (prestate out : St P K C) (S : CGRun N (k + 1)),
      exec I (Builder.ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
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
      (pure ())).run st = some out ∧
      S.A = R.A ∧ S.b = R.b ∧ S.ε = R.ε ∧
      StoreContext tag dec N S.A S.b ⟨S.x (k + 1), S.r (k + 1), S.p (k + 1)⟩ (S.ν (k + 1))
        (if S.ν (k + 1) = 0 then flag else 0) flag
        out.store storedMatrix ∧
      (∀ j ≤ k, S.x j = R.x j ∧ S.r j = R.r j ∧ S.p j = R.p j ∧ S.ν j = R.ν j) ∧
      (∀ i : Fin N, ∃ w, prestate.store.read tag 6 i = some w ∧ dec tag w = S.s k i) ∧
      (∃ w, prestate.store.read tag 7 2 = some w ∧ dec tag w = S.μ k) ∧
      (∃ w, out.store.read tag 7 3 = some w ∧ dec tag w = S.γ k) ∧
      (∃ w, out.store.read tag 7 4 = some w ∧ dec tag w = S.δ k) := by
  obtain ⟨prestate, out, next, sv, μ, ν, θ, γ, eγ, δ, eδ, _, hrun, hctx,
      hs, hμ, hμpos, hes, heμ, hνeq, hθ, _, _, hγeq, heγ, _, hδeq, heδ,
      hex, her, hep, hγ, hδ⟩ := exec_rounded_positive_step (hmv := hmv) I tag hsem hz st N R.A R.b
        ⟨R.x k, R.r k, R.p k⟩ (R.ν k) flag h hνpos hN hsmall R.transpose_A ha hspec hprec hp
  rw [← hε] at hes heμ hθ heγ heδ hex her hep
  obtain ⟨S, hSA, hSb, hSe, hSx, hSr, hSp, hSν, _, hSs, hSμ, hSγ, hSδ, _⟩ :=
    R.exists_extend next sv ν θ μ γ eγ δ eδ hνpos hμpos hνeq hθ hes heμ
      hγeq heγ hδeq heδ hex her hep
  refine ⟨prestate, out, S, hrun, hSA, hSb, hSe, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hSA, hSb, hSx, hSr, hSp, hSν, Function.update_self] using hctx
  · intro j hj
    simp only [hSx, hSr, hSp, hSν,
      Function.update_of_ne (show j ≠ k + 1 by omega), and_self]
  · simpa only [hSs, Function.update_self] using hs
  · simpa only [hSμ, Function.update_self] using hμ
  · simpa only [hSγ, Function.update_self] using hγ
  · simpa only [hSδ, Function.update_self] using hδ

end NLAlib.CGImplementation
