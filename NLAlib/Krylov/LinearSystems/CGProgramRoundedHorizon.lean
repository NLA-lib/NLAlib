/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramRoundedPrefix
public import NLAlib.Krylov.FinitePrecision.CGRunSpectrum

/-!
# Input-only continuation of actual rounded CG execution

An induction predicate records actual stored headers and an extracted existing CGRun after
positive active-step counts. Zero completed steps are represented by the initialized store.
Terminal residuals are retained by actual skipped iterations. This predicate is bookkeeping
for program execution, not an additional numerical iteration model.

## Main results

* `NLAlib.CGImplementation.exec_rounded_loop`: actual execution through the input-only horizon.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation
open scoped Matrix

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {u : P → ℝ} {dec : P → K → ℝ} {storedMatrix : Bool}
  {mv : Builder P ι ℕ ℕ Unit}

/-- A loop-header induction predicate, using only the existing stored context and CGRun.
The initial branch includes cached-word provenance; the other branch counts actual active
steps. A strictly shorter active prefix has already reached a zero terminal cache. -/
def RoundedHeader (tag : P) (dec : P → K → ℝ) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (ε ν flag : ℝ) (cache : Option K)
    (j : ℕ) (store : Store P K) (storedMatrix : Bool := true) : Prop :=
  (StoreContext tag dec N A b ⟨0, b, b⟩ ν (if ν = 0 then flag else 0) flag store storedMatrix ∧
    store.read tag 7 0 = cache ∧ (j = 0 ∨ ν = 0)) ∨
  ∃ (m : ℕ) (R : CGRun N m), m ≤ j ∧ R.A = A ∧ R.b = b ∧ R.ε = ε ∧
    StoreContext tag dec N A b ⟨R.x m, R.r m, R.p m⟩ (R.ν m)
      (if R.ν m = 0 then flag else 0) flag store storedMatrix ∧ (m < j → R.ν m = 0)

/-- A stopped header actually executes its skip branch. It preserves every stored word;
only the comparison charge changes. The skipped body is arbitrary and is never executed. -/
theorem exec_rounded_inactive_header (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C)
    (body : Builder P ι ℕ ℕ Unit) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status flag : ℝ)
    (h : StoreContext tag dec N A b v ν status flag
      st.store storedMatrix) (hne : status ≠ 0) :
    exec I (Builder.ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩ body (pure ())).run st =
      some { st with cnt := st.cnt + I.charge (.cmp tag) } := by
  classical
  obtain ⟨ws, hs, hds⟩ := h.statusValue
  obtain ⟨wz, hz, hdz⟩ := h.zero
  have hc : I.sem.cmp tag .eq ws wz = some false := by
    simpa only [hds, hdz, hne, decide_false] using hsem.cmp_eq tag ws wz
  have hcmp : cmpStep I tag .eq ⟨4, 0⟩ ⟨7, 6⟩ st =
      some (false, { st with cnt := st.cnt + I.charge (.cmp tag) }) := by
    simp only [cmpStep, IExp.eval_ofNat, hs, hz, Option.bind_some, hc, Option.map_some]
  change exec I (.seq (.ite tag .eq ⟨4, 0⟩ ⟨7, 6⟩ _ _) .skip) st = _
  rw [exec_seq_skip, exec_ite, hcmp, Option.bind_some]
  exact exec_skip I _

/-- The extracted positive-length branch either skips its terminal state or executes a
new positive-curvature step. All active-step counts remain tied to the loop prefix. -/
theorem exec_rounded_run_header (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K C) {N m : ℕ} (q j : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (ν flag : ℝ) (cache : Option K) (R : CGRun N m)
    (hRA : R.A = A) (hRb : R.b = b) (hRε : R.ε = cgImplementationRoundoffBound N (u tag))
    (hmj : m ≤ j) (hjq : j < q)
    (hctx : StoreContext tag dec N A b ⟨R.x m, R.r m, R.p m⟩ (R.ν m)
      (if R.ν m = 0 then flag else 0) flag
      st.store storedMatrix)
    (hfreeze : m < j → R.ν m = 0) (hflag : 0 < flag)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hprec : 3 * cgImplementationRoundoffBound N (u tag) * a' ≤ a)
    (horizon : CGPrecisionHorizon q (cgImplementationRoundoffBound N (u tag)) (a' / a))
    (hmv : IsMatvecRoutine I dec tag A (cgImplementationRoundoffBound N (u tag) *
      specNorm A) (fun store => if storedMatrix then HoldsDecoded store dec tag 5 0 A
      else True) 3 6 0 0 mv) :
    ∃ out,
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
      RoundedHeader tag dec N A b (cgImplementationRoundoffBound N (u tag)) ν flag cache
        (j + 1) out.store storedMatrix := by
  classical
  by_cases hzero : R.ν m = 0
  · have hcflag : StoreContext tag dec N A b ⟨R.x m, R.r m, R.p m⟩ (R.ν m) flag flag
        st.store storedMatrix := by simpa only [if_pos hzero] using hctx
    refine ⟨{ st with cnt := st.cnt + I.charge (.cmp tag) }, ?_, Or.inr ?_⟩
    · exact exec_rounded_inactive_header I tag hsem st _ N A b _ _ flag flag hcflag hflag.ne'
    · exact ⟨m, R, by omega, hRA, hRb, hRε, hctx, fun _ => hzero⟩
  · have hmj' : m = j := by
      exact le_antisymm hmj (le_of_not_gt (fun hlt => hzero (hfreeze hlt)))
    have hs : spectrum ℝ R.A ⊆ Set.Icc a a' := by simpa only [hRA] using hspec
    have hsm : CGPrecisionHorizon m R.ε (a' / a) := by
      rw [hRε]
      have hmq : m ≤ q := hmj.trans hjq.le
      have hε : 0 ≤ cgImplementationRoundoffBound N (u tag) :=
        cgImplementationRoundoffBound_nonneg N (hsem.nonneg trivial)
      exact horizon.mono hε hmq
    have hr : R.r m ≠ 0 := fun hr => hzero ((R.ν_eq_zero_iff le_rfl).mpr hr)
    have hp := R.p_ne_zero_of_r_ne_zero ha hs hsm hr
    have hn : 0 ≤ R.ν m := by
      rw [R.ν_eq m le_rfl]
      exact mul_nonneg (sq_nonneg _) (R.one_add_θ_pos le_rfl).le
    have hνpos : 0 < R.ν m := lt_of_le_of_ne hn (Ne.symm hzero)
    have hc : StoreContext tag dec N R.A R.b ⟨R.x m, R.r m, R.p m⟩ (R.ν m) 0 flag
        st.store storedMatrix := by simpa only [hRA, hRb, if_neg hzero] using hctx
    obtain ⟨prestate, out, S, hrun, hSA, hSb, hSε, hnext, _⟩ :=
      cgRun_succ_of_active_header (hmv := by simpa only [hRA] using hmv) I tag hsem hz st R
        flag hc hRε
        hνpos hN hsmall ha hs hprec hp
    refine ⟨out, hrun, Or.inr ⟨m + 1, S, by omega, hSA.trans hRA, hSb.trans hRb,
      hSε.trans hRε, ?_, ?_⟩⟩
    · simpa only [hSA, hSb, hRA, hRb] using hnext
    · intro hlt
      omega

/-- The zero-active-step branch either preserves a zero initial residual or executes the
first canonical active step. The initial self-dot provenance derives the cached error. -/
theorem exec_rounded_initial_header (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (predot cached st : St P K C) (N j : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (ν flag : ℝ)
    (hctx : StoreContext tag dec N A b ⟨0, b, b⟩ ν (if ν = 0 then flag else 0) flag
      st.store storedMatrix)
    (horigin : st.store.read tag 7 0 = cached.store.read tag 7 0) (hfreeze : j = 0 ∨ ν = 0)
    (hpreShape : predot.store.shape = workspaceShape tag N storedMatrix)
    (hpreR : ∀ i : Fin N, ∃ w, predot.store.read tag 2 i = some w ∧ dec tag w = b i)
    (hinit : exec I (dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)).run predot = some cached)
    (hflag : 0 < flag) (hN : 0 < N)
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hprec : 3 * cgImplementationRoundoffBound N (u tag) * a' ≤ a)
    (hmv : IsMatvecRoutine I dec tag A (cgImplementationRoundoffBound N (u tag) *
      specNorm A) (fun store => if storedMatrix then HoldsDecoded store dec tag 5 0 A
      else True) 3 6 0 0 mv) :
    ∃ out,
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
      RoundedHeader tag dec N A b (cgImplementationRoundoffBound N (u tag)) ν flag
        (cached.store.read tag 7 0) (j + 1) out.store storedMatrix := by
  classical
  by_cases hzero : ν = 0
  · have hcflag : StoreContext tag dec N A b ⟨0, b, b⟩ ν flag flag st.store storedMatrix := by
      simpa only [if_pos hzero] using hctx
    refine ⟨{ st with cnt := st.cnt + I.charge (.cmp tag) }, ?_, Or.inl ?_⟩
    · exact exec_rounded_inactive_header I tag hsem st _ N A b _ _ flag flag hcflag hflag.ne'
    · exact ⟨hctx, horigin, Or.inr hzero⟩
  · have hc : StoreContext tag dec N A b ⟨0, b, b⟩ ν 0 flag st.store storedMatrix := by
      simpa only [if_neg hzero] using hctx
    obtain ⟨_, _, _, _, hzeroiff⟩ := initial_cache_of_self_dot_execution I tag hsem hz
      predot cached st N b ν hN hsmall hpreShape hpreR hinit horigin hctx.squaredResidual
    have hb : b ≠ 0 := fun hb => hzero (hzeroiff.mpr hb)
    obtain ⟨prestate, out, R, _, hrun, hRA, hRb, hRε, _, hnext, _⟩ :=
      cgRun_one_of_initial_dot_execution (hmv := hmv) I tag hsem hz predot cached st N A b ν flag hc
        hpreShape hpreR hinit horigin hN hsmall hA ha hspec hprec hb
    refine ⟨out, hrun, Or.inr ⟨1, R, by omega, hRA, hRb, hRε, hnext, ?_⟩⟩
    intro hlt
    rcases hfreeze with hj | hz
    · omega
    · exact (hzero hz).elim

/-- The actual q-loop completes under input spectral precision. Each active prefix is an
existing CGRun; zero termination changes subsequent iterations to actual skips. The
initialized zero-step branch remains separate and no CGRun of length zero is constructed. -/
theorem exec_rounded_loop (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (predot cached header : St P K C) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (ν flag : ℝ)
    (hctx : StoreContext tag dec N A b ⟨0, b, b⟩ ν (if ν = 0 then flag else 0) flag
      header.store storedMatrix)
    (horigin : header.store.read tag 7 0 = cached.store.read tag 7 0)
    (hpreShape : predot.store.shape = workspaceShape tag N storedMatrix)
    (hpreR : ∀ i : Fin N, ∃ w, predot.store.read tag 2 i = some w ∧ dec tag w = b i)
    (hinit : exec I (dot tag ⟨7, 0⟩ 2 0 2 0 (.const N)).run predot = some cached)
    (hflag : 0 < flag) (hN : 0 < N)
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (hprec : 3 * cgImplementationRoundoffBound N (u tag) * a' ≤ a)
    (horizon : CGPrecisionHorizon q (cgImplementationRoundoffBound N (u tag)) (a' / a))
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
  let Inv (j : ℕ) (st : St P K C) : Prop := RoundedHeader tag dec N A b
    (cgImplementationRoundoffBound N (u tag)) ν flag (cached.store.read tag 7 0) j
      st.store storedMatrix
  have h0 : Inv 0 header := Or.inl ⟨hctx, horigin, Or.inl rfl⟩
  have hstep : ∀ i < q, ∀ st, Inv i st → ∃ out,
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
      (pure ())).run st = some out ∧ Inv (i + 1) out := by
    intro i hi st hinv
    rcases hinv with ⟨hctx, horigin, hfreeze⟩ | ⟨m, R, hm, hRA, hRb, hRε, hctx, hfreeze⟩
    · exact exec_rounded_initial_header (hmv := hmv) I tag hsem hz predot cached st N i A b ν flag
        hctx
        horigin hfreeze hpreShape hpreR hinit hflag hN hsmall hA ha hspec hprec
    · exact exec_rounded_run_header (hmv := hmv) I tag hsem hz st q i A b ν flag _ R hRA hRb hRε
        hm hi
        hctx hfreeze hflag hN hsmall ha hspec hprec horizon
  obtain ⟨out, hrun, hout⟩ := exists_exec_loop_eq_some_of_forall I (n := .const q) Inv h0 hstep
  refine ⟨out, ?_, hout⟩
  change exec I (.seq (.loop (.const q) _) .skip) header = _
  rw [exec_seq_skip]
  exact hrun

/-- Every requested iteration after a stop really executes the status comparison and
skip. The exact returned record retains the terminal vectors, all words and memory fields. -/
theorem exec_rounded_stopped_loop (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C)
    (body : Builder P ι ℕ ℕ Unit) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (v : CGState ℝ (Fin N)) (ν status flag : ℝ)
    (h : StoreContext tag dec N A b v ν status flag
      st.store storedMatrix) (hne : status ≠ 0) :
    exec I (Builder.forRange (.const q) fun _ => Builder.ifThenElse tag .eq
      ⟨4, 0⟩ ⟨7, 6⟩ body (pure ())).run st =
      some { st with cnt := st.cnt + q • I.charge (.cmp tag) } := by
  let Inv (j : ℕ) (out : St P K C) : Prop :=
    out = { st with cnt := st.cnt + j • I.charge (.cmp tag) }
  have h0 : Inv 0 st := by simp only [Inv, zero_nsmul, add_zero]
  have hstep : ∀ i < q, ∀ out, Inv i out → ∃ out',
      exec I (Builder.ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩ body (pure ())).run out = some out' ∧
        Inv (i + 1) out' := by
    rintro i _ out rfl
    refine ⟨{ st with cnt := st.cnt + (i + 1) • I.charge (.cmp tag) }, ?_, rfl⟩
    have he := exec_rounded_inactive_header I tag hsem
      { st with cnt := st.cnt + i • I.charge (.cmp tag) } body N A b v ν status flag h hne
    simpa only [succ_nsmul, add_assoc] using he
  obtain ⟨out, hrun, hout⟩ := exists_exec_loop_eq_some_of_forall I (n := .const q) Inv h0 hstep
  change exec I (.seq (.loop (.const q) _) .skip) st = _
  rw [exec_seq_skip]
  exact hrun.trans (congrArg some hout)

end NLAlib.CGImplementation
