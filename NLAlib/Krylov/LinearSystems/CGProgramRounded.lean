/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramRoundedWorkspace
public import NLAlib.Krylov.LinearSystems.CGProgramScope
public import NLAlib.Krylov.LinearSystems.CGProgramStaticCost

/-!
# Rounded execution of the registered stored-entry CG tree

The one registered compiled tree actually executes under the standard scalar contract and
an input-only precision horizon. The proof loads the ROM, initializes the actual stores,
constructs the existing CGRun along active prefixes, skips after zero termination and frees
all workspace. Empty dimension, zero input and zero requested budget remain explicit cases.
No numerical target, Result id or alternate program is introduced.
The extracted runs support the backward model and physical energy comparison in
[CGProgramRoundedBackward](CGProgramRoundedBackward.lean).

The sufficient horizon is $q^{5/2}(4N^2u)\kappa^2\le10^{-5}$. Substituting
$u=2^{-53}$ gives at most eight requested steps for $N=100$, $\kappa=100$, and one
for $N=1000$, $\kappa=100$. These illustrate the strength of the sufficient assumptions;
they neither predict CG failure beyond the horizon nor instantiate the theorem at IEEE
binary64. The theorem requires pure relative arithmetic and success at every exact result,
whereas finite binary64 has absolute underflow error and range-limited success.

## Main results

* `NLAlib.CGImplementation.exec_rounded_scoped`: actual execution and workspace witness.
* `NLAlib.CGImplementation.exec_rounded_compiled`: decoded outputs and resources of that run.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation Computation.Builder
open scoped Matrix

variable {P ι K : Type} [DecidableEq P] {u : P → ℝ} {dec : P → K → ℝ}

/-- The actual registered tree executes and returns the release of an explicitly witnessed
workspace state. The witness contains either zero active steps or an existing positive-length
CGRun tied to the actual decoded final vectors, residual cache and termination status. -/
theorem exec_rounded_scoped (I : Interp P ι K (OpCount P ι)) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hu : u tag < 1) (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → K) (vals : ℕ → K)
    (hshape : st.store.shape = #[(tag, N), (tag, N), (tag, N), (tag, N), (tag, 1)])
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hrom : ∀ i < N * N, I.rom i = some (vals i))
    (hdecode : ∀ i j : Fin N, dec tag (vals (i + N * j)) = A i j)
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (horizon : CGPrecisionHorizon q (cgImplementationRoundoffBound N (u tag)) (a' / a)) :
    ∃ (workout out : St P K (OpCount P ι)) (ν flag : ℝ),
      (cgProg.compiled tag).exec I N ![q] st = some out ∧
      out = releaseWorkspace tag (N * N) N (I.width tag) workout ∧
      0 < flag ∧ |flag - 1| ≤ u tag ∧
      ((q = 0 ∨ (fun i => dec tag (b i)) = 0) ∧
        StoreContext tag dec N A (fun i => dec tag (b i))
          ⟨0, fun i => dec tag (b i), fun i => dec tag (b i)⟩ ν
          (if (fun i => dec tag (b i)) = 0 then flag else 0) flag workout.store ∨
      ∃ (m : ℕ) (R : CGRun N m), m ≤ q ∧ R.A = A ∧ R.b = (fun i => dec tag (b i)) ∧
        R.ε = cgImplementationRoundoffBound N (u tag) ∧
        StoreContext tag dec N A (fun i => dec tag (b i)) ⟨R.x m, R.r m, R.p m⟩ (R.ν m)
          (if R.r m = 0 then flag else 0) flag workout.store ∧ (m < q → R.r m = 0)) := by
  have hsize : st.store.size = 5 := by
    simpa [Store.shape] using congrArg Array.size hshape
  let workspace := (((st.allocate tag (N * N) (I.width tag)).allocate tag N
    (I.width tag)).allocate tag 9 (I.width tag))
  obtain ⟨workout, ν, flag, hpre, hflag, herr, hpost⟩ := exec_rounded_preallocated I tag
    hsem hz hu hc workspace N q A b vals (by simp only [workspace, St.shape_allocate, hshape]; rfl)
      (fun i => by
        rw [St.read_allocate_of_lt, St.read_allocate_of_lt, St.read_allocate_of_lt]
        · exact hb i
        all_goals simp [St.allocate, hsize])
      hrom hdecode hsmall hA ha hspec horizon
  let body (A s scalars : ℕ) : Builder P ι ℕ ℕ Unit := do
    forRange ((.const N) * (.const N)) fun i => stmt (.rom tag ⟨A, .var i⟩ (.var i))
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
        gemv tag (.const N) (.const N) A 0 3 0 s 0
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
  refine ⟨workout, releaseWorkspace tag (N * N) N (I.width tag) workout, ν, flag,
    ?_, rfl, hflag, herr, hpost⟩
  rw [Prog.exec_eq_exec_toStmt, cgProg.toStmt_compiled]
  exact exec_scope_of_exec_eq_some I tag (IExp.const N * IExp.const N) N st workout hsize body hbody

/-- Releasing workspace preserves the actual declared decoded vectors and status. -/
theorem decoded_release_context (tag : P) (N width : ℕ) {storedMatrix : Bool}
    (workout : St P K (OpCount P ι)) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (v : CGState ℝ (Fin N)) (ν status flag : ℝ)
    (h : StoreContext tag dec N A b v ν status flag workout.store storedMatrix) :
    let out := releaseWorkspace tag (if storedMatrix then N * N else 0) N width workout
    out.store.shape = #[(tag, N), (tag, N), (tag, N), (tag, N), (tag, 1)] ∧
    (∀ i : Fin N, ∃ w, out.store.read tag 0 i = some w ∧ dec tag w = b i) ∧
    (∀ i : Fin N, ∃ wx wr wp, out.store.read tag 1 i = some wx ∧ dec tag wx = v.x i ∧
      out.store.read tag 2 i = some wr ∧ dec tag wr = v.r i ∧
      out.store.read tag 3 i = some wp ∧ dec tag wp = v.p i) ∧
    (∃ w, out.store.read tag 4 0 = some w ∧ dec tag w = status) := by
  have hsize : workout.store.size = 8 := by
    simpa [Store.shape, workspaceShape] using congrArg Array.size h.shape
  let matrixLen := if storedMatrix then N * N else 0
  have frame (buf idx : ℕ) (hb : buf < 5) :=
    read_releaseWorkspace tag matrixLen N width workout hsize tag buf idx hb
  refine ⟨shape_releaseWorkspace tag matrixLen N width workout h.shape, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨w, hw, hd⟩ := h.input i
    exact ⟨w, (frame 0 i (by norm_num)).trans hw, hd⟩
  · intro i
    obtain ⟨wx, hx, hdx⟩ := h.iterate i
    obtain ⟨wr, hr, hdr⟩ := h.residual i
    obtain ⟨wp, hp, hdp⟩ := h.direction i
    exact ⟨wx, wr, wp, (frame 1 i (by norm_num)).trans hx, hdx,
      (frame 2 i (by norm_num)).trans hr, hdr, (frame 3 i (by norm_num)).trans hp, hdp⟩
  · obtain ⟨w, hw, hd⟩ := h.statusValue
    exact ⟨w, (frame 4 0 (by norm_num)).trans hw, hd⟩

/-- Actual execution of the registered stored-entry CG tree under the existing scalar
contract and input-only spectral precision. Outputs are decoded from the returned declared
buffers after scope release. A positive completed prefix gives the existing CGRun with the
same matrix, input and precision; early zero termination and zero budget stay separate.
The standard count and full cell/bit workspace bounds hold for this same actual execution.
The backward-model and physical-energy consequences are in
[CGProgramRoundedBackward](CGProgramRoundedBackward.lean). -/
theorem exec_rounded_compiled (I : Interp P ι K (OpCount P ι)) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hu : u tag < 1) (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → K) (vals : ℕ → K)
    (hshape : st.store.shape = #[(tag, N), (tag, N), (tag, N), (tag, N), (tag, 1)])
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hrom : ∀ i < N * N, I.rom i = some (vals i))
    (hdecode : ∀ i j : Fin N, dec tag (vals (i + N * j)) = A i j)
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (horizon : CGPrecisionHorizon q (cgImplementationRoundoffBound N (u tag)) (a' / a)) :
    ∃ (out : St P K (OpCount P ι)) (flag : ℝ),
      (cgProg.compiled tag).exec I N ![q] st = some out ∧
      out.store.shape = #[(tag, N), (tag, N), (tag, N), (tag, N), (tag, 1)] ∧
      0 < flag ∧ |flag - 1| ≤ u tag ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 0 i = some w ∧ dec tag w = dec tag (b i)) ∧
      (StaticCost.mk (cgCount tag N q) (fun p => if p = tag then N ^ 2 + N + 10 else 0)
        ((N ^ 2 + N + 10) * I.width tag)).Bounds st out ∧
      (((q = 0 ∨ (fun i => dec tag (b i)) = 0) ∧
        (∀ i : Fin N, ∃ wx wr wp, out.store.read tag 1 i = some wx ∧ dec tag wx = 0 ∧
          out.store.read tag 2 i = some wr ∧ dec tag wr = dec tag (b i) ∧
          out.store.read tag 3 i = some wp ∧ dec tag wp = dec tag (b i)) ∧
        (∃ w, out.store.read tag 4 0 = some w ∧
          dec tag w = if (fun i => dec tag (b i)) = 0 then flag else 0)) ∨
      ∃ (m : ℕ) (R : CGRun N m), m ≤ q ∧ R.A = A ∧ R.b = (fun i => dec tag (b i)) ∧
        R.ε = cgImplementationRoundoffBound N (u tag) ∧
        (∀ i : Fin N, ∃ wx wr wp, out.store.read tag 1 i = some wx ∧ dec tag wx = R.x m i ∧
          out.store.read tag 2 i = some wr ∧ dec tag wr = R.r m i ∧
          out.store.read tag 3 i = some wp ∧ dec tag wp = R.p m i) ∧
        (∃ w, out.store.read tag 4 0 = some w ∧ dec tag w = if R.r m = 0 then flag else 0) ∧
        (m < q → R.r m = 0)) := by
  obtain ⟨workout, out, ν, flag, hrun, hrelease, hflag, herr, hpost⟩ :=
    exec_rounded_scoped I tag hsem hz hu hc st N q A b vals hshape hb hrom hdecode
      hsmall hA ha hspec horizon
  subst out
  have hcost := cgProg.bounds_of_exec_eq_some I tag N q hc hrun
  rcases hpost with ⟨hstop, hctx⟩ | ⟨m, R, hm, hRA, hRb, hRε, hctx, hstop⟩
  · obtain ⟨shape, input, vectors, status⟩ :=
      decoded_release_context tag N (I.width tag) workout A _ _ ν _ flag hctx
    exact ⟨_, flag, hrun, shape, hflag, herr, input, hcost, Or.inl ⟨hstop, vectors, status⟩⟩
  · obtain ⟨shape, input, vectors, status⟩ :=
      decoded_release_context tag N (I.width tag) workout A _ _ (R.ν m) _ flag hctx
    exact ⟨_, flag, hrun, shape, hflag, herr, input, hcost,
      Or.inr ⟨m, R, hm, hRA, hRb, hRε, vectors, status, hstop⟩⟩

end NLAlib.CGImplementation
