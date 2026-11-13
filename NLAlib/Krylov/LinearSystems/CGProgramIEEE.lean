/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.IEEE
public import NLAlib.Krylov.LinearSystems.CGProgramUnderflow
public import NLAlib.Krylov.LinearSystems.CGProgramTree
-- Expose core's logical literal conversions for the closed checked execution below.
import all Init.Data.OfScientific

/-!
# The CG residual cache with actual Lean Float arithmetic

The checked finite-word endpoint uses actual Lean `Float` operations through core's logical
binary64 model. Its arithmetic accuracy, full-range success and exact zero addition are
proved, so the input-only CG residual-kernel certificate needs no abstract accuracy premise.
The result retains actual execution, the returned word, and its destination write/read.

The general result concerns the actual dot kernel called by the registered CG trees.
A separate concrete example executes the entire registered tree on the one-dimensional
identity system, with nonzero input and one requested iteration, and reads back its exact
solution and successful status. General finite-word CG convergence, native runtime replacement
correctness and true-residual bounds for arbitrary computed iterates remain separate questions.

## Main results

* `NLAlib.CGImplementation.exec_self_dot_of_sem_eq_finiteFloatSem`:
  actual binary64 residual-dot execution and its underflow-aware cache certificate.
* `NLAlib.CGImplementation.exists_exec_cgProg_identity_finiteFloat`: a full positive-budget
  finite-word run of the registered tree on the one-dimensional identity system.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation

private def identityInput : St Unit FiniteFloat ℕ :=
  inputState () [#[some finiteFloatOne], #[none], #[none], #[none], #[none]]

private def identityRun : Option (St Unit FiniteFloat ℕ) :=
  (cgProg.compiled (ι := Unit) ()).exec
    (finiteFloatStoredInterp #[finiteFloatOne]) 1 ![1] identityInput

-- The closed checked Float execution traverses core's logical bit arithmetic at each step.
set_option maxHeartbeats 400000 in
-- Four readbacks normalize the complete registered execution, including checked Float literals.
set_option maxRecDepth 4096 in
/-- The actual registered CG tree solves the one-dimensional system $[1]x=[1]$ with checked
finite binary64 words and one requested iteration. The input residual is nonzero, so this run
executes a positive-curvature step. Its returned iterate decodes to $1$, residual to $0$,
and positive status to $1$, all read from the actual returned store. ROM and arithmetic are
concrete; there is no abstract error, range, successful-trajectory or probabilistic hypothesis.
This is a full finite-word execution example, not a general finite-format convergence claim.
No printed source. -/
theorem exists_exec_cgProg_identity_finiteFloat :
    ∃ out : St Unit FiniteFloat ℕ,
      (cgProg.compiled (ι := Unit) ()).exec (finiteFloatStoredInterp #[finiteFloatOne])
        1 ![1] (inputState () [#[some finiteFloatOne], #[none], #[none], #[none], #[none]]) =
          some out ∧
      (∃ w, out.store.read () 1 0 = some w ∧ floatDecode w.val = 1) ∧
      (∃ w, out.store.read () 2 0 = some w ∧ floatDecode w.val = 0) ∧
      (∃ w, out.store.read () 4 0 = some w ∧ floatDecode w.val = 1) := by
  refine ⟨identityRun.getD identityInput, ?_, ⟨finiteFloatOne, ?_, floatDecode_finiteFloatOne⟩,
    ⟨finiteFloatZero, ?_, floatDecode_finiteFloatZero⟩,
    ⟨finiteFloatOne, ?_, floatDecode_finiteFloatOne⟩⟩ <;> rfl

/-- The actual CG squared-residual kernel executes with finite Lean `Float` words when
its input satisfies $P\|\mathbf{r}\|^2+D\le M$, where $u=2^{-53}$, $\eta=2^{-1075}$,
$P=(1+u)^{2N}$, $D=NP(2+u)\eta$ and $M=(2^{53}-1)2^{971}$. Every intermediate product and
accumulation is then in range. The decoded cache $\nu$ has error at most
$(P-1)\|\mathbf{r}\|^2+D$; if $P<2$, a zero cache certifies
$\|\mathbf{r}\|^2\le D/(2-P)$. This includes dimension zero and retains the actual
destination write/read. No observed intermediate-finiteness hypothesis or abstract arithmetic
accuracy assumption is required. The residual is the supplied recursive vector. -/
theorem exec_self_dot_of_sem_eq_finiteFloatSem {ι C : Type} [AddMonoid C]
    (I : Interp Unit ι FiniteFloat C) (hsem : I.sem = finiteFloatSem)
    (st : St Unit FiniteFloat C)
    (N : ℕ) (dst : Cell ℕ ℕ) (r : ℕ) (off : IExp ℕ) (rv : ℕ → ℝ)
    (hr : ∀ i < N, ∃ w, st.store.read () r (off.eval + i) = some w ∧
      floatDecode w.val = rv i)
    (hdr : dst.buf = r → ∀ i < N, dst.idx.eval ≠ off.eval + i)
    (hdst : ∃ v s, st.store.write () dst.buf dst.idx.eval v = some s)
    (hrange : (1 + (2 : ℝ) ^ (-53 : ℤ)) ^ (2 * N) *
        ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 +
      N * (1 + (2 : ℝ) ^ (-53 : ℤ)) ^ (2 * N) *
        (2 + (2 : ℝ) ^ (-53 : ℤ)) * (2 : ℝ) ^ (-1075 : ℤ) ≤
          ((2 : ℝ) ^ 53 - 1) * (2 : ℝ) ^ (971 : ℤ)) :
    ∃ out w, exec I (dot () dst r off r off (.const N)).run st = some out ∧
      st.store.write () dst.buf dst.idx.eval w = some out.store ∧
      out.store.read () dst.buf dst.idx.eval = some w ∧
      AbsRelErr ((1 + (2 : ℝ) ^ (-53 : ℤ)) ^ (2 * N) - 1)
        (N * (1 + (2 : ℝ) ^ (-53 : ℤ)) ^ (2 * N) *
          (2 + (2 : ℝ) ^ (-53 : ℤ)) * (2 : ℝ) ^ (-1075 : ℤ))
        (‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2) (floatDecode w.val) ∧
      (0 < 2 - (1 + (2 : ℝ) ^ (-53 : ℤ)) ^ (2 * N) → floatDecode w.val = 0 →
        ‖WithLp.toLp 2 (fun i : Fin N => rv i)‖ ^ 2 ≤
          (N * (1 + (2 : ℝ) ^ (-53 : ℤ)) ^ (2 * N) *
            (2 + (2 : ℝ) ^ (-53 : ℤ)) * (2 : ℝ) ^ (-1075 : ℤ)) /
              (2 - (1 + (2 : ℝ) ^ (-53 : ℤ)) ^ (2 * N))) := by
  have hu : Float.Model.Format.binary64.unitRoundoff = (2 : ℝ) ^ (-53 : ℤ) := rfl
  have hη : Float.Model.Format.binary64.underflowBound = (2 : ℝ) ^ (-1075 : ℤ) := by
    change (2 : ℝ) ^ (-1074 : ℤ) / 2 = (2 : ℝ) ^ (-1075 : ℤ)
    rw [div_eq_iff two_ne_zero, ← zpow_add_one₀ two_ne_zero]
    congr 1
  have hM : Float.Model.Format.binary64.maxFinite =
      ((2 : ℝ) ^ 53 - 1) * (2 : ℝ) ^ (971 : ℤ) := rfl
  have h : IsArithErrSem (fun (_ : Unit) _ =>
      AbsRelErr ((2 : ℝ) ^ (-53 : ℤ)) ((2 : ℝ) ^ (-1075 : ℤ)))
      (fun _ (x : FiniteFloat) => floatDecode x.val)
      (fun _ a => |a| ≤ ((2 : ℝ) ^ 53 - 1) * (2 : ℝ) ^ (971 : ℤ)) I.sem := by
    rw [hsem]
    simpa only [hu, hη, hM] using isArithErrSem_finiteFloatSem
  have hz : AddsZeroExactly (fun (_ : Unit) (x : FiniteFloat) => floatDecode x.val) I.sem := by
    rw [hsem]
    exact addsZeroExactly_finiteFloatSem
  exact h.exec_cg_self_dot_of_absRelErr_of_abs_le I () hz st N dst r off rv
    (by positivity) (by positivity) hr hdr hdst
      (((2 : ℝ) ^ 53 - 1) * (2 : ℝ) ^ (971 : ℤ)) (fun _ ha => ha) hrange

end NLAlib.CGImplementation
