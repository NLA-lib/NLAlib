/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Examples.WorkedInstances.Basic
public import NLAlib.Ops.Examples.Integrator

/-!
# Worked instance: two steps of the explicit integrator

The certified program `NLAlib.Ops.Examples.Integrator.myProgram`, which runs the routine of one
step $x \leftarrow x + h A x$ inside a loop, with exact operations (the allowances $\delta$ and
$e$ of its model are zero), on
$$A = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}, \qquad h = \tfrac12, \qquad
  x_0 = (4, 8), \qquad N = 2.$$
It exercises a routine run by another, an allocation inside a loop, and the peak scratch.

Expected, from `scripts/worked_instances.py` (`Integrator`): the output `[11, 2]`, `2`
products with $A$ and `2` updates, and one scratch vector of `2` cells. The work of `91`
(products weigh $2 n^2$, updates $2 n$, structural instructions one) is a regression value in
its structural part, $28 N + 11 = 67$.

## Main results

* `NLAlib.Ops.Examples.WorkedInstances.Integrator.run_exact`: with exact operations the
  integrator leaves exactly $(I + h A)^N x_0$, at every size.
* `NLAlib.Ops.Examples.WorkedInstances.Integrator.instance_run`: the run on the instance.
-/

@[expose] public section

namespace NLAlib.Ops.Examples.WorkedInstances.Integrator

open NLAlib.Ops.Examples.Integrator
open scoped Matrix Matrix.Norms.L2Operator

/-- The tree of the integrator has no test. -/
theorem program_straight : myProgram.body.Straight :=
  Stmt.straight_of_isStraight rfl

/-- With exact operations the integrator leaves exactly $(I + h A)^N x_0$: at zero allowances
the error bound of its certificate is zero. -/
theorem run_exact (A : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ) (d : Fin 2 → ℕ) (h : ℝ)
    (x₀ : Fin (d 0) → ℝ) (I : Interp MyOperation Empty ℝ)
    (hI : (myModel A 0 0 le_rfl le_rfl).contracts d (myDomain.input d (h, x₀) trivial) I)
    (τ : Tape ℝ) :
    ∃ st, Reference.Execution myProgram I myResources myProblem.formats τ d
        (myProblem.initial d (myDomain.input d (h, x₀) trivial)) st ∧
      st.mem.store.readBlock 1 0 (d 0) =
        some (List.ofFn (((1 + h • A (d 0)) ^ d 1) *ᵥ x₀)) := by
  obtain ⟨st, hr, -, -, -, -, -, xT, hxT, hgood⟩ :=
    (myAlgorithm A 0 0 le_rfl le_rfl).correct d trivial (myDomain.input d (h, x₀) trivial) I hI τ
  refine ⟨st, hr, ?_⟩
  have hg : ‖WithLp.toLp 2 (decv id (d 0) xT - ((1 + h • A (d 0)) ^ d 1) *ᵥ x₀)‖ ≤ 0 := by
    have h0 : myEta (A (d 0)) 0 0 h = 0 := by simp [myEta]
    have := hgood
    change _ ≤ ((‖1 + h • A (d 0)‖ + myEta (A (d 0)) 0 0 h) ^ d 1 - ‖1 + h • A (d 0)‖ ^ d 1) * _
      at this
    rw [h0, add_zero, sub_self, zero_mul] at this
    exact this
  have hz : decv id (d 0) xT = ((1 + h • A (d 0)) ^ d 1) *ᵥ x₀ := by
    have h1 := norm_le_zero_iff.mp hg
    exact sub_eq_zero.mp ((WithLp.toLp_injective 2) (by simpa using h1))
  rw [hxT, ← hz, ofFn_decv (Store.length_of_readBlock hxT)]

/-- The matrix of the instance at every size: `1` above the diagonal and `-1` below it. -/
def skew (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if (i : ℕ) + 1 = j then 1 else if (j : ℕ) + 1 = i then -1 else 0

/-- At size two the matrix of the instance is the rotation generator. -/
theorem skew_two : skew 2 = !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew]

/-- At $n = 2$ and $N = 2$ the scratch of the tree is the two cells of its one vector. -/
theorem peak_instance : staticPeak myResources myProgram ![2, 2] = 2 := by
  rw [staticPeak, myResources.queryReserve_of_zero (fun q => nomatch q), Nat.add_zero]
  simpa [myProgram, Routine.close, Routine.bindsFit, Routine.flat, Port.flat, myIntegrate,
    myStep, Program.environment, List.ofFn_succ, Routine.closeDims, Routine.closeOps,
    List.range_succ, stmtPeak_tally, Stmt.instrument, indexBookkeeping, operandBookkeeping,
    stmtPeak, myResources, instrumentWorkspace, IExp.evalList, IExp.eval] using
    Finset.sup_const (s := Finset.range 2) (by simp) 2

/-- The instance. With exact operations, from the buffers holding $h = 1/2$ and
$x_0 = (4, 8)$, the execution rules derive one outcome of two steps of the integrator: the
second buffer holds `[11, 2]`; the run makes `2` products with $A$ at the dimensions `[2, 2]`
and `2` updates at `[2]`, and no other operation; its work is `91`; its peak scratch is `2`
cells. -/
theorem instance_run (I : Interp MyOperation Empty ℝ)
    (hI : (myModel skew 0 0 le_rfl le_rfl).contracts ![2, 2]
      (myDomain.input ![2, 2] (1 / 2, ![4, 8]) trivial) I) (τ : Tape ℝ) :
    ∃ st, Reference.Execution myProgram I myResources myProblem.formats τ ![2, 2]
        (myProblem.initial ![2, 2] (myDomain.input ![2, 2] (1 / 2, ![4, 8]) trivial)) st ∧
      st.mem.store.readBlock 1 0 2 = some [11, 2] ∧
      Count.original st.cost =
        2 • (Count.one MyOperation.matvec [2, 2] + Count.one MyOperation.axpy [2]) ∧
      myResources.work st.cost = 91 ∧ st.peak = 2 := by
  obtain ⟨st, hr, hout⟩ := run_exact skew ![2, 2] (1 / 2) ![4, 8] I hI τ
  obtain ⟨hc, hp⟩ := hr.eq_static_of_straight program_straight
  refine ⟨st, hr, ?_, ?_, ?_, ?_⟩
  · have h : st.mem.store.readBlock 1 0 2 =
        some (List.ofFn (((1 + (1 / 2 : ℝ) • skew 2) ^ 2) *ᵥ ![4, 8])) := hout
    rw [h, skew_two]
    simp [List.ofFn_succ, Matrix.one_fin_two, sq]
    norm_num
  · rw [hc, myProgram_calls]
    rfl
  · rw [hc, work_myProgram]
    rfl
  · rw [hp, peak_instance]

end NLAlib.Ops.Examples.WorkedInstances.Integrator
