/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.ForwardError
public import NLAlib.Ops.PolynomialWork

/-!
# A full work majorant for exact shifted QR

The base is the sum of matrix order minus one, Ritz depth, Ritz count, iteration fuel and grid
resolution, plus two. A fixed computable coefficient and loop degree come from the complete
instrumented program, preserving separate exponents for each index slot.
The spectral term is an explicit finite maximum of the supplied Ritz/root kernel costs.
Scalar arithmetic, index literals, queries, addressing, control, allocation and release all
retain their declared unit work. No spectral cost is assumed to vanish.

Only the overhead factor is asserted polynomial; supplied kernel costs may have arbitrary growth.
The admitted Ritz count is exponential in Ritz depth. Fuel and grid resolution remain explicit
inputs, so this is not a bit-complexity or accuracy-complexity assertion.
This is an intentionally coarse majorant, rather than a tight complexity estimate.
It provides a closed dimension/fuel/grid expression for the same total execution certified by
`exactAlgorithm`, independently of the much more detailed static count manifest.

## Main results

* `NLAlib.ShiftedQR.exactWorkCoefficient`: the fixed structural coefficient.
* `NLAlib.ShiftedQR.exactWorkDegree`: the fixed polynomial loop degree.
* `NLAlib.ShiftedQR.exactPolynomialWork`: explicit parameter and finite-kernel expression.
* `NLAlib.ShiftedQR.exactPolynomialWork_eq`: the kernel-checked numeric expression.
* `NLAlib.ShiftedQR.exactAlgorithm_runs_with_work_le`: total same-run work and output.
* `NLAlib.ShiftedQR.exactAlgorithmWithPolynomialWork`: canonical certificate with this work field.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- Sum of the five actual natural input parameters, with a base of at least two. The matrix
order is `d 0 + 1`, Ritz depth is `d 1`, count `d 2`, fuel `d 3`, and grid bound `d 4`. -/
def exactWorkBase (d : Fin 5 → ℕ) : ℕ := d 0 + d 1 + d 2 + d 3 + d 4 + 2

private def initialDegrees : List ℕ := List.replicate 5 1 ++ List.replicate 3 0

/-- A fixed syntax-computed coefficient counting alternative instruction bodies additively. -/
def exactWorkCoefficient : ℕ :=
  (deflationProgram scalarDecouple).body.instrument.workCoefficient

/-- The polynomial loop degree from separate initial index slots. Sequential code contributes
through the coefficient, while frames preserve the distinction between dimensions and offsets. -/
def exactWorkDegree : ℕ :=
  (deflationProgram scalarDecouple).body.instrument.workDegreeAt
    (List.replicate 5 1 ++ List.replicate 3 0)

/-- A separate exponent controlling primitive dimension values, including allocation lengths. -/
def exactCallDegree : ℕ :=
  (deflationProgram scalarDecouple).body.instrument.callDegreeAt
    (List.replicate 5 1 ++ List.replicate 3 0)

/-- The actual maximum primitive/query dimension-list length in the instrumented tree. -/
def exactCallArity : ℕ :=
  (deflationProgram scalarDecouple).body.instrument.callArity

-- Kernel reduction of the closed instrumented tree exceeds the default recursion depth.
set_option maxRecDepth 8192 in
/-- The structural coefficient of this fixed complete instrumented tree is 17109. -/
theorem exactWorkCoefficient_eq : exactWorkCoefficient = 17109 := by rfl

-- Kernel reduction of the closed instrumented tree exceeds the default recursion depth.
set_option maxRecDepth 8192 in
/-- The slot-sensitive full-program work exponent is fourteen. -/
theorem exactWorkDegree_eq : exactWorkDegree = 14 := by rfl

-- Kernel reduction of the closed instrumented tree exceeds the default recursion depth.
set_option maxRecDepth 8192 in
/-- Primitive dimension entries are bounded by the fifth power of the input base. -/
theorem exactCallDegree_eq : exactCallDegree = 5 := by rfl

-- Kernel reduction of the closed instrumented tree exceeds the default recursion depth.
set_option maxRecDepth 8192 in
/-- Every primitive/query dimension list in the complete tree has length at most two. -/
theorem exactCallArity_eq : exactCallArity = 2 := by rfl

/-- A finite maximum of both supplied spectral costs over bounded dimension-list lengths
and bounded entries. This includes malformed shapes conservatively without constraining the
cost function at any unbounded dimension. -/
def spectralWorkEnvelope (kernelWork : EigenvalueKernelOp → List ℕ → ℕ)
    (arity extent : ℕ) : ℕ :=
  weightEnvelope (fun ds => max (kernelWork .ritz ds) (kernelWork .smallEig ds)) arity extent

/-- Full work majorant: a fixed-degree polynomial in the five natural parameters, multiplied
by one plus the explicit finite spectral-cost envelope. The coefficient is computed from the
fixed instruction tree. -/
def exactPolynomialWork (kernelWork : EigenvalueKernelOp → List ℕ → ℕ)
    (d : Fin 5 → ℕ) : ℕ :=
  exactWorkCoefficient * exactWorkBase d ^ exactWorkDegree *
    (1 + spectralWorkEnvelope kernelWork exactCallArity (exactWorkBase d ^ exactCallDegree))

/-- The complete numeric work expression has coefficient 17109, work degree fourteen,
primitive arity two and primitive dimension degree five. All four values are kernel-checked
reductions of the same actual instrumented tree. -/
theorem exactPolynomialWork_eq (kernelWork : EigenvalueKernelOp → List ℕ → ℕ)
    (d : Fin 5 → ℕ) :
    exactPolynomialWork kernelWork d = 17109 * exactWorkBase d ^ 14 *
      (1 + spectralWorkEnvelope kernelWork 2 (exactWorkBase d ^ 5)) := by
  simp only [exactPolynomialWork, exactWorkCoefficient_eq, exactWorkDegree_eq,
    exactCallArity_eq, exactCallDegree_eq]

private theorem exact_initial_indices_le (d : Fin 5 → ℕ) :
    List.Forall₂ (fun v e => v ≤ exactWorkBase d ^ e)
      (Program.environment (b := 3) d).idx initialDegrees := by
  change List.Forall₂ (fun v e => v ≤ exactWorkBase d ^ e)
    [d 0, d 1, d 2, d 3, d 4, 0, 0, 0] [1, 1, 1, 1, 1, 0, 0, 0]
  repeat' apply List.Forall₂.cons
  all_goals try exact List.Forall₂.nil
  all_goals simp only [pow_one, pow_zero]
  all_goals first | exact Nat.zero_le _ | (dsimp [exactWorkBase]; omega)

private theorem exact_work_envelope
    (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ) (d : Fin 5 → ℕ) :
    WorkEnvelope
      (Sum.elim (resources kernelWork kernelWorkspace).operationWork
        (resources kernelWork kernelWorkspace).coreWork)
      (resources kernelWork kernelWorkspace).queryWork
      exactCallArity (exactWorkBase d ^ exactCallDegree)
      (1 + spectralWorkEnvelope kernelWork exactCallArity
        (exactWorkBase d ^ exactCallDegree)) := by
  constructor
  · intro o ds hl hx
    have hk := le_weightEnvelope
      (fun ds => max (kernelWork .ritz ds) (kernelWork .smallEig ds)) hl hx
    rcases o with o | core
    · rcases o with scalar | o
      · exact Nat.le_add_right 1 _
      · rcases o with index | kernel
        · exact Nat.le_add_right 1 _
        · cases kernel
          · exact (Nat.le_max_left _ _).trans (hk.trans (Nat.le_add_left _ _))
          · exact (Nat.le_max_right _ _).trans (hk.trans (Nat.le_add_left _ _))
    · exact Nat.le_add_right 1 _
  · intro q ds hl hx
    exact Nat.le_add_right 1 _

/-- Every admitted raw input, every interpreter meeting the jointly realized exact model and
every tape have a successful canonical execution whose full work and span are bounded by the
explicit polynomial expression. Its stored output is the certified nearby-matrix root output;
no successful-run, decoupling-success, or zero-kernel-cost assumption is added. -/
theorem exactAlgorithm_runs_with_work_le
    (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ)
    {d : Fin 5 → ℕ} (hd : deflationProblem.valid d) (x : deflationProblem.Input d)
    (I : Interp Op Tst ℝ)
    (hI : (model deflationProblem exactRoutines
      (resources kernelWork kernelWorkspace)).contracts d x I) (tape : Tape ℝ) :
    ∃ st, exec (deflationProgram scalarDecouple) I (resources kernelWork kernelWorkspace)
      deflationProblem.formats tape d (deflationProblem.initial d x) = some st ∧
      (resources kernelWork kernelWorkspace).work st.cost ≤ exactPolynomialWork kernelWork d ∧
      (resources kernelWork kernelWorkspace).span st.cost ≤ exactPolynomialWork kernelWork d ∧
      (deflationSpecification scalarDecouple kernelWork kernelWorkspace).good
        d x tape st.cost st.mem := by
  obtain ⟨st, hr, hp, hc, hw, hs, hm, hg⟩ :=
    (exactAlgorithm kernelWork kernelWorkspace).correct d hd x I hI tape
  have hwork : (resources kernelWork kernelWorkspace).work st.cost ≤
      exactPolynomialWork kernelWork d :=
    Program.exec_work_le_coefficient_mul_pow (deflationProgram scalarDecouple)
      (resources kernelWork kernelWorkspace) (base := exactWorkBase d)
      (by dsimp [exactWorkBase]; omega)
      (exact_initial_indices_le d) (exact_work_envelope kernelWork kernelWorkspace d) hr
  exact ⟨st, hr, hwork,
    ((resources kernelWork kernelWorkspace).span_le_work st.cost).trans hwork, hg⟩

/-- The backward/forward exact specification with the explicit full-work and span expression.
Its count, scratch, resident-memory and mathematical-output fields retain those guarantees. -/
noncomputable def exactWorkSpecification
    (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ) :
    Specification Op Tst deflationProblem :=
  { deflationForwardSpecification kernelWork kernelWorkspace with
    work := exactPolynomialWork kernelWork
    span := exactPolynomialWork kernelWork }

/-- Canonical exact shifted QR with the explicit work majorant and both backward and forward
error. The program, admitted inputs, operation model and full instruction budget are unchanged.
Algorithm: shifted-qr (run model) -/
noncomputable def exactAlgorithmWithPolynomialWork
    (kernelWork kernelWorkspace : EigenvalueKernelOp → List ℕ → ℕ) :
    Algorithm (model deflationProblem exactRoutines (resources kernelWork kernelWorkspace))
      (exactWorkSpecification kernelWork kernelWorkspace) where
  program := deflationProgram scalarDecouple
  correct := by
    intro d hd x I hI tape
    obtain ⟨old, hold, hp, hc, hw, hs, hm, hg⟩ :=
      (exactForwardAlgorithm kernelWork kernelWorkspace).correct d hd x I hI tape
    obtain ⟨st, hr, hwork, hspan, -⟩ :=
      exactAlgorithm_runs_with_work_le kernelWork kernelWorkspace hd x I hI tape
    have he : old = st := Option.some.inj (hold.symm.trans hr)
    subst old
    exact ⟨st, hr, hp, hc, hwork, hspan, hm, hg⟩

end NLAlib.ShiftedQR
