/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.ComplexCodec
public import NLAlib.Eigensolvers.ShiftedQR.DeflationRoutine
public import NLAlib.Eigensolvers.ShiftedQR.Kernels
public import NLAlib.Ops.RoutineProblem
public import NLAlib.Ops.Certification

/-!
# Raw input interface for exact shifted-QR deflation

The inputs are an upper Hessenberg matrix and the reals $B, \theta, \alpha, \gamma, \delta$; the
problem holds the interleaved matrix words, the five parameter words and uninitialized output
capacity. The spectral gap is a mathematical promise, stated as an existential in the admission,
not an input. Admission states raw quantitative matrix assumptions and the chosen integer
iteration/grid parameters; it never mentions execution or a future output.

## Main results

* `NLAlib.ShiftedQR.deflationInputs`, `NLAlib.ShiftedQR.deflationProblem`: the admitted inputs
  and their problem.
* `NLAlib.ShiftedQR.initialBytes_deflationProblem`: the supplied payload.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

/-- The admitted inputs of exact shifted QR with deflation. The dimensions are the order minus
one and `m, k, F, M`; the inputs are an upper Hessenberg matrix of order `n + 1` and the reals
$B, \theta, \alpha, \gamma, \delta$. An input is admitted when the Ritz count is $2^m$, the
hypotheses of the analysis (`NLAlib.ShiftedQR.ShiftedQRHyps`) hold for some lower bound on the
gaps between distinct eigenvalues, and the grid bound is the one the parameters determine. The
gap is no input: no operand holds it and the program never reads it. The first operand holds the
interleaved words of the matrix, the second the five parameters; the root block is blank. The
admitted sizes are those at which some input is admitted. -/
noncomputable def deflationInputs :
    (deflationRoutine (O := Op) (Q := Tst) .skip).Domain ℝ 5 3 where
  valid d := ∃ x : Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ × (Fin 5 → ℝ),
    d 2 = 2 ^ d 1 ∧ IsUpperHessenberg x.1 ∧
    (∃ gap, ShiftedQRHyps x.1 (x.2 0) (x.2 1) (x.2 2) (x.2 3) (x.2 4) gap (d 1) (d 3)) ∧
    d 4 = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ d 1) (x.2 0) (x.2 1) (x.2 2)
      ((1 - x.2 3) ^ 2)⌉₊
  In d := Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ × (Fin 5 → ℝ)
  accepts d x := d 2 = 2 ^ d 1 ∧ IsUpperHessenberg x.1 ∧
    (∃ gap, ShiftedQRHyps x.1 (x.2 0) (x.2 1) (x.2 2) (x.2 3) (x.2 4) gap (d 1) (d 3)) ∧
    d 4 = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ d 1) (x.2 0) (x.2 1) (x.2 2)
      ((1 - x.2 3) ^ 2)⌉₊
  slot d := ![.stored (Codec.complexMatrix (d 0 + 1)) Prod.fst,
    .stored (Codec.vector 5) Prod.snd, .blank (2 * (d 0 + 1))]
  fits := by
    intro d i p hp
    fin_cases i <;> (
      have hport := Option.some.inj hp
      subst hport
      constructor <;>
        simp [Slot.len, Slot.held, Access.readable, Codec.complexMatrix, Codec.vector,
          List.ofFn_succ])
  faithful d x y _ h := by
    have h0 := h 0
    have h1 := h 1
    simp only [Slot.input, Matrix.cons_val_zero, Matrix.cons_val_one, Option.some.injEq]
      at h0 h1
    exact Prod.ext ((Codec.complexMatrix (d 0 + 1)).encode_injective h0)
      ((Codec.vector 5).encode_injective h1)
  admitted := by
    let F := ⌈Real.log (2 / (1 : ℝ)) / Real.log (1 / (1 - (1 / 2 : ℝ)))⌉₊
    let M := ⌈Real.sqrt 2 / exceptionalSpacing 2 2 1 4 ((1 - (1 / 2 : ℝ)) ^ 2)⌉₊
    have hcond : pseudoConditionNumber (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
      apply HasOrthonormalCols.pseudoConditionNumber_eq_one
      rw [hasOrthonormalCols_iff]
      simp
    have hGlobal : ShiftedQRHyps (1 : Matrix (Fin 1) (Fin 1) ℂ) 2 1 4 (1 / 2) 1 1 1 F := by
      refine ⟨⟨1, fun _ => 1, isUnit_one, by simp, ?_, ?_⟩,
        by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
        by norm_num, by norm_num, by norm_num, by norm_num, ?_, le_rfl⟩
      · simp [hcond]
      · intro i j hne
        exact False.elim (hne (Subsingleton.elim i j))
      · simpa only [Nat.sub_self, Nat.cast_zero, zero_mul] using
          specNorm_nonneg (1 : Matrix (Fin 1) (Fin 1) ℂ)
    refine ⟨![0, 1, 2, F, M], ((1 : Matrix (Fin 1) (Fin 1) ℂ), ![2, 1, 4, 1 / 2, 1]), rfl, ?_,
      ⟨1, by simpa using hGlobal⟩, by simp [M]⟩
    intro i j hij
    fin_cases i
    fin_cases j
    omega
  inhabited _ h := h

/-- The matrix words, the five parameters and blank root slots: the problem of exact shifted QR
with deflation. -/
noncomputable abbrev deflationProblem : Problem ℝ 5 3 := deflationInputs.problem

/-- The matrix of an input of the problem. -/
abbrev deflationInputMatrix (d : Fin 5 → ℕ) (x : deflationProblem.Input d) :
    Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ := x.val.1.1

/-- The parameters $B, \theta, \alpha, \gamma, \delta$ of an input of the problem. -/
abbrev deflationInputParams (d : Fin 5 → ℕ) (x : deflationProblem.Input d) : Fin 5 → ℝ :=
  x.val.1.2

/-- Resident storage counts both raw inputs and the full initially empty output capacity. -/
theorem initialBytes_deflationProblem (d : Fin 5 → ℕ) (x : deflationProblem.Input d) :
    deflationProblem.initialBytes d x = 2 * ((d 0 + 1) * (d 0 + 1)) + 5 + 2 * (d 0 + 1) := by
  refine (deflationInputs.initialBytes_eq x).trans ?_
  simp [deflationInputs, Slot.len, Codec.complexMatrix, Codec.vector, List.ofFn_succ]
  ring

end NLAlib.ShiftedQR
