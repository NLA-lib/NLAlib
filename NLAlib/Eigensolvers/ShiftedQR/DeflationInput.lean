/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.WorklistAllocation
public import NLAlib.Ops.Certification

/-!
# Raw input interface for exact shifted-QR deflation

The supplied words are an interleaved Hessenberg matrix, raw parameters
`[B, theta, alpha, gamma, delta]`, and uninitialized output capacity. The spectral gap is a
mathematical promise, not a precomputed runtime result. Admissibility states raw quantitative
matrix assumptions and the chosen integer iteration/grid parameters; it never mentions
execution or a future output. Every valid size has a raw input by its definition.

## Main results

* `NLAlib.ShiftedQR.DeflationData`: supplied raw words and a mathematical gap promise.
* `NLAlib.ShiftedQR.DeflationAdmissible`: raw numerical and dimension assumptions.
* `NLAlib.ShiftedQR.deflationProblem`: the three-buffer canonical raw problem.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

/-- Raw matrix and parameter words. The gap is used only by the mathematical hypotheses. -/
structure DeflationData where
  /-- Actual column-major interleaved matrix words. -/
  matrixWords : List ℝ
  /-- Actual raw words `[B,theta,alpha,gamma,delta]`. -/
  parameterWords : List ℝ
  /-- A lower bound on distances between distinct eigenvalues of the input. -/
  gap : ℝ

/-- Decode the input matrix directly from its actual supplied words. -/
def DeflationData.matrix (x : DeflationData) (d : Fin 5 → ℕ) :
    Matrix (Fin (d 0 + 1)) (Fin (d 0 + 1)) ℂ := matrixOfWords (d 0 + 1) x.matrixWords

/-- The chosen degree, raw spectral assumptions, and grid/iteration dimensions.
Dimension zero is the matrix order minus one; the other dimensions are `m,k,F,M`. -/
def DeflationAdmissible (d : Fin 5 → ℕ) (x : DeflationData) : Prop :=
  x.matrixWords.length = 2 * ((d 0 + 1) * (d 0 + 1)) ∧ x.parameterWords.length = 5 ∧
  d 2 = 2 ^ d 1 ∧ IsUpperHessenberg (x.matrix d) ∧
  ShiftedQRHyps (x.matrix d) (vec x.parameterWords 0) (vec x.parameterWords 1)
    (vec x.parameterWords 2) (vec x.parameterWords 3) (vec x.parameterWords 4) x.gap (d 1) (d 3) ∧
  d 4 = ⌈Real.sqrt 2 / exceptionalSpacing (2 ^ d 1) (vec x.parameterWords 0)
    (vec x.parameterWords 1) (vec x.parameterWords 2) ((1 - vec x.parameterWords 3) ^ 2)⌉₊

/-- A scalar identity matrix supplies one genuinely admitted raw input. Integer iteration and
grid parameters are chosen from the same explicit formulas used by admissibility. -/
private theorem exists_deflationAdmissible : ∃ d x, DeflationAdmissible d x := by
  let H : Matrix (Fin 1) (Fin 1) ℂ := 1
  let params : List ℝ := [2, 1, 4, 1 / 2, 1]
  let F := ⌈Real.log (2 / (1 : ℝ)) / Real.log (1 / (1 - (1 / 2 : ℝ)))⌉₊
  let M := ⌈Real.sqrt 2 / exceptionalSpacing 2 2 1 4 ((1 - (1 / 2 : ℝ)) ^ 2)⌉₊
  let d : Fin 5 → ℕ := ![0, 1, 2, F, M]
  let x : DeflationData := ⟨matrixWords H, params, 1⟩
  have hHess : IsUpperHessenberg H := by
    intro i j hij
    fin_cases i
    fin_cases j
    omega
  have hcond : pseudoConditionNumber (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
    apply HasOrthonormalCols.pseudoConditionNumber_eq_one
    rw [hasOrthonormalCols_iff]
    simp
  have hGlobal : ShiftedQRHyps H 2 1 4 (1 / 2) 1 1 1 F := by
    refine ⟨⟨1, fun _ => 1, isUnit_one, by simp [H], ?_, ?_⟩,
      by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, by norm_num, ?_, le_rfl⟩
    · simp [hcond]
    · intro i j hne
      exact False.elim (hne (Subsingleton.elim i j))
    · simpa only [Nat.sub_self, Nat.cast_zero, zero_mul] using specNorm_nonneg H
  refine ⟨d, x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [x, d, H]
  · simp [x, params]
  · rfl
  · simpa [x, d, DeflationData.matrix] using hHess
  · simpa [x, d, params, DeflationData.matrix, vec] using hGlobal
  · simp [x, d, params, vec, M]

/-- Three raw buffers: the supplied matrix and parameter words, and empty root-output slots.
Valid sizes mean exactly that the raw mathematical domain is inhabited, so supply is an
existence proof of raw data rather than a callback computing an initial state or answer. -/
def deflationProblem : Problem ℝ 5 3 where
  formats _ := .cell
  valid d := ∃ x, DeflationAdmissible d x
  Data _ := DeflationData
  admissible d x buffers := DeflationAdmissible d x ∧
    buffers = ![x.matrixWords.map some, x.parameterWords.map some,
      List.replicate (2 * (d 0 + 1)) none]
  admitted := by
    obtain ⟨d, x, hx⟩ := exists_deflationAdmissible
    exact ⟨d, x, hx⟩
  supply d hd := by
    obtain ⟨x, hx⟩ := hd
    exact ⟨x, _, hx, rfl⟩

/-- Admissibility identifies exactly the actual raw supplied buffers. -/
theorem deflation_input_buffers (d : Fin 5 → ℕ) (x : deflationProblem.Input d) :
    x.val.2 = ![x.val.1.matrixWords.map some, x.val.1.parameterWords.map some,
      List.replicate (2 * (d 0 + 1)) none] := x.property.2

/-- The initial matrix is decoded directly from its actual supplied words. -/
theorem initial_deflation_matrix (d : Fin 5 → ℕ) (x : deflationProblem.Input d) :
    HoldsMatrix (0, 0) (x.val.1.matrix d) (deflationProblem.initial d x).store := by
  have hr := Problem.initial_readBlock (P := deflationProblem) d x (0 : Fin 3)
    (show x.val.2 0 = x.val.1.matrixWords.map some by rw [deflation_input_buffers]; rfl)
  rw [x.property.1.1] at hr
  change _ = some (matrixWords (matrixOfWords _ _))
  rw [matrixWords_matrixOfWords _ x.property.1.1]
  exact hr

/-- The actual raw parameter block is supplied verbatim. -/
theorem initial_deflation_parameters (d : Fin 5 → ℕ) (x : deflationProblem.Input d) :
    (deflationProblem.initial d x).store.readBlock 1 0 5 = some x.val.1.parameterWords := by
  have hr := Problem.initial_readBlock (P := deflationProblem) d x (1 : Fin 3)
    (show x.val.2 1 = x.val.1.parameterWords.map some by rw [deflation_input_buffers]; rfl)
  simpa [x.property.1.2.1] using hr

/-- Resident storage counts both raw inputs and the full initially empty output capacity. -/
theorem initialBytes_deflationProblem (d : Fin 5 → ℕ) (x : deflationProblem.Input d) :
    deflationProblem.initialBytes d x = 2 * ((d 0 + 1) * (d 0 + 1)) + 5 + 2 * (d 0 + 1) := by
  unfold Problem.initialBytes
  rw [deflation_input_buffers]
  simp [deflationProblem, List.ofFn_succ, x.property.1.1, x.property.1.2.1, Nat.add_assoc]

end NLAlib.ShiftedQR
