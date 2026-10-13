/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.RCLike.ToComplex
public import NLAlib.Matrix.Functions.Exponential

/-!
# Transfer from `𝕜` to `ℂ`

Many results on functions of Hermitian matrices are theorems about complex C⋆-algebras. To state
them over an arbitrary `RCLike` field (in particular over `ℝ`), a matrix over `𝕜` is sent to the
complex matrix with the same real and imaginary parts, `NLAlib.complexify A`. The map is an
injective star algebra homomorphism over `ℝ` compatible with traces, the Loewner order, the
functional calculus and the exponential, so a statement about Hermitian matrices that holds over
`ℂ` holds over `𝕜`.

## Main definitions

* `NLAlib.complexify`: entrywise embedding of `Matrix m n 𝕜` into `Matrix m n ℂ`.

## Main results

* `NLAlib.complexify_mul`, `NLAlib.complexify_conjTranspose`: it is a star-ring homomorphism.
* `NLAlib.re_trace_complexify`, `NLAlib.complexify_le_complexify_iff`.
* `NLAlib.complexify_cfc`, `NLAlib.complexify_exp`.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open NormedSpace (exp)

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- The **complexification** of a matrix over an `RCLike` field: the complex matrix with the same
real and imaginary parts. Over `ℂ` it is the identity, over `ℝ` the inclusion.
Port of `NLAlib.realMatrixComplexification`, there for real matrices. -/
noncomputable def complexify (A : Matrix m n 𝕜) : Matrix m n ℂ :=
  A.map RCLike.toComplex

/-- Entries of the complexification. -/
@[simp]
theorem complexify_apply (A : Matrix m n 𝕜) (i : m) (j : n) :
    complexify A i j = RCLike.toComplex (A i j) :=
  rfl

/-- On square matrices the complexification is the star algebra homomorphism induced by
`RCLike.toComplex`. -/
theorem complexify_eq_mapMatrix [DecidableEq n] (A : Matrix n n 𝕜) :
    complexify A = (RCLike.toComplex : 𝕜 →⋆ₐ[ℝ] ℂ).toAlgHom.mapMatrix A := by
  sorry

/-- The complexification is injective. -/
theorem complexify_injective : Function.Injective (complexify : Matrix m n 𝕜 → Matrix m n ℂ) := by
  sorry

/-- The complexification is additive. -/
@[simp]
theorem complexify_add (A B : Matrix m n 𝕜) : complexify (A + B) = complexify A + complexify B := by
  sorry

/-- The complexification commutes with subtraction. -/
@[simp]
theorem complexify_sub (A B : Matrix m n 𝕜) : complexify (A - B) = complexify A - complexify B := by
  sorry

/-- The complexification commutes with real scalar multiplication. -/
@[simp]
theorem complexify_real_smul (c : ℝ) (A : Matrix m n 𝕜) :
    complexify (c • A) = c • complexify A := by
  sorry

/-- The complexification of zero. -/
@[simp]
theorem complexify_zero : complexify (0 : Matrix m n 𝕜) = 0 := by
  sorry

/-- The complexification of the identity. -/
@[simp]
theorem complexify_one [DecidableEq n] : complexify (1 : Matrix n n 𝕜) = 1 := by
  sorry

/-- The complexification is multiplicative. -/
@[simp]
theorem complexify_mul (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    complexify (A * B) = complexify A * complexify B := by
  sorry

/-- The complexification commutes with natural powers. -/
@[simp]
theorem complexify_pow [DecidableEq n] (A : Matrix n n 𝕜) (k : ℕ) :
    complexify (A ^ k) = complexify A ^ k := by
  sorry

/-- The complexification commutes with the conjugate transpose. -/
@[simp]
theorem complexify_conjTranspose (A : Matrix m n 𝕜) : complexify Aᴴ = (complexify A)ᴴ := by
  sorry

/-- The complexification of a Hermitian matrix is Hermitian, and conversely. -/
@[simp]
theorem isHermitian_complexify_iff {A : Matrix n n 𝕜} :
    (complexify A).IsHermitian ↔ A.IsHermitian := by
  sorry

/-- The complexification preserves the real part of the trace. -/
@[simp]
theorem re_trace_complexify (A : Matrix n n 𝕜) :
    (complexify A).trace.re = RCLike.re A.trace := by
  sorry

/-- The complexification preserves and reflects positive semidefiniteness. -/
@[simp]
theorem posSemidef_complexify_iff {A : Matrix n n 𝕜} :
    (complexify A).PosSemidef ↔ A.PosSemidef := by
  sorry

/-- The complexification preserves and reflects positive definiteness. -/
@[simp]
theorem posDef_complexify_iff {A : Matrix n n 𝕜} : (complexify A).PosDef ↔ A.PosDef := by
  sorry

/-- **The complexification preserves and reflects the Loewner order.** -/
@[simp]
theorem complexify_le_complexify_iff {A B : Matrix n n 𝕜} :
    complexify A ≤ complexify B ↔ A ≤ B := by
  sorry

/-- The complexification preserves the real spectrum. -/
@[simp]
theorem spectrum_complexify [DecidableEq n] (A : Matrix n n 𝕜) :
    spectrum ℝ (complexify A) = spectrum ℝ A := by
  sorry

/-- The complexification preserves the sorted eigenvalues. -/
@[simp]
theorem eigenvalue_complexify (A : Matrix n n 𝕜) (k : ℕ) :
    eigenvalue (complexify A) k = eigenvalue A k := by
  sorry

/-- The complexification preserves the spectral norm. -/
@[simp]
theorem specNorm_complexify (A : Matrix m n 𝕜) : specNorm (complexify A) = specNorm A := by
  sorry

/-- **The complexification commutes with the functional calculus** of a Hermitian matrix. -/
theorem complexify_cfc [DecidableEq n] {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    complexify (cfc f A) = cfc f (complexify A) := by
  sorry

/-- The complexification commutes with the square root. -/
theorem complexify_sqrt [DecidableEq n] (A : Matrix n n 𝕜) :
    complexify (CFC.sqrt A) = CFC.sqrt (complexify A) := by
  sorry

/-- The complexification commutes with real powers. -/
theorem complexify_rpow [DecidableEq n] (A : Matrix n n 𝕜) (r : ℝ) :
    complexify (A ^ r) = complexify A ^ r := by
  sorry

/-- The complexification commutes with the exponential. -/
theorem complexify_exp [DecidableEq n] (A : Matrix n n 𝕜) :
    complexify (exp A) = exp (complexify A) := by
  sorry

end NLAlib
