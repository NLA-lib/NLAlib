/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import NLAlib.ForMathlib.MeasureTheory.Integral.Log
public import NLAlib.Matrix.Functions.ExponentialInterpolation
public import NLAlib.Matrix.Norms.Schatten

/-!
# Ordered products of powers of positive semidefinite matrices

Complex powers are evaluated on the spectrum by the principal scalar power. The factors keep
their original order even if they do not commute. A positive shift of each factor preserves
its eigenvectors and hence gives convergence to the stated product, including on the kernel.
This is the singular limit in the multivariate trace inequality of
[SutterBertaTomamichel2017, Theorem 3.2].

## Main results

* `NLAlib.orderedMatrixCpow`: the ordered product of principal complex powers.
* `NLAlib.orderedMatrixCpow_ofReal_eq_prod_rpow`: its real boundary for PSD factors.
* `NLAlib.orderedMatrixCpow_eq_orderedMatrixExp_log`: its logarithmic form for definite factors.
* `NLAlib.schattenNorm_rpow_abs_prod_rpow_le_exp_integral_log`: the finite definite case.
* `NLAlib.log_schattenNorm_rpow_abs_prod_rpow_le_extendedLogIntegral`: the multivariate
  Araki–Lieb–Thirring inequality for positive semidefinite factors.
-/

@[expose] public section

open Matrix Complex Set Filter MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

private def diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ :=
  { (Matrix.diagonalAlgHom ℂ : (n → ℂ) →ₐ[ℂ] Matrix n n ℂ) with
    map_star' := by intro x; simp [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose] }

/-- Every complex-valued function on the finite normal spectrum commutes
with actual unitary conjugation. -/
private theorem cfc_complex_unitary_conj (U : unitary (Matrix n n ℂ)) (f : ℂ → ℂ)
    (A : Matrix n n ℂ) (hA : IsStarNormal A) :
    cfc f ((U : Matrix n n ℂ) * A * (U : Matrix n n ℂ)ᴴ) =
      (U : Matrix n n ℂ) * cfc f A * (U : Matrix n n ℂ)ᴴ := by
  cases isEmpty_or_nonempty n with
  | inl h =>
    let := h
    exact Subsingleton.elim _ _
  | inr h =>
    let := h
    let E := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U
    symm
    change E (cfc f A) = cfc f (E A)
    exact StarAlgHomClass.map_cfc E f A (A.finite_spectrum.continuousOn f)
      E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional hA (hA.map E)

/-- The native principal complex power of a normal matrix. In particular,
this is the source's complex power for PSD matrices; no logarithm is taken
at their zero eigenvalues when the exponent has positive real part. -/
private noncomputable abbrev matrixCpow (A : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  cfc (fun w : ℂ => w ^ z) A

/-- Native matrix complex powers keep their scalar spectral meaning under
unitary changes of coordinates. -/
private theorem matrixCpow_unitary_conj (U : unitary (Matrix n n ℂ))
    (A : Matrix n n ℂ) (hA : IsStarNormal A) (z : ℂ) :
    matrixCpow ((U : Matrix n n ℂ) * A * (U : Matrix n n ℂ)ᴴ) z =
      (U : Matrix n n ℂ) * matrixCpow A z * (U : Matrix n n ℂ)ᴴ :=
  cfc_complex_unitary_conj U _ A hA

/-- Complex functional calculus acts entrywise on an arbitrary complex diagonal.
No continuity assumption is needed on its finite spectrum. -/
private theorem cfc_diagonal_complex (f : ℂ → ℂ) (x : n → ℂ) :
    cfc f (Matrix.diagonal x) = Matrix.diagonal (fun i => f (x i)) := by
  let := IsStarNormal.instContinuousFunctionalCalculus (A := n → ℂ)
  have hx : IsStarNormal x := by infer_instance
  have hd : IsStarNormal (diagonalStarAlgHom x) := hx.map diagonalStarAlgHom
  have hc : ContinuousOn f (spectrum ℂ x) := by
    rw [Pi.spectrum_eq]
    have heq : (⋃ i, spectrum ℂ (x i)) = Set.range x := by
      change (⋃ i, spectrum ℂ (algebraMap ℂ ℂ (x i))) = _
      simp only [spectrum.scalar_eq, Set.iUnion_singleton_eq_range]
    rw [heq]
    exact Set.Finite.continuousOn (Set.finite_range _) _
  have heq := diagonalStarAlgHom.map_cfc (p := IsStarNormal) (q := IsStarNormal) f x hc
    (by change Continuous (fun z : n → ℂ => Matrix.diagonal z); fun_prop) hx hd
  rw [cfc_map_pi (p := IsStarNormal) (q := fun _ => IsStarNormal) (S := ℂ) f x
    (by rwa [← Pi.spectrum_eq]) hx (fun _ => inferInstance)] at heq
  change Matrix.diagonal (fun i => cfc f (algebraMap ℂ ℂ (x i))) =
    cfc f (Matrix.diagonal x) at heq
  have hh (i : n) : cfc f (x i) = f (x i) := cfc_algebraMap (R := ℂ) (A := ℂ) (x i) f
  simp only [Algebra.algebraMap_self, RingHom.id_apply, hh] at heq
  exact heq.symm

/-- A Hermitian matrix's native complex calculus is evaluation at its real
spectrum in one fixed orthonormal eigenbasis. -/
private theorem cfc_complex_eq_eigenbasis {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℂ → ℂ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => f (hA.eigenvalues i : ℂ)) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    cfc_complex_unitary_conj, cfc_diagonal_complex]
  · rfl
  · exact (Matrix.isHermitian_diagonal_of_self_adjoint _
      (by ext i; simp)).isSelfAdjoint.isStarNormal

/-- Native complex powers evaluate the scalar principal power at every
Hermitian eigenvalue, with multiplicity. -/
private theorem matrixCpow_eq_eigenbasis {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (z : ℂ) :
    matrixCpow A z = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ) ^ z) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ :=
  cfc_complex_eq_eigenbasis hA _

/-- Scalar shifts retain a fixed Hermitian eigenbasis, including at repeated
eigenvalues. -/
private theorem add_ofReal_smul_one_eq_eigenbasis {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (ε : ℝ) :
    A + (ε : ℂ) • (1 : Matrix n n ℂ) =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun i => ((hA.eigenvalues i + ε : ℝ) : ℂ)) *
          (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  let E := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary
  have hd : Matrix.diagonal (fun i => ((hA.eigenvalues i + ε : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) +
        (ε : ℂ) • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  change A + (ε : ℂ) • 1 = E _
  rw [hd, map_add, map_smul, map_one]
  congr 1
  exact hA.spectral_theorem

/-- A shifted Hermitian matrix's complex power in its original eigenbasis.
This formula avoids choosing eigenvectors separately at each shift. -/
private theorem matrixCpow_add_ofReal_smul_one {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (ε : ℝ) (z : ℂ) :
    matrixCpow (A + (ε : ℂ) • (1 : Matrix n n ℂ)) z =
      (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun i => ((hA.eigenvalues i + ε : ℝ) : ℂ) ^ z) *
          (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  rw [add_ofReal_smul_one_eq_eigenbasis hA ε, matrixCpow_unitary_conj]
  · exact congrArg (fun X : Matrix n n ℂ =>
      (hA.eigenvectorUnitary : Matrix n n ℂ) * X *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ)
      (cfc_diagonal_complex (fun w => w ^ z) _)
  · exact (Matrix.isHermitian_diagonal_of_self_adjoint _
      (by ext i; simp)).isSelfAdjoint.isStarNormal

/-- Complex powers are continuous under scalar regularization of a fixed
Hermitian matrix when the exponent has positive real part. In particular,
this includes all zero eigenvalues of a PSD input. -/
private theorem continuousAt_matrixCpow_add_ofReal_smul_one
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt (fun ε : ℝ => matrixCpow
      (A + (ε : ℂ) • (1 : Matrix n n ℂ)) z) 0 := by
  simp_rw [matrixCpow_add_ofReal_smul_one hA]
  have hc : Continuous (fun ε : ℝ => fun i : n =>
      ((hA.eigenvalues i + ε : ℝ) : ℂ) ^ z) := by
    apply continuous_pi
    intro i
    exact (Complex.continuous_ofReal_cpow_const hz).comp (by fun_prop)
  apply ContinuousAt.mul
  · apply ContinuousAt.mul continuousAt_const
    exact ((Matrix.diagonalLinearMap n ℂ ℂ).continuous_of_finiteDimensional.comp hc).continuousAt
  · exact continuousAt_const

/-- For positive definite matrices the native principal complex power equals
the exponential of the complex scalar times the real matrix logarithm. -/
theorem _root_.Matrix.PosDef.cfc_cpow_eq_exp_smul_log {A : Matrix n n ℂ}
    (hA : A.PosDef) (z : ℂ) :
    cfc (fun w : ℂ => w ^ z) A = NormedSpace.exp (z • cfc Real.log A) := by
  change matrixCpow A z = _
  have hlog : (cfc Real.log) A = (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => (Real.log (hA.isHermitian.eigenvalues i) : ℂ)) *
        (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    rw [hA.isHermitian.cfc_eq]
    rfl
  rw [matrixCpow_eq_eigenbasis hA.isHermitian, hlog]
  have hU := hasOrthonormalCols_iff_mem_unitaryGroup.mpr hA.isHermitian.eigenvectorUnitary.2
  rw [← smul_mul_assoc, ← mul_smul_comm, hU.exp_mul_mul_conjTranspose rfl,
    ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  apply congrArg (fun X : Matrix n n ℂ =>
    (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * X *
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ)
  apply congrArg Matrix.diagonal
  funext i
  have hpos : 0 < hA.isHermitian.eigenvalues i := hA.eigenvalues_pos i
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'),
    ← Complex.ofReal_log hpos.le]
  simp [Pi.coe_exp, smul_eq_mul, mul_comm, Complex.exp_eq_exp_ℂ]

/-- Native real powers of a PSD matrix agree with its principal complex
power at real exponents. Zero eigenvalues retain the scalar power convention. -/
theorem _root_.Matrix.PosSemidef.cfc_cpow_ofReal {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (r : ℝ) :
    cfc (fun w : ℂ => w ^ (r : ℂ)) A = A ^ r := by
  change matrixCpow A (r : ℂ) = CFC.rpow A r
  rw [matrixCpow_eq_eigenbasis hA.isHermitian,
    show CFC.rpow A r = cfc (fun x : ℝ => x ^ r) A from
      CFC.rpow_eq_cfc_real hA.nonneg, hA.isHermitian.cfc_eq]
  change _ = (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) *
    Matrix.diagonal (fun i => ((hA.isHermitian.eigenvalues i ^ r : ℝ) : ℂ)) *
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ
  apply congrArg (fun X : Matrix n n ℂ =>
    (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ) * X *
      (hA.isHermitian.eigenvectorUnitary : Matrix n n ℂ)ᴴ)
  apply congrArg Matrix.diagonal
  funext i
  exact (Complex.ofReal_cpow (hA.eigenvalues_nonneg i) r).symm

omit [Fintype n] in
/-- Every positive scalar regularization of a PSD matrix is positive
definite. The scalar field is complex so this matches complex power formulas. -/
private theorem posDef_add_ofReal_smul_one {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) :
    (A + (ε : ℂ) • (1 : Matrix n n ℂ)).PosDef :=
  Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul (by exact_mod_cast hε))

/-- On the right boundary, a PSD matrix's complex powers have operator norm
at most the original operator norm, uniformly in imaginary time. -/
private theorem norm_matrixCpow_le_of_re_eq_one {A : Matrix n n ℂ}
    (hA : A.PosSemidef) {z : ℂ} (hz : z.re = 1) :
    ‖matrixCpow A z‖ ≤ ‖A‖ := by
  apply norm_cfc_le (norm_nonneg A)
  intro w hw
  rw [hA.isHermitian.spectrum_eq_image_range] at hw
  obtain ⟨x, ⟨i, rfl⟩, rfl⟩ := hw
  let : Nonempty n := ⟨i⟩
  change ‖(hA.isHermitian.eigenvalues i : ℂ) ^ z‖ ≤ ‖A‖
  have hi : (hA.isHermitian.eigenvalues i : ℂ) ∈ spectrum ℂ A :=
    (spectrum.algebraMap_mem_iff ℂ).mpr (hA.isHermitian.eigenvalues_mem_spectrum_real i)
  have h := spectrum.norm_le_norm_of_mem hi
  calc
    _ = hA.isHermitian.eigenvalues i ^ z.re :=
      Complex.norm_cpow_eq_rpow_re_of_nonneg (hA.eigenvalues_nonneg i) (by rw [hz]; norm_num)
    _ = hA.isHermitian.eigenvalues i := by rw [hz, Real.rpow_one]
    _ ≤ ‖A‖ := by simpa [abs_of_nonneg (hA.eigenvalues_nonneg i)] using h

/-- Ordered imaginary powers of a PSD matrix vary continuously along the
right boundary, including when the matrix is singular. -/
private theorem continuous_matrixCpow_right {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    Continuous (fun t : ℝ => matrixCpow A (1 + (t : ℂ) * I)) := by
  have hc (i : n) : Continuous (fun t : ℝ =>
      (hA.isHermitian.eigenvalues i : ℂ) ^ (1 + (t : ℂ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have ht : ContinuousAt (fun s : ℝ =>
        (hA.isHermitian.eigenvalues i, 1 + (s : ℂ) * I)) t := by fun_prop
    have hfull := Complex.continuousAt_ofReal_cpow (hA.isHermitian.eigenvalues i)
      (1 + (t : ℂ) * I) (Or.inl (by simp))
    have hcomp := ContinuousAt.comp
      (f := fun s : ℝ => (hA.isHermitian.eigenvalues i, 1 + (s : ℂ) * I))
      (g := fun p : ℝ × ℂ => (p.1 : ℂ) ^ p.2) hfull ht
    exact hcomp
  simp_rw [matrixCpow_eq_eigenbasis hA.isHermitian]
  have hpi : Continuous (fun t : ℝ => fun i : n =>
      (hA.isHermitian.eigenvalues i : ℂ) ^ (1 + (t : ℂ) * I)) := continuous_pi hc
  exact (continuous_const.mul
    ((Matrix.diagonalLinearMap n ℂ ℂ).continuous_of_finiteDimensional.comp hpi)).mul
      continuous_const

private theorem matrix_norm_one_le : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  cases isEmpty_or_nonempty n with
  | inl h =>
    let := h
    have hz : (1 : Matrix n n ℂ) = 0 := Subsingleton.elim _ _
    simp [hz]
  | inr h =>
    let := h
    simp

/-- The actual ordered product of principal matrix complex powers. -/
noncomputable def orderedMatrixCpow (L : List (Matrix n n ℂ)) (z : ℂ) : Matrix n n ℂ :=
  (L.map (fun A => cfc (fun w : ℂ => w ^ z) A)).prod

/-- The ordered product for an empty list equals the identity at every exponent. -/
@[simp] theorem orderedMatrixCpow_nil (z : ℂ) :
    orderedMatrixCpow ([] : List (Matrix n n ℂ)) z = 1 := rfl

/-- Prepending a matrix multiplies the ordered product by its principal power on the left. -/
@[simp] theorem orderedMatrixCpow_cons (A : Matrix n n ℂ)
    (L : List (Matrix n n ℂ)) (z : ℂ) :
    orderedMatrixCpow (A :: L) z =
      cfc (fun w : ℂ => w ^ z) A * orderedMatrixCpow L z := rfl

/-- Positive definite complex powers are the ordered exponential family
generated by the individual matrix logarithms. -/
theorem orderedMatrixCpow_eq_orderedMatrixExp_log
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosDef) (z : ℂ) :
    orderedMatrixCpow L z = orderedMatrixExp (L.map (cfc Real.log)) z := by
  unfold orderedMatrixCpow orderedMatrixExp
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro A hA
  exact (hL A hA).cfc_cpow_eq_exp_smul_log z

/-- At real exponents, an ordered PSD complex-power product is precisely
the product of the native positive real CFC powers. -/
theorem orderedMatrixCpow_ofReal_eq_prod_rpow
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef) (r : ℝ) :
    orderedMatrixCpow L (r : ℂ) = (L.map (fun A => A ^ r)).prod := by
  unfold orderedMatrixCpow
  congr 1
  apply List.map_congr_left
  intro A hA
  exact (hL A hA).cfc_cpow_ofReal r

/-- All logarithms generating the positive definite ordered family are
Hermitian. -/
private theorem isHermitian_mem_map_log (L : List (Matrix n n ℂ)) :
    ∀ H ∈ L.map (cfc Real.log), H.IsHermitian := by
  intro H hH
  obtain ⟨A, _, rfl⟩ := List.mem_map.mp hH
  exact cfc_predicate Real.log A

/-- Complex powers on the right boundary are uniformly controlled by the
product of the original PSD operator norms. Empty products are included. -/
theorem norm_orderedMatrixCpow_right_le
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef) (t : ℝ) :
    ‖orderedMatrixCpow L (1 + (t : ℂ) * I)‖ ≤ (L.map (fun A => ‖A‖)).prod := by
  induction L with
  | nil => simpa using (matrix_norm_one_le (n := n))
  | cons A L ih =>
    rw [orderedMatrixCpow_cons, List.map_cons, List.prod_cons]
    exact (norm_mul_le _ _).trans (mul_le_mul
      (norm_matrixCpow_le_of_re_eq_one (hL A (by simp)) (by simp))
      (ih (fun B hB => hL B (by simp [hB]))) (norm_nonneg _ ) (norm_nonneg _))

/-- The right-boundary ordered complex product is continuous even for
singular PSD factors. -/
theorem continuous_orderedMatrixCpow_right
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef) :
    Continuous (fun t : ℝ => orderedMatrixCpow L (1 + (t : ℂ) * I)) := by
  induction L with
  | nil => exact continuous_const
  | cons A L ih =>
    exact (continuous_matrixCpow_right (hL A (by simp))).mul
      (ih (fun B hB => hL B (by simp [hB])))

/-- Adding the same real scalar identity to every factor preserves their
displayed order. -/
private noncomputable def regularizeMatrixList (L : List (Matrix n n ℂ)) (ε : ℝ) :
    List (Matrix n n ℂ) :=
  L.map (fun A => A + (ε : ℂ) • (1 : Matrix n n ℂ))

omit [Fintype n] in
@[local simp] private theorem regularizeMatrixList_zero (L : List (Matrix n n ℂ)) :
    regularizeMatrixList L 0 = L := by simp [regularizeMatrixList]

omit [Fintype n] in
/-- Positive regularization gives genuine positive definite inputs. -/
private theorem posDef_mem_regularizeMatrixList (L : List (Matrix n n ℂ))
    (hL : ∀ A ∈ L, A.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    ∀ A ∈ regularizeMatrixList L ε, A.PosDef := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
  exact posDef_add_ofReal_smul_one (hL B hB) hε

omit [Fintype n] in
/-- Nonnegative scalar regularization preserves PSD inputs. -/
private theorem posSemidef_mem_regularizeMatrixList (L : List (Matrix n n ℂ))
    (hL : ∀ A ∈ L, A.PosSemidef) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ A ∈ regularizeMatrixList L ε, A.PosSemidef := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hA
  exact (hL B hB).add (Matrix.PosSemidef.one.smul (by exact_mod_cast hε))

/-- The entire ordered product converges to the original product as the
scalar regularization tends to zero, for every exponent of positive real part. -/
private theorem continuousAt_orderedMatrixCpow_regularize
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.IsHermitian)
    {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt (fun ε : ℝ => orderedMatrixCpow (regularizeMatrixList L ε) z) 0 := by
  induction L with
  | nil => exact continuousAt_const
  | cons A L ih =>
    exact (continuousAt_matrixCpow_add_ofReal_smul_one (hL A (by simp)) hz).mul
      (ih (fun B hB => hL B (by simp [hB])))

/-- A common operator norm bound for scalar regularizations with $0 \le \varepsilon \le 1$,
uniform in imaginary time. -/
private theorem norm_orderedMatrixCpow_regularize_right_le
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef)
    {ε : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    ‖orderedMatrixCpow (regularizeMatrixList L ε) (1 + (t : ℂ) * I)‖ ≤
      (L.map (fun A => ‖A‖ + 1)).prod := by
  apply (norm_orderedMatrixCpow_right_le _
    (posSemidef_mem_regularizeMatrixList L hL hε.1) t).trans
  unfold regularizeMatrixList
  rw [List.map_map]
  apply List.prod_map_le_prod_map₀ _ _ (fun _ _ => norm_nonneg _)
  intro A hA
  have hn : ‖A + (ε : ℂ) • (1 : Matrix n n ℂ)‖ ≤ ‖A‖ + 1 := by
    apply (norm_add_le _ _).trans
    apply add_le_add le_rfl
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε.1]
    exact (mul_le_mul_of_nonneg_left matrix_norm_one_le hε.1).trans (by simpa using hε.2)
  exact hn

/-- Right-boundary Schatten norms have a fixed bound for all positive scalar
regularizations up to one. -/
private theorem schattenNorm_orderedMatrixCpow_regularize_right_le
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef)
    {p ε : ℝ} (hp : 0 < p) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    schattenNorm (ENNReal.ofReal p) (orderedMatrixCpow (regularizeMatrixList L ε)
      (1 + (t : ℂ) * I)) ≤
        (Fintype.card n : ℝ) ^ (1 / p) * (L.map (fun A => ‖A‖ + 1)).prod := by
  apply (schattenNorm_le_card_rpow_mul_specNorm (ENNReal.ofReal_pos.mpr hp).ne' _).trans
  rw [ENNReal.toReal_ofReal hp.le, ← one_div, specNorm_eq_norm]
  exact mul_le_mul_of_nonneg_left
    (norm_orderedMatrixCpow_regularize_right_le L hL hε t)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- A fixed uniform Schatten bound for an unregularized PSD ordered family. -/
private theorem schattenNorm_orderedMatrixCpow_right_le
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef)
    {p : ℝ} (hp : 0 < p) (t : ℝ) :
    schattenNorm (ENNReal.ofReal p) (orderedMatrixCpow L (1 + (t : ℂ) * I)) ≤
      (Fintype.card n : ℝ) ^ (1 / p) * (L.map (fun A => ‖A‖ + 1)).prod := by
  simpa only [regularizeMatrixList_zero] using
    schattenNorm_orderedMatrixCpow_regularize_right_le L hL hp
      (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num) t

private noncomputable abbrev boundaryNorm (L : List (Matrix n n ℂ)) (p t : ℝ) : ℝ :=
  schattenNorm (ENNReal.ofReal p) (orderedMatrixCpow L (1 + (t : ℂ) * I))

private theorem abs_log_add_le {x C δ : ℝ} (hx : 0 ≤ x) (hC : x ≤ C) (hδ : 0 < δ) :
    |Real.log (x + δ)| ≤ |Real.log δ| + |Real.log (C + δ)| := by
  have hlo := Real.log_le_log hδ (show δ ≤ x + δ by linarith)
  have hhi := Real.log_le_log (add_pos_of_nonneg_of_pos hx hδ)
    (show x + δ ≤ C + δ by linarith)
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log δ), abs_nonneg (Real.log (C + δ))],
    by linarith [le_abs_self (Real.log (C + δ)), abs_nonneg (Real.log δ)]⟩

private theorem continuous_log_boundaryNorm_add (L : List (Matrix n n ℂ))
    (hL : ∀ A ∈ L, A.PosSemidef) {p δ : ℝ} (hp : 1 ≤ p) (hδ : 0 < δ) :
    Continuous (fun t => Real.log (boundaryNorm L p t + δ)) := by
  apply Continuous.log
  · exact ((continuous_schattenNorm (ENNReal.one_le_ofReal.mpr hp)).comp
      (continuous_orderedMatrixCpow_right L hL)).add continuous_const
  · exact fun _ => (add_pos_of_nonneg_of_pos (schattenNorm_nonneg _ _) hδ).ne'

/-- For positive definite factors, the right-boundary logarithm of their Schatten norm is
integrable under any finite measure. In positive dimension this follows from uniform product
and inverse bounds. In dimension zero the integrand is identically zero. -/
theorem integrable_log_schattenNorm_orderedMatrixCpow
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosDef) {p : ℝ} (hp : 0 < p)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun t : ℝ => Real.log (schattenNorm (ENNReal.ofReal p)
      (orderedMatrixCpow L (1 + (t : ℂ) * I)))) μ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hz (t : ℝ) : orderedMatrixCpow L (1 + (t : ℂ) * I) = 0 := Subsingleton.elim _ _
    simp only [hz, schattenNorm_zero, Real.log_zero]
    exact integrable_zero ℝ ℝ μ
  · simp_rw [orderedMatrixCpow_eq_orderedMatrixExp_log L hL]
    let H := L.map (cfc Real.log)
    have hH : ∀ A ∈ H, A.IsHermitian := isHermitian_mem_map_log L
    exact ⟨(continuous_log_schattenNorm_orderedMatrixExp H hH hp).aestronglyMeasurable,
      .of_bounded (ae_of_all _ fun t => abs_log_schattenNorm_orderedMatrixExp_le H hH hp t)⟩

/-- **Positive definite Araki–Lieb–Thirring inequality.** For $p\ge1$ and $0<r<1$,
$$
\left\|\left\lvert\prod_j A_j^r\right\rvert^{1/r}\right\|_{S_p}
\le \exp\!\left(\int \log\left\|\prod_j A_j^{1+it}\right\|_{S_p}\,d\mu_r(t)\right).
$$
The inverse product bounds the right-boundary norm away from zero on a nonempty space,
so its real logarithm is integrable. In dimension zero, Mathlib's $\log 0=0$ convention
reduces the bound to $0\le 1$. [SutterBertaTomamichel2017, Theorem 3.2].
Result: multivariate-araki-lieb-thirring -/
theorem schattenNorm_rpow_abs_prod_rpow_le_exp_integral_log
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosDef) {p r : ℝ}
    (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) :
    schattenNorm (ENNReal.ofReal p) ((CFC.abs (L.map (fun A => A ^ r)).prod) ^ (1 / r)) ≤
      Real.exp (∫ t, Real.log (schattenNorm (ENNReal.ofReal p)
        (orderedMatrixCpow L (1 + (t : ℂ) * I))) ∂Real.stripHarmonicMeasure r) := by
  rw [← orderedMatrixCpow_ofReal_eq_prod_rpow L (fun A hA => (hL A hA).posSemidef)]
  simpa only [orderedMatrixCpow_eq_orderedMatrixExp_log L hL] using
    schattenNorm_rpow_abs_orderedMatrixExp_le_exp_integral (L.map (cfc Real.log))
      (isHermitian_mem_map_log L) hp hr

/-- The positive definite inequality survives a positive displacement of the logarithm.
The inverse exponential family bounds the negative part of the original logarithm. -/
private theorem schattenNorm_rpow_abs_orderedMatrixCpow_le_exp_integral_log_add_of_posDef
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosDef) {p r δ : ℝ}
    (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) (hδ : 0 < δ) :
    schattenNorm (ENNReal.ofReal p) ((CFC.abs (orderedMatrixCpow L (r : ℂ))) ^ (1 / r)) ≤
      Real.exp (∫ t, Real.log (boundaryNorm L p t + δ) ∂Real.stripHarmonicMeasure r) := by
  by_cases hn : Nonempty n
  · let := hn
    let H := L.map (cfc Real.log)
    have hH : ∀ A ∈ H, A.IsHermitian := isHermitian_mem_map_log L
    have hp0 := zero_lt_one.trans_le hp
    have he (z : ℂ) : orderedMatrixExp H z = orderedMatrixCpow L z :=
      (orderedMatrixCpow_eq_orderedMatrixExp_log L hL z).symm
    have h := schattenNorm_rpow_abs_prod_rpow_le_exp_integral_log L hL hp hr
    rw [← orderedMatrixCpow_ofReal_eq_prod_rpow L (fun A hA => (hL A hA).posSemidef)] at h
    apply h.trans
    apply Real.exp_le_exp.mpr
    let := Real.isProbabilityMeasure_stripHarmonicMeasure hr
    apply integral_mono
    · exact integrable_log_schattenNorm_orderedMatrixCpow L hL hp0 _
    · exact ⟨(continuous_log_boundaryNorm_add L (fun A hA => (hL A hA).posSemidef)
        hp hδ).aestronglyMeasurable, .of_bounded (ae_of_all _ fun t =>
          abs_log_add_le (schattenNorm_nonneg _ _) (schattenNorm_orderedMatrixCpow_right_le L
            (fun A hA => (hL A hA).posSemidef) (zero_lt_one.trans_le hp) t) hδ)⟩
    · intro t
      have hpos := (Real.exp_pos _).trans_le
        ((exp_neg_sum_specNorm_le_specNorm_orderedMatrixExp H hH t).trans
          (specNorm_le_schattenNorm (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans_le hp)) _))
      dsimp only
      rw [he] at hpos
      exact Real.log_le_log hpos (le_add_of_nonneg_right hδ.le)
  · let : IsEmpty n := not_nonempty_iff.mp hn
    have hz (A : Matrix n n ℂ) : A = 0 := Subsingleton.elim _ _
    rw [hz (_ ^ (1 / r : ℝ)), schattenNorm_zero]
    exact (Real.exp_pos _).le

/-- For a fixed positive displacement of the logarithm, the boundary integrals converge under
scalar regularization of each factor. The strip probability measure gives a constant majorant. -/
private theorem tendsto_integral_log_boundaryNorm_add (L : List (Matrix n n ℂ))
    (hL : ∀ A ∈ L, A.PosSemidef) {p r δ : ℝ} (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1)
    (hδ : 0 < δ) {ε : ℕ → ℝ} (hε : ∀ k, ε k ∈ Icc (0 : ℝ) 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ t, Real.log (boundaryNorm (regularizeMatrixList L (ε k)) p t + δ)
      ∂Real.stripHarmonicMeasure r) atTop
        (𝓝 (∫ t, Real.log (boundaryNorm L p t + δ) ∂Real.stripHarmonicMeasure r)) := by
  let := Real.isProbabilityMeasure_stripHarmonicMeasure hr
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall fun k =>
      (continuous_log_boundaryNorm_add _ (posSemidef_mem_regularizeMatrixList L hL (hε k).1)
        hp hδ).aestronglyMeasurable
  · exact ⟨_, Eventually.of_forall fun k => ae_of_all _ fun t =>
      abs_log_add_le (schattenNorm_nonneg _ _) (schattenNorm_orderedMatrixCpow_regularize_right_le
        L hL (zero_lt_one.trans_le hp) (hε k) t) hδ⟩
  · exact ae_of_all _ fun t => by
      have hm := (continuousAt_orderedMatrixCpow_regularize L (fun A hA => (hL A hA).isHermitian)
        (z := 1 + (t : ℂ) * I) (by simp)).tendsto.comp hεlim
      simp only [Function.comp_def, regularizeMatrixList_zero] at hm
      have hn := ((continuous_schattenNorm (ENNReal.one_le_ofReal.mpr hp)).tendsto _).comp hm
      exact (Real.continuousAt_log
        (add_pos_of_nonneg_of_pos (schattenNorm_nonneg _ _) hδ).ne').tendsto.comp (hn.add_const δ)

/-- Remove the positive matrix shifts while retaining the regularized logarithm. -/
private theorem schattenNorm_rpow_abs_orderedMatrixCpow_le_exp_integral_log_add
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef) {p r δ : ℝ}
    (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) (hδ : 0 < δ) :
    schattenNorm (ENNReal.ofReal p) ((CFC.abs (orderedMatrixCpow L (r : ℂ))) ^ (1 / r)) ≤
      Real.exp (∫ t, Real.log (boundaryNorm L p t + δ) ∂Real.stripHarmonicMeasure r) := by
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hε (k : ℕ) : ε k ∈ Icc (0 : ℝ) 1 :=
    ⟨(hεpos k).le, (div_le_one (by positivity : 0 < (k : ℝ) + 1)).mpr
      (by linarith [Nat.cast_nonneg (α := ℝ) k])⟩
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc := (continuousAt_orderedMatrixCpow_regularize L (fun A hA => (hL A hA).isHermitian)
    (z := (r : ℂ)) (by simpa using hr.1)).tendsto.comp hεlim
  simp only [Function.comp_def, regularizeMatrixList_zero] at hc
  have hs := one_div_pos.mpr hr.1
  have hq : 1 ≤ (1 / r) * p := one_le_mul_of_one_le_of_one_le
    ((one_le_div hr.1).mpr hr.2.le) hp
  have hl := (((continuous_schattenNorm (ENNReal.one_le_ofReal.mpr hq)).tendsto _).comp hc
    ).rpow_const (Or.inr hs.le)
  have hg := Real.continuous_exp.continuousAt.tendsto.comp
    (tendsto_integral_log_boundaryNorm_add L hL hp hr hδ hε hεlim)
  rw [schattenNorm_rpow_abs _ (zero_lt_one.trans_le hp) hs]
  apply le_of_tendsto_of_tendsto hl hg
  apply Eventually.of_forall
  intro k
  have hh := schattenNorm_rpow_abs_orderedMatrixCpow_le_exp_integral_log_add_of_posDef
    _ (posDef_mem_regularizeMatrixList L hL (hεpos k)) hp hr hδ
  rwa [schattenNorm_rpow_abs _ (zero_lt_one.trans_le hp) hs] at hh

/-- **Multivariate Araki–Lieb–Thirring.** For positive semidefinite factors $A_j$, $p \ge 1$
and $0 < r < 1$, with both products in the given order,
$$
\log \left\|\left\lvert\prod_j A_j^r\right\rvert^{1/r}\right\|_{S_p}
\le \int_{\mathbb{R}} \beta_r(t) \log \left\|\prod_j A_j^{1+it}\right\|_{S_p}\,dt.
$$
Here $\beta_r$ is the strip Poisson density and the extended logarithm takes the value
$-\infty$ at zero. [SutterBertaTomamichel2017, Theorem 3.2].
The formal proof adapts `tchen-research/NLAlib@77514ce`.
Result: multivariate-araki-lieb-thirring -/
theorem log_schattenNorm_rpow_abs_prod_rpow_le_extendedLogIntegral
    (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, A.PosSemidef)
    {p r : ℝ} (hp : 1 ≤ p) (hr : r ∈ Ioo (0 : ℝ) 1) :
    ENNReal.log (ENNReal.ofReal (schattenNorm (ENNReal.ofReal p)
        ((CFC.abs (L.map (fun A => A ^ r)).prod) ^ (1 / r)))) ≤
      extendedLogIntegral (Real.stripHarmonicMeasure r)
        (fun t => schattenNorm (ENNReal.ofReal p) (orderedMatrixCpow L (1 + (t : ℂ) * I))) := by
  let := Real.isProbabilityMeasure_stripHarmonicMeasure hr
  apply log_le_extendedLogIntegral_of_le_exp_integral_log_add
  · exact ((continuous_schattenNorm (ENNReal.one_le_ofReal.mpr hp)).comp
      (continuous_orderedMatrixCpow_right L hL)).measurable
  · intro t
    exact ⟨schattenNorm_nonneg _ _, schattenNorm_orderedMatrixCpow_right_le L hL
      (zero_lt_one.trans_le hp) t⟩
  · intro δ hδ
    rw [← orderedMatrixCpow_ofReal_eq_prod_rpow L hL]
    exact schattenNorm_rpow_abs_orderedMatrixCpow_le_exp_integral_log_add L hL hp hr hδ

end NLAlib
