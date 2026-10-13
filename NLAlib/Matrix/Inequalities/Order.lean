/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Spectral.Weyl
public import NLAlib.Matrix.Spectral.SingularValues
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Basic.SchurComplement

/-!
# Consequences of the Loewner order

Monotonicity of the trace, the determinant and the inverse in the Loewner order, with their
equality cases; invariance of the order under congruence; compressions of inverses; spectral
equivalence `a • M ≤ A ≤ b • M`, which is how the quality of a preconditioner `M` is stated, with
its consequence for the condition number of the preconditioned matrix and its description through
the spectrum of `M⁻¹ * A` (the generalized eigenvalues of the pair).

## Main results

* `NLAlib.re_trace_le_re_trace_of_le`, `NLAlib.eq_of_le_of_re_trace_eq`.
* `Matrix.PosSemidef.re_det_le_re_det_of_le`, `Matrix.PosDef.eq_of_le_of_det_eq`.
* `NLAlib.conjTranspose_mul_mul_le_conjTranspose_mul_mul_iff`: congruence by an invertible matrix.
* `Matrix.PosDef.inv_le_inv_of_le`: the inverse is order-reversing.
* `Matrix.PosDef.inv_conjTranspose_mul_mul_le`: the inverse of a compression.
* `Matrix.PosDef.exists_pos_smul_one_le`: a positive definite matrix dominates a positive
  multiple of the identity.
* `NLAlib.conditionNumber_conjTranspose_mul_mul_le_div`: the condition number of a preconditioned
  matrix.
* `Matrix.PosDef.smul_le_and_le_smul_iff_spectrum_subset`: spectral equivalence through the
  generalized eigenvalues.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-! ### Trace and determinant -/

omit [DecidableEq n] in
/-- The trace is monotone in the Loewner order. Port of `NLAlib.trace_le_of_le`. -/
theorem re_trace_le_re_trace_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) :
    RCLike.re A.trace ≤ RCLike.re B.trace := by
  have h' := (Matrix.le_iff.mp h).re_trace_nonneg
  rw [Matrix.trace_sub, map_sub] at h'
  linarith

omit [DecidableEq n] in
/-- Loewner-ordered matrices with the same trace are equal.
Port of `NLAlib.trace_eq_iff_of_le`. -/
theorem eq_of_le_of_re_trace_eq {A B : Matrix n n 𝕜} (h : A ≤ B)
    (ht : RCLike.re A.trace = RCLike.re B.trace) : A = B := by
  have h' := (Matrix.le_iff.mp h).re_trace_eq_zero_iff.mp
    (by rw [Matrix.trace_sub, map_sub, ht, sub_self])
  exact (sub_eq_zero.mp h').symm

/-- The determinant of a Hermitian matrix is real. -/
theorem _root_.Matrix.IsHermitian.det_eq_re_det {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A.det = ((RCLike.re A.det : ℝ) : 𝕜) := by
  rw [eq_comm, ← RCLike.conj_eq_iff_re, ← RCLike.star_def, ← Matrix.det_conjTranspose, hA.eq]

/-- **The determinant is monotone on positive semidefinite matrices.**
[HornJohnson2013, Corollary 7.7.4]. Port of `NLAlib.det_le_det_of_posSemidef_le`. -/
theorem _root_.Matrix.PosSemidef.re_det_le_re_det_of_le {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (h : A ≤ B) : RCLike.re A.det ≤ RCLike.re B.det := by
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (hA.nonneg.trans h)
  rw [hA.isHermitian.det_eq_prod_range_eigenvalue, hB.isHermitian.det_eq_prod_range_eigenvalue,
    RCLike.ofReal_re, RCLike.ofReal_re]
  exact Finset.prod_le_prod (fun k _ => hA.eigenvalue_nonneg k)
    fun k _ => eigenvalue_le_eigenvalue_of_le h hA.isHermitian k

/-- Equality in the monotonicity of the determinant: if `B ≤ A` with `A` positive definite, `B`
positive semidefinite and `det B = det A`, then `B = A`.
[HornJohnson2013, Corollary 7.7.4]. Port of `NLAlib.det_eq_iff_eq_of_posSemidef_le_posDef`. -/
theorem _root_.Matrix.PosDef.eq_of_le_of_det_eq {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.PosSemidef) (h : B ≤ A) (hdet : B.det = A.det) : B = A := by
  refine eq_of_le_of_re_trace_eq h ?_
  rw [hB.isHermitian.re_trace_eq_sum_range_eigenvalue,
    hA.isHermitian.re_trace_eq_sum_range_eigenvalue]
  have hle : ∀ k, eigenvalue B k ≤ eigenvalue A k :=
    eigenvalue_le_eigenvalue_of_le h hB.isHermitian
  have hprod : ∏ k ∈ Finset.range (Fintype.card n), eigenvalue B k =
      ∏ k ∈ Finset.range (Fintype.card n), eigenvalue A k := by
    rw [hB.isHermitian.det_eq_prod_range_eigenvalue,
      hA.isHermitian.det_eq_prod_range_eigenvalue] at hdet
    exact_mod_cast hdet
  have hApos : 0 < ∏ k ∈ Finset.range (Fintype.card n), eigenvalue A k :=
    Finset.prod_pos fun i hi =>
      hA.isHermitian.posDef_iff_eigenvalue_pos.mp hA i (Finset.mem_range.mp hi)
  have hBpos : ∀ j ∈ Finset.range (Fintype.card n), 0 < eigenvalue B j := by
    intro j hj
    refine lt_of_le_of_ne (hB.eigenvalue_nonneg j) fun h0 => ?_
    have h1 : ∏ k ∈ Finset.range (Fintype.card n), eigenvalue B k = 0 :=
      Finset.prod_eq_zero hj h0.symm
    linarith
  refine Finset.sum_congr rfl fun k hk => ?_
  by_contra hne
  exact (Finset.prod_lt_prod hBpos (fun i _ => hle i) ⟨k, hk, lt_of_le_of_ne (hle k) hne⟩).ne
    hprod

/-! ### Congruence and inverses -/

/-- **Congruence by an invertible matrix preserves and reflects the Loewner order.**
Port of `NLAlib.congruence_le_congruence_iff`. -/
theorem conjTranspose_mul_mul_le_conjTranspose_mul_mul_iff {A B S : Matrix n n 𝕜}
    (hS : IsUnit S) : Sᴴ * A * S ≤ Sᴴ * B * S ↔ A ≤ B := by
  rw [Matrix.le_iff, Matrix.le_iff, ← Matrix.sub_mul, ← Matrix.mul_sub]
  exact Matrix.IsUnit.posSemidef_star_left_conjugate_iff hS

/-- For positive definite `A`, the block matrix `[A 1; 1 A⁻¹]` is positive semidefinite. -/
private theorem posSemidef_fromBlocks_one_one_inv {A : Matrix n n 𝕜} (hA : A.PosDef) :
    (Matrix.fromBlocks A 1 (1 : Matrix n n 𝕜)ᴴ A⁻¹).PosSemidef := by
  have hAA : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  refine posSemidef_fromBlocks_iff_exists.mpr ⟨hA.posSemidef, A⁻¹, hAA, ?_⟩
  rw [hA.isHermitian.inv.eq, Matrix.mul_assoc, hAA, Matrix.mul_one, sub_self]
  exact Matrix.PosSemidef.zero

/-- If `[M 1; 1 C]` is positive semidefinite with `M` invertible, then `M⁻¹ ≤ C`. -/
private theorem inv_le_of_posSemidef_fromBlocks_one {M C : Matrix n n 𝕜} (hM : IsUnit M)
    (h : (Matrix.fromBlocks M 1 (1 : Matrix n n 𝕜)ᴴ C).PosSemidef) : M⁻¹ ≤ C := by
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hM)
  have hMh : M.IsHermitian := by
    have h' := h.isHermitian
    rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose] at h'
    exact (Matrix.fromBlocks_inj.mp h').1
  have h' := posSemidef_sub_conjTranspose_mul_mul_of_posSemidef_fromBlocks h hMM
  rw [hMh.inv.eq, Matrix.mul_assoc, hMM, Matrix.mul_one] at h'
  exact Matrix.le_iff.mpr h'

/-- **The inverse is order-reversing** on positive definite matrices.
[HornJohnson2013, Corollary 7.7.4]. -/
theorem _root_.Matrix.PosDef.inv_le_inv_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hB : B.PosDef := by
    have h' := hA.add_posSemidef (Matrix.le_iff.mp h)
    rwa [add_sub_cancel] at h'
  refine inv_le_of_posSemidef_fromBlocks_one hB.isUnit ?_
  have h0 : (Matrix.fromBlocks (B - A) 0 (0 : Matrix n n 𝕜)ᴴ 0).PosSemidef :=
    posSemidef_fromBlocks_iff_exists.mpr
      ⟨Matrix.le_iff.mp h, 0, by simp, by simp [Matrix.PosSemidef.zero]⟩
  have h' := (posSemidef_fromBlocks_one_one_inv hA).add h0
  simpa [Matrix.fromBlocks_add] using h'

/-- The inverse of a positive definite matrix is bounded by the reciprocal of a lower bound:
`a • 1 ≤ A` with `0 < a` gives `A⁻¹ ≤ a⁻¹ • 1`. -/
theorem inv_le_inv_smul_one_of_smul_one_le {A : Matrix n n 𝕜} {a : ℝ} (ha : 0 < a)
    (h : a • (1 : Matrix n n 𝕜) ≤ A) : A⁻¹ ≤ a⁻¹ • (1 : Matrix n n 𝕜) := by
  have hpd : (a • (1 : Matrix n n 𝕜)).PosDef := Matrix.PosDef.one.smul ha
  have h' := hpd.inv_le_inv_of_le h
  have e : (a • (1 : Matrix n n 𝕜))⁻¹ = a⁻¹ • (1 : Matrix n n 𝕜) :=
    Matrix.inv_eq_right_inv (by
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ ha.ne', one_smul])
  rwa [e] at h'

/-- **The inverse of a compression is at most the compression of the inverse**:
`(Vᴴ A V)⁻¹ ≤ Vᴴ A⁻¹ V` for positive definite `A` and `V` with orthonormal columns.
[HornJohnson2013, Theorem 7.7.8 context].
Port of `NLAlib.inv_compression_le_compression_inv`. -/
theorem _root_.Matrix.PosDef.inv_conjTranspose_mul_mul_le {A : Matrix m m 𝕜} (hA : A.PosDef)
    {V : Matrix m n 𝕜} (hV : HasOrthonormalCols V) : (Vᴴ * A * V)⁻¹ ≤ Vᴴ * A⁻¹ * V := by
  have hM : (Vᴴ * A * V).PosDef := hA.conjTranspose_mul_mul_same hV.mulVec_injective
  have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdet
  refine inv_le_of_posSemidef_fromBlocks_one hM.isUnit ?_
  have h := hA.posSemidef.conjTranspose_mul_mul_same (Matrix.fromCols V (A⁻¹ * V))
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul,
    Matrix.fromRows_mul_fromCols] at h
  have e1 : Vᴴ * A * (A⁻¹ * V) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, hAA, Matrix.one_mul, hV.conjTranspose_mul_self]
  have e2 : (A⁻¹ * V)ᴴ * A * V = 1 := by
    rw [Matrix.conjTranspose_mul, hA.isHermitian.inv.eq, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc A⁻¹, Matrix.nonsing_inv_mul A hdet, Matrix.one_mul,
      hV.conjTranspose_mul_self]
  have e3 : (A⁻¹ * V)ᴴ * A * (A⁻¹ * V) = Vᴴ * A⁻¹ * V := by
    rw [Matrix.conjTranspose_mul, hA.isHermitian.inv.eq, Matrix.mul_assoc, ← Matrix.mul_assoc A,
      hAA, Matrix.one_mul]
  rw [e1, e2, e3] at h
  rwa [Matrix.conjTranspose_one]

/-- The inverse of a principal submatrix is at most the principal submatrix of the inverse.
[HornJohnson2013, Theorem 7.7.8]. Port of `NLAlib.inv_submatrix_le_submatrix_inv`. -/
theorem _root_.Matrix.PosDef.inv_submatrix_le {A : Matrix m m 𝕜} (hA : A.PosDef) {f : n → m}
    (hf : Function.Injective f) : (A.submatrix f f)⁻¹ ≤ A⁻¹.submatrix f f := by
  have hV : HasOrthonormalCols ((1 : Matrix m m 𝕜).submatrix id f) :=
    hasOrthonormalCols_one.submatrix (Equiv.refl m) hf
  have e : ∀ M : Matrix m m 𝕜,
      ((1 : Matrix m m 𝕜).submatrix id f)ᴴ * M * (1 : Matrix m m 𝕜).submatrix id f =
        M.submatrix f f := by
    intro M
    ext i j
    simp [Matrix.mul_apply, Matrix.one_apply]
  have h := hA.inv_conjTranspose_mul_mul_le hV
  rwa [e, e] at h

/-! ### Comparison with the identity -/

/-- A positive semidefinite matrix is at most the identity exactly when its spectral norm is at
most one. Port of `NLAlib.le_one_iff_specNorm_le_one_of_posSemidef`. -/
theorem _root_.Matrix.PosSemidef.le_one_iff_specNorm_le_one {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : A ≤ 1 ↔ specNorm A ≤ 1 := by
  rw [hA.specNorm_le_iff zero_le_one, one_smul]

/-- For positive semidefinite `A`, `1 - A` is positive definite exactly when `‖A‖₂ < 1`.
Port of `NLAlib.posDef_one_sub_iff_specNorm_lt_one_of_posSemidef`. -/
theorem _root_.Matrix.PosSemidef.posDef_one_sub_iff_specNorm_lt_one {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : (1 - A).PosDef ↔ specNorm A < 1 := by
  have hH : (1 - A).IsHermitian := Matrix.isHermitian_one.sub hA.isHermitian
  have hq : ∀ x : n → 𝕜, RCLike.re (quadForm (1 - A) x) =
      ‖WithLp.toLp 2 x‖ ^ 2 - RCLike.re (quadForm A x) := by
    intro x
    rw [quadForm_sub_left, map_sub, quadForm_one, RCLike.ofReal_re]
  constructor
  · intro h
    rcases isEmpty_or_nonempty n with hn | hn
    · rw [Subsingleton.elim A 0, specNorm_zero]
      exact zero_lt_one
    · obtain ⟨u, hu, hAu⟩ := hA.exists_norm_eq_one_and_mulVec_eq_specNorm_smul
      have hu0 : u ≠ 0 := by
        rintro rfl
        simp at hu
      have hpos := h.re_quadForm_pos hu0
      have hre : RCLike.re (quadForm A u) = specNorm A := by
        rw [← rayleighQuotient_of_norm_eq_one A hu, rayleighQuotient_of_mulVec_eq_smul
          (c := (specNorm A : 𝕜)) (by rw [hAu, RCLike.real_smul_eq_coe_smul (K := 𝕜)]) hu0,
          RCLike.ofReal_re]
      rw [hq, hu, hre] at hpos
      linarith
  · intro h
    rw [posDef_iff_quadForm_pos]
    refine ⟨hH, fun x hx => ?_⟩
    rw [← hH.coe_re_quadForm, hq, RCLike.ofReal_pos]
    have hx' : 0 < ‖WithLp.toLp 2 x‖ ^ 2 := by
      have : WithLp.toLp 2 x ≠ 0 := by simpa using hx
      positivity
    have h1 := (le_abs_self _).trans (abs_re_quadForm_le A x)
    nlinarith

omit [Fintype n] in
/-- **A positive definite matrix dominates a positive multiple of the identity**: `a • 1 ≤ A`
for some `a > 0`. The largest such `a` is the smallest eigenvalue of `A`; the one produced here
is `(‖A⁻¹‖₂ + 1)⁻¹`. -/
theorem _root_.Matrix.PosDef.exists_pos_smul_one_le [Finite n] {A : Matrix n n 𝕜}
    (hA : A.PosDef) : ∃ a : ℝ, 0 < a ∧ a • (1 : Matrix n n 𝕜) ≤ A := by
  have := Fintype.ofFinite n
  have hc : 0 < specNorm A⁻¹ + 1 := add_pos_of_nonneg_of_pos (specNorm_nonneg _) one_pos
  have h := hA.inv.inv_le_inv_of_le
    (hA.inv.isHermitian.le_smul_one_of_specNorm_le (le_add_of_nonneg_right zero_le_one))
  have e : ((specNorm A⁻¹ + 1) • (1 : Matrix n n 𝕜))⁻¹ =
      (specNorm A⁻¹ + 1)⁻¹ • (1 : Matrix n n 𝕜) :=
    Matrix.inv_eq_right_inv (by
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul])
  rw [e, Matrix.nonsing_inv_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)] at h
  exact ⟨_, inv_pos.mpr hc, h⟩

/-! ### Spectral equivalence -/

private theorem conditionNumber_le_div_aux [Nonempty n] {A : Matrix n n 𝕜} {a b : ℝ}
    (ha : 0 < a) (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) :
    conditionNumber A ≤ b / a := by
  have hA : A.PosDef := by
    have h := (Matrix.PosDef.one.smul ha).add_posSemidef (Matrix.le_iff.mp h₁)
    rwa [add_sub_cancel] at h
  have hb : 0 ≤ b :=
    (hA.posSemidef.eigenvalue_nonneg 0).trans (hA.isHermitian.le_smul_one_iff.mp h₂)
  rw [conditionNumber_of_isUnit hA.isUnit, div_eq_mul_inv]
  exact mul_le_mul ((hA.posSemidef.specNorm_le_iff hb).mpr h₂)
    ((hA.posSemidef.inv.specNorm_le_iff (inv_nonneg.mpr ha.le)).mpr
      (inv_le_inv_smul_one_of_smul_one_le ha h₁)) (specNorm_nonneg _) hb

/-- A Hermitian matrix between `a • 1` and `b • 1` with `0 < a` has condition number at most
`b / a`. -/
theorem conditionNumber_le_div_of_smul_one_le_of_le_smul_one {A : Matrix n n 𝕜} {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (h₁ : a • (1 : Matrix n n 𝕜) ≤ A)
    (h₂ : A ≤ b • (1 : Matrix n n 𝕜)) : conditionNumber A ≤ b / a := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Subsingleton.elim A 0, conditionNumber_zero]
    exact div_nonneg hb ha.le
  · exact conditionNumber_le_div_aux ha h₁ h₂

/-- **Spectral equivalence, lower half, after a change of variables.** If `Cᴴ * M * C = 1`
(for instance `C = M^{-1/2}`, or the inverse of a Cholesky factor), then `a • M ≤ A` exactly when
`a • 1 ≤ Cᴴ * A * C`. -/
theorem smul_le_iff_smul_one_le_conjTranspose_mul_mul {A M C : Matrix n n 𝕜}
    (hC : Cᴴ * M * C = 1) {a : ℝ} : a • M ≤ A ↔ a • (1 : Matrix n n 𝕜) ≤ Cᴴ * A * C := by
  rw [← conjTranspose_mul_mul_le_conjTranspose_mul_mul_iff
    ((Matrix.isUnit_iff_isUnit_det C).mpr (Matrix.isUnit_det_of_left_inverse hC)),
    Matrix.mul_smul, Matrix.smul_mul, hC]

/-- Spectral equivalence, upper half, after a change of variables: if `Cᴴ * M * C = 1`, then
`A ≤ b • M` exactly when `Cᴴ * A * C ≤ b • 1`. -/
theorem le_smul_iff_conjTranspose_mul_mul_le_smul_one {A M C : Matrix n n 𝕜}
    (hC : Cᴴ * M * C = 1) {b : ℝ} : A ≤ b • M ↔ Cᴴ * A * C ≤ b • (1 : Matrix n n 𝕜) := by
  rw [← conjTranspose_mul_mul_le_conjTranspose_mul_mul_iff
    ((Matrix.isUnit_iff_isUnit_det C).mpr (Matrix.isUnit_det_of_left_inverse hC)),
    Matrix.mul_smul, Matrix.smul_mul, hC]

/-- **The condition number of a preconditioned matrix.** If `a • M ≤ A ≤ b • M` with `0 < a` and
`Cᴴ * M * C = 1`, the symmetrically preconditioned matrix `Cᴴ * A * C` has condition number at
most `b / a`. This is the statement that conjugate gradient rates consume.
Result: preconditioned-condition-number -/
theorem conditionNumber_conjTranspose_mul_mul_le_div {A M C : Matrix n n 𝕜}
    (hC : Cᴴ * M * C = 1) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (h₁ : a • M ≤ A)
    (h₂ : A ≤ b • M) : conditionNumber (Cᴴ * A * C) ≤ b / a := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Subsingleton.elim (Cᴴ * A * C) 0, conditionNumber_zero]
    exact div_nonneg hb ha.le
  · exact conditionNumber_le_div_aux ha
      ((smul_le_iff_smul_one_le_conjTranspose_mul_mul hC).mp h₁)
      ((le_smul_iff_conjTranspose_mul_mul_le_smul_one hC).mp h₂)

/-! ### Generalized eigenvalues -/

/-- A positive definite `A` is congruent to the identity by a matrix `C` such that `A⁻¹ * B` is
similar to `Cᴴ * B * C`. -/
private theorem exists_conjTranspose_mul_mul_eq_one_and_inv_mul_eq {A : Matrix n n 𝕜}
    (hA : A.PosDef) (B : Matrix n n 𝕜) :
    ∃ C : Matrix n n 𝕜, Cᴴ * A * C = 1 ∧
      ∃ u : (Matrix n n 𝕜)ˣ, A⁻¹ * B = u * (Cᴴ * B * C) * (u⁻¹ : (Matrix n n 𝕜)ˣ) := by
  have hS : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hSS : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSu : IsUnit (CFC.sqrt A) := by
    refine IsUnit.of_mul_eq_one (CFC.sqrt A * A⁻¹) ?_
    rw [← Matrix.mul_assoc, hSS,
      Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)]
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hSu
  have hSi : (CFC.sqrt A)⁻¹ᴴ = (CFC.sqrt A)⁻¹ := hS.inv.eq
  have hAinv : A⁻¹ = (CFC.sqrt A)⁻¹ * (CFC.sqrt A)⁻¹ := by
    rw [← Matrix.mul_inv_rev, hSS]
  refine ⟨(CFC.sqrt A)⁻¹, ?_, hSu.unit⁻¹, ?_⟩
  · calc (CFC.sqrt A)⁻¹ᴴ * A * (CFC.sqrt A)⁻¹
        = (CFC.sqrt A)⁻¹ * (CFC.sqrt A * CFC.sqrt A) * (CFC.sqrt A)⁻¹ := by rw [hSi, hSS]
      _ = 1 := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one,
          Matrix.nonsing_inv_mul _ hdet]
  · rw [hSi, inv_inv, Matrix.coe_units_inv, IsUnit.unit_spec, hAinv]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]

private theorem smul_one_le_iff_forall_le_spectrum {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    (a : ℝ) : a • (1 : Matrix n n 𝕜) ≤ H ↔ ∀ z ∈ spectrum ℝ H, a ≤ z := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
    refine iff_of_true (le_of_eq (Subsingleton.elim _ _)) fun z hz => ?_
    rw [hH.spectrum_eq_image_eigenvalue, h0] at hz
    simp at hz
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n := ⟨Fintype.card n - 1, by omega⟩
    rw [hH.smul_one_le_iff hk, hH.spectrum_eq_image_eigenvalue]
    constructor
    · rintro h z ⟨j, hj, rfl⟩
      exact h.trans (hH.eigenvalue_le_eigenvalue (by have := Set.mem_Iio.mp hj; omega) (by omega))
    · intro h
      exact h _ ⟨k, Set.mem_Iio.mpr (by omega), rfl⟩

private theorem le_smul_one_iff_forall_spectrum_le {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    (b : ℝ) : H ≤ b • (1 : Matrix n n 𝕜) ↔ ∀ z ∈ spectrum ℝ H, z ≤ b := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
    refine iff_of_true (le_of_eq (Subsingleton.elim _ _)) fun z hz => ?_
    rw [hH.spectrum_eq_image_eigenvalue, h0] at hz
    simp at hz
  · have : Nonempty n := Fintype.card_pos_iff.mp hpos
    rw [hH.le_smul_one_iff, hH.spectrum_eq_image_eigenvalue]
    constructor
    · rintro h z ⟨j, hj, rfl⟩
      exact (hH.eigenvalue_le_eigenvalue (Nat.zero_le j) (Set.mem_Iio.mp hj)).trans h
    · intro h
      exact h _ ⟨0, Set.mem_Iio.mpr hpos, rfl⟩

/-- **Spectral equivalence through generalized eigenvalues.** For positive definite `A` and
Hermitian `B`, `a • A ≤ B ≤ b • A` exactly when the spectrum of `A⁻¹ * B` lies in `[a, b]`.
[HornJohnson2013, Theorem 7.6.4 context].
Port of `NLAlib.loewner_sandwich_iff_relative_spectrum_subset`, there over `ℝ`.
Result: relative-spectrum -/
theorem _root_.Matrix.PosDef.smul_le_and_le_smul_iff_spectrum_subset {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.IsHermitian) (a b : ℝ) :
    a • A ≤ B ∧ B ≤ b • A ↔ spectrum ℝ (A⁻¹ * B) ⊆ Set.Icc a b := by
  obtain ⟨C, hC, u, hu⟩ := exists_conjTranspose_mul_mul_eq_one_and_inv_mul_eq hA B
  have hH := Matrix.isHermitian_conjTranspose_mul_mul C hB
  rw [hu, spectrum.units_conjugate, smul_le_iff_smul_one_le_conjTranspose_mul_mul hC,
    le_smul_iff_conjTranspose_mul_mul_le_smul_one hC, smul_one_le_iff_forall_le_spectrum hH,
    le_smul_one_iff_forall_spectrum_le hH]
  exact ⟨fun h z hz => ⟨h.1 z hz, h.2 z hz⟩,
    fun h => ⟨fun z hz => (h hz).1, fun z hz => (h hz).2⟩⟩

/-- The upper half: `B ≤ b • A` exactly when the spectrum of `A⁻¹ * B` is at most `b`.
Port of `NLAlib.le_smul_iff_relative_spectrum_upper`. -/
theorem _root_.Matrix.PosDef.le_smul_iff_forall_spectrum_le {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.IsHermitian) (b : ℝ) :
    B ≤ b • A ↔ ∀ z ∈ spectrum ℝ (A⁻¹ * B), z ≤ b := by
  obtain ⟨C, hC, u, hu⟩ := exists_conjTranspose_mul_mul_eq_one_and_inv_mul_eq hA B
  rw [hu, spectrum.units_conjugate, le_smul_iff_conjTranspose_mul_mul_le_smul_one hC,
    le_smul_one_iff_forall_spectrum_le (Matrix.isHermitian_conjTranspose_mul_mul C hB)]

/-- The lower half: `a • A ≤ B` exactly when the spectrum of `A⁻¹ * B` is at least `a`.
Port of `NLAlib.smul_le_iff_relative_spectrum_lower`. -/
theorem _root_.Matrix.PosDef.smul_le_iff_forall_le_spectrum {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.IsHermitian) (a : ℝ) :
    a • A ≤ B ↔ ∀ z ∈ spectrum ℝ (A⁻¹ * B), a ≤ z := by
  obtain ⟨C, hC, u, hu⟩ := exists_conjTranspose_mul_mul_eq_one_and_inv_mul_eq hA B
  rw [hu, spectrum.units_conjugate, smul_le_iff_smul_one_le_conjTranspose_mul_mul hC,
    smul_one_le_iff_forall_le_spectrum (Matrix.isHermitian_conjTranspose_mul_mul C hB)]

/-- The generalized eigenvalues of a positive definite pair are real: the spectrum of
`A⁻¹ * B` over `𝕜` consists of real numbers when `A` is positive definite and `B` Hermitian. -/
theorem _root_.Matrix.PosDef.spectrum_inv_mul_subset_range_ofReal {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.IsHermitian) :
    spectrum 𝕜 (A⁻¹ * B) ⊆ Set.range (fun r : ℝ => (r : 𝕜)) := by
  obtain ⟨C, -, u, hu⟩ := exists_conjTranspose_mul_mul_eq_one_and_inv_mul_eq hA B
  rw [hu, spectrum.units_conjugate,
    (Matrix.isHermitian_conjTranspose_mul_mul C hB).spectrum_eq_image_range]
  rintro _ ⟨r, -, rfl⟩
  exact ⟨r, rfl⟩

/-- `B² ≤ A²` exactly when `‖B A⁻¹‖₂ ≤ 1`, for positive definite `A` and Hermitian `B`.
Port of `NLAlib.sq_le_sq_iff_relative_specNorm_le_one`. -/
theorem _root_.Matrix.PosDef.sq_le_sq_iff_specNorm_mul_inv_le_one {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.IsHermitian) : B ^ 2 ≤ A ^ 2 ↔ specNorm (B * A⁻¹) ≤ 1 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have e1 : A⁻¹ᴴ * B ^ 2 * A⁻¹ = (B * A⁻¹)ᴴ * (B * A⁻¹) := by
    rw [Matrix.conjTranspose_mul, hB.eq, sq]
    simp only [Matrix.mul_assoc]
  have e2 : A⁻¹ᴴ * A ^ 2 * A⁻¹ = 1 := by
    rw [hA.isHermitian.inv.eq, sq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
      Matrix.one_mul, Matrix.mul_nonsing_inv _ hdet]
  rw [← conjTranspose_mul_mul_le_conjTranspose_mul_mul_iff (A := B ^ 2) (B := A ^ 2)
    (Matrix.isUnit_nonsing_inv_iff.mpr hA.isUnit), e1, e2, ← sq_le_one_iff₀ (specNorm_nonneg _),
    specNorm_sq_le_iff_conjTranspose_mul_self_le zero_le_one, one_smul]

end NLAlib
