/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecificLimits.Normed
public import NLAlib.Matrix.Norms.HermitianFrobenius
public import NLAlib.Matrix.Functions.PositivePart
public import NLAlib.ForMathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Symmetric operators on the positive semidefinite cone

For a self-adjoint real-linear operator on Hermitian matrices which preserves positive
semidefiniteness, a strict positive supersolution characterizes contraction in the Frobenius
norm. The inverse of the identity minus a contraction acts by its Neumann series.

## Main results

* `NLAlib.norm_lt_one_iff_exists_posDef_sub_map`: the strict supersolution criterion.
-/

@[expose] public section

open Matrix

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- PSD matrices have nonnegative real Frobenius pairing. -/
private theorem frobInner_nonneg_of_posSemidef {P Q : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ frobInner P Q := by
  classical
  rw [frobInner, hP.isHermitian.eq]
  exact RCLike.nonneg_iff.mp (hP.trace_mul_nonneg hQ) |>.1

omit [DecidableEq n] in
/-- Every Hermitian matrix splits as two orthogonal positive spectral parts. Their sum and
difference have the same Frobenius norm. -/
private theorem exists_posSemidef_parts {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ∃ P N : Matrix n n 𝕜, P.PosSemidef ∧ N.PosSemidef ∧
      H = P - N ∧ frobInner P N = 0 ∧ frobNorm (P + N) ^ 2 = frobNorm H ^ 2 := by
  classical
  let P := H⁺
  let N := H⁻
  have hP : P.PosSemidef := (Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg H))
  have hN : N.PosSemidef := (Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H))
  have hdiff : P - N = H := CFC.posPart_sub_negPart H hH.isSelfAdjoint
  have hPN : P * N = 0 := CFC.posPart_mul_negPart H
  have horth : frobInner P N = 0 := by simp only [frobInner, hP.isHermitian.eq, hPN,
    Matrix.trace_zero, map_zero]
  refine ⟨P, N, hP, hN, hdiff.symm, horth, ?_⟩
  rw [← hdiff, frobNorm_add_sq, frobNorm_sub_sq, horth]
  ring

omit [DecidableEq n] in
/-- A cone-positive real-linear map has a PSD Rayleigh majorant for every Hermitian test, with
exactly the same Frobenius norm. -/
private theorem exists_posSemidef_rayleigh_majorant
    (L : Matrix n n 𝕜 →ₗ[ℝ] Matrix n n 𝕜)
    (hL : ∀ P : Matrix n n 𝕜, P.PosSemidef → (L P).PosSemidef)
    {H : Matrix n n 𝕜} (hH : H.IsHermitian) :
    ∃ K : Matrix n n 𝕜, K.PosSemidef ∧ frobNorm K ^ 2 = frobNorm H ^ 2 ∧
      |frobInner H (L H)| ≤ frobInner K (L K) := by
  classical
  obtain ⟨P, N, hP, hN, hH, hi, hnorm⟩ := exists_posSemidef_parts hH
  refine ⟨P + N, hP.add hN, hnorm, ?_⟩
  rw [hH, map_sub, map_add]
  simp only [frobInner_add_left, frobInner_add_right, frobInner_sub_left, frobInner_sub_right]
  have hPP := frobInner_nonneg_of_posSemidef hP (hL P hP)
  have hPN := frobInner_nonneg_of_posSemidef hP (hL N hN)
  have hNP := frobInner_nonneg_of_posSemidef hN (hL P hP)
  have hNN := frobInner_nonneg_of_posSemidef hN (hL N hN)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end NLAlib

open Matrix

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] [Nonempty n]

omit [DecidableEq n] in
/-- A symmetric cone-positive operator on the Hermitian Frobenius space has a nonzero PSD
eigenmatrix at its operator norm. -/
private theorem exists_posSemidef_norm_eigenvector
    (T : hermitianFrobenius 𝕜 n →L[ℝ] hermitianFrobenius 𝕜 n)
    (hT : T.IsSymmetric)
    (hpos : ∀ x, (hermitianFrobeniusMatrix 𝕜 n x).PosSemidef →
      (hermitianFrobeniusMatrix 𝕜 n (T x)).PosSemidef) :
    ∃ x, x ≠ 0 ∧ (hermitianFrobeniusMatrix 𝕜 n x).PosSemidef ∧ T x = ‖T‖ • x := by
  classical
  let E := (hermitianFrobeniusEquiv 𝕜 n).symm.toLinearMap.comp
    (selfAdjointPart ℝ : Matrix n n 𝕜 →ₗ[ℝ] selfAdjoint (Matrix n n 𝕜))
  let L := hermitianFrobeniusMatrixLinear.comp (T.toLinearMap.comp E)
  have hE (x : hermitianFrobenius 𝕜 n) : E (hermitianFrobeniusMatrix 𝕜 n x) = x := by
    apply (hermitianFrobeniusEquiv 𝕜 n).injective
    apply Subtype.ext
    change (selfAdjointPart ℝ (hermitianFrobeniusMatrix 𝕜 n x) : Matrix n n 𝕜) =
      hermitianFrobeniusMatrix 𝕜 n x
    exact (isHermitian_hermitianFrobeniusMatrix x).isSelfAdjoint.coe_selfAdjointPart_apply ℝ
  have hL (x : hermitianFrobenius 𝕜 n) :
      L (hermitianFrobeniusMatrix 𝕜 n x) = hermitianFrobeniusMatrix 𝕜 n (T x) := by
    change hermitianFrobeniusMatrix 𝕜 n (T (E (hermitianFrobeniusMatrix 𝕜 n x))) = _
    rw [hE]
  have hLP (P : Matrix n n 𝕜) (hP : P.PosSemidef) : (L P).PosSemidef := by
    have hh := hpos (toHermitianFrobenius hP.isHermitian) hP
    rwa [← hL, Matrix.IsHermitian.hermitianFrobeniusMatrix_toHermitianFrobenius] at hh
  apply T.exists_norm_eigenvector_of_rayleigh_majorants hT
    (fun x => (hermitianFrobeniusMatrix 𝕜 n x).PosSemidef)
  intro x
  obtain ⟨K, hK, hKn, hKQ⟩ := exists_posSemidef_rayleigh_majorant L hLP
    (isHermitian_hermitianFrobeniusMatrix x)
  let y := toHermitianFrobenius hK.isHermitian
  refine ⟨y, hK, ?_, ?_⟩
  · rw [norm_eq_frobNorm, norm_eq_frobNorm]
    change frobNorm K = frobNorm (hermitianFrobeniusMatrix 𝕜 n x)
    exact (sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).mp hKn
  · have hLy : L K = hermitianFrobeniusMatrix 𝕜 n (T y) := hL y
    rw [hLy] at hKQ
    simpa only [ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
      inner_eq_frobInner, frobInner_comm, hL,
      Matrix.IsHermitian.hermitianFrobeniusMatrix_toHermitianFrobenius, y] using hKQ

end NLAlib

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- **Positive Neumann inverse.** If a Frobenius operator on Hermitian matrices preserves the
positive semidefinite cone and has norm below one, the inverse of the identity minus that
operator preserves the cone. [MontanariSaeed2026, Eqs. (108)–(109)].
Result: matrix-k-transform-stability -/
theorem posSemidef_inverse_one_sub_apply
    (L : hermitianFrobenius 𝕜 n →L[ℝ] hermitianFrobenius 𝕜 n)
    (hL : ∀ x, (hermitianFrobeniusMatrix 𝕜 n x).PosSemidef →
      (hermitianFrobeniusMatrix 𝕜 n (L x)).PosSemidef)
    (hnorm : ‖L‖ < 1) {x : hermitianFrobenius 𝕜 n}
    (hx : (hermitianFrobeniusMatrix 𝕜 n x).PosSemidef) :
    (hermitianFrobeniusMatrix 𝕜 n (Ring.inverse (1 - L) x)).PosSemidef := by
  classical
  rw [← geom_series_eq_inverse L hnorm]
  let Φ := (hermitianFrobeniusMatrixLinear :
    hermitianFrobenius 𝕜 n →ₗ[ℝ] Matrix n n 𝕜).toContinuousLinearMap
  have hp (j : ℕ) : (Φ ((L ^ j) x)).PosSemidef := by
    induction j with
    | zero =>
      change (hermitianFrobeniusMatrix 𝕜 n x).PosSemidef
      exact hx
    | succ j ih =>
      rw [pow_succ']
      exact hL _ ih
  let ev := ContinuousLinearMap.apply' (hermitianFrobenius 𝕜 n) (RingHom.id ℝ) x
  have hsum := (Φ.comp ev).hasSum
    (summable_geometric_of_norm_lt_one hnorm).hasSum
  have hclosed : IsClosed {A : Matrix n n 𝕜 | A.PosSemidef} := by
    simpa only [Set.Ici, Matrix.nonneg_iff_posSemidef] using
      (isClosed_Ici : IsClosed (Set.Ici (0 : Matrix n n 𝕜)))
  apply hclosed.mem_of_tendsto hsum.tendsto_sum_nat
  exact Filter.Eventually.of_forall fun j => Matrix.posSemidef_sum _ (fun i _ => hp i)

omit [DecidableEq n] in
/-- Applying the Neumann inverse solves the equation `(I-L)Y=X`. -/
theorem inverse_one_sub_apply_sub_map
    (L : hermitianFrobenius 𝕜 n →L[ℝ] hermitianFrobenius 𝕜 n) (hnorm : ‖L‖ < 1)
    (x : hermitianFrobenius 𝕜 n) :
    Ring.inverse (1 - L) x - L (Ring.inverse (1 - L) x) = x := by
  rw [← geom_series_eq_inverse L hnorm]
  exact congrArg (fun A : hermitianFrobenius 𝕜 n →L[ℝ] hermitianFrobenius 𝕜 n => A x)
    (mul_neg_geom_series L hnorm)

/-- The canonical identity supersolution obtained by the Neumann inverse dominates the identity
in Loewner order. -/
theorem one_le_inverse_one_sub_apply_one
    (L : hermitianFrobenius 𝕜 n →L[ℝ] hermitianFrobenius 𝕜 n)
    (hL : ∀ x, (hermitianFrobeniusMatrix 𝕜 n x).PosSemidef →
      (hermitianFrobeniusMatrix 𝕜 n (L x)).PosSemidef) (hnorm : ‖L‖ < 1) :
    (1 : Matrix n n 𝕜) ≤ hermitianFrobeniusMatrix 𝕜 n (Ring.inverse (1 - L) 1) := by
  let I : hermitianFrobenius 𝕜 n := 1
  let Y := Ring.inverse (1 - L) I
  have hY := posSemidef_inverse_one_sub_apply L hL hnorm (x := I) Matrix.PosSemidef.one
  have he := congrArg (hermitianFrobeniusMatrix 𝕜 n) (inverse_one_sub_apply_sub_map L hnorm I)
  change hermitianFrobeniusMatrix 𝕜 n Y - hermitianFrobeniusMatrix 𝕜 n (L Y) = 1 at he
  apply Matrix.le_iff.mpr
  have hh : hermitianFrobeniusMatrix 𝕜 n Y - 1 = hermitianFrobeniusMatrix 𝕜 n (L Y) := by
    exact sub_eq_iff_eq_add.mpr (eq_add_of_sub_eq' he)
  change (hermitianFrobeniusMatrix 𝕜 n Y - 1).PosSemidef
  rw [hh]
  exact hL Y hY

/-- Norm below one supplies a strictly positive supersolution. The canonical choice is the
Neumann inverse applied to the identity. -/
private theorem exists_posDef_supersolution_of_norm_lt_one
    (L : hermitianFrobenius 𝕜 n →L[ℝ] hermitianFrobenius 𝕜 n)
    (hL : ∀ x, (hermitianFrobeniusMatrix 𝕜 n x).PosSemidef →
      (hermitianFrobeniusMatrix 𝕜 n (L x)).PosSemidef)
    (hnorm : ‖L‖ < 1) :
    ∃ Y : hermitianFrobenius 𝕜 n,
      (hermitianFrobeniusMatrix 𝕜 n Y).PosDef ∧
      (hermitianFrobeniusMatrix 𝕜 n (Y - L Y)).PosDef ∧
      (1 : Matrix n n 𝕜) ≤ hermitianFrobeniusMatrix 𝕜 n Y := by
  let I : hermitianFrobenius 𝕜 n := 1
  let Y := Ring.inverse (1 - L) I
  have hI : hermitianFrobeniusMatrix 𝕜 n I = 1 := rfl
  have hEq : Y - L Y = I := inverse_one_sub_apply_sub_map L hnorm I
  have hge : (1 : Matrix n n 𝕜) ≤ hermitianFrobeniusMatrix 𝕜 n Y :=
    one_le_inverse_one_sub_apply_one L hL hnorm
  refine ⟨Y, ?_, ?_, hge⟩
  · have hh := Matrix.PosDef.one.add_posSemidef (Matrix.le_iff.mp hge)
    simpa only [add_sub_cancel] using hh
  · rw [hEq, hI]
    exact Matrix.PosDef.one

end NLAlib

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace NLAlib

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- A nonzero PSD matrix pairs strictly positively with every PD matrix. -/
private theorem frobInner_pos_of_posSemidef_posDef {P Y : Matrix n n 𝕜}
    (hP : P.PosSemidef) (hP0 : P ≠ 0) (hY : Y.PosDef) : 0 < frobInner P Y := by
  classical
  have hn := frobInner_nonneg_of_posSemidef hP hY.posSemidef
  apply lt_of_le_of_ne hn
  intro hz
  have hz' : (P * Y).trace = 0 := by
    apply RCLike.ext
    · have he : frobInner P Y = 0 := hz.symm
      rw [frobInner, hP.isHermitian.eq] at he
      simpa only [map_zero] using he
    · simpa only [map_zero] using (RCLike.nonneg_iff.mp (hP.trace_mul_nonneg hY.posSemidef)).2
  have hPY := (hP.trace_mul_eq_zero_iff hY.posSemidef).mp hz'
  apply hP0
  calc
    P = P * (Y * Y⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit), Matrix.mul_one]
    _ = 0 := by rw [← Matrix.mul_assoc, hPY, Matrix.zero_mul]

/-- Norm below one makes `I-L` strictly positive for the Hilbert pairing. -/
private theorem inner_sub_map_pos_of_norm_lt_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) (hL : ‖L‖ < 1) {x : E} (hx : x ≠ 0) :
    0 < inner ℝ x (x - L x) := by
  have hb : inner ℝ x (L x) ≤ ‖L‖ * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖x‖ * ‖L x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖L‖ * ‖x‖) := mul_le_mul_of_nonneg_left (L.le_opNorm x) (norm_nonneg x)
      _ = _ := by ring
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  have hp : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  nlinarith

omit [DecidableEq n] in
/-- For symmetric PSD-cone maps the strict Hilbert test is precisely the Frobenius operator norm
bound. -/
theorem inner_sub_map_pos_iff_norm_lt_one [Nonempty n]
    (L : hermitianFrobenius 𝕜 n →L[ℝ] hermitianFrobenius 𝕜 n) (hsym : L.IsSymmetric)
    (hcone : ∀ x, (hermitianFrobeniusMatrix 𝕜 n x).PosSemidef →
      (hermitianFrobeniusMatrix 𝕜 n (L x)).PosSemidef) :
    (∀ x ≠ 0, 0 < inner ℝ x (x - L x)) ↔ ‖L‖ < 1 := by
  classical
  constructor
  · intro h
    obtain ⟨x, hx, _, heig⟩ := exists_posSemidef_norm_eigenvector L hsym hcone
    have hp := h x hx
    rw [heig, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hp
    have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    nlinarith
  · exact fun h x hx => inner_sub_map_pos_of_norm_lt_one L h hx

omit [DecidableEq n] in
/-- A strict PSD supersolution forces the norm below one. -/
private theorem norm_lt_one_of_posDef_supersolution [Nonempty n]
    (L : hermitianFrobenius 𝕜 n →L[ℝ] hermitianFrobenius 𝕜 n) (hsym : L.IsSymmetric)
    (hcone : ∀ x, (hermitianFrobeniusMatrix 𝕜 n x).PosSemidef →
      (hermitianFrobeniusMatrix 𝕜 n (L x)).PosSemidef)
    {Y : hermitianFrobenius 𝕜 n} (hY : (hermitianFrobeniusMatrix 𝕜 n Y).PosDef)
    (hgap : (hermitianFrobeniusMatrix 𝕜 n (Y - L Y)).PosDef) : ‖L‖ < 1 := by
  classical
  obtain ⟨x, hx, hP, heig⟩ := exists_posSemidef_norm_eigenvector L hsym hcone
  have hx0 : hermitianFrobeniusMatrix 𝕜 n x ≠ 0 := by
    intro h
    apply hx
    apply (hermitianFrobeniusEquiv 𝕜 n).injective
    exact Subtype.ext h
  have hp := frobInner_pos_of_posSemidef_posDef hP hx0 hgap
  have hq := frobInner_pos_of_posSemidef_posDef hP hx0 hY
  change 0 < inner ℝ x (Y - L Y) at hp
  change 0 < inner ℝ x Y at hq
  have hs := hsym x Y
  change inner ℝ (L x) Y = inner ℝ x (L Y) at hs
  rw [heig, inner_smul_left] at hs
  rw [inner_sub_right, ← hs] at hp
  simp only [starRingEnd_apply, star_trivial] at hp
  nlinarith

omit [DecidableEq n] in
/-- The strict Hilbert test, Frobenius norm test and existence of a strict positive
supersolution are equivalent. -/
theorem norm_lt_one_iff_exists_posDef_sub_map [Nonempty n]
    (L : hermitianFrobenius 𝕜 n →L[ℝ] hermitianFrobenius 𝕜 n) (hsym : L.IsSymmetric)
    (hcone : ∀ x, (hermitianFrobeniusMatrix 𝕜 n x).PosSemidef →
      (hermitianFrobeniusMatrix 𝕜 n (L x)).PosSemidef) :
    ‖L‖ < 1 ↔ ∃ Y, (hermitianFrobeniusMatrix 𝕜 n Y).PosDef ∧
      (hermitianFrobeniusMatrix 𝕜 n (Y - L Y)).PosDef := by
  classical
  constructor
  · intro h
    obtain ⟨Y, hY, hg, _⟩ := exists_posDef_supersolution_of_norm_lt_one L hcone h
    exact ⟨Y, hY, hg⟩
  · rintro ⟨Y, hY, hg⟩
    exact norm_lt_one_of_posDef_supersolution L hsym hcone hY hg

end NLAlib
