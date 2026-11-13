/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.SylvesterEquation
public import NLAlib.Matrix.Functions.Sign
public import NLAlib.ForMathlib.FieldTheory.IsAlgClosed.RootPartition
public import NLAlib.ForMathlib.LinearAlgebra.Eigenspace.PrimaryInvolution
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# The matrix sign on two open half-planes

The complex spectrum may be defective. The sign selects complete primary subspaces.
The algebraic construction adapts the original NLAlib atlas at commit 77514ce.

## Main results

* `NLAlib.IsMatrixSign.eq`: uniqueness of the sign characterization.
* `NLAlib.IsMatrixSign.range_toLin_smul_add_eq_iSup`: half-plane primary projectors.
* `NLAlib.matrixSign_fromBlocks_zero₂₁`: the Sylvester block identity.
-/

@[expose] public section

open Matrix Polynomial Module
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix is positive stable when every complex spectral value has
strictly positive real part. The empty spectrum satisfies this predicate. -/
noncomputable def IsPositiveStable (A : Matrix n n ℂ) : Prop :=
  ∀ z ∈ spectrum ℂ A, 0 < z.re

/-- The algebraic and spectral characterization of the matrix sign.
Existence under spectral separation is proved separately. -/
noncomputable def IsMatrixSign (A S : Matrix n n ℂ) : Prop :=
  S ^ 2 = 1 ∧ Commute A S ∧ IsPositiveStable (S * A)

/-- Positive-stable matrices have spectra disjoint from the negative of
every positive-stable matrix. -/
theorem IsPositiveStable.disjoint_neg {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : IsPositiveStable A) (hB : IsPositiveStable B) :
    Disjoint (spectrum ℂ A) (spectrum ℂ (-B)) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  have hn : -z ∈ spectrum ℂ B := by
    rw [← spectrum.neg_eq] at hz'
    exact Set.mem_neg.mp hz'
  have ha := hA z hz
  have hb := hB (-z) hn
  simp only [Complex.neg_re] at hb
  linarith

/-- **Uniqueness of the matrix sign.** Two commuting involutions satisfying the positive-stability
characterization for the same input coincide. [Higham2008, Theorem 5.1].
Result: matrix-sign-spectral-projectors -/
theorem IsMatrixSign.eq {A S T : Matrix n n ℂ}
    (hS : IsMatrixSign A S) (hT : IsMatrixSign A T) : S = T := by
  have hs : S * S = 1 := by simpa only [pow_two] using hS.1
  have ht : T * T = 1 := by simpa only [pow_two] using hT.1
  have hsep := hS.2.2.disjoint_neg hT.2.2
  have heq : (S * A) * (S - T) = (S - T) * (-(T * A)) := by
    have hSA : A * S = S * A := hS.2.1.eq
    have hTA : A * T = T * A := hT.2.1.eq
    calc
      _ = S * (A * S) - S * (A * T) := by noncomm_ring
      _ = (S * S) * A - S * T * A := by rw [hSA, hTA]; noncomm_ring
      _ = A - S * T * A := by rw [hs, Matrix.one_mul]
      _ = (S - T) * (-(T * A)) := by
        calc
          _ = -(S * T * A) + (T * T) * A := by rw [ht, Matrix.one_mul]; abel
          _ = _ := by noncomm_ring
  exact sub_eq_zero.mp (eq_zero_of_mul_eq_mul_of_isCoprime_charpoly
    ((isCoprime_charpoly_iff_disjoint_spectrum _ _).mpr hsep) heq)

/-- The two half-sign matrices are complementary commuting idempotents. -/
theorem IsMatrixSign.mul_self_and_mul_eq_zero {A S : Matrix n n ℂ} (hS : IsMatrixSign A S) :
    let P := (2 : ℂ)⁻¹ • (1 + S)
    let Q := (2 : ℂ)⁻¹ • (1 - S)
    P * P = P ∧ Q * Q = Q ∧ P * Q = 0 ∧ Q * P = 0 ∧ P + Q = 1 := by
  dsimp
  have hs : S * S = 1 := by simpa only [pow_two] using hS.1
  constructor
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (1 + S) * (1 + S) = (2 : ℂ) • (1 + S) by
      simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, hs]
      module]
    simp [smul_smul]
  constructor
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (1 - S) * (1 - S) = (2 : ℂ) • (1 - S) by
      simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hs]
      module]
    simp [smul_smul]
  constructor
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (1 + S) * (1 - S) = 0 by noncomm_ring [hs], smul_zero]
  constructor
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (1 - S) * (1 + S) = 0 by noncomm_ring [hs], smul_zero]
  · rw [← smul_add]
    have heq : (1 : Matrix n n ℂ) + S + (1 - S) = (2 : ℂ) • 1 := by module
    rw [heq, smul_smul]
    norm_num

section
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Spectral separation from the imaginary axis gives a matrix satisfying
the sign characterization, constructed by coprime polynomial factors. -/
private theorem exists_isMatrixSign_nonempty {A : Matrix n n ℂ}
    (hA : ∀ z ∈ spectrum ℂ A, z.re ≠ 0) : ∃ S, IsMatrixSign A S := by
  classical
  obtain ⟨f, g, hf, hg, hfg, hcop, hfr, hgr⟩ :=
    Polynomial.exists_monic_mul_eq_of_filter_roots A.charpoly A.charpoly_monic
      (fun z : ℂ => 0 < z.re)
  obtain ⟨a, b, hab⟩ := hcop
  let P := aeval A (b * g)
  let Q := aeval A (a * f)
  have hsum : P + Q = 1 := by
    change aeval A (b * g) + aeval A (a * f) = 1
    rw [← map_add, add_comm (b * g), hab, map_one]
  have hzero : aeval A (f * g) = 0 := by rw [hfg, Matrix.aeval_self_charpoly]
  have hPQ : P * Q = 0 := by
    change aeval A (b * g) * aeval A (a * f) = 0
    calc
      _ = aeval A ((f * g) * (a * b)) := by rw [← map_mul]; congr 1; ring
      _ = 0 := by rw [map_mul, hzero, Matrix.zero_mul]
  have hQP : Q * P = 0 := by
    have hc := (Commute.all (a * f) (b * g)).map (aeval A)
    exact hc.eq.trans hPQ
  have hPP : P * P = P := by
    calc
      _ = P * P + P * Q := by rw [hPQ, add_zero]
      _ = P * (P + Q) := (Matrix.mul_add _ _ _).symm
      _ = P := by rw [hsum, Matrix.mul_one]
  have hQQ : Q * Q = Q := by
    calc
      _ = Q * P + Q * Q := by rw [hQP, zero_add]
      _ = Q * (P + Q) := (Matrix.mul_add _ _ _).symm
      _ = Q := by rw [hsum, Matrix.mul_one]
  refine ⟨P - Q, ?_, ?_, ?_⟩
  · calc
      (P - Q) ^ 2 = P * P - P * Q - Q * P + Q * Q := by noncomm_ring
      _ = 1 := by rw [hPP, hQQ, hPQ, hQP, sub_zero, sub_zero, hsum]
  · have hc := (Commute.all (X : ℂ[X]) (b * g - a * f)).map (aeval A)
    simpa only [map_sub, aeval_X] using hc
  · intro z hz
    have heq : (P - Q) * A = aeval A ((b * g - a * f) * X) := by
      simp only [map_mul, map_sub, aeval_X, P, Q]
    rw [heq, spectrum.map_polynomial_aeval] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hwroot : w ∈ A.charpoly.roots :=
      (Polynomial.mem_roots A.charpoly_monic.ne_zero).mpr
        (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hw)
    have hbez : a.eval w * f.eval w + b.eval w * g.eval w = 1 := by
      simpa only [eval_add, eval_mul, eval_one] using congrArg (eval w) hab
    by_cases hwpos : 0 < w.re
    · have hfw : f.eval w = 0 := (Polynomial.mem_roots hf.ne_zero).mp
        (by rw [hfr, Multiset.mem_filter]; exact ⟨hwroot, hwpos⟩)
      have hbg : b.eval w * g.eval w = 1 := by simpa only [hfw, mul_zero, zero_add] using hbez
      simpa only [eval_mul, eval_sub, eval_X, hfw, mul_zero, hbg, sub_zero, one_mul] using hwpos
    · have hgw : g.eval w = 0 := (Polynomial.mem_roots hg.ne_zero).mp
        (by rw [hgr, Multiset.mem_filter]; exact ⟨hwroot, hwpos⟩)
      have haf : a.eval w * f.eval w = 1 := by simpa only [hgw, mul_zero, add_zero] using hbez
      have hwneg : w.re < 0 := lt_of_le_of_ne (le_of_not_gt hwpos) (hA w hw)
      simp only [eval_mul, eval_sub, eval_X, hgw, mul_zero, haf, zero_sub, neg_one_mul,
        Complex.neg_re]
      linarith

omit [Nonempty n] in
/-- The spectral sign exists in every finite dimension, including zero. -/
theorem exists_isMatrixSign {A : Matrix n n ℂ}
    (hA : ∀ z ∈ spectrum ℂ A, z.re ≠ 0) : ∃ S, IsMatrixSign A S := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    let := hn
    refine ⟨1, ?_, ?_, ?_⟩
    · simp
    · exact Commute.one_right A
    · intro z hz
      simp only [spectrum.of_subsingleton, Set.mem_empty_iff_false] at hz
  | inr hn =>
    let := hn
    exact exists_isMatrixSign_nonempty hA

/-- The matrix sign, uniquely characterized by an involution commuting
with the input whose product with the input is positive stable.
The value is zero if no sign satisfies this characterization. -/
noncomputable def matrixSign (A : Matrix n n ℂ) : Matrix n n ℂ := by
  classical
  exact if h : ∃ S, IsMatrixSign A S then h.choose else 0

omit [Nonempty n] in
/-- The matrix sign satisfies its defining characterization whenever no
eigenvalue lies on the imaginary axis. -/
theorem isMatrixSign_matrixSign {A : Matrix n n ℂ}
    (hA : ∀ z ∈ spectrum ℂ A, z.re ≠ 0) : IsMatrixSign A (matrixSign A) :=
by
  classical
  simp only [matrixSign, dif_pos (exists_isMatrixSign hA)]
  exact (exists_isMatrixSign hA).choose_spec

omit [Nonempty n] in
/-- Every matrix satisfying the sign characterization equals the
canonical sign; the construction is independent of Bezout choices. -/
theorem IsMatrixSign.eq_matrixSign {A S : Matrix n n ℂ}
    (hA : ∀ z ∈ spectrum ℂ A, z.re ≠ 0) (hS : IsMatrixSign A S) :
    S = matrixSign A := hS.eq (isMatrixSign_matrixSign hA)
end

/-- On an invertible Hermitian complex matrix the primary half-plane sign agrees with
the real-sign continuous functional calculus. [Higham2008, §5.1]. -/
theorem _root_.Matrix.IsHermitian.matrixSign_eq_cfc_sign {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (hunit : IsUnit A) : matrixSign A = cfc Real.sign A := by
  have ha : IsSelfAdjoint A := hA
  have hn (x : ℝ) (hx : x ∈ spectrum ℝ A) : x ≠ 0 := by
    intro h
    subst x
    exact spectrum.zero_notMem ℝ hunit hx
  have hspec {H : Matrix n n ℂ} (h : H.IsHermitian) :
      spectrum ℂ H = Complex.ofReal '' spectrum ℝ H := by
    rw [h.spectrum_real_eq_range_eigenvalues, h.spectrum_eq_image_range]
    rfl
  have haxis : ∀ z ∈ spectrum ℂ A, z.re ≠ 0 := by
    intro z hz
    rw [hspec hA] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact hn _ hx
  symm
  apply IsMatrixSign.eq_matrixSign haxis
  refine ⟨?_, ?_, ?_⟩
  · rw [← cfc_pow _ _ A (A.finite_real_spectrum.continuousOn _) ha, ← cfc_one ℝ A]
    apply cfc_congr
    intro x hx
    rcases (hn _ hx).lt_or_gt with h | h <;> simp [Real.sign_of_neg, Real.sign_of_pos, h]
  · simpa only [cfc_id' ℝ A ha] using cfc_commute_cfc (fun x : ℝ => x) Real.sign A
  · have hm : cfc Real.sign A * A = cfc (fun x : ℝ => Real.sign x * x) A := by
      rw [cfc_mul _ _ A (A.finite_real_spectrum.continuousOn _)
        (A.finite_real_spectrum.continuousOn _), cfc_id' ℝ A ha]
    rw [hm]
    intro z hz
    have hc : IsSelfAdjoint (cfc (fun x : ℝ => Real.sign x * x) A) := cfc_predicate _ _
    rw [hspec hc] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [cfc_map_spectrum (fun x : ℝ => Real.sign x * x) A ha
      (A.finite_real_spectrum.continuousOn _)] at ht
    obtain ⟨x, hx, rfl⟩ := ht
    change 0 < Real.sign x * x
    rcases (hn _ hx).lt_or_gt with h | h
    · simpa only [Real.sign_of_neg h, neg_one_mul, neg_pos] using h
    · simpa only [Real.sign_of_pos h, one_mul] using h

/-- The range of an algebraic half-involution is its signed eigenspace. -/
private theorem range_toLin_smul_add_eq_eigenspace {S : Matrix n n ℂ} (hS : S ^ 2 = 1)
    (a : ℂ) (ha : a ^ 2 = 1) :
    LinearMap.range ((2 : ℂ)⁻¹ • (1 + a • S)).toLin' = Module.End.eigenspace S.toLin' a := by
  have hs (v : n → ℂ) : S *ᵥ (S *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← pow_two, hS, Matrix.one_mulVec]
  have haa : a * a = 1 := by simpa only [pow_two] using ha
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change S *ᵥ (((2 : ℂ)⁻¹ • (1 + a • S)) *ᵥ w) =
      a • (((2 : ℂ)⁻¹ • (1 + a • S)) *ᵥ w)
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_smul, Matrix.mulVec_add, hs]
    rw [smul_comm a ((2 : ℂ)⁻¹)]
    congr 1
    simp only [smul_add, smul_smul, haa, one_smul]
    abel
  · intro hv
    have he : S *ᵥ v = a • v := Module.End.mem_eigenspace_iff.mp hv
    refine ⟨v, ?_⟩
    change ((2 : ℂ)⁻¹ • (1 + a • S)) *ᵥ v = v
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, he,
      smul_smul, haa, one_smul]
    rw [← two_smul ℂ v, smul_smul]
    norm_num

/-- The signed eigenspace of a matrix sign is the matching primary
spectral half-plane. -/
theorem IsMatrixSign.eigenspace_eq_iSup {A S : Matrix n n ℂ}
    (hS : IsMatrixSign A S) (a : ℂ) (ha : a ^ 2 = 1) :
    Module.End.eigenspace S.toLin' a = ⨆ z : {z : ℂ // 0 < (a * z).re},
      Module.End.maxGenEigenspace A.toLin' z.val := by
  have hc : Commute A.toLin' S.toLin' := by
    change A.toLin' * S.toLin' = S.toLin' * A.toLin'
    simpa only [Matrix.toLin'_mul, Module.End.mul_eq_comp] using
      congrArg Matrix.toLin' hS.2.1.eq
  have hss : S.toLin' ^ 2 = 1 := by
    calc
      _ = (S ^ 2).toLin' := (Matrix.toLin'_pow S 2).symm
      _ = (1 : Matrix n n ℂ).toLin' := congrArg Matrix.toLin' hS.1
      _ = 1 := by rw [Matrix.toLin'_one]; rfl
  apply Module.End.eigenspace_eq_iSup_maxGenEigenspace_of_stable_involution
    A.toLin' S.toLin' hc hss _ a ha
  intro z hz
  apply hS.2.2 z
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  simpa only [Matrix.toLin'_mul, Module.End.mul_eq_comp] using hz

/-- **Half-plane spectral projector.** If an involution is the matrix sign, the range of
its signed half-projector is the sum of the maximal generalized eigenspaces in the
selected open half-plane, including defective eigenvalues. [Higham2008, §5.1].
Result: matrix-sign-spectral-projectors -/
theorem IsMatrixSign.range_toLin_smul_add_eq_iSup {A S : Matrix n n ℂ}
    (hS : IsMatrixSign A S) (a : ℂ) (ha : a ^ 2 = 1) :
    LinearMap.range (((2 : ℂ)⁻¹ • (1 + a • S)).toLin') =
      ⨆ z : {z : ℂ // 0 < (a * z).re}, Module.End.maxGenEigenspace A.toLin' z.val :=
  (range_toLin_smul_add_eq_eigenspace hS.1 a ha).trans (hS.eigenspace_eq_iSup a ha)


section
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- A block upper triangular matrix has the union of its diagonal spectra. -/
theorem spectrum_fromBlocks_zero₂₁ (A : Matrix m m ℂ) (C : Matrix m n ℂ)
    (B : Matrix n n ℂ) :
    spectrum ℂ (fromBlocks A C 0 B) = spectrum ℂ A ∪ spectrum ℂ B := by
  ext z
  simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_fromBlocks_zero₂₁,
    Polynomial.IsRoot, Polynomial.eval_mul, mul_eq_zero, Set.mem_union]

/-- Positive stability is preserved by block upper triangular assembly. -/
theorem IsPositiveStable.fromBlocks {A : Matrix m m ℂ} {B : Matrix n n ℂ}
    (hA : IsPositiveStable A) (hB : IsPositiveStable B) (C : Matrix m n ℂ) :
    IsPositiveStable (fromBlocks A C 0 B) := by
  intro z hz
  rw [spectrum_fromBlocks_zero₂₁] at hz
  exact hz.elim (hA z) (hB z)

/-- **The matrix sign of a Sylvester block.** For positive-stable diagonal coefficients and
a solution of the Sylvester sum equation, the off-diagonal block of the matrix sign is twice
the solution. [Higham2008, §5.1].
Result: matrix-sign-sylvester-block -/
theorem matrixSign_fromBlocks_zero₂₁
    {A : Matrix m m ℂ} {B : Matrix n n ℂ} (hA : IsPositiveStable A)
    (hB : IsPositiveStable B) {C X : Matrix m n ℂ} (hX : A * X + X * B = C) :
    matrixSign (fromBlocks A C 0 (-B)) = fromBlocks 1 ((2 : ℂ) • X) 0 (-1) := by
  have hsep : ∀ z ∈ spectrum ℂ (fromBlocks A C 0 (-B)), z.re ≠ 0 := by
    intro z hz
    rw [spectrum_fromBlocks_zero₂₁] at hz
    rcases hz with hz | hz
    · exact (hA z hz).ne'
    · have hn : -z ∈ spectrum ℂ B := by
        rw [← spectrum.neg_eq] at hz
        exact Set.mem_neg.mp hz
      have hh := hB (-z) hn
      simp only [Complex.neg_re] at hh
      linarith
  symm
  apply IsMatrixSign.eq_matrixSign hsep
  refine ⟨?_, ?_, ?_⟩
  · rw [pow_two, Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.mul_neg, neg_neg, add_zero, zero_add, add_neg_cancel,
      Matrix.fromBlocks_one]
  · change fromBlocks A C 0 (-B) * fromBlocks 1 ((2 : ℂ) • X) 0 (-1) =
      fromBlocks 1 ((2 : ℂ) • X) 0 (-1) * fromBlocks A C 0 (-B)
    simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_smul, Matrix.smul_mul, neg_neg, add_zero, zero_add, smul_zero]
    congr 1
    rw [← hX]
    module
  · have heq : fromBlocks 1 ((2 : ℂ) • X) 0 (-1) * fromBlocks A C 0 (-B) =
        fromBlocks A (C - (2 : ℂ) • (X * B)) 0 B := by
      simp [Matrix.fromBlocks_multiply, Matrix.smul_mul, sub_eq_add_neg]
    rw [heq]
    exact hA.fromBlocks hB _


end

end NLAlib
