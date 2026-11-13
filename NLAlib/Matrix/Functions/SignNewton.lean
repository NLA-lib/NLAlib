/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.HalfPlaneSign
public import NLAlib.Matrix.Spectral.PowerBounds

/-!
# Newton iteration for the half-plane sign

The complex Cayley transform sends the open right half-plane to the unit disk.
The algebraic argument adapts the original NLAlib sign iteration, commit 77514ce.

## Main results

* `NLAlib.IsMatrixSign.signNewtonIterate_eq`: Cayley-power closed form.
* `NLAlib.IsMatrixSign.tendsto_signNewtonIterate`: convergence of the iteration.
* `NLAlib.IsMatrixSign.specNorm_sub_signNewtonIterate_le`: the quadratic error estimate.
-/

@[expose] public section

open Matrix Filter
open scoped Matrix.Norms.L2Operator Topology Pointwise

namespace NLAlib

section
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
private theorem commute_inv_right {A B : Matrix n n K} (h : Commute A B) : Commute A B⁻¹ := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  by_cases hu : IsUnit B
  · obtain ⟨u, rfl⟩ := hu
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ hu]
    exact Commute.zero_right _

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- The bicommutant of a singleton matrix, as a scalar subalgebra. -/
private noncomputable def bicommutantAlgebra (A : Matrix n n K) : Subalgebra K (Matrix n n K) :=
  Subalgebra.centralizer K (Subalgebra.centralizer K ({A} : Set (Matrix n n K)))

/-- The generator belongs to its bicommutant. -/
private theorem self_mem_bicommutantAlgebra (A : Matrix n n K) : A ∈ bicommutantAlgebra A := by
  intro B hB
  exact (hB A (Set.mem_singleton A)).symm

/-- A singleton bicommutant is commutative. -/
private instance bicommutantAlgebraIsMulCommutative (A : Matrix n n K) :
    IsMulCommutative (bicommutantAlgebra A) := by
  apply IsMulCommutative.of_comm
  intro X Y
  apply Subtype.ext
  exact Y.property X.val (by
    intro B hB
    have hBA : B = A := Set.mem_singleton_iff.mp hB
    rw [hBA]
    exact X.property A (by intro B hB; have hBA : B = A := Set.mem_singleton_iff.mp hB; rw [hBA]))

open scoped IsMulCommutative in
/-- The singleton bicommutant carries its canonical commutative-ring structure. -/
private noncomputable instance bicommutantAlgebraCommRing (A : Matrix n n K)
    : CommRing (bicommutantAlgebra A) :=
  inferInstance

/-- The ordinary inverse stays in the bicommutant, without any unit
assumption on the matrix being inverted. -/
private theorem inv_mem_bicommutantAlgebra {A X : Matrix n n K}
    (hX : X ∈ bicommutantAlgebra A) : X⁻¹ ∈ bicommutantAlgebra A := by
  intro B hB
  exact (commute_inv_right (show Commute B X from hX B hB)).eq

/-- Inversion in the bicommutant, with the same total convention as matrices. -/
private noncomputable def bicommutantInverse {A : Matrix n n K} (X : bicommutantAlgebra A)
    : bicommutantAlgebra A :=
  ⟨X.val⁻¹, inv_mem_bicommutantAlgebra X.property⟩


end

section
variable {R : Type*} [CommRing R]
private theorem one_sub_sq_mul_inverse_product (t d e : R)
    (hd : (1 - t) * d = 1) (he : (1 + t) * e = 1) : (1 - t ^ 2) * (d * e) = 1 := by
  calc
    _ = ((1 - t) * d) * ((1 + t) * e) := by ring
    _ = 1 := by rw [hd, he, one_mul]

private theorem cayley_value_mul_inverse (t d e : R)
    (hd : (1 - t) * d = 1) (he : (1 + t) * e = 1) : (d * (1 + t)) * (e * (1 - t)) = 1 := by
  calc
    _ = ((1 - t) * d) * ((1 + t) * e) := by ring
    _ = 1 := by rw [hd, he, one_mul]

private theorem half_mul_cayley_add_inverse (t d e c : R)
    (hd : (1 - t) * d = 1) (he : (1 + t) * e = 1) (hc : c * 2 = 1) :
    c * (d * (1 + t) + e * (1 - t)) = (d * e) * (1 + t ^ 2) := by
  calc
    _ = c * ((d * (1 + t)) * (e * (1 + t)) + (e * (1 - t)) * (d * (1 - t))) := by
      rw [mul_comm e (1 + t), he, mul_comm d (1 - t), hd, mul_one, mul_one]
    _ = c * (d * e) * ((1 + t) ^ 2 + (1 - t) ^ 2) := by ring
    _ = (c * 2) * (d * e) * (1 + t ^ 2) := by ring
    _ = _ := by rw [hc, one_mul]

private theorem one_sub_cayley_mul (x e : R) (he : (x + 1) * e = 1) :
    (1 - (x - 1) * e) * x = 1 + (x - 1) * e := by
  calc
    _ = 1 + (x - 1) * e + (x - 1) * (1 - (x + 1) * e) := by ring
    _ = _ := by rw [he, sub_self, mul_zero, add_zero]
end

variable {n : Type*} [Fintype n] [DecidableEq n]
private noncomputable def cayleyTransform {K : Type*} [RCLike K] (A : Matrix n n K) (p : ℝ)
    : Matrix n n K :=
  (A + (p : K) • 1) * (A - (p : K) • 1)⁻¹

private theorem cayleyTransform_eq_one_add {K : Type*} [RCLike K] (A : Matrix n n K) (p : ℝ)
    (h : IsUnit (A - (p : K) • 1).det) :
    cayleyTransform A p = 1 + (2 * (p : K)) • (A - (p : K) • 1)⁻¹ := by
  have heq : A + (p : K) • (1 : Matrix n n K) =
      (A - (p : K) • 1) + (2 * (p : K)) • 1 := by module
  rw [cayleyTransform, heq, Matrix.add_mul, Matrix.mul_nonsing_inv _ h]
  simp

private theorem norm_cayley_lt_one {z : ℂ} (hz : z.re < 0) (p : ℝ) (hp : 0 < p) :
    ‖(z + (p : ℂ)) / (z - (p : ℂ))‖ < 1 := by
  have hd : z - (p : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hr
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  have hs : ‖z + (p : ℂ)‖ ^ 2 < ‖z - (p : ℂ)‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_sub,
      Complex.normSq_ofReal, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  nlinarith [norm_nonneg (z + (p : ℂ)), norm_nonneg (z - (p : ℂ))]

private theorem spectrum_cayleyTransform (A : Matrix n n ℂ) (p : ℝ) (hp : p ≠ 0)
    (h : IsUnit (A - (p : ℂ) • 1)) :
    spectrum ℂ (cayleyTransform A p) =
      (fun z : ℂ => (z + (p : ℂ)) / (z - (p : ℂ))) '' spectrum ℂ A := by
  let u := h.unit
  have huval : (u : Matrix n n ℂ) = A - (p : ℂ) • 1 := h.unit_spec
  have huinv : (A - (p : ℂ) • 1)⁻¹ = (↑u⁻¹ : Matrix n n ℂ) := by
    apply Matrix.inv_eq_right_inv
    rw [← huval]
    exact u.val_inv
  have hinv : spectrum ℂ (A - (p : ℂ) • 1)⁻¹ =
      (spectrum ℂ (A - (p : ℂ) • 1))⁻¹ := by
    rw [huinv, ← spectrum.map_inv u, huval]
  have hscale : (2 * (p : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast hp)
  have hshift : spectrum ℂ (A - (p : ℂ) • 1) = spectrum ℂ A - {(p : ℂ)} := by
    simpa only [Algebra.algebraMap_eq_smul_one] using (spectrum.sub_singleton_eq A (p : ℂ)).symm
  rw [cayleyTransform_eq_one_add A p ((Matrix.isUnit_iff_isUnit_det _).mp h)]
  change spectrum ℂ (algebraMap ℂ (Matrix n n ℂ) 1 +
    (Units.mk0 (2 * (p : ℂ)) hscale) • (A - (p : ℂ) • 1)⁻¹) = _
  rw [← spectrum.singleton_add_eq, spectrum.unit_smul_eq_smul _ (Units.mk0 _ hscale),
    hinv, hshift]
  have hden (z : ℂ) (hz : z ∈ spectrum ℂ A) : z - (p : ℂ) ≠ 0 := by
    have hm : z - (p : ℂ) ∈ spectrum ℂ (A - (p : ℂ) • 1) := by
      rw [hshift]
      exact ⟨z, hz, (p : ℂ), rfl, rfl⟩
    intro heq
    rw [heq] at hm
    exact spectrum.zero_notMem ℂ h hm
  ext w
  simp only [Set.mem_add, Set.mem_singleton_iff, Set.mem_smul_set, Set.mem_inv,
    Set.mem_sub, Set.mem_image]
  constructor
  · rintro ⟨_, rfl, v, ⟨v', ⟨z, hz, _, rfl, hzv⟩, hvinv⟩, hvw⟩
    refine ⟨z, hz, ?_⟩
    have hv' : v' = (z - (p : ℂ))⁻¹ := by
      simpa only [inv_inv] using (congrArg Inv.inv hzv).symm
    rw [← hvw, ← hvinv, hv']
    change (z + (p : ℂ)) / (z - (p : ℂ)) = 1 + (2 * (p : ℂ)) * (z - (p : ℂ))⁻¹
    field_simp [hden z hz]
    ring
  · rintro ⟨z, hz, rfl⟩
    refine ⟨1, rfl, (Units.mk0 (2 * (p : ℂ)) hscale) • (z - (p : ℂ))⁻¹, ?_, ?_⟩
    · exact ⟨(z - (p : ℂ))⁻¹, ⟨z, hz, (p : ℂ), rfl, by simp⟩, rfl⟩
    · change 1 + (2 * (p : ℂ)) * (z - (p : ℂ))⁻¹ = (z + (p : ℂ)) / (z - (p : ℂ))
      field_simp [hden z hz]
      ring

private theorem isUnit_one_sub_of_specRadius_lt_one {A : Matrix n n ℂ}
    (h : specRadius A < 1) : IsUnit (1 - A) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_one_sub_of_specRadius_lt_one h)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The inverse Cayley value for a total matrix argument. -/
noncomputable def inverseCayley {𝕜 : Type*} [RCLike 𝕜] (T : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  (1 - T)⁻¹ * (1 + T)

/-- Newton averaging of an inverse Cayley value squares its coordinate,
provided both original denominators are invertible. -/
private theorem half_smul_inverseCayley_add_inv (T : Matrix n n ℂ)
    (hm : IsUnit (1 - T)) (hp : IsUnit (1 + T)) :
    (2 : ℂ)⁻¹ • (inverseCayley T + (inverseCayley T)⁻¹) = inverseCayley (T ^ 2) := by
  let R := bicommutantAlgebra T
  let t : R := ⟨T, self_mem_bicommutantAlgebra T⟩
  let d : R := bicommutantInverse (1 - t)
  let e : R := bicommutantInverse (1 + t)
  let c : R := algebraMap ℂ R ((2 : ℂ)⁻¹)
  have hd : (1 - t) * d = 1 :=
      Subtype.ext (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hm))
  have he : (1 + t) * e = 1 :=
      Subtype.ext (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hp))
  have hc : c * 2 = 1 := by
    change algebraMap ℂ R ((2 : ℂ)⁻¹) * algebraMap ℂ R 2 = 1
    rw [← map_mul]
    norm_num
  have hxi : (inverseCayley T)⁻¹ = (e * (1 - t) : R).val := by
    apply Matrix.inv_eq_right_inv
    exact congrArg Subtype.val (cayley_value_mul_inverse t d e hd he)
  have hdi : (1 - T ^ 2)⁻¹ = (d * e : R).val := by
    apply Matrix.inv_eq_right_inv
    exact congrArg Subtype.val (one_sub_sq_mul_inverse_product t d e hd he)
  have hh := congrArg Subtype.val (half_mul_cayley_add_inverse t d e c hd he hc)
  rw [hxi]
  change (2 : ℂ)⁻¹ • ((1 - T)⁻¹ * (1 + T) + (e * (1 - t) : R).val) = (1 - T ^ 2)⁻¹ * (1 + T ^ 2)
  rw [hdi]
  simpa [c, d, e, t, bicommutantInverse, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mul] using hh

/-- Power convergence also holds for the negative matrix. -/
private theorem tendsto_neg_matrix_pow_zero {T : Matrix n n ℂ}
    (h : Tendsto (fun k : ℕ => T ^ k) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => (-T) ^ k) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at h ⊢
  have he (k : ℕ) : ‖(-T) ^ k‖=‖T ^ k‖ := by
    by_cases hk : Even k
    · rw [hk.neg_pow]
    · rw [(Nat.not_even_iff_odd.mp hk).neg_pow, norm_neg]
  simpa only [he] using h

/-- Every positive power of a matrix with convergent powers has both
unit Cayley denominators. -/
private theorem isUnit_one_sub_and_add_matrix_pow {T : Matrix n n ℂ}
    (h : Tendsto (fun k : ℕ => T ^ k) atTop (𝓝 0)) {m : ℕ} (hm : 0 < m) :
    IsUnit (1 - T ^ m) ∧ IsUnit (1 + T ^ m) := by
  have hp : Tendsto (fun k : ℕ => (T ^ m) ^ k) atTop (𝓝 0) := by
    have ht : Tendsto (fun k : ℕ => m * k) atTop atTop := by
      simpa using (tendsto_id.nsmul_atTop hm : Tendsto (fun k : ℕ => m • k) atTop atTop)
    simpa only [Function.comp_def, pow_mul] using h.comp ht
  constructor
  · exact isUnit_one_sub_of_specRadius_lt_one
      ((tendsto_pow_zero_iff_specRadius_lt_one _).mp hp)
  · simpa only [sub_neg_eq_add] using isUnit_one_sub_of_specRadius_lt_one
      ((tendsto_pow_zero_iff_specRadius_lt_one _).mp (tendsto_neg_matrix_pow_zero hp))

/-- Inverse Cayley values are nonsingular if both denominators are units. -/
private theorem isUnit_inverseCayley {T : Matrix n n ℂ}
    (hm : IsUnit (1 - T)) (hp : IsUnit (1 + T)) : IsUnit (inverseCayley T) := by
  exact (Matrix.isUnit_nonsing_inv_iff.mpr hm).mul hp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The total Newton sign recursion. Theorems below certify that every
inverse is nonsingular on the spectrally separated domain. [Higham2008, §5.3].
Algorithm: matrix-sign-newton -/
noncomputable def signNewtonIterate {𝕜 : Type*} [RCLike 𝕜] (A : Matrix n n 𝕜) : ℕ → Matrix n n 𝕜
  | 0 => A
  | k + 1 => (2 : 𝕜)⁻¹ • (signNewtonIterate A k + (signNewtonIterate A k)⁻¹)

/-- A convergent-power Cayley coordinate gives the exact actual Newton
iterate, with a doubly exponential power. -/
private theorem signNewtonIterate_inverseCayley {G : Matrix n n ℂ}
    (hG : Tendsto (fun k : ℕ => G ^ k) atTop (𝓝 0)) (k : ℕ) :
    signNewtonIterate (inverseCayley G) k = inverseCayley (G ^ (2 ^ k)) := by
  induction k with
  | zero => simp [signNewtonIterate]
  | succ k ih =>
    obtain ⟨hm, hp⟩ := isUnit_one_sub_and_add_matrix_pow hG (pow_pos (by norm_num : 0 < (2 : ℕ)) k)
    rw [signNewtonIterate, ih, half_smul_inverseCayley_add_inv _ hm hp,
      ← pow_mul, pow_succ]

/-- Inverse Cayley values converge to the identity as their coordinates
converge to zero. -/
private theorem tendsto_inverseCayley_one {ι : Type*} {l : Filter ι} {G : ι → Matrix n n ℂ}
    (hG : Tendsto G l (𝓝 0)) : Tendsto (fun k => inverseCayley (G k)) l (𝓝 1) := by
  have hc : ContinuousAt (Ring.inverse : Matrix n n ℂ → Matrix n n ℂ) 1 :=
    NormedRing.inverse_continuousAt (1 : (Matrix n n ℂ)ˣ)
  have hd : Tendsto (fun k => (1 - G k)⁻¹) l (𝓝 1) := by
    have hsub : Tendsto (fun k => (1 : Matrix n n ℂ) - G k) l (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub hG)
    have h := hc.tendsto.comp hsub
    have hh : Tendsto (fun k => Ring.inverse (1 - G k)) l (𝓝 1) := by
      simpa only [Function.comp_def, Ring.inverse_one] using h
    convert! hh using 1
    funext k
    exact Matrix.nonsing_inv_eq_ringInverse _
  have hadd : Tendsto (fun k => (1 : Matrix n n ℂ) + G k) l (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hG)
  simpa only [inverseCayley, mul_one] using hd.mul hadd

/-- A convergent-power Cayley coordinate yields convergence of the actual
Newton recursion to the identity. -/
private theorem tendsto_signNewtonIterate_inverseCayley {G : Matrix n n ℂ}
    (hG : Tendsto (fun k : ℕ => G ^ k) atTop (𝓝 0)) :
    Tendsto (signNewtonIterate (inverseCayley G)) atTop (𝓝 1) := by
  convert! tendsto_inverseCayley_one (hG.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))) using 1
  funext k
  exact signNewtonIterate_inverseCayley hG k

/-- The positive-half-plane Cayley transform. -/
private noncomputable def positiveCayley (A : Matrix n n ℂ) : Matrix n n ℂ := (A - 1) * (A + 1)⁻¹

private theorem isUnit_add_one_of_positiveStable {A : Matrix n n ℂ} (hA : IsPositiveStable A) :
    IsUnit (A + 1) := by
  have hn : (-1 : ℂ) ∉ spectrum ℂ A := by
    intro h
    have hh := hA _ h
    norm_num at hh
  have hu := (spectrum.notMem_iff.mp hn).neg
  simpa [sub_eq_add_neg, add_comm] using hu

private theorem specRadius_positiveCayley_lt_one {A : Matrix n n ℂ} (hA : IsPositiveStable A) :
    specRadius (positiveCayley A) < 1 := by
  by_cases! hn : Nonempty n
  · obtain ⟨μ, hμ, he⟩ := exists_mem_spectrum_norm_eq_specRadius (positiveCayley A)
    have hu : IsUnit (A - ((-1 : ℝ) : ℂ) • 1) := by
      simpa using isUnit_add_one_of_positiveStable hA
    have hm : μ ∈ spectrum ℂ (cayleyTransform A (-1)) := by
      simpa [cayleyTransform, positiveCayley, sub_eq_add_neg] using hμ
    rw [spectrum_cayleyTransform A (-1) (by norm_num) hu] at hm
    obtain ⟨z, hz, rfl⟩ := hm
    rw [← he]
    have hh := norm_cayley_lt_one (z := -z) (by simpa using hA z hz) 1 zero_lt_one
    have h₁ : -z + (1 : ℂ) = -(z + ((-1 : ℝ) : ℂ)) := by push_cast; ring
    have h₂ : -z - (1 : ℂ) = -(z - ((-1 : ℝ) : ℂ)) := by push_cast; ring
    rw [Complex.ofReal_one, h₁, h₂, neg_div_neg_eq] at hh
    exact hh
  · have hz : positiveCayley A = 0 := Subsingleton.elim _ _
    rw [hz, specRadius_eq_toReal_spectralRadius, spectrum.spectralRadius_zero, ENNReal.toReal_zero]
    exact zero_lt_one

/-- The inverse Cayley formula reconstructs every positive-stable matrix. -/
private theorem IsPositiveStable.inverseCayley_positiveCayley {A : Matrix n n ℂ}
    (hA : IsPositiveStable A) : inverseCayley (positiveCayley A) = A := by
  let R := bicommutantAlgebra A
  let a : R := ⟨A, self_mem_bicommutantAlgebra A⟩
  let e : R := bicommutantInverse (a + 1)
  have he : (a + 1) * e = 1 := Subtype.ext (Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_add_one_of_positiveStable hA)))
  have hh := congrArg Subtype.val (one_sub_cayley_mul a e he)
  have hc : (1 - positiveCayley A) * A = 1 + positiveCayley A := hh
  have hu := isUnit_one_sub_of_specRadius_lt_one (specRadius_positiveCayley_lt_one hA)
  rw [inverseCayley, ← hc, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.one_mul]

/-- Positive-stable Newton iterates have the exact Cayley formula and
are nonsingular at every step. -/
private theorem IsPositiveStable.signNewtonIterate_eq_and_isUnit {A : Matrix n n ℂ}
    (hA : IsPositiveStable A) (k : ℕ) :
    signNewtonIterate A k = inverseCayley ((positiveCayley A) ^ (2 ^ k)) ∧
      IsUnit (signNewtonIterate A k) := by
  have hp := (tendsto_pow_zero_iff_specRadius_lt_one _).mpr (specRadius_positiveCayley_lt_one hA)
  have he := signNewtonIterate_inverseCayley hp k
  rw [hA.inverseCayley_positiveCayley] at he
  refine ⟨he, ?_⟩
  rw [he]
  obtain ⟨hm, hp⟩ := isUnit_one_sub_and_add_matrix_pow hp (pow_pos (by norm_num : 0 < (2 : ℕ)) k)
  exact isUnit_inverseCayley hm hp

/-- Newton iteration converges to the identity for every positive-stable
matrix, including defective and nonnormal matrices. -/
private theorem IsPositiveStable.tendsto_signNewtonIterate {A : Matrix n n ℂ}
    (hA : IsPositiveStable A) : Tendsto (signNewtonIterate A) atTop (𝓝 1) := by
  have h := tendsto_signNewtonIterate_inverseCayley
    ((tendsto_pow_zero_iff_specRadius_lt_one _).mpr (specRadius_positiveCayley_lt_one hA))
  rwa [hA.inverseCayley_positiveCayley] at h

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every Newton iterate commutes with any matrix commuting with its input. -/
private theorem commute_signNewtonIterate {A S : Matrix n n ℂ} (h : Commute S A) (k : ℕ) :
    Commute S (signNewtonIterate A k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    change S * ((2 : ℂ)⁻¹ • (_ + _)) = ((2 : ℂ)⁻¹ • (_ + _)) * S
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      ih.eq, (commute_inv_right ih).eq]

/-- Multiplication by a commuting involution intertwines the exact
Newton recursions, including their total inverse conventions. -/
private theorem involution_mul_signNewtonIterate {A S : Matrix n n ℂ}
    (h : Commute S A) (hS : S ^ 2 = 1) (k : ℕ) :
    S * signNewtonIterate A k = signNewtonIterate (S * A) k := by
  have hSi : S⁻¹ = S := Matrix.inv_eq_right_inv (by simpa only [pow_two] using hS)
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [signNewtonIterate, signNewtonIterate, ← ih, Matrix.mul_inv_rev, hSi]
    simp only [Matrix.mul_smul, Matrix.mul_add,
        (commute_inv_right (commute_signNewtonIterate h k)).eq]

/-- The source's sign Cayley matrix equals the positive Cayley transform
of the positive-stable product `SA`. -/
private theorem IsMatrixSign.cayley_eq_positiveCayley {A S : Matrix n n ℂ} (hS : IsMatrixSign A S) :
    (A - S) * (A + S)⁻¹ = positiveCayley (S * A) := by
  have hs : S * S = 1 := by simpa only [pow_two] using hS.1
  have hSi : S⁻¹ = S := Matrix.inv_eq_right_inv hs
  have hSA : A * S = S * A := hS.2.1.eq
  have hc : Commute S (S * A) := by change S * (S * A) = (S * A) * S; noncomm_ring [hSA, hs]
  have hm : A - S = S * (S * A - 1) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hs, Matrix.one_mul, Matrix.mul_one]
  have hp : A + S = S * (S * A + 1) := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hs, Matrix.one_mul, Matrix.mul_one]
  rw [hm, hp, Matrix.mul_inv_rev, hSi]
  have ht : Commute S ((S * A - 1) * (S * A + 1)⁻¹) :=
    (hc.sub_right (Commute.one_right _)).mul_right
        (commute_inv_right (hc.add_right (Commute.one_right _)))
  change S * (S * A - 1) * ((S * A + 1)⁻¹ * S) = (S * A - 1) * (S * A + 1)⁻¹
  calc
    _ = S * ((S * A - 1) * (S * A + 1)⁻¹) * S := by noncomm_ring
    _ = ((S * A - 1) * (S * A + 1)⁻¹) * (S * S) := by rw [ht.eq]; noncomm_ring
    _ = _ := by rw [hs, Matrix.mul_one]

/-- The source's Cayley coordinate is spectrally contractive. -/
theorem IsMatrixSign.specRadius_mul_inv_lt_one {A S : Matrix n n ℂ} (hS : IsMatrixSign A S) :
    specRadius ((A - S) * (A + S)⁻¹) < 1 := by
  rw [hS.cayley_eq_positiveCayley]
  exact specRadius_positiveCayley_lt_one hS.2.2

/-- **Exact sign Newton iterates.** The commuting sign and the doubly powered Cayley coordinate
give the actual inverse-averaging iteration. [Higham2008, §5.3].
Result: matrix-sign-newton -/
theorem IsMatrixSign.signNewtonIterate_eq {A S : Matrix n n ℂ}
    (hS : IsMatrixSign A S) (k : ℕ) :
    signNewtonIterate A k = inverseCayley (((A - S) * (A + S)⁻¹) ^ (2 ^ k)) * S := by
  have hs : S * S = 1 := by simpa only [pow_two] using hS.1
  have hi := involution_mul_signNewtonIterate hS.2.1.symm hS.1 k
  have he := (hS.2.2.signNewtonIterate_eq_and_isUnit k).1
  have hc : Commute S (signNewtonIterate A k) := commute_signNewtonIterate hS.2.1.symm k
  have hv : S * signNewtonIterate A k = inverseCayley ((positiveCayley (S * A)) ^ (2 ^ k)) :=
      hi.trans he
  rw [hS.cayley_eq_positiveCayley, ← hv, hc.eq, Matrix.mul_assoc, hs, Matrix.mul_one]

/-- Every actual sign Newton iterate is nonsingular. -/
theorem IsMatrixSign.isUnit_signNewtonIterate {A S : Matrix n n ℂ}
    (hS : IsMatrixSign A S) (k : ℕ) : IsUnit (signNewtonIterate A k) := by
  rw [hS.signNewtonIterate_eq]
  have hp := (tendsto_pow_zero_iff_specRadius_lt_one _).mpr hS.specRadius_mul_inv_lt_one
  obtain ⟨hm, hp⟩ := isUnit_one_sub_and_add_matrix_pow hp (pow_pos (by norm_num : 0 < (2 : ℕ)) k)
  have hSu : IsUnit S := ⟨⟨S,S,by simpa only [pow_two] using hS.1,
    by simpa only [pow_two] using hS.1⟩, rfl⟩
  exact (isUnit_inverseCayley hm hp).mul hSu

/-- **Newton convergence to the matrix sign.** The actual inverse-averaging sequence converges
to the sign, including for nonnormal complex matrices. [Higham2008, §5.3].
Result: matrix-sign-newton -/
theorem IsMatrixSign.tendsto_signNewtonIterate {A S : Matrix n n ℂ}
    (hS : IsMatrixSign A S) : Tendsto (signNewtonIterate A) atTop (𝓝 S) := by
  have hp := (tendsto_pow_zero_iff_specRadius_lt_one _).mpr hS.specRadius_mul_inv_lt_one
  have ht := (tendsto_inverseCayley_one (hp.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)))).mul_const S
  convert! ht using 1
  · funext k; exact hS.signNewtonIterate_eq k
  · simp

/-- The exact Newton error identity for a commuting involution. -/
private theorem half_smul_add_inv_sub_involution {X S : Matrix n n ℂ}
    (hX : IsUnit X) (hS : S ^ 2 = 1) (hc : Commute X S) :
    (2 : ℂ)⁻¹ • (X + X⁻¹) - S = (2 : ℂ)⁻¹ • (X⁻¹ * (X - S) ^ 2) := by
  have hi := Matrix.nonsing_inv_mul X ((Matrix.isUnit_iff_isUnit_det _).mp hX)
  have hs : S * S = 1 := by simpa only [pow_two] using hS
  have hp : (X - S) ^ 2 = X * X - (2 : ℂ) • (X * S) + 1 := by
    simp only [two_smul]
    noncomm_ring [← hc.eq, hs]
  have hq : X⁻¹ * (X - S) ^ 2 = X + X⁻¹ - (2 : ℂ) • S := by
    rw [hp]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc,
      hi, Matrix.one_mul, Matrix.mul_one]
    abel
  rw [hq, smul_sub, smul_smul]
  norm_num

/-- **Quadratic Newton sign error.** For a sign involution and every Newton iterate, the
error equals half the inverse iterate times the preceding squared error. [Higham2008, §5.3].
Result: matrix-sign-newton -/
theorem IsMatrixSign.signNewtonIterate_succ_sub {A S : Matrix n n ℂ} (h : IsMatrixSign A S)
    (k : ℕ) : signNewtonIterate A (k + 1) - S =
      (2 : ℂ)⁻¹ • ((signNewtonIterate A k)⁻¹ * (signNewtonIterate A k - S) ^ 2) :=
  half_smul_add_inv_sub_involution (h.isUnit_signNewtonIterate k) h.1
    (commute_signNewtonIterate h.2.1.symm k).symm

/-- **Newton sign error bound.** For a sign involution $\mathbf{S}$, the next iterate satisfies
$$\|\mathbf{S}-\mathbf{X}_{k+1}\|_2\le\tfrac12\|\mathbf{X}_k^{-1}\|_2
\,\|\mathbf{S}-\mathbf{X}_k\|_2^2.$$
[Higham2008, §5.3].
Result: matrix-sign-newton -/
theorem IsMatrixSign.specNorm_sub_signNewtonIterate_le {A S : Matrix n n ℂ}
    (h : IsMatrixSign A S) (k : ℕ) :
    specNorm (S - signNewtonIterate A (k + 1)) ≤
      (1 / 2 : ℝ) * specNorm (signNewtonIterate A k)⁻¹
          * specNorm (S - signNewtonIterate A k) ^ 2 := by
  rw [specNorm_sub_comm S, h.signNewtonIterate_succ_sub, specNorm_smul,
    specNorm_sub_comm S, mul_assoc]
  have hn : ‖(2 : ℂ)⁻¹‖ = (1 / 2 : ℝ) := by norm_num
  rw [hn]
  let X := signNewtonIterate A k
  exact mul_le_mul_of_nonneg_left ((specNorm_mul_le X⁻¹ ((X - S) ^ 2)).trans
    (mul_le_mul_of_nonneg_left (specNorm_pow_le (X - S) 2) (specNorm_nonneg X⁻¹)))
    (by norm_num : (0 : ℝ) ≤ 1 / 2)


end NLAlib
