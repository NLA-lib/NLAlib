/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import NLAlib.Matrix.Spectral.CourantFischer
public import NLAlib.RandomMatrix.Gaussian.InverseMoments

/-!
# Spectral moments of the pseudoinverse of a Gaussian matrix

For a wide standard Gaussian matrix `G : r × k` (`r < k`),
`E ‖G†‖^q ≤ (e √((k + r - 1)/2) / (k - r))^q` for `0 < q ≤ k - r` (Halko, Martinsson and Tropp
2011, Proposition 10.4, in a sharper form), with `E ‖G†‖` as the case `q = 1` and the source's
`e √k / (k - r)` as a corollary. The constant `√((k + r - 1)/2)` is not from the literature: it is
what this proof reaches, and it is at most the source's `√k`.

The proof is by Gaussian probes and needs no eigenvalue density. For a positive semidefinite `A`
with top unit eigenvector `v`, `‖A‖ (v ⬝ z)² ≤ z ⬝ A z`; averaging over an independent standard
Gaussian `z` gives `E |N(0,1)|^{2q} ‖A‖^q ≤ E_z (z ⬝ A z)^q`. For `A = (G Gᴴ)⁻¹`, Tonelli and the
moments of the probes
(`NLAlib.integral_dotProduct_mul_conjTranspose_inv_mulVec_rpow_of_hasLaw_gaussianMatrix`) evaluate
the right side exactly, as `E ‖z‖^{2q} E (1/χ²_{k-r+1})^q`. At `q = (k - r)/2` Gamma estimates
(log-convexity and Stirling) give the constant; Lyapunov's inequality gives every smaller `q`.
`pinv` is total, and `‖G†‖² = ‖(G Gᴴ)⁻¹‖` off a null set; the integrals are unaffected.

## Main results

* `NLAlib.integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_specNorm_pinv_le_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {r k : Type*} [Fintype r]
  [Fintype k] {X : Ω → Matrix r k ℝ}

section Probes

variable [DecidableEq r]

private theorem measurable_inv_mul_conjTranspose :
    Measurable fun G : Matrix r k ℝ => (G * Gᴴ)⁻¹ := by
  classical
  exact (measurable_id.matrix_mul (continuous_id.matrix_conjTranspose).measurable).matrix_inv

private theorem dotProduct_inv_mul_conjTranspose_mulVec_nonneg (G : Matrix r k ℝ) (u : r → ℝ) :
    0 ≤ u ⬝ᵥ ((G * Gᴴ)⁻¹ *ᵥ u) := by
  simpa only [star_trivial] using
    (Matrix.posSemidef_self_mul_conjTranspose G).inv.dotProduct_mulVec_nonneg u

/-! ### Spectral probes -/

omit [DecidableEq r] in
/-- A top eigenvector `v` of a positive semidefinite `A` detects its norm:
`‖A‖ (v ⬝ z)² ≤ z ⬝ A z`. -/
private theorem specNorm_mul_dotProduct_sq_le {A : Matrix r r ℝ} (hA : A.PosSemidef)
    {v : r → ℝ} (hv : ‖WithLp.toLp 2 v‖ = 1) (hAv : A *ᵥ v = specNorm A • v) (z : r → ℝ) :
    specNorm A * (v ⬝ᵥ z) ^ 2 ≤ z ⬝ᵥ (A *ᵥ z) := by
  have hvv : v ⬝ᵥ v = 1 := by
    rw [← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hv, one_pow]
  set a := v ⬝ᵥ z with ha
  set w := z - a • v with hw
  have hvw : v ⬝ᵥ w = 0 := by
    rw [hw, dotProduct_sub, dotProduct_smul, hvv, smul_eq_mul, mul_one, ha, sub_self]
  have hz : z = a • v + w := by rw [hw, add_sub_cancel]
  have hAt : Aᵀ = A := by
    have h := hA.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hvAw : v ⬝ᵥ (A *ᵥ w) = 0 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hAt, hAv, smul_dotProduct, hvw,
      smul_zero]
  have hwAw : 0 ≤ w ⬝ᵥ (A *ᵥ w) := by
    simpa only [star_trivial] using hA.dotProduct_mulVec_nonneg w
  have hexp : z ⬝ᵥ (A *ᵥ z) = specNorm A * a ^ 2 + w ⬝ᵥ (A *ᵥ w) := by
    rw [hz]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hAv, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, hvAw, hvv, smul_eq_mul]
    rw [dotProduct_comm w v, hvw]
    ring
  rw [hexp]
  linarith

omit [DecidableEq r] in
/-- The moments of a squared unit projection of a standard Gaussian vector:
`E ((v ⬝ z)²)^q = 2^q Γ(1/2 + q) / √π`. -/
private theorem integrable_and_integral_dotProduct_sq_rpow {v : r → ℝ}
    (hv : ‖WithLp.toLp 2 v‖ = 1) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun z => ((v ⬝ᵥ z) ^ 2) ^ q) (gaussianVector r) ∧
      ∫ z, ((v ⬝ᵥ z) ^ 2) ^ q ∂(gaussianVector r) =
        2 ^ q * Real.Gamma (1 / 2 + q) / √Real.pi := by
  set B : Matrix Unit r ℝ := Matrix.of fun _ l => v l with hB
  have hBo : HasOrthonormalCols Bᴴ := by
    rw [hasOrthonormalCols_iff, Matrix.conjTranspose_conjTranspose]
    ext a b
    obtain rfl : a = b := Subsingleton.elim a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hB, Matrix.of_apply, star_trivial,
      Matrix.one_apply_eq]
    have h := EuclideanSpace.norm_toLp_sq_eq_dotProduct_self v
    rw [hv, one_pow] at h
    exact h.symm
  have hlaw := hasLaw_mulVec_of_hasLaw_gaussianVector (HasLaw.id (μ := gaussianVector r)) hBo
  have hnorm (z : r → ℝ) : ‖WithLp.toLp 2 (B *ᵥ z)‖ ^ 2 = (v ⬝ᵥ z) ^ 2 := by
    rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, Matrix.mulVec, hB,
      Matrix.of_apply, sq]
  have hint := integrable_norm_sq_rpow_of_hasLaw_gaussianVector hlaw (s := q)
    (by simp only [Fintype.card_unit]; linarith)
  have hval := integral_norm_sq_rpow_of_hasLaw_gaussianVector hlaw (s := q)
    (by simp only [Fintype.card_unit]; linarith)
  simp only [hnorm, id_eq, Fintype.card_unit, Nat.cast_one] at hint hval
  refine ⟨hint, ?_⟩
  rw [hval, add_comm, Real.Gamma_one_half_eq]

/-- The moment `E (z ⬝ (G Gᴴ)⁻¹ z)^q = ‖z‖^{2q} E (1/χ²_{k-r+1})^q` for a fixed `z`. -/
private theorem lintegral_dotProduct_inv_mul_conjTranspose_mulVec_rpow
    (hrk : Fintype.card r ≤ Fintype.card k) {q : ℝ} (hq0 : 0 < q)
    (hq : q < ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2) (z : r → ℝ) :
    ∫⁻ G, ENNReal.ofReal ((z ⬝ᵥ ((G * Gᴴ)⁻¹ *ᵥ z)) ^ q) ∂(gaussianMatrix r k) =
      ENNReal.ofReal ((‖WithLp.toLp 2 z‖ ^ 2) ^ q *
        (2 ^ (-q) * Real.Gamma (((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2 - q) /
          Real.Gamma (((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2))) := by
  by_cases hz : z = 0
  · subst hz
    simp only [Matrix.mulVec_zero, dotProduct_zero, Real.zero_rpow hq0.ne',
      ENNReal.ofReal_zero, lintegral_zero, WithLp.toLp_zero, norm_zero]
    rw [zero_pow two_ne_zero, Real.zero_rpow hq0.ne', zero_mul, ENNReal.ofReal_zero]
  set ρ := ‖WithLp.toLp 2 z‖ with hρ
  have hρ0 : 0 < ρ := norm_pos_iff.2 fun h => hz (by simpa using congrArg WithLp.ofLp h)
  set u := ρ⁻¹ • z with hu
  have hu1 : ‖WithLp.toLp 2 u‖ = 1 := by
    rw [hu, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ0, ← hρ,
      inv_mul_cancel₀ hρ0.ne']
  have hzu : z = ρ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hρ0.ne', one_smul]
  have hform (G : Matrix r k ℝ) : (z ⬝ᵥ ((G * Gᴴ)⁻¹ *ᵥ z)) ^ q =
      (ρ ^ 2) ^ q * (u ⬝ᵥ ((G * Gᴴ)⁻¹ *ᵥ u)) ^ q := by
    rw [← Real.mul_rpow (sq_nonneg _) (dotProduct_inv_mul_conjTranspose_mulVec_nonneg G u)]
    congr 1
    conv_lhs => rw [hzu]
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, sq,
      mul_assoc]
  have hcast : ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) =
      (Fintype.card k : ℝ) - Fintype.card r + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hrk, Nat.cast_one]
  rw [hcast] at hq ⊢
  have hint0 := integrable_dotProduct_mul_conjTranspose_inv_mulVec_rpow_of_hasLaw_gaussianMatrix
    (HasLaw.id (μ := gaussianMatrix r k)) hrk hu1 hq
  have hval := integral_dotProduct_mul_conjTranspose_inv_mulVec_rpow_of_hasLaw_gaussianMatrix
    (HasLaw.id (μ := gaussianMatrix r k)) hrk hu1 hq
  simp only [id_eq] at hint0 hval
  have hint := hint0.const_mul ((ρ ^ 2) ^ q)
  simp only [hform]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun G =>
      mul_nonneg (Real.rpow_nonneg (sq_nonneg _) _)
        (Real.rpow_nonneg (dotProduct_inv_mul_conjTranspose_mulVec_nonneg G u) _)),
    integral_const_mul, hval]

private theorem measurable_dotProduct_inv_mul_conjTranspose_mulVec :
    Measurable fun p : Matrix r k ℝ × (r → ℝ) => p.2 ⬝ᵥ ((p.1 * p.1ᴴ)⁻¹ *ᵥ p.2) :=
  (continuous_fst.dotProduct continuous_snd).measurable.comp
    (measurable_snd.prodMk ((measurable_inv_mul_conjTranspose.comp measurable_fst).matrix_mulVec
      measurable_snd))

/-- **The probe bound**: for `0 < q < (k - r + 1)/2`,
`c_q E ‖(G Gᴴ)⁻¹‖^q ≤ E ‖z‖^{2q} E (1/χ²_{k-r+1})^q`, with `c_q = E |N(0,1)|^{2q}`. -/
private theorem lintegral_specNorm_inv_rpow_le [Nonempty r]
    (hrk : Fintype.card r ≤ Fintype.card k) {q : ℝ} (hq0 : 0 < q)
    (hq : q < ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2) :
    ENNReal.ofReal (2 ^ q * Real.Gamma (1 / 2 + q) / √Real.pi) *
        ∫⁻ G, ENNReal.ofReal (specNorm (G * Gᴴ)⁻¹ ^ q) ∂(gaussianMatrix r k) ≤
      ENNReal.ofReal (2 ^ q * Real.Gamma ((Fintype.card r : ℝ) / 2 + q) /
          Real.Gamma ((Fintype.card r : ℝ) / 2) *
        (2 ^ (-q) * Real.Gamma (((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2 - q) /
          Real.Gamma (((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2))) := by
  set m := 2 ^ (-q) * Real.Gamma (((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2 - q) /
    Real.Gamma (((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2) with hm
  set c := 2 ^ q * Real.Gamma (1 / 2 + q) / √Real.pi with hc
  have hdetect (G : Matrix r k ℝ) : ENNReal.ofReal c * ENNReal.ofReal (specNorm (G * Gᴴ)⁻¹ ^ q) ≤
      ∫⁻ z, ENNReal.ofReal ((z ⬝ᵥ ((G * Gᴴ)⁻¹ *ᵥ z)) ^ q) ∂(gaussianVector r) := by
    have hA := (Matrix.posSemidef_self_mul_conjTranspose G).inv
    obtain ⟨v, hv, hAv⟩ := hA.exists_norm_eq_one_and_mulVec_eq_specNorm_smul
    obtain ⟨hint, hval⟩ := integrable_and_integral_dotProduct_sq_rpow hv hq0.le
    rw [← hc] at hval
    rw [← ENNReal.ofReal_mul (by rw [hc]; positivity), mul_comm, ← hval, ← integral_const_mul,
      ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) (Filter.Eventually.of_forall
        fun z => mul_nonneg (Real.rpow_nonneg (specNorm_nonneg _) _)
          (Real.rpow_nonneg (sq_nonneg _) _))]
    refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    rw [← Real.mul_rpow (specNorm_nonneg _) (sq_nonneg _)]
    exact Real.rpow_le_rpow (mul_nonneg (specNorm_nonneg _) (sq_nonneg _))
      (specNorm_mul_dotProduct_sq_le hA hv hAv z) hq0.le
  have hjoint : AEMeasurable (Function.uncurry fun (G : Matrix r k ℝ) (z : r → ℝ) =>
      ENNReal.ofReal ((z ⬝ᵥ ((G * Gᴴ)⁻¹ *ᵥ z)) ^ q))
      ((gaussianMatrix r k).prod (gaussianVector r)) :=
    ((measurable_dotProduct_inv_mul_conjTranspose_mulVec.pow_const q).ennreal_ofReal).aemeasurable
  have hr0 : (0 : ℝ) ≤ Fintype.card r := Nat.cast_nonneg _
  have hnormint := (integrable_norm_sq_rpow_of_hasLaw_gaussianVector
    (HasLaw.id (μ := gaussianVector r)) (s := q) (by linarith)).mul_const m
  simp only [id_eq] at hnormint
  calc ENNReal.ofReal c * ∫⁻ G, ENNReal.ofReal (specNorm (G * Gᴴ)⁻¹ ^ q) ∂(gaussianMatrix r k)
      = ∫⁻ G, ENNReal.ofReal c * ENNReal.ofReal (specNorm (G * Gᴴ)⁻¹ ^ q)
          ∂(gaussianMatrix r k) := (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ G, ∫⁻ z, ENNReal.ofReal ((z ⬝ᵥ ((G * Gᴴ)⁻¹ *ᵥ z)) ^ q) ∂(gaussianVector r)
          ∂(gaussianMatrix r k) := lintegral_mono hdetect
    _ = ∫⁻ z, ∫⁻ G, ENNReal.ofReal ((z ⬝ᵥ ((G * Gᴴ)⁻¹ *ᵥ z)) ^ q) ∂(gaussianMatrix r k)
          ∂(gaussianVector r) := lintegral_lintegral_swap hjoint
    _ = ∫⁻ z, ENNReal.ofReal ((‖WithLp.toLp 2 z‖ ^ 2) ^ q * m) ∂(gaussianVector r) := by
        simp only [lintegral_dotProduct_inv_mul_conjTranspose_mulVec_rpow hrk hq0 hq, hm]
    _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hnormint (Filter.Eventually.of_forall fun z =>
          mul_nonneg (Real.rpow_nonneg (sq_nonneg _) _) (by
            rw [hm]
            have := Real.Gamma_pos_of_pos (show (0 : ℝ) <
              ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2 - q by linarith)
            have := Real.Gamma_pos_of_pos (show (0 : ℝ) <
              ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2 by positivity)
            positivity)), integral_mul_const]
        have h := integral_norm_sq_rpow_of_hasLaw_gaussianVector
          (HasLaw.id (μ := gaussianVector r)) (s := q) (by linarith)
        simp only [id_eq] at h
        rw [h]

/-! ### Gamma estimates -/

section GammaBounds

open Real

/-- `Γ(x + 1/2) ≤ Γ(x) √x` (log-convexity). -/
private theorem Gamma_add_half_le_mul_sqrt {x : ℝ} (hx : 0 < x) :
    Gamma (x + 1 / 2) ≤ Gamma x * √x := by
  have h := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx (by linarith : 0 < x + 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hG : 0 < Gamma x := Gamma_pos_of_pos hx
  rw [show 1 / 2 * x + 1 / 2 * (x + 1) = x + 1 / 2 by ring, Gamma_add_one hx.ne',
    ← Real.mul_rpow hG.le (by positivity), ← Real.sqrt_eq_rpow,
    show Gamma x * (x * Gamma x) = Gamma x ^ 2 * x by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hG.le] at h
  exact h

/-- AM–GM for an arithmetic progression. -/
private theorem prod_range_add_le_pow (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ∏ i ∈ Finset.range (n + 1), (a + i) ≤ ((2 * a + n) / 2) ^ (n + 1) := by
  set M := (2 * a + n) / 2 with hM
  have hpos : ∀ i ∈ Finset.range (n + 1), 0 ≤ a + (i : ℝ) := fun i _ => by positivity
  have hP : 0 ≤ ∏ i ∈ Finset.range (n + 1), (a + (i : ℝ)) := Finset.prod_nonneg hpos
  have hMpos : 0 ≤ M := by rw [hM]; positivity
  have hrefl : ∏ i ∈ Finset.range (n + 1), (a + ((n - i : ℕ) : ℝ)) =
      ∏ i ∈ Finset.range (n + 1), (a + (i : ℝ)) := by
    have := Finset.prod_range_reflect (fun i : ℕ => a + (i : ℝ)) (n + 1)
    simpa using this
  have hsq : (∏ i ∈ Finset.range (n + 1), (a + (i : ℝ))) ^ 2 ≤ (M ^ (n + 1)) ^ 2 := by
    rw [sq]
    calc (∏ i ∈ Finset.range (n + 1), (a + (i : ℝ))) * ∏ i ∈ Finset.range (n + 1), (a + (i : ℝ))
        = (∏ i ∈ Finset.range (n + 1), (a + (i : ℝ))) *
            ∏ i ∈ Finset.range (n + 1), (a + ((n - i : ℕ) : ℝ)) := by rw [hrefl]
      _ = ∏ i ∈ Finset.range (n + 1), ((a + (i : ℝ)) * (a + ((n - i : ℕ) : ℝ))) :=
          Finset.prod_mul_distrib.symm
      _ ≤ ∏ _i ∈ Finset.range (n + 1), M ^ 2 := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i hi
            have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
            rw [Nat.cast_sub hin, hM]
            nlinarith [sq_nonneg ((i : ℝ) - ((n : ℝ) - i))]
      _ = (M ^ (n + 1)) ^ 2 := by
          rw [Finset.prod_const, Finset.card_range, ← pow_mul, ← pow_mul, mul_comm]
  exact (pow_le_pow_iff_left₀ hP (pow_nonneg hMpos _) two_ne_zero).1 hsq

private theorem Gamma_add_nat_div_two_sq_le_mul_prod {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Gamma (x + n / 2) ^ 2 ≤ Gamma x ^ 2 * ∏ i ∈ Finset.range n, (x + i / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : 0 < x + (n : ℝ) / 2 := by positivity
    have hg : Gamma (x + n / 2 + 1 / 2) ^ 2 ≤ (x + n / 2) * Gamma (x + n / 2) ^ 2 := by
      have h0 : 0 ≤ Gamma (x + n / 2 + 1 / 2) := (Gamma_pos_of_pos (by linarith)).le
      calc Gamma (x + n / 2 + 1 / 2) ^ 2 ≤ (Gamma (x + n / 2) * √(x + n / 2)) ^ 2 :=
            pow_le_pow_left₀ h0 (Gamma_add_half_le_mul_sqrt hz) 2
        _ = _ := by rw [mul_pow, Real.sq_sqrt hz.le]; ring
    have he : x + n / 2 + 1 / 2 = x + ((n + 1 : ℕ) : ℝ) / 2 := by push_cast; ring
    rw [he] at hg
    rw [Finset.prod_range_succ]
    calc Gamma (x + ((n + 1 : ℕ) : ℝ) / 2) ^ 2 ≤ (x + n / 2) * Gamma (x + n / 2) ^ 2 := hg
      _ ≤ (x + n / 2) * (Gamma x ^ 2 * ∏ i ∈ Finset.range n, (x + i / 2)) :=
          mul_le_mul_of_nonneg_left ih hz.le
      _ = _ := by ring

private theorem Gamma_add_nat_div_two_le {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    Gamma (x + n / 2) ≤ Gamma x * (x + ((n : ℝ) - 1) / 4) ^ ((n : ℝ) / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := Gamma_add_nat_div_two_sq_le_mul_prod hx (m + 1)
  have h2 := prod_range_add_le_pow (2 * x) (by positivity) m
  have hprod : ∏ i ∈ Finset.range (m + 1), (x + i / 2) =
      (∏ i ∈ Finset.range (m + 1), (2 * x + i)) / 2 ^ (m + 1) := by
    calc _ = ∏ i ∈ Finset.range (m + 1), ((2 * x + i) / 2) :=
          Finset.prod_congr rfl fun i _ => by ring
      _ = _ := by rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  rw [hprod] at h1
  have h3 : (∏ i ∈ Finset.range (m + 1), (2 * x + i)) / 2 ^ (m + 1) ≤ (x + m / 4) ^ (m + 1) := by
    calc _ ≤ ((2 * (2 * x) + m) / 2) ^ (m + 1) / 2 ^ (m + 1) := by gcongr
      _ = (x + m / 4) ^ (m + 1) := by rw [← div_pow]; congr 1; ring
  have h4 := h1.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))
  have hxmean : 0 ≤ x + (m : ℝ) / 4 := by positivity
  have hrpow : (x + (m : ℝ) / 4) ^ (((m + 1 : ℕ) : ℝ) / 2) =
      √((x + (m : ℝ) / 4) ^ (m + 1)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hxmean]
    congr 1; push_cast; ring
  have hs := Real.sqrt_le_sqrt h4
  rw [Real.sqrt_sq (Gamma_pos_of_pos (by positivity)).le, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (Gamma_pos_of_pos hx).le] at hs
  convert hs using 1
  rw [show ((m + 1 : ℕ) : ℝ) - 1 = m by push_cast; ring, hrpow]

private theorem Gamma_nat_add_one_div_two_sq_ge {d : ℕ} (hd : 1 ≤ d) :
    π * ((d : ℝ) / (2 * exp 1)) ^ d ≤ Gamma (((d : ℝ) + 1) / 2) ^ 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set z : ℝ := ((d : ℝ) + 1) / 2 with hz
  have hz0 : 0 < z := by positivity
  have hg0 := Gamma_pos_of_pos hz0
  have hdup := Gamma_mul_Gamma_add_half_of_pos hz0
  have hdup' : Gamma z * Gamma (z + 1 / 2) = (d.factorial : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) * √π := by
    rw [show 1 - 2 * z = -(d : ℝ) by rw [hz]; ring, show 2 * z = (d : ℝ) + 1 by rw [hz]; ring,
      Gamma_nat_eq_factorial] at hdup
    exact hdup
  have hupper : (d.factorial : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) * √π ≤ Gamma z ^ 2 * √z := by
    rw [← hdup']
    have := mul_le_mul_of_nonneg_left (Gamma_add_half_le_mul_sqrt hz0) hg0.le
    nlinarith
  have htwo : (2 : ℝ) ^ (-(d : ℝ)) * 2 ^ d = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    simp
  have hfac : (d.factorial : ℝ) * √π ≤ 2 ^ d * Gamma z ^ 2 * √z := by
    calc _ = 2 ^ d * ((d.factorial : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) * √π) := by
          rw [show 2 ^ d * ((d.factorial : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) * √π) =
            (d.factorial : ℝ) * ((2 : ℝ) ^ (-(d : ℝ)) * 2 ^ d) * √π by ring, htwo, mul_one]
      _ ≤ 2 ^ d * (Gamma z ^ 2 * √z) := by gcongr
      _ = _ := by ring
  have hsqrt : π * √z ≤ √(2 * π * d) * √π := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1
    rw [mul_pow, Real.sq_sqrt hz0.le, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt pi_pos.le, hz]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [sq_nonneg π, pi_pos]
  have hst := Stirling.le_factorial_stirling d
  have hpower : (2 : ℝ) ^ d * ((d : ℝ) / (2 * exp 1)) ^ d = ((d : ℝ) / exp 1) ^ d := by
    rw [← mul_pow]; congr 1; field_simp
  have hfinal : 2 ^ d * (π * ((d : ℝ) / (2 * exp 1)) ^ d) * √z ≤ 2 ^ d * Gamma z ^ 2 * √z := by
    calc _ = (π * √z) * ((d : ℝ) / exp 1) ^ d := by rw [← hpower]; ring
      _ ≤ (√(2 * π * d) * √π) * ((d : ℝ) / exp 1) ^ d := by gcongr
      _ = (√(2 * π * d) * ((d : ℝ) / exp 1) ^ d) * √π := by ring
      _ ≤ (d.factorial : ℝ) * √π := by gcongr
      _ ≤ _ := hfac
  exact le_of_mul_le_mul_left (le_of_mul_le_mul_right hfinal (Real.sqrt_pos.mpr hz0))
    (by positivity)

private theorem Gamma_endpoint_moment_le {x : ℝ} (hx : 0 < x) {d : ℕ} (hd : 1 ≤ d) :
    2 ^ (-(d : ℝ) / 2) * π * Gamma (x + d / 2) / (Gamma x * Gamma (((d : ℝ) + 1) / 2) ^ 2) ≤
      (2 * exp 1 ^ 2 * (x + ((d : ℝ) - 1) / 4) / (d : ℝ) ^ 2) ^ ((d : ℝ) / 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set q : ℝ := (d : ℝ) / 2 with hq
  set M : ℝ := x + ((d : ℝ) - 1) / 4 with hM
  set T : ℝ := (d : ℝ) / (2 * exp 1) with hT
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hM0 : 0 < M := by rw [hM]; linarith
  have hT0 : 0 < T := by rw [hT]; positivity
  have hg0 := Gamma_pos_of_pos hx
  have hz0 := Gamma_pos_of_pos (show 0 < ((d : ℝ) + 1) / 2 by positivity)
  have hratio : Gamma (x + d / 2) / Gamma x ≤ M ^ q := by
    apply (div_le_iff₀ hg0).2
    simpa [hM, hq, mul_comm] using Gamma_add_nat_div_two_le hx hd
  have hinv : π / Gamma (((d : ℝ) + 1) / 2) ^ 2 ≤ 1 / T ^ d := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simpa [hT] using Gamma_nat_add_one_div_two_sq_ge hd
  have hfactor : 2 ^ (-q) * π * Gamma (x + d / 2) / (Gamma x * Gamma (((d : ℝ) + 1) / 2) ^ 2) ≤
      2 ^ (-q) * M ^ q / T ^ d := by
    calc _ = 2 ^ (-q) * (Gamma (x + d / 2) / Gamma x) * (π / Gamma (((d : ℝ) + 1) / 2) ^ 2) := by
          ring
      _ ≤ 2 ^ (-q) * M ^ q * (1 / T ^ d) := by gcongr
      _ = _ := by ring
  have hTpow : T ^ d = (T ^ 2) ^ q := by
    rw [← Real.rpow_natCast T d, ← Real.rpow_natCast T 2, ← Real.rpow_mul hT0.le]
    congr 1; rw [hq]; push_cast; ring
  have htwo : (2 : ℝ) ^ (-q) = (1 / 2 : ℝ) ^ q := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  have heq : 2 ^ (-q) * M ^ q / T ^ d = (2 * exp 1 ^ 2 * M / (d : ℝ) ^ 2) ^ q := by
    rw [hTpow, htwo, ← Real.mul_rpow (by norm_num) hM0.le,
      ← Real.div_rpow (by positivity) (by positivity)]
    congr 1
    rw [hT]
    field_simp
  simpa [hq, hM, neg_div] using hfactor.trans heq.le

/-- The endpoint constant: for `1 ≤ r < k`,
`2^{-(k-r)/2} π Γ(k/2) / (Γ(r/2) Γ((k-r+1)/2)²) ≤ (e² (k+r-1) / (2 (k-r)²))^{(k-r)/2}`. -/
private theorem gamma_inverse_spectral_endpoint_le {r k : ℕ} (hr : 1 ≤ r) (hrk : r < k) :
    2 ^ (-((k : ℝ) - r) / 2) * π * Gamma ((k : ℝ) / 2) /
        (Gamma ((r : ℝ) / 2) * Gamma (((k : ℝ) - r + 1) / 2) ^ 2) ≤
      (exp 1 ^ 2 * ((k : ℝ) + r - 1) / (2 * ((k : ℝ) - r) ^ 2)) ^ (((k : ℝ) - r) / 2) := by
  obtain ⟨d, hk⟩ := Nat.exists_eq_add_of_le hrk.le
  have hd : 1 ≤ d := by omega
  subst k
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have h := Gamma_endpoint_moment_le (show 0 < (r : ℝ) / 2 by positivity) hd
  have he1 : (r : ℝ) / 2 + d / 2 = ((r : ℝ) + d) / 2 := by ring
  have he2 : 2 * exp 1 ^ 2 * ((r : ℝ) / 2 + ((d : ℝ) - 1) / 4) / (d : ℝ) ^ 2 =
      exp 1 ^ 2 * (((r : ℝ) + d) + r - 1) / (2 * (d : ℝ) ^ 2) := by ring
  rw [he1, he2] at h
  simpa only [Nat.cast_add, add_sub_cancel_left] using h


end GammaBounds

/-! ### Moment comparison -/

/-- A lower nonnegative moment is integrable when a higher one is. -/
private theorem integrable_rpow_of_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsFiniteMeasure ν] {f : α → ℝ} {p q : ℝ} (hf : AEStronglyMeasurable f ν)
    (hfnn : ∀ x, 0 ≤ f x) (hp : 0 ≤ p) (hpq : p ≤ q) (hfq : Integrable (fun x => f x ^ q) ν) :
    Integrable (fun x => f x ^ p) ν := by
  have hnorm : ∀ x, ‖f x‖ = f x := fun x => Real.norm_of_nonneg (hfnn x)
  have hfq' : Integrable (fun x => ‖f x‖ ^ q) ν := by simpa only [hnorm] using hfq
  simpa only [hnorm] using integrable_norm_rpow_of_le hf hp (hp.trans hpq) hpq hfq'

/-- **Lyapunov's inequality** in the form `E f^q ≤ C^q ⟹ E f^p ≤ C^p` for `0 < p ≤ q`. -/
private theorem integral_rpow_le_of_integral_rpow_le {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsProbabilityMeasure ν] {f : α → ℝ} {p q C : ℝ}
    (hf : AEStronglyMeasurable f ν) (hfnn : ∀ x, 0 ≤ f x) (hp : 0 < p) (hpq : p ≤ q)
    (hC : 0 ≤ C) (hfq : Integrable (fun x => f x ^ q) ν) (hbound : ∫ x, f x ^ q ∂ν ≤ C ^ q) :
    ∫ x, f x ^ p ∂ν ≤ C ^ p := by
  have hq : 0 < q := hp.trans_le hpq
  have hnorm : ∀ x, ‖f x‖ = f x := fun x => Real.norm_of_nonneg (hfnn x)
  have hfp := integrable_rpow_of_le hf hfnn hp.le hpq hfq
  have hMp : MemLp f (ENNReal.ofReal p) ν :=
    (integrable_norm_rpow_iff hf (by simp [hp]) (by simp)).1
      (by simpa only [ENNReal.toReal_ofReal hp.le, hnorm] using hfp)
  have hMq : MemLp f (ENNReal.ofReal q) ν :=
    (integrable_norm_rpow_iff hf (by simp [hq]) (by simp)).1
      (by simpa only [ENNReal.toReal_ofReal hq.le, hnorm] using hfq)
  have hmono := eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq) hf (μ := ν)
  rw [hMp.eLpNorm_eq_integral_rpow_norm (by simp [hp]) (by simp),
    hMq.eLpNorm_eq_integral_rpow_norm (by simp [hq]) (by simp)] at hmono
  simp only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le, hnorm] at hmono
  have hpint : 0 ≤ ∫ x, f x ^ p ∂ν := integral_nonneg fun x => Real.rpow_nonneg (hfnn x) _
  have hqint : 0 ≤ ∫ x, f x ^ q ∂ν := integral_nonneg fun x => Real.rpow_nonneg (hfnn x) _
  have hroot : (∫ x, f x ^ p ∂ν) ^ p⁻¹ ≤ C :=
    ((ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hqint _)).1 hmono).trans <|
      (Real.rpow_le_rpow hqint hbound (by positivity)).trans_eq (Real.rpow_rpow_inv hC hq.ne')
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hpint _) hroot hp.le
  rwa [Real.rpow_inv_rpow hpint hp.ne'] at h

/-! ### Spectral moments of `(G Gᴴ)⁻¹` -/

private theorem measurable_specNorm_inv_mul_conjTranspose :
    Measurable fun G : Matrix r k ℝ => specNorm (G * Gᴴ)⁻¹ :=
  measurable_specNorm.comp measurable_inv_mul_conjTranspose

private theorem integrable_and_integral_specNorm_inv_rpow_le [Nonempty r]
    (hrk : Fintype.card r ≤ Fintype.card k) {q : ℝ} (hq0 : 0 < q)
    (hq : q < ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2) :
    Integrable (fun G : Matrix r k ℝ => specNorm (G * Gᴴ)⁻¹ ^ q) (gaussianMatrix r k) ∧
      ∫ G, specNorm (G * Gᴴ)⁻¹ ^ q ∂(gaussianMatrix r k) ≤
        2 ^ q * Real.Gamma ((Fintype.card r : ℝ) / 2 + q) / Real.Gamma ((Fintype.card r : ℝ) / 2) *
          (2 ^ (-q) * Real.Gamma (((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2 - q) /
            Real.Gamma (((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2)) /
          (2 ^ q * Real.Gamma (1 / 2 + q) / √Real.pi) := by
  set c := 2 ^ q * Real.Gamma (1 / 2 + q) / √Real.pi with hc
  set a := 2 ^ q * Real.Gamma ((Fintype.card r : ℝ) / 2 + q) /
      Real.Gamma ((Fintype.card r : ℝ) / 2) *
    (2 ^ (-q) * Real.Gamma (((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2 - q) /
      Real.Gamma (((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2)) with ha
  have hr0 : (0 : ℝ) < Fintype.card r := by exact_mod_cast Fintype.card_pos
  have hc0 : 0 < c := by
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 + q by linarith)
    rw [hc]; positivity
  have ha0 : 0 ≤ a := by
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < (Fintype.card r : ℝ) / 2 + q by positivity)
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < (Fintype.card r : ℝ) / 2 by positivity)
    have := Real.Gamma_pos_of_pos
      (show (0 : ℝ) < ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2 - q by linarith)
    have := Real.Gamma_pos_of_pos
      (show (0 : ℝ) < ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) / 2 by positivity)
    rw [ha]; positivity
  have hL := lintegral_specNorm_inv_rpow_le hrk hq0 hq
  rw [← hc, ← ha] at hL
  have hbound : ∫⁻ G, ENNReal.ofReal (specNorm (G * Gᴴ)⁻¹ ^ q) ∂(gaussianMatrix r k) ≤
      ENNReal.ofReal (a / c) := by
    rw [ENNReal.ofReal_div_of_pos hc0]
    exact ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hc0)) (Or.inl ENNReal.ofReal_ne_top)
      |>.2 (by rwa [mul_comm])
  have hnn (G : Matrix r k ℝ) : 0 ≤ specNorm (G * Gᴴ)⁻¹ ^ q :=
    Real.rpow_nonneg (specNorm_nonneg _) _
  have hm := (measurable_specNorm_inv_mul_conjTranspose (k := k) (r := r)).pow_const q
  have hint : Integrable (fun G : Matrix r k ℝ => specNorm (G * Gᴴ)⁻¹ ^ q)
      (gaussianMatrix r k) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg ha0 hc0.le)).1 hbound

/-- `E ‖(G Gᴴ)⁻¹‖^p ≤ (e² (k + r - 1) / (2 (k - r)²))^p` for `0 < p ≤ (k - r)/2`. -/
private theorem integrable_and_integral_specNorm_inv_rpow_le_pow [Nonempty r]
    (hrk : Fintype.card r < Fintype.card k) {p : ℝ} (hp0 : 0 < p)
    (hp : p ≤ ((Fintype.card k : ℝ) - Fintype.card r) / 2) :
    Integrable (fun G : Matrix r k ℝ => specNorm (G * Gᴴ)⁻¹ ^ p) (gaussianMatrix r k) ∧
      ∫ G, specNorm (G * Gᴴ)⁻¹ ^ p ∂(gaussianMatrix r k) ≤
        (Real.exp 1 ^ 2 * ((Fintype.card k : ℝ) + Fintype.card r - 1) /
          (2 * ((Fintype.card k : ℝ) - Fintype.card r) ^ 2)) ^ p := by
  set R : ℝ := (Fintype.card r : ℝ) with hR
  set K : ℝ := (Fintype.card k : ℝ) with hK
  have hR1 : (1 : ℝ) ≤ R := by rw [hR]; exact_mod_cast Fintype.card_pos
  have hRK : R < K := by rw [hR, hK]; exact_mod_cast hrk
  have hd : ((Fintype.card k - Fintype.card r + 1 : ℕ) : ℝ) = K - R + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hrk.le, Nat.cast_one]
  set q := (K - R) / 2 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  obtain ⟨hint, hbound⟩ := integrable_and_integral_specNorm_inv_rpow_le (k := k) hrk.le hq0
    (by rw [hd, hq]; linarith)
  rw [hd, show R / 2 + q = K / 2 by rw [hq]; ring,
    show (K - R + 1) / 2 - q = 1 / 2 by rw [hq]; ring,
    show 1 / 2 + q = (K - R + 1) / 2 by rw [hq]; ring, Real.Gamma_one_half_eq] at hbound
  have hC : 0 ≤ Real.exp 1 ^ 2 * (K + R - 1) / (2 * (K - R) ^ 2) := by
    apply div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by positivity)
  have hend := gamma_inverse_spectral_endpoint_le (r := Fintype.card r) (k := Fintype.card k)
    Fintype.card_pos hrk
  rw [← hR, ← hK] at hend
  have heq : 2 ^ q * Real.Gamma (K / 2) / Real.Gamma (R / 2) *
      (2 ^ (-q) * √Real.pi / Real.Gamma ((K - R + 1) / 2)) /
        (2 ^ q * Real.Gamma ((K - R + 1) / 2) / √Real.pi) =
      2 ^ (-(K - R) / 2) * Real.pi * Real.Gamma (K / 2) /
        (Real.Gamma (R / 2) * Real.Gamma ((K - R + 1) / 2) ^ 2) := by
    have h1 := (Real.Gamma_pos_of_pos (show 0 < R / 2 by positivity)).ne'
    have h2 := (Real.Gamma_pos_of_pos (show 0 < (K - R + 1) / 2 by linarith)).ne'
    have h3 := (Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) q).ne'
    have h4 : √Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
    rw [neg_div, ← hq, Real.rpow_neg (by norm_num)]
    field_simp
    rw [Real.sq_sqrt Real.pi_pos.le]
  rw [heq] at hbound
  have hfm := (measurable_specNorm_inv_mul_conjTranspose (k := k) (r := r)).aestronglyMeasurable
    (μ := gaussianMatrix r k)
  exact ⟨integrable_rpow_of_le hfm (fun _ => specNorm_nonneg _) hp0.le hp hint,
    integral_rpow_le_of_integral_rpow_le hfm (fun _ => specNorm_nonneg _) hp0 hp hC hint
      (hbound.trans hend)⟩

end Probes

/-- Almost surely `‖G†‖^q = ‖(G Gᴴ)⁻¹‖^{q/2}`. -/
private theorem ae_specNorm_pinv_rpow_eq [DecidableEq r] (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r ≤ Fintype.card k) (q : ℝ) :
    ∀ᵐ ω ∂μ, specNorm (pinv (X ω)) ^ q = specNorm (X ω * (X ω)ᴴ)⁻¹ ^ (q / 2) := by
  filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hX] with ω hω
  have hinj : Function.Injective (X ω)ᴴ.mulVec := by
    rw [mulVec_injective_iff_rank_eq, Matrix.rank_conjTranspose, hω, min_eq_left hrk]
  have hunit : IsUnit (X ω * (X ω)ᴴ) := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      (isUnit_conjTranspose_mul_self_iff (A := (X ω)ᴴ)).2 hinj
  have hsq : specNorm (pinv (X ω)) ^ 2 = specNorm (X ω * (X ω)ᴴ)⁻¹ := by
    have h := specNorm_pinv_sq (X ω)ᴴ
    rwa [pinv_conjTranspose, specNorm_conjTranspose, Matrix.conjTranspose_conjTranspose,
      pinv_of_isUnit hunit] at h
  rw [← hsq, ← Real.rpow_natCast, ← Real.rpow_mul (specNorm_nonneg _)]
  congr 1
  push_cast
  ring

/-- `‖G†‖^q` is integrable for `0 < q ≤ k - r`. -/
theorem integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) {q : ℝ} (hq0 : 0 < q)
    (hq : q ≤ (Fintype.card k : ℝ) - Fintype.card r) :
    Integrable (fun ω => specNorm (pinv (X ω)) ^ q) μ := by
  classical
  have := hX.isProbabilityMeasure
  rcases isEmpty_or_nonempty r with hr | hr
  · have h0 (ω : Ω) : specNorm (pinv (X ω)) ^ q = 0 := by
      rw [Subsingleton.elim (pinv (X ω)) 0, specNorm_zero, Real.zero_rpow hq0.ne']
    simp only [h0]
    exact integrable_zero _ _ _
  have hrk : Fintype.card r < Fintype.card k := by
    have : (Fintype.card r : ℝ) < Fintype.card k := by linarith
    exact_mod_cast this
  obtain ⟨hint, -⟩ := integrable_and_integral_specNorm_inv_rpow_le_pow hrk (p := q / 2)
    (by positivity) (by linarith)
  have hm := ((measurable_specNorm_inv_mul_conjTranspose (r := r) (k := k)).pow_const (q / 2))
  refine ((hX.integrable_comp_iff hm.aestronglyMeasurable).2 hint).congr ?_
  filter_upwards [ae_specNorm_pinv_rpow_eq hX hrk.le q] with ω hω
  exact hω.symm

/-- **The spectral moments of `G†`**: `E ‖G†‖^q ≤ (e √((k + r - 1)/2) / (k - r))^q` for
`0 < q ≤ k - r` (Halko, Martinsson and Tropp, Proposition 10.4, in a sharper form: the constant
`√((k + r - 1)/2)` in place of `√k` is what the proof by probes reaches). -/
theorem integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) {q : ℝ} (hq0 : 0 < q)
    (hq : q ≤ (Fintype.card k : ℝ) - Fintype.card r) :
    ∫ ω, specNorm (pinv (X ω)) ^ q ∂μ ≤
      (Real.exp 1 / ((Fintype.card k : ℝ) - Fintype.card r) *
        √(((Fintype.card k : ℝ) + Fintype.card r - 1) / 2)) ^ q := by
  classical
  have := hX.isProbabilityMeasure
  have hB : 0 ≤ Real.exp 1 / ((Fintype.card k : ℝ) - Fintype.card r) *
      √(((Fintype.card k : ℝ) + Fintype.card r - 1) / 2) :=
    mul_nonneg (div_nonneg (Real.exp_pos 1).le (by linarith)) (Real.sqrt_nonneg _)
  rcases isEmpty_or_nonempty r with hr | hr
  · have h0 (ω : Ω) : specNorm (pinv (X ω)) ^ q = 0 := by
      rw [Subsingleton.elim (pinv (X ω)) 0, specNorm_zero, Real.zero_rpow hq0.ne']
    simp only [h0, integral_zero]
    exact Real.rpow_nonneg hB _
  have hR1 : (1 : ℝ) ≤ Fintype.card r := by exact_mod_cast Fintype.card_pos
  have hrk : Fintype.card r < Fintype.card k := by
    have : (Fintype.card r : ℝ) < Fintype.card k := by linarith
    exact_mod_cast this
  obtain ⟨-, hbound⟩ := integrable_and_integral_specNorm_inv_rpow_le_pow hrk (p := q / 2)
    (by positivity) (by linarith)
  have hm := ((measurable_specNorm_inv_mul_conjTranspose (r := r) (k := k)).pow_const (q / 2))
  rw [integral_congr_ae (ae_specNorm_pinv_rpow_eq hX hrk.le q)]
  have h := hX.integral_comp hm.aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h]
  refine hbound.trans_eq ?_
  have hsq : Real.exp 1 ^ 2 * ((Fintype.card k : ℝ) + Fintype.card r - 1) /
      (2 * ((Fintype.card k : ℝ) - Fintype.card r) ^ 2) =
      (Real.exp 1 / ((Fintype.card k : ℝ) - Fintype.card r) *
        √(((Fintype.card k : ℝ) + Fintype.card r - 1) / 2)) ^ (2 : ℕ) := by
    have hkr : (Fintype.card k : ℝ) - Fintype.card r ≠ 0 := by
      have : (Fintype.card r : ℝ) < Fintype.card k := by exact_mod_cast hrk
      linarith
    rw [mul_pow, div_pow, Real.sq_sqrt (by linarith)]
    field_simp
  rw [hsq, ← Real.rpow_natCast, ← Real.rpow_mul hB]
  congr 1
  push_cast
  ring

/-- `E ‖G†‖ ≤ e √((k + r - 1)/2) / (k - r)` for `r < k`: the case `q = 1`. -/
theorem integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r < Fintype.card k) :
    ∫ ω, specNorm (pinv (X ω)) ∂μ ≤
      Real.exp 1 / ((Fintype.card k : ℝ) - Fintype.card r) *
        √(((Fintype.card k : ℝ) + Fintype.card r - 1) / 2) := by
  have hrk' : (Fintype.card r : ℝ) + 1 ≤ Fintype.card k := by exact_mod_cast hrk
  have h := integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix hX one_pos (by linarith)
  simpa only [Real.rpow_one] using h

/-- The form of Halko, Martinsson and Tropp (Proposition 10.2), `E ‖G†‖ ≤ e √k / (k - r)`;
weaker in every regime and proved from `integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix`. -/
theorem integral_specNorm_pinv_le_exp_mul_sqrt_card_div_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r < Fintype.card k) :
    ∫ ω, specNorm (pinv (X ω)) ∂μ ≤
      Real.exp 1 * √(Fintype.card k : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r) := by
  have hrk' : (Fintype.card r : ℝ) + 1 ≤ Fintype.card k := by exact_mod_cast hrk
  refine (integral_specNorm_pinv_le_of_hasLaw_gaussianMatrix hX hrk).trans ?_
  rw [div_mul_eq_mul_div]
  gcongr
  · linarith
  · linarith

end NLAlib
