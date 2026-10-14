/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import NLAlib.Matrix.Spectral.SpectralRadius
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber

/-!
# Powers of a matrix and the spectral radius

The spectral radius is the limit of `‖Aᵏ‖₂^{1/k}` (Gelfand); the powers of `A` tend to zero
exactly when it is less than one, in which case the Neumann series converges; a similarity
brings the spectral norm within `ε` of it; and the powers stay bounded exactly when it is at
most one and the eigenvalues of modulus one are semisimple.

## Main results

* `NLAlib.tendsto_specNorm_pow_rpow_specRadius`: Gelfand's formula.
* `NLAlib.specNorm_pow_le_conditionNumber_mul`: powers through a similarity.
* `NLAlib.exists_forall_specNorm_pow_le_mul_pow`: growth of the powers.
* `NLAlib.tendsto_pow_zero_iff_specRadius_lt_one`.
* `NLAlib.hasSum_pow_inv_one_sub_of_specRadius_lt_one`: the Neumann series.
* `NLAlib.exists_specNorm_inv_mul_mul_le`: a similarity to within `ε` of the spectral radius.
* `NLAlib.exists_forall_specNorm_pow_le_iff`: power-bounded matrices.
-/

@[expose] public section

open scoped Matrix
open Filter Topology

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Gelfand's formula and growth of the powers -/

/-- **Gelfand's formula**: `‖Aᵏ‖₂^{1/k}` tends to the spectral radius.
[HornJohnson2013, Corollary 5.6.14].
Port of `NLAlib.tendsto_norm_matrix_pow_rpow_spectralRadius`, there over `ℂ`.
Result: gelfand-formula -/
theorem tendsto_specNorm_pow_rpow_specRadius (A : Matrix n n 𝕜) :
    Tendsto (fun k : ℕ => specNorm (A ^ k) ^ (1 / (k : ℝ))) atTop (𝓝 (specRadius A)) := by
  open scoped Matrix.Norms.L2Operator in
  have h := (ENNReal.tendsto_toReal (spectralRadius_complexify_ne_top A)).comp
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius (complexify A))
  refine h.congr fun k => ?_
  rw [Function.comp_apply, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _),
    ← specNorm_eq_norm, ← complexify_pow, specNorm_complexify]

/-- The spectral radius bounds the powers from below: `ρ(A)ᵏ ≤ ‖Aᵏ‖₂`. -/
theorem specRadius_pow_le_specNorm_pow [Nonempty n] (A : Matrix n n 𝕜) (k : ℕ) :
    specRadius A ^ k ≤ specNorm (A ^ k) := by
  rw [← specRadius_pow]
  exact specRadius_le_specNorm _

/-- **Powers through a similarity**: `‖Aᵏ‖₂ ≤ κ(S) ‖S⁻¹ A S‖₂ᵏ` for every invertible `S`. With a
similarity that brings the norm close to the spectral radius this bounds the transient growth of
the powers. [TrefethenBau1997, Lecture 24 context]. -/
theorem specNorm_pow_le_conditionNumber_mul (A : Matrix n n 𝕜) {S : Matrix n n 𝕜}
    (hS : IsUnit S.det) (k : ℕ) :
    specNorm (A ^ k) ≤ conditionNumber S * specNorm (S⁻¹ * A * S) ^ k := by
  have hSu : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).mpr hS
  rw [conditionNumber_of_isUnit hSu]
  obtain ⟨u, rfl⟩ := hSu
  set S : Matrix n n 𝕜 := ↑u with hSdef
  have hpow : A ^ k = S * (S⁻¹ * A * S) ^ k * S⁻¹ := by
    rw [hSdef, ← Matrix.coe_units_inv, Units.conj_pow', mul_assoc, mul_assoc, Units.mul_inv,
      mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  calc specNorm (A ^ k) ≤ specNorm S * specNorm ((S⁻¹ * A * S) ^ k) * specNorm S⁻¹ := by
        rw [hpow]
        exact (specNorm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
    _ ≤ specNorm S * specNorm (S⁻¹ * A * S) ^ k * specNorm S⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (specNorm_pow_le _ k)
          (specNorm_nonneg _)) (specNorm_nonneg _)
    _ = _ := by ring

/-- **Growth of the powers**: for every `ε > 0`, `‖Aᵏ‖₂ ≤ C (ρ(A) + ε)ᵏ` for some `C`.
[HornJohnson2013, Corollary 5.6.13].
Port of `NLAlib.exists_prefix_norm_matrix_pow_le_spectralRadius_add`. -/
theorem exists_forall_specNorm_pow_le_mul_pow (A : Matrix n n 𝕜) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, specNorm (A ^ k) ≤ C * (specRadius A + ε) ^ k := by
  set r := specRadius A + ε with hr
  have hr0 : 0 < r := add_pos_of_nonneg_of_pos (specRadius_nonneg A) hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_specNorm_pow_rpow_specRadius A).eventually
    (gt_mem_nhds (lt_add_of_pos_right _ hε)))
  have hbound (k : ℕ) (hk : N + 1 ≤ k) : specNorm (A ^ k) ≤ r ^ k := by
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg (specNorm_nonneg _) _) (hN k (by lia)).le
      (Nat.cast_nonneg k)
    rwa [← Real.rpow_mul (specNorm_nonneg _), one_div_mul_cancel (Nat.cast_ne_zero.mpr (by lia)),
      Real.rpow_one, Real.rpow_natCast] at hp
  have hsum : 0 ≤ ∑ k ∈ Finset.range (N + 1), specNorm (A ^ k) / r ^ k :=
    Finset.sum_nonneg fun k _ => div_nonneg (specNorm_nonneg _) (pow_nonneg hr0.le k)
  refine ⟨1 + ∑ k ∈ Finset.range (N + 1), specNorm (A ^ k) / r ^ k, by positivity, fun k => ?_⟩
  by_cases hk : k < N + 1
  · rw [← div_le_iff₀ (pow_pos hr0 k)]
    exact (Finset.single_le_sum (f := fun k => specNorm (A ^ k) / r ^ k)
      (fun j _ => div_nonneg (specNorm_nonneg _) (pow_nonneg hr0.le j))
      (Finset.mem_range.mpr hk)).trans (le_add_of_nonneg_left zero_le_one)
  · exact (hbound k (not_lt.mp hk)).trans
      (le_mul_of_one_le_left (pow_nonneg hr0.le k) (le_add_of_nonneg_right hsum))

private theorem exists_forall_specNorm_pow_le_mul_pow_of_specRadius_lt_one {A : Matrix n n 𝕜}
    (hA : specRadius A < 1) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧ ∀ k : ℕ, specNorm (A ^ k) ≤ C * r ^ k := by
  obtain ⟨C, hC, h⟩ := exists_forall_specNorm_pow_le_mul_pow A
    (show 0 < (1 - specRadius A) / 2 by linarith)
  exact ⟨C, _, hC, by linarith [specRadius_nonneg A], by linarith, h⟩
/-! ### Convergent matrices and the Neumann series -/

/-- **The powers of a matrix tend to zero exactly when its spectral radius is less than one.**
[HornJohnson2013, Theorem 5.6.12].
Port of `NLAlib.tendsto_matrix_pow_zero_iff_spectralRadius_lt_one`, there over `ℂ`.
Result: convergent-matrix -/
theorem tendsto_pow_zero_iff_specRadius_lt_one (A : Matrix n n 𝕜) :
    Tendsto (fun k : ℕ => A ^ k) atTop (𝓝 0) ↔ specRadius A < 1 := by
  constructor
  · intro h
    cases isEmpty_or_nonempty n with
    | inl hn => rw [specRadius_of_isEmpty]; exact zero_lt_one
    | inr hn =>
      have h0 := (continuous_specNorm.tendsto (0 : Matrix n n 𝕜)).comp h
      rw [specNorm_zero] at h0
      obtain ⟨N, hN⟩ := eventually_atTop.mp (h0.eventually (gt_mem_nhds zero_lt_one))
      by_contra hρ
      exact absurd ((one_le_pow₀ (not_lt.mp hρ)).trans (specRadius_pow_le_specNorm_pow A N))
        (not_le.mpr (hN N le_rfl))
  · intro h
    obtain ⟨C, r, -, hr0, hr1, hC⟩ := exists_forall_specNorm_pow_le_mul_pow_of_specRadius_lt_one h
    have hlim : Tendsto (fun k : ℕ => C * r ^ k) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).const_mul C
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    exact squeeze_zero_norm (fun k => (norm_apply_le_specNorm (A ^ k) i j).trans (hC k)) hlim

/-- **The Neumann series** converges to `(1 - A)⁻¹` when the spectral radius is less than one.
[HornJohnson2013, Corollary 5.6.16].
Port of `NLAlib.hasSum_matrix_pow_inv_of_spectralRadius_lt_one`. -/
theorem hasSum_pow_inv_one_sub_of_specRadius_lt_one {A : Matrix n n 𝕜}
    (hA : specRadius A < 1) : HasSum (fun k : ℕ => A ^ k) (1 - A)⁻¹ := by
  obtain ⟨C, r, -, hr0, hr1, hC⟩ := exists_forall_specNorm_pow_le_mul_pow_of_specRadius_lt_one hA
  have hs : Summable fun k : ℕ => A ^ k := by
    open scoped Matrix.Norms.L2Operator in
    exact Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0.le hr1).mul_left C)
      fun k => (specNorm_eq_norm (A ^ k)).symm.trans_le (hC k)
  have hleft : Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, A ^ k) * (1 - A))
      atTop (𝓝 ((∑' k : ℕ, A ^ k) * (1 - A))) :=
    hs.hasSum.tendsto_sum_nat.mul_const (1 - A)
  have hright : Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, A ^ k) * (1 - A))
      atTop (𝓝 1) := by
    simp only [geom_sum_mul_neg]
    simpa only [sub_zero] using
      tendsto_const_nhds.sub ((tendsto_pow_zero_iff_specRadius_lt_one A).mpr hA)
  rw [Matrix.inv_eq_left_inv (tendsto_nhds_unique hleft hright)]
  exact hs.hasSum

/-- `1 - A` is invertible when the spectral radius of `A` is less than one.
Port of `NLAlib.isUnit_one_sub_of_matrix_spectralRadius_lt_one`. -/
theorem isUnit_det_one_sub_of_specRadius_lt_one {A : Matrix n n 𝕜} (hA : specRadius A < 1) :
    IsUnit (1 - A).det := by
  by_contra h
  have hmem : (1 : 𝕜) ∈ spectrum 𝕜 A := by
    rwa [spectrum.mem_iff, map_one, Matrix.isUnit_iff_isUnit_det]
  have h1 := norm_le_specRadius_of_mem_spectrum hmem
  rw [norm_one] at h1
  exact absurd hA (not_lt.mpr h1)
/-! ### Similarity to within `ε` -/

omit [DecidableEq n] in
private theorem specNorm_le_card_mul_of_forall_norm_apply_le {A : Matrix n n 𝕜} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i j, ‖A i j‖ ≤ c) : specNorm A ≤ Fintype.card n * c := by
  refine (specNorm_le_frobNorm A).trans ?_
  refine (pow_le_pow_iff_left₀ (frobNorm_nonneg A) (by positivity) two_ne_zero).mp ?_
  rw [frobNorm_sq_eq_sum]
  calc ∑ i, ∑ j, ‖A i j‖ ^ 2 ≤ ∑ _i : n, ∑ _j : n, c ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (Fintype.card n * c) ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
        ring

/-- **A similarity brings the spectral norm within `ε` of the spectral radius.**
[HornJohnson2013, Lemma 5.6.10]. -/
theorem exists_specNorm_inv_mul_mul_le (A : Matrix n n ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Matrix n n ℂ, IsUnit S.det ∧ specNorm (S⁻¹ * A * S) ≤ specRadius A + ε := by
  let _ : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  have hcard : (0 : ℝ) < Fintype.card n + 1 := by positivity
  obtain ⟨S, hS, hT, hsmall⟩ :=
    exists_isUpperTriangular_inv_mul_mul_norm_apply_lt A (div_pos hε hcard)
  refine ⟨S, hS, ?_⟩
  set T := S⁻¹ * A * S with hTdef
  have hdiag : specNorm (Matrix.diagonal fun i => T i i) ≤ specRadius A := by
    refine specNorm_diagonal_le (specRadius_nonneg A) fun i => ?_
    rw [← specRadius_inv_mul_mul A hS]
    exact norm_le_specRadius_of_mem_spectrum
      (hT.isEigenvalueListing_diag.spectrum_eq_range ▸ Set.mem_range_self i)
  have hoff : specNorm (T - Matrix.diagonal fun i => T i i) ≤ ε := by
    refine (specNorm_le_card_mul_of_forall_norm_apply_le (div_pos hε hcard).le
      fun i j => ?_).trans ?_
    · by_cases hij : i = j
      · subst hij
        rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, sub_self, norm_zero]
        exact (div_pos hε hcard).le
      · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, sub_zero]
        exact (hsmall i j hij).le
    · rw [mul_div_assoc', div_le_iff₀ hcard]
      nlinarith [hε.le]
  calc specNorm T = specNorm ((Matrix.diagonal fun i => T i i) +
        (T - Matrix.diagonal fun i => T i i)) := by rw [add_sub_cancel]
    _ ≤ specRadius A + ε := (specNorm_add_le _ _).trans (add_le_add hdiag hoff)

/-! ### Power-bounded matrices -/

/-- In a generalized eigenspace of an eigenvalue of modulus less than one every orbit is
bounded. -/
private theorem exists_forall_norm_pow_apply_le_of_norm_lt_one {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Module.End ℂ E) {μ : ℂ} (hμ : ‖μ‖ < 1)
    (m : ℕ) : ∀ x : E, ((f - μ • 1) ^ m) x = 0 → ∃ C : ℝ, ∀ k : ℕ, ‖(f ^ k) x‖ ≤ C := by
  induction m with
  | zero =>
    intro x hx
    rw [pow_zero, Module.End.one_apply] at hx
    exact ⟨0, fun k => by rw [hx, map_zero, norm_zero]⟩
  | succ m ih =>
    intro x hx
    obtain ⟨D, hD⟩ := ih ((f - μ • 1) x) (by rwa [pow_succ, Module.End.mul_apply] at hx)
    have hstep (k : ℕ) : (f ^ (k + 1)) x = μ • (f ^ k) x + (f ^ k) ((f - μ • 1) x) := by
      rw [pow_succ, Module.End.mul_apply, LinearMap.sub_apply, map_sub, LinearMap.smul_apply,
        Module.End.one_apply, map_smul]
      abel
    have hB : D ≤ (1 - ‖μ‖) * max ‖x‖ (D / (1 - ‖μ‖)) := by
      have h := le_max_right ‖x‖ (D / (1 - ‖μ‖))
      rw [div_le_iff₀ (by linarith)] at h
      linarith
    refine ⟨max ‖x‖ (D / (1 - ‖μ‖)), fun k => ?_⟩
    induction k with
    | zero => rw [pow_zero, Module.End.one_apply]; exact le_max_left _ _
    | succ k ihk =>
      rw [hstep]
      have h1 := norm_add_le (μ • (f ^ k) x) ((f ^ k) ((f - μ • 1) x))
      rw [norm_smul] at h1
      have h2 := mul_le_mul_of_nonneg_left ihk (norm_nonneg μ)
      linarith [hD k]

/-- A bounded orbit excludes a Jordan chain of length two at an eigenvalue of modulus one. -/
private theorem eq_zero_of_forall_norm_pow_apply_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : Module.End ℂ E) {μ : ℂ} (hμ : ‖μ‖ = 1) {x y : E}
    (hx : f x = μ • x) (hy : f y = μ • y + x) (hb : ∃ C : ℝ, ∀ k : ℕ, ‖(f ^ k) y‖ ≤ C) :
    x = 0 := by
  have hμne : μ ≠ 0 := fun h => by simp [h] at hμ
  have hpow (k : ℕ) : (f ^ k) y = μ ^ k • y + ((k : ℂ) * μ ^ k * μ⁻¹) • x := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, map_smul, hy, hx, smul_add,
        smul_smul, smul_smul, add_assoc, ← add_smul, pow_succ]
      congr 2
      push_cast
      field_simp
      ring
  obtain ⟨C, hC⟩ := hb
  by_contra hne
  have hpos := norm_pos_iff.mpr hne
  obtain ⟨k, hk⟩ := exists_nat_gt ((C + ‖y‖) / ‖x‖)
  rw [div_lt_iff₀ hpos] at hk
  have h1 : ‖((k : ℂ) * μ ^ k * μ⁻¹) • x‖ = k * ‖x‖ := by
    rw [norm_smul, norm_mul, norm_mul, norm_inv, norm_pow, hμ, one_pow, inv_one, mul_one,
      mul_one, Complex.norm_natCast]
  have h2 : ‖((k : ℂ) * μ ^ k * μ⁻¹) • x‖ ≤ ‖(f ^ k) y‖ + ‖μ ^ k • y‖ := by
    rw [hpow k]
    simpa only [add_sub_cancel_left] using
      norm_sub_le (μ ^ k • y + ((k : ℂ) * μ ^ k * μ⁻¹) • x) (μ ^ k • y)
  rw [h1, norm_smul, norm_pow, hμ, one_pow, one_mul] at h2
  linarith [hC k]

/-- If every orbit is bounded, the generalized eigenspaces at eigenvalues of modulus one are
eigenspaces. -/
private theorem maxGenEigenspace_eq_eigenspace_of_forall_norm_pow_apply_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Module.End ℂ E)
    (hb : ∀ x : E, ∃ C : ℝ, ∀ k : ℕ, ‖(f ^ k) x‖ ≤ C) {μ : ℂ} (hμ : ‖μ‖ = 1) :
    f.maxGenEigenspace μ = f.eigenspace μ := by
  have hstep (z : E) (hz : (f - μ • 1) ((f - μ • 1) z) = 0) : (f - μ • 1) z = 0 := by
    refine eq_zero_of_forall_norm_pow_apply_le f hμ (y := z) ?_ ?_ (hb z)
    · exact sub_eq_zero.mp hz
    · rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      abel
  have hpower (k : ℕ) : ∀ z : E, ((f - μ • 1) ^ k) z = 0 → (f - μ • 1) z = 0 := by
    induction k with
    | zero =>
      intro z hz
      rw [pow_zero, Module.End.one_apply] at hz
      rw [hz, map_zero]
    | succ k ih =>
      intro z hz
      exact hstep z (ih _ (by rwa [pow_succ, Module.End.mul_apply] at hz))
  refine le_antisymm (fun z hz => ?_) Module.End.eigenspace_le_maxGenEigenspace
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f μ z).mp hz
  have h := hpower k z hk
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  exact Module.End.mem_eigenspace_iff.mpr h

omit [DecidableEq n] in
private theorem norm_toLin'_pow_apply_le [DecidableEq n] (M : Matrix n n ℂ) (k : ℕ)
    (x : n → ℂ) : ‖(Matrix.toLin' M ^ k) x‖ ≤ specNorm (M ^ k) * ‖WithLp.toLp 2 x‖ := by
  rw [← Matrix.toLin'_pow, Matrix.toLin'_apply]
  refine (norm_toLp_mulVec_le (M ^ k) x).trans' ?_
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  exact PiLp.norm_apply_le (WithLp.toLp 2 (M ^ k *ᵥ x)) i

/-- With spectral radius at most one and semisimple eigenvalues of modulus one, every orbit is
bounded. -/
private theorem exists_forall_norm_pow_apply_le_of_specRadius_le_one {A : Matrix n n 𝕜}
    (hρ : specRadius A ≤ 1)
    (hsemi : ∀ μ : ℂ, ‖μ‖ = 1 →
      Module.End.maxGenEigenspace (Matrix.toLin' (complexify A)) μ =
        Module.End.eigenspace (Matrix.toLin' (complexify A)) μ) (x : n → ℂ) :
    ∃ C : ℝ, ∀ k : ℕ, ‖(Matrix.toLin' (complexify A) ^ k) x‖ ≤ C := by
  set f : Module.End ℂ (n → ℂ) := Matrix.toLin' (complexify A) with hf
  let P : Submodule ℂ (n → ℂ) :=
    { carrier := {x | ∃ C : ℝ, ∀ k : ℕ, ‖(f ^ k) x‖ ≤ C}
      zero_mem' := ⟨0, fun k => by rw [map_zero, norm_zero]⟩
      add_mem' := by
        rintro x y ⟨C, hC⟩ ⟨D, hD⟩
        exact ⟨C + D, fun k => by
          rw [map_add]
          exact (norm_add_le _ _).trans (add_le_add (hC k) (hD k))⟩
      smul_mem' := by
        rintro a x ⟨C, hC⟩
        exact ⟨‖a‖ * C, fun k => by
          rw [map_smul, norm_smul]
          exact mul_le_mul_of_nonneg_left (hC k) (norm_nonneg a)⟩ }
  have hprimary (μ : ℂ) : f.maxGenEigenspace μ ≤ P := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]
      exact P.zero_mem
    obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace f μ x).mp hx
    have heigen : f.HasEigenvalue μ :=
      Module.End.hasEigenvalue_of_hasGenEigenvalue (k := m)
        (Module.End.HasUnifEigenvector.hasUnifEigenvalue
          (x := x) ⟨Module.End.mem_genEigenspace_nat.mpr hm, hx0⟩)
    have hμ : ‖μ‖ ≤ 1 := by
      rw [Module.End.hasEigenvalue_iff_mem_spectrum, hf, Matrix.spectrum_toLin'] at heigen
      exact (norm_le_specRadius_of_mem_spectrum_complexify heigen).trans hρ
    rcases hμ.lt_or_eq with hlt | heq
    · exact exists_forall_norm_pow_apply_le_of_norm_lt_one f hlt m x hm
    · have hx' : x ∈ f.eigenspace μ := by rw [← hsemi μ heq]; exact hx
      have hxe : f.HasEigenvector μ x := ⟨hx', hx0⟩
      exact ⟨‖x‖, fun k => by rw [hxe.pow_apply, norm_smul, norm_pow, heq, one_pow, one_mul]⟩
  have htop : (⊤ : Submodule ℂ (n → ℂ)) ≤ P := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top f]
    exact iSup_le hprimary
  exact htop Submodule.mem_top

/-- **Power-bounded matrices.** The powers of `A` are bounded exactly when the spectral radius is
at most one and every eigenvalue of modulus one is semisimple.
[HornJohnson2013, Theorem 3.2.5.2].
Port of `NLAlib.exists_bound_norm_matrix_pow_iff`, there over `ℂ`. -/
theorem exists_forall_specNorm_pow_le_iff (A : Matrix n n 𝕜) :
    (∃ C : ℝ, ∀ k : ℕ, specNorm (A ^ k) ≤ C) ↔
      specRadius A ≤ 1 ∧ ∀ μ : ℂ, ‖μ‖ = 1 →
        Module.End.maxGenEigenspace (Matrix.toLin' (complexify A)) μ =
          Module.End.eigenspace (Matrix.toLin' (complexify A)) μ := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨?_, fun μ hμ => maxGenEigenspace_eq_eigenspace_of_forall_norm_pow_apply_le _
      (fun x => ⟨C * ‖WithLp.toLp 2 x‖, fun k => ?_⟩) hμ⟩
    · cases isEmpty_or_nonempty n with
      | inl hn => rw [specRadius_of_isEmpty]; exact zero_le_one
      | inr hn =>
        by_contra hρ
        obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.mp hρ)
        exact absurd ((specRadius_pow_le_specNorm_pow A k).trans (hC k)) (not_le.mpr hk)
    · refine (norm_toLin'_pow_apply_le _ k x).trans
        (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      rw [← complexify_pow, specNorm_complexify]
      exact hC k
  · rintro ⟨hρ, hsemi⟩
    choose C hC using fun j : n => exists_forall_norm_pow_apply_le_of_specRadius_le_one hρ hsemi
      (Pi.single j (1 : ℂ))
    have hC0 : ∀ j, 0 ≤ C j := fun j => (norm_nonneg _).trans (hC j 0)
    refine ⟨Fintype.card n * ∑ j, C j, fun k => ?_⟩
    rw [← specNorm_complexify, complexify_pow]
    refine specNorm_le_card_mul_of_forall_norm_apply_le (Finset.sum_nonneg fun j _ => hC0 j)
      fun i j => ?_
    have hij : (complexify A ^ k) i j =
        ((Matrix.toLin' (complexify A) ^ k) (Pi.single j (1 : ℂ))) i := by
      rw [← Matrix.toLin'_pow, Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply]
    rw [hij]
    exact (norm_le_pi_norm _ i).trans ((hC j k).trans
      (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ j)))
end NLAlib
