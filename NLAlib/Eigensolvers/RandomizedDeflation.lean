/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Deflation
public import NLAlib.RandomMatrix.Gaussian.Complex.LeastSingularValue

/-!
# Randomized deflation with a complex Gaussian test matrix

With a standard complex Gaussian sample, the deterministic bounds of
`NLAlib.FloatMachine.IsArithAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le` and
`FloatMachine.IsArithAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le`
hold with $m$ replaced by its high-probability bound ([Shah2024, Theorem 3.3]).

## Main results

* [The Gaussian tail of deflation](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsArithAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le_of_hasLaw_complexGaussianMatrix).
* [The Gaussian tail of deflation, sharp tails](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsArithAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le_exp_neg_sq_add_of_hasLaw_complexGaussianMatrix).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- At $u = 0$ the machine contract holds with any matrix-multiplication constant. -/
private lemma FloatMachine.IsArithAccurate.of_u_eq_zero {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {τ Ω : ℝ} {μM : ℕ → ℝ} (hM : M.IsArithAccurate dec 0 τ Ω μM)
    (μM' : ℕ → ℝ) : M.IsArithAccurate dec 0 τ Ω μM' :=
  { hM with
    isMatMulErr :=
      { specNorm_mul_sub_le := fun A B h => by
          have := hM.isMatMulErr.specNorm_mul_sub_le A B h
          rw [mul_zero, zero_mul] at this ⊢
          exact this
        isHermitian_of_map_eq_conjTranspose :=
          hM.isMatMulErr.isHermitian_of_map_eq_conjTranspose } }

/-- With range $\Omega \ge 1$ the contract forces $u \ge 0$, and $\mu_{\mathrm{MM}}(n) \ge 0$ when
$u > 0$ and $n \ge 1$ (the stored identity times itself). -/
private lemma FloatMachine.IsArithAccurate.nonneg_of_one_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω : ℝ} {μM : ℕ → ℝ}
    (hM : M.IsArithAccurate dec u τ Ω μM)
    {n : ℕ} (hn : 0 < n) (hΩ : 1 ≤ Ω) : 0 ≤ u ∧ (0 < u → 0 ≤ μM n) := by
  have hmax : (0 : ℝ) < max 1 τ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hu : 0 ≤ u := by
    have h := hM.ofNat 1
    simp only [IsRoundingOf, Nat.cast_one, abs_one] at h
    have h0 := (abs_nonneg _).trans (h hΩ)
    by_contra hneg
    push Not at hneg
    linarith [mul_neg_of_neg_of_pos hneg hmax]
  refine ⟨hu, fun hpos => ?_⟩
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let I' : Matrix (Fin n) (Fin n) (F × F) :=
    Matrix.of fun i j => (if i = j then M.one else M.zero, M.zero)
  have hI : I'.map (decodeComplex dec) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [I', decodeComplex, hM.dec_one, hM.dec_zero]
      rfl
    · simp [I', decodeComplex, hM.dec_zero, hij, Matrix.one_apply_ne hij]
      rfl
  have h := hM.isMatMulErr.specNorm_mul_sub_le I' I' (by rw [hI, specNorm_one, mul_one]; exact hΩ)
  rw [hI, specNorm_one, mul_one, mul_one, max_self, max_self] at h
  by_contra hneg
  push Not at hneg
  linarith [specNorm_nonneg (1 - (M.mm I' I').map (decodeComplex dec)),
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg hpos) hmax]

/-- The event that the last singular value of `Vᴴ G₁` is at most `x` has probability at most
$\min(r^2, e\,r)x^2$. -/
private lemma measureReal_rank_deflate_le_min {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω'} {n r : ℕ} (hr : r ≤ n) {V : Matrix (Fin n) (Fin r) ℂ}
    (hV : HasOrthonormalCols V) {G : Ω' → Matrix (Fin n) (Fin n) ℂ}
    (hG : HasLaw G (complexGaussianMatrix (Fin n) (Fin n)) μ) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | r ≠ 0 ∧
      singularValues (Vᴴ * (G ω).submatrix id (Fin.castLE hr)) (r - 1) ≤ x} ≤
      min ((r : ℝ) ^ 2) (Real.exp 1 * r) * x ^ 2 := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  rcases eq_or_ne r 0 with h0 | h0
  · subst h0
    simp
  have hL2 := hasLaw_submatrix_of_hasLaw_complexGaussianMatrix
    (hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix hG hV)
    (f := id) Function.injective_id (e := Fin.castLE hr) (Fin.castLE_injective hr)
  have hfun : (fun ω => Vᴴ * (G ω).submatrix id (Fin.castLE hr)) =
      (fun ω => (Vᴴ * G ω).submatrix id (Fin.castLE hr)) := by
    funext ω
    ext i j
    simp [Matrix.mul_apply]
  rw [← hfun] at hL2
  have hk : r - 1 + 1 = Fintype.card (Fin r) := by rw [Fintype.card_fin]; omega
  have h1 := measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix hL2 hk hx
  have h2 := measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix hL2 hk hx
  rw [Fintype.card_fin] at h1 h2
  rw [min_mul_of_nonneg _ _ (by positivity)]
  exact (measureReal_mono fun ω hω => hω.2).trans (le_min h1 h2)

/-- On the event $\sigma_{r-1}(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1) > x$, $r \ne 0$:
$u \ge 0$, the contract holds with a product constant $\mu' \ge 0$ at $n$ and
$\mu'(n)u = \mu_{\mathrm{MM}}(n)u$, $\mathbf{V}^{\mathsf{H}}\mathbf{G}_1$ is invertible with
inverse of norm at most $1/x$, and $x \le \|\mathbf{G}\|_2$. -/
private lemma FloatMachine.IsArithAccurate.isUnit_and_specNorm_inv_le_of_lt_singularValues
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω x : ℝ} {μM : ℕ → ℝ}
    (hM : M.IsArithAccurate dec u τ Ω μM) {n r : ℕ} (hr : r ≤ n) (h0 : r ≠ 0)
    {V : Matrix (Fin n) (Fin r) ℂ} (hV : HasOrthonormalCols V) (hx : 0 < x) (hΩ1 : 1 ≤ Ω)
    {Gm : Matrix (Fin n) (Fin n) ℂ}
    (hσ : x < singularValues (Vᴴ * Gm.submatrix id (Fin.castLE hr)) (r - 1)) :
    0 ≤ u ∧ (∃ μ' : ℕ → ℝ, M.IsArithAccurate dec u τ Ω μ' ∧ 0 ≤ μ' n ∧ μ' n * u = μM n * u) ∧
      IsUnit (Vᴴ * Gm.submatrix id (Fin.castLE hr)) ∧
      specNorm (Vᴴ * Gm.submatrix id (Fin.castLE hr))⁻¹ ≤ 1 / x ∧ x ≤ specNorm Gm := by
  obtain ⟨hu0, hμpos⟩ := hM.nonneg_of_one_le (by omega : 0 < n) hΩ1
  have hlow : ∀ z : Fin r → ℂ, x * ‖WithLp.toLp 2 z‖ ≤
      ‖WithLp.toLp 2 ((Vᴴ * Gm.submatrix id (Fin.castLE hr)) *ᵥ z)‖ := fun z =>
    (mul_le_mul_of_nonneg_right hσ.le (norm_nonneg _)).trans
      (singularValues_last_mul_norm_le _ (k := r - 1) (by rw [Fintype.card_fin]; omega) z)
  obtain ⟨hGu, hinv⟩ := isUnit_and_specNorm_inv_le_of_forall_mul_norm_le hx hlow
  have hMG : specNorm (Vᴴ * Gm.submatrix id (Fin.castLE hr)) ≤ specNorm Gm :=
    (hV.specNorm_conjTranspose_mul_le _).trans
      (specNorm_submatrix_le Gm Function.injective_id (Fin.castLE_injective hr))
  refine ⟨hu0, ?_, hGu, hinv, hσ.le.trans ((singularValues_le_specNorm _ _).trans hMG)⟩
  rcases hu0.eq_or_lt with h | h
  · subst h
    exact ⟨fun _ => 0, hM.of_u_eq_zero _, le_rfl, by simp⟩
  · exact ⟨μM, hM, hμpos h, rfl⟩

/-- The deterministic step of randomized deflation: on the event
$\|\mathbf{G}\|_2 < \sqrt2(2\sqrt n + t)$, $\sigma_{r-1}(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1) > x$,
some unitary $\mathbf{W}$ has
$\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le 6\bar m\beta$. -/
private lemma FloatMachine.IsArithAccurate.exists_specNorm_mul_sub_deflate_le_of_good
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β t x : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsArithAccurate dec u τ Ω μM) (hqr : IsQRErr (decodeComplex dec) u τ Ω μQ M.qr)
    (hnormal : IsNormalSampler (decodeComplex dec) u cN τ Ω M.normal) {n r : ℕ} (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β) (hβ₁ : β ≤ 1) (ht : 0 ≤ t) (hx : 0 < x)
    (hmβ : (specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) / x * β ≤ 1 / 5)
    (hu : (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β) (hτ : τ ≤ specNorm S * x)
    (hτN : τ * √(n : ℝ) ≤ x)
    (hΩ : 2 * (specNorm S + 1) * (√2 * (2 * √(n : ℝ) + t)) ≤ Ω)
    {Gm : Matrix (Fin n) (Fin n) ℂ} (hGB : specNorm Gm < √2 * (2 * √(n : ℝ) + t))
    (hσ : r ≠ 0 → x < singularValues (Vᴴ * Gm.submatrix id (Fin.castLE hr)) (r - 1)) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' Gm)) ≤
        6 * ((specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) / x) * β := by
  have hβ0 : 0 ≤ β := (specNorm_nonneg _).trans hβ
  have hσ0 : 0 ≤ specNorm S := specNorm_nonneg S
  have hB0 : 0 ≤ √2 * (2 * √(n : ℝ) + t) := by positivity
  rcases eq_or_ne r 0 with h0 | h0
  · subst h0
    refine ⟨1, hasOrthonormalCols_one, ?_⟩
    rw [Subsingleton.elim (U * 1 - _) 0, specNorm_zero]
    have := specNorm_nonneg S⁻¹
    positivity
  have hΩ1 : 1 ≤ Ω := by
    have hn1 : (1 : ℝ) ≤ √(n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 0 < n))
    have hs2 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
    nlinarith
  obtain ⟨hu0, ⟨μ', hM', hμ', hμu⟩, hGu, hinv, hxG⟩ :=
    hM.isUnit_and_specNorm_inv_le_of_lt_singularValues hr h0 hV hx hΩ1 (hσ h0)
  have hmval : (specNorm S + β + 1) * specNorm S⁻¹ * specNorm Gm *
      specNorm (Vᴴ * Gm.submatrix id (Fin.castLE hr))⁻¹ ≤
      (specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) / x := by
    have h1 : specNorm S + β + 1 ≤ specNorm S + 2 := by linarith
    rw [div_eq_mul_one_div]
    gcongr
  have h2 : 2 * (specNorm S + β) ≤ 2 * (specNorm S + 1) := by linarith
  have hΩ' : 2 * (specNorm S + β) * specNorm Gm ≤ Ω := by
    nlinarith [mul_le_mul h2 hGB.le (specNorm_nonneg _) (by positivity)]
  have hΩG : specNorm Gm ≤ Ω := by nlinarith [mul_nonneg hσ0 hB0, hGB.le]
  obtain ⟨W, hW, hWb⟩ := hM'.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le hqr hnormal
    hμ' hu0 hr hU hV hS hA hβ hGu rfl (mul_le_mul_of_nonneg_right hmval hβ0 |>.trans hmβ)
    (by linarith)
    (hτ.trans (mul_le_mul_of_nonneg_left hxG hσ0)) (hτN.trans hxG)
    hΩ' hΩG
  exact ⟨W, hW, hWb.trans (by gcongr)⟩

/-- The deterministic step of randomized deflation with the roundings charged at $\beta/16$: on
the event $\|\mathbf{G}\|_2 < 2\sqrt2\sqrt n + t$,
$\sigma_{r-1}(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1) > x$, some unitary $\mathbf{W}$ has
$\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le
\tfrac32\bar m\beta$. -/
private lemma FloatMachine.IsArithAccurate.exists_specNorm_mul_sub_deflate_le_of_good_of_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β t x : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsArithAccurate dec u τ Ω μM) (hqr : IsQRErr (decodeComplex dec) u τ Ω μQ M.qr)
    (hnormal : IsNormalSampler (decodeComplex dec) u cN τ Ω M.normal) {n r : ℕ} (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β) (hβ₁ : β ≤ 1) (ht : 0 ≤ t) (hx : 0 < x)
    (hmβ : (1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x * β ≤
      1 / 64)
    (hu : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β) (hτ : τ ≤ specNorm S * x)
    (hτN : τ * √(n : ℝ) ≤ x)
    (hΩ : 2 * (specNorm S + 1) * (2 * √2 * √(n : ℝ) + t) ≤ Ω)
    {Gm : Matrix (Fin n) (Fin n) ℂ} (hGB : specNorm Gm < 2 * √2 * √(n : ℝ) + t)
    (hσ : r ≠ 0 → x < singularValues (Vᴴ * Gm.submatrix id (Fin.castLE hr)) (r - 1)) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' Gm)) ≤
        3 / 2 * ((1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x) *
          β := by
  have hβ0 : 0 ≤ β := (specNorm_nonneg _).trans hβ
  have hσ0 : 0 ≤ specNorm S := specNorm_nonneg S
  have hB0 : 0 ≤ 2 * √2 * √(n : ℝ) + t := by positivity
  rcases eq_or_ne r 0 with h0 | h0
  · subst h0
    refine ⟨1, hasOrthonormalCols_one, ?_⟩
    rw [Subsingleton.elim (U * 1 - _) 0, specNorm_zero]
    have := specNorm_nonneg S⁻¹
    positivity
  have hΩ1 : 1 ≤ Ω := by
    have hn1 : (1 : ℝ) ≤ √(n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 0 < n))
    have hs2 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
    nlinarith [mul_le_mul hs2 hn1 zero_le_one (by positivity)]
  obtain ⟨hu0, ⟨μ', hM', hμ', hμu⟩, hGu, hinv, hxG⟩ :=
    hM.isUnit_and_specNorm_inv_le_of_lt_singularValues hr h0 hV hx hΩ1 (hσ h0)
  have hmval : (1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * specNorm Gm *
      specNorm (Vᴴ * Gm.submatrix id (Fin.castLE hr))⁻¹ ≤
      (1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x := by
    rw [mul_assoc _ (specNorm Gm), mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by linarith) (specNorm_nonneg _))
    rw [div_eq_mul_one_div]
    gcongr
  have h2 : 2 * (specNorm S + β) ≤ 2 * (specNorm S + 1) := by linarith
  have hΩ' : 2 * (specNorm S + β) * specNorm Gm ≤ Ω := by
    nlinarith [mul_le_mul h2 hGB.le (specNorm_nonneg _) (by positivity)]
  have hΩG : specNorm Gm ≤ Ω := by nlinarith [mul_nonneg hσ0 hB0, hGB.le]
  obtain ⟨W, hW, hWb⟩ := hM'.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le hqr
    hnormal hμ' hu0 hr hU hV hS hA hβ hGu rfl (mul_le_mul_of_nonneg_right hmval hβ0 |>.trans hmβ)
    (by linarith) (hτ.trans (mul_le_mul_of_nonneg_left hxG hσ0)) (hτN.trans hxG)
    hΩ' hΩG
  exact ⟨W, hW, hWb.trans (by gcongr)⟩

-- The declaration name exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Randomized deflation** (Theorem 3.3): under the arithmetic contract
`NLAlib.FloatMachine.IsArithAccurate` $u$ $\tau$ $\Omega$ with product constant
$\mu_{\mathrm{MM}}$, with the QR routine meeting `NLAlib.IsQRErr` with constant
$\mu_{\mathrm{QR}}$ and the normal sampler meeting `NLAlib.IsNormalSampler` with constant
$c_{\mathrm N}$ (at $u$, $\tau$, $\Omega$, through the decoding), let $r \le n$,
$\mathbf{U}, \mathbf{V} \in \mathbb{C}^{n \times r}$ have orthonormal columns, $\mathbf{S}$ be
invertible, $\mathbf{A} =
\mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$ and the stored $\widetilde{\mathbf{A}}$ decode
within $\beta \le 1$ of $\mathbf{A}$, and let $\mathbf{G}$ be a standard complex Gaussian $n \times
n$ matrix. For $t \ge 0$ and $x > 0$ put
$$\bar m = (\|\mathbf{S}\|_2 + 2)\|\mathbf{S}^{-1}\|_2\,\frac{\sqrt2\,(2\sqrt n + t)}{x} \,.$$
If $\bar m\beta \le 1/5$,
$(4\mu_{\mathrm{QR}}(n) + 4\sqrt n\,c_{\mathrm N} + 2\mu_{\mathrm{MM}}(n))u
\le \beta$, $\tau \le \|\mathbf{S}\|_2 x$, $\sqrt n\,\tau \le x$ and $2(\|\mathbf{S}\|_2 +
1)\sqrt2(2\sqrt n + t) \le \Omega$, then
$$\mathbb{P}\bigl[\text{no unitary } \mathbf{W} \text{ has }
\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le 6\bar m\beta\bigr]
\le 2e^{-t^2/2} + r^2x^2 \,,$$
$\mathsf{deflate}$ the algorithm `NLAlib.deflate` with sample $\mathbf{G}$. [Shah2024, Theorem 3.3],
there with $(2\sqrt2 + t)\sqrt n$, failure $2e^{-nt^2} + (r/2)x^2$ and the requirement on $\beta$
written out; the constants differ through Lemmas 3.1 and 3.2.
Result: deflate-accuracy -/
theorem
    FloatMachine.IsArithAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le_of_hasLaw_complexGaussianMatrix
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β t x : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsArithAccurate dec u τ Ω μM) (hqr : IsQRErr (decodeComplex dec) u τ Ω μQ M.qr)
    (hnormal : IsNormalSampler (decodeComplex dec) u cN τ Ω M.normal) {n r : ℕ} (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β) (hβ₁ : β ≤ 1) (ht : 0 ≤ t) (hx : 0 < x)
    (hmβ : (specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) / x * β ≤ 1 / 5)
    (hu : (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β) (hτ : τ ≤ specNorm S * x)
    (hτN : τ * √(n : ℝ) ≤ x)
    (hΩ : 2 * (specNorm S + 1) * (√2 * (2 * √(n : ℝ) + t)) ≤ Ω)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {G : Ω' → Matrix (Fin n) (Fin n) ℂ}
    (hG : HasLaw G (complexGaussianMatrix (Fin n) (Fin n)) μ) :
    μ.real {ω | ¬ ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' (G ω))) ≤
        6 * ((specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) / x) * β} ≤
      2 * Real.exp (-t ^ 2 / 2) + r ^ 2 * x ^ 2 := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hE1 : μ.real {ω | √2 * (2 * √(n : ℝ) + t) ≤ specNorm (G ω)} ≤ 2 * Real.exp (-t ^ 2 / 2) := by
    refine le_trans (measureReal_mono fun ω hω => ?_)
      (measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix hG ht)
    simp only [Set.mem_ofPred_eq, Fintype.card_fin] at hω ⊢
    linarith
  have hsub : {ω | ¬ ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' (G ω))) ≤
        6 * ((specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) / x) * β} ⊆
      {ω | √2 * (2 * √(n : ℝ) + t) ≤ specNorm (G ω)} ∪
        {ω | r ≠ 0 ∧ singularValues (Vᴴ * (G ω).submatrix id (Fin.castLE hr)) (r - 1) ≤ x} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_and] at hcon hω
    exact hω (hM.exists_specNorm_mul_sub_deflate_le_of_good hqr hnormal hr hU hV hS hA hβ hβ₁ ht hx
      hmβ hu hτ hτN hΩ hcon.1 hcon.2)
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add hE1 ((measureReal_rank_deflate_le_min hr hV hG hx.le).trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg x)))))

-- The declaration name and a docstring line exceed 100 characters.
set_option linter.style.longLine false in
/-- **Randomized deflation with sharp tails** (Theorem 3.3): under the arithmetic contract
`NLAlib.FloatMachine.IsArithAccurate` $u$ $\tau$ $\Omega$ with product constant
$\mu_{\mathrm{MM}}$, with the QR routine meeting `NLAlib.IsQRErr` with constant
$\mu_{\mathrm{QR}}$ and the normal sampler meeting `NLAlib.IsNormalSampler` with constant
$c_{\mathrm N}$ (at $u$, $\tau$, $\Omega$, through the decoding), let $r \le n$,
$\mathbf{U}, \mathbf{V} \in \mathbb{C}^{n \times r}$ have orthonormal columns, $\mathbf{S}$ be
invertible, $\mathbf{A} =
\mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$ and the stored $\widetilde{\mathbf{A}}$ decode
within $\beta \le 1$ of $\mathbf{A}$, and let $\mathbf{G}$ be a standard complex Gaussian $n \times
n$ matrix. For $t \ge 0$ and $x > 0$ put
$$\bar m = \Bigl(1 + 2\beta + \frac{\|\mathbf{S}\|_2}{8}\Bigr)\|\mathbf{S}^{-1}\|_2\,
\frac{2\sqrt2\sqrt n + t}{x} \,.$$
If $\bar m\beta \le 1/64$,
$16(4\mu_{\mathrm{QR}}(n) + 4\sqrt n\,c_{\mathrm N} + 2\mu_{\mathrm{MM}}(n))u \le \beta$,
$\tau \le \|\mathbf{S}\|_2 x$, $\sqrt n\,\tau \le x$ and
$2(\|\mathbf{S}\|_2 + 1)(2\sqrt2\sqrt n + t) \le \Omega$, then
$$\mathbb{P}\bigl[\text{no unitary } \mathbf{W} \text{ has }
\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le
\tfrac32\bar m\beta\bigr] \le e^{-t^2} + \min(r^2, e\,r)\,x^2 \,.$$
Compared with
`NLAlib.FloatMachine.IsArithAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le_of_hasLaw_complexGaussianMatrix`,
the deterministic constant, the norm tail and the singular value tail are sharper.
[Shah2024, Theorem 3.3]. -/
theorem
    FloatMachine.IsArithAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le_exp_neg_sq_add_of_hasLaw_complexGaussianMatrix
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β t x : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsArithAccurate dec u τ Ω μM) (hqr : IsQRErr (decodeComplex dec) u τ Ω μQ M.qr)
    (hnormal : IsNormalSampler (decodeComplex dec) u cN τ Ω M.normal) {n r : ℕ} (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β) (hβ₁ : β ≤ 1) (ht : 0 ≤ t) (hx : 0 < x)
    (hmβ : (1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x * β ≤
      1 / 64)
    (hu : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β) (hτ : τ ≤ specNorm S * x)
    (hτN : τ * √(n : ℝ) ≤ x)
    (hΩ : 2 * (specNorm S + 1) * (2 * √2 * √(n : ℝ) + t) ≤ Ω)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {G : Ω' → Matrix (Fin n) (Fin n) ℂ}
    (hG : HasLaw G (complexGaussianMatrix (Fin n) (Fin n)) μ) :
    μ.real {ω | ¬ ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' (G ω))) ≤
        3 / 2 * ((1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x) *
          β} ≤
      Real.exp (-t ^ 2) + min ((r : ℝ) ^ 2) (Real.exp 1 * r) * x ^ 2 := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hE1 : μ.real {ω | 2 * √2 * √(n : ℝ) + t ≤ specNorm (G ω)} ≤ Real.exp (-t ^ 2) := by
    refine le_trans (measureReal_mono fun ω hω => ?_)
      (measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix hG ht)
    simp only [Set.mem_ofPred_eq, Fintype.card_fin] at hω ⊢
    linarith
  have hsub : {ω | ¬ ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' (G ω))) ≤
        3 / 2 * ((1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x) *
          β} ⊆
      {ω | 2 * √2 * √(n : ℝ) + t ≤ specNorm (G ω)} ∪
        {ω | r ≠ 0 ∧ singularValues (Vᴴ * (G ω).submatrix id (Fin.castLE hr)) (r - 1) ≤ x} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_and] at hcon hω
    exact hω (hM.exists_specNorm_mul_sub_deflate_le_of_good_of_mul_le hqr hnormal hr hU hV hS hA hβ
      hβ₁ ht hx hmβ hu hτ hτN hΩ hcon.1 hcon.2)
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add hE1 (measureReal_rank_deflate_le_min hr hV hG hx.le)))

end NLAlib
