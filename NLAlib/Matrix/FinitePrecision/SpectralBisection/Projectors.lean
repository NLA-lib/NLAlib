/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.SpectralBisection
public import NLAlib.Matrix.FinitePrecision.NewtonSchulzSign.Accuracy

/-!
# Spectral projectors and rank recovery at a node of spectral bisection

On Event I (the
ideal shift $c' = (R/\ell)v$ is at distance at least $w$ from every eigenvalue), the stored
spectral projectors of one node of `NLAlib.eighStep` are within $\beta$ of the true ones, and the
rounded rank estimate is the inertia $i_+(\mathbf{A} - c'\mathbf{I})$, so the node splits exactly
when the true projectors are both nontrivial ([Shah2024, proof of Lemma 4.1]). The precision
hypotheses of a node are bundled in `NLAlib.FloatMachine.IsEighNodeBudget`, generic in the
parameters $(w, x, t)$ of the good event (shift distance, smallest singular value and norm
thresholds of the Gaussian blocks), so that the probabilistic choice of $(x, t)$ is made in the
probability files. The file also holds two facts on roundings.

## Main definitions

* `NLAlib.FloatMachine.IsEighNodeBudget`: the precision hypotheses of one node.

## Main results

* `NLAlib.FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget`:
  the computed projectors.
* `NLAlib.FloatMachine.IsAccurate.min_toNat_eq_inertiaPos_of_isEighNodeBudget`: the rank estimate.
* `NLAlib.FloatMachine.IsAccurate.eighStep_isSplit_iff_of_isEighNodeBudget`: rank recovery.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- If the machine's leaf test $R \le \mathrm{fl}(e R_0)$ fails, then
$eR_0 - u(eR_0 + \tau) < R$ (for $e, R_0 \ge 0$ and $eR_0 \le \Omega$). -/
theorem FloatMachine.IsAccurate.mul_sub_lt_of_le_eq_false {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    {R e R₀ : F} (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) (he : 0 ≤ dec e) (hR₀ : 0 ≤ dec R₀)
    (hΩ : dec e * dec R₀ ≤ Ω) (hint : M.le R (M.mul e R₀) = false) :
    dec e * dec R₀ - u * (dec e * dec R₀ + τ) < dec R := by
  have hlt : dec (M.mul e R₀) < dec R :=
    not_le.mp fun h => by simp [(hM.le_iff _ _).mpr h] at hint
  linarith [(le_and_le_of_isRoundingOf (hM.mul e R₀) (mul_nonneg he hR₀) hΩ hu hτ₀).1]

/-- The stored $\mathrm{fl}(2)$ is within $3u$ of $2$ (for $u \ge 0$, $0 \le \tau \le 1/4$ and
$2 \le \Omega$). -/
private theorem FloatMachine.IsAccurate.abs_dec_ofNat_two_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 4)
    (hΩ : 2 ≤ Ω) : 2 - 3 * u ≤ dec (M.ofNat 2) ∧ dec (M.ofNat 2) ≤ 2 + 3 * u := by
  have h := le_and_le_of_isRoundingOf (hM.ofNat 2) (by norm_num) (by push_cast; linarith) hu hτ₀
  push_cast at h
  have := mul_le_mul_of_nonneg_left hτ1 hu
  constructor <;> linarith [h.1, h.2]

/-- The stored $\mathrm{fl}(Z/\mathrm{fl}(2))$ of a Hermitian $\mathbf{Z}$ within $\delta \le 1$ of
$\mathbf{Y}$, $\|\mathbf{Y}\|_2 \le 2$, is within $\delta/2 + u(2\sqrt k + 4)$ of
$\mathbf{Y}/2$. -/
private theorem FloatMachine.IsAccurate.specNorm_decodeMatrix_hermScale_two_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 1000)
    (hτ₀ : 0 ≤ τ) {k : ℕ} (hk1 : (1 : ℝ) ≤ k) (hkτ : (k : ℝ) * τ ≤ 1 / 4) (hΩ : 4 ≤ Ω)
    {Z : Matrix (Fin k) (Fin k) (F × F)} (hZ : (decodeMatrix dec Z).IsHermitian)
    {Y : Matrix (Fin k) (Fin k) ℂ} (hY : specNorm Y ≤ 2) {δ : ℝ}
    (hδ : specNorm (decodeMatrix dec Z - Y) ≤ δ) (hδ1 : δ ≤ 1) :
    specNorm (decodeMatrix dec (M.hermScale Z (M.ofNat 2)) - (2⁻¹ : ℝ) • Y) ≤
      δ / 2 + u * (2 * √(k : ℝ) + 4) := by
  have hτ1 : τ ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_right hk1 hτ₀]
  obtain ⟨ht1, ht2⟩ := hM.abs_dec_ofNat_two_sub_le hu hτ₀ hτ1 (by linarith)
  have hs := hM.specNorm_sub_decodeMatrix_hermScale_le hu hτ₀ hZ (c := M.ofNat 2)
  set t := dec (M.ofNat 2)
  have ht0 : 0 < t := by linarith
  set Zd := decodeMatrix dec Z
  have hZn : specNorm Zd ≤ 3 := by
    have := specNorm_add_le (Zd - Y) Y
    rw [sub_add_cancel] at this
    linarith
  have hZs : specNorm (t⁻¹ • Zd) ≤ 2 := by
    rw [specNorm_real_smul, abs_of_pos (inv_pos.mpr ht0), inv_mul_le_iff₀ ht0]
    linarith
  have hs' : specNorm (t⁻¹ • Zd - decodeMatrix dec (M.hermScale Z (M.ofNat 2))) ≤
      u * (2 * √(k : ℝ) + 1 / 2) := by
    refine (hs ht0.ne' (by rw [abs_of_pos ht0, div_le_iff₀ ht0]; nlinarith)).trans ?_
    have := mul_le_mul_of_nonneg_left hZs (Real.sqrt_nonneg (k : ℝ))
    nlinarith
  have hinv : |t⁻¹ - 2⁻¹| ≤ u := by
    rw [inv_sub_inv ht0.ne' two_ne_zero, abs_div, abs_of_pos (mul_pos ht0 two_pos),
      div_le_iff₀ (mul_pos ht0 two_pos), abs_le]
    constructor <;> nlinarith
  have hmid : specNorm (t⁻¹ • Zd - (2⁻¹ : ℝ) • Y) ≤ 3 * u + δ / 2 := by
    rw [show t⁻¹ • Zd - (2⁻¹ : ℝ) • Y = (t⁻¹ - 2⁻¹) • Zd + (2⁻¹ : ℝ) • (Zd - Y) by module]
    refine (specNorm_add_le _ _).trans ?_
    rw [specNorm_real_smul, specNorm_real_smul, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    have := mul_le_mul hinv hZn (specNorm_nonneg _) hu
    linarith
  rw [show decodeMatrix dec (M.hermScale Z (M.ofNat 2)) - (2⁻¹ : ℝ) • Y = (t⁻¹ • Zd -
    (2⁻¹ : ℝ) • Y) - (t⁻¹ • Zd - decodeMatrix dec (M.hermScale Z (M.ofNat 2))) by abel]
  exact (specNorm_sub_le _ _).trans (by linarith)

/-- The stored scale $b = \mathrm{fl}(\mathrm{fl}(2)R)$ is within $7uR$ of $2R$ (for
$u \le 1/1000$, $0 \le \tau \le \min(1/4, R/2)$ and $3R + 2 \le \Omega$). -/
private theorem FloatMachine.IsAccurate.dec_mul_ofNat_two_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R : F} (hu : 0 ≤ u) (hu1 : u ≤ 1 / 1000)
    (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 4) (hτR : τ ≤ dec R / 2) (hΩ : 3 * dec R + 2 ≤ Ω) :
    2 * dec R - 7 * u * dec R ≤ dec (M.mul (M.ofNat 2) R) ∧
      dec (M.mul (M.ofNat 2) R) ≤ 2 * dec R + 7 * u * dec R := by
  obtain ⟨ht1, ht2⟩ := hM.abs_dec_ofNat_two_sub_le hu hτ₀ hτ1 (by linarith)
  have hR0 : 0 ≤ dec R := by linarith
  have htR0 : 0 ≤ dec (M.ofNat 2) * dec R := mul_nonneg (by linarith) hR0
  have htR : dec (M.ofNat 2) * dec R ≤ 3 * dec R := mul_le_mul_of_nonneg_right (by linarith) hR0
  obtain ⟨hb1, hb2⟩ := le_and_le_of_isRoundingOf (hM.mul (M.ofNat 2) R) htR0 (by linarith) hu hτ₀
  have e1 := mul_le_mul_of_nonneg_left htR hu
  have e2 := mul_le_mul_of_nonneg_left hτR hu
  have e3 := mul_le_mul_of_nonneg_right ht1 hR0
  have e4 := mul_le_mul_of_nonneg_right ht2 hR0
  have e5 := mul_nonneg hu hR0
  constructor <;> linarith

/-- The stored shift $c = \mathrm{unif}(\mathrm{fl}(R/\mathrm{fl}(\ell)), v)$ of a seed
$v \in [-1, 1]$ is within $2uR$ of the ideal shift $c' = (R/\ell)v$, with $\lvert c\rvert \le
R/10$ and $\lvert c'\rvert \le R/20$ (for $R > 0$, $\ell \ge 20$, $u\ell \le 1/1000$,
$0 \le \tau \le \min(1, R/2)$ and $16(R + \ell) \le \Omega$). -/
private theorem FloatMachine.IsAccurate.abs_dec_unif_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {R : F} {ℓ : ℕ} {v : ℝ} (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ1 : τ ≤ 1) (hR0 : 0 < dec R) (hℓ : (20 : ℝ) ≤ ℓ) (huℓ : u * ℓ ≤ 1 / 1000)
    (hτR : τ ≤ dec R / 2) (hΩ : 16 * (dec R + ℓ) ≤ Ω) (hv : v ∈ Set.Icc (-1 : ℝ) 1) :
    |dec (M.unif (M.div R (M.ofNat ℓ)) v) - dec R / ℓ * v| ≤ 2 * u * dec R ∧
      |dec (M.unif (M.div R (M.ofNat ℓ)) v)| ≤ dec R / 10 ∧ |dec R / ℓ * v| ≤ dec R / 20 := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  -- the rounded `ℓ`
  have hLr := (hM.ofNat ℓ) (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; linarith)
  rw [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) ℓ), max_eq_left (by linarith : τ ≤ (ℓ : ℝ))] at hLr
  have hLr' := abs_le.mp hLr
  have hL1 : 19 ≤ dec (M.ofNat ℓ) := by linarith
  have hL0 : 0 < dec (M.ofNat ℓ) := by linarith
  have hq10 : dec R / dec (M.ofNat ℓ) ≤ dec R / 19 :=
    div_le_div_of_nonneg_left hR0.le (by norm_num) hL1
  have hq0 : 0 ≤ dec R / dec (M.ofNat ℓ) := div_nonneg hR0.le hL0.le
  have hsr := abs_sub_le_of_isRoundingOf (hM.div R (M.ofNat ℓ) hL0.ne')
    (by rw [abs_of_nonneg hq0]; linarith) hu hτ₀
  rw [abs_of_nonneg hq0] at hsr
  set L := dec (M.ofNat ℓ)
  set q := dec R / L with hq
  set s := dec (M.div R (M.ofNat ℓ)) with hs
  clear_value s q L
  have hqd : |q - dec R / ℓ| ≤ u * q := by
    have hqL : q * L = dec R := by rw [hq]; exact div_mul_cancel₀ _ hL0.ne'
    rw [show q - dec R / ℓ = q * (ℓ - L) / ℓ by rw [← hqL]; field_simp, abs_div, abs_mul,
      abs_of_nonneg hq0, abs_of_pos hℓ0, div_le_iff₀ hℓ0]
    nlinarith [mul_le_mul_of_nonneg_left hLr hq0]
  have hsbd : |s - dec R / ℓ| ≤ u * dec R * (7 / 10) := by
    have e1 := abs_sub_le s q (dec R / ℓ)
    rw [abs_sub_comm s q] at e1
    have e2 := mul_le_mul_of_nonneg_left hq10 hu
    have e3 := mul_le_mul_of_nonneg_left hτR hu
    linarith [mul_nonneg hu hR0.le]
  have hRℓ : u * dec R ≤ dec R / ℓ := by
    rw [le_div_iff₀ hℓ0]
    linarith [mul_le_mul_of_nonneg_left huℓ hR0.le]
  have hRℓ2 : dec R / ℓ ≤ dec R / 20 := div_le_div_of_nonneg_left hR0.le (by norm_num) hℓ
  have hsbd' := abs_le.mp hsbd
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ dec R / 10 := by linarith
  obtain ⟨hc1, hc2⟩ := hM.isUnifSampler (M.div R (M.ofNat ℓ)) v (by rw [← hs]; exact hs0) hv
  rw [← hs] at hc1 hc2
  have hv' : |v| ≤ 1 := abs_le.mpr ⟨hv.1, hv.2⟩
  refine ⟨?_, hc1.trans hs1, ?_⟩
  · have e1 := abs_le.mp (hc2.trans (mul_le_mul_of_nonneg_left
      (max_le_add_of_nonneg hs0 hτ₀) hu))
    have e2 : |(s - dec R / ℓ) * v| ≤ |s - dec R / ℓ| := by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hv'
    have e3 := abs_le.mp (e2.trans hsbd)
    have e4 := mul_le_mul_of_nonneg_left hs1 hu
    have e5 := mul_le_mul_of_nonneg_left hτR hu
    have e6 := mul_nonneg hu hR0.le
    rw [abs_le]
    constructor <;> linarith
  · rw [abs_mul, abs_of_nonneg (div_nonneg hR0.le hℓ0.le)]
    exact (mul_le_of_le_one_right (div_nonneg hR0.le hℓ0.le) hv').trans hRℓ2

/-- If $z$ is in the spectrum of $\mathbf{X} - c\mathbf{I}$, then $z + c$ is in that of
$\mathbf{X}$. -/
private theorem add_mem_spectrum_of_mem_spectrum_sub_smul_one {k : ℕ}
    {X : Matrix (Fin k) (Fin k) ℂ} {c z : ℝ}
    (hz : z ∈ spectrum ℝ (X - c • (1 : Matrix (Fin k) (Fin k) ℂ))) : z + c ∈ spectrum ℝ X := by
  rw [spectrum.mem_iff] at hz ⊢
  rwa [show algebraMap ℝ (Matrix (Fin k) (Fin k) ℂ) (z + c) - X =
    algebraMap ℝ _ z - (X - c • (1 : Matrix (Fin k) (Fin k) ℂ)) by
      simp only [Algebra.algebraMap_eq_smul_one, add_smul]; abel]

/-- The stored shifted matrix $\mathbf{X} = \mathrm{fl}(\mathbf{A} - c\mathbf{I})$ of a node, for a
stored shift $c$ within $2uR$ of $c'$, is Hermitian, within $4uR$ of $\mathbf{A} - c'\mathbf{I}$
and of norm at most $(21/20)R + 4uR$; on Event I its eigenvalues have modulus at least
$w - 4uR$. -/
private theorem FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_hermShift_eighShift_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k : ℕ} {A : Matrix (Fin k) (Fin k) (F × F)}
    {R c : F} {c' w : ℝ} (hu : 0 ≤ u)
    (hA : (decodeMatrix dec A).IsHermitian) (hR : specNorm (decodeMatrix dec A) ≤ dec R)
    (hτR : τ ≤ dec R / 2) (hΩ : 2 * dec R ≤ Ω) (hcc : |dec c - c'| ≤ 2 * u * dec R)
    (hcR : |dec c| ≤ dec R / 10) (hcpR : |c'| ≤ dec R / 20)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec A), w ≤ |e - c'|) :
    (decodeMatrix dec (M.hermShift A c)).IsHermitian ∧
      specNorm ((decodeMatrix dec A - c' • (1 : Matrix (Fin k) (Fin k) ℂ)) -
        decodeMatrix dec (M.hermShift A c)) ≤ 4 * u * dec R ∧
      specNorm (decodeMatrix dec (M.hermShift A c)) ≤ 21 / 20 * dec R + 4 * u * dec R ∧
      (∀ z ∈ spectrum ℝ (decodeMatrix dec A - c' • (1 : Matrix (Fin k) (Fin k) ℂ)), w ≤ |z|) ∧
      ∀ x ∈ spectrum ℝ (decodeMatrix dec (M.hermShift A c)), w - 4 * u * dec R ≤ |x| := by
  set Ad := decodeMatrix dec A
  set I := (1 : Matrix (Fin k) (Fin k) ℂ)
  have hI1 : specNorm I ≤ 1 := specNorm_one_le
  have hR0 : 0 ≤ dec R := (specNorm_nonneg _).trans hR
  have hsm : ∀ {a b : ℝ}, |a| ≤ b → specNorm (Ad - a • I) ≤ dec R + b := fun h => by
    refine (specNorm_sub_le _ _).trans (add_le_add hR ?_)
    rw [specNorm_real_smul]
    exact (mul_le_mul_of_nonneg_left hI1 (abs_nonneg _)).trans (by linarith)
  have hAc := hsm hcR
  have hsh := (hM.specNorm_sub_decodeMatrix_hermShift_le hu hA c (hAc.trans (by linarith))).trans
    (mul_le_mul_of_nonneg_left (max_le hAc (by linarith)) hu)
  set Xd := decodeMatrix dec (M.hermShift A c)
  have he : specNorm ((Ad - c' • I) - Xd) ≤ 4 * u * dec R := by
    rw [show (Ad - c' • I) - Xd = ((Ad - dec c • I) - Xd) + (dec c - c') • I by
      rw [sub_smul]; abel]
    refine (specNorm_add_le _ _).trans ?_
    rw [specNorm_real_smul]
    nlinarith [mul_le_mul hcc hI1 (specNorm_nonneg _) (by positivity)]
  have hXh : Xd.IsHermitian := hM.isHermitian_decodeMatrix_hermFrom _ _
  have hB : (Ad - c' • I).IsHermitian := hA.sub (isHermitian_real_smul_one c')
  have hspecA : ∀ z ∈ spectrum ℝ (Ad - c' • I), w ≤ |z| := fun z hz => by
    simpa using hI _ (add_mem_spectrum_of_mem_spectrum_sub_smul_one hz)
  refine ⟨hXh, he, ?_, hspecA, fun x hx => ?_⟩
  · have := specNorm_sub_le (Ad - c' • I) ((Ad - c' • I) - Xd)
    rw [sub_sub_cancel] at this
    linarith [hsm hcpR]
  · rw [hXh.spectrum_eq_image_eigenvalue] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have h1 := hspecA _ (hB.eigenvalue_mem_spectrum hj)
    have h2 := hB.abs_eigenvalue_sub_le hXh j
    have := abs_sub_abs_le_abs_sub (eigenvalue (Ad - c' • I) j) (eigenvalue Xd j)
    linarith

/-- The sign of a shifted Hermitian matrix has norm at most $1$. -/
private theorem specNorm_cfc_sign_sub_smul_one_le {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) (c : ℝ) :
    specNorm (cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) ≤ 1 :=
  (hA.sub (isHermitian_real_smul_one c)).specNorm_cfc_le zero_le_one fun x _ => by
    rcases Real.sign_apply_eq x with h | h | h <;> rw [h] <;> norm_num

/-- The rounded trace $\mathrm{fl}(t + \mathrm{fl}(1/2))$ of a stored $\mathbf{X}$ whose diagonal
sum is within $1/57600$ of $r \le k$ (with $\sum_i \lvert x_{ii}\rvert \le 2k$) has floor $r$. -/
private theorem FloatMachine.IsAccurate.toNat_add_traceRe_div_eq {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) {k : ℕ}
    (hk1 : (1 : ℝ) ≤ k) (hk2u : (k : ℝ) ^ 2 * u ≤ 1 / 100000) (hkτ : (k : ℝ) * τ ≤ 1 / 4)
    (hΩ : 16 * k ≤ Ω) (X : Matrix (Fin k) (Fin k) (F × F)) {r : ℕ} (hrk : (r : ℝ) ≤ k)
    (hdiag : |∑ i, dec (X i i).1 - r| ≤ 1 / 57600) (hsabs : ∑ i, |dec (X i i).1| ≤ 2 * k) :
    M.toNat (M.add (M.traceRe X) (M.div M.one (M.ofNat 2))) = r := by
  have hkk : (k : ℝ) ≤ k ^ 2 := by nlinarith
  have hku : (k : ℝ) * u ≤ 1 / 100000 := by linarith [mul_le_mul_of_nonneg_right hkk hu]
  have hu1 : u ≤ 1 / 100000 := by linarith [mul_le_mul_of_nonneg_right hk1 hu]
  have hτ1 : τ ≤ 1 / 4 := by linarith [mul_le_mul_of_nonneg_right hk1 hτ₀]
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  -- the rounded trace
  have htrace := abs_le.mp (hM.abs_sum_sub_traceRe_le hu hτ₀ (by linarith) X (by linarith))
  have htr2 := mul_le_mul_of_nonneg_left (by linarith : ∑ i, |dec (X i i).1| + k * τ ≤ 3 * k)
    (by positivity : (0 : ℝ) ≤ 2 * k * u)
  have hdiag' := abs_le.mp hdiag
  -- the rounded half
  obtain ⟨h2a, h2b⟩ := hM.abs_dec_ofNat_two_sub_le hu hτ₀ hτ1 (by linarith)
  have hd2 : 1.9 ≤ dec (M.ofNat 2) := by linarith
  have hd20 : 0 < dec (M.ofNat 2) := by linarith
  have hh2 : 1 / dec (M.ofNat 2) ≤ 1 := by rw [div_le_one hd20]; linarith
  have hh := abs_le.mp (abs_sub_le_of_isRoundingOf (hM.div M.one (M.ofNat 2) hd20.ne')
    (by rw [hM.dec_one, abs_of_pos (div_pos one_pos hd20)]; linarith) hu hτ₀)
  rw [hM.dec_one, abs_of_pos (div_pos one_pos hd20)] at hh
  have hh1 : |1 / dec (M.ofNat 2) - 1 / 2| ≤ u := by
    rw [div_sub_div _ _ hd20.ne' (by norm_num), abs_div, abs_of_pos (mul_pos hd20 two_pos),
      div_le_iff₀ (mul_pos hd20 two_pos), abs_le]
    have := mul_le_mul_of_nonneg_left hd2 hu
    constructor <;> linarith
  have hh1' := abs_le.mp hh1
  have := mul_le_mul_of_nonneg_left hh2 hu
  have hdh : |dec (M.div M.one (M.ofNat 2)) - 1 / 2| ≤ 3 * u := by
    rw [abs_le]; constructor <;> linarith
  have hdh' := abs_le.mp hdh
  -- their rounded sum
  have hzabs : |dec (M.traceRe X) + dec (M.div M.one (M.ofNat 2))| ≤ k + 1 := by
    rw [abs_le]; constructor <;> linarith
  have hz := abs_le.mp (abs_sub_le_of_isRoundingOf (hM.add (M.traceRe X)
    (M.div M.one (M.ofNat 2))) (by linarith) hu hτ₀)
  have hzu := mul_le_mul_of_nonneg_left hzabs hu
  rw [hM.toNat_eq, Nat.floor_eq_iff (by linarith)]
  constructor <;> linarith

/-- The rounded rank estimate of a stored projector within $\beta$ of the ideal spectral
projector $\tfrac12(\mathbf{I} + \operatorname{sign}(\mathbf{A} - c\mathbf{I}))$ is the
inertia, for $k\beta \le 1/57600$. -/
private theorem FloatMachine.IsAccurate.min_toNat_eq_inertiaPos_of_specNorm_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hu : 0 ≤ u) (hτ₀ : 0 ≤ τ) {k : ℕ}
    (hk1 : (1 : ℝ) ≤ k) (hk2u : (k : ℝ) ^ 2 * u ≤ 1 / 100000) (hkτ : (k : ℝ) * τ ≤ 1 / 4)
    (hΩ : 16 * k ≤ Ω) {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian) {c : ℝ}
    (hc : ∀ x ∈ spectrum ℝ A, x ≠ c) {β : ℝ} (hβ0 : 0 ≤ β) (hkβ : k * β ≤ 1 / 57600)
    {Pp : Matrix (Fin k) (Fin k) (F × F)}
    (hP : specNorm (decodeMatrix dec Pp -
      (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)))) ≤ β) :
    min k (M.toNat (M.add (M.traceRe Pp) (M.div M.one (M.ofNat 2)))) =
      inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
  set r := inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) with hr
  have hβ1 : β ≤ 1 / 57600 := by nlinarith
  set S := cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))
  have hPid : specNorm ((2⁻¹ : ℝ) • (1 + S)) ≤ 1 := by
    rw [specNorm_real_smul, abs_of_pos (by norm_num)]
    linarith [(specNorm_add_le 1 S).trans (add_le_add specNorm_one_le
      (specNorm_cfc_sign_sub_smul_one_le hA _))]
  have htr := hA.re_trace_smul_one_add_cfc_sign (c := c) fun x hx h => hc x hx h
  rw [← hr] at htr
  have hentry : ∀ i, |dec (Pp i i).1 - RCLike.re (((2⁻¹ : ℝ) • (1 + S)) i i)| ≤ β := by
    intro i
    have h := (RCLike.abs_re_le_norm _).trans
      ((norm_apply_le_specNorm (decodeMatrix dec Pp - (2⁻¹ : ℝ) • (1 + S)) i i).trans hP)
    simpa [decodeMatrix, decodeComplex] using h
  have hentry' : ∀ i, |dec (Pp i i).1| ≤ 1 + β := by
    intro i
    have h1 := (RCLike.abs_re_le_norm _).trans
      ((norm_apply_le_specNorm ((2⁻¹ : ℝ) • (1 + S)) i i).trans hPid)
    have h2 := abs_sub_abs_le_abs_sub (dec (Pp i i).1) (RCLike.re (((2⁻¹ : ℝ) • (1 + S)) i i))
    linarith [hentry i]
  have hdiag : |∑ i, dec (Pp i i).1 - r| ≤ k * β := by
    rw [← htr, Matrix.trace, map_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hentry i
  have hsabs : ∑ i, |dec (Pp i i).1| ≤ k * (1 + β) := by
    rw [mul_add, mul_one]
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hentry' i
  have hrk : (r : ℝ) ≤ k := by
    have : r ≤ k := by
      rw [hr, inertiaPos]
      exact (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hk2 := mul_le_mul_of_nonneg_left (by linarith : 1 + β ≤ 2) (Nat.cast_nonneg (α := ℝ) k)
  rw [hM.toNat_add_traceRe_div_eq hu hτ₀ hk1 hk2u hkτ hΩ Pp hrk (hdiag.trans hkβ)
    (hsabs.trans (by linarith))]
  exact min_eq_right (by exact_mod_cast hrk)

/-! ### Generic node lemmas for a precision budget -/

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
  {N signFuel : ℕ} {R₀ β : F} {w x t : ℝ} {y : EighNode F}

/-- `M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y`: the **precision budget of the
node $y$** of spectral bisection for a good event with shift distance $w$, smallest singular value
threshold $x$ and norm threshold $t$: the node's matrix is Hermitian with norm at most its window
$R$, its depth counter is at least $20$, $0 < \varepsilon \le 1/8$, $0 < w \le R$, $0 < x \le 1$,
$t \ge 2\sqrt2\sqrt k$, and, with $\nu = 4\mu_{\mathrm{MM}}(k) + 10 + 10\sqrt k$ and
$N_0 = N(w/(5R), \beta/(16k))$: the deflation tolerance $2t\beta/x \le
(1 - 1/\ell)\varepsilon/(5\ell)$, the sign condition $32\nu u \le (1 - 2^{-7})\,w\beta/(2R)$, the
stopping condition $2048(k + N_0 + 1)\nu u \le \beta$, the deflation rounding condition
$16(4\mu_{\mathrm{QR}}(k) + 4\sqrt k(c_{\mathrm N} + 1) + 2\mu_{\mathrm{MM}}(k) + 1)u \le \beta$,
$k\beta \le 1/57600$, at least $N_0$ sign steps, and the floor and range conditions
$4k^{3/2}\tau \le \min(x, \varepsilon R_0)$, $16(R_0 + R + k + \ell + t) \le \Omega$. The
hypotheses of [Shah2024, Lemma 4.1] with the constants of
`FloatMachine.IsArithAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le_of_mul_le`
(sign) and
`FloatMachine.IsArithAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le`
(deflation). -/
structure FloatMachine.IsEighNodeBudget {F : Type*} (M : FloatMachine F ℝ ℂ) (dec : F → ℝ)
    (u τ Ω : ℝ) (μM μQ : ℕ → ℝ) (cN : ℝ) (R₀ β : F) (signFuel : ℕ) (w x t : ℝ)
    (y : EighNode F) : Prop where
  /-- The product constant is nonnegative. -/
  nonneg_μM : 0 ≤ μM y.k
  /-- The QR constant is nonnegative. -/
  nonneg_μQ : 0 ≤ μQ y.k
  /-- The sampler constant is nonnegative. -/
  nonneg_cN : 0 ≤ cN
  /-- The unit roundoff is nonnegative. -/
  nonneg_u : 0 ≤ u
  /-- The node's matrix is Hermitian. -/
  isHermitian : (decodeMatrix dec y.A).IsHermitian
  /-- The node's matrix lies in its window. -/
  specNorm_le : specNorm (decodeMatrix dec y.A) ≤ dec y.R
  /-- The depth counter is at least $20$. -/
  twenty_le : 20 ≤ y.ℓ
  /-- The tolerance is positive. -/
  pos_ε : 0 < dec y.ε
  /-- The tolerance is at most $1/8$. -/
  ε_le : dec y.ε ≤ 1 / 8
  /-- The root scale is positive. -/
  pos_R₀ : 0 < dec R₀
  /-- The shift distance is positive. -/
  pos_w : 0 < w
  /-- The shift distance is at most the window. -/
  w_le : w ≤ dec y.R
  /-- The singular value threshold is positive. -/
  pos_x : 0 < x
  /-- The singular value threshold is at most $1$. -/
  x_le : x ≤ 1
  /-- The norm threshold is at least $2\sqrt2\sqrt k$. -/
  le_t : 2 * √2 * √(y.k : ℝ) ≤ t
  /-- The accuracy is positive. -/
  pos_β : 0 < dec β
  /-- The deflation tolerance. -/
  defl_tol : 2 * t / x * dec β ≤ (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)
  /-- The sign condition. -/
  sign_tol : 32 * (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u ≤
    (1 - 2⁻¹ ^ 7) * w / (2 * dec y.R) * dec β
  /-- The stopping condition. -/
  stop_tol : 2048 * (y.k + newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) + 1) *
    (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u ≤ dec β
  /-- The deflation rounding condition. -/
  defl_u : 16 * (4 * μQ y.k + 4 * √(y.k : ℝ) * (cN + 1) + 2 * μM y.k + 1) * u ≤ dec β
  /-- The accuracy is small against the size. -/
  mul_β_le : (y.k : ℝ) * dec β ≤ 1 / 57600
  /-- Enough sign steps. -/
  fuel : newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) ≤ signFuel
  /-- The floor is nonnegative. -/
  nonneg_τ : 0 ≤ τ
  /-- The floor condition. -/
  τ_le : τ * (4 * y.k * √(y.k : ℝ)) ≤ min x (dec y.ε * dec R₀)
  /-- The range condition. -/
  Ω_le : 16 * (dec R₀ + dec y.R + y.k + y.ℓ + t) ≤ Ω

/-- The stopping condition of a node budget without the step count: for $k \ge 1$,
$2048(k + 1)\nu u \le \beta$ with $\nu = 4\mu_{\mathrm{MM}}(k) + 10 + 10\sqrt k$. -/
theorem FloatMachine.IsEighNodeBudget.mul_le_dec_β
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk : 1 ≤ y.k) :
    2048 * (y.k + 1) * (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u ≤ dec β := by
  refine le_trans ?_ hB.stop_tol
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hR := hB.pos_w.trans_le hB.w_le
  have hN := newtonSchulzSteps_nonneg (s := w / (5 * dec y.R)) (ε := dec β / (16 * y.k))
    (div_pos hB.pos_w (by positivity)) (by rw [div_le_iff₀ (by positivity)]; linarith [hB.w_le])
    (div_pos hB.pos_β (by positivity))
    (by rw [div_le_iff₀ (by positivity)]; nlinarith [hB.mul_β_le, hB.pos_β])
  have hν : 0 ≤ (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u :=
    mul_nonneg (by linarith [hB.nonneg_μM, Real.sqrt_nonneg (y.k : ℝ)]) hB.nonneg_u
  nlinarith

/-- The scalar smallness facts of a node budget of positive size: $\beta \le 1/57600$,
$20480u(1 + \sqrt k) \le \beta$, $4k\tau \le 1$, $80\ell\beta \le 1$ and $640uR \le w\beta$. -/
private theorem FloatMachine.IsEighNodeBudget.le_of_one_le
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk : 1 ≤ y.k) :
    dec β ≤ 1 / 57600 ∧ 20480 * u + 20480 * (u * √(y.k : ℝ)) ≤ dec β ∧
      4 * (y.k * τ) ≤ 1 ∧ 80 * (y.ℓ * dec β) ≤ 1 ∧ 640 * (u * dec y.R) ≤ w * dec β := by
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hsq1 : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr hk1
  have hu := hB.nonneg_u
  have hβ := hB.pos_β
  have hR0 : 0 < dec y.R := hB.pos_w.trans_le hB.w_le
  set ν := 4 * μM y.k + 10 + 10 * √(y.k : ℝ) with hν
  have hν10 : 10 + 10 * √(y.k : ℝ) ≤ ν := by linarith [hB.nonneg_μM]
  have hνu : 0 ≤ ν * u := mul_nonneg (by linarith) hu
  have hstop : 2048 * (ν * u) ≤ dec β := by nlinarith [hB.mul_le_dec_β hk]
  have hsign : 32 * (ν * u) ≤ w / (2 * dec y.R) * dec β := by
    have h := hB.sign_tol
    have : 0 ≤ w / (2 * dec y.R) * dec β := by have := hB.pos_w; positivity
    rw [show (1 - 2⁻¹ ^ 7) * w / (2 * dec y.R) * dec β =
      (1 - 2⁻¹ ^ 7) * (w / (2 * dec y.R) * dec β) by ring] at h
    nlinarith
  have hνu' := mul_le_mul_of_nonneg_right hν10 hu
  have hxk : τ * (4 * y.k * √(y.k : ℝ)) ≤ 1 := hB.τ_le.trans ((min_le_left _ _).trans hB.x_le)
  have hkτ := mul_le_mul_of_nonneg_left hsq1 (mul_nonneg (by positivity : (0 : ℝ) ≤ y.k)
    hB.nonneg_τ)
  refine ⟨by nlinarith [hB.mul_β_le], by nlinarith, by nlinarith, ?_, ?_⟩
  · have hℓ : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
    have ht : 1 ≤ t := by
      have : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
      nlinarith [hB.le_t]
    have h2 : 2 * dec β ≤ 2 * t / x * dec β := by
      gcongr
      rw [le_div_iff₀ hB.pos_x]; nlinarith [hB.x_le]
    have h3 : (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ≤ 1 / (40 * y.ℓ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ 1 / (y.ℓ : ℝ) := by positivity
      nlinarith [hB.ε_le, hB.pos_ε, mul_nonneg this hB.pos_ε.le]
    have h4 := (h2.trans hB.defl_tol).trans h3
    rw [le_div_iff₀ (by positivity)] at h4
    nlinarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at hsign
    nlinarith [mul_le_mul_of_nonneg_right hνu' hR0.le,
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg (y.k : ℝ)) hu) hR0.le]

/-- The Newton–Schulz sign of the stored shifted matrix of a node with budget is within
$\beta + \beta/64$ of $\operatorname{sign}(\mathbf{A} - c'\mathbf{I})$ on Event I, when the leaf
test fails. -/
private theorem FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_eighSign_le_of_budget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk : 1 ≤ y.k)
    (hint : M.le y.R (M.mul y.ε R₀) = false)
    {smp : EighSample ℝ ℂ N} (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    specNorm (cfc Real.sign (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) -
      decodeMatrix dec (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
        (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1)))) ≤
      dec β + dec β / 64 := by
  obtain ⟨hβ1, hu20, hkτ, hℓβ, huR⟩ := hB.le_of_one_le hk
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hw := hB.pos_w
  have hβ := hB.pos_β
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hR0 : 0 < dec y.R := hw.trans_le hB.w_le
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
  have hR₀ := hB.pos_R₀
  have hΩ := hB.Ω_le
  have ht0 : 0 ≤ t := le_trans (by positivity) hB.le_t
  have hsk := mul_nonneg hu (Real.sqrt_nonneg (y.k : ℝ))
  have hu1 : u ≤ 1 / 1000000 := by linarith
  have hτ1 : τ ≤ 1 / 4 := by nlinarith
  have hkk : (1 : ℝ) ≤ y.k * √(y.k : ℝ) :=
    one_le_mul_of_one_le_of_one_le hk1 (Real.one_le_sqrt.mpr hk1)
  have h4τ : 4 * τ ≤ dec y.ε * dec R₀ := by
    nlinarith [hB.τ_le.trans (min_le_right _ _), mul_le_mul_of_nonneg_right hkk hτ₀]
  have hε8 := mul_le_mul_of_nonneg_right hB.ε_le hR₀.le
  have hτR : τ ≤ dec y.R / 2 := by
    have := hM.mul_sub_lt_of_le_eq_false hu hτ₀ hB.pos_ε.le hR₀.le (by linarith) hint
    nlinarith [mul_le_mul_of_nonneg_right hu1 (mul_pos hB.pos_ε hR₀).le,
      mul_le_mul_of_nonneg_right hu1 hτ₀]
  obtain ⟨hcc, hcR, hcpR⟩ := hM.abs_dec_unif_sub_le (R := y.R) (ℓ := y.ℓ) hu hτ₀ (by linarith)
    hR0 hℓ' (by nlinarith) hτR (by linarith) hv
  obtain ⟨hb1, hb2⟩ := hM.dec_mul_ofNat_two_le (R := y.R) hu (by linarith) hτ₀ hτ1 hτR
    (by linarith)
  obtain ⟨hXh, he, hXn, hspecA, hspecX⟩ := hM.specNorm_sub_decodeMatrix_hermShift_eighShift_le hu
    hB.isHermitian hB.specNorm_le hτR (by linarith) hcc hcR hcpR hI
  set b := dec (M.mul (M.ofNat 2) y.R)
  set X := M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1)
  set a := w - 4 * u * dec y.R with ha
  have hwβ : w * dec β ≤ w * (1 / 57600) := mul_le_mul_of_nonneg_left hβ1 hw.le
  have huR1 : u * dec y.R ≤ w / 36864000 := by linarith
  have huRR := mul_le_mul_of_nonneg_right huR1 hR0.le
  have huwR := mul_le_mul_of_nonneg_right hu1 (mul_pos hw hR0).le
  have hb0 : 0 < b := by nlinarith [mul_le_mul_of_nonneg_right hu1 hR0.le]
  have hwb := mul_le_mul_of_nonneg_left hb2 hw.le
  have ha0 : 0 < a := by rw [ha]; linarith
  have hab : (1 - 2⁻¹ ^ 7) * w / (2 * dec y.R) ≤ a / b := by
    rw [div_le_div_iff₀ (by positivity) hb0, ha]
    nlinarith
  have hN : newtonSchulzSteps (a / (2 * b)) (dec β / (16 * y.k)) ≤
      newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) := by
    refine newtonSchulzSteps_le_of_le_abs (by positivity) ?_
    rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity), ha]
    linarith [mul_pos hw hR0]
  have hνu : 0 ≤ (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u :=
    mul_nonneg (by linarith [hB.nonneg_μM, Real.sqrt_nonneg (y.k : ℝ)]) hu
  have hstop : 640 * (y.k + newtonSchulzSteps (a / (2 * b)) (dec β / (16 * y.k)) + 1) *
      (4 * μM y.k + 10 + 10 * √(y.k : ℝ)) * u ≤ dec β := by
    refine le_trans ?_ hB.stop_tol
    have h : 640 * (y.k + newtonSchulzSteps (a / (2 * b)) (dec β / (16 * y.k)) + 1) ≤
        2048 * (y.k + newtonSchulzSteps (w / (5 * dec y.R)) (dec β / (16 * y.k)) + 1) := by
      have hw5 : w / (5 * dec y.R) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith [hB.w_le]
      have hβk : dec β / (16 * y.k) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith [newtonSchulzSteps_nonneg (by positivity) hw5 (by positivity) hβk]
    have := mul_le_mul_of_nonneg_right h hνu
    linarith
  have hSN := hM.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le_of_mul_le hB.nonneg_μM hu
    hτ₀ (by linarith) (by linarith) hXh ha0 hspecX (b := M.mul (M.ofNat 2) y.R)
    (by linarith [mul_le_mul_of_nonneg_right hu1 hR0.le]) hβ (by linarith)
    (hB.sign_tol.trans (mul_le_mul_of_nonneg_right hab hβ.le)) hstop (N := signFuel)
    (by exact_mod_cast hN.trans hB.fuel)
  have hAcp := hB.isHermitian.sub (isHermitian_real_smul_one (dec y.R / y.ℓ * smp.1))
  have hmove := hAcp.specNorm_cfc_sign_sub_cfc_sign_le hXh hw hspecA
  have hmove' : 2 * specNorm ((decodeMatrix dec y.A - (dec y.R / y.ℓ * smp.1) •
      (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) - decodeMatrix dec X) / w ≤ dec β / 64 := by
    rw [div_le_iff₀ hw]
    linarith
  have := specNorm_add_le (cfc Real.sign (decodeMatrix dec y.A - (dec y.R / y.ℓ * smp.1) •
      (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) - cfc Real.sign (decodeMatrix dec X))
    (cfc Real.sign (decodeMatrix dec X) - decodeMatrix dec (newtonSchulzSign M β
      (M.mul (M.ofNat 2) y.R) signFuel X))
  rw [sub_add_sub_cancel] at this
  linarith

/-- **Computed spectral projectors under a node budget**: at an internal node with
budget `NLAlib.FloatMachine.IsEighNodeBudget` and Event I (seed in $[-1, 1]$, every eigenvalue at
distance at least $w$ from the ideal shift), the stored $\mathbf{P}_\pm$ are within $\beta$ of
$\tfrac12(\mathbf{I} \pm \operatorname{sign}(\mathbf{A} - c'\mathbf{I}))$. [Shah2024, proof of
Lemma 4.1]. -/
theorem FloatMachine.IsAccurate.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    (hint : M.le y.R (M.mul y.ε R₀) = false)
    {smp : EighSample ℝ ℂ N} (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    specNorm (decodeMatrix dec (M.hermScale (M.hermShift
        (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
          (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) (M.neg M.one)) (M.ofNat 2)) -
      (2⁻¹ : ℝ) • (1 + cfc Real.sign (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)))) ≤ dec β ∧
    specNorm (decodeMatrix dec (M.hermScale (M.negMat (M.hermShift
        (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
          (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) M.one)) (M.ofNat 2)) -
      (2⁻¹ : ℝ) • (1 - cfc Real.sign (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)))) ≤ dec β := by
  rcases Nat.eq_zero_or_pos y.k with hk0 | hk
  · have : IsEmpty (Fin y.k) := by rw [hk0]; infer_instance
    simp only [Subsingleton.elim _ (0 : Matrix (Fin y.k) (Fin y.k) ℂ), specNorm_zero]
    exact ⟨hB.pos_β.le, hB.pos_β.le⟩
  obtain ⟨hβ1, hu20, hkτ, -, -⟩ := hB.le_of_one_le hk
  have hSB := hM.specNorm_cfc_sign_sub_decodeMatrix_eighSign_le_of_budget hB hk hint hv hI
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hβ := hB.pos_β
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast hk
  have hsk := mul_nonneg hu (Real.sqrt_nonneg (y.k : ℝ))
  have hΩ4 : 4 ≤ Ω := by
    have : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
    linarith [hB.Ω_le, hB.pos_R₀, hB.pos_w.trans_le hB.w_le,
      le_trans (by positivity) hB.le_t]
  have hBh := hM.isHermitian_decodeMatrix_newtonSchulzSign β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))
  set B := newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
    (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))
  set S := cfc Real.sign (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))
  set Bd := decodeMatrix dec B
  have hS : specNorm S ≤ 1 := specNorm_cfc_sign_sub_smul_one_le hB.isHermitian _
  have hBn : specNorm Bd ≤ 2 := by
    have := specNorm_sub_le S (S - Bd)
    rw [sub_sub_cancel] at this
    linarith
  have hBS : specNorm (Bd - S) ≤ dec β + dec β / 64 := by rw [specNorm_sub_comm]; exact hSB
  have hI1 : specNorm (1 : Matrix (Fin y.k) (Fin y.k) ℂ) ≤ 1 := specNorm_one_le
  have hsc : ∀ {Z : Matrix (Fin y.k) (Fin y.k) (F × F)} {Y : Matrix (Fin y.k) (Fin y.k) ℂ},
      (decodeMatrix dec Z).IsHermitian → specNorm Y ≤ 2 →
      specNorm (decodeMatrix dec Z - Y) ≤ dec β + dec β / 64 + 3 * u →
      specNorm (decodeMatrix dec (M.hermScale Z (M.ofNat 2)) - (2⁻¹ : ℝ) • Y) ≤ dec β :=
    fun hZ hY hZY => (hM.specNorm_decodeMatrix_hermScale_two_sub_le hu (by linarith) hτ₀ hk1
      (by linarith) hΩ4 hZ hY hZY (by linarith)).trans (by linarith)
  have hshift : ∀ s : F, |dec s| = 1 → specNorm ((Bd - dec s • 1) -
      decodeMatrix dec (M.hermShift B s)) ≤ 3 * u := fun s hs => by
    have hBs : specNorm (Bd - dec s • 1) ≤ 3 := by
      refine (specNorm_sub_le _ _).trans ?_
      rw [specNorm_real_smul, hs, one_mul]
      linarith
    have hτ3 : τ ≤ 3 := by nlinarith
    exact (hM.specNorm_sub_decodeMatrix_hermShift_le hu hBh s (by linarith)).trans
      (by linarith [mul_le_mul_of_nonneg_left (max_le hBs hτ3) hu])
  have hW : ∀ s : F, (decodeMatrix dec (M.hermShift B s)).IsHermitian := fun s =>
    hM.isHermitian_decodeMatrix_hermFrom _ _
  constructor
  · have hsh := hshift (M.neg M.one) (by rw [hM.dec_neg, hM.dec_one]; norm_num)
    rw [hM.dec_neg, hM.dec_one, neg_one_smul, sub_neg_eq_add] at hsh
    refine hsc (hW _) ((specNorm_add_le _ _).trans (by linarith)) ?_
    rw [show decodeMatrix dec (M.hermShift B (M.neg M.one)) - (1 + S) =
      (Bd - S) - ((Bd + 1) - decodeMatrix dec (M.hermShift B (M.neg M.one))) by abel]
    exact (specNorm_sub_le _ _).trans (by linarith)
  · have hsh := hshift M.one (by rw [hM.dec_one]; norm_num)
    rw [hM.dec_one, one_smul] at hsh
    refine hsc (by rw [hM.decodeMatrix_negMat]; exact (hW _).neg)
      ((specNorm_sub_le _ _).trans (by linarith)) ?_
    rw [hM.decodeMatrix_negMat, show -decodeMatrix dec (M.hermShift B M.one) - (1 - S) =
      ((Bd - 1) - decodeMatrix dec (M.hermShift B M.one)) - (Bd - S) by abel]
    exact (specNorm_sub_le _ _).trans (by linarith)

/-- The smallness facts of a node budget used for the rounded trace: $k^2u \le 10^{-5}$,
$k\tau \le 1/4$ and $16k \le \Omega$. -/
private theorem FloatMachine.IsEighNodeBudget.sq_mul_le
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk1 : (1 : ℝ) ≤ y.k) :
    (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 ∧ (y.k : ℝ) * τ ≤ 1 / 4 ∧ 16 * (y.k : ℝ) ≤ Ω := by
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hβ := hB.pos_β
  have hkβ := hB.mul_β_le
  have hβ1 : dec β ≤ 1 / 57600 := by linarith [mul_le_mul_of_nonneg_right hk1 hβ.le]
  have hsk : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr hk1
  -- smallness of `k u` and `k τ`
  have hku : (y.k : ℝ) * u ≤ dec β / 20480 := by
    have := mul_le_mul_of_nonneg_right (by linarith [hB.nonneg_μM, Real.sqrt_nonneg (y.k : ℝ)] :
      (10 : ℝ) ≤ 4 * μM y.k + 10 + 10 * √(y.k : ℝ))
      (mul_nonneg (by linarith : (0 : ℝ) ≤ y.k + 1) hu)
    linarith [hB.mul_le_dec_β (by exact_mod_cast hk1)]
  have hk2u : (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 := by
    have := mul_le_mul_of_nonneg_left hku (by linarith : (0 : ℝ) ≤ y.k)
    nlinarith
  have hkτ : (y.k : ℝ) * τ ≤ 1 / 4 := by
    have h1 := hB.τ_le.trans ((min_le_left _ _).trans hB.x_le)
    have := mul_le_mul_of_nonneg_left hsk (by positivity : (0 : ℝ) ≤ y.k * τ)
    nlinarith
  have hΩ : 16 * (y.k : ℝ) ≤ Ω := by
    have := hB.Ω_le
    have : (0 : ℝ) ≤ y.ℓ := by positivity
    linarith [hB.pos_R₀, hB.pos_w.trans_le hB.w_le, hB.le_t,
      (by positivity : (0 : ℝ) ≤ 2 * √2 * √(y.k : ℝ))]
  exact ⟨hk2u, hkτ, hΩ⟩

/-- **The rank estimate under a node budget**: at an internal node of size $k \ge 2$ with budget
`NLAlib.FloatMachine.IsEighNodeBudget`, not a leaf
($\mathrm{fl}(R) > \mathrm{fl}(\varepsilon R_0)$), and Event I (seed $v \in [-1, 1]$, every
eigenvalue at distance at least $w$ from the ideal shift $c' = (R/\ell)v$), the rounded trace of
the stored projector $\mathbf{P}_+$ of `NLAlib.eighStep`, capped at $k$, is the inertia
$i_+(\mathbf{A} - c'\mathbf{I})$. [Shah2024, proof of Lemma 4.1]. -/
theorem FloatMachine.IsAccurate.min_toNat_eq_inertiaPos_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false) {smp : EighSample ℝ ℂ N}
    (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    min y.k (M.toNat (M.add (M.traceRe (M.hermScale (M.hermShift
        (newtonSchulzSign M β (M.mul (M.ofNat 2) y.R) signFuel
          (M.hermShift y.A (M.unif (M.div y.R (M.ofNat y.ℓ)) smp.1))) (M.neg M.one)) (M.ofNat 2)))
        (M.div M.one (M.ofNat 2)))) =
      inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) := by
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast (by omega : 1 ≤ y.k)
  obtain ⟨hk2u, hkτ, hΩ⟩ := hB.sq_mul_le hk1
  exact hM.min_toNat_eq_inertiaPos_of_specNorm_sub_le hB.nonneg_u hB.nonneg_τ hk1 hk2u hkτ hΩ
    hB.isHermitian (fun e he h => by
      have := hI e he; rw [h, sub_self, abs_zero] at this; linarith [hB.pos_w]) hB.pos_β.le
    hB.mul_β_le (hM.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget hB hint hv hI).1

/-- **Rank recovery under a node budget**: at an internal node of size $k \ge 2$ with budget
`NLAlib.FloatMachine.IsEighNodeBudget` and Event I (seed in $[-1, 1]$, every eigenvalue at distance
at least $w$ from the ideal shift $c'$), the step splits iff
$0 < i_+(\mathbf{A} - c'\mathbf{I}) < k$. [Shah2024,
proof of Lemma 4.1]. -/
theorem FloatMachine.IsAccurate.eighStep_isSplit_iff_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    (hk : 2 ≤ y.k) (hint : M.le y.R (M.mul y.ε R₀) = false) {smp : EighSample ℝ ℂ N}
    (hv : smp.1 ∈ Set.Icc (-1 : ℝ) 1)
    (hI : ∀ e ∈ spectrum ℝ (decodeMatrix dec y.A), w ≤ |e - dec y.R / y.ℓ * smp.1|) :
    (eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ smp).IsSplit ↔
      0 < inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) ∧
      inertiaPos (decodeMatrix dec y.A -
        (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) < y.k := by
  set r := inertiaPos (decodeMatrix dec y.A -
    (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ)) with hr
  have hrk : r ≤ y.k := by
    rw [hr, inertiaPos]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hkp := hM.min_toNat_eq_inertiaPos_of_isEighNodeBudget hB hk hint hv hI
  rw [← hr] at hkp
  unfold eighStep
  rw [if_neg (by omega), if_neg (by simp [hint])]
  dsimp only
  clear_value r
  split_ifs with h1 h2
  · rw [hkp] at h1
    exact iff_of_false id (by rw [h1]; exact fun h => h.2.false)
  · rw [hkp] at h2
    exact iff_of_false id (by rw [h2]; exact fun h => h.1.false)
  · rw [hkp] at h1 h2
    exact iff_of_true trivial ⟨Nat.pos_of_ne_zero h2, lt_of_le_of_ne hrk h1⟩

end NLAlib
