/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.FinitePrecision.Deflation
public import NLAlib.Matrix.FinitePrecision.SpectralBisection.Projectors

/-!
# Frames, deflated bases and compressions at a split of spectral bisection

When the step of a node
of `NLAlib.eighStep` with a good sample is a split, each side has an orthonormal frame of the
true spectral projector, the computed basis is within $\eta = (1 - 1/\ell)\varepsilon/(5\ell)$ of
a rotation of that frame (deflation, Event II), and the stored child is within $(2 + 2\eta)R\eta$
of the compression of the node's matrix shifted by the stored half window ([Shah2024, proof of
Lemma 4.1]).

## Main results

* `NLAlib.FloatMachine.IsAccurate.abs_dec_div_ofNat_two_sub_le`: the stored half window.
* `NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_isEighNodeBudget`:
  frames, deflated bases and compressions at a split.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- The stored half window $\mathrm{fl}(R/\mathrm{fl}(2))$ is within $3u$ (relative) of $R/2$, for
$0 \le u \le 1/1000$, $0 \le \tau \le 1/8$, $6\tau \le R$, $2 \le \Omega$ and $R \le \Omega$. -/
theorem FloatMachine.IsAccurate.abs_dec_div_ofNat_two_sub_le {F : Type*} {M : FloatMachine F ℝ ℂ}
    {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ} (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hu : 0 ≤ u) (hu1 : u ≤ 1 / 1000) (hτ₀ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 8) {R : F}
    (hRτ : 6 * τ ≤ dec R) (hΩ2 : 2 ≤ Ω) (hΩR : dec R ≤ Ω) :
    |dec (M.div R (M.ofNat 2)) - dec R / 2| ≤ 3 * u * (dec R / 2) := by
  have h2 := abs_le.mp (abs_sub_le_of_isRoundingOf (hM.ofNat 2) (by norm_num; linarith) hu hτ₀)
  push_cast at h2
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h2
  have huτ := mul_le_mul_of_nonneg_left hτ1 hu
  set t := dec (M.ofNat 2)
  have ht1 : 2 - 2.2 * u ≤ t := by linarith
  have ht2 : t ≤ 2 + 2.2 * u := by linarith
  have ht0 : 0 < t := by linarith
  have hR0 : 0 ≤ dec R := by linarith
  have hq : |dec R / t - dec R / 2| ≤ 0.6 * u * dec R := by
    rw [div_sub_div _ _ ht0.ne' (by norm_num), abs_div, abs_of_pos (mul_pos ht0 two_pos),
      div_le_iff₀ (mul_pos ht0 two_pos), abs_le]
    have e1 := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hu hR0)
    have e2 := mul_le_mul_of_nonneg_left ht2 (mul_nonneg hu hR0)
    have e3 := mul_le_mul_of_nonneg_left ht1 hR0
    have e4 := mul_le_mul_of_nonneg_left ht2 hR0
    have e5 := mul_le_mul_of_nonneg_left hu1 (mul_nonneg hu hR0)
    constructor <;> nlinarith
  have hq' := abs_le.mp hq
  have hRt : dec R / t ≤ 0.51 * dec R := by
    rw [div_le_iff₀ ht0]
    nlinarith [mul_le_mul_of_nonneg_left ht1 hR0, mul_le_mul_of_nonneg_left hu1 hR0]
  have hRt0 : 0 ≤ dec R / t := div_nonneg hR0 ht0.le
  have hz := abs_le.mp (abs_sub_le_of_isRoundingOf (hM.div R (M.ofNat 2) ht0.ne')
    (by rw [abs_of_nonneg hRt0]; linarith) hu hτ₀)
  rw [abs_of_nonneg hRt0] at hz
  have := mul_le_mul_of_nonneg_left hRt hu
  have := mul_le_mul_of_nonneg_left hRτ hu
  rw [abs_le]; constructor <;> linarith

/-- A Hermitian eigenvalue is bounded by the spectral norm. -/
private theorem abs_le_of_mem_spectrum_of_specNorm_le {k : ℕ} {X : Matrix (Fin k) (Fin k) ℂ}
    (hX : X.IsHermitian) {R x : ℝ} (hR : specNorm X ≤ R) (hx : x ∈ spectrum ℝ X) : |x| ≤ R := by
  rw [hX.spectrum_eq_image_eigenvalue] at hx
  obtain ⟨j, -, rfl⟩ := hx
  exact (hX.abs_eigenvalue_le_specNorm j).trans hR

/-- The frame of the positive spectral projector, with a prescribed column count. -/
private theorem exists_frame_pos {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) {R c : ℝ} (hR : specNorm A ≤ R) (hc : ∀ x ∈ spectrum ℝ A, x ≠ c)
    {r : ℕ} (hr : inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) = r) :
    ∃ V : Matrix (Fin k) (Fin r) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) ∧
      spectrum ℝ (Vᴴ * A * V) ⊆ Set.Icc c R := by
  subst hr
  obtain ⟨V, hV, hVV, -, hsp⟩ := hA.exists_hasOrthonormalCols_mul_conjTranspose_eq hc
  refine ⟨V, hV, hVV, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hsp hx
  exact ⟨le_of_lt h2, (le_abs_self x).trans (abs_le_of_mem_spectrum_of_specNorm_le hA hR h1)⟩

/-- The frame of the negative spectral projector, with the complementary column count. -/
private theorem exists_frame_neg {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ}
    (hA : A.IsHermitian) {R c : ℝ} (hR : specNorm A ≤ R) (hc : ∀ x ∈ spectrum ℝ A, x ≠ c)
    {m : ℕ} (hm : inertiaPos (A - c • (1 : Matrix (Fin k) (Fin k) ℂ)) = m) (hmk : m ≤ k) :
    ∃ V : Matrix (Fin k) (Fin (k - m)) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 - cfc Real.sign (A - c • (1 : Matrix (Fin k) (Fin k) ℂ))) ∧
      spectrum ℝ (Vᴴ * A * V) ⊆ Set.Icc (-R) c := by
  set X := A - c • (1 : Matrix (Fin k) (Fin k) ℂ) with hXdef
  have hX : X.IsHermitian := hA.sub (isHermitian_real_smul_one c)
  have hc' : ∀ x ∈ spectrum ℝ (-A), x ≠ -c := by
    intro x hx hxc
    rw [← spectrum.neg_eq] at hx
    exact hc (-x) (Set.mem_neg.mp hx) (by rw [hxc, neg_neg])
  have heq : -A - (-c) • (1 : Matrix (Fin k) (Fin k) ℂ) = -X := by
    rw [hXdef, neg_smul]; abel
  have hunit : IsUnit X := by
    have hcn : c ∉ spectrum ℝ A := fun h => hc c h rfl
    rw [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one] at hcn
    rw [show X = -(c • (1 : Matrix (Fin k) (Fin k) ℂ) - A) by rw [hXdef]; abel]
    exact hcn.neg
  have hrank : X.rank = k := by rw [Matrix.rank_of_isUnit X hunit, Fintype.card_fin]
  have hrk : inertiaPos (-A - (-c) • (1 : Matrix (Fin k) (Fin k) ℂ)) = k - m := by
    rw [heq, ← inertiaNeg_eq_inertiaPos_neg]
    have := hX.inertiaPos_add_inertiaNeg
    omega
  have key := hA.neg.exists_hasOrthonormalCols_mul_conjTranspose_eq hc'
  rw [hrk] at key
  obtain ⟨V, hV, hVV, -, hsp⟩ := key
  refine ⟨V, hV, ?_, fun x hx => ?_⟩
  · rw [hVV, heq]
    have hs : cfc Real.sign (-X) = -cfc Real.sign X := by
      rw [← cfc_comp_neg Real.sign X ((X.finite_real_spectrum.image _).continuousOn _)
        hX.isSelfAdjoint]
      rw [show (fun x : ℝ => Real.sign (-x)) = fun x => -Real.sign x from
        funext fun x => Real.sign_neg, cfc_neg]
    rw [hs, ← sub_eq_add_neg]
  · have hx' : -x ∈ spectrum ℝ (Vᴴ * -A * V) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, ← spectrum.neg_eq]
      exact Set.neg_mem_neg.mpr hx
    obtain ⟨h1, h2⟩ := hsp hx'
    rw [← spectrum.neg_eq] at h1
    have := abs_le_of_mem_spectrum_of_specNorm_le hA hR (by simpa using h1)
    rw [Set.mem_Ioi] at h2
    exact ⟨(neg_abs_le x).trans' (by linarith), by linarith⟩

/-- The product contract through `decodeMatrix`. -/
private theorem FloatMachine.IsAccurate.specNorm_mul_sub_decodeMatrix_mm_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {l m n : ℕ} (A : Matrix (Fin l) (Fin m) (F × F))
    (B : Matrix (Fin m) (Fin n) (F × F))
    (h : specNorm (decodeMatrix dec A) * specNorm (decodeMatrix dec B) ≤ Ω) :
    specNorm (decodeMatrix dec A * decodeMatrix dec B - decodeMatrix dec (M.mm A B)) ≤
      μM (max l (max m n)) * u *
        max (specNorm (decodeMatrix dec A) * specNorm (decodeMatrix dec B)) τ :=
  hM.isMatMulErr.specNorm_mul_sub_le A B h

/-- Replacing the frame $\mathbf{Z}$ ($\|\mathbf{Z}\|_2 \le 1$) of a compression by a matrix
within $e$ of it costs at most $Re(2 + e)$, for $\|\mathbf{A}\|_2 \le R$. -/
private theorem specNorm_conjTranspose_mul_mul_sub_le {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m m ℂ} {Z Q : Matrix m n ℂ} {R e : ℝ} (hA : specNorm A ≤ R)
    (hZ : specNorm Z ≤ 1) (he : specNorm (Z - Q) ≤ e) :
    specNorm (Zᴴ * A * Z - Qᴴ * A * Q) ≤ R * (e * (2 + e)) := by
  have hR0 : 0 ≤ R := (specNorm_nonneg _).trans hA
  have he0 : 0 ≤ e := (specNorm_nonneg _).trans he
  have hQ : specNorm Q ≤ 1 + e := by
    rw [show Q = Z - (Z - Q) by abel]; exact (specNorm_sub_le _ _).trans (add_le_add hZ he)
  have hZA : specNorm (Zᴴ * A) ≤ R :=
    (specNorm_mul_le _ _).trans ((mul_le_mul (by rw [specNorm_conjTranspose]; exact hZ) hA
      (specNorm_nonneg _) zero_le_one).trans (one_mul R).le)
  rw [show Zᴴ * A * Z - Qᴴ * A * Q = Zᴴ * A * (Z - Q) + (Z - Q)ᴴ * A * Q by
    rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]; abel]
  refine (specNorm_add_le _ _).trans ?_
  have h1 : specNorm (Zᴴ * A * (Z - Q)) ≤ R * e :=
    (specNorm_mul_le _ _).trans (mul_le_mul hZA he (specNorm_nonneg _) hR0)
  have h2 : specNorm ((Z - Q)ᴴ * A * Q) ≤ R * e * (1 + e) := by
    refine (specNorm_mul_le _ _).trans (mul_le_mul ?_ hQ (specNorm_nonneg _) (mul_nonneg hR0 he0))
    refine (specNorm_mul_le _ _).trans ?_
    rw [specNorm_conjTranspose, mul_comm R]
    exact mul_le_mul he hA (specNorm_nonneg _) he0
  linarith [show R * e + R * e * (1 + e) = R * (e * (2 + e)) by ring]

/-- The Hermitian average $d^{-1}(\mathbf{C} + \mathbf{C}^{\mathsf{H}})$, for
$\lvert d - 2\rvert \le 3u$ ($u \le 1/1000$), of a $\mathbf{C}$ within $\delta \le R/100$ of a
Hermitian $\mathbf{H}$ with $\|\mathbf{H}\|_2 \le R$, is within $\delta + 3uR/100 + 3uR$ of
$\mathbf{H}$. -/
private theorem specNorm_sub_inv_smul_add_conjTranspose_le {n : Type*} [Fintype n]
    {H C : Matrix n n ℂ} {R δ u d : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 1000) (hHh : Hᴴ = H)
    (hH : specNorm H ≤ R) (hHC : specNorm (H - C) ≤ δ) (hδ : δ ≤ R / 100)
    (hd : |d - 2| ≤ 3 * u) :
    specNorm (H - d⁻¹ • (C + Cᴴ)) ≤ δ + 3 * u * (R / 100) + 3 * u * R := by
  obtain ⟨hda, hdb⟩ := abs_le.mp hd
  have hd1 : 1 ≤ d := by linarith
  have ha : d⁻¹ * d = 1 := inv_mul_cancel₀ (by linarith)
  have ha0 : 0 < d⁻¹ := inv_pos.mpr (by linarith)
  have ha1 : d⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd1
  have h2a : 2 * d⁻¹ ≤ 1 + 3 * u := by
    linarith [mul_le_mul_of_nonneg_left (by linarith : 2 - 3 * u ≤ d) ha0.le,
      mul_le_mul_of_nonneg_right ha1 (by linarith : 0 ≤ 3 * u)]
  have h1a : |1 - 2 * d⁻¹| ≤ 3 * u := by
    rw [show 1 - 2 * d⁻¹ = d⁻¹ * (d - 2) by rw [mul_sub, ha]; ring, abs_mul, abs_of_pos ha0]
    linarith [mul_le_mul_of_nonneg_left hd ha0.le,
      mul_le_mul_of_nonneg_right ha1 (by linarith : 0 ≤ 3 * u)]
  rw [show H - d⁻¹ • (C + Cᴴ) = d⁻¹ • ((H - C) + (H - C)ᴴ) + (1 - 2 * d⁻¹) • H by
    rw [Matrix.conjTranspose_sub, hHh]; module]
  refine (specNorm_add_le _ _).trans ?_
  rw [specNorm_real_smul, specNorm_real_smul, abs_of_pos ha0]
  have hHC0 := specNorm_nonneg (H - C)
  have h1 : specNorm ((H - C) + (H - C)ᴴ) ≤ 2 * specNorm (H - C) := by
    have := specNorm_add_le (H - C) (H - C)ᴴ
    rw [specNorm_conjTranspose] at this; linarith
  have h2 := mul_le_mul_of_nonneg_left h1 ha0.le
  have h3 := mul_le_mul_of_nonneg_right h2a hHC0
  have h4 := mul_le_mul h1a hH (specNorm_nonneg _) (by linarith)
  have h5 := mul_le_mul_of_nonneg_left (hHC.trans hδ) (by linarith : 0 ≤ 3 * u)
  linarith

/-- The stored Hermitian average and shift of a matrix near a Hermitian `H`. -/
private theorem FloatMachine.IsAccurate.specNorm_decodeMatrix_hermShift_hermAvg_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {r : ℕ} {β R δ : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hβ1 : β ≤ 1 / 115200) (hR0 : 0 < R)
    (hτ0 : 0 ≤ τ) (hτR : τ ≤ R / 3) (hrτ : (r : ℝ) * τ ≤ R / 3) (hsr : √(r : ℝ) * u ≤ β / 4)
    (hΩ : 4 * R ≤ Ω) {H : Matrix (Fin r) (Fin r) ℂ} (hHh : Hᴴ = H) (hH : specNorm H ≤ R)
    {X : Matrix (Fin r) (Fin r) (F × F)} (hHC2 : specNorm (H - decodeMatrix dec X) ≤ δ)
    (hδ : δ ≤ R / 100) {two s : F} (htwo : |dec two - 2| ≤ 3 * u) (hs : |dec s| ≤ R) :
    specNorm (decodeMatrix dec (M.hermShift (M.hermAvg X two) s) -
      (H - dec s • (1 : Matrix (Fin r) (Fin r) ℂ))) ≤
        δ + 3 * u * (R / 100) + 3 * u * R + (3 * (β / 4) * (102 / 100 * R) + 2 * (u * R)) +
          u * (21 / 10 * R + R / 3) := by
  have hβR : β * R ≤ R / 115200 := by nlinarith [mul_le_mul_of_nonneg_right hβ1 hR0.le]
  set C2 := decodeMatrix dec X with hC2def
  set d := dec two with hddef
  have hd1 : 1 ≤ d := by linarith [(abs_le.mp htwo).1]
  set Hs := d⁻¹ • (C2 + C2ᴴ) with hHsdef
  have hHHs := specNorm_sub_inv_smul_add_conjTranspose_le hu0 (by linarith) hHh hH hHC2 hδ htwo
  rw [← hHsdef] at hHHs
  have huR : u * R ≤ β * R := mul_le_mul_of_nonneg_right hu1 hR0.le
  have hHs : specNorm Hs ≤ 102 / 100 * R := by
    rw [show Hs = H - (H - Hs) by abel]
    refine (specNorm_sub_le _ _).trans ?_
    linarith
  have hC2 : specNorm C2 ≤ 101 / 100 * R := by
    rw [show C2 = H - (H - C2) by abel]
    exact (specNorm_sub_le _ _).trans (by linarith)
  have hAvg := hM.specNorm_sub_decodeMatrix_hermAvg_le hu0 (by linarith) hτ0 X (c := two)
    (by rw [← hddef, abs_of_pos (by linarith)]; exact hd1) (by rw [← hC2def]; linarith)
  rw [← hC2def, ← hddef, ← hHsdef] at hAvg
  set Y := decodeMatrix dec (M.hermAvg X two) with hYdef
  have hHsY : specNorm (Hs - Y) ≤ 3 * (β / 4) * (102 / 100 * R) + 2 * (u * R) := by
    refine hAvg.trans ?_
    rw [show 3 * u * (√(r : ℝ) * specNorm Hs + 2 * r * τ) =
      3 * (√(r : ℝ) * u) * specNorm Hs + 6 * u * (r * τ) by ring]
    have h1 : 3 * (√(r : ℝ) * u) * specNorm Hs ≤ 3 * (β / 4) * (102 / 100 * R) :=
      mul_le_mul (by linarith) hHs (specNorm_nonneg _) (by linarith)
    linarith [mul_le_mul_of_nonneg_left hrτ (by linarith : 0 ≤ 6 * u)]
  -- the shift
  set I := (1 : Matrix (Fin r) (Fin r) ℂ)
  have hs1 : specNorm (dec s • I) ≤ R := by
    rw [specNorm_real_smul]
    exact (mul_le_mul hs specNorm_one_le (specNorm_nonneg _) hR0.le).trans (mul_one R).le
  have hYs : specNorm (Y - dec s • I) ≤ 21 / 10 * R := by
    rw [show Y - dec s • I = Hs - (Hs - Y) - dec s • I by abel]
    refine (specNorm_sub_le _ _).trans ?_
    linarith [specNorm_sub_le Hs (Hs - Y)]
  have hYh : Y.IsHermitian := hM.isHermitian_decodeMatrix_hermFrom _ _
  have hSh := (hM.specNorm_sub_decodeMatrix_hermShift_le hu0 hYh s (by linarith)).trans
    (mul_le_mul_of_nonneg_left (max_le (c := 21 / 10 * R + R / 3) (by linarith) (by linarith)) hu0)
  rw [← hYdef] at hSh
  rw [show decodeMatrix dec (M.hermShift (M.hermAvg X two) s) - (H - dec s • I) =
    -((H - Hs) + (Hs - Y)) - ((Y - dec s • I) - decodeMatrix dec (M.hermShift (M.hermAvg X two) s))
      by abel]
  refine (specNorm_sub_le _ _).trans ?_
  rw [specNorm_neg]
  linarith [specNorm_add_le (H - Hs) (Hs - Y)]

/-- A split of `NLAlib.eighStep` happens at an internal node whose leaf test fails. -/
private theorem two_le_and_le_eq_false_of_eighStep_eq_split {F Su Sg : Type*} [Inhabited Sg]
    {M : FloatMachine F Su Sg} {N signFuel : ℕ} {R₀ β : F} {k : ℕ}
    {A : Matrix (Fin k) (Fin k) (F × F)} {R ε : F} {ℓ : ℕ} {smp : EighSample Su Sg N} {kp : ℕ}
    {hkp : kp ≤ k} {Qp : Matrix (Fin k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin k) (Fin (k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (k - kp)) (Fin (k - kp)) (F × F)} {σ : F}
    (h : eighStep M N signFuel R₀ β A R ε ℓ smp = .split kp hkp Qp Qm Ap Am σ) :
    2 ≤ k ∧ M.le R (M.mul ε R₀) = false := by
  unfold eighStep at h
  by_cases hk : k ≤ 1
  · rw [if_pos hk] at h; cases h
  cases hle : M.le R (M.mul ε R₀)
  · exact ⟨by omega, rfl⟩
  · rw [if_neg hk, if_pos hle] at h; cases h

/-! ### Generic node lemmas for a precision budget -/

variable {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
  {N signFuel : ℕ} {R₀ β : F} {w x t : ℝ} {y : EighNode F}

/-- The two stored products of a compression, against the exact compression by `V W`. -/
private theorem FloatMachine.IsAccurate.specNorm_compress_sub_decodeMatrix_mm_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k r : ℕ} (hk1 : 1 ≤ k) (hrk : r ≤ k) {β e R : ℝ}
    (hu0 : 0 ≤ u) (hμ0 : 0 ≤ μM k) (hμ : μM k * u ≤ β / 2)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 115200) (he0 : 0 ≤ e) (he1 : e ≤ 1 / 500)
    (hR0 : 0 < R) (hτ0 : 0 ≤ τ) (hkτ : 3 * k * τ ≤ R) (hΩ : 4 * R ≤ Ω)
    {As : Matrix (Fin k) (Fin k) (F × F)} (hAR : specNorm (decodeMatrix dec As) ≤ R)
    {Q : Matrix (Fin k) (Fin r) (F × F)} {V : Matrix (Fin k) (Fin r) ℂ}
    {W : Matrix (Fin r) (Fin r) ℂ} (hV : HasOrthonormalCols V) (hW : HasOrthonormalCols W)
    (he : specNorm (V * W - decodeMatrix dec Q) ≤ e) :
    specNorm ((V * W)ᴴ * decodeMatrix dec As * (V * W) -
      decodeMatrix dec (M.mm (M.mm (M.conjTransposeMat Q) As) Q)) ≤
        R * (e * (2 + e)) + 136 / 100 * β * R := by
  set A := decodeMatrix dec As with hAdef
  set Qb := decodeMatrix dec Q with hQbdef
  have heR' : (1 + e) * R ≤ 1002 / 1000 * R := mul_le_mul_of_nonneg_right (by linarith) hR0.le
  have hτR : τ ≤ R / 3 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith [mul_le_mul_of_nonneg_right this hτ0]
  have hβR := mul_le_mul_of_nonneg_right hβ1 hR0.le
  have hβR0 := mul_nonneg hβ0 hR0.le
  have hA0 := specNorm_nonneg A
  have hμu0 : 0 ≤ μM k * u := mul_nonneg hμ0 hu0
  have hQ : specNorm Qb ≤ 1 + e := by
    rw [show Qb = V * W - (V * W - Qb) by abel]
    exact (specNorm_sub_le _ _).trans (by linarith [(hV.mul hW).specNorm_le_one])
  have hQ0 := specNorm_nonneg Qb
  -- the first product
  have hQH : decodeMatrix dec (M.conjTransposeMat Q) = Qbᴴ := hM.decodeMatrix_conjTransposeMat Q
  have hQA : specNorm Qbᴴ * specNorm A ≤ (1 + e) * R := by
    rw [specNorm_conjTranspose]; exact mul_le_mul hQ hAR hA0 (by linarith)
  have hm1 := hM.specNorm_mul_sub_decodeMatrix_mm_le (M.conjTransposeMat Q) As
    (by rw [hQH]; linarith)
  rw [hQH, ← hAdef, show max r (max k k) = k by omega] at hm1
  set C1 := decodeMatrix dec (M.mm (M.conjTransposeMat Q) As) with hC1def
  have hd1 : specNorm (Qbᴴ * A - C1) ≤ β / 2 * (134 / 100 * R) :=
    hm1.trans ((mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hμu0).trans
      (mul_le_mul_of_nonneg_right hμ (by linarith)))
  have hC1 : specNorm C1 ≤ 1003 / 1000 * R := by
    rw [show C1 = Qbᴴ * A - (Qbᴴ * A - C1) by abel]
    refine (specNorm_sub_le _ _).trans ?_
    linarith [(specNorm_mul_le Qbᴴ A).trans hQA]
  -- the second product
  have hC1Q : specNorm C1 * specNorm Qb ≤ 1006 / 1000 * R := by
    have := mul_le_mul hC1 hQ hQ0 (by linarith)
    have h2 : 1003 / 1000 * R * (1 + e) ≤ 1003 / 1000 * R * (1002 / 1000) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hm2 := hM.specNorm_mul_sub_decodeMatrix_mm_le (M.mm (M.conjTransposeMat Q) As) Q
    (by rw [← hC1def]; linarith)
  rw [← hC1def, ← hQbdef, show max r (max k r) = k by omega] at hm2
  set C2 := decodeMatrix dec (M.mm (M.mm (M.conjTransposeMat Q) As) Q)
  have hd2 : specNorm (C1 * Qb - C2) ≤ β / 2 * (134 / 100 * R) :=
    hm2.trans ((mul_le_mul_of_nonneg_left (max_le (by linarith) (by linarith)) hμu0).trans
      (mul_le_mul_of_nonneg_right hμ (by linarith)))
  -- the exact compression
  have hHQ := specNorm_conjTranspose_mul_mul_sub_le hAR (hV.mul hW).specNorm_le_one he
  rw [show (V * W)ᴴ * A * (V * W) - C2 = ((V * W)ᴴ * A * (V * W) - Qbᴴ * A * Qb) +
    (Qbᴴ * A - C1) * Qb + (C1 * Qb - C2) by rw [Matrix.sub_mul]; abel]
  have h3 := specNorm_add_le ((V * W)ᴴ * A * (V * W) - Qbᴴ * A * Qb + (Qbᴴ * A - C1) * Qb)
    (C1 * Qb - C2)
  have h4 := specNorm_add_le ((V * W)ᴴ * A * (V * W) - Qbᴴ * A * Qb) ((Qbᴴ * A - C1) * Qb)
  have h1 := (specNorm_mul_le (Qbᴴ * A - C1) Qb).trans (mul_le_mul hd1 hQ hQ0 (by positivity))
  have : β / 2 * (134 / 100 * R) * (1 + e) ≤ β / 2 * (134 / 100 * R) * (1 + 1 / 500) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- The stored compression of a deflated basis near `V W`. -/
private theorem FloatMachine.IsAccurate.specNorm_decodeMatrix_compress_sub_le {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k r : ℕ} (hk1 : 1 ≤ k) (hrk : r ≤ k) {β η R : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ β / 1000) (hμ0 : 0 ≤ μM k) (hμ : μM k * u ≤ β / 2)
    (hsk : √(k : ℝ) * u ≤ β / 4) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 115200) (hβη : β ≤ η / 8)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 800)
    (hR0 : 0 < R) (hτ0 : 0 ≤ τ) (hkτ : 3 * k * τ ≤ R) (hΩ : 4 * R ≤ Ω)
    {As : Matrix (Fin k) (Fin k) (F × F)} (hAh : (decodeMatrix dec As).IsHermitian)
    (hAR : specNorm (decodeMatrix dec As) ≤ R)
    {Q : Matrix (Fin k) (Fin r) (F × F)} {V : Matrix (Fin k) (Fin r) ℂ}
    {W : Matrix (Fin r) (Fin r) ℂ} (hV : HasOrthonormalCols V) (hW : HasOrthonormalCols W)
    (he : specNorm (V * W - decodeMatrix dec Q) ≤ 17 / 20 * η)
    {two s : F} (htwo : |dec two - 2| ≤ 3 * u) (hs : |dec s| ≤ R) :
    specNorm (decodeMatrix dec
        (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat Q) As) Q) two) s) -
      (Wᴴ * (Vᴴ * decodeMatrix dec As * V) * W - dec s • (1 : Matrix (Fin r) (Fin r) ℂ))) ≤
        (2 + 2 * η) * R * η := by
  have hP1 := hM.specNorm_compress_sub_decodeMatrix_mm_le hk1 hrk hu0 hμ0 hμ hβ0 hβ1
    (by positivity) (by linarith) hR0 hτ0 hkτ hΩ hAR hV hW he
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hrk' : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hsr : √(r : ℝ) * u ≤ β / 4 := by
    linarith [mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hrk') hu0]
  have hHh : ((V * W)ᴴ * decodeMatrix dec As * (V * W))ᴴ =
      (V * W)ᴴ * decodeMatrix dec As * (V * W) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hAh.eq,
      Matrix.mul_assoc]
  have hZ1 : specNorm (V * W) ≤ 1 := (hV.mul hW).specNorm_le_one
  have hH : specNorm ((V * W)ᴴ * decodeMatrix dec As * (V * W)) ≤ R :=
    (specNorm_mul_le _ _).trans ((mul_le_mul ((specNorm_mul_le _ _).trans
      ((mul_le_mul (by rw [specNorm_conjTranspose]; exact hZ1) hAR (specNorm_nonneg _)
        zero_le_one).trans (one_mul R).le)) hZ1 (specNorm_nonneg _) hR0.le).trans (mul_one R).le)
  have h4 : R * η * η ≤ R * η * (1 / 800) := mul_le_mul_of_nonneg_left hη1 (by positivity)
  have h5 : R * η ≤ R * (1 / 800) := mul_le_mul_of_nonneg_left hη1 hR0.le
  have hP2 := hM.specNorm_decodeMatrix_hermShift_hermAvg_sub_le hu0 (by linarith) hβ1 hR0 hτ0
    (by linarith [mul_le_mul_of_nonneg_right hk1' hτ0])
    (by linarith [mul_le_mul_of_nonneg_right hrk' hτ0]) hsr hΩ hHh hH hP1
    (by nlinarith [mul_le_mul_of_nonneg_right hβ1 hR0.le]) htwo hs
  rw [show Wᴴ * (Vᴴ * decodeMatrix dec As * V) * W = (V * W)ᴴ * decodeMatrix dec As * (V * W) by
    rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]]
  refine hP2.trans ?_
  have h3 : β * R ≤ η / 8 * R := mul_le_mul_of_nonneg_right hβη hR0.le
  have h6 : 0 ≤ R * η * η := by positivity
  have huR : u * R ≤ β / 1000 * R := mul_le_mul_of_nonneg_right hu1 hR0.le
  have huR0 : 0 ≤ u * R := mul_nonneg hu0 hR0.le
  nlinarith

/-- Deflation of a true spectral projector `V Vᴴ` through a stored approximation, on Event II:
`FloatMachine.IsArithAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le`
with $\mathbf{S} = \mathbf{I}_r$, for $2t\beta/x \le \eta \le 1/800$. -/
private theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_deflate_le_of_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β t x η : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hr0 : 0 < r) (hr : r ≤ n)
    (hμM : 0 ≤ μM n) (hu₀ : 0 ≤ u)
    {V : Matrix (Fin n) (Fin r) ℂ} (hV : HasOrthonormalCols V) {P : Matrix (Fin n) (Fin n) (F × F)}
    (hP : specNorm (V * Vᴴ - decodeMatrix dec P) ≤ β) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 115200)
    {G : Matrix (Fin n) (Fin n) ℂ} (hGt : specNorm G < t) (hx : 0 < x)
    (hσ : x < singularValues (Vᴴ * G.submatrix id (Fin.castLE hr)) (r - 1))
    (htx : 2 * t / x * β ≤ η) (hη : η ≤ 1 / 800)
    (hu : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β) (hτ0 : 0 ≤ τ)
    (hτ : τ * √(n : ℝ) ≤ x) (hΩ : 16 * t ≤ Ω) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (V * W - decodeMatrix dec (deflate M r P G)) ≤ 17 / 20 * η := by
  set B := Vᴴ * G.submatrix id (Fin.castLE hr)
  obtain ⟨hGu, hinv⟩ := isUnit_and_specNorm_inv_le_of_forall_mul_norm_le hx fun z =>
    (mul_le_mul_of_nonneg_right hσ.le (norm_nonneg _)).trans
      (singularValues_last_mul_norm_le B (k := r - 1) (by rw [Fintype.card_fin]; omega) z)
  have hVn : specNorm Vᴴ ≤ 1 := by rw [specNorm_conjTranspose]; exact hV.specNorm_le_one
  have hMG : specNorm B ≤ specNorm G :=
    (specNorm_mul_le _ _).trans ((mul_le_mul hVn (specNorm_submatrix_le G Function.injective_id
      (Fin.castLE_injective hr)) (specNorm_nonneg _) zero_le_one).trans (one_mul _).le)
  have hxG : x ≤ specNorm G := hσ.le.trans ((singularValues_le_specNorm _ _).trans hMG)
  have hn1 : (1 : ℝ) ≤ √(n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ n))
  have : Nonempty (Fin r) := ⟨⟨0, hr0⟩⟩
  have hS1 : specNorm (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := specNorm_one
  have hG0 := specNorm_nonneg G
  have ht0 : 0 < t := lt_of_le_of_lt hG0 hGt
  have hη0 : 0 ≤ η := le_trans (by positivity) htx
  have htxβ : t / x * β ≤ η / 2 := by
    have : 2 * t / x * β = 2 * (t / x * β) := by ring
    linarith
  have hmval : (1 + 2 * β + specNorm (1 : Matrix (Fin r) (Fin r) ℂ) / 8) *
      specNorm (1 : Matrix (Fin r) (Fin r) ℂ)⁻¹ * specNorm G * specNorm B⁻¹ ≤
        (9 / 8 + 2 * β) * (t / x) := by
    rw [inv_one, hS1, mul_one]
    calc (1 + 2 * β + 1 / 8) * specNorm G * specNorm B⁻¹ ≤ (1 + 2 * β + 1 / 8) * t * (1 / x) := by
          gcongr
      _ = (9 / 8 + 2 * β) * (t / x) := by ring
  have hmβ : (9 / 8 + 2 * β) * (t / x) * β ≤ (9 / 8 + 2 * β) * (η / 2) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left htxβ (by linarith)
  have hmβ' := (mul_le_mul_of_nonneg_right hmval hβ0).trans hmβ
  have hu' : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β := hu
  obtain ⟨W, hW, hWb⟩ := hM.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le
    hM.isQRErr hM.isNormalSampler hμM hu₀ hr hV hV isUnit_one (by rw [Matrix.mul_one]) hP hGu rfl
    (hmβ'.trans (by nlinarith)) hu'
    (by rw [hS1, one_mul]; nlinarith) (hτ.trans hxG) (by rw [hS1]; nlinarith) (by linarith)
  refine ⟨W, hW, hWb.trans ?_⟩
  change 3 / 2 * ((1 + 2 * β + specNorm (1 : Matrix (Fin r) (Fin r) ℂ) / 8) *
    specNorm (1 : Matrix (Fin r) (Fin r) ℂ)⁻¹ * specNorm G * specNorm B⁻¹) * β ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hβ1 hη0]

/-- One side of a split under a node budget: the frame `V` of a true spectral projector, through
the deflation of the stored projector (Event II) and the compression of the node's matrix. -/
private theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_deflate_compress_le_of_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {k r : ℕ} (hk1 : 1 ≤ k) (hr0 : 0 < r) (hrk : r ≤ k)
    {β η R t x : ℝ} (hμM : 0 ≤ μM k) (hu : 0 ≤ u) (huβ : u ≤ β / 1000) (hμ : μM k * u ≤ β / 2)
    (hsk : √(k : ℝ) * u ≤ β / 4) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 115200) (hβη : β ≤ η / 8)
    (hη0 : 0 < η) (hη1 : η ≤ 1 / 800) (hR0 : 0 < R) (hτ₀ : 0 ≤ τ) (hkτ : 3 * k * τ ≤ R)
    (hΩ : 4 * R ≤ Ω) (hx : 0 < x) (htx : 2 * t / x * β ≤ η)
    (hdefl : 16 * (4 * μQ k + 4 * √(k : ℝ) * cN + 2 * μM k) * u ≤ β) (hτx : τ * √(k : ℝ) ≤ x)
    (hΩt : 16 * t ≤ Ω) {As : Matrix (Fin k) (Fin k) (F × F)}
    (hAh : (decodeMatrix dec As).IsHermitian) (hAR : specNorm (decodeMatrix dec As) ≤ R)
    {two : F} (htwo : |dec two - 2| ≤ 3 * u) {V : Matrix (Fin k) (Fin r) ℂ}
    (hV : HasOrthonormalCols V) {P : Matrix (Fin k) (Fin k) (F × F)}
    (hP : specNorm (V * Vᴴ - decodeMatrix dec P) ≤ β) {G : Matrix (Fin k) (Fin k) ℂ}
    (hGt : specNorm G < t)
    (hσ : x < singularValues (Vᴴ * G.submatrix id (Fin.castLE hrk)) (r - 1))
    {s : F} (hs : |dec s| ≤ R) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (V * W - decodeMatrix dec (deflate M r P G)) ≤ η ∧
      specNorm (decodeMatrix dec (M.hermShift (M.hermAvg (M.mm (M.mm (M.conjTransposeMat
        (deflate M r P G)) As) (deflate M r P G)) two) s) -
        (Wᴴ * (Vᴴ * decodeMatrix dec As * V) * W - dec s • (1 : Matrix (Fin r) (Fin r) ℂ))) ≤
          (2 + 2 * η) * R * η := by
  obtain ⟨W, hW, hWb⟩ := hM.exists_hasOrthonormalCols_specNorm_sub_deflate_le_of_mul_le hr0 hrk
    hμM hu hV hP hβ0 hβ1 hGt hx hσ htx hη1 hdefl hτ₀ hτx hΩt
  exact ⟨W, hW, hWb.trans (by linarith), hM.specNorm_decodeMatrix_compress_sub_le hk1 hrk hu huβ
    hμM hμ hsk hβ0 hβ1 hβη hη0 hη1 hR0 hτ₀ hkτ hΩ hAh hAR hV hW hWb htwo hs⟩

/-- The roundoff budget of a node from the stopping condition of
`NLAlib.FloatMachine.IsEighNodeBudget`. -/
private theorem FloatMachine.IsEighNodeBudget.le_of_stop_tol
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk2 : 2 ≤ y.k) :
    u ≤ dec β / 1000 ∧ μM y.k * u ≤ dec β / 2 ∧ √(y.k : ℝ) * u ≤ dec β / 4 ∧
      dec β ≤ 1 / 115200 ∧ (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 := by
  have hk2' : (2 : ℝ) ≤ y.k := by exact_mod_cast hk2
  have hsqk : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hsk2 : √(y.k : ℝ) * √(y.k : ℝ) = y.k := Real.mul_self_sqrt (by linarith)
  have hsqk' : √(y.k : ℝ) ≤ y.k := by nlinarith
  have hR0 : 0 < dec y.R := hB.pos_w.trans_le hB.w_le
  have hu := hB.nonneg_u
  have hμM := hB.nonneg_μM
  have hβ := hB.pos_β
  -- the stopping condition
  set ν := 4 * μM y.k + 10 + 10 * √(y.k : ℝ) with hν
  have hνu : 0 ≤ ν * u := mul_nonneg (by positivity) hu
  have hkβ := hB.mul_β_le
  have hβ1 : dec β ≤ 1 / 115200 := by nlinarith
  have hstop := hB.mul_le_dec_β (by omega)
  have hkνu : 2048 * (y.k * (ν * u)) ≤ dec β := by linarith
  have hνu3 : 2048 * 3 * (ν * u) ≤ dec β := by
    linarith [mul_le_mul_of_nonneg_right (by linarith : (3 : ℝ) ≤ y.k + 1) hνu]
  have hνe : ν * u = 4 * (μM y.k * u) + 10 * u + 10 * (√(y.k : ℝ) * u) := by rw [hν]; ring
  have hμu := mul_nonneg hμM hu
  have hsu := mul_le_mul_of_nonneg_right hsqk hu
  have hu1β : u ≤ dec β / 1000 := by linarith
  have hμ : μM y.k * u ≤ dec β / 2 := by linarith
  have hsk : √(y.k : ℝ) * u ≤ dec β / 4 := by linarith
  have hkνe : y.k * (ν * u) = 4 * (y.k * (μM y.k * u)) + 10 * (y.k * u) +
      10 * (y.k * √(y.k : ℝ) * u) := by rw [hν]; ring
  have hk3u : y.k * √(y.k : ℝ) * u ≤ dec β / 20480 := by
    have : 0 ≤ (y.k : ℝ) * (μM y.k * u) := by positivity
    have : 0 ≤ (y.k : ℝ) * u := by positivity
    linarith
  have hk2u : (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 := by
    have h1 : (y.k : ℝ) ^ 2 * u = √(y.k : ℝ) * (y.k * √(y.k : ℝ) * u) := by
      rw [show √(y.k : ℝ) * (y.k * √(y.k : ℝ) * u) = y.k * (√(y.k : ℝ) * √(y.k : ℝ)) * u by ring,
        hsk2]
      ring
    have h2 := mul_le_mul_of_nonneg_right hsqk' (by positivity : 0 ≤ y.k * √(y.k : ℝ) * u)
    have h3 := mul_le_mul_of_nonneg_left hk3u (by positivity : (0 : ℝ) ≤ y.k)
    linarith
  exact ⟨hu1β, hμ, hsk, hβ1, hk2u⟩

/-- The scalar budget of a split node under `NLAlib.FloatMachine.IsEighNodeBudget`. -/
private theorem FloatMachine.IsEighNodeBudget.split_numerics
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y) (hk2 : 2 ≤ y.k)
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) (hint : M.le y.R (M.mul y.ε R₀) = false) :
    u ≤ 1 / 1000 ∧ τ ≤ 1 / 8 ∧ 6 * τ ≤ dec y.R ∧ 3 * y.k * τ ≤ dec y.R ∧ 2 ≤ Ω ∧
      4 * dec y.R ≤ Ω ∧ μM y.k * u ≤ dec β / 2 ∧ √(y.k : ℝ) * u ≤ dec β / 4 ∧
      u ≤ dec β / 1000 ∧ dec β ≤ 1 / 115200 ∧
      dec β ≤ (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) / 8 ∧
      0 < (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ∧
      (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) ≤ 1 / 800 ∧
      (y.k : ℝ) ^ 2 * u ≤ 1 / 100000 ∧ (y.k : ℝ) * τ ≤ 1 / 4 ∧ 16 * (y.k : ℝ) ≤ Ω ∧
      τ * √(y.k : ℝ) ≤ x ∧
      16 * (4 * μQ y.k + 4 * √(y.k : ℝ) * cN + 2 * μM y.k) * u ≤ dec β ∧ 16 * t ≤ Ω := by
  have hk2' : (2 : ℝ) ≤ y.k := by exact_mod_cast hk2
  have hℓ' : (20 : ℝ) ≤ y.ℓ := by exact_mod_cast hB.twenty_le
  have hsqk : 1 ≤ √(y.k : ℝ) := Real.one_le_sqrt.mpr (by linarith)
  have hR0 : 0 < dec y.R := hB.pos_w.trans_le hB.w_le
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hβ := hB.pos_β
  obtain ⟨hu1β, hμ, hsk, hβ1, hk2u⟩ := hB.le_of_stop_tol hk2
  -- the norm threshold
  have ht4 : 4 ≤ t := by
    have h2 : √2 * √(y.k : ℝ) = √(2 * y.k) := (Real.sqrt_mul (by norm_num) _).symm
    have h4 : (2 : ℝ) ≤ √(2 * y.k) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
    have := hB.le_t
    rw [mul_assoc, h2] at this
    linarith
  have hΩ := hB.Ω_le
  have hR₀ := hB.pos_R₀
  have hRlt := hM.mul_sub_lt_of_le_eq_false hu hτ₀ hB.pos_ε.le hR₀.le
    (by linarith [mul_le_mul_of_nonneg_right hB.ε_le hR₀.le]) hint
  -- the floor and the range
  have hτ := hB.τ_le
  have hτx : τ * (4 * y.k * √(y.k : ℝ)) ≤ x := hτ.trans (min_le_left _ _)
  have hτε : τ * (4 * y.k * √(y.k : ℝ)) ≤ dec y.ε * dec R₀ := hτ.trans (min_le_right _ _)
  have hkτ4 : 4 * y.k * τ ≤ τ * (4 * y.k * √(y.k : ℝ)) := by
    linarith [mul_le_mul_of_nonneg_left hsqk (by positivity : (0 : ℝ) ≤ 4 * y.k * τ)]
  have hτk : τ * √(y.k : ℝ) ≤ τ * (4 * y.k * √(y.k : ℝ)) := by
    linarith [mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 4 * y.k)
      (mul_nonneg hτ₀ (Real.sqrt_nonneg (y.k : ℝ)))]
  have hx1 := hB.x_le
  have hkτ : (y.k : ℝ) * τ ≤ 1 / 4 := by linarith
  have h2τ := mul_le_mul_of_nonneg_right hk2' hτ₀
  have hτ1 : τ ≤ 1 / 8 := by linarith
  have hu1 : u ≤ 1 / 1000 := by linarith
  have hkτR : 3 * y.k * τ ≤ dec y.R := by
    linarith [mul_le_mul_of_nonneg_left (hkτ4.trans hτε) (by linarith : (0 : ℝ) ≤ 1 - u),
      mul_le_mul_of_nonneg_right hu1 hτ₀,
      mul_le_mul_of_nonneg_right hu1 (by positivity : (0 : ℝ) ≤ y.k * τ)]
  -- the tolerance
  have hε := hB.pos_ε
  have hε₁ := hB.ε_le
  set η := (1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ) with hηdef
  have hℓinv : 1 / (y.ℓ : ℝ) ≤ 1 / 20 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hℓinv0 : 0 < 1 / (y.ℓ : ℝ) := by positivity
  have hη0 : 0 < η := div_pos (mul_pos (by linarith) hε) (by linarith)
  have hη1 : η ≤ 1 / 800 := by
    rw [hηdef, div_le_iff₀ (by linarith)]
    linarith [mul_nonneg hℓinv0.le hε.le]
  have hx := hB.pos_x
  have htx : t ≤ t / x := by
    rw [le_div_iff₀ hx]; exact mul_le_of_le_one_right (by linarith) hx1
  have hβη : dec β ≤ η / 8 := by
    have h := hB.defl_tol
    have : 2 * 4 * dec β ≤ 2 * t / x * dec β := by
      rw [mul_div_assoc]; gcongr; linarith
    linarith
  have hdefl := hB.defl_u
  have hcN := hB.nonneg_cN
  refine ⟨hu1, hτ1, by linarith, hkτR, by linarith, by linarith, hμ, hsk, hu1β, hβ1, hβη, hη0,
    hη1, hk2u, hkτ, by linarith, by linarith, ?_, by linarith⟩
  linarith [mul_nonneg (Real.sqrt_nonneg (y.k : ℝ)) hu]

/-- **A split node under a node budget**: with budget `NLAlib.FloatMachine.IsEighNodeBudget` and a
good sample
(`NLAlib.IsEighGoodSample` with parameters $(w, x, t)$), a split gives frames $\mathbf{V}_\pm$,
unitaries $\mathbf{W}_\pm$ with $\|\mathbf{V}_\pm\mathbf{W}_\pm - \mathbf{Q}_\pm\|_2 \le \eta =
(1 - 1/\ell)\varepsilon/(5\ell)$ and children within $(2 + 2\eta)R\eta$ of the shifted
compressions. [Shah2024, proof of Lemma 4.1]. -/
theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_sub_le_of_isEighNodeBudget
    (hM : M.IsAccurate dec u τ Ω μM μQ cN)
    (hB : M.IsEighNodeBudget dec u τ Ω μM μQ cN R₀ β signFuel w x t y)
    {smp : EighSample ℝ ℂ N}
    (hgood : 2 ≤ y.k → M.le y.R (M.mul y.ε R₀) = false → IsEighGoodSample dec w x t y smp)
    {kp : ℕ} {hkp : kp ≤ y.k} {Qp : Matrix (Fin y.k) (Fin kp) (F × F)}
    {Qm : Matrix (Fin y.k) (Fin (y.k - kp)) (F × F)} {Ap : Matrix (Fin kp) (Fin kp) (F × F)}
    {Am : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) (F × F)} {σ : F}
    (hsplit : eighStep M N signFuel R₀ β y.A y.R y.ε y.ℓ smp = .split kp hkp Qp Qm Ap Am σ) :
    |dec σ - dec y.R / 2| ≤ 3 * u * (dec y.R / 2) ∧
    (∃ V : Matrix (Fin y.k) (Fin kp) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 + cfc Real.sign (decodeMatrix dec y.A -
          (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))) ∧
      spectrum ℝ (Vᴴ * decodeMatrix dec y.A * V) ⊆ Set.Icc (dec y.R / y.ℓ * smp.1) (dec y.R) ∧
      ∃ W : Matrix (Fin kp) (Fin kp) ℂ, HasOrthonormalCols W ∧
        specNorm (V * W - decodeMatrix dec Qp) ≤ ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)) ∧
        specNorm (decodeMatrix dec Ap - (Wᴴ * (Vᴴ * decodeMatrix dec y.A * V) * W -
          dec σ • (1 : Matrix (Fin kp) (Fin kp) ℂ))) ≤
            (2 + 2 * ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) * dec y.R *
              ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) ∧
    (∃ V : Matrix (Fin y.k) (Fin (y.k - kp)) ℂ, HasOrthonormalCols V ∧
      V * Vᴴ = (2⁻¹ : ℝ) • (1 - cfc Real.sign (decodeMatrix dec y.A -
          (dec y.R / y.ℓ * smp.1) • (1 : Matrix (Fin y.k) (Fin y.k) ℂ))) ∧
      spectrum ℝ (Vᴴ * decodeMatrix dec y.A * V) ⊆ Set.Icc (-dec y.R) (dec y.R / y.ℓ * smp.1) ∧
      ∃ W : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) ℂ, HasOrthonormalCols W ∧
        specNorm (V * W - decodeMatrix dec Qm) ≤ ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ)) ∧
        specNorm (decodeMatrix dec Am - (Wᴴ * (Vᴴ * decodeMatrix dec y.A * V) * W +
          dec σ • (1 : Matrix (Fin (y.k - kp)) (Fin (y.k - kp)) ℂ))) ≤
            (2 + 2 * ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) * dec y.R *
              ((1 - 1 / (y.ℓ : ℝ)) * dec y.ε / (5 * y.ℓ))) := by
  obtain ⟨hk2, hint⟩ := two_le_and_le_eq_false_of_eighStep_eq_split hsplit
  obtain ⟨⟨hv, hI⟩, hII⟩ := hgood hk2 hint
  have hR0 : 0 < dec y.R := hB.pos_w.trans_le hB.w_le
  have hu := hB.nonneg_u
  have hτ₀ := hB.nonneg_τ
  have hk1 : (1 : ℝ) ≤ y.k := by exact_mod_cast (by omega : 1 ≤ y.k)
  obtain ⟨hu1, hτ1, hτR6, hkτR, hΩ2, hΩ4, hμ, hsk, huβ, hβ1, hβη, hη0, hη1, hk2u, hkτ, hΩk,
    hτx, hdefl, hΩt⟩ := hB.split_numerics hk2 hM hint
  -- the shift
  have hσ := hM.abs_dec_div_ofNat_two_sub_le hu (by linarith) hτ₀ hτ1 hτR6 hΩ2 (by linarith)
  have hhalf : |dec (M.div y.R (M.ofNat 2))| ≤ dec y.R := by
    have h1 := abs_sub_abs_le_abs_sub (dec (M.div y.R (M.ofNat 2))) (dec y.R / 2)
    rw [abs_of_pos (by linarith : 0 < dec y.R / 2)] at h1
    linarith [mul_le_mul_of_nonneg_right hu1 hR0.le]
  have htwo : |dec (M.ofNat 2) - 2| ≤ 3 * u := by
    have h := abs_sub_le_of_isRoundingOf (hM.ofNat 2) (by push_cast; rw [abs_two]; exact hΩ2) hu
      hτ₀
    push_cast at h
    rw [abs_two, abs_sub_comm] at h
    linarith [mul_le_mul_of_nonneg_left (by linarith : τ ≤ 1) hu]
  -- Event I: the ideal shift is not an eigenvalue
  have hc : ∀ x ∈ spectrum ℝ (decodeMatrix dec y.A), x ≠ dec y.R / y.ℓ * smp.1 :=
    fun x hx hxc => by have := hI x hx; rw [hxc, sub_self, abs_zero] at this; linarith [hB.pos_w]
  obtain ⟨hPp, hPm⟩ :=
    hM.specNorm_sub_decodeMatrix_eighProjectors_le_of_isEighNodeBudget hB hint hv hI
  have hkpr := hM.min_toNat_eq_inertiaPos_of_isEighNodeBudget hB hk2 hint hv hI
  -- unfold the step
  unfold eighStep at hsplit
  rw [if_neg (by omega), if_neg (by simp [hint])] at hsplit
  dsimp only at hsplit
  split_ifs at hsplit with h1 h2
  cases hsplit
  refine ⟨hσ, ?_, ?_⟩
  · -- the positive side
    obtain ⟨V, hV, hVV, hsp⟩ := exists_frame_pos hB.isHermitian hB.specNorm_le hc hkpr.symm
    have hr0 := Nat.pos_of_ne_zero h2
    have hrk := lt_of_le_of_ne (min_le_left _ _) h1
    obtain ⟨hGt, hσG⟩ := hII true _ V hr0 hrk hV (by rw [if_pos rfl, one_smul]; exact hVV)
    rw [specNorm_sub_comm, ← hVV] at hPp
    exact ⟨V, hV, hVV, hsp, hM.exists_hasOrthonormalCols_deflate_compress_le_of_mul_le (by omega)
      hr0 hrk.le hB.nonneg_μM hu huβ hμ hsk hB.pos_β.le hβ1 hβη hη0 hη1 hR0 hτ₀ hkτR hΩ4
      hB.pos_x hB.defl_tol hdefl hτx hΩt hB.isHermitian hB.specNorm_le htwo hV hPp hGt
      (hσG hrk.le) hhalf⟩
  · -- the negative side
    obtain ⟨V, hV, hVV, hsp⟩ := exists_frame_neg hB.isHermitian hB.specNorm_le hc hkpr.symm
      (min_le_left _ _)
    have hr0 := Nat.sub_pos_of_lt (lt_of_le_of_ne (min_le_left _ _) h1)
    have hrk : y.k - _ < y.k := Nat.sub_lt (by omega) (Nat.pos_of_ne_zero h2)
    obtain ⟨hGt, hσG⟩ := hII false _ V hr0 hrk hV
      (by rw [if_neg (by simp), neg_one_smul, ← sub_eq_add_neg]; exact hVV)
    rw [specNorm_sub_comm, ← hVV] at hPm
    obtain ⟨W, hW, hWb, hC⟩ := hM.exists_hasOrthonormalCols_deflate_compress_le_of_mul_le
      (by omega) hr0 hrk.le hB.nonneg_μM hu huβ hμ hsk hB.pos_β.le hβ1 hβη hη0 hη1 hR0 hτ₀
      hkτR hΩ4 hB.pos_x hB.defl_tol hdefl hτx hΩt hB.isHermitian hB.specNorm_le htwo hV hPm hGt
      (hσG hrk.le) (s := M.neg (M.div y.R (M.ofNat 2))) (by rw [hM.dec_neg, abs_neg]; exact hhalf)
    rw [hM.dec_neg, neg_smul, sub_neg_eq_add] at hC
    exact ⟨V, hV, hVV, hsp, W, hW, hWb, hC⟩

end NLAlib
