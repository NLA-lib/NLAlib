/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.QRIteration.StableStep

/-!
# Forward error of a backward-stable multishift step

A backward-stable degree $m$ step (`NLAlib.IsStableQRChain`) of an upper Hessenberg $\mathbf{H} =
\mathbf{V}\operatorname{diag}(\mathbf{e})\mathbf{V}^{-1}$, with shifts at distance at least $d$ from
the eigenvalues, is close in the Frobenius norm to the exact multishift step, up to a diagonal
unitary phase ([BanksGarzaVargasSrivastava2022, Lemma 3.8], with the factor $(2 + 2C)^{-m}$ added to
the precision hypothesis); and the potential after a step that is entrywise close to the exact step
on the last $k$ subdiagonals grows by at most a factor $1.0011$, unless one of those subdiagonals is
small ([BanksGarzaVargasSrivastava2022, Lemma 5.2], over the last $k$ subdiagonals).

## Main results

* `NLAlib.IsStableQRChain.exists_frobNorm_conj_sub_le`: the forward error of the step.
* `NLAlib.potential_le_or_exists_lt_of_sub_le`: the potential after a rounded step.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {n : ℕ}

/-- A unimodular phase: $\lvert p\rvert = 1$ gives $\bar p p = 1$. -/
private theorem star_mul_self_of_norm_eq_one {p : ℂ} (hp : ‖p‖ = 1) : star p * p = 1 := by
  rw [Complex.star_def, Complex.conj_mul', hp]
  norm_num

/-- A diagonal of unimodular entries is unitary. -/
private theorem hasOrthonormalCols_diagonal_of_norm_eq_one {p : Fin (n + 1) → ℂ}
    (hp : ∀ i, ‖p i‖ = 1) : HasOrthonormalCols (Matrix.diagonal p) := by
  rw [HasOrthonormalCols, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  exact congrArg _ (funext fun i => star_mul_self_of_norm_eq_one (hp i))

/-- The phases of the diagonal of a QR factorization of an invertible matrix: $p_i =
\mathbf{R}_{ii}/\lvert\mathbf{R}_{ii}\rvert$ has modulus one and $\bar p_i\mathbf{R}_{ii} > 0$. -/
private theorem IsQR.exists_phase_pos {A Q R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h : IsQR A Q R) (hA : IsUnit A) :
    ∃ p : Fin (n + 1) → ℂ, (∀ i, ‖p i‖ = 1) ∧
      ∀ i, 0 < (Matrix.diagonal (star p) * R) i i := by
  have hQ := h.hasOrthonormalCols
  have hQu : IsUnit Qᴴ :=
    ⟨⟨Qᴴ, Q, hQ.conjTranspose_mul_self, hQ.mul_conjTranspose_self⟩, rfl⟩
  have hR : ∀ i, R i i ≠ 0 := h.isUnit_iff.mp (by
    have := hQu.mul hA
    rwa [h.conjTranspose_mul_eq] at this)
  have hn : ∀ i, (‖R i i‖ : ℂ) ≠ 0 := fun i => by exact_mod_cast norm_ne_zero_iff.mpr (hR i)
  refine ⟨fun i => R i i / (‖R i i‖ : ℂ), fun i => ?_, fun i => ?_⟩
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.mpr
      (hR i))]
  · rw [Matrix.diagonal_mul, Pi.star_apply, star_div₀, Complex.star_def, Complex.conj_ofReal,
      div_mul_eq_mul_div, ← Complex.star_def, Complex.star_def, Complex.conj_mul',
      show ((‖R i i‖ : ℂ) ^ 2) / (‖R i i‖ : ℂ) = (‖R i i‖ : ℂ) by field_simp]
    exact Complex.zero_lt_real.mpr (norm_pos_iff.mpr (hR i))

/-- Two unitary conjugations of $\mathbf{H}$ differ by at most
$2\|\mathbf{H}\|_2\|\mathbf{Q}_2 - \mathbf{Q}_1\|_{\mathsf F}$ in the Frobenius norm. -/
private theorem frobNorm_conj_sub_conj_le {Q₁ Q₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h₁ : HasOrthonormalCols Q₁) (h₂ : HasOrthonormalCols Q₂)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    frobNorm (Q₂ᴴ * H * Q₂ - Q₁ᴴ * H * Q₁) ≤ 2 * specNorm H * frobNorm (Q₂ - Q₁) := by
  have e : Q₂ᴴ * H * Q₂ - Q₁ᴴ * H * Q₁ = (Q₂ - Q₁)ᴴ * (H * Q₂) + Q₁ᴴ * H * (Q₂ - Q₁) := by
    rw [Matrix.conjTranspose_sub]
    noncomm_ring
  have a : frobNorm ((Q₂ - Q₁)ᴴ * (H * Q₂)) ≤ specNorm H * frobNorm (Q₂ - Q₁) := by
    refine (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans_eq ?_
    rw [frobNorm_conjTranspose, h₂.specNorm_mul_right, mul_comm]
  have b : frobNorm (Q₁ᴴ * H * (Q₂ - Q₁)) ≤ specNorm H * frobNorm (Q₂ - Q₁) :=
    (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans
      (by gcongr; exact h₁.specNorm_conjTranspose_mul_le H)
  rw [e]
  linarith [frobNorm_add_le ((Q₂ - Q₁)ᴴ * (H * Q₂)) (Q₁ᴴ * H * (Q₂ - Q₁))]

/-- The scalar bound on the accumulated similarity error of Lemma 3.8: under $m x \le 1/4$,
$(1 + x)^m - 1 \le 2\kappa T x$ for $\kappa \ge 1$ and $T \ge 2^m$. -/
private theorem one_add_pow_sub_one_le_of_two_pow_le {x κ T : ℝ} {m : ℕ} (hx : 0 ≤ x) (hκ : 1 ≤ κ)
    (hmx : (m : ℝ) * x ≤ 1 / 4) (hT : 2 ^ m ≤ T) :
    (1 + x) ^ m - 1 ≤ 2 * κ * T * x := by
  have h1 := one_add_pow_mul_one_sub_le hx m
  have hm2 : (m : ℝ) + 1 ≤ 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
  have hp0 : 0 ≤ (1 + x) ^ m := pow_nonneg (by linarith) m
  have hmx0 : 0 ≤ (m : ℝ) * x := by positivity
  have hp : (1 + x) ^ m ≤ 4 / 3 := by nlinarith
  have hκT : 2 ^ m ≤ κ * T := by nlinarith [pow_pos (two_pos (α := ℝ)) m]
  calc (1 + x) ^ m - 1 ≤ (1 + x) ^ m * (m * x) := by nlinarith
    _ ≤ 4 / 3 * (m * x) := by gcongr
    _ ≤ 2 * 2 ^ m * x := by nlinarith
    _ ≤ 2 * κ * T * x := by nlinarith

/-- The scalar hypotheses of Lemma 3.8 give $2^m \le ((2 + 2C)\|\mathbf{H}\|_2/d)^m$ (a shift in
$\mathbb{D}(0, C\|\mathbf{H}\|_2)$ is within $(1 + C)\|\mathbf{H}\|_2$ of every eigenvalue) and
$m x \le 1/4$. -/
private theorem forward_scalar_bounds {x C κ d : ℝ} {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {e : Fin (n + 1) → ℂ} {ss : List ℂ} (hd : 0 < d) (hH : 0 < specNorm H) (hC : 0 ≤ C)
    (hκ1 : 1 ≤ κ) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖)
    (hu : x ≤ (16 * κ)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ ss.length) :
    (2 : ℝ) ^ ss.length ≤ ((2 + 2 * C) * specNorm H / d) ^ ss.length ∧
      (ss.length : ℝ) * x ≤ 1 / 4 := by
  set m := ss.length
  set Λ := (2 + 2 * C) * specNorm H
  have hL : 0 < Λ := by positivity
  have hT : (2 : ℝ) ^ m ≤ (Λ / d) ^ m := by
    rcases eq_or_ne ss [] with hss | hss
    · simp [m, hss]
    · obtain ⟨s, hs'⟩ := List.exists_mem_of_ne_nil ss hss
      have h1 := hdist s hs' 0
      have h2 := norm_le_specNorm_of_mul_eq_mul_diagonal hV hHV 0
      have h3 := norm_sub_le (e 0) s
      have h4 := hs s hs'
      refine pow_le_pow_left₀ (by norm_num) ?_ m
      rw [le_div_iff₀ hd]
      nlinarith
  refine ⟨hT, ?_⟩
  have hρ : (d / Λ) ^ m ≤ (1 / 2) ^ m := by
    rw [div_pow, one_div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    rw [div_pow, le_div_iff₀ (by positivity)] at hT
    linarith
  have hx' : x ≤ 16⁻¹ * (1 / 2) ^ m := by
    refine hu.trans ?_
    rw [mul_inv]
    calc 16⁻¹ * κ⁻¹ * (d / Λ) ^ m ≤ 16⁻¹ * 1 * (1 / 2) ^ m := by
          gcongr
          exact inv_le_one_of_one_le₀ hκ1
      _ = _ := by ring
  have h2m : (m : ℝ) * (1 / 2) ^ m ≤ 1 := by
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact_mod_cast Nat.lt_two_pow_self.le
  nlinarith [mul_le_mul_of_nonneg_left hx' (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- **Forward error from a perturbed factorization**: if $\mathbf{M} = \mathbf{Q}\mathbf{R}$ and
$\mathbf{M} - \mathbf{E} = \widehat{\mathbf{Q}}\widehat{\mathbf{R}}$ are QR factorizations with
$\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_2 \le 1/4$, a diagonal unitary $\mathbf{D}$ has
$\|\mathbf{D}^{\mathsf H}\mathbf{H}'\mathbf{D} - \mathbf{Q}^{\mathsf H}\mathbf{H}\mathbf{Q}
\|_{\mathsf F} \le \sqrt{n + 1}\,\|\mathbf{H}' - \widehat{\mathbf{Q}}^{\mathsf H}\mathbf{H}
\widehat{\mathbf{Q}}\|_2 + 16\sqrt{n + 1}\,\|\mathbf{H}\|_2\|\mathbf{M}^{-1}\|_2\|\mathbf{E}\|_2$:
the phases rescale both factorizations to positive diagonals, then
`NLAlib.IsQR.frobNorm_sub_le_of_add`. -/
private theorem exists_frobNorm_conj_sub_le_of_isQR
    {M E Q R Qh Rh H H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hMu : IsUnit M)
    (hQR : IsQR M Q R) (hQR' : IsQR (M + -E) Qh Rh) (hη : specNorm M⁻¹ * specNorm E ≤ 1 / 4) :
    ∃ D : Fin (n + 1) → ℂ, (∀ i, ‖D i‖ = 1) ∧
      frobNorm ((Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D - Qᴴ * H * Q) ≤
        Real.sqrt (n + 1) * specNorm (H' - Qhᴴ * H * Qh) +
          2 * specNorm H * (8 * specNorm M⁻¹ * (Real.sqrt (n + 1) * specNorm E)) := by
  have hMEu : IsUnit (M + -E) := isUnit_add_of_specNorm_inv_mul_specNorm_lt_one hMu
    (by rw [specNorm_neg]; linarith)
  obtain ⟨p, hp, hpR⟩ := hQR.exists_phase_pos hMu
  obtain ⟨p', hp', hpR'⟩ := hQR'.exists_phase_pos hMEu
  have hs1 : ∀ i, star (p i) * p i = 1 := fun i => star_mul_self_of_norm_eq_one (hp i)
  have hs2 : ∀ i, star (p' i) * p' i = 1 := fun i => star_mul_self_of_norm_eq_one (hp' i)
  have hQd := (hQR.mul_diagonal hs1).frobNorm_sub_le_of_add (hQR'.mul_diagonal hs2) hpR hpR'
    (by rw [specNorm_neg]; exact hη)
  -- the phase `D = p' p̄` matches the two unitary factors
  set D : Fin (n + 1) → ℂ := fun i => p' i * star (p i)
  have hDn : ∀ i, ‖D i‖ = 1 := fun i => by simp only [D, norm_mul, norm_star, hp, hp', mul_one]
  have hDo := hasOrthonormalCols_diagonal_of_norm_eq_one hDn
  have hPo := hasOrthonormalCols_diagonal_of_norm_eq_one (p := star p) fun i => by
    rw [Pi.star_apply, norm_star, hp]
  have eQ : Q = Q * Matrix.diagonal p * Matrix.diagonal (star p) := by
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, show (fun i => p i * star p i) = 1 from
      funext fun i => by rw [mul_comm]; exact hs1 i, Pi.one_def, Matrix.diagonal_one,
      Matrix.mul_one]
  have eQh : Qh * Matrix.diagonal D = Qh * Matrix.diagonal p' * Matrix.diagonal (star p) := by
    rw [Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    rfl
  set X := H' - Qhᴴ * H * Qh
  have hsplit : (Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D - Qᴴ * H * Q =
      (Matrix.diagonal D)ᴴ * X * Matrix.diagonal D +
        ((Qh * Matrix.diagonal D)ᴴ * H * (Qh * Matrix.diagonal D) - Qᴴ * H * Q) := by
    rw [Matrix.conjTranspose_mul]
    simp only [X]
    noncomm_ring
  have hN : Real.sqrt (Fintype.card (Fin (n + 1)) : ℝ) = Real.sqrt (n + 1) := by
    rw [Fintype.card_fin]; push_cast; rfl
  refine ⟨D, hDn, hsplit ▸ (frobNorm_add_le _ _).trans (add_le_add ?_ ?_)⟩
  · rw [hDo.frobNorm_mul_right, ← hN]
    refine (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans ?_
    rw [specNorm_conjTranspose]
    calc _ ≤ 1 * frobNorm X := by
          gcongr
          exact hDo.specNorm_le_one
      _ ≤ _ := by rw [one_mul]; exact frobNorm_le_sqrt_card_mul_specNorm X
  · rw [eQh, eQ]
    refine (frobNorm_conj_sub_conj_le ((hQR.mul_diagonal hs1).hasOrthonormalCols.mul hPo)
      ((hQR'.mul_diagonal hs2).hasOrthonormalCols.mul hPo) H).trans ?_
    rw [← Matrix.sub_mul, hPo.frobNorm_mul_right]
    gcongr
    refine hQd.trans ?_
    gcongr
    rw [← hN, ← specNorm_neg E]
    exact frobNorm_le_sqrt_card_mul_specNorm _

/-- **Forward error of a degree $m$ step** (corrected [BanksGarzaVargasSrivastava2022,
Lemma 3.8]): let $\mathbf{H}$ be upper Hessenberg, $\mathbf{H}\mathbf{V} = \mathbf{V}\mathbf{D}$
with $\kappa(\mathbf{V}) \le \kappa$, every shift at distance at least $d > 0$ from every
eigenvalue and in $\mathbb{D}(0, C\|\mathbf{H}\|_2)$, $\mathbf{H} \ne 0$, and
$x \le (16\kappa)^{-1}(d / ((2 + 2C)\|\mathbf{H}\|_2))^m$ (the paper's hypothesis lacks the factor
$(2 + 2C)^{-m}$). Then for a diagonal unitary $\mathbf{D}$ (the phase of the last diagonal entry
of the computed triangular factor; the paper compares with the positive-diagonal QR factor
directly), $\|\mathbf{D}^{\mathsf H}\widehat{\mathbf{H}}'\mathbf{D} - \mathbf{H}'\|_{\mathsf F} \le
(66 + 2C)\kappa\|\mathbf{H}\|_2((2 + 2C)\|\mathbf{H}\|_2 / d)^m\sqrt{n + 1}\,x$, where
$\mathbf{H}'$ is the exact multishift step. $64$ is the QR perturbation term with the loose
constant $8$ (`NLAlib.IsQR.frobNorm_sub_le_of_add`); $2 + 2C$ absorbs the accumulated similarity
error, which the paper's $33$ covers only when $d \le \|\mathbf{H}\|_2$ (false for large $C$:
$\mathbf{H} = -\mathbf{I}_2$, $s = 200$). The Hessenberg hypothesis is needed: Givens QR of a
matrix that is not Hessenberg is not a QR factorization, and a $3 \times 3$ counterexample
breaks the bound by a factor $1670$ without it. -/
theorem IsStableQRChain.exists_frobNorm_conj_sub_le {x C κ d : ℝ} {H H' V : Matrix (Fin (n + 1))
    (Fin (n + 1)) ℂ} {e : Fin (n + 1) → ℂ} {ss : List ℂ}
    {Rs : List (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)}
    (h : IsStableQRChain x H ss H' Rs) (hx : 0 ≤ x) (hC : 0 ≤ C) (hd : 0 < d) (hH0 : H ≠ 0)
    (hHess : IsUpperHessenberg H)
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal e) (hκ : pseudoConditionNumber V ≤ κ)
    (hs : ∀ s ∈ ss, ‖s‖ ≤ C * specNorm H) (hdist : ∀ s ∈ ss, ∀ i, d ≤ ‖e i - s‖)
    (hu : x ≤ (16 * κ)⁻¹ * (d / ((2 + 2 * C) * specNorm H)) ^ ss.length) :
    ∃ D : Fin (n + 1) → ℂ, (∀ i, ‖D i‖ = 1) ∧
      frobNorm ((Matrix.diagonal D)ᴴ * H' * Matrix.diagonal D - multiShiftedQRStep H ss) ≤
        (66 + 2 * C) * κ * specNorm H * ((2 + 2 * C) * specNorm H / d) ^ ss.length *
          Real.sqrt (n + 1) * x := by
  set m := ss.length
  set M := Polynomial.aeval H (shiftPoly ss)
  have hκ1 : 1 ≤ κ := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hH : 0 < specNorm H :=
    (specNorm_nonneg H).lt_of_ne fun h0 => hH0 (specNorm_eq_zero_iff.mp h0.symm)
  obtain ⟨hT, hmx⟩ := forward_scalar_bounds hd hH hC hκ1 hV hHV hs hdist hu
  set Λ := (2 + 2 * C) * specNorm H
  have hL : 0 < Λ := by positivity
  -- one unitary for both parts of the backward error
  obtain ⟨Qh, hQh, hE, hsim⟩ := h.exists_specNorm_aeval_sub_le_scale hx
    (mul_nonneg hC hH.le) hs hmx ((1 + C) * specNorm H) (by linarith)
  set Rh := Rs.reverse.prod
  set E := M - Qh * Rh
  obtain ⟨hMM, hMi⟩ := specNorm_inv_aeval_shiftPoly_le hd hV hHV hdist
  have hMu : IsUnit M :=
    (Matrix.isUnit_iff_isUnit_det M).mpr (Matrix.isUnit_det_of_right_inverse hMM)
  have hEb : specNorm E ≤ 4 * Λ ^ m * x := by
    refine hE.trans_eq ?_
    have e2 : Λ ^ ss.length = 2 ^ ss.length * ((1 + C) * specNorm H) ^ ss.length := by
      rw [← mul_pow]
      congr 1
      simp only [Λ]
      ring
    change _ = 4 * Λ ^ ss.length * x
    rw [e2]
    ring
  -- `‖M⁻¹‖ ‖E‖ ≤ 4 κ (Λ / d)^m x ≤ 1 / 4`
  have hηx : specNorm M⁻¹ * specNorm E ≤ 4 * κ * (Λ / d) ^ m * x := by
    calc _ ≤ κ / d ^ m * (4 * Λ ^ m * x) :=
          mul_le_mul (hMi.trans (by gcongr)) hEb (specNorm_nonneg _) (by positivity)
      _ = _ := by rw [div_pow]; ring
  have hη : specNorm M⁻¹ * specNorm E ≤ 1 / 4 := by
    refine hηx.trans ?_
    have hdm : (Λ / d) ^ m * (d / Λ) ^ m = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm Λ d, div_self (by positivity), one_pow]
    calc 4 * κ * (Λ / d) ^ m * x ≤ 4 * κ * (Λ / d) ^ m * ((16 * κ)⁻¹ * (d / Λ) ^ m) := by
          gcongr
      _ = 1 / 4 := by
          rw [mul_inv]
          field_simp
          nlinarith [hdm]
  -- compare with the exact step through the QR perturbation bound
  obtain ⟨Q, R, hQR, hstep⟩ := hHess.exists_isQR_aeval_shiftPoly ss
  have hU : Rh.IsUpperTriangular := (list_prod_isUpperTriangular_apply_self (L := Rs.reverse)
    (fun R hR => h.forall_isUpperTriangular R (List.mem_reverse.mp hR)) 0).1
  obtain ⟨D, hDn, hD⟩ := exists_frobNorm_conj_sub_le_of_isQR (H := H) (H' := H') hMu hQR
    (⟨by simp [E], hQh, hU⟩ : IsQR (M + -E) Qh Rh) hη
  refine ⟨D, hDn, hstep ▸ hD.trans ?_⟩
  have hX : specNorm (H' - Qhᴴ * H * Qh) ≤ (1 + C) * specNorm H * (2 * κ * (Λ / d) ^ m * x) :=
    hsim.trans (by gcongr; exact one_add_pow_sub_one_le_of_two_pow_le hx hκ1 hmx hT)
  have hs0 : 0 ≤ Real.sqrt (n + 1) := Real.sqrt_nonneg _
  have hHs := hH.le
  calc _ ≤ Real.sqrt (n + 1) * ((1 + C) * specNorm H * (2 * κ * (Λ / d) ^ m * x)) +
        2 * specNorm H * (8 * Real.sqrt (n + 1) * (4 * κ * (Λ / d) ^ m * x)) := by
        rw [show 2 * specNorm H * (8 * specNorm M⁻¹ * (Real.sqrt (n + 1) * specNorm E)) =
          2 * specNorm H * (8 * Real.sqrt (n + 1) * (specNorm M⁻¹ * specNorm E)) by ring]
        gcongr
    _ = _ := by ring

/-- **The potential after a rounded step** (corrected [BanksGarzaVargasSrivastava2022,
Lemma 5.2]): if the computed $\widehat{\mathbf{H}}'$ is within $0.001\omega$ of the exact step
$\mathbf{H}'$ entrywise on the last $k$ subdiagonals, then either one of those last $k$
subdiagonals of $\widehat{\mathbf{H}}'$ is below $\omega$, or
$\psi_k(\widehat{\mathbf{H}}') \le 1.0011\,\psi_k(\mathbf{H}')$. The paper takes the product and
the case split over all $n - 1$ subdiagonals; then the first alternative is not a decoupling of
the bottom block, and the factor is $1.001^{(n-1)/k}$. -/
theorem potential_le_or_exists_lt_of_sub_le {k : ℕ} (hk : 0 < k) {ω : ℝ} (hω : 0 < ω)
    {H₁ H₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hclose : ∀ i : Fin n, n ≤ (i : ℕ) + k →
      ‖H₁ i.succ i.castSucc - H₂ i.succ i.castSucc‖ ≤ 0.001 * ω) :
    (∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H₁ i.succ i.castSucc‖ < ω) ∨
      hessenbergPotential k H₁ ≤ 1.0011 * hessenbergPotential k H₂ := by
  by_cases hex : ∃ i : Fin n, n ≤ (i : ℕ) + k ∧ ‖H₁ i.succ i.castSucc‖ < ω
  · exact Or.inl hex
  right
  simp only [not_exists, not_and, not_lt] at hex
  set S := Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k) with hS
  have hent : ∀ i ∈ S, ‖H₁ i.succ i.castSucc‖ ≤ 1.0011 * ‖H₂ i.succ i.castSucc‖ := by
    intro i hi
    rw [hS, Finset.mem_filter] at hi
    have h1 := hex i hi.2
    have h2 := hclose i hi.2
    have h3 := norm_sub_norm_le (H₁ i.succ i.castSucc) (H₂ i.succ i.castSucc)
    linarith
  have hcard : S.card ≤ k := by
    have := Finset.card_le_card_of_injOn (fun i : Fin n => (i : ℕ) + k - n) (s := S)
      (t := Finset.range k)
      (by
        intro i hi
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
          Finset.mem_coe, Finset.mem_range] at hi ⊢
        have := i.isLt
        omega)
      (by
        intro i hi j hj hij
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq] at hi hj
        simp only at hij
        have := i.isLt
        have := j.isLt
        apply Fin.ext
        omega)
    simpa using this
  have hprod : ∏ i ∈ S, ‖H₁ i.succ i.castSucc‖ ≤ 1.0011 ^ k * ∏ i ∈ S, ‖H₂ i.succ i.castSucc‖ := by
    calc ∏ i ∈ S, ‖H₁ i.succ i.castSucc‖ ≤ ∏ i ∈ S, (1.0011 * ‖H₂ i.succ i.castSucc‖) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) hent
      _ = 1.0011 ^ S.card * ∏ i ∈ S, ‖H₂ i.succ i.castSucc‖ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ 1.0011 ^ k * ∏ i ∈ S, ‖H₂ i.succ i.castSucc‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard)
            (Finset.prod_nonneg fun i _ => norm_nonneg _)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold hessenbergPotential
  rw [← hS]
  calc (∏ i ∈ S, ‖H₁ i.succ i.castSucc‖) ^ ((k : ℝ)⁻¹)
      ≤ (1.0011 ^ k * ∏ i ∈ S, ‖H₂ i.succ i.castSucc‖) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Finset.prod_nonneg fun i _ => norm_nonneg _) hprod (by positivity)
    _ = 1.0011 * (∏ i ∈ S, ‖H₂ i.succ i.castSucc‖) ^ ((k : ℝ)⁻¹) := by
        rw [Real.mul_rpow (by positivity) (Finset.prod_nonneg fun i _ => norm_nonneg _),
          Real.pow_rpow_inv_natCast (by norm_num) hk.ne']

end NLAlib
