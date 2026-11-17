/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.Decouple
public import NLAlib.Eigensolvers.SmallEig.OneEig
public import NLAlib.Eigensolvers.SmallEig.Precision
public import NLAlib.Eigensolvers.SmallEig.RandomHessenberg

/-!
# The precision of the decoupler of the small-eigenvalue solver

The arithmetic of one node of the deflation of [BanksGarzaVargasSrivastava2025, §6] at the unit
roundoff $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$: the class after `RHess` (one
doubling of the condition, Lemma 6.2's class part), the precision conditions of `RHess`,
`OneEig` and `Decouple` unfolded from `NLAlib.SmallEig.uSmallEig`, and the backward error of the
node, `NLAlib.SmallEig.smallEigDecoupleError`.

## Main definitions

* `NLAlib.SmallEig.smallEigDecoupleError`: the backward error of the decoupler.

## Main results

* `NLAlib.SmallEig.class_of_rhess`: the class after `RHess`.
* `NLAlib.SmallEig.smallEigDecoupler_precision`,
  `NLAlib.SmallEig.smallEigDecoupler_rhess_precision`,
  `NLAlib.SmallEig.smallEigDecoupler_oneEig_precision`,
  `NLAlib.SmallEig.smallEigDecoupler_decouple_precision`: the precision of each block.
* `NLAlib.SmallEig.smallEigDecoupleError_le`,
  `NLAlib.SmallEig.smallEigDecoupler_decouple_conditions`: the error of the node and
  the side conditions of `Decouple`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

/-- The backward error of the decoupler on a block of norm at most $N$ at the unit roundoff
$\boldsymbol{u}$: `RHess`, $200(n_{\max} + 1)^2\boldsymbol{u}N$, and `Decouple` from a block of norm
at most $2N$ with the shift reach $10$,
$11 \cdot 2N((1 + 300(n_{\max} + 1)^2\boldsymbol{u})^{m_2} - 1)$. -/
noncomputable def smallEigDecoupleError (nmax : ℕ) (S δ φ : ℝ) (c₂ : PolyLogTail) (u N : ℝ) :
    ℝ :=
  200 * ((nmax : ℝ) + 1) ^ 2 * u * N +
    11 * (2 * N) * ((1 + 300 * ((nmax : ℝ) + 1) ^ 2 * u) ^ smallEigDecoupleSteps nmax S δ φ c₂ - 1)

/-- **The class after `RHess`** ([BanksGarzaVargasSrivastava2025, Lemma 6.2], the class part, as
the merged deflation's class doubling): if $\mathbf{A}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le 2B$,
eigenvalues separated by $g/2$, $g > 0$, $\mathbf{Q}$ unitary and
$\|\mathbf{H} - \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}\|_2 \le g/(64(n + 1)B)$, then
$\mathbf{H}$ has a diagonalization with condition at most $4B$ and eigenvalues separated by
$g/4$. -/
theorem class_of_rhess {n : ℕ} {A H Q V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} {B g : ℝ} (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ 2 * B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g / 2 ≤ ‖d i - d j‖) (hQ : HasOrthonormalCols Q)
    (hH : specNorm (H - Qᴴ * A * Q) ≤ g / (64 * (n + 1) * B)) :
    ∃ (V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d' : Fin (n + 1) → ℂ), IsUnit V' ∧
      H * V' = V' * Matrix.diagonal d' ∧ pseudoConditionNumber V' ≤ 4 * B ∧
      ∀ i j, i ≠ j → g / 4 ≤ ‖d' i - d' j‖ := by
  have hB : 0 < B := by
    have := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ; linarith
  obtain ⟨hV₀, hAV₀, hκ₀⟩ := hQ.isUnit_conjTranspose_mul_and_mul_eq_mul_diagonal hV hAV
  have hE : specNorm (H - Qᴴ * A * Q) ≤ g / 2 / (16 * (n + 1) * (2 * B)) := by
    convert hH using 1; field_simp; ring
  obtain ⟨V', d', hV', hHV', hκ', hgap'⟩ := exists_pseudoConditionNumber_le_and_le_norm_sub hV₀
    hAV₀ (hκ₀.trans_le hκ) (by positivity) hgap hE
  rw [add_sub_cancel] at hHV'
  refine ⟨V', d', hV', hHV', by linarith, fun i j hij => le_trans ?_ (hgap' i j hij)⟩
  have hn : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h1 : 2 * (2 * B) * specNorm (H - Qᴴ * A * Q) ≤ g / 16 := by
    calc 2 * (2 * B) * specNorm (H - Qᴴ * A * Q) ≤ 4 * B * (g / (64 * (n + 1) * B)) := by
          rw [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num]; gcongr
      _ = g / (16 * (n + 1)) := by field_simp; ring
      _ ≤ g / 16 := div_le_div_of_nonneg_left hg.le (by norm_num) (by linarith)
  linarith

/-! ### The precision bookkeeping of the decoupler -/

/-- $(1 + x)^m \le 2$ for $x \ge 0$ with $mx \le 1/2$. -/
theorem one_add_pow_le_two {x : ℝ} {m : ℕ} (hx : 0 ≤ x) (h : m * x ≤ 1 / 2) :
    (1 + x) ^ m ≤ 2 := by
  have he : Real.exp (1 / 2) ^ 2 < 4 := by
    rw [← Real.exp_nat_mul]; norm_num
    linarith [Real.exp_one_lt_d9]
  calc (1 + x) ^ m ≤ Real.exp x ^ m := by
        gcongr; linarith [Real.add_one_le_exp x]
    _ = Real.exp (m * x) := (Real.exp_nat_mul x m).symm
    _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr h
    _ ≤ 2 := by nlinarith [Real.exp_pos (1 / 2)]

/-- $(m + 1)r^m \le 1$ for $0 \le r \le 1/2$. -/
theorem succ_mul_pow_le_one {r : ℝ} (h0 : 0 ≤ r) (h : r ≤ 1 / 2) (m : ℕ) :
    ((m : ℝ) + 1) * r ^ m ≤ 1 := by
  have h2 : ((m : ℝ) + 1) ≤ 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
  calc ((m : ℝ) + 1) * r ^ m ≤ 2 ^ m * (1 / 2) ^ m := by gcongr
    _ = 1 := by rw [← mul_pow]; norm_num

/-- The terms of the precision threshold that the decoupler uses, unfolded: for tail records
with $b_1, b_2 > 0$, $n_{\max} \ge 1$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and
$\boldsymbol{u} \le$ `NLAlib.SmallEig.uSmallEig`, the counts, `RHess`, `DistSpec` and `Decouple`
terms. -/
theorem smallEigDecoupler_precision {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {nmax : ℕ} (hn : 1 ≤ nmax) {S δ φ u : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) :
    100000 * ((nmax : ℝ) + 1) ^ 2 * u ≤ 1 ∧
    1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S) * u ≤ smallEigSeparation nmax S δ φ c₁ / 2 /
      (64 * ((nmax : ℝ) + 1) * (2 * smallEigCondition nmax S δ φ c₂)) ∧
    1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S) * u ≤
      √(smallEigWeight nmax S δ φ c₂) * (smallEigSeparation nmax S δ φ c₁ / 2) /
        (1024 * ((nmax : ℝ) + 1) * (2 * smallEigCondition nmax S δ φ c₂) ^ 2) ∧
    30000 * ((2 : ℝ) ^ smallEigDegreeLog nmax S δ φ c₂ + 1) * u ≤ 1 ∧
    300 * ((nmax : ℝ) + 1) ^ 2 * u ≤ (8004 * (8 * smallEigCondition nmax S δ φ c₂))⁻¹ *
      (smallEigInnerRadius nmax S δ φ c₁ c₂ / (22 * (2 * S))) ^
        (2 ^ smallEigDegreeLog nmax S δ φ c₂) ∧
    300 * ((nmax : ℝ) + 1) ^ 2 * u ≤ (16 * (8 * smallEigCondition nmax S δ φ c₂))⁻¹ *
      (smallEigInnerRadius nmax S δ φ c₁ c₂ / (22 * (2 * S))) ^
        smallEigDecoupleSteps nmax S δ φ c₂ ∧
    300 * ((nmax : ℝ) + 1) ^ 2 * u ≤ smallEigOmega nmax S δ φ c₁ c₂ / 2 /
      (86 * (8 * smallEigCondition nmax S δ φ c₂) * (2 * S) *
        (22 * (2 * S) / smallEigInnerRadius nmax S δ φ c₁ c₂) ^
          smallEigDecoupleSteps nmax S δ φ c₂ * √((nmax : ℝ) + 1)) := by
  obtain ⟨-, h1, -, h3, h4, h5, -⟩ := uSmallEig_spec hb₁ hb₂ hn hδ hδS hφ hφ1
  have hS : 0 < S := hδ.trans_le hδS
  have hN : (0 : ℝ) < ((nmax : ℝ) + 1) ^ 2 := by positivity
  have a := hu.trans h1
  have b := hu.trans h3
  have c := hu.trans h4
  have d := hu.trans h5
  unfold uSmallEigBasic at a
  unfold uSmallEigRHess at b
  unfold uSmallEigDistSpec at c
  unfold uSmallEigDecouple at d
  rw [le_div_iff₀ (by positivity)] at b d
  have a2 := a.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at a2
  have c1 := c.trans (min_le_left _ _)
  have c2 := c.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at c1
  rw [le_div_iff₀ (by positivity)] at c2
  have b1 := b.trans (min_le_left _ _)
  have b2 := b.trans (min_le_right _ _)
  have d1 := d.trans (min_le_left _ _)
  have d2 := d.trans (min_le_right _ _)
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-- The precision conditions of `RHess` inside the decoupler: on a block of order
$n + 1 \le n_{\max} + 1$ and norm $N \le 2\Sigma$, in the class $(2B_c, g_c/2)$ with $B_c \ge 4$
and $0 < g_c \le \Sigma$, with the direction bound $s > 0$, the radius $R > 0$ and
$\sqrt p = s/(16RB_c)$, the `RHess` terms of the threshold give the precision conditions of
`NLAlib.SmallEig.rhess_pwrites` at the norm $N$. -/
theorem smallEigDecoupler_rhess_precision {nmax n : ℕ} (hn : n ≤ nmax) {u N S gc Bc s R p : ℝ}
    (hu0 : 0 ≤ u) (hN0 : 0 ≤ N) (hNS : N ≤ 2 * S) (hgc : 0 < gc) (hgcS : gc ≤ S)
    (hBc : 4 ≤ Bc) (hs : 0 < s) (hR : 0 < R) (hp : √p = s / (16 * R * Bc))
    (ha : 100000 * ((nmax : ℝ) + 1) ^ 2 * u ≤ 1)
    (hb : 1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S) * u ≤
      gc / 2 / (64 * ((nmax : ℝ) + 1) * (2 * Bc)))
    (hc : 1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S) * u ≤
      √p * (gc / 2) / (1024 * ((nmax : ℝ) + 1) * (2 * Bc) ^ 2)) :
    100 * ((n : ℝ) + 1) ^ 2 * u ≤ 1 ∧ 60 * ((n : ℝ) + 1) * u ≤ s / (2 * R) ∧
      200 * ((n : ℝ) + 1) ^ 2 * u * N ≤ min (gc / 2 / (32 * (n + 1) * (2 * Bc)))
        (s * (gc / 2) / (1024 * (n + 1) * (2 * Bc) ^ 2 * R)) := by
  have hn' : (n : ℝ) + 1 ≤ nmax + 1 := by exact_mod_cast Nat.succ_le_succ hn
  have hn1 : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((nmax : ℝ) + 1) ^ 2 := by gcongr
  have hS : 0 < S := hgc.trans_le hgcS
  have hK : 200 * ((n : ℝ) + 1) ^ 2 * u * N ≤ 1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S) * u := by
    have h1 : ((n : ℝ) + 1) ^ 2 * u * N ≤ ((nmax : ℝ) + 1) ^ 2 * u * (2 * S) := by
      gcongr
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ((nmax : ℝ) + 1)) hu0) hS.le]
  set Y := s / R with hY
  have hY0 : 0 < Y := div_pos hs hR
  have hA : √p ≤ Y / 64 := by
    rw [hp, hY, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hs hR]
  have hD : (1 : ℝ) ≤ 1024 * ((nmax : ℝ) + 1) * (2 * Bc) ^ 2 := by nlinarith
  have hc' : 1000 * ((nmax : ℝ) + 1) ^ 2 * (2 * S) * u ≤ Y / 64 * (S / 2) := by
    refine hc.trans ((div_le_self (by positivity) hD).trans ?_)
    exact mul_le_mul hA (by linarith) (by positivity) (by positivity)
  have hu1 : 2000 * ((nmax : ℝ) + 1) ^ 2 * u ≤ Y / 128 := by
    have : S * (2000 * ((nmax : ℝ) + 1) ^ 2 * u) ≤ S * (Y / 128) := by nlinarith
    exact le_of_mul_le_mul_left this hS
  refine ⟨by nlinarith, ?_, le_min (hK.trans (hb.trans ?_)) (hK.trans (hc.trans ?_))⟩
  · have e : s / (2 * R) = Y / 2 := by rw [hY]; field_simp
    rw [e]
    have : ((n : ℝ) + 1) ≤ ((nmax : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  · rw [hp]
    have e1 : s / (16 * R * Bc) * (gc / 2) / (1024 * ((nmax : ℝ) + 1) * (2 * Bc) ^ 2) =
        s * gc / (2048 * (2 * Bc) ^ 2 * R) / (16 * Bc * ((nmax : ℝ) + 1)) := by
      field_simp; norm_num
    have e2 : s * (gc / 2) / (1024 * ((n : ℝ) + 1) * (2 * Bc) ^ 2 * R) =
        s * gc / (2048 * (2 * Bc) ^ 2 * R) / ((n : ℝ) + 1) := by
      field_simp; norm_num
    rw [e1, e2]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

/-- The parameters of `RHess` inside the decoupler: with the direction bound
$s = \sqrt{\varphi_D/(8n_{\max})}$ and the radius $R' = \sqrt2\,R$ ($R$ =
`NLAlib.SmallEig.smallEigVectorRadius`), for $n \le n_{\max}$, $n_{\max} \ge 1$ and
$0 < \varphi \le 1$: the weight bound $p$ = `NLAlib.SmallEig.smallEigWeight` is the bound
$s^2/(64R'^2(2B_c)^2)$ of `NLAlib.SmallEig.rhess_pwrites` at the condition $2B_c$, so
$\sqrt p = s/(16R'B_c)$; $R'$ is a valid radius at the failure $\varphi_D/4$; and the failure
$(n + 1)s^2 + \varphi_D/4$ is at most $\varphi_D/2$. -/
theorem smallEigDecoupler_rhess_params {nmax n : ℕ} (hn1 : 1 ≤ nmax) (hn : n ≤ nmax)
    {φ Bc : ℝ} (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hBc : 0 < Bc) (S δ : ℝ) (c₂ : PolyLogTail)
    (hB : Bc = smallEigCondition nmax S δ φ c₂) :
    let s := √(smallEigDecouplerFailure nmax φ / (8 * nmax))
    let R := √2 * smallEigVectorRadius nmax φ
    0 < s ∧ 0 < R ∧
    smallEigWeight nmax S δ φ c₂ = s ^ 2 / (64 * R ^ 2 * (2 * Bc) ^ 2) ∧
    √(smallEigWeight nmax S δ φ c₂) = s / (16 * R * Bc) ∧
    2 * (√((n : ℝ) + 1) + 1) + √(2 * Real.log (smallEigDecouplerFailure nmax φ / 4)⁻¹) ≤ R ∧
    (n + 1) * s ^ 2 + smallEigDecouplerFailure nmax φ / 4 ≤
      smallEigDecouplerFailure nmax φ / 2 := by
  intro s R
  have hn' : (1 : ℝ) ≤ nmax := by exact_mod_cast hn1
  have hnn : (n : ℝ) ≤ nmax := by exact_mod_cast hn
  set φD := smallEigDecouplerFailure nmax φ with hφD
  have hD : 0 < φD := by rw [hφD]; unfold smallEigDecouplerFailure; positivity
  have hD16 : φD ≤ 1 / 16 := by
    rw [hφD]; unfold smallEigDecouplerFailure
    rw [div_le_iff₀ (by positivity)]; nlinarith
  set L := √(2 * Real.log (4 / φD)) with hL
  have hL2 : 2 ≤ L := by
    have h64 : 64 ≤ 4 / φD := by rw [le_div_iff₀ hD]; linarith
    have he : Real.exp 2 ≤ 64 := by
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
    have hlog : 2 ≤ Real.log (4 / φD) :=
      (Real.le_log_iff_exp_le (by positivity)).mpr (he.trans h64)
    rw [hL, Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hRv : smallEigVectorRadius nmax φ = 3 * √(nmax : ℝ) + L := by
    rw [hL, hφD]; rfl
  have hsn : 1 ≤ √(nmax : ℝ) := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hn'
  have h2 : 1.41 ≤ √(2 : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hRv0 : 0 < smallEigVectorRadius nmax φ := by rw [hRv]; positivity
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hR : 0 < R := by positivity
  have hs2 : s ^ 2 = φD / (8 * nmax) := Real.sq_sqrt (by positivity)
  have hR2 : R ^ 2 = 2 * smallEigVectorRadius nmax φ ^ 2 := by
    simp only [R, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hp : smallEigWeight nmax S δ φ c₂ = s ^ 2 / (64 * R ^ 2 * (2 * Bc) ^ 2) := by
    rw [hs2, hR2, smallEigWeight, ← hB, ← hφD]
    field_simp; ring
  refine ⟨hs, hR, hp, ?_, ?_, ?_⟩
  · rw [hp, show 64 * R ^ 2 * (2 * Bc) ^ 2 = (16 * R * Bc) ^ 2 by ring, ← div_pow,
      Real.sqrt_sq (by positivity)]
  · rw [inv_div, ← hL]
    have hnn2 : √((n : ℝ) + 1) ≤ √2 * √(nmax : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt (by linarith)
    simp only [R, hRv]
    nlinarith [mul_le_mul h2 hsn (by norm_num) (Real.sqrt_nonneg 2),
      mul_le_mul_of_nonneg_left hL2 (by linarith : (0 : ℝ) ≤ √2 - 1)]
  · rw [hs2]
    have : ((n : ℝ) + 1) * (φD / (8 * nmax)) ≤ φD / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith

/-- A power of a ratio loses at most a factor $2$ when the denominator grows by $1 + x$ with
$mx \le 1/2$: for $0 < a \le b(1 + x)$, $x \ge 0$, $c \ge 0$,
$(c/b)^m \le 2(c/a)^m$. -/
theorem div_pow_le_two_mul {a b c x : ℝ} {m : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hab : a ≤ b * (1 + x)) (hmx : m * x ≤ 1 / 2) :
    (c / b) ^ m ≤ 2 * (c / a) ^ m := by
  have h2 := one_add_pow_le_two hx hmx
  have h1 : c / b = (c / (b * (1 + x))) * (1 + x) := by field_simp
  have h3 : c / (b * (1 + x)) ≤ c / a := div_le_div_of_nonneg_left hc ha hab
  rw [h1, mul_pow]
  calc (c / (b * (1 + x))) ^ m * (1 + x) ^ m ≤ (c / a) ^ m * 2 := by gcongr
    _ = 2 * (c / a) ^ m := mul_comm _ _

/-- The precision conditions of `OneEig` inside the decoupler: on a block of order
$n + 1 \le n_{\max} + 1$ after `RHess`, of norm $\|\mathbf{H}\|_2 \le 2\Sigma(1 + x)$ with
$x = 200(n_{\max} + 1)^2\boldsymbol{u}$, the norm $\Sigma'' = 2\Sigma(1 + x)$ is within $1\%$ of
$2\Sigma$, and the `DistSpec` term of the threshold at the condition $8B_c$ gives the precision
condition of `NLAlib.SmallEig.oneEig_pwrites_of_norm_le` at the condition $4B_c$. -/
theorem smallEigDecoupler_oneEig_precision {nmax n m : ℕ} (hn : n ≤ nmax) {u S Hn η₁ Bc : ℝ}
    (hu0 : 0 ≤ u) (hS : 0 < S) (hη₁ : 0 < η₁) (hη₁S : η₁ ≤ S) (hBc : 4 ≤ Bc) (hN0 : 0 ≤ Hn)
    (hN : Hn ≤ 2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u))
    (ha : 100000 * ((nmax : ℝ) + 1) ^ 2 * u ≤ 1)
    (he : 300 * ((nmax : ℝ) + 1) ^ 2 * u ≤ (8004 * (8 * Bc))⁻¹ * (η₁ / (22 * (2 * S))) ^ m) :
    2 * S ≤ 2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u) ∧
      2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u) ≤ 1.01 * (2 * S) ∧
      300 * ((n : ℝ) + 1) ^ 2 * u ≤ (8004 * (4 * Bc))⁻¹ *
        (η₁ / (2 * Hn + 20 * (2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u)))) ^ m := by
  set x := 200 * ((nmax : ℝ) + 1) ^ 2 * u with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 0.01 := by linarith
  have hn' : (n : ℝ) + 1 ≤ nmax + 1 := by exact_mod_cast Nat.succ_le_succ hn
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((nmax : ℝ) + 1) ^ 2 := by gcongr
  set r := η₁ / (22 * (2 * S)) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 / 2 := by rw [hr, div_le_iff₀ (by positivity)]; linarith
  set K := (8004 * (8 * Bc))⁻¹ with hK
  have hK0 : 0 < K := by positivity
  have hK1 : K ≤ 1 / 2 := by rw [hK]; rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  have hmr := succ_mul_pow_le_one hr0.le hr1 m
  have hmx : m * x ≤ 1 / 2 := by
    have : x ≤ K * r ^ m := by linarith
    have h1 : (m : ℝ) * x ≤ m * (K * r ^ m) := by gcongr
    have h2 : (m : ℝ) * r ^ m ≤ 1 := by nlinarith [pow_nonneg hr0.le m]
    nlinarith
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have hden : 0 < 2 * Hn + 20 * (2 * S * (1 + x)) := by positivity
  have hpow := div_pow_le_two_mul (c := η₁) (m := m) hden (by positivity : (0 : ℝ) < 22 * (2 * S))
    hη₁.le hx0 (by nlinarith) hmx
  rw [← hr] at hpow
  have e : (8004 * (4 * Bc))⁻¹ = 2 * K := by rw [hK]; field_simp; ring
  rw [e]
  have : 300 * ((n : ℝ) + 1) ^ 2 * u ≤ 300 * ((nmax : ℝ) + 1) ^ 2 * u := by gcongr
  nlinarith

/-- The precision conditions of `Decouple` inside the decoupler: on a block of order
$k + 2 \le n_{\max} + 1$ after `RHess`, with $\eta_1 \le \|\mathbf{H}\|_2 \le 2\Sigma(1 + x)$,
$x = 200(n_{\max} + 1)^2\boldsymbol{u}$, the `Decouple` terms of the threshold at the condition
$8B_c$ give the precision conditions of `NLAlib.SmallEig.decoupleLast_spec` at the condition $4B_c$
and the shift reach $C = 10$, for every step count $\ell \le m_2$. -/
theorem smallEigDecoupler_decouple_precision {nmax k m₂ : ℕ} (hk : k + 1 ≤ nmax)
    {u S Hn η₁ Bc ω : ℝ} (hu0 : 0 ≤ u) (hS : 0 < S) (hη₁ : 0 < η₁) (hη₁S : η₁ ≤ S)
    (hBc : 4 ≤ Bc) (hη₁H : η₁ ≤ Hn) (hN : Hn ≤ 2 * S * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u))
    (hf : 300 * ((nmax : ℝ) + 1) ^ 2 * u ≤ (16 * (8 * Bc))⁻¹ * (η₁ / (22 * (2 * S))) ^ m₂)
    (hg : 300 * ((nmax : ℝ) + 1) ^ 2 * u ≤ ω / 2 / (86 * (8 * Bc) * (2 * S) *
      (22 * (2 * S) / η₁) ^ m₂ * √((nmax : ℝ) + 1))) :
    (∀ ℓ ≤ m₂, 300 * ((k : ℝ) + 2) ^ 2 * u ≤
      (16 * (4 * Bc))⁻¹ * (η₁ / ((2 + 2 * 10) * Hn)) ^ ℓ) ∧
    ∀ ℓ ≤ m₂, (66 + 2 * 10) * (4 * Bc) * Hn * ((2 + 2 * 10) * Hn / η₁) ^ ℓ *
      √((k : ℝ) + 2) * (300 * ((k : ℝ) + 2) ^ 2 * u) ≤ ω / 2 := by
  set x := 200 * ((nmax : ℝ) + 1) ^ 2 * u with hx
  have hx0 : 0 ≤ x := by positivity
  have hk' : (k : ℝ) + 2 ≤ nmax + 1 := by
    have : ((k + 1 : ℕ) : ℝ) ≤ nmax := by exact_mod_cast hk
    push_cast at this; linarith
  have hsq : ((k : ℝ) + 2) ^ 2 ≤ ((nmax : ℝ) + 1) ^ 2 := by gcongr
  set V := 300 * ((nmax : ℝ) + 1) ^ 2 * u with hV
  have hV0 : 0 ≤ V := by positivity
  have hkV : 300 * ((k : ℝ) + 2) ^ 2 * u ≤ V := by rw [hV]; gcongr
  set r := η₁ / (22 * (2 * S)) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 / 2 := by rw [hr, div_le_iff₀ (by positivity)]; linarith
  have hmr := succ_mul_pow_le_one hr0.le hr1 m₂
  have hK1 : (16 * (8 * Bc))⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  have hmx : ((m₂ + 1 : ℕ) : ℝ) * x ≤ 1 / 2 := by
    have h1 : x ≤ r ^ m₂ / 2 := by nlinarith [pow_nonneg hr0.le m₂]
    push_cast
    nlinarith [pow_nonneg hr0.le m₂]
  have hmx' : (m₂ : ℝ) * x ≤ 1 / 2 := by push_cast at hmx; nlinarith
  have hH0 : 0 < Hn := hη₁.trans_le hη₁H
  refine ⟨fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
  · have ha1 : η₁ / ((2 + 2 * 10) * Hn) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hpow := div_pow_le_two_mul (c := η₁) (m := m₂)
      (by positivity : (0 : ℝ) < (2 + 2 * 10) * Hn) (by positivity : (0 : ℝ) < 22 * (2 * S))
      hη₁.le hx0 (by nlinarith) hmx'
    rw [← hr] at hpow
    have hℓ' : (η₁ / ((2 + 2 * 10) * Hn)) ^ m₂ ≤ (η₁ / ((2 + 2 * 10) * Hn)) ^ ℓ :=
      pow_le_pow_of_le_one (by positivity) ha1 hℓ
    have e : (16 * (4 * Bc))⁻¹ = 2 * (16 * (8 * Bc))⁻¹ := by field_simp; ring
    rw [e]
    nlinarith [inv_pos.mpr (by positivity : (0 : ℝ) < 16 * (8 * Bc))]
  · set Z := (22 * (2 * S) / η₁) ^ m₂ with hZ
    have hb1 : 1 ≤ (2 + 2 * 10) * Hn / η₁ := by rw [le_div_iff₀ hη₁]; linarith
    have hb : ((2 + 2 * 10) * Hn / η₁) ^ ℓ ≤ Z * (1 + x) ^ m₂ := by
      calc ((2 + 2 * 10) * Hn / η₁) ^ ℓ ≤ ((2 + 2 * 10) * Hn / η₁) ^ m₂ :=
            pow_le_pow_right₀ hb1 hℓ
        _ ≤ (22 * (2 * S) / η₁ * (1 + x)) ^ m₂ := by
            gcongr
            rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hη₁]; nlinarith
        _ = Z * (1 + x) ^ m₂ := by rw [mul_pow]
    have h2 := one_add_pow_le_two hx0 hmx
    have hD : 0 < 86 * (8 * Bc) * (2 * S) * Z * √((nmax : ℝ) + 1) := by positivity
    rw [le_div_iff₀ hD] at hg
    have hsk : √((k : ℝ) + 2) ≤ √((nmax : ℝ) + 1) := Real.sqrt_le_sqrt hk'
    calc (66 + 2 * 10) * (4 * Bc) * Hn * ((2 + 2 * 10) * Hn / η₁) ^ ℓ *
          √((k : ℝ) + 2) * (300 * ((k : ℝ) + 2) ^ 2 * u)
        ≤ (66 + 2 * 10) * (4 * Bc) * (2 * S * (1 + x)) * (Z * (1 + x) ^ m₂) *
          √((nmax : ℝ) + 1) * V := by gcongr
      _ = V * (86 * (8 * Bc) * (2 * S) * Z * √((nmax : ℝ) + 1)) * ((1 + x) ^ (m₂ + 1) / 2) := by
          ring
      _ ≤ V * (86 * (8 * Bc) * (2 * S) * Z * √((nmax : ℝ) + 1)) * 1 := by
          gcongr; linarith
      _ ≤ ω / 2 := by linarith

/-- The backward errors of `RHess` and `Decouple` add up to
`NLAlib.SmallEig.smallEigDecoupleError`: for a block of order $k + 2 \le n_{\max} + 1$ and norm at
most $N$, an error $\varepsilon_1 \le 200(n_{\max} + 1)^2\boldsymbol{u}N$ and a block after
`RHess` of norm at most $2N$. -/
theorem smallEigDecoupleError_le {nmax k : ℕ} (hk : k + 1 ≤ nmax) {S δ φ : ℝ}
    {c₂ : PolyLogTail} {u N ε₁ Hn : ℝ} (hu0 : 0 ≤ u) (hN0 : 0 ≤ N)
    (hH : Hn ≤ 2 * N) (hε₁ : ε₁ ≤ 200 * ((nmax : ℝ) + 1) ^ 2 * u * N) :
    ε₁ + (1 + 10) * Hn * ((1 + 300 * ((k : ℝ) + 2) ^ 2 * u) ^
      smallEigDecoupleSteps nmax S δ φ c₂ - 1) ≤ smallEigDecoupleError nmax S δ φ c₂ u N := by
  unfold smallEigDecoupleError
  set m := smallEigDecoupleSteps nmax S δ φ c₂
  have hk' : (k : ℝ) + 2 ≤ nmax + 1 := by
    have : ((k + 1 : ℕ) : ℝ) ≤ nmax := by exact_mod_cast hk
    push_cast at this; linarith
  have hpow : (1 + 300 * ((k : ℝ) + 2) ^ 2 * u) ^ m ≤ (1 + 300 * ((nmax : ℝ) + 1) ^ 2 * u) ^ m := by
    gcongr
  have h1 : 1 ≤ (1 + 300 * ((k : ℝ) + 2) ^ 2 * u) ^ m :=
    one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  have h2 : (1 + 10) * Hn * ((1 + 300 * ((k : ℝ) + 2) ^ 2 * u) ^ m - 1) ≤
      11 * (2 * N) * ((1 + 300 * ((nmax : ℝ) + 1) ^ 2 * u) ^ m - 1) := by
    norm_num
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

/-- The level of `Decouple`: from $(1 - \boldsymbol{u})a \le \sqrt{2\omega^2}$ with
$\omega > 0$ and $\boldsymbol{u} \le 1/100$, $a \le 1.5\,\omega$. -/
theorem le_of_sub_mul_le_sqrt {ω u a : ℝ} (hω : 0 < ω) (hu : u ≤ 1 / 100)
    (h : (1 - u) * a ≤ √(2 * ω ^ 2)) : a ≤ 1.5 * ω := by
  have hsq : √(2 * ω ^ 2) ≤ 1.42 * ω := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  by_contra hlt
  push Not at hlt
  have : 0.99 * (1.5 * ω) ≤ (1 - u) * a :=
    mul_le_mul (by linarith) hlt.le (by positivity) (by linarith)
  linarith

/-- The side conditions of `NLAlib.SmallEig.decoupleLast_spec` inside the decoupler, at the
condition $4B_c$ and the shift reach $C = 10$: let $\mathbf{H}_1$ of order $k + 2 \le n_{\max} + 1$
be a perturbed unitary similarity with error at most $200(n_{\max} + 1)^2\boldsymbol{u}N$ of a
block of norm at most $N \le 2\Sigma$, with a diagonalization of separation $g_c/4$, and let $z$ be
at distance between $\eta_1$ and $\beta'$ from its eigenvalues. Then $\mathbf{H}_1 \ne 0$,
$\|\mathbf{H}_1\|_2 \le 2N$, $\lvert z\rvert \le 10\|\mathbf{H}_1\|_2$, $z$ is at distance at least
$\eta_1$ from every eigenvalue and within $\beta'$ of one, and the precision conditions hold for
every step count $\ell \le m_2$. -/
theorem smallEigDecoupler_decouple_conditions {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b)
    (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn1 : 1 ≤ nmax) {S δ φ u : ℝ} (hu0 : 0 ≤ u) (hδ : 0 < δ)
    (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) {k : ℕ}
    (hk : k + 1 ≤ nmax) {N ε₁ : ℝ} {H H₁ V : Matrix (Fin (k + 1 + 1)) (Fin (k + 1 + 1)) ℂ}
    {d : Fin (k + 1 + 1) → ℂ} (hHN : specNorm H ≤ N) (hN : N ≤ 2 * S)
    (hH₁ : IsPerturbedUnitarySimilar H H₁ ε₁) (hε₁ : ε₁ ≤ 200 * ((nmax : ℝ) + 1) ^ 2 * u * N)
    (hV : IsUnit V) (hHV : H₁ * V = V * Matrix.diagonal d)
    (hgap : ∀ i j, i ≠ j → smallEigSeparation nmax S δ φ c₁ / 4 ≤ ‖d i - d j‖) {z : ℂ}
    (hz1 : smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ ⨅ i, ‖z - d i‖)
    (hz2 : ⨅ i, ‖z - d i‖ ≤ smallEigAccuracy nmax S δ φ c₁ c₂) :
    H₁ ≠ 0 ∧ specNorm H₁ ≤ 2 * N ∧ ‖z‖ ≤ 10 * specNorm H₁ ∧
      (∀ j, smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ ‖d j - z‖) ∧
      (∃ i, ‖z - d i‖ ≤ smallEigAccuracy nmax S δ φ c₁ c₂) ∧
      (∀ ℓ ≤ smallEigDecoupleSteps nmax S δ φ c₂, 300 * ((k : ℝ) + 2) ^ 2 * u ≤
        (16 * (4 * smallEigCondition nmax S δ φ c₂))⁻¹ *
          (smallEigInnerRadius nmax S δ φ c₁ c₂ / ((2 + 2 * 10) * specNorm H₁)) ^ ℓ) ∧
      ∀ ℓ ≤ smallEigDecoupleSteps nmax S δ φ c₂, (66 + 2 * 10) *
        (4 * smallEigCondition nmax S δ φ c₂) * specNorm H₁ *
        ((2 + 2 * 10) * specNorm H₁ / smallEigInnerRadius nmax S δ φ c₁ c₂) ^ ℓ *
        √((k : ℝ) + 2) * (300 * ((k : ℝ) + 2) ^ 2 * u) ≤ smallEigOmega nmax S δ φ c₁ c₂ / 2 := by
  have hS0 : 0 < S := hδ.trans_le hδS
  have hn' : (1 : ℝ) ≤ nmax := by exact_mod_cast hn1
  obtain ⟨ha, -, -, -, -, hf, hg⟩ := smallEigDecoupler_precision hb₁ hb₂ hn1 hδ hδS hφ hφ1 hu
  obtain ⟨-, -, -, -, -, -, hω, -, hωB, hβS, -⟩ := smallEigParams_spec hb₁ hb₂ hn1 hδ hδS hφ hφ1
  have hβ : smallEigAccuracy nmax S δ φ c₁ c₂ = smallEigOmega nmax S δ φ c₁ c₂ / 20 := rfl
  have hsep := smallEigSeparation_pos hb₁ hn1 hS0.le hδ hφ hφ1
  have hBc := smallEigCondition_ge hb₂ hn1 hS0.le hδ hφ hφ1
  have hη₁ := smallEigInnerRadius_pos hb₁ hb₂ hn1 hδ hδS hφ hφ1
  have hD1 : smallEigDecouplerFailure nmax φ / 2 ≤ 1 := by
    unfold smallEigDecouplerFailure
    rw [div_div, div_le_one (by positivity)]; nlinarith
  have hη₁6 := oneEigInnerRadius_le (by linarith) hβS
    (by positivity : 0 < smallEigSeparation nmax S δ φ c₁ / 4) hD1
  have hη₂g : smallEigOuterRadius nmax S δ φ c₁ c₂ ≤ smallEigSeparation nmax S δ φ c₁ / 4 / 3 :=
    min_le_right _ _
  have hη₂β : smallEigOuterRadius nmax S δ φ c₁ c₂ ≤ smallEigAccuracy nmax S δ φ c₁ c₂ / 40 :=
    min_le_left _ _
  change oneEigInnerRadius _ _ _ _ ≤ _ at hη₁6
  unfold smallEigOuterRadius at hη₂g hη₂β
  change smallEigInnerRadius nmax S δ φ c₁ c₂ ≤ _ at hη₁6
  have hN0 : 0 ≤ N := (specNorm_nonneg H).trans hHN
  have hx : 200 * ((nmax : ℝ) + 1) ^ 2 * u ≤ 1 := by linarith
  have hH₁N : specNorm H₁ ≤ N * (1 + 200 * ((nmax : ℝ) + 1) ^ 2 * u) := by
    have := hH₁.specNorm_le; nlinarith
  have hlast : (0 : Fin (k + 1 + 1)) ≠ Fin.last (k + 1) := fun h => by
    have := congrArg Fin.val h; simp at this
  have hdH : ∀ i, ‖d i‖ ≤ specNorm H₁ := norm_le_specNorm_of_mul_eq_mul_diagonal hV hHV
  have hlow : smallEigSeparation nmax S δ φ c₁ / 8 ≤ specNorm H₁ := by
    have h1 := hgap 0 (Fin.last (k + 1)) hlast
    have h2 := norm_sub_le (d 0) (d (Fin.last (k + 1)))
    linarith [hdH 0, hdH (Fin.last (k + 1))]
  obtain ⟨hxu, hfwd⟩ := smallEigDecoupler_decouple_precision hk hu0 hS0 hη₁ (by linarith)
    hBc (by linarith) (hH₁N.trans (by gcongr)) hf hg
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => ‖z - d i‖)
  have hzi : ‖z - d i‖ ≤ smallEigAccuracy nmax S δ φ c₁ c₂ := hi ▸ hz2
  refine ⟨fun h0 => by rw [h0, specNorm_zero] at hlow; linarith,
    by have := mul_le_mul_of_nonneg_left hx hN0; linarith, ?_,
    fun j => by rw [norm_sub_rev]; exact hz1.trans (ciInf_le (Finite.bddBelow_range _) j),
    ⟨i, hzi⟩, hxu, hfwd⟩
  have := norm_le_insert' z (d i)
  have h3 : 2 * (2.25 * smallEigOmega nmax S δ φ c₁ c₂) ≤ smallEigSeparation nmax S δ φ c₁ := by
    have : smallEigSeparation nmax S δ φ c₁ /
        (16 * nmax * smallEigCondition nmax S δ φ c₂) ≤ smallEigSeparation nmax S δ φ c₁ :=
      div_le_self hsep.le (by nlinarith)
    have := mul_le_mul_of_nonneg_right hn'
      (by positivity : (0 : ℝ) ≤ 2 * (2.25 * smallEigOmega nmax S δ φ c₁ c₂))
    linarith
  linarith [hdH i, specNorm_nonneg H₁]

end NLAlib.SmallEig
