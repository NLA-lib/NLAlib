/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Growth
public import NLAlib.LowRank.Structural.BlockKrylov
public import NLAlib.LowRank.Structural.Filter
public import NLAlib.Matrix.Spectral.CompressionSingularValues

/-!
# Singular values of filtered sketches and of block Krylov iteration

Deterministic lower bounds on the singular values of the randomized SVD at a filtered test
matrix, $\mathsf{rsvd}(\mathbf{A}, g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega})$, and of
randomized block Krylov iteration $\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)$: the squares
$\sigma_i(\cdot)^2$ of the singular values of the output (the Ritz values of
$\mathbf{A}\mathbf{A}^{\mathsf{H}}$ on the sketched space) are close to
$\sigma_i(\mathbf{A})^2$. The test matrix enters through a frame $\mathbf{Z}$ of right singular
vectors with $\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ of full row rank and the residual
$(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t)\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}$, as in the structural analysis of the randomized
SVD. There are two regimes: with a gap between a head index and a tail index $t$ the deficit is
the residual times a Chebyshev value in the relative gap; without a gap the deficit is
$\gamma\,\sigma_k^2$ plus the residual times a Chebyshev value in $\gamma$, for any
$\gamma \in (0, 1]$. These are the per-vector guarantees of [MuscoMusco2015], stated for singular
values.

## Main results

* `NLAlib.HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rsvd_cfc`,
  `NLAlib.HasOrthonormalCols.sq_sub_le_sq_singularValues_rsvd_cfc_of_le_singularValues`: a
  filtered sketch, gap form and cut form.
* `NLAlib.specNorm_sub_mul_cfc_mul_mul_le`: a filter bounded by $a$ on the tail scales the
  sketch residual by at most $a$.
* `NLAlib.HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki`: block Krylov
  iteration, no gap.
* `NLAlib.HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki_singularGapRatio`,
  `NLAlib.HasOrthonormalCols.sum_sq_singularValues_sub_sq_singularValues_rbki_le`: block Krylov
  iteration with a gap, per index and summed.
* `NLAlib.HasOrthonormalCols.frobNorm_sub_truncatedSVD_rbki_sq_le_add_mul`: the Frobenius error
  of one truncated run.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n s : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype s]
  [DecidableEq m] [DecidableEq n] [DecidableEq s]

/-! ### Filters -/

omit [DecidableEq m] [DecidableEq n] in
/-- A Chebyshev filter of every degree, over $\Bbbk$: for a matrix $\mathbf{A}$, a head of
$r = h + 1$ singular values, a tail index $t \ge r$ and a degree $d$, there are a real
polynomial $f$ of degree at most $d$ and constants $c > 0$ and $a$ with
$\lvert f(\sigma_i^2) \rvert \ge c$ for $i < r$, $\lvert f \rvert \le a$ on $[0, \sigma_t^2]$,
and $(a/c)^2 \le 4e^{-8d\sqrt{\gamma}}$, where
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$ (zero when $\sigma_h = 0$). The statement
of `NLAlib.exists_degree_lt_div_sq_le_exp_singularGapRatio` for a matrix over any `RCLike` field
instead of a real matrix; it replaces that theorem, under its name, once it is proved. -/
theorem exists_degree_lt_div_sq_le_exp_singularGapRatio' (A : Matrix m n 𝕜) {h r t : ℕ}
    (hr : h + 1 = r) (hrt : r ≤ t) (d : ℕ) :
    ∃ f : ℝ[X], f.degree < (d + 1 : ℕ) ∧ ∃ c a : ℝ, 0 < c ∧
      (∀ i < r, c ≤ |f.eval (singularValues A i ^ 2)|) ∧
      (∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |f.eval x| ≤ a) ∧
      (a / c) ^ 2 ≤ 4 * Real.exp (-8 * (d : ℝ) * Real.sqrt (singularGapRatio A h t)) := by
  have hht : h ≤ t := by omega
  rcases (singularValues_nonneg A h).eq_or_lt with hσh | hσh
  · -- $\sigma_h = 0$: then $\sigma_t = 0$, the gap ratio is zero and the constant filter does.
    have hσt : singularValues A t = 0 :=
      le_antisymm (hσh ▸ singularValues_antitone A hht) (singularValues_nonneg A t)
    refine ⟨1, by rw [degree_one]; exact_mod_cast Nat.succ_pos d, 1, 1, one_pos,
      fun i _ => by simp, fun x _ => by simp, ?_⟩
    simp [singularGapRatio, hσt, ← hσh]
  obtain ⟨f, hf, c, a, hc, hhead, htail, hac⟩ :=
    Polynomial.Chebyshev.exists_degree_lt_div_sq_le_exp_of_le
      (singularValues_nonneg A t) (singularValues_antitone A hht) hσh d
  refine ⟨f, hf, c, a, hc, fun i hi => hhead _ ?_, htail, hac⟩
  exact pow_le_pow_left₀ (singularValues_nonneg A h) (singularValues_antitone A (by omega)) 2

/-! ### Filtered sketches -/

omit [DecidableEq m] [DecidableEq n] [DecidableEq s] in
/-- A frame whose range contains the row space of $\llbracket\mathbf{A}\rrbracket_{i+1}$
contains every head frame: if $\sigma_i(\mathbf{A}) > 0$,
$\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{T} = \mathbf{T}\operatorname{diag}(\sigma_j^2)_{j \le i}$
with $\mathbf{A}\mathbf{T}\mathbf{T}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_{i+1}$, and
$\llbracket\mathbf{A}\rrbracket_{i+1}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} =
\llbracket\mathbf{A}\rrbracket_{i+1}$, then
$\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\mathbf{T} = \mathbf{T}$. -/
private theorem mul_conjTranspose_mul_eq_of_truncatedSVD_mul {A : Matrix m n 𝕜} {i : ℕ}
    (hσ : 0 < singularValues A i) {T : Matrix n (Fin (i + 1)) 𝕜} (hT : HasOrthonormalCols T)
    (hHT : Aᴴ * A * T =
      T * Matrix.diagonal fun j : Fin (i + 1) => ((singularValues A j ^ 2 : ℝ) : 𝕜))
    (hATT : A * T * Tᴴ = truncatedSVD A (i + 1)) {Z : Matrix n s 𝕜}
    (hAZ : truncatedSVD A (i + 1) * Z * Zᴴ = truncatedSVD A (i + 1)) : Z * Zᴴ * T = T := by
  set Dinv := Matrix.diagonal fun j : Fin (i + 1) => (((singularValues A j ^ 2)⁻¹ : ℝ) : 𝕜)
  have hDD : (Matrix.diagonal fun j : Fin (i + 1) => ((singularValues A j ^ 2 : ℝ) : 𝕜)) *
      Dinv = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    have hj : 0 < singularValues A j :=
      hσ.trans_le (singularValues_antitone A (Nat.lt_succ_iff.mp j.isLt))
    rw [← RCLike.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero 2 hj.ne'), RCLike.ofReal_one]
  have hG : (A * T)ᴴ * (A * T) =
      Matrix.diagonal fun j : Fin (i + 1) => ((singularValues A j ^ 2 : ℝ) : 𝕜) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hHT,
      ← Matrix.mul_assoc, hT.conjTranspose_mul_self, Matrix.one_mul]
  have hTD : (truncatedSVD A (i + 1))ᴴ * (A * T * Dinv) = T := by
    calc (truncatedSVD A (i + 1))ᴴ * (A * T * Dinv) = T * ((A * T)ᴴ * (A * T)) * Dinv := by
          rw [← hATT, Matrix.conjTranspose_mul (A * T) Tᴴ, Matrix.conjTranspose_conjTranspose]
          simp only [Matrix.mul_assoc]
      _ = T := by rw [hG, Matrix.mul_assoc, hDD, Matrix.mul_one]
  have hZA : Z * Zᴴ * (truncatedSVD A (i + 1))ᴴ = (truncatedSVD A (i + 1))ᴴ := by
    have h := congrArg Matrix.conjTranspose hAZ
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc] at h
  conv_lhs => rw [← hTD]
  rw [← Matrix.mul_assoc, hZA, hTD]

omit [DecidableEq m] [DecidableEq s] in
-- TODO(move): NLAlib/Matrix/Functions/HermitianCalculus.lean
/-- The quadratic form of a function of a Hermitian matrix through two complementary invariant
frames: if $\mathbf{T}\mathbf{T}^{\mathsf{H}} + \mathbf{V}\mathbf{V}^{\mathsf{H}} = \mathbf{I}$,
$\mathbf{H}\mathbf{T} = \mathbf{T}\operatorname{diag}(\mathbf{d})$ and
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{e})$, then for every real
$\varphi$ and every $\mathbf{x}$,
$$\operatorname{Re}\bigl(\mathbf{x}^{\mathsf{H}}\varphi(\mathbf{H})\mathbf{x}\bigr) =
\sum_j \varphi(d_j)\,\lvert(\mathbf{T}^{\mathsf{H}}\mathbf{x})_j\rvert^2 +
\sum_j \varphi(e_j)\,\lvert(\mathbf{V}^{\mathsf{H}}\mathbf{x})_j\rvert^2\,.$$
The two-frame form of `NLAlib.HasOrthonormalCols.re_quadForm_cfc_eq_sum`: a head frame and its
complement, with no relabelling into one square frame. -/
theorem _root_.Matrix.IsHermitian.re_quadForm_cfc_eq_sum_add_sum {p q : Type*} [Fintype p]
    [Fintype q] [DecidableEq p] [DecidableEq q] {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    {T : Matrix n p 𝕜} {V : Matrix n q 𝕜} (h1 : T * Tᴴ + V * Vᴴ = 1) {d : p → ℝ} {e : q → ℝ}
    (hHT : H * T = T * Matrix.diagonal fun j => (d j : 𝕜))
    (hHV : H * V = V * Matrix.diagonal fun j => (e j : 𝕜)) (φ : ℝ → ℝ) (x : n → 𝕜) :
    RCLike.re (quadForm (cfc φ H) x) =
      ∑ j, φ (d j) * ‖(Tᴴ *ᵥ x) j‖ ^ 2 + ∑ j, φ (e j) * ‖(Vᴴ *ᵥ x) j‖ ^ 2 := by
  have hsplit : cfc φ H =
      Tᴴᴴ * (Matrix.diagonal fun j => (φ (d j) : 𝕜)) * Tᴴ +
        Vᴴᴴ * (Matrix.diagonal fun j => (φ (e j) : 𝕜)) * Vᴴ := by
    rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
      ← hH.cfc_mul_eq_mul_diagonal_of_mul_eq hHT φ, ← hH.cfc_mul_eq_mul_diagonal_of_mul_eq hHV φ,
      Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, h1, Matrix.mul_one]
  rw [hsplit, quadForm_add_left, quadForm_conjTranspose_mul_mul, quadForm_conjTranspose_mul_mul,
    quadForm_diagonal, quadForm_diagonal, map_add, map_sum, map_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun j _ => by rw [← RCLike.ofReal_mul, RCLike.ofReal_re]

omit [DecidableEq m] [DecidableEq s] in
/-- The vector core of the tail bound: with complementary invariant frames $\mathbf{T}$ and
$\mathbf{V}$ of $\mathbf{A}^{\mathsf{H}}\mathbf{A}$, tail eigenvalues $e_j \ge 0$ with
$\lvert g(e_j) \rvert \le a$, and $\mathbf{T}^{\mathsf{H}}\mathbf{y} = \mathbf{0}$,
$\|\mathbf{A}g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{y}\| \le a\|\mathbf{A}\mathbf{y}\|$. -/
private theorem norm_mulVec_cfc_mulVec_le {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] (A : Matrix m n 𝕜) (g : ℝ → ℝ) {T : Matrix n p 𝕜} {V : Matrix n q 𝕜}
    (h1 : T * Tᴴ + V * Vᴴ = 1) {d : p → ℝ} {e : q → ℝ}
    (hHT : Aᴴ * A * T = T * Matrix.diagonal fun j => (d j : 𝕜))
    (hHV : Aᴴ * A * V = V * Matrix.diagonal fun j => (e j : 𝕜)) {a : ℝ} (ha : 0 ≤ a)
    (he : ∀ j, 0 ≤ e j) (heg : ∀ j, |g (e j)| ≤ a) {y : n → 𝕜} (hy : Tᴴ *ᵥ y = 0) :
    ‖WithLp.toLp 2 (A *ᵥ (cfc g (Aᴴ * A) *ᵥ y))‖ ≤ a * ‖WithLp.toLp 2 (A *ᵥ y)‖ := by
  have hH : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  have hF : (cfc g (Aᴴ * A)).IsHermitian := cfc_predicate g (Aᴴ * A)
  have hsa : IsSelfAdjoint (Aᴴ * A) := hH
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (Aᴴ * A)) := fun f =>
    (Aᴴ * A).finite_real_spectrum.continuousOn f
  have hcY : cfc (fun x => g x * x * g x) (Aᴴ * A) =
      (cfc g (Aᴴ * A))ᴴ * (Aᴴ * A) * cfc g (Aᴴ * A) := by
    rw [cfc_mul (fun x => g x * x) g _ (hcont _) (hcont _),
      cfc_mul g (fun x => x) _ (hcont _) (hcont _), cfc_id' ℝ (Aᴴ * A) hsa, hF.eq]
  have hq := hH.re_quadForm_cfc_eq_sum_add_sum h1 hHT hHV
  have hY := hq (fun x => g x * x * g x) y
  rw [hcY, quadForm_conjTranspose_mul_mul, quadForm_conjTranspose_mul_self, RCLike.ofReal_re,
    hy] at hY
  have hE := hq (fun x => x) y
  rw [cfc_id' ℝ (Aᴴ * A) hsa, quadForm_conjTranspose_mul_self, RCLike.ofReal_re, hy] at hE
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, Finset.sum_const_zero, zero_add] at hY hE
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
  rw [mul_pow, hY, hE, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hga : g (e j) ^ 2 ≤ a ^ 2 := by
    rw [← sq_abs (g (e j))]
    exact pow_le_pow_left₀ (abs_nonneg _) (heg j) 2
  nlinarith [mul_le_mul_of_nonneg_right hga (mul_nonneg (he j) (sq_nonneg ‖(Vᴴ *ᵥ y) j‖))]

omit [DecidableEq m] [DecidableEq s] in
/-- A filter on the tail of a frame: if $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} =
\llbracket\mathbf{A}\rrbracket_t$ (the columns of $\mathbf{Z}$ need not be orthonormal) and
$\lvert g \rvert \le a$ on $[0, \sigma_t(\mathbf{A})^2]$, then for every $\mathbf{Y}$, with
$\mathbf{B} = \mathbf{A}g(\mathbf{A}^{\mathsf{H}}\mathbf{A})$,
$$\|(\mathbf{B} - \mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{Y}\|_2 \le
a\,\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t)\mathbf{Y}\|_2\,.$$
The filtered residual of
`NLAlib.HasOrthonormalCols.singularValues_one_sub_rangeProjector_mul_mul_le` at $\mathbf{Y} = \mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}$ is at most $a$
times the unfiltered one: $\mathbf{I} - \mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ differs from the
projector onto the tail right singular vectors only on the kernel of $\mathbf{A}$, which
$g(\mathbf{A}^{\mathsf{H}}\mathbf{A})$ preserves. -/
theorem specNorm_sub_mul_cfc_mul_mul_le {A : Matrix m n 𝕜} (g : ℝ → ℝ) {Z : Matrix n s 𝕜}
    {t : ℕ} (hAZ : A * Z * Zᴴ = truncatedSVD A t) {a : ℝ}
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |g x| ≤ a) (Y : Matrix n l 𝕜) :
    specNorm ((A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) * Y) ≤
      a * specNorm ((A - truncatedSVD A t) * Y) := by
  classical
  have ha : 0 ≤ a := (abs_nonneg _).trans (htail 0 ⟨le_rfl, sq_nonneg _⟩)
  set t' := min t (Fintype.card n)
  have hT' : truncatedSVD A t' = truncatedSVD A t := by
    rcases le_total t (Fintype.card n) with h | h
    · rw [show t' = t from min_eq_left h]
    · rw [show t' = Fintype.card n from min_eq_right h,
        truncatedSVD_of_rank_le A A.rank_le_card_width,
        truncatedSVD_of_rank_le A (A.rank_le_card_width.trans h)]
  obtain ⟨T, V, hT, -, -, h1, hHT, hHV, htr⟩ :=
    exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal A
      (min_le_right t (Fintype.card n))
  have hATT : A * T * Tᴴ = truncatedSVD A t := by
    have h := htr t' le_rfl
    rw [Fin.castLE_rfl, Matrix.submatrix_id_id] at h
    rw [h, hT']
  have he (j : Fin (Fintype.card n - t')) : singularValues A (t' + j) ≤ singularValues A t := by
    rcases le_total t (Fintype.card n) with h | h
    · exact singularValues_antitone A (by omega)
    · rw [singularValues_of_card_cols_le A (by omega)]
      exact singularValues_nonneg A t
  -- `Z Zᴴ` and `T Tᴴ` differ on the kernel of `A`, which the filter preserves
  have hK : A * (Z * Zᴴ - T * Tᴴ) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAZ, hATT, sub_self]
  have hGK : A * cfc g (Aᴴ * A) * (Z * Zᴴ - T * Tᴴ) = 0 := by
    have hHK : Aᴴ * A * (Z * Zᴴ - T * Tᴴ) =
        (Z * Zᴴ - T * Tᴴ) * Matrix.diagonal fun _ : n => ((0 : ℝ) : 𝕜) := by
      rw [Matrix.mul_assoc, hK, Matrix.mul_zero, RCLike.ofReal_zero, Matrix.diagonal_zero,
        Matrix.mul_zero]
    rw [Matrix.mul_assoc,
      (Matrix.isHermitian_conjTranspose_mul_self A).cfc_mul_eq_mul_diagonal_of_mul_eq hHK g,
      ← Matrix.mul_assoc, hK, Matrix.zero_mul]
  have hB : A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ =
      A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * T * Tᴴ := by
    rw [Matrix.mul_sub, sub_eq_zero] at hGK
    rw [Matrix.mul_assoc _ Z, hGK, Matrix.mul_assoc _ T]
  rw [hB, ← hATT]
  refine (specNorm_le_iff (mul_nonneg ha (specNorm_nonneg _))).mpr fun x => ?_
  have hy (w : n → 𝕜) : Tᴴ *ᵥ (w - T *ᵥ (Tᴴ *ᵥ w)) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hT.conjTranspose_mul_self, Matrix.one_mulVec,
      sub_self]
  set w := Y *ᵥ x
  have hBx : ((A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * T * Tᴴ) * Y) *ᵥ x =
      A *ᵥ (cfc g (Aᴴ * A) *ᵥ (w - T *ᵥ (Tᴴ *ᵥ w))) := by
    simp only [w, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.mul_assoc,
      Matrix.sub_mulVec]
  have hAx : ((A - A * T * Tᴴ) * Y) *ᵥ x = A *ᵥ (w - T *ᵥ (Tᴴ *ᵥ w)) := by
    simp only [w, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.mul_assoc,
      Matrix.sub_mulVec]
  rw [hBx, mul_assoc]
  refine (norm_mulVec_cfc_mulVec_le A g h1 hHT hHV ha (fun _ => sq_nonneg _) (fun j => htail _
    ⟨sq_nonneg _, pow_le_pow_left₀ (singularValues_nonneg _ _) (he j) 2⟩) (hy w)).trans ?_
  rw [← hAx]
  exact mul_le_mul_of_nonneg_left (norm_toLp_mulVec_le _ x) ha

omit [DecidableEq m] in
/-- **Singular values of a filtered sketch, gap form**: let $g$ be a real function,
$\mathbf{Z}$ a frame (orthonormal columns) with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_t$ and
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
and $i < t$. If $\lvert g(\sigma_j(\mathbf{A})^2) \rvert \ge c > 0$ for $j \le i$ and
$\lvert g \rvert \le a$ on $[0, \sigma_t(\mathbf{A})^2]$, then
$$\sigma_i(\mathbf{A})^2 - \Bigl(\frac{a}{c}\Bigr)^2
\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t)\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2^2 \le
\sigma_i\bigl(\mathsf{rsvd}(\mathbf{A},
g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega})\bigr)^2\,.$$
It combines `IsStarProjection.sq_singularValues_sub_sq_specNorm_le` with the head capture
`NLAlib.HasOrthonormalCols.matrixNorm_one_sub_rangeProjector_mul_mul_le` of the filtered range
finder and the tail bound `NLAlib.specNorm_sub_mul_cfc_mul_mul_le`.
[MuscoMusco2015, Lemma 9]; property 1 there, for the Chebyshev filter and a Gaussian block with
probability $99/100$, here deterministic, for any filter, with the residual explicit. -/
theorem HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rsvd_cfc
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) {t : ℕ}
    (hAZ : A * Z * Zᴴ = truncatedSVD A t) {i : ℕ} (hi : i < t) {c a : ℝ} (hc : 0 < c)
    (hhead : ∀ j ≤ i, c ≤ |g (singularValues A j ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (singularValues A t ^ 2), |g x| ≤ a) :
    singularValues A i ^ 2 -
        (a / c) ^ 2 * specNorm ((A - truncatedSVD A t) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rsvd A (cfc g (Aᴴ * A) * Ω)) i ^ 2 := by
  classical
  set ρ := specNorm ((A - truncatedSVD A t) * Ω * pinv (Zᴴ * Ω))
  rcases (singularValues_nonneg A i).eq_or_lt with hσ | hσ
  · rw [← hσ]
    nlinarith [sq_nonneg (a / c * ρ), sq_nonneg (singularValues (rsvd A (cfc g (Aᴴ * A) * Ω)) i)]
  have hiN : i + 1 ≤ Fintype.card n :=
    ((singularValues_pos_iff A).mp hσ).trans_le A.rank_le_card_width
  obtain ⟨W, -, hW, -, -, -, hHW, -, htr⟩ :=
    exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal A hiN
  have hAWW : A * W * Wᴴ = truncatedSVD A (i + 1) := by simpa using htr (i + 1) le_rfl
  -- the frame `Z` contains the head frame `W`
  have hAZ' : truncatedSVD A (i + 1) * Z * Zᴴ = truncatedSVD A (i + 1) := by
    have hle := range_truncatedSVD_mono A (show i + 1 ≤ t by omega)
    have hRT := rangeProjector_truncatedSVD_mul A (i + 1)
    calc truncatedSVD A (i + 1) * Z * Zᴴ =
          rangeProjector (truncatedSVD A (i + 1)) * (A * Z * Zᴴ) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hRT]
      _ = rangeProjector (truncatedSVD A (i + 1)) * (rangeProjector (truncatedSVD A t) * A) := by
          rw [hAZ, rangeProjector_truncatedSVD_mul]
      _ = truncatedSVD A (i + 1) := by
          rw [← Matrix.mul_assoc, rangeProjector_mul_rangeProjector_of_range_le' hle, hRT]
  have hZW := mul_conjTranspose_mul_eq_of_truncatedSVD_mul hσ hW hHW hAWW hAZ'
  have hWZ : LinearMap.range W.mulVecLin ≤ LinearMap.range Z.mulVecLin :=
    range_le_iff_exists_mul.mpr ⟨Zᴴ * W, by rw [← Matrix.mul_assoc, hZW]⟩
  -- head capture, then the tail bound on the filtered residual
  have hcap := hW.matrixNorm_one_sub_rangeProjector_mul_mul_le (lpGauge ⊤) g hHW hZ hΩ hWZ hc
    fun j => hhead j (Nat.lt_succ_iff.mp j.isLt)
  rw [lpGauge_top_matrixNorm, lpGauge_top_matrixNorm, hAWW, Matrix.mul_assoc A] at hcap
  have hres := specNorm_sub_mul_cfc_mul_mul_le g hAZ htail (Ω * pinv (Zᴴ * Ω))
  simp only [← Matrix.mul_assoc] at hres
  have hP := (isStarProjection_rangeProjector
    (A * (cfc g (Aᴴ * A) * Ω))).sq_singularValues_sub_sq_specNorm_le A i
  have hb : specNorm ((1 - rangeProjector (A * (cfc g (Aᴴ * A) * Ω))) *
      truncatedSVD A (i + 1)) ≤ a / c * ρ := by
    refine hcap.trans ?_
    rw [div_eq_inv_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hres (inv_nonneg.mpr hc.le)
  have hb2 := pow_le_pow_left₀ (specNorm_nonneg _) hb 2
  rw [rsvd]
  nlinarith [hb2, hP, mul_pow (a / c) ρ 2]

/-- The scalar core of the cut form: with head weights $d_j \ge \sigma^2 \ge \tau^2$ where
$\lvert g \rvert \ge c$, tail weights $e_j \ge 0$ where $\lvert g \rvert \le a$ below $\tau^2$, and
a tail mass $\sum_j e_j v_j \le \rho^2 \sum_j u_j$, the weights $x g(x)^2$ have mass
at least $\sigma^2c^2\sum_j u_j$, and the Rayleigh quotient of $x \mapsto x^2 g(x)^2$ against
$x \mapsto x g(x)^2$ is at least $\tau^2 - (a/c)^2\rho^2$. -/
private theorem sq_sub_mul_sum_le_sum {p q : Type*} [Fintype p] [Fintype q] (g : ℝ → ℝ)
    {d u : p → ℝ} {e v : q → ℝ} {σ c a τ ρ : ℝ} (hc : 0 < c) (hτ : 0 ≤ τ) (hτσ : τ ≤ σ)
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) (hd : ∀ j, σ ^ 2 ≤ d j) (hdg : ∀ j, c ≤ |g (d j)|)
    (he : ∀ j, 0 ≤ e j) (heg : ∀ j, e j ≤ τ ^ 2 → |g (e j)| ≤ a)
    (hX : ∑ j, e j * v j ≤ ρ ^ 2 * ∑ j, u j) :
    σ ^ 2 * c ^ 2 * ∑ j, u j ≤
        ∑ j, g (d j) * d j * g (d j) * u j + ∑ j, g (e j) * e j * g (e j) * v j ∧
      (τ ^ 2 - (a / c) ^ 2 * ρ ^ 2) *
          (∑ j, g (d j) * d j * g (d j) * u j + ∑ j, g (e j) * e j * g (e j) * v j) ≤
        ∑ j, (d j * g (d j)) ^ 2 * u j + ∑ j, (e j * g (e j)) ^ 2 * v j := by
  have hσ0 : 0 ≤ σ := hτ.trans hτσ
  have hU : 0 ≤ ∑ j, u j := Finset.sum_nonneg fun j _ => hu j
  have hS1 : σ ^ 2 * c ^ 2 * ∑ j, u j ≤ ∑ j, g (d j) * d j * g (d j) * u j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hg2 : c ^ 2 ≤ g (d j) ^ 2 := by
      rw [← sq_abs (g (d j))]; exact pow_le_pow_left₀ hc.le (hdg j) 2
    have := mul_le_mul (hd j) hg2 (sq_nonneg c) ((sq_nonneg σ).trans (hd j))
    nlinarith [hu j]
  have hS2 : 0 ≤ ∑ j, g (e j) * e j * g (e j) * v j := by
    refine Finset.sum_nonneg fun j _ => ?_
    nlinarith [mul_nonneg (mul_nonneg (he j) (hv j)) (sq_nonneg (g (e j)))]
  have hK1 : τ ^ 2 * ∑ j, g (d j) * d j * g (d j) * u j ≤ ∑ j, (d j * g (d j)) ^ 2 * u j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hτd : τ ^ 2 ≤ d j := (pow_le_pow_left₀ hτ hτσ 2).trans (hd j)
    have h0 : 0 ≤ g (d j) ^ 2 * d j * u j :=
      mul_nonneg (mul_nonneg (sq_nonneg _) ((sq_nonneg σ).trans (hd j))) (hu j)
    nlinarith [mul_le_mul_of_nonneg_right hτd h0]
  have hK2 : τ ^ 2 * ∑ j, g (e j) * e j * g (e j) * v j - τ ^ 2 * a ^ 2 * ∑ j, e j * v j ≤
      ∑ j, (e j * g (e j)) ^ 2 * v j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have h0 : 0 ≤ e j * v j := mul_nonneg (he j) (hv j)
    rcases le_or_gt (e j) (τ ^ 2) with hle | hlt
    · have hga : g (e j) ^ 2 ≤ a ^ 2 := by
        rw [← sq_abs (g (e j))]
        exact pow_le_pow_left₀ (abs_nonneg _) (heg j hle) 2
      nlinarith [mul_le_mul_of_nonneg_left hga (mul_nonneg (sq_nonneg τ) h0),
        mul_nonneg (hv j) (sq_nonneg (e j * g (e j)))]
    · have h1 : 0 ≤ g (e j) ^ 2 * e j * v j := mul_nonneg (mul_nonneg (sq_nonneg _) (he j)) (hv j)
      nlinarith [mul_le_mul_of_nonneg_right hlt.le h1, mul_nonneg (mul_nonneg (sq_nonneg τ)
        (sq_nonneg a)) h0]
  have hac : (a / c) ^ 2 * c ^ 2 = a ^ 2 := by field_simp
  have step1 := mul_le_mul_of_nonneg_left hX (mul_nonneg (sq_nonneg τ) (sq_nonneg a))
  have step2 : a ^ 2 * ρ ^ 2 * τ ^ 2 * ∑ j, u j ≤ (a / c) ^ 2 * ρ ^ 2 *
      (∑ j, g (d j) * d j * g (d j) * u j + ∑ j, g (e j) * e j * g (e j) * v j) := by
    have hτσ2 : τ ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hτ hτσ 2
    have hw : 0 ≤ (a / c) ^ 2 * ρ ^ 2 := by positivity
    calc a ^ 2 * ρ ^ 2 * τ ^ 2 * ∑ j, u j ≤ a ^ 2 * ρ ^ 2 * σ ^ 2 * ∑ j, u j := by
          gcongr
      _ = (a / c) ^ 2 * ρ ^ 2 * (σ ^ 2 * c ^ 2 * ∑ j, u j) := by rw [← hac]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hw
  exact ⟨by linarith, by linarith⟩

omit [DecidableEq m] in
/-- The vector form of the cut bound: with a head frame $\mathbf{T}$ of the top $i + 1$ right
singular vectors (with $\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\mathbf{T} = \mathbf{T}$) and its
invariant complement $\mathbf{V}$, the sketched head vectors
$\mathbf{y} = \mathbf{A}g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\mathbf{Z}^{\mathsf{H}}\mathbf{T}\mathbf{t}$ satisfy
$\sigma_i^2c^2\|\mathbf{t}\|^2 \le \|\mathbf{y}\|^2$ and
$(\tau^2 - (a/c)^2\rho^2)\|\mathbf{y}\|^2 \le \|\mathbf{A}^{\mathsf{H}}\mathbf{y}\|^2$. -/
private theorem sq_sub_mul_norm_sq_le_norm_conjTranspose_mulVec_sq {q : Type*} [Fintype q]
    [DecidableEq q] {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) {i : ℕ}
    {T : Matrix n (Fin (i + 1)) 𝕜} {V : Matrix n q 𝕜} (hT : HasOrthonormalCols T)
    (hTV : Tᴴ * V = 0) (h1 : T * Tᴴ + V * Vᴴ = 1) {e : q → ℝ}
    (hHT : Aᴴ * A * T =
      T * Matrix.diagonal fun j : Fin (i + 1) => ((singularValues A j ^ 2 : ℝ) : 𝕜))
    (hHV : Aᴴ * A * V = V * Matrix.diagonal fun j => (e j : 𝕜)) (he : ∀ j, 0 ≤ e j)
    (hZT : Z * Zᴴ * T = T) {c a τ : ℝ} (hc : 0 < c) (hτ : 0 ≤ τ)
    (hτi : τ ≤ singularValues A i) (hhead : ∀ j ≤ i, c ≤ |g (singularValues A j ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (τ ^ 2), |g x| ≤ a) (t : Fin (i + 1) → 𝕜) :
    singularValues A i ^ 2 * c ^ 2 * ‖WithLp.toLp 2 t‖ ^ 2 ≤
        ‖WithLp.toLp 2 ((A * cfc g (Aᴴ * A) * (Ω * pinv (Zᴴ * Ω) * Zᴴ * T)) *ᵥ t)‖ ^ 2 ∧
      (τ ^ 2 - (a / c) ^ 2 * specNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2) *
          ‖WithLp.toLp 2 ((A * cfc g (Aᴴ * A) * (Ω * pinv (Zᴴ * Ω) * Zᴴ * T)) *ᵥ t)‖ ^ 2 ≤
        ‖WithLp.toLp 2 (Aᴴ *ᵥ ((A * cfc g (Aᴴ * A) * (Ω * pinv (Zᴴ * Ω) * Zᴴ * T)) *ᵥ t))‖ ^ 2 := by
  have hH : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  have hF : (cfc g (Aᴴ * A)).IsHermitian := cfc_predicate g (Aᴴ * A)
  set X := Ω * pinv (Zᴴ * Ω) * Zᴴ * T
  set ρ := specNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (Aᴴ * A)) := fun f =>
    (Aᴴ * A).finite_real_spectrum.continuousOn f
  have hZΩ := hZ.mul_pinv_self_of_rank_eq hΩ
  have hTZ : Tᴴ * (Z * Zᴴ) = Tᴴ := by
    have h := congrArg Matrix.conjTranspose hZT
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      at h
  have hZX : Z * Zᴴ * X = T := by
    calc Z * Zᴴ * X = Z * (Zᴴ * Ω * pinv (Zᴴ * Ω)) * Zᴴ * T := by simp only [X, Matrix.mul_assoc]
      _ = T := by rw [hZΩ, Matrix.mul_one, hZT]
  have hTX : Tᴴ * X = 1 := by
    rw [← hTZ, Matrix.mul_assoc, hZX, hT.conjTranspose_mul_self]
  have hVT : Vᴴ * T = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose (Vᴴ * T), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hTV, Matrix.conjTranspose_zero]
  have hAXT : A * (X - T) = (A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω) * (Zᴴ * T) := by
    conv_lhs => rw [← hZX]
    simp only [X, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  have hsa : IsSelfAdjoint (Aᴴ * A) := hH
  have hcY : cfc (fun x => g x * x * g x) (Aᴴ * A) =
      (cfc g (Aᴴ * A))ᴴ * (Aᴴ * A) * cfc g (Aᴴ * A) := by
    rw [cfc_mul (fun x => g x * x) g _ (hcont _) (hcont _),
      cfc_mul g (fun x => x) _ (hcont _) (hcont _), cfc_id' ℝ (Aᴴ * A) hsa, hF.eq]
  have hcK : cfc (fun x => x * g x) (Aᴴ * A) = Aᴴ * A * cfc g (Aᴴ * A) := by
    rw [cfc_mul (fun x => x) g _ (hcont _) (hcont _), cfc_id' ℝ (Aᴴ * A) hsa]
  -- coordinates of the sketched vector in the two frames
  set b := Vᴴ *ᵥ ((X - T) *ᵥ t)
  have hxT : Tᴴ *ᵥ (X *ᵥ t) = t := by rw [Matrix.mulVec_mulVec, hTX, Matrix.one_mulVec]
  have hxV : Vᴴ *ᵥ (X *ᵥ t) = b := by
    simp only [b, Matrix.mulVec_mulVec, Matrix.mul_sub, hVT, sub_zero]
  have hx'T : Tᴴ *ᵥ ((X - T) *ᵥ t) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, hTX, hT.conjTranspose_mul_self, sub_self,
      Matrix.zero_mulVec]
  have hy : (A * cfc g (Aᴴ * A) * X) *ᵥ t = A *ᵥ (cfc g (Aᴴ * A) *ᵥ (X *ᵥ t)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hAy : Aᴴ *ᵥ ((A * cfc g (Aᴴ * A) * X) *ᵥ t) =
      cfc (fun x => x * g x) (Aᴴ * A) *ᵥ (X *ᵥ t) := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hcK]
  -- the three quadratic forms in these coordinates
  have hq := hH.re_quadForm_cfc_eq_sum_add_sum h1 hHT hHV
  have hY := hq (fun x => g x * x * g x) (X *ᵥ t)
  rw [hcY, quadForm_conjTranspose_mul_mul, quadForm_conjTranspose_mul_self, RCLike.ofReal_re,
    ← hy, hxT, hxV] at hY
  have hK := hq (fun x => (x * g x) ^ 2) (X *ᵥ t)
  rw [← hH.norm_toLp_cfc_mulVec_sq, ← hAy, hxT, hxV] at hK
  have hE := hq (fun x => x) ((X - T) *ᵥ t)
  rw [cfc_id' ℝ (Aᴴ * A) hsa, quadForm_conjTranspose_mul_self, RCLike.ofReal_re, hx'T] at hE
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, Finset.sum_const_zero, zero_add] at hE
  have hEb : ‖WithLp.toLp 2 (A *ᵥ ((X - T) *ᵥ t))‖ ≤ ρ * ‖WithLp.toLp 2 t‖ := by
    rw [Matrix.mulVec_mulVec, hAXT]
    refine (norm_toLp_mulVec_le _ t).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (specNorm_mul_le _ _).trans (mul_le_of_le_one_right (specNorm_nonneg _)
      ((hZ.specNorm_conjTranspose_mul_le T).trans hT.specNorm_le_one))
  have ht : ‖WithLp.toLp 2 t‖ ^ 2 = ∑ j, ‖t j‖ ^ 2 := EuclideanSpace.norm_sq_eq _
  have hX : ∑ j, e j * ‖b j‖ ^ 2 ≤ ρ ^ 2 * ∑ j, ‖t j‖ ^ 2 := by
    rw [← hE, ← ht, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hEb 2
  obtain ⟨hs1, hs2⟩ := sq_sub_mul_sum_le_sum g (d := fun j : Fin (i + 1) => singularValues A j ^ 2)
    (u := fun j => ‖t j‖ ^ 2) (v := fun j => ‖b j‖ ^ 2) hc hτ hτi (fun _ => sq_nonneg _)
    (fun _ => sq_nonneg _)
    (fun j => pow_le_pow_left₀ (singularValues_nonneg A _)
      (singularValues_antitone A (Nat.lt_succ_iff.mp j.isLt)) 2)
    (fun j => hhead j (Nat.lt_succ_iff.mp j.isLt)) he (fun j h => htail _ ⟨he j, h⟩) hX
  rw [hY, hK, ht]
  exact ⟨hs1, hs2⟩

omit [DecidableEq m] in
/-- **Singular values of a filtered sketch, cut form**: let $g$ be a real function,
$\mathbf{Z}$ a frame (orthonormal columns) whose range contains the row space of
$\llbracket\mathbf{A}\rrbracket_{i+1}$, that is
$\llbracket\mathbf{A}\rrbracket_{i+1}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} =
\llbracket\mathbf{A}\rrbracket_{i+1}$, with
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
and let $0 \le \tau \le \sigma_i(\mathbf{A})$ be a cut. If
$\lvert g(\sigma_j(\mathbf{A})^2) \rvert \ge c > 0$ for $j \le i$ and $\lvert g \rvert \le a$ on
$[0, \tau^2]$, then
$$\tau^2 - \Bigl(\frac{a}{c}\Bigr)^2
\|(\mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2^2 \le
\sigma_i\bigl(\mathsf{rsvd}(\mathbf{A},
g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega})\bigr)^2\,.$$
The filter need not separate $\sigma_i$ from the singular values just below it: everything above
the cut $\tau$ counts as head, and the bound is for $\tau^2$, not $\sigma_i^2$.
[MuscoMusco2015, Lemma 9]; property 2 there, with the cut at $\sigma_{k+1}$ times a fixed factor
and probability $99/100$, here deterministic with the cut as a parameter. -/
theorem HasOrthonormalCols.sq_sub_le_sq_singularValues_rsvd_cfc_of_le_singularValues
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank) {i : ℕ}
    (hAZ : truncatedSVD A (i + 1) * Z * Zᴴ = truncatedSVD A (i + 1)) {c a τ : ℝ} (hc : 0 < c)
    (hτ : 0 ≤ τ) (hτi : τ ≤ singularValues A i)
    (hhead : ∀ j ≤ i, c ≤ |g (singularValues A j ^ 2)|)
    (htail : ∀ x ∈ Set.Icc 0 (τ ^ 2), |g x| ≤ a) :
    τ ^ 2 - (a / c) ^ 2 * specNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rsvd A (cfc g (Aᴴ * A) * Ω)) i ^ 2 := by
  classical
  set ρ := specNorm ((A - A * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))
  rcases le_or_gt (τ ^ 2 - (a / c) ^ 2 * ρ ^ 2) 0 with hneg | hpos
  · exact hneg.trans (sq_nonneg _)
  have hσ : 0 < singularValues A i := by
    rcases (singularValues_nonneg A i).eq_or_lt with h0 | h0
    · have hτ0 : τ = 0 := le_antisymm (h0 ▸ hτi) hτ
      rw [hτ0] at hpos
      nlinarith [sq_nonneg (a / c * ρ)]
    · exact h0
  have hiN : i + 1 ≤ Fintype.card n :=
    ((singularValues_pos_iff A).mp hσ).trans_le A.rank_le_card_width
  obtain ⟨T, V, hT, -, hTV, h1, hHT, hHV, htr⟩ :=
    exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal A hiN
  have hZT := mul_conjTranspose_mul_eq_of_truncatedSVD_mul hσ hT hHT
    (by simpa using htr (i + 1) le_rfl) hAZ
  -- the sketched head vectors
  set K := A * cfc g (Aᴴ * A) * (Ω * pinv (Zᴴ * Ω) * Zᴴ * T)
  have hv := fun t => sq_sub_mul_norm_sq_le_norm_conjTranspose_mulVec_sq g hZ hΩ hT hTV h1 hHT
    hHV (fun _ => sq_nonneg _) hZT hc hτ hτi hhead htail t
  have hinj : Function.Injective K.mulVec := by
    intro t₁ t₂ h12
    have h := (hv (t₁ - t₂)).1
    rw [Matrix.mulVec_sub, h12, sub_self, WithLp.toLp_zero, norm_zero,
      zero_pow two_ne_zero] at h
    have hn : ‖WithLp.toLp 2 (t₁ - t₂)‖ ^ 2 = 0 := le_antisymm
      (nonpos_of_mul_nonpos_right h (by positivity)) (sq_nonneg _)
    rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero, WithLp.toLp_eq_zero] at hn
    exact sub_eq_zero.mp hn
  have hrank : K.rank = i + 1 := by rw [mulVec_injective_iff_rank_eq.mp hinj, Fintype.card_fin]
  -- min–max for the conjugate transpose of the output, on the range of `K`
  have hPK : rangeProjector (A * (cfc g (Aᴴ * A) * Ω)) * K = K := by
    rw [rangeProjector_mul_eq_self_iff, range_le_iff_exists_mul]
    exact ⟨pinv (Zᴴ * Ω) * Zᴴ * T, by simp only [K, Matrix.mul_assoc]⟩
  have key : Real.sqrt (τ ^ 2 - (a / c) ^ 2 * ρ ^ 2) ≤
      singularValues (rsvd A (cfc g (Aᴴ * A) * Ω))ᴴ i := by
    refine le_singularValues_of_forall_mem _ (LinearMap.range K.mulVecLin) hrank.ge
      fun y hy => ?_
    obtain ⟨t, rfl⟩ := hy
    rw [Matrix.mulVecLin_apply, rsvd, Matrix.conjTranspose_mul,
      (isStarProjection_rangeProjector _).conjTranspose_eq,
      ← Matrix.mulVec_mulVec (M := Aᴴ) (N := rangeProjector (A * (cfc g (Aᴴ * A) * Ω))),
      Matrix.mulVec_mulVec (M := rangeProjector (A * (cfc g (Aᴴ * A) * Ω))) (N := K), hPK]
    refine (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp ?_
    rw [mul_pow, Real.sq_sqrt hpos.le]
    exact (hv t).2
  rw [← singularValues_conjTranspose]
  calc τ ^ 2 - (a / c) ^ 2 * ρ ^ 2 = Real.sqrt (τ ^ 2 - (a / c) ^ 2 * ρ ^ 2) ^ 2 :=
        (Real.sq_sqrt hpos.le).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) key 2

/-! ### Block Krylov iteration -/

omit [DecidableEq m] in
/-- **Singular values of block Krylov iteration, no gap**: let $\mathbf{Z}$ be a frame
(orthonormal columns) with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_k$ and
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
$q \ge 1$ and $0 < \gamma \le 1$. Then for every $i < k$,
$$\sigma_i(\mathbf{A})^2 - \gamma\,\sigma_k(\mathbf{A})^2 -
4e^{-2\sqrt{2}(q-1)\sqrt{\gamma}}\,
\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2^2 \le
\sigma_i\bigl(\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\bigr)^2\,.$$
No gap in the spectrum is assumed; $\gamma$ is a free parameter.
[BakshiClarksonWoodruff2022, Lemma 3.1]; [MuscoMusco2015, Theorem 12]; there for a Gaussian block
of $k$ columns, with probability $99/100$, depth $O(\log(d/\gamma)/\sqrt{\gamma})$ and
unspecified constants, here deterministic for any block, with the residual explicit. -/
theorem HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {k : ℕ} (hAZ : A * Z * Zᴴ = truncatedSVD A k) {q : ℕ}
    (hq : 1 ≤ q) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) {i : ℕ} (hi : i < k) :
    singularValues A i ^ 2 - γ * singularValues A k ^ 2 -
        4 * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt γ) *
          specNorm ((A - truncatedSVD A k) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rbki A Ω q) i ^ 2 := sorry

omit [DecidableEq m] in
/-- **Singular values of block Krylov iteration with a gap, per index**: let $r = h + 1 \le t$,
let $\mathbf{Z}$ be a frame (orthonormal columns) with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_t$ and
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
$q \ge 1$, and $\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$
(`NLAlib.singularGapRatio`). Then for every $i < r$,
$$\sigma_i(\mathbf{A})^2 - 4e^{-8(q-1)\sqrt{\gamma}}\,
\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t)\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2^2 \le
\sigma_i\bigl(\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\bigr)^2\,.$$
[BakshiClarksonWoodruff2022, Lemma 3.2]; [MuscoMusco2015, Theorem 13]; there for a Gaussian block
with probability $99/100$, depth $O(\log(n/\gamma)/\sqrt{\gamma'})$ in the gap
$\gamma' = \min(1, \sigma_k/\sigma_{b+1} - 1)$ and unspecified constants, here deterministic,
with a head count $r$ that may be smaller than the tail index. -/
theorem HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki_singularGapRatio
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {h r t : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (hAZ : A * Z * Zᴴ = truncatedSVD A t) {q : ℕ} (hq : 1 ≤ q) {i : ℕ} (hi : i < r) :
    singularValues A i ^ 2 -
        4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
          specNorm ((A - truncatedSVD A t) * Ω * pinv (Zᴴ * Ω)) ^ 2 ≤
      singularValues (rbki A Ω q) i ^ 2 := sorry

omit [DecidableEq m] in
/-- **Singular values of block Krylov iteration with a gap, summed**: let $r = h + 1 \le t$,
let $\mathbf{Z}$ be a frame (orthonormal columns) with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_t$ and
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
$q \ge 1$, and $\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$
(`NLAlib.singularGapRatio`). Then
$$\sum_{i<r} \Bigl(\sigma_i(\mathbf{A})^2 -
\sigma_i\bigl(\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\bigr)^2\Bigr) \le
4e^{-8(q-1)\sqrt{\gamma}}\,
\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t)\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_{\mathsf{F}}^2\,.$$
The sum of the $r$ deficits is bounded by the Frobenius norm of the residual, with no factor
$r$: the per-index bound
`NLAlib.HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki_singularGapRatio`
summed over $i < r$ would give $r$ times the spectral norm.
[MuscoMusco2015, Lemma 9]; property 1 there, with probability $99/100$ and unspecified
constants. -/
theorem HasOrthonormalCols.sum_sq_singularValues_sub_sq_singularValues_rbki_le
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {h r t : ℕ} (hr : h + 1 = r) (hrt : r ≤ t)
    (hAZ : A * Z * Zᴴ = truncatedSVD A t) {q : ℕ} (hq : 1 ≤ q) :
    ∑ i ∈ Finset.range r, (singularValues A i ^ 2 - singularValues (rbki A Ω q) i ^ 2) ≤
      4 * Real.exp (-8 * ((q : ℝ) - 1) * Real.sqrt (singularGapRatio A h t)) *
        frobNorm ((A - truncatedSVD A t) * Ω * pinv (Zᴴ * Ω)) ^ 2 := sorry

omit [DecidableEq m] in
/-- **The Frobenius error of one truncated run of block Krylov iteration, no gap**: let
$\mathbf{Z}$ be a frame (orthonormal columns) with
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}\rrbracket_k$ and
$\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$,
$q \ge 1$ and $0 < \gamma \le 1$. Then
$$\|\mathbf{A} - \llbracket\mathsf{rbki}(\mathbf{A}, \mathbf{\Omega}, q)\rrbracket_k
\|_{\mathsf{F}}^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 +
k\gamma\,\sigma_k(\mathbf{A})^2 + 4k\,e^{-2\sqrt{2}(q-1)\sqrt{\gamma}}\,
\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\|_2^2\,.$$
The sum over $i < k$ of
`NLAlib.HasOrthonormalCols.sq_singularValues_sub_le_sq_singularValues_rbki` in
`IsStarProjection.frobNorm_sub_truncatedSVD_mul_sq`. The term $k\gamma\,\sigma_k^2$ is compared
with the optimal error only through $\sigma_k^2 \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$, so this is not the
$(1 + \varepsilon)$ Frobenius bound of [MuscoMusco2015, Theorem 1] at depth
$O(\log d/\sqrt{\varepsilon})$. -/
theorem HasOrthonormalCols.frobNorm_sub_truncatedSVD_rbki_sq_le_add_mul
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Z : Matrix n s 𝕜} (hZ : HasOrthonormalCols Z)
    (hΩ : (Ωᴴ * Z).rank = Z.rank) {k : ℕ} (hAZ : A * Z * Zᴴ = truncatedSVD A k) {q : ℕ}
    (hq : 1 ≤ q) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    frobNorm (A - truncatedSVD (rbki A Ω q) k) ^ 2 ≤
      frobNorm (A - truncatedSVD A k) ^ 2 + k * γ * singularValues A k ^ 2 +
        4 * k * Real.exp (-2 * Real.sqrt 2 * ((q : ℝ) - 1) * Real.sqrt γ) *
          specNorm ((A - truncatedSVD A k) * Ω * pinv (Zᴴ * Ω)) ^ 2 := sorry

end NLAlib
