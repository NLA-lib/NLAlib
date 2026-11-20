/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.EigenvalueBackward

/-!
# Conditioning of approximate eigenvectors

Let $\mathbf{M}$ be diagonalizable by $\mathbf{W}$ with $\kappa(\mathbf{W}) \le B$ and eigenvalues
at mutual distance at least $\Gamma > 0$ (`NLAlib.IsConditionedDiagonalizable`). If the columns of
$\mathbf{V}$ have norms in $[m, m']$, column residuals
$\|(\mathbf{M} - \mathrm{ev}_j\mathbf{I})\mathbf{v}_j\| \le \eta\|\mathbf{v}_j\|$ with
$8\sqrt N B\eta \le \Gamma$, and the values $\mathrm{ev}_j$ are $\Gamma/2$-separated, then
$\mathbf{V}$ is invertible with $\kappa(\mathbf{V}) \le \tfrac75\sqrt N B\, m'/m$. Each
$\mathrm{ev}_j$ is matched to its own eigenvalue by Bauer–Fike; in the eigenbasis each column is
one entry plus a small rest, and a Neumann series inverts the matrix of the rests. No hypothesis on
a gap of a triangular form is needed: a gap of $\mathbf{T}$ alone does not bound the conditioning.

## Main results

* `NLAlib.IsConditionedDiagonalizable.pseudoConditionNumber_le_of_residual`: the condition number
  of approximate eigenvectors of a matrix of the class.
* `NLAlib.isUnit_and_specNorm_inv_le_of_mul_norm_le`: a matrix bounded below is invertible.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix bounded below is invertible: if $c > 0$ and
$c\|\mathbf{x}\| \le \|\mathbf{V}\mathbf{x}\|$ for every $\mathbf{x}$, then $\mathbf{V}$ is
invertible and $\|\mathbf{V}^{-1}\|_2 \le c^{-1}$. -/
theorem isUnit_and_specNorm_inv_le_of_mul_norm_le {𝕜 : Type*} [RCLike 𝕜] {V : Matrix n n 𝕜}
    {c : ℝ} (hc : 0 < c) (h : ∀ x, c * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (V *ᵥ x)‖) :
    IsUnit V ∧ specNorm V⁻¹ ≤ c⁻¹ := by
  have hV : IsUnit V := by
    refine Matrix.mulVec_injective_iff_isUnit.mp fun x y hxy => ?_
    have h0 := h (x - y)
    rw [Matrix.mulVec_sub, hxy, sub_self, WithLp.toLp_zero, norm_zero] at h0
    have h1 : ‖WithLp.toLp 2 (x - y)‖ = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right h0 hc) (norm_nonneg _)
    rw [norm_eq_zero, WithLp.toLp_sub, sub_eq_zero] at h1
    exact WithLp.toLp_injective 2 h1
  refine ⟨hV, (specNorm_le_iff (inv_nonneg.2 hc.le)).2 fun x => ?_⟩
  have hx := h (V⁻¹ *ᵥ x)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det V).mp hV),
    Matrix.one_mulVec] at hx
  rw [inv_mul_eq_div, le_div_iff₀ hc]
  linarith

/-- The approximate eigenvalues are matched one to one with the eigenvalues: with
$8B\eta \le \Gamma$, each $\mathrm{ev}_j$ is within $B\eta$ of the eigenvalue $d_{\pi(j)}$ and at
distance at least $\tfrac78\Gamma$ from the others. -/
private theorem exists_equiv_le_norm_sub_of_residual {B Γ η m : ℝ} {M V W : Matrix n n ℂ}
    {d ev : n → ℂ} (hW : IsUnit W) (hMW : M * W = W * Matrix.diagonal d)
    (hB : pseudoConditionNumber W ≤ B) (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hΓ : 0 < Γ)
    (hBη : 8 * B * η ≤ Γ) (hm : 0 < m)
    (hcol : ∀ j, m ≤ ‖WithLp.toLp 2 (V.col j)‖)
    (hres : ∀ j, ‖WithLp.toLp 2 ((M - ev j • 1) *ᵥ V.col j)‖ ≤ η * ‖WithLp.toLp 2 (V.col j)‖)
    (hsep : ∀ i j, i ≠ j → Γ / 2 ≤ ‖ev i - ev j‖) :
    ∃ π : n ≃ n, ∀ j i, i ≠ π j → 7 / 8 * Γ ≤ ‖d i - ev j‖ := by
  have hB0 : 0 ≤ B := (pseudoConditionNumber_nonneg W).trans hB
  have hnear (j : n) : ∃ i, ‖d i - ev j‖ ≤ B * η := by
    have : Nonempty n := ⟨j⟩
    obtain ⟨i, hi⟩ := exists_norm_sub_mul_norm_le_pseudoConditionNumber_mul hW hMW (V.col j) (ev j)
    refine ⟨i, ?_⟩
    have hv : 0 < ‖WithLp.toLp 2 (V.col j)‖ := hm.trans_le (hcol j)
    have hr : M *ᵥ V.col j - ev j • V.col j = (M - ev j • 1) *ᵥ V.col j := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hr] at hi
    refine le_of_mul_le_mul_right ?_ hv
    calc ‖d i - ev j‖ * ‖WithLp.toLp 2 (V.col j)‖ ≤ _ := hi
      _ ≤ B * (η * ‖WithLp.toLp 2 (V.col j)‖) := mul_le_mul hB (hres j) (norm_nonneg _) hB0
      _ = _ := by ring
  choose π₀ hπ₀ using hnear
  have hinj : Function.Injective π₀ := by
    intro j k hjk
    by_contra hne
    have h2 := hπ₀ k
    rw [← hjk] at h2
    have h3 : ‖ev j - ev k‖ ≤ ‖d (π₀ j) - ev k‖ + ‖d (π₀ j) - ev j‖ := by
      calc ‖ev j - ev k‖ = ‖(d (π₀ j) - ev k) - (d (π₀ j) - ev j)‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    linarith [hsep j k hne, hπ₀ j]
  refine ⟨Equiv.ofBijective π₀ (Finite.injective_iff_bijective.mp hinj), fun j i hi => ?_⟩
  have h1 := hgap i (π₀ j) hi
  have h3 : ‖d i - d (π₀ j)‖ ≤ ‖d i - ev j‖ + ‖d (π₀ j) - ev j‖ := by
    calc ‖d i - d (π₀ j)‖ = ‖(d i - ev j) - (d (π₀ j) - ev j)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  linarith [hπ₀ j]

omit [Fintype n] in
/-- A vector is its entry at `p` plus the rest. -/
private theorem eq_single_add_update (c : n → ℂ) (p : n) :
    c = Pi.single p (c p) + Function.update c p 0 := by
  funext i
  by_cases hi : i = p
  · subst hi; simp
  · simp [hi]

/-- The rest of an eigenvector coordinate vector is bounded by its residual: for
$\mathbf{c} = \mathbf{W}^{-1}\mathbf{v}$ and $\lvert d_i - \mu\rvert \ge g$ off the index $p$,
$g\|\mathbf{c}_{\ne p}\| \le \|\mathbf{W}^{-1}\|_2\|(\mathbf{M} - \mu\mathbf{I})\mathbf{v}\|$. -/
private theorem mul_norm_update_le {M W : Matrix n n ℂ} {d : n → ℂ} {v : n → ℂ} {μ : ℂ} {p : n}
    {g : ℝ} (hW : IsUnit W) (hMW : M * W = W * Matrix.diagonal d) (hg : 0 ≤ g)
    (hfar : ∀ i, i ≠ p → g ≤ ‖d i - μ‖) :
    g * ‖WithLp.toLp 2 (Function.update (W⁻¹ *ᵥ v) p 0)‖ ≤
      specNorm W⁻¹ * ‖WithLp.toLp 2 ((M - μ • 1) *ᵥ v)‖ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det W).mp hW
  have hWM : W⁻¹ * M = Matrix.diagonal d * W⁻¹ := by
    calc W⁻¹ * M = W⁻¹ * (M * W) * W⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = _ := by
          rw [hMW, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have hr : W⁻¹ *ᵥ ((M - μ • 1) *ᵥ v) = fun i => (d i - μ) * (W⁻¹ *ᵥ v) i := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hWM, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_smul]
    funext i
    rw [Pi.sub_apply, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul,
      sub_mul]
  refine le_trans ?_ (hr ▸ norm_toLp_mulVec_le W⁻¹ ((M - μ • 1) *ᵥ v))
  rw [← EuclideanSpace.norm_toLp_norm (Function.update (W⁻¹ *ᵥ v) p 0),
    ← EuclideanSpace.norm_toLp_norm (fun i => (d i - μ) * (W⁻¹ *ᵥ v) i)]
  have hs (u : n → ℝ) : g * ‖WithLp.toLp 2 u‖ = ‖WithLp.toLp 2 (g • u)‖ := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hg]
  rw [hs]
  refine EuclideanSpace.norm_toLp_le_norm_toLp fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg hg, abs_norm]
  by_cases hi : i = p
  · subst hi; simp only [Function.update_self, norm_zero, mul_zero]; positivity
  · rw [Function.update_of_ne hi]
    exact mul_le_mul_of_nonneg_right (hfar i hi) (norm_nonneg _)

/-- One column in the eigenbasis: for $\mathbf{c} = \mathbf{W}^{-1}\mathbf{v}$ with
$\mathbf{M}\mathbf{W} = \mathbf{W}\operatorname{diag}(\mathbf{d})$, a residual
$\|(\mathbf{M} - \mu\mathbf{I})\mathbf{v}\| \le \eta\|\mathbf{v}\|$ and $\lvert d_i - \mu\rvert \ge
\tfrac78\Gamma$ off the index $p$, the entry $c_p$ carries $\tfrac67$ of $\mathbf{v}$ and the rest
of $\mathbf{c}$ is small. -/
private theorem col_bounds_of_residual {B Γ η : ℝ} {M W : Matrix n n ℂ} {d : n → ℂ}
    {v : n → ℂ} {μ : ℂ} {p : n} (hW : IsUnit W) (hMW : M * W = W * Matrix.diagonal d)
    (hκ : specNorm W * specNorm W⁻¹ ≤ B) (hΓ : 0 < Γ) (hη : 0 ≤ η)
    (hsmall : 8 * √(Fintype.card n : ℝ) * B * η ≤ Γ)
    (hres : ‖WithLp.toLp 2 ((M - μ • 1) *ᵥ v)‖ ≤ η * ‖WithLp.toLp 2 v‖)
    (hfar : ∀ i, i ≠ p → 7 / 8 * Γ ≤ ‖d i - μ‖) :
    6 / 7 * ‖WithLp.toLp 2 v‖ ≤ specNorm W * ‖(W⁻¹ *ᵥ v) p‖ ∧
      7 * √(Fintype.card n : ℝ) * specNorm W *
        ‖WithLp.toLp 2 (Function.update (W⁻¹ *ᵥ v) p 0)‖ ≤ ‖WithLp.toLp 2 v‖ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det W).mp hW
  have hN : 1 ≤ √(Fintype.card n : ℝ) := by
    have : Nonempty n := ⟨p⟩
    exact Real.one_le_sqrt.mpr (by exact_mod_cast Fintype.card_pos)
  have hf := mul_norm_update_le (v := v) hW hMW (by positivity : (0 : ℝ) ≤ 7 / 8 * Γ) hfar
  obtain ⟨f, hfdef⟩ : ∃ f, f = Function.update (W⁻¹ *ᵥ v) p 0 := ⟨_, rfl⟩
  rw [← hfdef] at hf ⊢
  have hf' : 7 * √(Fintype.card n : ℝ) * specNorm W * ‖WithLp.toLp 2 f‖ ≤
      ‖WithLp.toLp 2 v‖ := by
    refine le_of_mul_le_mul_left ?_ hΓ
    calc Γ * (7 * √(Fintype.card n : ℝ) * specNorm W * ‖WithLp.toLp 2 f‖)
        = 8 * √(Fintype.card n : ℝ) * specNorm W * (7 / 8 * Γ * ‖WithLp.toLp 2 f‖) := by ring
      _ ≤ 8 * √(Fintype.card n : ℝ) * specNorm W *
          (specNorm W⁻¹ * (η * ‖WithLp.toLp 2 v‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hf.trans (mul_le_mul_of_nonneg_left hres (specNorm_nonneg _))
      _ = 8 * √(Fintype.card n : ℝ) * (specNorm W * specNorm W⁻¹) * η *
          ‖WithLp.toLp 2 v‖ := by ring
      _ ≤ 8 * √(Fintype.card n : ℝ) * B * η * ‖WithLp.toLp 2 v‖ := by gcongr
      _ ≤ Γ * ‖WithLp.toLp 2 v‖ := by gcongr
  refine ⟨?_, hf'⟩
  have hv : ‖WithLp.toLp 2 v‖ ≤ specNorm W * (‖(W⁻¹ *ᵥ v) p‖ + ‖WithLp.toLp 2 f‖) := by
    have hWc : W *ᵥ (W⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    calc ‖WithLp.toLp 2 v‖ = ‖WithLp.toLp 2 (W *ᵥ (W⁻¹ *ᵥ v))‖ := by rw [hWc]
      _ ≤ specNorm W * ‖WithLp.toLp 2 (W⁻¹ *ᵥ v)‖ := norm_toLp_mulVec_le _ _
      _ ≤ specNorm W * (‖(W⁻¹ *ᵥ v) p‖ + ‖WithLp.toLp 2 f‖) := by
          gcongr
          conv_lhs => rw [eq_single_add_update (W⁻¹ *ᵥ v) p, ← hfdef]
          refine (EuclideanSpace.norm_toLp_add_le _ _).trans_eq ?_
          rw [PiLp.toLp_single, PiLp.norm_single]
  have ha : 0 ≤ specNorm W * ‖WithLp.toLp 2 f‖ := mul_nonneg (specNorm_nonneg _) (norm_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hN ha]

/-- A sum of single entries along a bijection is a relabelling. -/
private theorem norm_sum_single_equiv (π : n ≃ n) (y : n → ℂ) :
    ‖WithLp.toLp 2 (∑ j, (Pi.single (π j) (y j) : n → ℂ))‖ = ‖WithLp.toLp 2 y‖ := by
  have h : ∑ j, (Pi.single (π j) (y j) : n → ℂ) = y ∘ π.symm := by
    funext i
    simp only [Finset.sum_apply, Pi.single_apply, Function.comp_apply]
    simp_rw [← Equiv.symm_apply_eq]
    simp
  rw [h, EuclideanSpace.norm_toLp_comp_equiv]

omit [DecidableEq n] in
/-- The sum of the entries of a vector is at most $\sqrt N$ times its Euclidean norm. -/
private theorem sum_le_sqrt_card_mul_norm (w : n → ℝ) :
    ∑ j, w j ≤ √(Fintype.card n : ℝ) * ‖WithLp.toLp 2 w‖ := by
  have h := EuclideanSpace.abs_dotProduct_le_norm (fun _ => (1 : ℝ)) w
  rw [EuclideanSpace.norm_toLp_const, norm_one, mul_one] at h
  simpa [dotProduct] using (le_abs_self _).trans h

/-- The lower bound from the columns: if the columns $\mathbf{c}_j$ have the entry
$c_{\pi(j),j}$ with $\tfrac67\ell_j \le a\lvert c_{\pi(j),j}\rvert$ and a rest $\mathbf{f}_j$ with
$7\sqrt N a\|\mathbf{f}_j\| \le \ell_j$, $\ell_j \ge m \ge 0$, then
$\tfrac57m\|\mathbf{x}\| \le a\|\sum_jx_j\mathbf{c}_j\|$. -/
private theorem mul_norm_le_norm_sum_smul {a m : ℝ} {c : n → n → ℂ} {ℓ : n → ℝ} (π : n ≃ n)
    (hN : 0 < √(Fintype.card n : ℝ)) (hm : 0 ≤ m) (ha : 0 ≤ a) (hℓ : ∀ j, m ≤ ℓ j)
    (hmain : ∀ j, 6 / 7 * ℓ j ≤ a * ‖c j (π j)‖)
    (hrest : ∀ j, 7 * √(Fintype.card n : ℝ) * a *
      ‖WithLp.toLp 2 (Function.update (c j) (π j) 0)‖ ≤ ℓ j) (x : n → ℂ) :
    5 / 7 * m * ‖WithLp.toLp 2 x‖ ≤ a * ‖WithLp.toLp 2 (∑ j, x j • c j)‖ := by
  obtain ⟨w, hw⟩ : ∃ w : n → ℝ, w = fun j => ‖x j‖ * ℓ j := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : n → ℂ, S = ∑ j, Pi.single (π j) (x j * c j (π j)) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : n → ℂ, T = ∑ j, x j • Function.update (c j) (π j) 0 := ⟨_, rfl⟩
  have hsplit : ∑ j, x j • c j = S + T := by
    rw [hS, hT, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [eq_single_add_update (c j) (π j)]
    rw [smul_add]
    congr 1
    funext i
    by_cases hi : i = π j <;> simp [hi]
  have hS' : 6 / 7 * ‖WithLp.toLp 2 w‖ ≤ a * ‖WithLp.toLp 2 S‖ := by
    rw [hS, norm_sum_single_equiv, ← EuclideanSpace.norm_toLp_norm (fun j => x j * c j (π j))]
    rw [← Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 7), ← Real.norm_of_nonneg ha,
      ← norm_smul, ← norm_smul, ← WithLp.toLp_smul, ← WithLp.toLp_smul]
    refine EuclideanSpace.norm_toLp_le_norm_toLp fun j => ?_
    have hℓ0 : 0 ≤ ℓ j := hm.trans (hℓ j)
    simp only [hw, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_norm,
      abs_of_nonneg hℓ0, abs_of_nonneg ha, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6 / 7)]
    nlinarith [mul_le_mul_of_nonneg_left (hmain j) (norm_nonneg (x j))]
  have hT' : 7 * a * ‖WithLp.toLp 2 T‖ ≤ ‖WithLp.toLp 2 w‖ := by
    refine le_of_mul_le_mul_left ?_ hN
    calc √(Fintype.card n : ℝ) * (7 * a * ‖WithLp.toLp 2 T‖)
        ≤ ∑ j, ‖x j‖ * (7 * √(Fintype.card n : ℝ) * a *
            ‖WithLp.toLp 2 (Function.update (c j) (π j) 0)‖) := by
          rw [hT, WithLp.toLp_sum]
          calc √(Fintype.card n : ℝ) * (7 * a *
                ‖∑ j, WithLp.toLp 2 (x j • Function.update (c j) (π j) 0)‖)
              = 7 * √(Fintype.card n : ℝ) * a *
                ‖∑ j, WithLp.toLp 2 (x j • Function.update (c j) (π j) 0)‖ := by ring
            _ ≤ 7 * √(Fintype.card n : ℝ) * a *
                ∑ j, ‖WithLp.toLp 2 (x j • Function.update (c j) (π j) 0)‖ := by
                gcongr; exact norm_sum_le _ _
            _ = _ := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [WithLp.toLp_smul, norm_smul]; ring
      _ ≤ ∑ j, w j := by
          rw [hw]
          exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hrest j) (norm_nonneg _)
      _ ≤ _ := sum_le_sqrt_card_mul_norm w
  have hwx : m * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 w‖ := by
    rw [← EuclideanSpace.norm_toLp_norm x, ← Real.norm_of_nonneg hm, ← norm_smul,
      ← WithLp.toLp_smul]
    refine EuclideanSpace.norm_toLp_le_norm_toLp fun j => ?_
    simp only [hw, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_norm,
      abs_of_nonneg hm, abs_of_nonneg (hm.trans (hℓ j))]
    nlinarith [mul_le_mul_of_nonneg_left (hℓ j) (norm_nonneg (x j))]
  have htri : ‖WithLp.toLp 2 S‖ ≤ ‖WithLp.toLp 2 (S + T)‖ + ‖WithLp.toLp 2 T‖ := by
    calc ‖WithLp.toLp 2 S‖ = ‖WithLp.toLp 2 (S + T) - WithLp.toLp 2 T‖ := by
          rw [WithLp.toLp_add, add_sub_cancel_right]
      _ ≤ _ := norm_sub_le _ _
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left htri ha]

/-- **Approximate eigenvectors of a matrix of the class $(B, \Gamma)$ are well conditioned**: let
$\mathbf{M}$ be of the class $(B, \Gamma)$ with $\Gamma > 0$, $\eta \ge 0$,
$8\sqrt N B\eta \le \Gamma$ ($N$ the order), and let the columns of $\mathbf{V}$ have norms in
$[m, m']$ with $m > 0$ and residuals
$\|(\mathbf{M} - \mathrm{ev}_j\mathbf{I})\mathbf{v}_j\| \le \eta\|\mathbf{v}_j\|$, the
$\mathrm{ev}_j$ at mutual distance at least $\Gamma/2$. Then $\mathbf{V}$ is invertible,
$m\|\mathbf{V}^{-1}\|_2 \le \tfrac75 B$ and $\kappa(\mathbf{V}) \le \tfrac75\sqrt N B\,m'/m$.
No printed source. -/
theorem IsConditionedDiagonalizable.pseudoConditionNumber_le_of_residual
    {B Γ η m m' : ℝ} {M V : Matrix n n ℂ} {ev : n → ℂ}
    (hM : IsConditionedDiagonalizable B Γ M) (hΓ : 0 < Γ) (hη : 0 ≤ η)
    (hsmall : 8 * √(Fintype.card n : ℝ) * B * η ≤ Γ) (hm : 0 < m)
    (hcol : ∀ j, m ≤ ‖WithLp.toLp 2 (V.col j)‖ ∧ ‖WithLp.toLp 2 (V.col j)‖ ≤ m')
    (hres : ∀ j, ‖WithLp.toLp 2 ((M - ev j • 1) *ᵥ V.col j)‖ ≤ η * ‖WithLp.toLp 2 (V.col j)‖)
    (hsep : ∀ i j, i ≠ j → Γ / 2 ≤ ‖ev i - ev j‖) :
    IsUnit V ∧ m * specNorm V⁻¹ ≤ 7 / 5 * B ∧
      pseudoConditionNumber V ≤ 7 / 5 * √(Fintype.card n : ℝ) * B * (m' / m) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · obtain ⟨W, -, -, -, hB, -⟩ := hM
    have hB0 : 0 ≤ B := (pseudoConditionNumber_nonneg W).trans hB
    have hV0 : V⁻¹ = 0 := Subsingleton.elim _ _
    refine ⟨isUnit_of_subsingleton V, by rw [hV0, specNorm_zero, mul_zero]; positivity, ?_⟩
    rw [Subsingleton.elim V 0, pseudoConditionNumber_def, specNorm_zero, zero_mul]
    simp [Fintype.card_eq_zero]
  obtain ⟨W, d, hW, hMW, hB, hgap⟩ := hM
  have hN1 : 1 ≤ √(Fintype.card n : ℝ) :=
    Real.one_le_sqrt.mpr (by exact_mod_cast Fintype.card_pos)
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hW.ne_zero).trans hB
  have hκ : specNorm W * specNorm W⁻¹ ≤ B := by rwa [← pseudoConditionNumber_of_isUnit hW]
  have hBη : 8 * B * η ≤ Γ := le_trans (by
    have := mul_le_mul_of_nonneg_right hN1 (by positivity : (0 : ℝ) ≤ 8 * B * η)
    linarith) hsmall
  obtain ⟨π, hπ⟩ := exists_equiv_le_norm_sub_of_residual hW hMW hB hgap hΓ hBη hm
    (fun j => (hcol j).1) hres hsep
  have hc (j : n) := col_bounds_of_residual (v := V.col j) hW hMW hκ hΓ hη hsmall (hres j) (hπ j)
  have hlow (x : n → ℂ) : 5 * m / (7 * B) * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (V *ᵥ x)‖ := by
    have hsum : W⁻¹ *ᵥ (V *ᵥ x) = ∑ j, x j • (W⁻¹ *ᵥ V.col j) := by
      have hVx : V *ᵥ x = ∑ j, x j • V.col j := by
        funext i
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [hVx, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
    have h1 := mul_norm_le_norm_sum_smul π (by linarith) hm.le (specNorm_nonneg W)
      (fun j => (hcol j).1) (fun j => (hc j).1) (fun j => (hc j).2) x
    rw [← hsum] at h1
    have h2 : specNorm W * ‖WithLp.toLp 2 (W⁻¹ *ᵥ (V *ᵥ x))‖ ≤ B * ‖WithLp.toLp 2 (V *ᵥ x)‖ :=
      calc _ ≤ specNorm W * (specNorm W⁻¹ * ‖WithLp.toLp 2 (V *ᵥ x)‖) :=
            mul_le_mul_of_nonneg_left (norm_toLp_mulVec_le _ _) (specNorm_nonneg _)
        _ = specNorm W * specNorm W⁻¹ * ‖WithLp.toLp 2 (V *ᵥ x)‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hκ (norm_nonneg _)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨hVu, hinv⟩ := isUnit_and_specNorm_inv_le_of_mul_norm_le (by positivity) hlow
  have hinv' : specNorm V⁻¹ ≤ 7 * B / (5 * m) := by
    rwa [inv_div] at hinv
  have hm' : 0 ≤ m' := (norm_nonneg _).trans (hcol hn.some).2
  have hVn : specNorm V ≤ √(Fintype.card n : ℝ) * m' :=
    (specNorm_le_frobNorm V).trans
      (frobNorm_le_sqrt_card_mul_of_forall_norm_toLp_col_le fun j => (hcol j).2)
  refine ⟨hVu, ?_, ?_⟩
  · calc m * specNorm V⁻¹ ≤ m * (7 * B / (5 * m)) := mul_le_mul_of_nonneg_left hinv' hm.le
      _ = 7 / 5 * B := by field_simp
  · rw [pseudoConditionNumber_of_isUnit hVu]
    calc specNorm V * specNorm V⁻¹ ≤ (√(Fintype.card n : ℝ) * m') * (7 * B / (5 * m)) :=
          mul_le_mul hVn hinv' (specNorm_nonneg _) (by positivity)
      _ = _ := by field_simp

end NLAlib
