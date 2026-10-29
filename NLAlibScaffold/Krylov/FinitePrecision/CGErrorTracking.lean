/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.CGAccuracy

/-!
# The A-norm error of finite-precision CG tracks exact CG on the backward model

For a conjugate gradient run `C : NLAlib.CGRun n k` on a matrix with spectrum in $[a, a']$,
$a > 0$, $\kappa = a'/a$, under (H) $k^3\varepsilon\kappa^2 \le 10^{-5}$ and
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, write
$E_j = \|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}$ for the error of the computed iterates,
$\nu_{j,d} = \sum_{i=j}^{j+d-1}\gamma_i\|\mathbf{r}_i\|^2$
for the computed estimator and $u = \|\mathbf{b}\|^2/a$. Then, for $j + d \le k$,
$$\bigl\lvert(E_j^2 - E_{j+d}^2) - \nu_{j,d}\bigr\rvert \le 60\,k\varepsilon\kappa\,\nu_{j,d}
+ (36(j + d) + 16)\,d\,\varepsilon\kappa\,u \le 200\,k^2\varepsilon\kappa\,u ,$$
which is the statement of [StrakosTichy2002, Thm 10.1] with the $O(\varepsilon^2)$ terms kept and
no finite-precision monotonicity assumed. Since $\nu_{j,d}$ is exactly the decrement of the
error of exact CG on the backward model $\tilde{\mathbf{H}}$
(`NLAlib.CGRun.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate`), the
computed error decrements track those of the model, and the errors themselves agree up to the
model distance:
$$\bigl\lvert E_j^2 - \|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_j\|_{\tilde{\mathbf{H}}}^2
\bigr\rvert \le 10^5\,k^3\varepsilon\kappa^2\,u .$$
With $\nu_{0,j} = \|\mathbf{b}\|^2(\mathbf{T}_j^{-1})_{00}$, $E_j^2$ is the Gauss quadrature
error $\|\mathbf{x}_\star\|_{\mathbf{A}}^2 - \|\mathbf{b}\|^2(\mathbf{T}_j^{-1})_{00}$ of the
computed tridiagonal matrix up to $200k^2\varepsilon\kappa u$ [MeurantStrakos2006, §5.3].

The proof is an exact one-step identity
$E_j^2 - E_{j+1}^2 = \gamma_j\rho_j^2 + 2\gamma_j(\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j - \rho_j^2)
- (\gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j - \gamma_j\rho_j^2)
+ 2\gamma_j\mathbf{p}_j^{\mathsf{T}}\mathbf{g}_j + 2\mathbf{e}^{x\mathsf{T}}_j\mathbf{A}\mathbf{w}_j
- \|\mathbf{e}^x_j\|_{\mathbf{A}}^2$, $\mathbf{w}_j = \mathbf{x}_\star - \mathbf{x}_j -
\gamma_j\mathbf{p}_j$, whose first two error terms are relative to $\gamma_j\rho_j^2$ (line search
defect and curvature error) and whose last three are additive (residual gap, iterate update),
bounded with the a priori results of `NLAlib.CGRun.quadForm_sub_x_le`,
`NLAlib.CGRun.norm_x_le`, `NLAlib.CGRun.γ_mul_norm_p_le` and
`NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_norm_b`; then a sum over the steps.

Research branch `research/cg-error-tracking`. Design: `docs/design/research/Krylov-CGRounding.md`
(§9.4). Constants are unoptimised.

## Main results

* `NLAlib.CGRun.quadForm_sub_x_sub_quadForm_sub_x_succ_eq`: the exact one-step identity.
* `NLAlib.CGRun.abs_p_dotProduct_r_sub_sq_le`,
  `NLAlib.CGRun.abs_γ_sq_mul_dotProduct_mulVec_sub_le`: its relative error terms.
* `NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_sub_x_succ_sub_le`: one step, two-sided.
* `NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_sum_le`,
  `NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_sum_le_sq`: $d$ steps, the
  estimator.
* `NLAlib.CGRun.abs_quadForm_sub_x_sub_sub_sum_le`,
  `NLAlib.CGRun.abs_quadForm_sub_x_sub_sub_sum_le_quadForm`,
  `NLAlib.CGRun.abs_quadForm_sub_x_succ_sub_sub_inv_cgTridiagonal_le`: the error itself, against
  the estimator and the Gauss quadrature error.
* `NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_backwardH_le`,
  `NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_backwardH_sub_cgIterate_le`: against exact CG on
  the backward model.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-! ### Helpers (copies of the private helpers of `CGAccuracy.lean`) -/

private theorem trk_n_pos {n k : ℕ} (C : CGRun n k) : 0 < n := by
  by_contra h
  have h0 : C.r 0 = 0 := funext fun i => absurd i.2 (by omega)
  have := C.ρ_pos C.k_pos
  rw [ρ, h0, WithLp.toLp_zero, norm_zero] at this
  exact lt_irrefl _ this

private theorem trk_isHermitian : C.A.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, C.transpose_A]

private theorem trk_quadForm_eq (v : Fin n → ℝ) : quadForm C.A v = v ⬝ᵥ (C.A *ᵥ v) := by
  rw [quadForm_def, star_trivial]

private theorem trk_dotProduct_mulVec_comm (u v : Fin n → ℝ) :
    u ⬝ᵥ (C.A *ᵥ v) = v ⬝ᵥ (C.A *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, C.transpose_A, dotProduct_comm]

/-- The Rayleigh bounds of the matrix of the run. -/
private theorem trk_quadForm_bounds {a a' : ℝ} (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (v : Fin n → ℝ) :
    a * ‖WithLp.toLp 2 v‖ ^ 2 ≤ quadForm C.A v ∧ quadForm C.A v ≤ a' * ‖WithLp.toLp 2 v‖ ^ 2 := by
  have hH := C.trk_isHermitian
  have hpos := C.trk_n_pos
  obtain ⟨c, hc⟩ : ∃ c, c + 1 = Fintype.card (Fin n) := ⟨n - 1, by simp; omega⟩
  have h1 := hH.eigenvalue_last_mul_le_re_quadForm hc v
  have h2 := hH.re_quadForm_le_eigenvalue_zero_mul v
  simp only [RCLike.re_to_real] at h1 h2
  have e1 := (hH.spectrum_subset_iff.mp hs c (by omega)).1
  have e2 := (hH.spectrum_subset_iff.mp hs 0 (by simp; omega)).2
  have hx := sq_nonneg ‖WithLp.toLp 2 v‖
  exact ⟨(mul_le_mul_of_nonneg_right e1 hx).trans h1,
    h2.trans (mul_le_mul_of_nonneg_right e2 hx)⟩

private theorem trk_le {a a' : ℝ} (hs : spectrum ℝ C.A ⊆ Set.Icc a a') : a ≤ a' := by
  have e0 := C.trk_isHermitian.spectrum_subset_iff.mp hs 0 (by
    simp only [Fintype.card_fin]; exact C.trk_n_pos)
  exact e0.1.trans e0.2

/-- The elementary consequences of the spectral hypothesis and of (H). -/
private theorem trk_small {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    a ≤ a' ∧ 1 ≤ a' / a ∧ specNorm C.A ≤ a' ∧ C.ε ≤ 1 / 10 ^ 5 ∧
      (k : ℝ) * C.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧ (k : ℝ) ^ 2 * C.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧
      (k : ℝ) ^ 2 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
  have hn := C.trk_n_pos
  have hherm := C.trk_isHermitian
  have e0 := hherm.spectrum_subset_iff.mp hs 0 (by simp; omega)
  have e1 := hherm.spectrum_subset_iff.mp hs (n - 1) (by simp; omega)
  have haa' : a ≤ a' := e0.1.trans e0.2
  have hκ : 1 ≤ a' / a := (one_le_div ha).mpr haa'
  have hm : (1 : ℝ) ≤ k := by exact_mod_cast C.k_pos
  have hε := C.ε_nonneg
  have hspec : specNorm C.A ≤ a' := by
    have hc : n - 1 + 1 = Fintype.card (Fin n) := by simp; omega
    rw [hherm.specNorm_eq_max hc, abs_of_pos (ha.trans_le e0.1), abs_of_pos (ha.trans_le e1.1)]
    exact max_le e0.2 e1.2
  have hκ2 : a' / a ≤ (a' / a) ^ 2 := by nlinarith
  have hm2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hm3 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by nlinarith
  have hX : 0 ≤ C.ε * (a' / a) := by positivity
  have hY : 0 ≤ C.ε * (a' / a) ^ 2 := by positivity
  have h22 : (k : ℝ) ^ 2 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_right hm3 hY
    nlinarith
  have h2 : (k : ℝ) ^ 2 * C.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_left hκ2 (by positivity : 0 ≤ (k : ℝ) ^ 2 * C.ε)
    nlinarith
  have h1 : (k : ℝ) * C.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_right hm2 hX
    nlinarith
  have h0 : C.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_right hm hX
    nlinarith
  have he : C.ε ≤ 1 / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_left hκ hε
    nlinarith
  exact ⟨haa', hκ, hspec, he, h1, h2, h22⟩

private theorem trk_εκ {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) : C.ε * (a' / a) ≤ 1 / 10 ^ 5 := by
  obtain ⟨-, hκ, -, -, hkεκ, -, -⟩ := C.trk_small ha hs hsmall
  have h1k : (1 : ℝ) ≤ k := by exact_mod_cast C.k_pos
  have := mul_le_mul_of_nonneg_right h1k (by have := C.ε_nonneg; positivity :
    0 ≤ C.ε * (a' / a))
  nlinarith

/-- **The residual against the energy** for the matrix of the run:
$\|\mathbf{A}\mathbf{e}\|^2 \le a'\,\mathbf{e}^{\mathsf{T}}\mathbf{A}\mathbf{e}$
(Cauchy–Schwarz for the form of $\mathbf{A}$). -/
private theorem trk_norm_mulVec_sq_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (e : Fin n → ℝ) :
    ‖WithLp.toLp 2 (C.A *ᵥ e)‖ ^ 2 ≤ a' * quadForm C.A e := by
  have hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (C.A *ᵥ x) := fun x => by
    have := (C.trk_quadForm_bounds hs x).1
    rw [C.trk_quadForm_eq] at this
    exact le_trans (by positivity) this
  set v := C.A *ᵥ e with hv
  have hCS : (e ⬝ᵥ (C.A *ᵥ v)) ^ 2 ≤ (e ⬝ᵥ (C.A *ᵥ e)) * (v ⬝ᵥ (C.A *ᵥ v)) := by
    have hd := discrim_le_zero (a := v ⬝ᵥ (C.A *ᵥ v)) (b := 2 * (e ⬝ᵥ (C.A *ᵥ v)))
      (c := e ⬝ᵥ (C.A *ᵥ e)) (fun x => by
        have h := hpsd (e + x • v)
        have hc := C.trk_dotProduct_mulVec_comm v e
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
          smul_dotProduct, dotProduct_smul, smul_eq_mul] at h
        rw [hc] at h
        have : v ⬝ᵥ (C.A *ᵥ v) * (x * x) + 2 * (e ⬝ᵥ (C.A *ᵥ v)) * x + e ⬝ᵥ (C.A *ᵥ e) =
            e ⬝ᵥ (C.A *ᵥ e) + x * (e ⬝ᵥ (C.A *ᵥ v)) +
              x * (e ⬝ᵥ (C.A *ᵥ v) + x * (v ⬝ᵥ (C.A *ᵥ v))) := by
          ring
        linarith)
    unfold discrim at hd
    nlinarith
  have h1 : e ⬝ᵥ (C.A *ᵥ v) = ‖WithLp.toLp 2 v‖ ^ 2 := by
    rw [C.trk_dotProduct_mulVec_comm, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
  have h2 : v ⬝ᵥ (C.A *ᵥ v) ≤ a' * ‖WithLp.toLp 2 v‖ ^ 2 := by
    have := (C.trk_quadForm_bounds hs v).2
    rwa [C.trk_quadForm_eq] at this
  have he0 := hpsd e
  rw [h1] at hCS
  rw [C.trk_quadForm_eq]
  rcases (sq_nonneg ‖WithLp.toLp 2 v‖).lt_or_eq with hpos | hzero
  · have : (‖WithLp.toLp 2 v‖ ^ 2) ^ 2 ≤ (e ⬝ᵥ (C.A *ᵥ e)) * (a' * ‖WithLp.toLp 2 v‖ ^ 2) :=
      hCS.trans (mul_le_mul_of_nonneg_left h2 he0)
    nlinarith
  · rw [← hzero]
    have ha' : 0 ≤ a' := ha.le.trans (C.trk_le hs)
    positivity

private theorem trk_norm_sol_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 xs‖ ≤ ‖WithLp.toLp 2 C.b‖ / a := by
  have h1 := (C.trk_quadForm_bounds hs xs).1
  rw [C.trk_quadForm_eq, hx] at h1
  have h2 := (le_abs_self _).trans (EuclideanSpace.abs_dotProduct_le_norm xs C.b)
  rw [le_div_iff₀ ha]
  rcases (norm_nonneg (WithLp.toLp 2 xs)).lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]
    simp

private theorem trk_quadForm_sol_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    quadForm C.A xs ≤ ‖WithLp.toLp 2 C.b‖ ^ 2 / a := by
  have h := C.trk_norm_sol_le ha hs hx
  rw [C.trk_quadForm_eq, hx]
  refine (le_abs_self _).trans ((EuclideanSpace.abs_dotProduct_le_norm xs C.b).trans ?_)
  calc ‖WithLp.toLp 2 xs‖ * ‖WithLp.toLp 2 C.b‖ ≤
        ‖WithLp.toLp 2 C.b‖ / a * ‖WithLp.toLp 2 C.b‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖WithLp.toLp 2 C.b‖ ^ 2 / a := by ring

private theorem trk_quadForm_sol_ge {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 C.b‖ ^ 2 / a ≤ a' / a * quadForm C.A xs := by
  have h := C.trk_norm_mulVec_sq_le ha hs xs
  rw [hx] at h
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h ha.le

private theorem trk_norm_sq_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (v : Fin n → ℝ) : ‖WithLp.toLp 2 v‖ ^ 2 ≤ quadForm C.A v / a := by
  rw [le_div_iff₀ ha, mul_comm]
  exact (C.trk_quadForm_bounds hs v).1

/-- The smallness of step $j \le k$ under (H). -/
private theorem trk_small_j {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j ≤ k) :
    (j : ℝ) * C.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧ (j : ℝ) ^ 2 * C.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧
      (j : ℝ) ^ 2 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
  obtain ⟨-, hκ, -, -, hkεκ, hk2εκ, hk2εκ2⟩ := C.trk_small ha hs hsmall
  have hε0 := C.ε_nonneg
  have hjr : (j : ℝ) ≤ k := by exact_mod_cast hj
  have hj2 : (j : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hjr 2
  have hT0 : 0 ≤ C.ε * (a' / a) := by positivity
  have hT1 : 0 ≤ C.ε * (a' / a) ^ 2 := by positivity
  refine ⟨le_trans ?_ hkεκ, le_trans ?_ hk2εκ, le_trans ?_ hk2εκ2⟩
  · have := mul_le_mul_of_nonneg_right hjr hT0
    linarith
  · have := mul_le_mul_of_nonneg_right hj2 hT0
    linarith
  · have := mul_le_mul_of_nonneg_right hj2 hT1
    linarith


/-! ### One step -/

/-- **The exact one-step identity for the computed error**: for $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$ and $j < k$, with the gap $\mathbf{g}_j = \mathbf{b} - \mathbf{A}\mathbf{x}_j -
\mathbf{r}_j$ and $\mathbf{w}_j = \mathbf{x}_\star - \mathbf{x}_j - \gamma_j\mathbf{p}_j$,
$$E_j^2 - E_{j+1}^2 = \gamma_j\rho_j^2 + 2\gamma_j(\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j -
\rho_j^2) - (\gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j - \gamma_j\rho_j^2) +
2\gamma_j\mathbf{p}_j^{\mathsf{T}}\mathbf{g}_j + 2\,\mathbf{e}^{x\mathsf{T}}_j\mathbf{A}\mathbf{w}_j
- \|\mathbf{e}^x_j\|_{\mathbf{A}}^2 .$$
No smallness hypothesis: this is algebra on the iterate update
$\mathbf{x}_{j+1} = \mathbf{x}_j + \gamma_j\mathbf{p}_j + \mathbf{e}^x_j$ and
$\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_j) = \mathbf{r}_j + \mathbf{g}_j$
(the decomposition of the research note, §9.4).
Proof: expand $\|\mathbf{w}_j - \mathbf{e}^x_j\|_{\mathbf{A}}^2$. Difficulty: easy. -/
theorem quadForm_sub_x_sub_quadForm_sub_x_succ_eq {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b)
    {j : ℕ} (hj : j < k) :
    quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + 1)) =
      C.γ j * C.ρ j ^ 2 + 2 * C.γ j * (C.p j ⬝ᵥ C.r j - C.ρ j ^ 2) -
        (C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) - C.γ j * C.ρ j ^ 2) +
        2 * C.γ j * (C.p j ⬝ᵥ (C.b - C.A *ᵥ C.x j - C.r j)) +
        2 * (C.ex j ⬝ᵥ (C.A *ᵥ (xs - C.x j - C.γ j • C.p j))) - quadForm C.A (C.ex j) := by
  set e := xs - C.x j with he
  set w := e - C.γ j • C.p j with hw
  set v := C.ex j
  have hxe : xs - C.x (j + 1) = w - v := by
    rw [C.x_succ j hj, hw, he]
    abel
  have hAe : C.A *ᵥ e = C.r j + (C.b - C.A *ᵥ C.x j - C.r j) := by
    rw [he, Matrix.mulVec_sub, hx]
    abel
  have hexp : w ⬝ᵥ (C.A *ᵥ w) = e ⬝ᵥ (C.A *ᵥ e) - 2 * C.γ j * (C.p j ⬝ᵥ (C.A *ᵥ e)) +
      C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) := by
    rw [hw]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [C.trk_dotProduct_mulVec_comm e (C.p j)]
    ring
  have hexp2 : (w - v) ⬝ᵥ (C.A *ᵥ (w - v)) = w ⬝ᵥ (C.A *ᵥ w) - 2 * (v ⬝ᵥ (C.A *ᵥ w)) +
      v ⬝ᵥ (C.A *ᵥ v) := by
    simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
    rw [C.trk_dotProduct_mulVec_comm w v]
    ring
  have hpAe : C.p j ⬝ᵥ (C.A *ᵥ e) =
      C.p j ⬝ᵥ C.r j + C.p j ⬝ᵥ (C.b - C.A *ᵥ C.x j - C.r j) := by
    rw [hAe, dotProduct_add]
  rw [hxe, C.trk_quadForm_eq, C.trk_quadForm_eq, C.trk_quadForm_eq, hexp2, hexp, hpAe]
  ring

/-- **The line search defect, relative**: under (H), for $j < k$,
$\lvert\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j - \|\mathbf{r}_j\|^2\rvert \le
26\,k\varepsilon\kappa\,\|\mathbf{r}_j\|^2$. The two-sided form of
`NLAlib.CGRun.p_dotProduct_r_ge` with the $\varepsilon$-dependence kept.
Proof: as there, $\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j - \rho_j^2 =
\delta_{j-1}\mathbf{p}_{j-1}^{\mathsf{T}}\mathbf{r}_j + \mathbf{e}^{p\mathsf{T}}_{j-1}\mathbf{r}_j$
with `NLAlib.CGRun.abs_p_dotProduct_r_succ_le`. Difficulty: easy. -/
theorem abs_p_dotProduct_r_sub_sq_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {j : ℕ} (hj : j < k) :
    |C.p j ⬝ᵥ C.r j - C.ρ j ^ 2| ≤ 26 * k * C.ε * (a' / a) * C.ρ j ^ 2 := by
  obtain ⟨-, hκ, -, hε5, -, -, -⟩ := C.trk_small ha hs hsmall
  have hε0 := C.ε_nonneg
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast C.k_pos
  set κ := a' / a with hκdef
  have hP : ∀ i < k, ‖WithLp.toLp 2 (C.p i)‖ ≤ 2 * κ * C.ρ i := fun i hi => by
    have h := C.norm_p_sq_le ha hs hsmall hi
    have h2 : ‖WithLp.toLp 2 (C.p i)‖ ^ 2 ≤ (2 * κ * C.ρ i) ^ 2 := by
      have := C.ρ_nonneg i
      nlinarith [sq_nonneg (C.ρ i)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by have := C.ρ_nonneg i; positivity)
      two_ne_zero).mp h2
  have hK := fun i (hi : i < k) => C.specNorm_mul_γ_mul_norm_p_sq_le ha hs hsmall hi
  rcases j with _ | i
  · rw [C.p_zero, ← C.r_zero, ρ, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, sub_self,
      abs_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  · have hi : i < k := by omega
    have hτ := C.abs_p_dotProduct_r_succ_le hP hK hi
    obtain ⟨hδ0, hδ1, -⟩ := C.δ_bounds hi
    have hep := C.norm_ep_le' hi
    have hD := C.δ_mul_norm_p_le hi
    have hPi := hP (i + 1) hj
    have hid : C.p (i + 1) ⬝ᵥ C.r (i + 1) - C.ρ (i + 1) ^ 2 =
        C.δ i * (C.p i ⬝ᵥ C.r (i + 1)) + C.ep i ⬝ᵥ C.r (i + 1) := by
      rw [C.p_succ i hi, add_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul, ρ,
        EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
      ring
    rw [hid]
    set ρ1 := C.ρ (i + 1)
    have hρ1 : 0 ≤ ρ1 := C.ρ_nonneg _
    have hik : ((i : ℕ) + 1 : ℝ) ≤ k := by exact_mod_cast hj.le
    -- the line search term
    have hY : 5 * ((i : ℝ) + 1) * C.ε * (1 + 2 * κ + 21 / 20 * κ) ≤
        81 / 4 * ((k : ℝ) * C.ε * κ) := by
      have h1 : 1 + 2 * κ + 21 / 20 * κ ≤ 81 / 20 * κ := by linarith
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 5 * ((i : ℝ) + 1) * C.ε)
      have h4 : 5 * ((i : ℝ) + 1) * C.ε * (81 / 20 * κ) ≤ 5 * (k : ℝ) * C.ε * (81 / 20 * κ) := by
        gcongr
      nlinarith
    have hτ' : |C.p i ⬝ᵥ C.r (i + 1)| ≤ 81 / 4 * ((k : ℝ) * C.ε * κ) * C.ρ i ^ 2 := by
      refine hτ.trans ?_
      exact mul_le_mul_of_nonneg_right hY (sq_nonneg (C.ρ i))
    have hδτ : |C.δ i * (C.p i ⬝ᵥ C.r (i + 1))| ≤ 21 * ((k : ℝ) * C.ε * κ) * ρ1 ^ 2 := by
      rw [abs_mul, abs_of_nonneg hδ0]
      calc C.δ i * |C.p i ⬝ᵥ C.r (i + 1)| ≤
            C.δ i * (81 / 4 * ((k : ℝ) * C.ε * κ) * C.ρ i ^ 2) :=
            mul_le_mul_of_nonneg_left hτ' hδ0
        _ = 81 / 4 * ((k : ℝ) * C.ε * κ) * (C.δ i * C.ρ i ^ 2) := by ring
        _ ≤ 81 / 4 * ((k : ℝ) * C.ε * κ) * ((1 + 31 / 10 * C.ε) * ρ1 ^ 2) := by gcongr
        _ ≤ 21 * ((k : ℝ) * C.ε * κ) * ρ1 ^ 2 := by
            have : 81 / 4 * (1 + 31 / 10 * C.ε) ≤ 21 := by nlinarith
            have h := mul_le_mul_of_nonneg_right this (by positivity :
              0 ≤ (k : ℝ) * C.ε * κ * ρ1 ^ 2)
            nlinarith
    -- the direction update term
    have hepr : |C.ep i ⬝ᵥ C.r (i + 1)| ≤ 5 * ((k : ℝ) * C.ε * κ) * ρ1 ^ 2 := by
      refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans ?_
      have h1 : ‖WithLp.toLp 2 (C.ep i)‖ ≤ C.ε * (ρ1 + 21 / 20 * (2 * κ * ρ1 + ρ1)) := by
        refine hep.trans (mul_le_mul_of_nonneg_left ?_ hε0)
        linarith
      have h2 : C.ε * (ρ1 + 21 / 20 * (2 * κ * ρ1 + ρ1)) ≤ 5 * ((k : ℝ) * C.ε * κ) * ρ1 := by
        have e : C.ε * (ρ1 + 21 / 20 * (2 * κ * ρ1 + ρ1)) =
            ρ1 * (41 / 20 * C.ε + 21 / 10 * (C.ε * κ)) := by ring
        rw [e]
        have hεκ : C.ε ≤ C.ε * κ := le_mul_of_one_le_right hε0 hκ
        have hkεκ : C.ε * κ ≤ (k : ℝ) * C.ε * κ := by
          have := mul_le_mul_of_nonneg_right hk1 (by positivity : 0 ≤ C.ε * κ)
          linarith
        nlinarith
      calc ‖WithLp.toLp 2 (C.ep i)‖ * ‖WithLp.toLp 2 (C.r (i + 1))‖ ≤
            5 * ((k : ℝ) * C.ε * κ) * ρ1 * ρ1 := mul_le_mul_of_nonneg_right (h1.trans h2) hρ1
        _ = _ := by ring
    calc |C.δ i * (C.p i ⬝ᵥ C.r (i + 1)) + C.ep i ⬝ᵥ C.r (i + 1)| ≤
          |C.δ i * (C.p i ⬝ᵥ C.r (i + 1))| + |C.ep i ⬝ᵥ C.r (i + 1)| := abs_add_le _ _
      _ ≤ 26 * k * C.ε * κ * ρ1 ^ 2 := by nlinarith

/-- **The curvature error, relative**: under (H), for $j < k$,
$\lvert\gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j - \gamma_j\|\mathbf{r}_j\|^2\rvert
\le 6\,\varepsilon\kappa\,\gamma_j\|\mathbf{r}_j\|^2$. The two-sided form of
`NLAlib.CGRun.γ_sq_mul_dotProduct_mulVec_le` with the $\varepsilon$-dependence kept.
Proof: $\gamma_j\mu_j = \|\mathbf{r}_j\|^2(1 + \theta_j)(1 + \eta^\gamma_j)$ and
$\lvert\mu_j - \mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j\rvert \le
3\varepsilon\kappa\,\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j$. Difficulty: easy. -/
theorem abs_γ_sq_mul_dotProduct_mulVec_sub_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {j : ℕ} (hj : j < k) :
    |C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) - C.γ j * C.ρ j ^ 2| ≤
      6 * C.ε * (a' / a) * (C.γ j * C.ρ j ^ 2) := by
  obtain ⟨haa', hκ, hspec, hε5, -, -, -⟩ := C.trk_small ha hs hsmall
  have hε0 := C.ε_nonneg
  have hγ := C.γ_pos hj
  have hG2 := C.γ_sq_mul_dotProduct_mulVec_le ha hs hsmall hj
  set N := ‖WithLp.toLp 2 (C.p j)‖ with hN
  have hNn : 0 ≤ N := norm_nonneg _
  set P := C.p j ⬝ᵥ (C.A *ᵥ C.p j) with hPdef
  have hP0 : a * N ^ 2 ≤ P := by
    have := (C.trk_quadForm_bounds hs (C.p j)).1
    rwa [C.trk_quadForm_eq] at this
  have hP0' : 0 ≤ P := le_trans (by positivity) hP0
  have hμ : C.μ j = P + (C.p j ⬝ᵥ C.es j + C.eμ j) := by
    rw [C.μ_eq j hj, C.s_eq j hj, dotProduct_add]
    ring
  set t := C.p j ⬝ᵥ C.es j + C.eμ j with ht
  have h1 : |C.p j ⬝ᵥ C.es j| ≤ C.ε * a' * N ^ 2 := by
    refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans ?_
    have := C.norm_es_le j hj
    calc N * ‖WithLp.toLp 2 (C.es j)‖ ≤ N * (C.ε * specNorm C.A * N) :=
          mul_le_mul_of_nonneg_left this hNn
      _ ≤ N * (C.ε * a' * N) := by gcongr
      _ = _ := by ring
  have h2 : |C.eμ j| ≤ 2 * C.ε * a' * N ^ 2 := by
    refine (C.abs_eμ_le j hj).trans ?_
    have hs' := C.norm_s_le hj
    have : ‖WithLp.toLp 2 (C.s j)‖ ≤ 2 * a' * N := by
      refine hs'.trans ?_
      have : (1 + C.ε) * specNorm C.A ≤ 2 * a' := by nlinarith [specNorm_nonneg C.A]
      exact mul_le_mul_of_nonneg_right this hNn
    calc C.ε * N * ‖WithLp.toLp 2 (C.s j)‖ ≤ C.ε * N * (2 * a' * N) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have h3 : a' * N ^ 2 ≤ a' / a * P := by
    have := mul_le_mul_of_nonneg_left hP0 (by linarith : 0 ≤ a' / a)
    calc a' * N ^ 2 = a' / a * (a * N ^ 2) := by field_simp
      _ ≤ _ := this
  have htP : |t| ≤ 3 * (C.ε * (a' / a)) * P := by
    have h4 : C.ε * (a' * N ^ 2) ≤ C.ε * (a' / a * P) := mul_le_mul_of_nonneg_left h3 hε0
    calc |t| ≤ |C.p j ⬝ᵥ C.es j| + |C.eμ j| := abs_add_le _ _
      _ ≤ 3 * (C.ε * (a' / a)) * P := by nlinarith
  have hgm := C.γ_mul_μ hj
  rw [C.ν_eq' hj.le, hμ] at hgm
  have hθ := abs_le.mp (C.abs_θ_le j hj.le)
  have he := abs_le.mp (C.abs_eγ_le j hj)
  have hρ2 : 0 ≤ C.ρ j ^ 2 := sq_nonneg _
  -- `γP ≤ 1.001ρ²`
  have hγP : C.γ j * P ≤ (1 + 1 / 1000) * C.ρ j ^ 2 := by
    have : C.γ j * (C.γ j * P) ≤ C.γ j * ((1 + 1 / 1000) * C.ρ j ^ 2) := by
      calc C.γ j * (C.γ j * P) = C.γ j ^ 2 * P := by ring
        _ ≤ _ := hG2
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hγ
  have hγP0 : 0 ≤ C.γ j * P := by positivity
  have hεκ : C.ε ≤ C.ε * (a' / a) := le_mul_of_one_le_right hε0 hκ
  -- `|γP - ρ²| ≤ 6εκρ²`
  have hid : C.γ j * P - C.ρ j ^ 2 =
      C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j) - C.γ j * t := by
    have : C.γ j * P = C.γ j * (P + t) - C.γ j * t := by ring
    rw [this, hgm]
    ring
  have hθe : |C.θ j + C.eγ j + C.θ j * C.eγ j| ≤ 21 / 10 * C.ε := by
    rw [abs_le]
    constructor <;> nlinarith
  have hA : |C.γ j * P - C.ρ j ^ 2| ≤ 6 * C.ε * (a' / a) * C.ρ j ^ 2 := by
    rw [hid]
    have hγt : |C.γ j * t| ≤ 3 * (C.ε * (a' / a)) * (C.γ j * P) := by
      rw [abs_mul, abs_of_pos hγ]
      calc C.γ j * |t| ≤ C.γ j * (3 * (C.ε * (a' / a)) * P) :=
            mul_le_mul_of_nonneg_left htP hγ.le
        _ = _ := by ring
    have hρθ : |C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j)| ≤
        C.ρ j ^ 2 * (21 / 10 * C.ε) := by
      rw [abs_mul, abs_of_nonneg hρ2]
      exact mul_le_mul_of_nonneg_left hθe hρ2
    have hT0 : 0 ≤ C.ε * (a' / a) := le_trans hε0 hεκ
    have h5 : 3 * (C.ε * (a' / a)) * (C.γ j * P) ≤
        3 * (C.ε * (a' / a)) * ((1 + 1 / 1000) * C.ρ j ^ 2) :=
      mul_le_mul_of_nonneg_left hγP (by positivity)
    have h6 : C.ρ j ^ 2 * (21 / 10 * C.ε) ≤ 21 / 10 * (C.ε * (a' / a)) * C.ρ j ^ 2 := by
      nlinarith
    calc |C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j) - C.γ j * t| ≤
          |C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j)| + |C.γ j * t| := abs_sub _ _
      _ ≤ 6 * C.ε * (a' / a) * C.ρ j ^ 2 := by
          have : 0 ≤ C.ε * (a' / a) * C.ρ j ^ 2 := by positivity
          linarith
  have e : C.γ j ^ 2 * P - C.γ j * C.ρ j ^ 2 = C.γ j * (C.γ j * P - C.ρ j ^ 2) := by ring
  rw [e, abs_mul, abs_of_pos hγ]
  calc C.γ j * |C.γ j * P - C.ρ j ^ 2| ≤ C.γ j * (6 * C.ε * (a' / a) * C.ρ j ^ 2) :=
        mul_le_mul_of_nonneg_left hA hγ.le
    _ = _ := by ring

/-- **One step of the computed error, two-sided**: under (H), for $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$ and $j < k$,
$$\bigl\lvert(E_j^2 - E_{j+1}^2) - \gamma_j\|\mathbf{r}_j\|^2\bigr\rvert \le
60\,k\varepsilon\kappa\,\gamma_j\|\mathbf{r}_j\|^2 + (36j + 16)\,\varepsilon\kappa\,
\frac{\|\mathbf{b}\|^2}{a} .$$
The upper half sharpens `NLAlib.CGRun.quadForm_sub_x_succ_le` (factor $0.99$) to
$1 - 60k\varepsilon\kappa$; the lower half is new.
Proof: `NLAlib.CGRun.quadForm_sub_x_sub_quadForm_sub_x_succ_eq`; the relative terms by
`NLAlib.CGRun.abs_p_dotProduct_r_sub_sq_le` and
`NLAlib.CGRun.abs_γ_sq_mul_dotProduct_mulVec_sub_le`; the gap term by
$\gamma_j\|\mathbf{p}_j\| \le 1.5\|\mathbf{b}\|/a$ and $\|\mathbf{g}_j\| \le
12j\varepsilon\kappa\|\mathbf{b}\|$; the update terms by $\|\mathbf{e}^x_j\| \le
3.6\varepsilon\|\mathbf{b}\|/a$ (`NLAlib.CGRun.norm_x_le`) and $\|\mathbf{A}\mathbf{w}_j\|^2
\le a'\|\mathbf{w}_j\|_{\mathbf{A}}^2 \le 4a'\|\mathbf{b}\|^2/a$. Difficulty: moderate. -/
theorem abs_quadForm_sub_x_sub_quadForm_sub_x_succ_sub_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) :
    |quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + 1)) - C.γ j * C.ρ j ^ 2| ≤
      60 * k * C.ε * (a' / a) * (C.γ j * C.ρ j ^ 2) +
        (36 * j + 16) * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  sorry

/-! ### Several steps -/

/-- **The computed error decrement against the estimator ([StrakosTichy2002, Thm 10.1])**:
under (H), for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $j + d \le k$, with
$\nu_{j,d} = \sum_{i=j}^{j+d-1}\gamma_i\|\mathbf{r}_i\|^2$,
$$\bigl\lvert(E_j^2 - E_{j+d}^2) - \nu_{j,d}\bigr\rvert \le 60\,k\varepsilon\kappa\,\nu_{j,d} +
(36(j + d) + 16)\,d\,\varepsilon\kappa\,\frac{\|\mathbf{b}\|^2}{a} :$$
the estimator is accurate to relative accuracy $60k\varepsilon\kappa$ up to an additive term of
the size of the attainable accuracy. [StrakosTichy2002, Thm 10.1] has the same shape with the
$O(\varepsilon^2)$ terms dropped and the additive term in $\max_i\|\mathbf{x}_i\|$.
Proof: `NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_sub_x_succ_sub_le`, summed over
$i = j, \dots, j + d - 1$. Difficulty: easy. -/
theorem abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_sum_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j d : ℕ} (hjd : j + d ≤ k) :
    |quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + d)) -
        ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2| ≤
      60 * k * C.ε * (a' / a) * ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2 +
        (36 * (j + d) + 16) * d * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  sorry

/-- **The computed error decrement against the estimator, additive form**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $j + d \le k$,
$$\bigl\lvert(E_j^2 - E_{j+d}^2) - \nu_{j,d}\bigr\rvert \le 200\,k^2\varepsilon\kappa\,
\frac{\|\mathbf{b}\|^2}{a} .$$
Proof: `NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_sum_le` and
$\nu_{j,d} \le 2\|\mathbf{b}\|^2/a$ (`NLAlib.CGRun.sum_γ_mul_ρ_sq_le`). Difficulty: easy. -/
theorem abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_sum_le_sq {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j d : ℕ} (hjd : j + d ≤ k) :
    |quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + d)) -
        ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2| ≤
      200 * k ^ 2 * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  sorry

/-- **The computed error against the estimator**: under (H), for $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$ and $j \le k$,
$$\Bigl\lvert E_j^2 - \Bigl(\|\mathbf{x}_\star\|_{\mathbf{A}}^2 -
\sum_{i<j}\gamma_i\|\mathbf{r}_i\|^2\Bigr)\Bigr\rvert \le 200\,k^2\varepsilon\kappa\,
\frac{\|\mathbf{b}\|^2}{a} ,$$
the two-sided form of `NLAlib.CGRun.quadForm_sub_x_le_sub_sum` (which has $0.99$ and
$25j^2\varepsilon\kappa$, one-sided).
Proof: `NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_sum_le_sq` at $j = 0$,
$\mathbf{x}_0 = \mathbf{0}$. Difficulty: easy. -/
theorem abs_quadForm_sub_x_sub_sub_sum_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    |quadForm C.A (xs - C.x j) - (quadForm C.A xs - ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2)| ≤
      200 * k ^ 2 * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  sorry

/-- **The computed error against the estimator, relative to the initial error**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $j \le k$,
$$\Bigl\lvert E_j^2 - \Bigl(\|\mathbf{x}_\star\|_{\mathbf{A}}^2 -
\sum_{i<j}\gamma_i\|\mathbf{r}_i\|^2\Bigr)\Bigr\rvert \le 200\,k^2\varepsilon\kappa^2\,
\|\mathbf{x}_\star\|_{\mathbf{A}}^2 .$$
Proof: `NLAlib.CGRun.abs_quadForm_sub_x_sub_sub_sum_le` and
$\|\mathbf{b}\|^2/a \le \kappa\|\mathbf{x}_\star\|_{\mathbf{A}}^2$. Difficulty: easy. -/
theorem abs_quadForm_sub_x_sub_sub_sum_le_quadForm {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    |quadForm C.A (xs - C.x j) - (quadForm C.A xs - ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2)| ≤
      200 * k ^ 2 * C.ε * (a' / a) ^ 2 * quadForm C.A xs := by
  sorry

/-- **The computed error is a Gauss quadrature error**: under (H), for $\mathbf{A}\mathbf{x}_\star
= \mathbf{b}$ and $j + 1 \le k$, with $\mathbf{T}_{j+1}$ = `cgTridiagonal C.γ C.ρ (j + 1)`,
$$\bigl\lvert E_{j+1}^2 - \bigl(\|\mathbf{x}_\star\|_{\mathbf{A}}^2 -
\|\mathbf{b}\|^2(\mathbf{T}_{j+1}^{-1})_{00}\bigr)\bigr\rvert \le 200\,k^2\varepsilon\kappa\,
\frac{\|\mathbf{b}\|^2}{a} :$$
the exact-arithmetic identity [MeurantStrakos2006, (3.17)] holds for the computed run with the
computed $\mathbf{T}_{j+1}$, up to $200k^2\varepsilon\kappa\|\mathbf{b}\|^2/a$.
Proof: `NLAlib.CGRun.abs_quadForm_sub_x_sub_sub_sum_le` and
`NLAlib.sq_mul_inv_cgTridiagonal_zero_zero` with $\rho_0 = \|\mathbf{b}\|$. Difficulty: easy. -/
theorem abs_quadForm_sub_x_succ_sub_sub_inv_cgTridiagonal_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j + 1 ≤ k) :
    |quadForm C.A (xs - C.x (j + 1)) -
        (quadForm C.A xs - ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgTridiagonal C.γ C.ρ (j + 1))⁻¹ 0 0)| ≤
      200 * k ^ 2 * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  sorry

/-! ### Against exact CG on the backward model -/

/-- **The computed error decrements track those of the model**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\tilde{\mathbf{H}}\tilde{\mathbf{x}}_\star =
(\mathbf{b}, \mathbf{0}, \dots)$, $\tilde E_j = \|\tilde{\mathbf{x}}_\star -
\tilde{\mathbf{x}}_j\|_{\tilde{\mathbf{H}}}$ (exact CG on the model) and $j + d \le k$,
$$\bigl\lvert(E_j^2 - E_{j+d}^2) - (\tilde E_j^2 - \tilde E_{j+d}^2)\bigr\rvert \le
60\,k\varepsilon\kappa\,(\tilde E_j^2 - \tilde E_{j+d}^2) + (36(j + d) + 16)\,d\,\varepsilon\kappa\,
\frac{\|\mathbf{b}\|^2}{a} .$$
The model distance does not enter.
Proof: `NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_sum_le` and
`NLAlib.CGRun.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate`.
Difficulty: easy. -/
theorem abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_backwardH_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {xs' : Fin n × Fin (k + 1) → ℝ}
    (hxs' : C.backwardH *ᵥ xs' = C.dilatedRhs) {j d : ℕ} (hjd : j + d ≤ k) :
    |quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + d)) -
        (quadForm C.backwardH (xs' - cgIterate C.backwardH C.dilatedRhs 0 j) -
          quadForm C.backwardH (xs' - cgIterate C.backwardH C.dilatedRhs 0 (j + d)))| ≤
      60 * k * C.ε * (a' / a) *
          (quadForm C.backwardH (xs' - cgIterate C.backwardH C.dilatedRhs 0 j) -
            quadForm C.backwardH (xs' - cgIterate C.backwardH C.dilatedRhs 0 (j + d))) +
        (36 * (j + d) + 16) * d * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  sorry

/-- **The computed error tracks the error of exact CG on the model**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\tilde{\mathbf{H}}\tilde{\mathbf{x}}_\star =
(\mathbf{b}, \mathbf{0}, \dots)$ and $j \le k$,
$$\bigl\lvert\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 -
\|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_j\|_{\tilde{\mathbf{H}}}^2\bigr\rvert \le
10^5\,k^3\varepsilon\kappa^2\,\frac{\|\mathbf{b}\|^2}{a} .$$
The dominant part is the model distance of
`NLAlib.CGRun.abs_quadForm_backwardH_sub_quadForm_le` ($8 \cdot 10^4k^3\varepsilon\kappa^2$); the
tracking itself costs $200k^2\varepsilon\kappa$. Meaningful down to error level
$\sqrt{k^3\varepsilon\kappa^3}\,\|\mathbf{x}_\star\|_{\mathbf{A}}$; the decrement form
`NLAlib.CGRun.abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_backwardH_le` avoids the model distance.
Proof: `NLAlib.CGRun.abs_quadForm_sub_x_sub_sub_sum_le`, the model identity at $j$
(`NLAlib.CGRun.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate` from $0$)
and `NLAlib.CGRun.abs_quadForm_backwardH_sub_quadForm_le`. Difficulty: easy. -/
theorem abs_quadForm_sub_x_sub_quadForm_backwardH_sub_cgIterate_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {xs' : Fin n × Fin (k + 1) → ℝ}
    (hxs' : C.backwardH *ᵥ xs' = C.dilatedRhs) {j : ℕ} (hj : j ≤ k) :
    |quadForm C.A (xs - C.x j) -
        quadForm C.backwardH (xs' - cgIterate C.backwardH C.dilatedRhs 0 j)| ≤
      10 ^ 5 * k ^ 3 * C.ε * (a' / a) ^ 2 * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  sorry

end CGRun

end NLAlib
