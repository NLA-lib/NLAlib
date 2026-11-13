/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.CGBackward

/-!
# The matrix of a CG run with spectrum in an interval

For a conjugate gradient run `C : NLAlib.CGRun n k` on a matrix with spectrum in $[a, a']$,
$a > 0$, $\kappa = a'/a$: the Rayleigh bounds of the energy
$\|\mathbf{v}\|_{\mathbf{A}}^2 = \mathbf{v}^{\mathsf{T}}\mathbf{A}\mathbf{v}$, the residual against
the energy, the energy of the exact step, the size of the solution of
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, and the elementary consequences of the smallness
hypothesis (H) $k^2\sqrt{k}\,\varepsilon\kappa^2 \le 10^{-5}$. These are the shared tools of
`CGAccuracy.lean` and `CGErrorTracking.lean`.

## Main results

* `NLAlib.CGRun.mul_norm_sq_le_quadForm`, `NLAlib.CGRun.quadForm_le_mul_norm_sq`: the Rayleigh
  bounds.
* `NLAlib.CGRun.norm_mulVec_sq_le_mul_quadForm`: the residual against the energy.
* `NLAlib.CGRun.quadForm_sub_eq`, `NLAlib.CGRun.quadForm_sub_x_sub_smul_p_eq`: the energy of a
  difference and of the exact step.
* `NLAlib.CGRun.norm_le_norm_b_div_of_mulVec_eq`,
  `NLAlib.CGRun.quadForm_le_norm_b_sq_div_of_mulVec_eq`,
  `NLAlib.CGRun.norm_b_sq_div_le_mul_quadForm_of_mulVec_eq`: the solution.
* `NLAlib.CGRun.le_of_sq_mul_sqrt_mul_ε_mul_sq_le`,
  `NLAlib.CGRun.le_of_sq_mul_sqrt_mul_ε_mul_sq_le_of_le`: the consequences of (H).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- For a nonempty symmetric matrix with spectrum in $[a,a']$, $a>0$, nonnegative
precision $\varepsilon$ and positive horizon $q$, the input-only condition
$q^2\sqrt q\varepsilon(a'/a)^2\le10^{-5}$ implies the curvature precision window
$3\varepsilon a'\le a$. This applies before constructing a CG run. -/
theorem _root_.Matrix.IsHermitian.three_mul_mul_le_of_cgPrecisionHorizon
    {N q : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (hn : 0 < N) (hq : 0 < q) {ε a a' : ℝ} (hε : 0 ≤ ε) (ha : 0 < a)
    (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon q ε (a' / a)) :
    3 * ε * a' ≤ a := by
  have he := hA.spectrum_subset_iff.mp hs 0 (by simpa using hn)
  have hκ : 1 ≤ a' / a := (one_le_div ha).mpr (he.1.trans he.2)
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hroot : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr hqr
  have hfactor : 1 ≤ (q : ℝ) ^ 2 * Real.sqrt q :=
    hq2.trans (le_mul_of_one_le_right (sq_nonneg _) hroot)
  have hε2 : 0 ≤ ε * (a' / a) ^ 2 := mul_nonneg hε (sq_nonneg _)
  have hκ2 : a' / a ≤ (a' / a) ^ 2 := by nlinarith
  have hεκ : ε * (a' / a) ≤ 1 / 10 ^ 5 := calc
    _ ≤ ε * (a' / a) ^ 2 := mul_le_mul_of_nonneg_left hκ2 hε
    _ ≤ (q : ℝ) ^ 2 * Real.sqrt q * ε * (a' / a) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hfactor hε2
      nlinarith
    _ ≤ _ := hsmall
  have hbudget : 3 * (ε * (a' / a)) ≤ 1 := by linarith
  have heq : (ε * (a' / a)) * a = ε * a' := by field_simp
  have := mul_le_mul_of_nonneg_right hbudget ha.le
  nlinarith

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-! ### The energy and the Rayleigh bounds -/

/-- The energy of $\mathbf{v}$ is $\mathbf{v}^{\mathsf{T}}\mathbf{A}\mathbf{v}$. -/
theorem quadForm_eq_dotProduct_mulVec (v : Fin n → ℝ) : quadForm C.A v = v ⬝ᵥ (C.A *ᵥ v) := by
  rw [quadForm_def, star_trivial]

private theorem acc_dotProduct_mulVec_comm (u v : Fin n → ℝ) :
    u ⬝ᵥ (C.A *ᵥ v) = v ⬝ᵥ (C.A *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, C.transpose_A, dotProduct_comm]

/-- The lower Rayleigh bound for the matrix of the run: with spectrum in $[a, a']$,
$a\|\mathbf{v}\|^2 \le \mathbf{v}^{\mathsf{T}}\mathbf{A}\mathbf{v}$. -/
theorem mul_norm_sq_le_quadForm {a a' : ℝ} (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (v : Fin n → ℝ) : a * ‖WithLp.toLp 2 v‖ ^ 2 ≤ quadForm C.A v := by
  have hH := C.isHermitian
  obtain ⟨c, hc⟩ : ∃ c, c + 1 = Fintype.card (Fin n) := ⟨n - 1, by simp; have := C.n_pos; omega⟩
  have h1 := hH.eigenvalue_last_mul_le_re_quadForm hc v
  simp only [RCLike.re_to_real] at h1
  have e1 := (hH.spectrum_subset_iff.mp hs c (by omega)).1
  exact (mul_le_mul_of_nonneg_right e1 (sq_nonneg _)).trans h1

/-- The upper Rayleigh bound for the matrix of the run: with spectrum in $[a, a']$,
$\mathbf{v}^{\mathsf{T}}\mathbf{A}\mathbf{v} \le a'\|\mathbf{v}\|^2$. -/
theorem quadForm_le_mul_norm_sq {a a' : ℝ} (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (v : Fin n → ℝ) : quadForm C.A v ≤ a' * ‖WithLp.toLp 2 v‖ ^ 2 := by
  have hH := C.isHermitian
  have hpos := C.n_pos
  have h2 := hH.re_quadForm_le_eigenvalue_zero_mul v
  simp only [RCLike.re_to_real] at h2
  have e2 := (hH.spectrum_subset_iff.mp hs 0 (by simp; omega)).2
  exact h2.trans (mul_le_mul_of_nonneg_right e2 (sq_nonneg _))

/-- The spectral interval is nonempty: $a \le a'$. -/
theorem le_of_spectrum_subset_Icc {a a' : ℝ} (hs : spectrum ℝ C.A ⊆ Set.Icc a a') : a ≤ a' := by
  have e0 := C.isHermitian.spectrum_subset_iff.mp hs 0 (by
    simp only [Fintype.card_fin]; exact C.n_pos)
  exact e0.1.trans e0.2

/-- The elementary consequences of the spectral hypothesis and of (H): with spectrum in
$[a, a']$, $a > 0$, $\kappa = a'/a$ and (H) $k^2\sqrt{k}\,\varepsilon\kappa^2 \le 10^{-5}$:
$a \le a'$, $1 \le \kappa$, $\|\mathbf{A}\|_2 \le a'$, $\varepsilon \le 10^{-5}$ and
$k\varepsilon\kappa$, $k^2\varepsilon\kappa$, $k^2\varepsilon\kappa^2 \le 10^{-5}$. -/
theorem le_of_sq_mul_sqrt_mul_ε_mul_sq_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) :
    a ≤ a' ∧ 1 ≤ a' / a ∧ specNorm C.A ≤ a' ∧ C.ε ≤ 1 / 10 ^ 5 ∧
      (k : ℝ) * C.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧ (k : ℝ) ^ 2 * C.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧
      (k : ℝ) ^ 2 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
  have hn := C.n_pos
  have hherm := C.isHermitian
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
  have hsqrt : 1 ≤ Real.sqrt k := Real.one_le_sqrt.mpr hm
  have hm3 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 * Real.sqrt k :=
    le_mul_of_one_le_right (sq_nonneg _) hsqrt
  have hX : 0 ≤ C.ε * (a' / a) := by positivity
  have hY : 0 ≤ C.ε * (a' / a) ^ 2 := by positivity
  have h22 : (k : ℝ) ^ 2 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
    have := mul_le_mul_of_nonneg_right hm3 hY
    unfold CGPrecisionHorizon at hsmall
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

/-- The residual against the energy for the matrix of the run:
$\|\mathbf{A}\mathbf{e}\|^2 \le a'\,\mathbf{e}^{\mathsf{T}}\mathbf{A}\mathbf{e}$
(Cauchy–Schwarz for the form of $\mathbf{A}$). -/
theorem norm_mulVec_sq_le_mul_quadForm {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (e : Fin n → ℝ) :
    ‖WithLp.toLp 2 (C.A *ᵥ e)‖ ^ 2 ≤ a' * quadForm C.A e := by
  have hpsd : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (C.A *ᵥ x) := fun x => by
    have := (C.mul_norm_sq_le_quadForm hs x)
    rw [C.quadForm_eq_dotProduct_mulVec] at this
    exact le_trans (by positivity) this
  set v := C.A *ᵥ e with hv
  have hCS : (e ⬝ᵥ (C.A *ᵥ v)) ^ 2 ≤ (e ⬝ᵥ (C.A *ᵥ e)) * (v ⬝ᵥ (C.A *ᵥ v)) := by
    have hd := discrim_le_zero (a := v ⬝ᵥ (C.A *ᵥ v)) (b := 2 * (e ⬝ᵥ (C.A *ᵥ v)))
      (c := e ⬝ᵥ (C.A *ᵥ e)) (fun x => by
        have h := hpsd (e + x • v)
        have hc := C.acc_dotProduct_mulVec_comm v e
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
    rw [C.acc_dotProduct_mulVec_comm, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
  have h2 : v ⬝ᵥ (C.A *ᵥ v) ≤ a' * ‖WithLp.toLp 2 v‖ ^ 2 := by
    have := (C.quadForm_le_mul_norm_sq hs v)
    rwa [C.quadForm_eq_dotProduct_mulVec] at this
  have he0 := hpsd e
  rw [h1] at hCS
  rw [C.quadForm_eq_dotProduct_mulVec]
  rcases (sq_nonneg ‖WithLp.toLp 2 v‖).lt_or_eq with hpos | hzero
  · have : (‖WithLp.toLp 2 v‖ ^ 2) ^ 2 ≤ (e ⬝ᵥ (C.A *ᵥ e)) * (a' * ‖WithLp.toLp 2 v‖ ^ 2) :=
      hCS.trans (mul_le_mul_of_nonneg_left h2 he0)
    nlinarith
  · rw [← hzero]
    have ha' : 0 ≤ a' := ha.le.trans (C.le_of_spectrum_subset_Icc hs)
    positivity
/-! ### The energy of the step -/

/-- The energy of a difference:
$\|\mathbf{u} - \mathbf{v}\|_{\mathbf{A}}^2 = \|\mathbf{u}\|_{\mathbf{A}}^2 -
2\,\mathbf{v}^{\mathsf{T}}\mathbf{A}\mathbf{u} + \|\mathbf{v}\|_{\mathbf{A}}^2$. -/
theorem quadForm_sub_eq (u v : Fin n → ℝ) :
    quadForm C.A (u - v) = quadForm C.A u - 2 * (v ⬝ᵥ (C.A *ᵥ u)) + quadForm C.A v := by
  simp only [C.quadForm_eq_dotProduct_mulVec, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
  rw [C.acc_dotProduct_mulVec_comm u v]
  ring

/-- The energy after the exact step, expanded: for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
with the gap $\mathbf{g}_j = \mathbf{b} - \mathbf{A}\mathbf{x}_j - \mathbf{r}_j$,
$$\|\mathbf{x}_\star - \mathbf{x}_j - \gamma_j\mathbf{p}_j\|_{\mathbf{A}}^2 =
\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 -
2\gamma_j\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j - 2\gamma_j\mathbf{p}_j^{\mathsf{T}}\mathbf{g}_j +
\gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j \,.$$ -/
theorem quadForm_sub_x_sub_smul_p_eq {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) (j : ℕ) :
    quadForm C.A (xs - C.x j - C.γ j • C.p j) = quadForm C.A (xs - C.x j) -
      2 * C.γ j * (C.p j ⬝ᵥ C.r j) - 2 * C.γ j * (C.p j ⬝ᵥ (C.b - C.A *ᵥ C.x j - C.r j)) +
        C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) := by
  set e := xs - C.x j with he
  have hpAe : C.p j ⬝ᵥ (C.A *ᵥ e) =
      C.p j ⬝ᵥ C.r j + C.p j ⬝ᵥ (C.b - C.A *ᵥ C.x j - C.r j) := by
    rw [← dotProduct_add, he, Matrix.mulVec_sub, hx]
    congr 1
    abel
  have hexp : (e - C.γ j • C.p j) ⬝ᵥ (C.A *ᵥ (e - C.γ j • C.p j)) = e ⬝ᵥ (C.A *ᵥ e) -
      2 * C.γ j * (C.p j ⬝ᵥ (C.A *ᵥ e)) + C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [C.acc_dotProduct_mulVec_comm e (C.p j)]
    ring
  rw [C.quadForm_eq_dotProduct_mulVec, C.quadForm_eq_dotProduct_mulVec, hexp, hpAe]
  ring

/-! ### The solution -/

/-- The solution against the right-hand side: with spectrum in $[a, a']$, $a > 0$, for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\|\mathbf{x}_\star\| \le \|\mathbf{b}\|/a$. -/
theorem norm_le_norm_b_div_of_mulVec_eq {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 xs‖ ≤ ‖WithLp.toLp 2 C.b‖ / a := by
  have h1 := (C.mul_norm_sq_le_quadForm hs xs)
  rw [C.quadForm_eq_dotProduct_mulVec, hx] at h1
  have h2 := (le_abs_self _).trans (EuclideanSpace.abs_dotProduct_le_norm xs C.b)
  rw [le_div_iff₀ ha]
  rcases (norm_nonneg (WithLp.toLp 2 xs)).lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]
    simp

/-- The energy of the solution, from above: with spectrum in $[a, a']$, $a > 0$, for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$\|\mathbf{x}_\star\|_{\mathbf{A}}^2 \le \|\mathbf{b}\|^2/a$. -/
theorem quadForm_le_norm_b_sq_div_of_mulVec_eq {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    quadForm C.A xs ≤ ‖WithLp.toLp 2 C.b‖ ^ 2 / a := by
  have h := C.norm_le_norm_b_div_of_mulVec_eq ha hs hx
  rw [C.quadForm_eq_dotProduct_mulVec, hx]
  refine (le_abs_self _).trans ((EuclideanSpace.abs_dotProduct_le_norm xs C.b).trans ?_)
  calc ‖WithLp.toLp 2 xs‖ * ‖WithLp.toLp 2 C.b‖ ≤
        ‖WithLp.toLp 2 C.b‖ / a * ‖WithLp.toLp 2 C.b‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖WithLp.toLp 2 C.b‖ ^ 2 / a := by ring

/-- The energy of the solution, from below: with spectrum in $[a, a']$, $a > 0$, for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$\|\mathbf{b}\|^2/a \le \kappa\,\|\mathbf{x}_\star\|_{\mathbf{A}}^2$. -/
theorem norm_b_sq_div_le_mul_quadForm_of_mulVec_eq {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 C.b‖ ^ 2 / a ≤ a' / a * quadForm C.A xs := by
  have h := C.norm_mulVec_sq_le_mul_quadForm ha hs xs
  rw [hx] at h
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h ha.le

/-! ### (H) at step $j$ -/

/-- The smallness of step $j \le k$ under (H): $j\varepsilon\kappa$, $j^2\varepsilon\kappa$,
$j^2\varepsilon\kappa^2 \le 10^{-5}$ (`NLAlib.CGRun.le_of_sq_mul_sqrt_mul_ε_mul_sq_le`). -/
theorem le_of_sq_mul_sqrt_mul_ε_mul_sq_le_of_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a)) {j : ℕ} (hj : j ≤ k) :
    (j : ℝ) * C.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧ (j : ℝ) ^ 2 * C.ε * (a' / a) ≤ 1 / 10 ^ 5 ∧
      (j : ℝ) ^ 2 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
  obtain ⟨-, hκ, -, -, hkεκ, hk2εκ, hk2εκ2⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
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

/-- For a successful run with spectrum in $[a,a']$, $a>0$ and
$k^2\sqrt{k}\varepsilon(a'/a)^2\le10^{-5}$, a nonzero residual after the last step implies
that the terminal search direction is nonzero. This derives the direction certificates from
the spectral and precision inputs; it does not assume a next-curvature test. -/
theorem p_ne_zero_of_r_ne_zero {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : CGPrecisionHorizon k C.ε (a' / a))
    (hr : C.r k ≠ 0) : C.p k ≠ 0 := by
  obtain ⟨-, hκ, -, -, hkεκ, -, -⟩ := C.le_of_sq_mul_sqrt_mul_ε_mul_sq_le ha hs hsmall
  have hε0 := C.ε_nonneg
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hwindow : (k : ℝ) * C.ε ≤ 1 / 100 := by
    have := mul_le_mul_of_nonneg_left hκ (mul_nonneg hk0 hε0)
    nlinarith
  have hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ (2 * (a' / a)) * C.ρ j := by
    intro j hj
    have h := C.norm_p_sq_le ha hs hsmall hj
    have hρ := C.ρ_nonneg j
    have hsq : ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ ((2 * (a' / a)) * C.ρ j) ^ 2 := by
      nlinarith [sq_nonneg (C.ρ j)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  have hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤
      (21 / 20 * (a' / a)) * C.ρ j ^ 2 := fun j hj =>
    C.specNorm_mul_γ_mul_norm_p_sq_le ha hs hsmall hj
  have hbudget : 20 * k * C.ε * (1 + 2 * (a' / a) + 21 / 20 * (a' / a)) ≤ 1 := by
    have hc : 1 + 2 * (a' / a) + 21 / 20 * (a' / a) ≤ 81 / 20 * (a' / a) := by linarith
    calc _ ≤ 20 * k * C.ε * (81 / 20 * (a' / a)) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 81 * ((k : ℝ) * C.ε * (a' / a)) := by ring
      _ ≤ 1 := by nlinarith
  have hnorm := C.norm_r_le_two_mul_norm_p hwindow hP hK hbudget
  intro hp
  rw [hp, WithLp.toLp_zero, norm_zero, mul_zero] at hnorm
  have hz : WithLp.toLp 2 (C.r k) = 0 := norm_eq_zero.mp
    (le_antisymm hnorm (norm_nonneg _))
  exact hr ((WithLp.toLp_eq_zero 2).mp hz)

end CGRun

end NLAlib
