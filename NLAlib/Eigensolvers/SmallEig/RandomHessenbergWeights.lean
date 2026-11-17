/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.RandomHessenbergRotations

/-!
# The eigenvector weights after the random Hessenberg form

The probabilistic half of `RHess` ([BanksGarzaVargasSrivastava2025, Proposition 5.3], corrected
for its errata P3 and P4): the drawn direction, a standard complex Gaussian vector, is nearly
orthogonal to a unit eigenvector of the input, fixed before the draw, or has a large norm, with
small probability (`NLAlib.SmallEig.measureReal_rhessBad_le`); off these windows the matrix that
`RHess` stores has a diagonalization of twice the condition, half the separation and every
last-row weight at least $s^2/(64R^2B^2)$ (`NLAlib.SmallEig.rhess_class`).

## Main definitions

* `NLAlib.SmallEig.winVec`, `NLAlib.SmallEig.unitCol`: the direction of a window and a unit
  column.
* `NLAlib.SmallEig.rhessBad`: the bad windows.

## Main results

* `NLAlib.SmallEig.measureReal_rhessBad_le`: their probability.
* `NLAlib.SmallEig.rhess_class`: the class and the weights off them.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

section Weights

/-- The complex vector of a window of $2N$ real draws, $(x_{2i} + i x_{2i+1})_{i < N}$
(`NLAlib.SmallEig.pairVector` on the window). -/
def winVec (N : ℕ) (x : Fin (N * 2) → ℝ) : Fin N → ℂ := fun i =>
  ⟨x ⟨2 * i, by have := i.isLt; omega⟩, x ⟨2 * i + 1, by have := i.isLt; omega⟩⟩

/-- The vector of a tape window is the direction the program draws. -/
theorem winVec_windowFn (N : ℕ) (τ : Tape ℝ) (s p : ℕ) :
    winVec N (Tape.windowFn τ s p (N * 2)) = pairVector (fun j => τ (p + j) s) N := rfl

/-- The entries of the vector of a window are measurable in the window. -/
private theorem measurable_winVec_apply (N : ℕ) (k : Fin N) :
    Measurable fun x => winVec N x k := by
  have hpair : Measurable fun v : ℝ × ℝ => (⟨v.1, v.2⟩ : ℂ) :=
    Complex.measurableEquivRealProd.symm.measurable
  exact hpair.comp (f := fun x => ((winVec N x k).re, (winVec N x k).im))
    ((measurable_pi_apply (⟨2 * k, by have := k.isLt; omega⟩ : Fin (N * 2))).prodMk
      (measurable_pi_apply (⟨2 * k + 1, by have := k.isLt; omega⟩ : Fin (N * 2))))

/-- The vector of a window has the Euclidean norm of the window. -/
theorem norm_winVec (N : ℕ) (x : Fin (N * 2) → ℝ) :
    ‖WithLp.toLp 2 (winVec N x)‖ = ‖WithLp.toLp 2 x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h0 : finProdFinEquiv (i, (0 : Fin 2)) = ⟨2 * i, by have := i.isLt; omega⟩ :=
    Fin.ext (by simp [finProdFinEquiv_apply_val])
  have h1 : finProdFinEquiv (i, (1 : Fin 2)) = ⟨2 * i + 1, by have := i.isLt; omega⟩ :=
    Fin.ext (by simp [finProdFinEquiv_apply_val]; ring)
  simp only [Fin.sum_univ_two, h0, h1, Real.norm_eq_abs, sq_abs,
    Complex.sq_norm, winVec, Complex.normSq_mk]
  ring

/-- A vector's norm is at most the spectral norm of its one-column matrix. -/
private theorem norm_le_specNorm_colMat {W : ℕ} (x : Fin W → ℝ) :
    ‖WithLp.toLp 2 x‖ ≤ specNorm (Matrix.of fun j (_ : Fin 1) => x j) := by
  have h := norm_toLp_mulVec_le (Matrix.of fun j (_ : Fin 1) => x j) (Pi.single 0 1)
  have e : (Matrix.of fun j (_ : Fin 1) => x j) *ᵥ Pi.single (0 : Fin 1) (1 : ℝ) = x := by
    ext j
    simp [Matrix.mulVec, dotProduct]
  rwa [e, PiLp.toLp_single, PiLp.norm_single, norm_one, mul_one] at h

/-- Cauchy–Schwarz for the inner product of complex vectors. -/
private theorem norm_star_dotProduct_le {N : ℕ} (a b : Fin N → ℂ) :
    ‖star a ⬝ᵥ b‖ ≤ ‖WithLp.toLp 2 a‖ * ‖WithLp.toLp 2 b‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 a) (WithLp.toLp 2 b)
  rwa [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h

/-- A column of an invertible matrix is not zero. -/
theorem norm_col_pos {N : ℕ} {V : Matrix (Fin N) (Fin N) ℂ} (hV : IsUnit V) (i : Fin N) :
    0 < ‖WithLp.toLp 2 (fun k => V k i)‖ := by
  refine norm_pos_iff.mpr fun h0 => ?_
  have hv : V *ᵥ Pi.single i (1 : ℂ) = 0 := by
    have := congrArg WithLp.ofLp h0
    ext k
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun this k
  have hdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have : (Pi.single i (1 : ℂ) : Fin N → ℂ) = 0 := by
    rw [← Matrix.one_mulVec (Pi.single i (1 : ℂ)), ← Matrix.nonsing_inv_mul V hdet,
      ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  simpa using congrFun this i

/-- The unit column $\mathbf{v}_i/\|\mathbf{v}_i\|$ of a matrix. -/
noncomputable def unitCol {N : ℕ} (V : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    Fin N → ℂ :=
  ((‖WithLp.toLp 2 (fun k => V k i)‖⁻¹ : ℝ) : ℂ) • fun k => V k i

private theorem norm_unitCol {N : ℕ} {V : Matrix (Fin N) (Fin N) ℂ} (hV : IsUnit V) (i : Fin N) :
    ‖WithLp.toLp 2 (unitCol V i)‖ = 1 := by
  rw [unitCol, WithLp.toLp_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg
    (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_col_pos hV i).ne']

/-- The bad windows of `RHess`: the direction is nearly orthogonal to a unit eigenvector of the
input (fixed before the draw), or the window has norm at least $R$. -/
def rhessBad {n : ℕ} (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s R : ℝ) :
    Set (Fin ((n + 1) * 2) → ℝ) :=
  (⋃ i, {x | ‖star (unitCol V i) ⬝ᵥ winVec (n + 1) x‖ ≤ s}) ∪ {x | R ≤ ‖WithLp.toLp 2 x‖}

/-- The bad windows are measurable. -/
theorem measurableSet_rhessBad {n : ℕ} (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (s R : ℝ) : MeasurableSet (rhessBad V s R) := by
  refine (MeasurableSet.iUnion fun i => measurableSet_le ?_ measurable_const).union
    (measurableSet_le measurable_const
      (continuous_norm.comp (PiLp.continuous_toLp 2 _)).measurable)
  refine continuous_norm.measurable.comp ?_
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun k _ => (measurable_winVec_apply (n + 1) k).const_mul _

/-- The probability of the bad windows of `RHess`: under independent standard real Gaussian
draws, for an invertible $\mathbf{V}$, $s > 0$, $0 < \varphi' \le 1$ and
$R \ge 2(\sqrt{n + 1} + 1) + \sqrt{2\log(1/\varphi')}$, the bad windows have probability at most
$(n + 1)s^2 + \varphi'$: anti-concentration in each fixed direction
(`NLAlib.measureReal_norm_dotProduct_le_le_of_hasLaw_complexGaussianVector`) and the norm tail
of a Gaussian vector (`NLAlib.measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix`). -/
theorem measureReal_rhessBad_le {n : ℕ} {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hV : IsUnit V) {s R φ' : ℝ} (hs : 0 < s) (hφ' : 0 < φ') (hφ'1 : φ' ≤ 1)
    (hR : 2 * (√((n : ℝ) + 1) + 1) + √(2 * Real.log φ'⁻¹) ≤ R) :
    (Measure.pi fun _ : Fin ((n + 1) * 2) => gaussianReal 0 1).real (rhessBad V s R) ≤
      (n + 1) * s ^ 2 + φ' := by
  set P := Measure.pi fun _ : Fin ((n + 1) * 2) => gaussianReal 0 1
  have hz := Computation.hasLaw_complexGaussianVector_pi_gaussianReal (n + 1)
  -- one direction
  have h1 : ∀ i, P.real {x | ‖star (unitCol V i) ⬝ᵥ winVec (n + 1) x‖ ≤ s} ≤ s ^ 2 := by
    intro i
    refine (measureReal_mono fun x (hx : _ ≤ s) => ?_).trans
      (measureReal_norm_dotProduct_le_le_of_hasLaw_complexGaussianVector hz (norm_unitCol hV i)
        hs.le)
    have e : winVec (n + 1) x = ((√2 : ℝ) : ℂ) • fun i : Fin (n + 1) =>
        (⟨x ⟨2 * i, by have := i.isLt; omega⟩ / √2,
          x ⟨2 * i + 1, by have := i.isLt; omega⟩ / √2⟩ : ℂ) := by
      ext k
      apply Complex.ext <;> simp [winVec] <;> field_simp
    rw [e, dotProduct_smul, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hx
    change _ ≤ s
    have h2 : (1 : ℝ) ≤ √2 := Real.one_le_sqrt.mpr (by norm_num)
    nlinarith [norm_nonneg (star (unitCol V i) ⬝ᵥ fun i : Fin (n + 1) =>
        (⟨x ⟨2 * i, by have := i.isLt; omega⟩ / √2,
          x ⟨2 * i + 1, by have := i.isLt; omega⟩ / √2⟩ : ℂ))]
  -- the norm
  have hL : 0 ≤ Real.log φ'⁻¹ := Real.log_nonneg ((one_le_inv₀ hφ').mpr hφ'1)
  have h2 : P.real {x | R ≤ ‖WithLp.toLp 2 x‖} ≤ φ' := by
    have h := measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix
      (Computation.hasLaw_gaussianMatrix_pi_gaussianReal ((n + 1) * 2))
      (Real.sqrt_nonneg (2 * Real.log φ'⁻¹))
    rw [Real.sq_sqrt (by positivity), show -(2 * Real.log φ'⁻¹) / 2 = -Real.log φ'⁻¹ by ring,
      Real.exp_neg, Real.exp_log (inv_pos.mpr hφ'), inv_inv] at h
    refine (measureReal_mono fun x (hx : R ≤ _) => ?_).trans h
    simp only [Set.mem_ofPred_eq]
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      Real.sqrt_one]
    have hs2 : √(((n : ℝ) + 1) * 2) ≤ 2 * √((n : ℝ) + 1) := by
      rw [Real.sqrt_mul (by positivity), mul_comm]
      have : √(2 : ℝ) ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num
      exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
    have := norm_le_specNorm_colMat x
    linarith
  refine (measureReal_union_le _ _).trans ?_
  have hU := measureReal_iUnion_fintype_le (μ := P)
    fun i => {x | ‖star (unitCol V i) ⬝ᵥ winVec (n + 1) x‖ ≤ s}
  have hS : ∑ i : Fin (n + 1), P.real {x | ‖star (unitCol V i) ⬝ᵥ winVec (n + 1) x‖ ≤ s} ≤
      (n + 1) * s ^ 2 := by
    refine (Finset.sum_le_sum fun i _ => h1 i).trans (le_of_eq ?_)
    simp
  linarith

end Weights

section Class

/-- The overlap of the computed direction: if a column $\mathbf{v}$ has
$\lvert\mathbf{g}^{\mathsf{H}}\mathbf{v}\rvert \ge s\|\mathbf{v}\|$, $0 < \|\mathbf{g}\| \le R$
and $\mathbf{q}$ is within $s/(2R)$ of a unit multiple of $\mathbf{g}/\|\mathbf{g}\|$, then
$\lvert\mathbf{q}^{\mathsf{H}}\mathbf{v}\rvert \ge (s/(2R))\|\mathbf{v}\|$. -/
theorem le_norm_star_dotProduct_of_near {N : ℕ} {q gv v : Fin N → ℂ} {c : ℂ} {s R : ℝ}
    (hc : ‖c‖ = 1) (hs : 0 ≤ s) (hR : 0 < R) (hg0 : 0 < ‖WithLp.toLp 2 gv‖)
    (hgR : ‖WithLp.toLp 2 gv‖ ≤ R)
    (hgi : s * ‖WithLp.toLp 2 v‖ ≤ ‖star gv ⬝ᵥ v‖)
    (hq : ‖WithLp.toLp 2 (q - (c * ((‖WithLp.toLp 2 gv‖⁻¹ : ℝ) : ℂ)) • gv)‖ ≤ s / (2 * R)) :
    s / (2 * R) * ‖WithLp.toLp 2 v‖ ≤ ‖star q ⬝ᵥ v‖ := by
  set a : ℂ := c * ((‖WithLp.toLp 2 gv‖⁻¹ : ℝ) : ℂ)
  set r := q - a • gv
  have hq' : q = a • gv + r := by simp [r]
  have ha : ‖a‖ = ‖WithLp.toLp 2 gv‖⁻¹ := by
    rw [norm_mul, hc, one_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hg0.le)]
  have h1 : ‖star (a • gv) ⬝ᵥ v‖ = ‖WithLp.toLp 2 gv‖⁻¹ * ‖star gv ⬝ᵥ v‖ := by
    rw [star_smul, smul_dotProduct, smul_eq_mul, norm_mul, norm_star, ha]
  have h2 : ‖star r ⬝ᵥ v‖ ≤ s / (2 * R) * ‖WithLp.toLp 2 v‖ :=
    (norm_star_dotProduct_le r v).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
  have h3 : s / R * ‖WithLp.toLp 2 v‖ ≤ ‖WithLp.toLp 2 gv‖⁻¹ * ‖star gv ⬝ᵥ v‖ := by
    rw [inv_mul_eq_div, le_div_iff₀ hg0]
    have hs0 : 0 ≤ s * ‖WithLp.toLp 2 v‖ := mul_nonneg hs (norm_nonneg _)
    calc s / R * ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 gv‖
        = s * ‖WithLp.toLp 2 v‖ * (‖WithLp.toLp 2 gv‖ / R) := by ring
      _ ≤ s * ‖WithLp.toLp 2 v‖ * 1 :=
        mul_le_mul_of_nonneg_left ((div_le_one hR).mpr hgR) hs0
      _ ≤ ‖star gv ⬝ᵥ v‖ := by rw [mul_one]; exact hgi
  have h4 : ‖star (a • gv) ⬝ᵥ v‖ ≤ ‖star q ⬝ᵥ v‖ + ‖star r ⬝ᵥ v‖ := by
    have e : star (a • gv) ⬝ᵥ v = star q ⬝ᵥ v - star r ⬝ᵥ v := by
      rw [hq', star_add, add_dotProduct]
      ring
    rw [e]
    exact norm_sub_le _ _
  have e2 : s / R * ‖WithLp.toLp 2 v‖ =
      s / (2 * R) * ‖WithLp.toLp 2 v‖ + s / (2 * R) * ‖WithLp.toLp 2 v‖ := by
    field_simp
    ring
  linarith

/-- The weight of a column with a large overlap with the last column of a unitary
$\mathbf{Q}$: if $\lvert\mathbf{q}^{\mathsf{H}}\mathbf{v}_i\rvert \ge (s/(2R))\|\mathbf{v}_i\|$
and $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$, then
$\sqrt{w_i(\mathbf{Q}^{\mathsf{H}}\mathbf{V})} \ge s/(2RB)$
(`NLAlib.le_lastRowWeights_conjTranspose_mul`). -/
private theorem half_le_sqrt_lastRowWeights {n : ℕ} {V Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {B s R : ℝ} (hV : IsUnit V) (hκ : pseudoConditionNumber V ≤ B) (hs : 0 < s) (hR : 0 < R)
    (hQ : HasOrthonormalCols Q) {i : Fin (n + 1)}
    (hqv : s / (2 * R) * ‖WithLp.toLp 2 (fun k => V k i)‖ ≤
      ‖star (fun k => Q k (Fin.last n)) ⬝ᵥ (fun k => V k i)‖) :
    s / (R * B) / 2 ≤ √(lastRowWeights (Qᴴ * V) i) := by
  have hq1 : ‖WithLp.toLp 2 (fun k => Q k (Fin.last n))‖ = 1 := by
    have e : (fun k => Q k (Fin.last n)) = Q *ᵥ Pi.single (Fin.last n) 1 := by
      ext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [e, hQ.norm_toLp_mulVec, PiLp.toLp_single, PiLp.norm_single, norm_one]
  have h := le_lastRowWeights_conjTranspose_mul (Q := Q) (V := V) (c := 1) (R := 1)
    (g := fun k => Q k (Fin.last n)) hV (by simp) (fun k => by simp [hq1]) hq1.le
    (by positivity) hqv
  have hκ0 : 0 < pseudoConditionNumber V := by
    linarith [one_le_pseudoConditionNumber hV.ne_zero]
  have hB : 0 < B := hκ0.trans_le hκ
  refine Real.le_sqrt_of_sq_le (le_trans ?_ h)
  rw [one_pow, one_mul]
  have e : (s / (R * B) / 2) ^ 2 = (s / (2 * R)) ^ 2 / B ^ 2 := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ hκ0.le hκ 2)

/-- The weight after a small right factor: if $\sqrt{w_i(\mathbf{W})} \ge a/2$ and
$\|\mathbf{Z}\|_2 \le \min(a/512, 1/16)$, then $w_i(\mathbf{W}(\mathbf{I} + \mathbf{Z})) \ge
(a/8)^2$ (`NLAlib.sqrt_lastRowWeights_le_mul_one_add`). -/
private theorem sq_div_eight_le_lastRowWeights {n : ℕ} {W Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {a : ℝ} {i : Fin (n + 1)} (ha : 0 < a) (hw : a / 2 ≤ √(lastRowWeights W i))
    (hζ₁ : specNorm Z ≤ a / 512) (hζ₂ : specNorm Z ≤ 1 / 16) :
    (a / 8) ^ 2 ≤ lastRowWeights (W * (1 + Z)) i := by
  have htr := sqrt_lastRowWeights_le_mul_one_add W Z i
  set y := √(lastRowWeights (W * (1 + Z)) i)
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hζ0 := specNorm_nonneg Z
  have hy : a / 8 ≤ y := by
    by_contra hlt
    push Not at hlt
    nlinarith
  have hw' := pow_le_pow_left₀ (by positivity) hy 2
  rwa [Real.sq_sqrt (lastRowWeights_nonneg _ _)] at hw'

/-- The class and the weights after `RHess`: let $\mathbf{A}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$,
eigenvalues separated by $g > 0$ and $\|\mathbf{A}\|_2 \le \Sigma$; let $\mathbf{Q}$ be unitary
with last column $\mathbf{q}$ satisfying $\lvert\mathbf{q}^{\mathsf{H}}\mathbf{v}_i\rvert \ge
(s/(2R))\|\mathbf{v}_i\|$ for every column $\mathbf{v}_i$ of $\mathbf{V}$, and
$\|\widehat{\mathbf{H}} - \mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}\|_2 \le \varepsilon \le
\min(g/(32(n + 1)B), sg/(1024(n + 1)B^2R))$. Then $\widehat{\mathbf{H}}$ has a diagonalization
with condition at most $2B$, separation $g/2$ and last-row weights at least $s^2/(64R^2B^2)$:
the eigenvectors $\mathbf{Q}^{\mathsf{H}}\mathbf{V}(\mathbf{I} + \mathbf{Z})$ with
$\|\mathbf{Z}\|_2 \le 2\sqrt{n + 1}\,B\varepsilon/g$
(`NLAlib.exists_add_mul_mul_one_add_eq_mul_diagonal`), and the weights transferred by
`NLAlib.sqrt_lastRowWeights_le_mul_one_add`. -/
theorem rhess_class {n : ℕ} {A V H Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} {B g s R ε : ℝ} (hV : IsUnit V) (hAV : A * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hs : 0 < s) (hR : 0 < R) (hQ : HasOrthonormalCols Q)
    (hqv : ∀ i, s / (2 * R) * ‖WithLp.toLp 2 (fun k => V k i)‖ ≤
      ‖star (fun k => Q k (Fin.last n)) ⬝ᵥ (fun k => V k i)‖)
    (hH : specNorm (H - Qᴴ * A * Q) ≤ ε)
    (hε : ε ≤ min (g / (32 * (n + 1) * B)) (s * g / (1024 * (n + 1) * B ^ 2 * R))) :
    ∃ (V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (d' : Fin (n + 1) → ℂ), IsUnit V' ∧
      H * V' = V' * Matrix.diagonal d' ∧ pseudoConditionNumber V' ≤ 2 * B ∧
      (∀ i j, i ≠ j → g / 2 ≤ ‖d' i - d' j‖) ∧
      ∀ i, s ^ 2 / (64 * R ^ 2 * B ^ 2) ≤ lastRowWeights V' i := by
  have hB1 : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  obtain ⟨hV₀, hAV₀, hκ₀'⟩ := hQ.isUnit_conjTranspose_mul_and_mul_eq_mul_diagonal hV hAV
  set V₀ := Qᴴ * V
  have hκ₀ : pseudoConditionNumber V₀ ≤ B := hκ₀'.trans_le hκ
  set E := H - Qᴴ * A * Q
  have hε₁ : ε ≤ g / (32 * (n + 1) * B) := hε.trans (min_le_left _ _)
  have hε₂ : ε ≤ s * g / (1024 * (n + 1) * B ^ 2 * R) := hε.trans (min_le_right _ _)
  have hE16 : specNorm E ≤ g / (16 * (n + 1) * B) :=
    hH.trans (hε₁.trans (div_le_div_of_nonneg_left hg.le (by positivity) (by nlinarith)))
  obtain ⟨Z, d', hZu, hAV', -, hκZ, hd', hZ⟩ :=
    exists_add_mul_mul_one_add_eq_mul_diagonal hV₀ hAV₀ hκ₀ hg hgap hE16
  have hHE : Qᴴ * A * Q + E = H := add_sub_cancel _ _
  rw [hHE] at hAV'
  refine ⟨V₀ * (1 + Z), d', hV₀.mul hZu, hAV', ?_, fun i j hij => ?_, fun i => ?_⟩
  · calc pseudoConditionNumber (V₀ * (1 + Z))
        ≤ pseudoConditionNumber V₀ * pseudoConditionNumber (1 + Z) :=
          pseudoConditionNumber_mul_le hV₀ hZu
      _ ≤ B * 2 := mul_le_mul hκ₀ hκZ (pseudoConditionNumber_nonneg _) (by linarith)
      _ = 2 * B := by ring
  · have h1 := hd' i
    have h2 := hd' j
    have h3 := hgap i j hij
    have e : d i - d j = (d' i - d' j) - (d' i - d i) + (d' j - d j) := by ring
    have h4 : ‖d i - d j‖ ≤ ‖d' i - d' j‖ + ‖d' i - d i‖ + ‖d' j - d j‖ := by
      rw [e]
      exact (norm_add_le _ _).trans (by linarith [norm_sub_le (d' i - d' j) (d' i - d i)])
    linarith
  -- the weights
  set a := s / (R * B)
  have ha : 0 < a := by positivity
  -- the weight before the perturbation
  have hw₀ : a / 2 ≤ √(lastRowWeights V₀ i) := half_le_sqrt_lastRowWeights hV hκ hs hR hQ (hqv i)
  -- the size of `Z`
  have hζ : specNorm Z ≤ a / 512 ∧ specNorm Z ≤ 1 / 16 := by
    have hsN : √((n : ℝ) + 1) ≤ (n : ℝ) + 1 := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    have hsN1 : 1 ≤ √((n : ℝ) + 1) := Real.one_le_sqrt.mpr hN
    have hE0 := specNorm_nonneg E
    have hEε := hH
    constructor
    · refine hZ.trans ?_
      rw [div_le_iff₀ hg]
      calc 2 * √((n : ℝ) + 1) * B * specNorm E ≤ 2 * ((n : ℝ) + 1) * B *
            (s * g / (1024 * (n + 1) * B ^ 2 * R)) := by gcongr; linarith
        _ = a / 512 * g := by simp only [a]; field_simp; ring
    · refine hZ.trans ?_
      rw [div_le_iff₀ hg]
      calc 2 * √((n : ℝ) + 1) * B * specNorm E ≤ 2 * ((n : ℝ) + 1) * B *
            (g / (32 * (n + 1) * B)) := by gcongr; linarith
        _ = 1 / 16 * g := by field_simp; ring
  have hw := sq_div_eight_le_lastRowWeights ha hw₀ hζ.1 hζ.2
  refine le_trans (le_of_eq ?_) hw
  simp only [a]
  field_simp
  ring

end Class

end NLAlib.SmallEig
