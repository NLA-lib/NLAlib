/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import NLAlib.Matrix.Perturbation.OrthErr

/-!
# Error analysis of classical Gram–Schmidt passes

One- and two-pass orthogonality bounds follow from ordinary residual and projection-error
inequalities. The mathematics is independent of the implementation supplying those inequalities.

## Main results

* `NLAlib.cgsPassBound_le_cgsPassBound`: monotonicity in the number of columns.
* `NLAlib.norm_transpose_mulVec_le_of_norm_sub_le`: one-pass projection bound.
* `NLAlib.isOrthErr_of_one_pass`: one pass meets the orthogonalization interface.
* `NLAlib.isOrthErr_of_two_passes`: two-pass orthogonalization guarantee.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **The error coefficient of one rounded classical Gram–Schmidt pass** against $j$ columns of
length $N$ with $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0$:
the value <!-- value cgsPassBound N j u \eta_0 -->$c_1 = 2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$,
a safe multiple of the first-order count
$(1+\eta_0)\sqrt{j}\,(\gamma_N + \gamma_j) + 4u$. -/
noncomputable irreducible_def cgsPassBound (N j : ℕ) (u η₀ : ℝ) : ℝ :=
  2 * (1 + η₀) * Real.sqrt ((j : ℝ) + 1) * ((N + j + 2 : ℕ) : ℝ) * u

/-- The CGS pass bound `NLAlib.cgsPassBound` $N\,j\,u\,\eta_0$
= <!-- value cgsPassBound N j u \eta_0 -->$2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$ is monotone in the
number $j$ of columns for $u, \eta_0 \ge 0$. -/
theorem cgsPassBound_le_cgsPassBound (N : ℕ) {j k : ℕ} (hjk : j ≤ k) {u η₀ : ℝ} (hu : 0 ≤ u)
    (hη₀ : 0 ≤ η₀) : cgsPassBound N j u η₀ ≤ cgsPassBound N k u η₀ := by
  rw [cgsPassBound_def, cgsPassBound_def]
  have hs : Real.sqrt ((j : ℝ) + 1) ≤ Real.sqrt ((k : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hn : ((N + j + 2 : ℕ) : ℝ) ≤ ((N + k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  gcongr

/-- **One pass leaves a first-order loss of orthogonality**: if
$\|\mathbf{w}_1 - (\mathbf{w} - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w})\| \le
c_1\|\mathbf{w}\|$ and $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0$, then
$\|\mathbf{V}^{\mathsf{T}}\mathbf{w}_1\| \le \sqrt{1 + \eta_0}\,(\eta_0 + c_1)\|\mathbf{w}\|$.
[GiraudLangouRozloznikVandenEshof2005, proof of Theorem 1]. -/
theorem norm_transpose_mulVec_le_of_norm_sub_le {n j : ℕ} {V : Matrix (Fin n) (Fin j) ℝ}
    {w w₁ : Fin n → ℝ} {η₀ c₁ : ℝ} (hV : specNorm (Vᵀ * V - 1) ≤ η₀)
    (hw₁ : ‖WithLp.toLp 2 (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤ c₁ * ‖WithLp.toLp 2 w‖) :
    ‖WithLp.toLp 2 (Vᵀ *ᵥ w₁)‖ ≤ Real.sqrt (1 + η₀) * (η₀ + c₁) * ‖WithLp.toLp 2 w‖ := by
  have hs : specNorm Vᵀ ≤ Real.sqrt (1 + η₀) := by
    rw [specNorm_transpose]
    exact specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le hV
  have hη : 0 ≤ η₀ := (specNorm_nonneg _).trans hV
  have hy : ‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖ ≤ Real.sqrt (1 + η₀) * ‖WithLp.toLp 2 w‖ :=
    (norm_toLp_mulVec_le Vᵀ w).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
  have key : ∀ x : Fin n → ℝ, Vᵀ *ᵥ (x + (w - V *ᵥ (Vᵀ *ᵥ w))) =
      Vᵀ *ᵥ x - (Vᵀ * V - 1) *ᵥ (Vᵀ *ᵥ w) := by
    intro x
    rw [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec]
    abel
  have hkey := key (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))
  rw [sub_add_cancel] at hkey
  have hsx : specNorm Vᵀ * ‖WithLp.toLp 2 (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤
      Real.sqrt (1 + η₀) * (c₁ * ‖WithLp.toLp 2 w‖) :=
    mul_le_mul hs hw₁ (norm_nonneg _) (Real.sqrt_nonneg _)
  have hsy : specNorm (Vᵀ * V - 1) * ‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖ ≤
      η₀ * (Real.sqrt (1 + η₀) * ‖WithLp.toLp 2 w‖) :=
    mul_le_mul hV hy (norm_nonneg _) hη
  rw [hkey, WithLp.toLp_sub]
  have h1 := norm_toLp_mulVec_le Vᵀ (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))
  have h2 := norm_toLp_mulVec_le (Vᵀ * V - 1) (Vᵀ *ᵥ w)
  have htri := norm_sub_le (WithLp.toLp 2 (Vᵀ *ᵥ (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))))
    (WithLp.toLp 2 ((Vᵀ * V - 1) *ᵥ (Vᵀ *ᵥ w)))
  have hfin : Real.sqrt (1 + η₀) * (c₁ * ‖WithLp.toLp 2 w‖) +
      η₀ * (Real.sqrt (1 + η₀) * ‖WithLp.toLp 2 w‖) =
      Real.sqrt (1 + η₀) * (η₀ + c₁) * ‖WithLp.toLp 2 w‖ := by ring
  linarith

/-- **One classical Gram–Schmidt pass meets the guarantee with a first-order input term**:
from residual and projection-error bounds, `NLAlib.IsOrthErr` holds with
$\varepsilon_1 = 0$, $\varepsilon_2 = c_1$, $\varepsilon_3 = \sqrt{1+\eta_0}(\eta_0 + c_1)$; this is
why one pass is not enough (the loss is divided by the admissibility ratio).
[GiraudLangouRozloznikVandenEshof2005, Theorem 1]. -/
theorem isOrthErr_of_one_pass {n j : ℕ} {V : Matrix (Fin n) (Fin j) ℝ}
    {w w₁ : Fin n → ℝ} {h₁ : Fin j → ℝ} {η₀ c₁ : ℝ}
    (hres : specNorm (Vᵀ * V - 1) ≤ η₀ →
      ‖WithLp.toLp 2 (w - V *ᵥ h₁ - w₁)‖ ≤ c₁ * ‖WithLp.toLp 2 w‖)
    (hw₁ : specNorm (Vᵀ * V - 1) ≤ η₀ →
      ‖WithLp.toLp 2 (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤ c₁ * ‖WithLp.toLp 2 w‖) :
    IsOrthErr η₀ 0 c₁ (Real.sqrt (1 + η₀) * (η₀ + c₁)) V w h₁ w₁ := by
  refine ⟨hres, fun hV => ?_⟩
  rw [zero_mul, zero_add]
  exact norm_transpose_mulVec_le_of_norm_sub_le hV (hw₁ hV)

/-- The exact reduction $\mathbf{w} - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w}$ against a basis
with $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0 \le 1$ does not increase the
norm. -/
private lemma norm_sub_mulVec_transpose_mulVec_le {n j : ℕ}
    {V : Matrix (Fin n) (Fin j) ℝ} {w : Fin n → ℝ} {η₀ : ℝ}
    (hV : specNorm (Vᵀ * V - 1) ≤ η₀) (hη : η₀ ≤ 1) :
    ‖WithLp.toLp 2 (w - V *ᵥ (Vᵀ *ᵥ w))‖ ≤ ‖WithLp.toLp 2 w‖ := by
  have hs := specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le hV
  have hη0 : 0 ≤ η₀ := (specNorm_nonneg _).trans hV
  have hy := (norm_toLp_mulVec_le V (Vᵀ *ᵥ w)).trans
    (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
  have hinner : inner ℝ (WithLp.toLp 2 w) (WithLp.toLp 2 (V *ᵥ (Vᵀ *ᵥ w))) =
      ‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp,
      EuclideanSpace.inner_toLp_toLp]
    simp only [star_trivial]
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hsq : ‖WithLp.toLp 2 (V *ᵥ (Vᵀ *ᵥ w))‖ ^ 2 ≤ (1 + η₀) * ‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖ ^ 2 := by
    rw [← Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + η₀), ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hy 2
  rw [WithLp.toLp_sub, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_real, hinner]
  nlinarith [sq_nonneg ‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖]

/-- The scalar inequality behind the residual bound of two passes. -/
private lemma two_passes_residual_arith {c₁ u s a b₁ H₁ H₂ H R : ℝ} (hc0 : 0 ≤ c₁)
    (hc₁ : c₁ ≤ 1 / 100) (hu : 0 ≤ u) (hu₁ : 4 * u ≤ c₁) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 + 1 / 200)
    (ha : 0 ≤ a) (hb₁ : b₁ ≤ (1 + c₁) * a) (hres : R ≤ c₁ * a + c₁ * b₁ + s * (u * H))
    (hh : H ≤ H₁ + H₂) (hh₁ : H₁ ≤ (s + c₁) * a) (hh₂ : H₂ ≤ (s + c₁) * b₁) :
    R ≤ 3 * c₁ * a := by
  have hH : H₁ + H₂ ≤ 21 / 10 * a := by
    have hk : (s + c₁) * ((2 + c₁) * a) ≤ (1 + 3 / 200) * ((2 + c₁) * a) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hb₁ (by linarith : 0 ≤ s + c₁),
      mul_le_mul_of_nonneg_right hc₁ ha]
  have h1 : u * H ≤ u * (21 / 10 * a) := mul_le_mul_of_nonneg_left (hh.trans hH) hu
  have hsu : s * (u * H) ≤ 3 / 5 * c₁ * a := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hs0, mul_le_mul_of_nonneg_right hs1
      (mul_nonneg hu ha), mul_le_mul_of_nonneg_right hu₁ ha, mul_nonneg hu ha]
  nlinarith [mul_le_mul_of_nonneg_left hb₁ hc0, mul_nonneg hc0 ha]

/-- The scalar inequality behind the orthogonality bound of two passes. -/
private lemma two_passes_orth_arith {η₀ c₁ s a b₁ b₂ t X : ℝ} (hη0 : 0 ≤ η₀)
    (hη : η₀ ≤ 1 / 100) (hc0 : 0 ≤ c₁) (hc₁ : c₁ ≤ 1 / 100) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 + η₀ / 2)
    (hss : s ^ 2 = 1 + η₀) (ha : 0 ≤ a) (hb0 : 0 ≤ b₁)
    (ht : t ≤ s * (η₀ + c₁) * a) (horth : X ≤ s * (c₁ * b₁) + η₀ * t)
    (hb₁' : b₁ ≤ b₂ + c₁ * b₁ + s * t) :
    X ≤ 2 * c₁ * b₂ + 2 * (η₀ + c₁) ^ 2 * a := by
  have h2 : 2 * c₁ * ((1 - c₁) * b₁) ≤ 2 * c₁ * (b₂ + s * t) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : s * (c₁ * b₁) ≤ 2 * c₁ * ((1 - c₁) * b₁) := by
    nlinarith [mul_nonneg hc0 hb0, mul_nonneg (mul_nonneg hc0 hc0) hb0]
  have h4 : (η₀ + 2 * c₁ * s) * t ≤ (η₀ + 2 * c₁ * s) * (s * (η₀ + c₁) * a) :=
    mul_le_mul_of_nonneg_left ht (by positivity)
  have h5 : (η₀ + 2 * c₁ * s) * s ≤ 2 * (η₀ + c₁) := by
    nlinarith [mul_le_mul_of_nonneg_left hs1 hη0, mul_nonneg hc0 hη0]
  have h6 : (η₀ + 2 * c₁ * s) * (s * (η₀ + c₁) * a) ≤ 2 * (η₀ + c₁) * ((η₀ + c₁) * a) :=
    calc _ = (η₀ + 2 * c₁ * s) * s * ((η₀ + c₁) * a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h5 (mul_nonneg (by linarith) ha)
  linarith only [horth, h2, h3, h4, h6]

/-- **Twice is enough**: two passes with coefficient, residual and projection-error bounds
(the second on $\mathbf{w}_1$), and coefficients summed with relative error $u$, meet
`NLAlib.IsOrthErr` with $\varepsilon_1 = 2c_1$, $\varepsilon_2 = 3c_1$,
$\varepsilon_3 = 2(\eta_0 + c_1)^2$, for $\eta_0 \le 1/100$, $c_1 \le 1/100$, $4u \le c_1$.
[GiraudLangouRozloznikVandenEshof2005, Theorem 2]; [Parlett1998, §6.9].
Result: gram-schmidt-cgs2-twice-is-enough -/
theorem isOrthErr_of_two_passes {n j : ℕ} {V : Matrix (Fin n) (Fin j) ℝ}
    {w w₁ w₂ : Fin n → ℝ} {h₁ h₂ h : Fin j → ℝ} {η₀ c₁ u : ℝ} (hη : η₀ ≤ 1 / 100)
    (hc₁ : c₁ ≤ 1 / 100) (hu : 0 ≤ u) (hu₁ : 4 * u ≤ c₁)
    (hp₁ : specNorm (Vᵀ * V - 1) ≤ η₀ →
      ‖WithLp.toLp 2 (h₁ - Vᵀ *ᵥ w)‖ ≤ c₁ * ‖WithLp.toLp 2 w‖ ∧
      ‖WithLp.toLp 2 (w - V *ᵥ h₁ - w₁)‖ ≤ c₁ * ‖WithLp.toLp 2 w‖ ∧
      ‖WithLp.toLp 2 (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤ c₁ * ‖WithLp.toLp 2 w‖)
    (hp₂ : specNorm (Vᵀ * V - 1) ≤ η₀ →
      ‖WithLp.toLp 2 (h₂ - Vᵀ *ᵥ w₁)‖ ≤ c₁ * ‖WithLp.toLp 2 w₁‖ ∧
      ‖WithLp.toLp 2 (w₁ - V *ᵥ h₂ - w₂)‖ ≤ c₁ * ‖WithLp.toLp 2 w₁‖ ∧
      ‖WithLp.toLp 2 (w₂ - (w₁ - V *ᵥ (Vᵀ *ᵥ w₁)))‖ ≤ c₁ * ‖WithLp.toLp 2 w₁‖)
    (hsum : ∀ i, |h i - (h₁ i + h₂ i)| ≤ u * |h₁ i + h₂ i|) :
    IsOrthErr η₀ (2 * c₁) (3 * c₁) (2 * (η₀ + c₁) ^ 2) V w h w₂ := by
  suffices H : specNorm (Vᵀ * V - 1) ≤ η₀ →
      ‖WithLp.toLp 2 (w - V *ᵥ h - w₂)‖ ≤ 3 * c₁ * ‖WithLp.toLp 2 w‖ ∧
      ‖WithLp.toLp 2 (Vᵀ *ᵥ w₂)‖ ≤
        2 * c₁ * ‖WithLp.toLp 2 w₂‖ + 2 * (η₀ + c₁) ^ 2 * ‖WithLp.toLp 2 w‖ from
    ⟨fun hV => (H hV).1, fun hV => (H hV).2⟩
  intro hV
  obtain ⟨e₁, r₁, f₁⟩ := hp₁ hV
  obtain ⟨e₂, r₂, f₂⟩ := hp₂ hV
  have hc0 : 0 ≤ c₁ := by linarith
  have hη0 : 0 ≤ η₀ := (specNorm_nonneg _).trans hV
  have hs0 : 0 ≤ Real.sqrt (1 + η₀) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (1 + η₀) ≤ 1 + η₀ / 2 :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hsV := specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le hV
  have hVx : ∀ x, ‖WithLp.toLp 2 (V *ᵥ x)‖ ≤ Real.sqrt (1 + η₀) * ‖WithLp.toLp 2 x‖ :=
    fun x => (norm_toLp_mulVec_le V x).trans (mul_le_mul_of_nonneg_right hsV (norm_nonneg _))
  have hVTx : ∀ x, ‖WithLp.toLp 2 (Vᵀ *ᵥ x)‖ ≤ Real.sqrt (1 + η₀) * ‖WithLp.toLp 2 x‖ :=
    fun x => (norm_toLp_mulVec_le Vᵀ x).trans
      (mul_le_mul_of_nonneg_right (by rwa [specNorm_transpose]) (norm_nonneg _))
  have ht := norm_transpose_mulVec_le_of_norm_sub_le hV f₁
  have hb₁ : ‖WithLp.toLp 2 w₁‖ ≤ (1 + c₁) * ‖WithLp.toLp 2 w‖ := by
    calc ‖WithLp.toLp 2 w₁‖
        = ‖WithLp.toLp 2 (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w))) + WithLp.toLp 2 (w - V *ᵥ (Vᵀ *ᵥ w))‖ := by
          rw [← WithLp.toLp_add, sub_add_cancel]
      _ ≤ c₁ * ‖WithLp.toLp 2 w‖ + ‖WithLp.toLp 2 w‖ :=
          (norm_add_le _ _).trans (add_le_add f₁
            (norm_sub_mulVec_transpose_mulVec_le hV (by linarith)))
      _ = _ := by ring
  have hb₁' : ‖WithLp.toLp 2 w₁‖ ≤ ‖WithLp.toLp 2 w₂‖ + c₁ * ‖WithLp.toLp 2 w₁‖ +
      Real.sqrt (1 + η₀) * ‖WithLp.toLp 2 (Vᵀ *ᵥ w₁)‖ := by
    calc ‖WithLp.toLp 2 w₁‖
        = ‖WithLp.toLp 2 w₂ - WithLp.toLp 2 (w₂ - (w₁ - V *ᵥ (Vᵀ *ᵥ w₁))) +
            WithLp.toLp 2 (V *ᵥ (Vᵀ *ᵥ w₁))‖ := by
          rw [← WithLp.toLp_sub, ← WithLp.toLp_add]; congr 2; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
            (add_le_add le_rfl f₂)) (hVx _))
  have hid : Vᵀ *ᵥ w₂ = Vᵀ *ᵥ (w₂ - (w₁ - V *ᵥ (Vᵀ *ᵥ w₁))) - (Vᵀ * V - 1) *ᵥ (Vᵀ *ᵥ w₁) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec]
    abel
  have horth : ‖WithLp.toLp 2 (Vᵀ *ᵥ w₂)‖ ≤ Real.sqrt (1 + η₀) * (c₁ * ‖WithLp.toLp 2 w₁‖) +
      η₀ * ‖WithLp.toLp 2 (Vᵀ *ᵥ w₁)‖ := by
    rw [hid, WithLp.toLp_sub]
    refine (norm_sub_le _ _).trans (add_le_add ((hVTx _).trans ?_) ?_)
    · exact mul_le_mul_of_nonneg_left f₂ hs0
    · exact (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hV (norm_nonneg _))
  have hsum' : ‖WithLp.toLp 2 (h - (h₁ + h₂))‖ ≤ u * ‖WithLp.toLp 2 (h₁ + h₂)‖ := by
    calc ‖WithLp.toLp 2 (h - (h₁ + h₂))‖ ≤ ‖WithLp.toLp 2 (u • (h₁ + h₂))‖ :=
          EuclideanSpace.norm_toLp_le_norm_toLp fun i => by
            simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu] using hsum i
      _ = _ := by rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hu]
  have hh₁ : ‖WithLp.toLp 2 h₁‖ ≤ (Real.sqrt (1 + η₀) + c₁) * ‖WithLp.toLp 2 w‖ := by
    calc ‖WithLp.toLp 2 h₁‖ = ‖WithLp.toLp 2 (h₁ - Vᵀ *ᵥ w) + WithLp.toLp 2 (Vᵀ *ᵥ w)‖ := by
          rw [← WithLp.toLp_add, sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (by linarith [hVTx w])
  have hh₂ : ‖WithLp.toLp 2 h₂‖ ≤ (Real.sqrt (1 + η₀) + c₁) * ‖WithLp.toLp 2 w₁‖ := by
    calc ‖WithLp.toLp 2 h₂‖ = ‖WithLp.toLp 2 (h₂ - Vᵀ *ᵥ w₁) + WithLp.toLp 2 (Vᵀ *ᵥ w₁)‖ := by
          rw [← WithLp.toLp_add, sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (by linarith [hVTx w₁])
  have hh : ‖WithLp.toLp 2 (h₁ + h₂)‖ ≤ ‖WithLp.toLp 2 h₁‖ + ‖WithLp.toLp 2 h₂‖ := by
    rw [WithLp.toLp_add]; exact norm_add_le _ _
  have hres : ‖WithLp.toLp 2 (w - V *ᵥ h - w₂)‖ ≤ c₁ * ‖WithLp.toLp 2 w‖ +
      c₁ * ‖WithLp.toLp 2 w₁‖ + Real.sqrt (1 + η₀) * (u * ‖WithLp.toLp 2 (h₁ + h₂)‖) := by
    have hid' : w - V *ᵥ h - w₂ =
        (w - V *ᵥ h₁ - w₁) + (w₁ - V *ᵥ h₂ - w₂) - V *ᵥ (h - (h₁ + h₂)) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_add]; abel
    rw [hid', WithLp.toLp_sub, WithLp.toLp_add]
    exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add r₁ r₂))
      ((hVx _).trans (mul_le_mul_of_nonneg_left hsum' hs0)))
  have hss : Real.sqrt (1 + η₀) ^ 2 = 1 + η₀ := Real.sq_sqrt (by linarith)
  exact ⟨two_passes_residual_arith hc0 hc₁ hu hu₁ hs0 (by linarith) (norm_nonneg _) hb₁ hres hh
      hh₁ hh₂,
    two_passes_orth_arith hη0 hη hc0 hc₁ hs0 hs1 hss (norm_nonneg _) (norm_nonneg _)
      ht horth hb₁'⟩

end NLAlib
