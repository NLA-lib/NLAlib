/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.TruncatedGeneralizedNystromOracle

/-!
# Truncated generalized Nyström: a lower bound on Epperly and Webber's instance

Late-truncated generalized Nyström $\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi})\rrbracket_k$ with independent standard Gaussian test matrices reaches relative
error $1 + \varepsilon$ in expected squared Frobenius norm at
$\ell = O(k/\varepsilon)$, $p = O(k/\varepsilon)$ for every rectangular real matrix.
The actual-estimator upper bound is proved in
`NLAlib/LowRank/Gaussian/TruncatedGeneralizedNystromRelativeError.lean`, with
$\ell \ge 200 k/\varepsilon$ and $p \ge 14\ell$, for $0 < \varepsilon \le 1$.
On Epperly and Webber's two-eigenvalue instance
$\mathbf{A}_a = \operatorname{diag}(a\mathbf{I}_k, \mathbf{I}_{n-k})$, as $a \to \infty$ the
expected error is at least
$$\|\mathbf{A}_a - \llbracket\mathbf{A}_a\rrbracket_k\|_{\mathsf{F}}^2 +
\frac{k(n - \ell)}{p - \ell - 1}\,,$$
so relative error $1 + \varepsilon$ needs $p \ge \ell + 1 + k(n-\ell)/((n-k)\varepsilon)$. On
the same instance untruncated generalized Nyström pays $\ell/(p - \ell - 1)$ in place of
$k/(p - \ell - 1)$ (Epperly and Webber's identity,
`NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_eq_mul_integral_of_hasLaw_gaussianMatrix`):
late truncation gains the factor $\ell/k$ where Epperly and Webber's lower bound for generalized
Nyström lives. For $n > \ell$ this gives a necessary co-range scale proportional to
$k/\varepsilon$, consistent with that upper bound.
New. Real.

## Main results

* `NLAlib.eventually_le_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_fromBlocks_sq`:
  the lower bound as $a \to \infty$.
* `NLAlib.mul_le_of_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_fromBlocks_sq_le`:
  the co-range size it forces.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l p s t : Type*} [Fintype l]
  [Fintype p] [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
  {X : Ω → Matrix (s ⊕ t) l ℝ} {Ψ : Ω → Matrix (s ⊕ t) p ℝ}

/-! ### Helpers for the lower bound -/

/-- The two-eigenvalue instance $\operatorname{diag}(a\mathbf{I}_k, \mathbf{I}_{n-k})$. -/
private noncomputable def blk (a : ℝ) : Matrix (s ⊕ t) (s ⊕ t) ℝ :=
  Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (1 : Matrix t t ℝ)

/-- The $a$-free envelope
$\lvert t\rvert + \|\mathbf{\Omega}_2\mathbf{\Omega}_1^{+}\|_{\mathsf{F}}^2$
of the range-finder error. -/
private noncomputable def env (x : Matrix (s ⊕ t) l ℝ) : ℝ :=
  Fintype.card t + frobNorm ((selectionMatrix Sum.inr : Matrix (s ⊕ t) t ℝ)ᴴ * x *
    pinv ((selectionMatrix Sum.inl : Matrix (s ⊕ t) s ℝ)ᴴ * x)) ^ 2

/-- The squared core noise. -/
private noncomputable def noise (a : ℝ) (x : Matrix (s ⊕ t) l ℝ) (ψ : Matrix (s ⊕ t) p ℝ) : ℝ :=
  frobNorm (obliqueProjector (blk a * x) ψᴴ * (blk a - rsvd (blk a) x)) ^ 2

/-- The squared Gaussian block
$\|(\mathbf{G}_1^{\mathsf{H}})^{+}\mathbf{G}_2^{\mathsf{H}}\|_{\mathsf{F}}^2$. -/
private noncomputable def blockSq {r r' : Type*} [Fintype r] [Fintype r']
    (z : Matrix r p ℝ × Matrix r' p ℝ) : ℝ :=
  frobNorm (pinv z.1ᴴ * z.2ᴴ) ^ 2

/-- The truncated second moment of the noise bound at rank $r$ in dimension $d$. -/
private noncomputable def hfun (p : Type*) [Fintype p] (d r : ℕ) (c u : ℝ) : ℝ :=
  ∫ z, min (blockSq z * max u 0) (c * (blockSq z * max u 0) ^ 2)
    ∂((gaussianMatrix (Fin r) p).prod (gaussianMatrix (Fin (d - r)) p))

/-- The pointwise defect. -/
private noncomputable def defect (a : ℝ) (x : Matrix (s ⊕ t) l ℝ) (ψ : Matrix (s ⊕ t) p ℝ) : ℝ :=
  (if a / 2 < √(env x) then noise a x ψ else 0) + min (noise a x ψ) (8 / a ^ 2 * noise a x ψ ^ 2)

/-- The conditional bound on the defect. -/
private noncomputable def bound (p : Type*) [Fintype p] (a : ℝ) (x : Matrix (s ⊕ t) l ℝ) : ℝ :=
  (if a / 2 < √(env x) then
    (Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) * env x else 0) +
    ∑ r ∈ Finset.range (Fintype.card l + 1), hfun p (Fintype.card (s ⊕ t)) r (8 / a ^ 2) (env x)

private theorem one_le_singularValues_blk {a : ℝ} (ha : 1 ≤ a) {i : ℕ}
    (hi : i < Fintype.card (s ⊕ t)) : 1 ≤ singularValues (blk (s := s) (t := t) a) i := by
  refine le_singularValues_of_forall_mem _ ⊤ (by
    rw [finrank_top, Module.finrank_fintype_fun_eq_card]; omega) fun x _ => ?_
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_toLp_sq_eq_sum_sq,
    EuclideanSpace.norm_toLp_sq_eq_sum_sq, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [blk, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
    Matrix.one_mulVec, Matrix.smul_mulVec, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
    smul_eq_mul, Function.comp_apply]
  refine add_le_add (Finset.sum_le_sum fun j _ => ?_) le_rfl
  rw [mul_pow]
  nlinarith [mul_nonneg (sq_nonneg (x (Sum.inl j))) (by nlinarith : (0 : ℝ) ≤ a ^ 2 - 1)]

private theorem sub_le_sum_Ico_singularValues_blk_sq {a : ℝ} (ha : 1 ≤ a) (j : ℕ) :
    (Fintype.card (s ⊕ t) : ℝ) - j ≤ ∑ i ∈ Finset.Ico j
      (min (Fintype.card (s ⊕ t)) (Fintype.card (s ⊕ t))),
        singularValues (blk (s := s) (t := t) a) i ^ 2 := by
  rw [min_self]
  refine le_trans ?_ (Finset.sum_le_sum fun i hi =>
    one_le_pow₀ (one_le_singularValues_blk ha (Finset.mem_Ico.mp hi).2))
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  rcases le_total j (Fintype.card (s ⊕ t)) with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero, sub_nonpos]
    exact_mod_cast h

private theorem le_singularValues_blk {a : ℝ} (ha : 0 ≤ a) (hk : 0 < Fintype.card s) :
    a ≤ singularValues (blk (s := s) (t := t) a) (Fintype.card s - 1) := by
  set f : ((s ⊕ t) → ℝ) →ₗ[ℝ] (t → ℝ) := LinearMap.funLeft ℝ ℝ Sum.inr
  have hf : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr (LinearMap.funLeft_surjective_of_injective _ _ _ Sum.inr_injective)
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hf, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_sum] at hrn
  refine le_singularValues_of_forall_mem _ (LinearMap.ker f) (by omega) fun x hx => ?_
  have hx0 : ∀ j, x (Sum.inr j) = 0 := fun j => congrFun (LinearMap.mem_ker.mp hx) j
  rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), mul_pow, EuclideanSpace.norm_toLp_sq_eq_sum_sq,
    EuclideanSpace.norm_toLp_sq_eq_sum_sq, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [blk, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
    Matrix.one_mulVec, Matrix.smul_mulVec, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
    smul_eq_mul, Function.comp_apply, hx0]
  simp only [mul_pow, ← Finset.mul_sum, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, add_zero]
  exact le_rfl

private theorem singularValues_blk_le (a : ℝ) :
    singularValues (blk (s := s) (t := t) a) (Fintype.card s) ≤ 1 := by
  have hB : (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (0 : Matrix t t ℝ)).rank ≤
      Fintype.card s := by
    rw [Matrix.rank_fromBlocks_zero₁₂_zero₂₁, Matrix.rank_zero, add_zero]
    exact Matrix.rank_le_card_width _
  refine (singularValues_le_specNorm_sub_of_rank_le _ hB).trans ?_
  rw [show blk a - Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (0 : Matrix t t ℝ) =
      Matrix.fromBlocks 0 0 0 1 by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [blk],
    specNorm_fromBlocks_zero₁₂_zero₂₁, specNorm_zero]
  exact max_le zero_le_one specNorm_one_le

private theorem frobNorm_sub_rsvd_blk_sq_le (a : ℝ) {x : Matrix (s ⊕ t) l ℝ}
    (hx : ((selectionMatrix Sum.inl : Matrix (s ⊕ t) s ℝ)ᴴ * x).rank = Fintype.card s) :
    frobNorm (blk a - rsvd (blk a) x) ^ 2 ≤ env x := by
  set Z : Matrix (s ⊕ t) s ℝ := selectionMatrix Sum.inl
  set W : Matrix (s ⊕ t) t ℝ := selectionMatrix Sum.inr
  have hZ : HasOrthonormalCols Z := hasOrthonormalCols_selectionMatrix Sum.inl_injective
  have hW : HasOrthonormalCols W := hasOrthonormalCols_selectionMatrix Sum.inr_injective
  have hWW : W * Wᴴ = Matrix.fromBlocks 0 0 0 1 := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;>
      simp [W, Matrix.mul_apply, selectionMatrix_apply, Matrix.one_apply]
  have hE : blk a - blk a * Z * Zᴴ = W * Wᴴ := by
    rw [hWW]
    ext i j; rcases i with i | i <;> rcases j with j | j <;>
      simp [Z, blk, Matrix.mul_apply, selectionMatrix_apply, Matrix.one_apply]
  have hΩ : (xᴴ * Z).rank = Z.rank := by
    rw [hZ.rank_eq, show xᴴ * Z = (Zᴴ * x)ᴴ by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose],
      Matrix.rank_conjTranspose, hx]
  refine (hZ.frobNorm_sub_rsvd_sq_le hΩ (blk a)).trans_eq ?_
  rw [hE, show W * Wᴴ * x * pinv (Zᴴ * x) = W * (Wᴴ * x * pinv (Zᴴ * x)) by
      simp only [Matrix.mul_assoc],
    hW.frobNorm_mul_left (Wᴴ * x * pinv (Zᴴ * x)), hWW, frobNorm_fromBlocks_sq, frobNorm_one_sq]
  simp only [env, W, Z, frobNorm_zero]
  ring

private theorem gap_le {a : ℝ} (ha : 4 ≤ a) (hk : 0 < Fintype.card s) {x : Matrix (s ⊕ t) l ℝ}
    (hx : ((selectionMatrix Sum.inl : Matrix (s ⊕ t) s ℝ)ᴴ * x).rank = Fintype.card s)
    (hD : √(env x) ≤ a / 2) :
    a ^ 2 / 8 ≤ singularValues (rsvd (blk a) x) (Fintype.card s - 1) ^ 2 -
      singularValues (rsvd (blk a) x) (Fintype.card s) ^ 2 := by
  have hF : frobNorm (blk a - rsvd (blk a) x) ≤ √(env x) := by
    rw [← Real.sqrt_sq (frobNorm_nonneg _)]
    exact Real.sqrt_le_sqrt (frobNorm_sub_rsvd_blk_sq_le a hx)
  have h1 := abs_le.mp (abs_singularValues_sub_le_specNorm (blk a) (rsvd (blk a) x)
    (Fintype.card s - 1))
  have h2 := le_singularValues_blk (s := s) (t := t) (by linarith : (0 : ℝ) ≤ a) hk
  have h3 : singularValues (rsvd (blk a) x) (Fintype.card s) ≤ 1 :=
    ((isStarProjection_rangeProjector (blk a * x)).singularValues_mul_le (blk a) _).trans
      (singularValues_blk_le a)
  have h4 := singularValues_nonneg (rsvd (blk a) x) (Fintype.card s)
  have h5 := specNorm_le_frobNorm (blk a - rsvd (blk a) x)
  have h6 : a / 2 ≤ singularValues (rsvd (blk a) x) (Fintype.card s - 1) := by linarith
  nlinarith

private theorem le_frobNorm_sub_truncatedSVD_generalizedNystrom_blk_sq {a : ℝ} (ha : 4 ≤ a)
    {x : Matrix (s ⊕ t) l ℝ} {ψ : Matrix (s ⊕ t) p ℝ}
    (hx : ((selectionMatrix Sum.inl : Matrix (s ⊕ t) s ℝ)ᴴ * x).rank = Fintype.card s)
    (hψ : (ψᴴ * (blk a * x)).rank = (blk a * x).rank) :
    frobNorm (blk a - truncatedSVD (rsvd (blk a) x) (Fintype.card s)) ^ 2 +
        frobNorm (rangeProjector (truncatedSVD (rsvd (blk a) x) (Fintype.card s)) *
          (obliqueProjector (blk a * x) ψᴴ * (blk a - rsvd (blk a) x))) ^ 2 - defect a x ψ ≤
      frobNorm (blk a - truncatedSVD (generalizedNystrom (blk a) x ψ) (Fintype.card s)) ^ 2 := by
  have hT1 :=
    frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq hψ
      (Fintype.card s)
  have hPN := pow_le_pow_left₀ (frobNorm_nonneg _) ((isStarProjection_rangeProjector
    (truncatedSVD (rsvd (blk a) x) (Fintype.card s))).frobNorm_mul_le
      (obliqueProjector (blk a * x) ψᴴ * (blk a - rsvd (blk a) x))) 2
  have hN0 : 0 ≤ noise a x ψ := sq_nonneg _
  have ha0 : 0 < a := by linarith
  have hm0 : 0 ≤ min (noise a x ψ) (8 / a ^ 2 * noise a x ψ ^ 2) :=
    le_min hN0 (by positivity)
  simp only [defect]
  by_cases hD : a / 2 < √(env x)
  · rw [if_pos hD]
    simp only [noise] at hm0 ⊢
    linarith
  rw [if_neg hD, zero_add]
  rcases Nat.eq_zero_or_pos (Fintype.card s) with hk | hk
  · have hP0 : rangeProjector (truncatedSVD (rsvd (blk a) x) (Fintype.card s)) = 0 := by
      rw [hk, truncatedSVD_zero, rangeProjector_zero]
    rw [hP0, Matrix.zero_mul, frobNorm_zero]
    linarith
  have hg := gap_le ha hk hx (not_lt.mp hD)
  have hg0 : 0 < a ^ 2 / 8 := by positivity
  have hT3 := le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq hψ hk (by linarith)
  rcases le_total (noise a x ψ) (8 / a ^ 2 * noise a x ψ ^ 2) with h | h
  · rw [min_eq_left h]
    simp only [noise] at ⊢
    linarith
  · rw [min_eq_right h]
    have hdiv : noise a x ψ ^ 2 /
        (singularValues (rsvd (blk a) x) (Fintype.card s - 1) ^ 2 -
          singularValues (rsvd (blk a) x) (Fintype.card s) ^ 2) ≤ 8 / a ^ 2 * noise a x ψ ^ 2 := by
      have h8 : 1 ≤ 8 / a ^ 2 * (singularValues (rsvd (blk a) x) (Fintype.card s - 1) ^ 2 -
          singularValues (rsvd (blk a) x) (Fintype.card s) ^ 2) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        linarith
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left h8 (sq_nonneg (noise a x ψ))]
    simp only [noise] at hdiv ⊢
    rw [← pow_mul] at hdiv
    linarith

/-- The two frame blocks of a standard Gaussian matrix are independent standard Gaussian. -/
private theorem map_conjTranspose_mul_prod {m r r' : Type*} [Fintype m] [Fintype r]
    [Fintype r'] [DecidableEq r] [DecidableEq r'] {Q₁ : Matrix m r ℝ} {Q₂ : Matrix m r' ℝ}
    (hQ₁ : HasOrthonormalCols Q₁) (hQ₂ : HasOrthonormalCols Q₂) (h₁₂ : Q₁ᴴ * Q₂ = 0) :
    (gaussianMatrix m p).map (fun ψ => (Q₁ᴴ * ψ, Q₂ᴴ * ψ)) =
      (gaussianMatrix r p).prod (gaussianMatrix r' p) := by
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  have h1 := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hid hQ₁
  have h2 := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hid hQ₂
  have hind := indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hid hQ₁ hQ₂ h₁₂
  rw [(indepFun_iff_map_prod_eq_prod_map_map h1.aemeasurable h2.aemeasurable).mp hind,
    h1.map_eq, h2.map_eq]

private theorem measurable_blockSq {r r' : Type*} [Fintype r] [Fintype r'] :
    Measurable (blockSq (p := p) (r := r) (r' := r')) :=
  (measurable_frobNorm.comp ((measurable_pinv.comp
    ((continuous_id.matrix_conjTranspose.measurable).comp measurable_fst)).matrix_mul
      ((continuous_id.matrix_conjTranspose.measurable).comp measurable_snd))).pow_const 2

private theorem blockSq_conjTranspose_mul {m r r' : Type*} [Fintype m] [Fintype r] [Fintype r']
    (Q₁ : Matrix m r ℝ) (Q₂ : Matrix m r' ℝ) (ψ : Matrix m p ℝ) :
    blockSq (Q₁ᴴ * ψ, Q₂ᴴ * ψ) = frobNorm (pinv (ψᴴ * Q₁) * (ψᴴ * Q₂)) ^ 2 := by
  simp only [blockSq, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- The Gaussian block is square integrable for $r + 2 \le p$. -/
private theorem integrable_blockSq (d r : ℕ) (hr : r + 2 ≤ Fintype.card p) :
    Integrable blockSq ((gaussianMatrix (Fin r) p).prod (gaussianMatrix (Fin (d - r)) p)) := by
  set Q₁ : Matrix (Fin r ⊕ Fin (d - r)) (Fin r) ℝ := selectionMatrix Sum.inl
  set Q₂ : Matrix (Fin r ⊕ Fin (d - r)) (Fin (d - r)) ℝ := selectionMatrix Sum.inr
  have hQ₁ : HasOrthonormalCols Q₁ := hasOrthonormalCols_selectionMatrix Sum.inl_injective
  have hQ₂ : HasOrthonormalCols Q₂ := hasOrthonormalCols_selectionMatrix Sum.inr_injective
  have h₁₂ : Q₁ᴴ * Q₂ = 0 := by
    rw [conjTranspose_selectionMatrix_mul]
    ext i j
    simp [Q₂, selectionMatrix_apply]
  have hid : HasLaw (fun ψ : Matrix (Fin r ⊕ Fin (d - r)) p ℝ => ψ)
      (gaussianMatrix (Fin r ⊕ Fin (d - r)) p) (gaussianMatrix (Fin r ⊕ Fin (d - r)) p) :=
    HasLaw.id
  have hφ : Measurable fun ψ : Matrix (Fin r ⊕ Fin (d - r)) p ℝ => (Q₁ᴴ * ψ, Q₂ᴴ * ψ) :=
    (measurable_const.matrix_mul measurable_id).prodMk (measurable_const.matrix_mul measurable_id)
  rw [← map_conjTranspose_mul_prod hQ₁ hQ₂ h₁₂,
    integrable_map_measure measurable_blockSq.aestronglyMeasurable hφ.aemeasurable]
  have h := integrable_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix hid hQ₁ hQ₂ h₁₂
    (by rwa [Fintype.card_fin]) (1 : Matrix (Fin (d - r)) (Fin (d - r)) ℝ)
  simp only [Matrix.mul_one] at h
  refine h.congr (ae_of_all _ fun ψ => ?_)
  simp only [Function.comp_apply, blockSq_conjTranspose_mul]

private theorem min_blockSq_nonneg {r r' : Type*} [Fintype r] [Fintype r'] {c : ℝ} (hc : 0 ≤ c)
    (u : ℝ) (z : Matrix r p ℝ × Matrix r' p ℝ) :
    0 ≤ min (blockSq z * max u 0) (c * (blockSq z * max u 0) ^ 2) :=
  le_min (mul_nonneg (sq_nonneg _) (le_max_right _ _)) (by positivity)

private theorem measurable_min_blockSq {r r' : Type*} [Fintype r] [Fintype r'] (c u : ℝ) :
    Measurable fun z : Matrix r p ℝ × Matrix r' p ℝ =>
      min (blockSq z * max u 0) (c * (blockSq z * max u 0) ^ 2) :=
  (measurable_blockSq.mul_const _).min (((measurable_blockSq.mul_const _).pow_const 2).const_mul c)

private theorem integrable_min_blockSq {d r : ℕ} (hr : r + 2 ≤ Fintype.card p) {c : ℝ}
    (hc : 0 ≤ c) (u : ℝ) :
    Integrable (fun z => min (blockSq z * max u 0) (c * (blockSq z * max u 0) ^ 2))
      ((gaussianMatrix (Fin r) p).prod (gaussianMatrix (Fin (d - r)) p)) :=
  ((integrable_blockSq d r hr).mul_const (max u 0)).mono'
    (measurable_min_blockSq c u).aestronglyMeasurable (ae_of_all _ fun z => by
      rw [Real.norm_of_nonneg (min_blockSq_nonneg hc u z)]
      exact min_le_left _ _)

private theorem hfun_nonneg {d r : ℕ} {c : ℝ} (hc : 0 ≤ c) (u : ℝ) : 0 ≤ hfun p d r c u :=
  integral_nonneg fun z => min_blockSq_nonneg hc u z

private theorem hfun_le {d r : ℕ} (hr : r + 2 ≤ Fintype.card p) {c : ℝ} (hc : 0 ≤ c) (u : ℝ) :
    hfun p d r c u ≤ (∫ z, blockSq z ∂((gaussianMatrix (Fin r) p).prod
      (gaussianMatrix (Fin (d - r)) p))) * max u 0 := by
  rw [← integral_mul_const]
  exact integral_mono (integrable_min_blockSq hr hc u)
    ((integrable_blockSq d r hr).mul_const _) fun z => min_le_left _ _

private theorem hfun_monotone {d r : ℕ} (hr : r + 2 ≤ Fintype.card p) {c : ℝ} (hc : 0 ≤ c) :
    Monotone (hfun p d r c) := fun u v huv =>
  integral_mono (integrable_min_blockSq hr hc u) (integrable_min_blockSq hr hc v) fun z => by
    have h0 : 0 ≤ blockSq z * max u 0 := mul_nonneg (sq_nonneg _) (le_max_right _ _)
    have h1 : blockSq z * max u 0 ≤ blockSq z * max v 0 :=
      mul_le_mul_of_nonneg_left (max_le_max huv le_rfl) (sq_nonneg _)
    exact min_le_min h1 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) hc)

private theorem tendsto_hfun {d r : ℕ} (hr : r + 2 ≤ Fintype.card p) (u : ℝ) :
    Tendsto (fun a : ℝ => hfun p d r (8 / a ^ 2) u) atTop (nhds 0) := by
  have hc : Tendsto (fun a : ℝ => 8 / a ^ 2) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have h := tendsto_integral_filter_of_dominated_convergence (fun z => blockSq z * max u 0)
    (Eventually.of_forall fun a => (measurable_min_blockSq (8 / a ^ 2) u).aestronglyMeasurable)
    (Eventually.of_forall fun a => ae_of_all _ fun z => by
      rw [Real.norm_of_nonneg (min_blockSq_nonneg (by positivity) u z)]
      exact min_le_left _ _)
    ((integrable_blockSq d r hr).mul_const _) (ae_of_all _ fun z =>
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using hc.mul_const ((blockSq z * max u 0) ^ 2))
        (fun a => min_blockSq_nonneg (by positivity) u z) fun a => min_le_right _ _)
    (f := fun _ => (0 : ℝ))
  simpa only [hfun, integral_zero] using h

/-- The full-row-rank event of the head block of a Gaussian range test matrix. -/
private theorem ae_rank_head_eq (hX : HasLaw X (gaussianMatrix (s ⊕ t) l) μ)
    (hsl : Fintype.card s ≤ Fintype.card l) :
    ∀ᵐ ω ∂μ, ((selectionMatrix Sum.inl : Matrix (s ⊕ t) s ℝ)ᴴ * X ω).rank = Fintype.card s := by
  filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix
    (hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX
      (hasOrthonormalCols_selectionMatrix Sum.inl_injective))] with ω hω
  rw [hω, min_eq_left hsl]

private theorem measurable_env : Measurable (env (s := s) (t := t) (l := l)) :=
  measurable_const.add ((measurable_frobNorm.comp
    ((measurable_const.matrix_mul measurable_id).matrix_mul
      (measurable_pinv.comp (measurable_const.matrix_mul measurable_id)))).pow_const 2)

private theorem env_nonneg (x : Matrix (s ⊕ t) l ℝ) : 0 ≤ env x := by
  unfold env
  positivity

/-- The envelope is integrable for $k + 2 \le \ell$. -/
private theorem integrable_env (hX : HasLaw X (gaussianMatrix (s ⊕ t) l) μ)
    (hsl : Fintype.card s + 2 ≤ Fintype.card l) : Integrable (fun ω => env (X ω)) μ := by
  have := hX.isProbabilityMeasure
  have h₁₂ : (selectionMatrix Sum.inl : Matrix (s ⊕ t) s ℝ)ᴴ *
      (selectionMatrix Sum.inr : Matrix (s ⊕ t) t ℝ) = 0 := by
    rw [conjTranspose_selectionMatrix_mul]
    ext i j
    simp [selectionMatrix_apply]
  have h := integrable_frobNorm_mul_mul_pinv_sq_of_hasLaw_gaussianMatrix hX
    (hasOrthonormalCols_selectionMatrix Sum.inl_injective)
    (hasOrthonormalCols_selectionMatrix Sum.inr_injective) h₁₂ (by omega) (1 : Matrix t t ℝ)
  simp only [Matrix.one_mul] at h
  exact (integrable_const _).add h

private theorem measurable_noise (a : ℝ) :
    Measurable fun q : Matrix (s ⊕ t) l ℝ × Matrix (s ⊕ t) p ℝ => noise a q.1 q.2 :=
  (measurable_frobNorm.comp (measurable_obliqueProjector_mul_sub_rsvd (blk a))).pow_const 2

/-- For a fixed range test matrix, the core noise is integrable with mean at most
$\ell/(p - \ell - 1)\,\|\mathbf{A}_a - \mathbf{R}_a\|_{\mathsf{F}}^2$. -/
private theorem integral_noise_le (a : ℝ) (x : Matrix (s ⊕ t) l ℝ)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    Integrable (fun ψ => noise a x ψ) (gaussianMatrix (s ⊕ t) p) ∧
      ∫ ψ, noise a x ψ ∂(gaussianMatrix (s ⊕ t) p) ≤
        (Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) *
          frobNorm (blk a - rsvd (blk a) x) ^ 2 := by
  have hid : HasLaw (fun ψ : Matrix (s ⊕ t) p ℝ => ψ) (gaussianMatrix (s ⊕ t) p)
      (gaussianMatrix (s ⊕ t) p) := HasLaw.id
  have hS := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hid
  have hr : (blk (s := s) (t := t) a * x).rank + 2 ≤ Fintype.card p := by
    have := Matrix.rank_le_card_width (blk (s := s) (t := t) a * x)
    omega
  have hsplit : ∀ᵐ ψ ∂(gaussianMatrix (s ⊕ t) p), noise a x ψ =
      frobNorm (blk a - generalizedNystrom (blk a) x ψ) ^ 2 -
        frobNorm (blk a - rsvd (blk a) x) ^ 2 := by
    filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix (blk a * x) hid
      (by omega)] with ψ hψ
    rw [noise, frobNorm_sub_generalizedNystrom_sq hψ]
    ring
  have hgn : Integrable (fun ψ : Matrix (s ⊕ t) p ℝ =>
      frobNorm (blk a - generalizedNystrom (blk a) x ψ) ^ 2) (gaussianMatrix (s ⊕ t) p) := by
    simp only [sub_generalizedNystrom]
    exact integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix hS
      (blk a * x) hr (blk a)
  refine ⟨(hgn.sub (integrable_const _)).congr (hsplit.mono fun _ h => h.symm), ?_⟩
  rw [integral_congr_ae hsplit, integral_sub hgn (integrable_const _),
    integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix (blk a) x hid hr,
    integral_const, probReal_univ, one_smul]
  have hq := gaussianProjectionFactor_le_gaussianProjectionFactor
    (Matrix.rank_le_card_width (blk (s := s) (t := t) a * x)) hlp
  rw [gaussianProjectionFactor_def, gaussianProjectionFactor_def] at hq
  rw [gaussianProjectionFactor_def]
  nlinarith [sq_nonneg (frobNorm (blk (s := s) (t := t) a - rsvd (blk a) x))]

/-- For a fixed range test matrix on the head-rank event, the truncated second moment of the
core noise is at most `hfun` at the rank of the sketch. -/
private theorem integral_min_noise_le (a : ℝ) {c : ℝ} (hc : 0 ≤ c) {x : Matrix (s ⊕ t) l ℝ}
    (hx : ((selectionMatrix Sum.inl : Matrix (s ⊕ t) s ℝ)ᴴ * x).rank = Fintype.card s)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ψ, min (noise a x ψ) (c * noise a x ψ ^ 2) ∂(gaussianMatrix (s ⊕ t) p) ≤
      hfun p (Fintype.card (s ⊕ t)) (blk a * x).rank c (env x) := by
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ :=
    exists_hasOrthonormalCols_frames_range_compl (blk (s := s) (t := t) a * x)
      (blk (s := s) (t := t) a)
  have hr : (blk (s := s) (t := t) a * x).rank + 2 ≤ Fintype.card p := by
    have := Matrix.rank_le_card_width (blk (s := s) (t := t) a * x)
    omega
  have hid : HasLaw (fun ψ : Matrix (s ⊕ t) p ℝ => ψ) (gaussianMatrix (s ⊕ t) p)
      (gaussianMatrix (s ⊕ t) p) := HasLaw.id
  have hφ : Measurable fun ψ : Matrix (s ⊕ t) p ℝ => (Q₁ᴴ * ψ, Q₂ᴴ * ψ) :=
    (measurable_const.matrix_mul measurable_id).prodMk (measurable_const.matrix_mul measurable_id)
  have hEnv := frobNorm_sub_rsvd_blk_sq_le a hx
  have hpt : ∀ᵐ ψ ∂(gaussianMatrix (s ⊕ t) p),
      noise a x ψ ≤ blockSq (Q₁ᴴ * ψ, Q₂ᴴ * ψ) * max (env x) 0 := by
    filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix (blk a * x) hid
      (by omega)] with ψ hψ
    have h3 : frobNorm (Q₂ᴴ * (((1 : Matrix (s ⊕ t) (s ⊕ t) ℝ) - rangeProjector (blk a * x)) *
        blk a)) =
        frobNorm (blk (s := s) (t := t) a - rsvd (blk a) x) := by
      rw [← hQ₂.frobNorm_mul_left, hE, sub_rsvd]
    have h2 := pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_mul_le
      (pinv (ψᴴ * Q₁) * (ψᴴ * Q₂))
      (Q₂ᴴ * (((1 : Matrix (s ⊕ t) (s ⊕ t) ℝ) - rangeProjector (blk a * x)) * blk a))) 2
    rw [h3, mul_pow] at h2
    rw [noise, sub_rsvd, obliqueProjector_mul_one_sub_rangeProjector_mul_eq hR₁ hE hψ,
      hQ₁.frobNorm_mul_left, blockSq_conjTranspose_mul]
    exact h2.trans (mul_le_mul_of_nonneg_left (hEnv.trans (le_max_left _ _)) (sq_nonneg _))
  have hg : Integrable (fun ψ => min (blockSq (Q₁ᴴ * ψ, Q₂ᴴ * ψ) * max (env x) 0)
      (c * (blockSq (Q₁ᴴ * ψ, Q₂ᴴ * ψ) * max (env x) 0) ^ 2)) (gaussianMatrix (s ⊕ t) p) := by
    have h := integrable_min_blockSq (d := Fintype.card (s ⊕ t)) hr hc (env x)
    rw [← map_conjTranspose_mul_prod hQ₁ hQ₂ h₁₂] at h
    exact (integrable_map_measure (measurable_min_blockSq c (env x)).aestronglyMeasurable
      hφ.aemeasurable).mp h
  refine (integral_mono_of_nonneg (ae_of_all _ fun ψ => le_min (sq_nonneg _) (by positivity)) hg
    (hpt.mono fun ψ h => ?_)).trans_eq ?_
  · have h0 : 0 ≤ noise a x ψ := sq_nonneg _
    exact min_le_min h (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h 2) hc)
  rw [hfun, ← map_conjTranspose_mul_prod hQ₁ hQ₂ h₁₂,
    integral_map hφ.aemeasurable (measurable_min_blockSq c (env x)).aestronglyMeasurable]

private theorem measurable_defect (a : ℝ) :
    Measurable fun q : Matrix (s ⊕ t) l ℝ × Matrix (s ⊕ t) p ℝ => defect a q.1 q.2 := by
  have hN := measurable_noise (s := s) (t := t) (l := l) (p := p) a
  have hS : MeasurableSet {q : Matrix (s ⊕ t) l ℝ × Matrix (s ⊕ t) p ℝ | a / 2 < √(env q.1)} :=
    measurableSet_lt measurable_const
      (Real.continuous_sqrt.measurable.comp (measurable_env.comp measurable_fst))
  exact (Measurable.ite hS hN measurable_const).add (hN.min ((hN.pow_const 2).const_mul _))

private theorem defect_nonneg {a : ℝ} (x : Matrix (s ⊕ t) l ℝ) (ψ : Matrix (s ⊕ t) p ℝ) :
    0 ≤ defect a x ψ := by
  have h0 : 0 ≤ noise a x ψ := sq_nonneg _
  have h1 : 0 ≤ min (noise a x ψ) (8 / a ^ 2 * noise a x ψ ^ 2) := le_min h0 (by positivity)
  unfold defect
  split_ifs <;> linarith

private theorem measurable_bound (a : ℝ) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    Measurable (bound (s := s) (t := t) (l := l) p a) := by
  refine (Measurable.ite (measurableSet_lt measurable_const
    (Real.continuous_sqrt.measurable.comp measurable_env)) (measurable_env.const_mul _)
      measurable_const).add (Finset.measurable_sum _ fun r hr => ?_)
  have := Finset.mem_range.mp hr
  exact (hfun_monotone (by omega) (by positivity)).measurable.comp measurable_env

/-- The constant of the $a$-free domination of `bound`. -/
private theorem bound_nonneg_le (a : ℝ) (hlp : Fintype.card l + 2 ≤ Fintype.card p)
    (x : Matrix (s ⊕ t) l ℝ) :
    0 ≤ bound p a x ∧ bound p a x ≤
      ((Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) +
        ∑ r ∈ Finset.range (Fintype.card l + 1), ∫ z, blockSq z ∂((gaussianMatrix (Fin r) p).prod
          (gaussianMatrix (Fin (Fintype.card (s ⊕ t) - r)) p))) * env x := by
  have hden : 0 ≤ (Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) := by
    have : (Fintype.card l : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hlp
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have he := env_nonneg x
  constructor
  · refine add_nonneg ?_ (Finset.sum_nonneg fun r _ => hfun_nonneg (by positivity) _)
    split_ifs
    · positivity
    · exact le_rfl
  · rw [add_mul, Finset.sum_mul]
    refine add_le_add ?_ (Finset.sum_le_sum fun r hr => ?_)
    · split_ifs
      · exact le_rfl
      · positivity
    · have := Finset.mem_range.mp hr
      exact hfun_le (by omega) (by positivity) _ |>.trans_eq (by rw [max_eq_left he])

private theorem integral_defect_le {a : ℝ} (ha : 4 ≤ a)
    (hX : HasLaw X (gaussianMatrix (s ⊕ t) l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix (s ⊕ t) p) μ) (hXΨ : IndepFun X Ψ μ)
    (hsl : Fintype.card s + 2 ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    Integrable (fun ω => noise a (X ω) (Ψ ω)) μ ∧ Integrable (fun ω => defect a (X ω) (Ψ ω)) μ ∧
      ∫ ω, defect a (X ω) (Ψ ω) ∂μ ≤ ∫ ω, bound p a (X ω) ∂μ := by
  have := hX.isProbabilityMeasure
  have ha0 : 0 < a := by linarith
  have hA := ae_rank_head_eq hX (by omega)
  have hden : 0 ≤ (Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) := by
    have : (Fintype.card l : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hlp
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hint (x : Matrix (s ⊕ t) l ℝ) := (integral_noise_le a x hlp).1
  have hmin (x : Matrix (s ⊕ t) l ℝ) : Integrable (fun ψ => min (noise a x ψ)
      (8 / a ^ 2 * noise a x ψ ^ 2)) (gaussianMatrix (s ⊕ t) p) := by
    have hN := (measurable_noise (s := s) (t := t) (l := l) (p := p) a).comp
      (measurable_prodMk_left (x := x))
    refine (hint x).mono' (hN.min ((hN.pow_const 2).const_mul _)).aestronglyMeasurable
      (ae_of_all _ fun ψ => ?_)
    have h0 : 0 ≤ noise a x ψ := sq_nonneg _
    rw [Real.norm_of_nonneg (le_min h0 (by positivity))]
    exact min_le_left _ _
  have hdint (x : Matrix (s ⊕ t) l ℝ) :
      Integrable (fun ψ => defect a x ψ) (gaussianMatrix (s ⊕ t) p) := by
    by_cases hD : a / 2 < √(env x)
    · simp only [defect, if_pos hD]
      exact (hint x).add (hmin x)
    · simp only [defect, if_neg hD, zero_add]
      exact hmin x
  have hdle : ∀ᵐ ω ∂μ, ∫ ψ, defect a (X ω) ψ ∂(gaussianMatrix (s ⊕ t) p) ≤ bound p a (X ω) := by
    filter_upwards [hA] with ω hx
    have h1 := (integral_noise_le a (X ω) hlp).2
    have h2 := integral_min_noise_le a (c := 8 / a ^ 2) (by positivity) hx hlp
    have h3 := Finset.single_le_sum
      (f := fun r => hfun p (Fintype.card (s ⊕ t)) r (8 / a ^ 2) (env (X ω)))
      (fun r _ => hfun_nonneg (by positivity) _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Matrix.rank_le_card_width (blk a * X ω))))
    have hE := mul_le_mul_of_nonneg_left (frobNorm_sub_rsvd_blk_sq_le a hx) hden
    simp only [defect, bound]
    by_cases hD : a / 2 < √(env (X ω))
    · simp only [if_pos hD]
      rw [integral_add (hint _) (hmin _)]
      linarith
    · simp only [if_neg hD, zero_add]
      linarith
  have hB := (integrable_env hX hsl).const_mul ((Fintype.card l : ℝ) /
    ((Fintype.card p : ℝ) - Fintype.card l - 1) + ∑ r ∈ Finset.range (Fintype.card l + 1),
      ∫ z, blockSq z ∂((gaussianMatrix (Fin r) p).prod
        (gaussianMatrix (Fin (Fintype.card (s ⊕ t) - r)) p)))
  have hH : Integrable (fun ω => bound p a (X ω)) μ :=
    hB.mono' ((measurable_bound a hlp).comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
      (ae_of_all _ fun ω => (Real.norm_of_nonneg (bound_nonneg_le a hlp (X ω)).1).trans_le
        (bound_nonneg_le a hlp (X ω)).2)
  have hNle : ∀ᵐ ω ∂μ, ∫ ψ, noise a (X ω) ψ ∂(gaussianMatrix (s ⊕ t) p) ≤
      (Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) * env (X ω) := by
    filter_upwards [hA] with ω hx
    exact (integral_noise_le a (X ω) hlp).2.trans
      (mul_le_mul_of_nonneg_left (frobNorm_sub_rsvd_blk_sq_le a hx) hden)
  refine ⟨hXΨ.integrable_comp_of_integral_le hX.aemeasurable hΨ (measurable_noise a)
      (fun _ => sq_nonneg _) (ae_of_all _ fun ω => hint _) hNle
      ((integrable_env hX hsl).const_mul _),
    hXΨ.integrable_comp_of_integral_le hX.aemeasurable hΨ (measurable_defect a)
      (fun q => defect_nonneg q.1 q.2) (ae_of_all _ fun ω => hdint _) hdle hH,
    hXΨ.integral_comp_le_of_integral_le hX.aemeasurable hΨ (measurable_defect a)
      (fun q => defect_nonneg q.1 q.2) (ae_of_all _ fun ω => hdint _) hdle hH⟩

private theorem tendsto_bound (hlp : Fintype.card l + 2 ≤ Fintype.card p)
    (x : Matrix (s ⊕ t) l ℝ) : Tendsto (fun a => bound p a x) atTop (nhds 0) := by
  have h1 : Tendsto (fun a : ℝ => if a / 2 < √(env x) then
      (Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) * env x else 0)
      atTop (nhds 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_gt_atTop (2 * √(env x))] with a ha
      rw [if_neg (by linarith)])
  have h2 := tendsto_finsetSum (Finset.range (Fintype.card l + 1)) fun r hr =>
    tendsto_hfun (p := p) (d := Fintype.card (s ⊕ t)) (r := r)
      (by have := Finset.mem_range.mp hr; omega) (env x)
  simp only [Finset.sum_const_zero] at h2
  have h := h1.add h2
  rw [add_zero] at h
  exact h

private theorem tendsto_integral_bound (hX : HasLaw X (gaussianMatrix (s ⊕ t) l) μ)
    (hsl : Fintype.card s + 2 ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    Tendsto (fun a => ∫ ω, bound p a (X ω) ∂μ) atTop (nhds 0) := by
  have := hX.isProbabilityMeasure
  have h := tendsto_integral_filter_of_dominated_convergence (fun ω =>
    ((Fintype.card l : ℝ) / ((Fintype.card p : ℝ) - Fintype.card l - 1) +
      ∑ r ∈ Finset.range (Fintype.card l + 1), ∫ z, blockSq z ∂((gaussianMatrix (Fin r) p).prod
        (gaussianMatrix (Fin (Fintype.card (s ⊕ t) - r)) p))) * env (X ω))
    (Eventually.of_forall fun a =>
      ((measurable_bound a hlp).comp_aemeasurable hX.aemeasurable).aestronglyMeasurable)
    (Eventually.of_forall fun a => ae_of_all _ fun ω =>
      (Real.norm_of_nonneg (bound_nonneg_le a hlp (X ω)).1).trans_le
        (bound_nonneg_le a hlp (X ω)).2)
    ((integrable_env hX hsl).const_mul _) (ae_of_all _ fun ω => tendsto_bound hlp (X ω))
    (f := fun _ => (0 : ℝ))
  simpa only [integral_zero, Function.comp_apply] using h

private theorem le_integral_err {a : ℝ} (ha : 4 ≤ a)
    (hX : HasLaw X (gaussianMatrix (s ⊕ t) l) μ) (hΨ : HasLaw Ψ (gaussianMatrix (s ⊕ t) p) μ)
    (hXΨ : IndepFun X Ψ μ) (hsl : Fintype.card s + 2 ≤ Fintype.card l)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    (Fintype.card t : ℝ) +
        Fintype.card s * ((Fintype.card s : ℝ) + Fintype.card t - Fintype.card l) /
          ((Fintype.card p : ℝ) - Fintype.card l - 1) - ∫ ω, bound p a (X ω) ∂μ ≤
      ∫ ω, frobNorm (blk a - truncatedSVD (generalizedNystrom (blk a) (X ω) (Ψ ω))
            (Fintype.card s)) ^ 2 ∂μ := by
  classical
  have := hX.isProbabilityMeasure
  have hA1 : (1 : ℝ) ≤ a := by linarith
  obtain ⟨hNi, hDi, hDle⟩ := integral_defect_le ha hX hΨ hXΨ hsl hlp
  have hErr := integrable_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_of_hasLaw_gaussianMatrix
    (blk a) hX.aemeasurable hΨ hXΨ hlp (Fintype.card s)
  have hE1 := integrable_frobNorm_sub_truncatedSVD_rsvd_sq (blk a) hX.aemeasurable (Fintype.card s)
  have hRi := integrable_frobNorm_sub_rsvd_sq (blk a) hX.aemeasurable
  have hPm : Measurable fun q : Matrix (s ⊕ t) l ℝ × Matrix (s ⊕ t) p ℝ =>
      frobNorm (rangeProjector (truncatedSVD (rsvd (blk a) q.1) (Fintype.card s)) *
        (obliqueProjector (blk a * q.1) q.2ᴴ * (blk a - rsvd (blk a) q.1))) ^ 2 :=
    (measurable_frobNorm.comp ((measurable_rangeProjector.comp ((measurable_truncatedSVD _).comp
      ((measurable_rsvd (blk a)).comp measurable_fst))).matrix_mul
        (measurable_obliqueProjector_mul_sub_rsvd (blk a)))).pow_const 2
  have hPi : Integrable (fun ω =>
      frobNorm (rangeProjector (truncatedSVD (rsvd (blk a) (X ω)) (Fintype.card s)) *
        (obliqueProjector (blk a * X ω) (Ψ ω)ᴴ * (blk a - rsvd (blk a) (X ω)))) ^ 2) μ :=
    hNi.mono' (hPm.comp_aemeasurable (hX.aemeasurable.prodMk hΨ.aemeasurable)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (frobNorm_nonneg _)
          ((isStarProjection_rangeProjector _).frobNorm_mul_le _) 2)
  have hG1 := integral_frobNorm_rangeProjector_mul_obliqueProjector_sq_of_hasLaw_gaussianMatrix
    (blk a) hX hΨ hXΨ (k := Fintype.card s) (by omega) hlp
  -- pointwise
  have hpt : ∀ᵐ ω ∂μ,
      frobNorm (blk a - truncatedSVD (rsvd (blk a) (X ω)) (Fintype.card s)) ^ 2 +
        frobNorm (rangeProjector (truncatedSVD (rsvd (blk a) (X ω)) (Fintype.card s)) *
          (obliqueProjector (blk a * X ω) (Ψ ω)ᴴ * (blk a - rsvd (blk a) (X ω)))) ^ 2 -
            defect a (X ω) (Ψ ω) ≤
        frobNorm (blk a - truncatedSVD (generalizedNystrom (blk a) (X ω) (Ψ ω))
          (Fintype.card s)) ^ 2 := by
    filter_upwards [ae_rank_head_eq hX (by omega), ae_rank_conjTranspose_mul_mul_eq (blk a)
      hX.aemeasurable hΨ hXΨ fun x => (Matrix.rank_le_card_width _).trans (by omega)]
      with ω hx hψ
    exact le_frobNorm_sub_truncatedSVD_generalizedNystrom_blk_sq ha hx hψ
  have hmono := integral_mono_ae ((hE1.add hPi).sub hDi) hErr hpt
  simp only [Pi.add_apply, Pi.sub_apply] at hmono
  rw [integral_sub (by exact hE1.add hPi) hDi, integral_add hE1 hPi, hG1] at hmono
  -- the two lower bounds
  have hcard : (Fintype.card (s ⊕ t) : ℝ) = Fintype.card s + Fintype.card t := by
    rw [Fintype.card_sum]; push_cast; ring
  have hE1t : (Fintype.card t : ℝ) ≤
      ∫ ω, frobNorm (blk a - truncatedSVD (rsvd (blk a) (X ω)) (Fintype.card s)) ^ 2 ∂μ := by
    refine le_trans (le_of_eq ?_)
      (integral_mono (integrable_const (Fintype.card t : ℝ)) hE1 fun ω => ?_)
    · simp
    have h2 := pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_sub_truncatedSVD_le_of_rank_le (blk a)
      (rank_truncatedSVD_le (rsvd (blk a) (X ω)) (Fintype.card s))) 2
    rw [frobNorm_sub_truncatedSVD_sq] at h2
    have h3 := sub_le_sum_Ico_singularValues_blk_sq (s := s) (t := t) hA1 (Fintype.card s)
    simp only
    linarith
  have hRt : (Fintype.card (s ⊕ t) : ℝ) - Fintype.card l ≤
      ∫ ω, frobNorm (blk a - rsvd (blk a) (X ω)) ^ 2 ∂μ := by
    refine le_trans (le_of_eq ?_) (integral_mono
      (integrable_const ((Fintype.card (s ⊕ t) : ℝ) - Fintype.card l)) hRi fun ω => ?_)
    · simp
    have h2 := sum_Ico_singularValues_sq_le_frobNorm_sub_sq_of_rank_le (blk a)
      ((rank_rsvd_le (blk a) (X ω)).trans (Matrix.rank_le_card_width _))
    have h3 := sub_le_sum_Ico_singularValues_blk_sq (s := s) (t := t) hA1 (Fintype.card l)
    simp only
    linarith
  have hden : 0 < (Fintype.card p : ℝ) - Fintype.card l - 1 := by
    have : (Fintype.card l : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hlp
    linarith
  have hkc : (Fintype.card s : ℝ) * ((Fintype.card s : ℝ) + Fintype.card t - Fintype.card l) /
      ((Fintype.card p : ℝ) - Fintype.card l - 1) ≤
      Fintype.card s / ((Fintype.card p : ℝ) - Fintype.card l - 1) *
        ∫ ω, frobNorm (blk a - rsvd (blk a) (X ω)) ^ 2 ∂μ := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **Truncated generalized Nyström keeps the noise in the head subspace** (lower bound on
Epperly and Webber's instance): for $\mathbf{A}_a = \operatorname{diag}(a\mathbf{I}_k,
\mathbf{I}_{n-k})$ on $s \oplus t$ ($k = \lvert s\rvert$, $n = \lvert s\rvert + \lvert t\rvert$),
independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and
$\mathbf{\Psi}$ ($n \times p$), $k + 2 \le \ell$, $\ell + 2 \le p$, and every $\eta > 0$: for all
large $a$,
$$\lvert t\rvert + \frac{k(n - \ell)}{p - \ell - 1} - \eta \le
\mathbb{E}\|\mathbf{A}_a - \llbracket\mathsf{gn}(\mathbf{A}_a, \mathbf{\Omega}, \mathbf{\Psi})
\rrbracket_k\|_{\mathsf{F}}^2\,,$$
where $\lvert t\rvert = \|\mathbf{A}_a - \llbracket\mathbf{A}_a\rrbracket_k\|_{\mathsf{F}}^2$ for
$a \ge 1$. For $n \le \ell$ the bound is below the optimum and trivially true. For the choice
`truncatedSVD` makes.
No printed source. New.
Result: truncated-gn-lower-bound -/
theorem eventually_le_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_fromBlocks_sq
    (hX : HasLaw X (gaussianMatrix (s ⊕ t) l) μ) (hΨ : HasLaw Ψ (gaussianMatrix (s ⊕ t) p) μ)
    (hXΨ : IndepFun X Ψ μ) (hsl : Fintype.card s + 2 ≤ Fintype.card l)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ a : ℝ in atTop, (Fintype.card t : ℝ) +
        Fintype.card s * ((Fintype.card s : ℝ) + Fintype.card t - Fintype.card l) /
          ((Fintype.card p : ℝ) - Fintype.card l - 1) - η ≤
      ∫ ω, frobNorm (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (1 : Matrix t t ℝ) -
        truncatedSVD (generalizedNystrom
          (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (1 : Matrix t t ℝ)) (X ω) (Ψ ω))
            (Fintype.card s)) ^ 2 ∂μ := by
  filter_upwards [eventually_ge_atTop 4,
    (tendsto_integral_bound hX hsl hlp).eventually (gt_mem_nhds hη)] with a ha hb
  have h := le_integral_err ha hX hΨ hXΨ hsl hlp
  simp only [blk] at h
  linarith

/-- Relative error $1 + \varepsilon$ forces $p - \ell - 1 \ge k(n - \ell)/((n-k)\varepsilon)$:
for independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and
$\mathbf{\Psi}$ ($n \times p$), $k + 2 \le \ell$, $\ell + 2 \le p$, if truncated generalized
Nyström has expected error at most $(1 + \varepsilon)\|\mathbf{A}_a -
\llbracket\mathbf{A}_a\rrbracket_k\|_{\mathsf{F}}^2 = (1 + \varepsilon)\lvert t\rvert$ on every
$\mathbf{A}_a = \operatorname{diag}(a\mathbf{I}_k, \mathbf{I}_{n-k})$ with $a \ge 1$
($k = \lvert s\rvert$, $n = \lvert s\rvert + \lvert t\rvert$), then
$$k(n - \ell) \le \varepsilon\,(p - \ell - 1)\,\lvert t\rvert\,.$$
For $n \gg \ell$: $p \ge \ell + 1 + k/\varepsilon$ up to the factor $(n-\ell)/(n-k)$.
No printed source. New. -/
theorem mul_le_of_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_fromBlocks_sq_le
    (hX : HasLaw X (gaussianMatrix (s ⊕ t) l) μ) (hΨ : HasLaw Ψ (gaussianMatrix (s ⊕ t) p) μ)
    (hXΨ : IndepFun X Ψ μ) (hsl : Fintype.card s + 2 ≤ Fintype.card l)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) {ε : ℝ}
    (h : ∀ a : ℝ, 1 ≤ a →
      ∫ ω, frobNorm (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (1 : Matrix t t ℝ) -
        truncatedSVD (generalizedNystrom
          (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (1 : Matrix t t ℝ)) (X ω) (Ψ ω))
            (Fintype.card s)) ^ 2 ∂μ ≤ (1 + ε) * Fintype.card t) :
    Fintype.card s * ((Fintype.card s : ℝ) + Fintype.card t - Fintype.card l) ≤
      ε * ((Fintype.card p : ℝ) - Fintype.card l - 1) * Fintype.card t := by
  have hp : (0 : ℝ) < (Fintype.card p : ℝ) - Fintype.card l - 1 := by
    have : (Fintype.card l : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hlp
    linarith
  have hK : (Fintype.card s : ℝ) * ((Fintype.card s : ℝ) + Fintype.card t - Fintype.card l) /
      ((Fintype.card p : ℝ) - Fintype.card l - 1) ≤ ε * Fintype.card t := by
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hev := eventually_le_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_fromBlocks_sq
      hX hΨ hXΨ hsl hlp hη
    obtain ⟨a, ha, ha1⟩ := (hev.and (eventually_ge_atTop 1)).exists
    linarith [h a ha1]
  rw [div_le_iff₀ hp] at hK
  linarith [hK]

end NLAlib
