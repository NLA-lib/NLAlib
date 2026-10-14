/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.QuadraticForm.HansonWright.LinearImage
public import NLAlib.Probability.SubExponential.Basic

/-!
# The off-diagonal part of a quadratic form in independent sub-Gaussian coordinates

For a random vector `X` with independent coordinates, each sub-Gaussian with proxy `c`, and a
real matrix `A`, the off-diagonal chaos `∑_{i ≠ j} A i j X i X j`, written
`quadForm (A - diagonal (diag A)) X`, is sub-exponential with variance proxy `18 c² ‖A‖_F²` and
scale `12 c ‖A‖`.

The proof decouples by random cuts. For `δ : n → Bool`, the cut of `A` keeps the entries `A i j`
with `δ i` and `¬ δ j`; averaged over all `δ`, a pair `i ≠ j` is kept with frequency `1/4`, so the
off-diagonal form is four times the average of the cut forms and, by convexity,
`exp (l O) ≤ avg_δ exp (4 l O_δ)`. A cut form pairs the coordinates in `δ` with the coordinates
outside it, which are independent of them, so its moment generating function is that of the
decoupled form `X ⬝ᵥ A_δ X'` with `X'` an independent copy. Conditioning on `X`, the linear form in
`X'` gives `exp (c λ² ‖A_δᵀ X‖² / 2)`, and `NLAlib.lintegral_exp_mul_norm_mulVec_sq_le` bounds its
mean.

## Main results

* `NLAlib.hasSubexponentialMGF_quadForm_sub_diagonal`.

## References

* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], §6.1 (decoupling) and the proof
  of Theorem 6.2.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {X : Ω → n → ℝ} {c : ℝ≥0}

/-! ### Cuts of a matrix -/

/-- The cut of `A` along `δ`: the entries `A i j` with `δ i` and `¬ δ j`, and `0` elsewhere. -/
private def cut (A : Matrix n n ℝ) (δ : n → Bool) : Matrix n n ℝ :=
  Matrix.of fun i j => if δ i = true ∧ δ j = false then A i j else 0

private lemma cut_eq_mul [DecidableEq n] (A : Matrix n n ℝ) (δ : n → Bool) :
    cut A δ = Matrix.diagonal (fun i => if δ i then 1 else 0) * A *
      Matrix.diagonal (fun j => if δ j then 0 else 1) := by
  ext i j
  simp only [cut, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases Bool.eq_false_or_eq_true (δ i) with hi | hi <;>
    rcases Bool.eq_false_or_eq_true (δ j) with hj | hj <;> simp [hi, hj]

private lemma specNorm_cut_le (A : Matrix n n ℝ) (δ : n → Bool) :
    specNorm (cut A δ) ≤ specNorm A := by
  classical
  have hd : ∀ d : n → ℝ, (∀ i, ‖d i‖ ≤ 1) → specNorm (Matrix.diagonal d) ≤ 1 :=
    fun d hd => specNorm_diagonal_le zero_le_one hd
  have h1 := hd (fun i => if δ i then 1 else 0) fun i => by split_ifs <;> simp
  have h2 := hd (fun j => if δ j then 0 else 1) fun j => by split_ifs <;> simp
  rw [cut_eq_mul]
  set D₁ : Matrix n n ℝ := Matrix.diagonal fun i => if δ i then 1 else 0
  set D₂ : Matrix n n ℝ := Matrix.diagonal fun j => if δ j then 0 else 1
  calc specNorm (D₁ * A * D₂) ≤ specNorm (D₁ * A) * specNorm D₂ := specNorm_mul_le _ _
    _ ≤ (specNorm D₁ * specNorm A) * 1 :=
        mul_le_mul (specNorm_mul_le _ _) h2 (specNorm_nonneg _)
          (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))
    _ ≤ (1 * specNorm A) * 1 := by gcongr
    _ = specNorm A := by ring

private lemma frobNorm_cut_sq_le (A : Matrix n n ℝ) (δ : n → Bool) :
    frobNorm (cut A δ) ^ 2 ≤ frobNorm A ^ 2 := by
  simp only [frobNorm_sq_eq_sum_sq, cut, Matrix.of_apply]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · exact le_rfl
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _

/-! ### The average over cuts -/

/-- A pair `i ≠ j` is cut with frequency `1/4`, and a pair `i = i` never. -/
private lemma sum_cut_weight [DecidableEq n] (i j : n) :
    ∑ δ : n → Bool, (1 / 2 : ℝ) ^ Fintype.card n *
      (if δ i = true ∧ δ j = false then 1 else 0) = if i = j then 0 else 1 / 4 := by
  by_cases hij : i = j
  · subst hij
    simp
  rw [if_neg hij]
  set F : n → Bool → ℝ := fun k b => 1 / 2 * (if k = i then (if b then 1 else 0) else 1) *
    (if k = j then (if b then 0 else 1) else 1)
  have hterm : ∀ δ : n → Bool, (1 / 2 : ℝ) ^ Fintype.card n *
      (if δ i = true ∧ δ j = false then 1 else 0) = ∏ k, F k (δ k) := by
    intro δ
    simp only [F, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Finset.prod_ite_eq', Finset.mem_univ, if_true]
    rcases Bool.eq_false_or_eq_true (δ i) with hi | hi <;>
      rcases Bool.eq_false_or_eq_true (δ j) with hj | hj <;> simp [hi, hj]
  have hsum : ∀ k, ∑ b, F k b = (if k = i then 1 / 2 else 1) * (if k = j then 1 / 2 else 1) := by
    intro k
    by_cases hki : k = i
    · subst hki
      simp [F, hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [F, hki]
      · simp only [F, hki, hkj, if_false, Fintype.sum_bool]
        norm_num
  simp only [hterm]
  rw [← Fintype.prod_sum]
  simp only [hsum, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  norm_num

/-- The off-diagonal form is four times the average of the cut forms. -/
private lemma sum_quadForm_cut [DecidableEq n] (A : Matrix n n ℝ) (x : n → ℝ) :
    ∑ δ : n → Bool, (1 / 2 : ℝ) ^ Fintype.card n * quadForm (cut A δ) x =
      1 / 4 * quadForm (A - Matrix.diagonal A.diag) x := by
  simp only [quadForm_eq_sum, cut, Matrix.of_apply, Matrix.sub_apply, Matrix.diagonal_apply,
    Matrix.diag_apply, star_trivial, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ δ : n → Bool, (1 / 2 : ℝ) ^ Fintype.card n *
        (x i * (if δ i = true ∧ δ j = false then A i j else 0) * x j)
      = (∑ δ : n → Bool, (1 / 2 : ℝ) ^ Fintype.card n *
          (if δ i = true ∧ δ j = false then 1 else 0)) * (x i * A i j * x j) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun δ _ => ?_
        split_ifs <;> ring
    _ = 1 / 4 * (x i * (A i j - if i = j then A i i else 0) * x j) := by
        rw [sum_cut_weight]
        split_ifs with h
        · subst h
          ring
        · ring

/-- Convexity of `exp` against the average over cuts. -/
private lemma sum_weight [DecidableEq n] :
    ∑ _δ : n → Bool, (1 / 2 : ℝ) ^ Fintype.card n = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  rw [← mul_pow]
  norm_num

private lemma exp_mul_quadForm_sub_diagonal_le [DecidableEq n] (A : Matrix n n ℝ) (l : ℝ)
    (x : n → ℝ) :
    rexp (l * quadForm (A - Matrix.diagonal A.diag) x) ≤
      ∑ δ : n → Bool, (1 / 2 : ℝ) ^ Fintype.card n * rexp (4 * l * quadForm (cut A δ) x) := by
  have hw := sum_weight (n := n)
  have key : l * quadForm (A - Matrix.diagonal A.diag) x =
      ∑ δ : n → Bool, (1 / 2 : ℝ) ^ Fintype.card n • (4 * l * quadForm (cut A δ) x) := by
    have := sum_quadForm_cut A x
    simp only [smul_eq_mul]
    calc l * quadForm (A - Matrix.diagonal A.diag) x
        = 4 * l * (1 / 4 * quadForm (A - Matrix.diagonal A.diag) x) := by ring
      _ = 4 * l * ∑ δ : n → Bool, (1 / 2 : ℝ) ^ Fintype.card n * quadForm (cut A δ) x := by
          rw [this]
      _ = _ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun δ _ => by ring
  rw [key]
  refine (convexOn_exp.map_sum_le (fun _ _ => by positivity) hw
    (fun _ _ => Set.mem_univ _)).trans (le_of_eq ?_)
  simp only [smul_eq_mul]

/-! ### Decoupling -/

omit [Fintype n] in
private lemma continuous_quadForm [Fintype n] (M : Matrix n n ℝ) :
    Continuous fun x : n → ℝ => quadForm M x := by
  simp only [quadForm, star_trivial]
  exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

/-- For independent `U` and `W`, `E f (U, W) = E_ω E_ω' f (U ω, W ω')`. -/
private lemma lintegral_comp_eq_lintegral_lintegral {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [IsFiniteMeasure μ] {U : Ω → α} {W : Ω → β} (hUW : IndepFun U W μ)
    (hU : AEMeasurable U μ) (hW : AEMeasurable W μ) {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (U ω, W ω) ∂μ = ∫⁻ ω, ∫⁻ ω', f (U ω, W ω') ∂μ ∂μ := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hU hW).mp hUW
  calc ∫⁻ ω, f (U ω, W ω) ∂μ = ∫⁻ p, f p ∂(μ.map fun ω => (U ω, W ω)) :=
        (lintegral_map' hf.aemeasurable (hU.prodMk hW)).symm
    _ = ∫⁻ p, f p ∂((μ.map U).prod (μ.map W)) := by rw [hmap]
    _ = ∫⁻ u, ∫⁻ w, f (u, w) ∂(μ.map W) ∂(μ.map U) := lintegral_prod _ hf.aemeasurable
    _ = ∫⁻ ω, ∫⁻ w, f (U ω, w) ∂(μ.map W) ∂μ :=
        lintegral_map' hf.lintegral_prod_right'.aemeasurable hU
    _ = ∫⁻ ω, ∫⁻ ω', f (U ω, W ω') ∂μ ∂μ :=
        lintegral_congr fun ω => lintegral_map' (hf.comp measurable_prodMk_left).aemeasurable hW

/-- A cut form only sees the coordinates in `δ` on the left and those outside it on the right. -/
private lemma dotProduct_mulVec_cut (A : Matrix n n ℝ) (δ : n → Bool) (x y : n → ℝ) :
    x ⬝ᵥ cut A δ *ᵥ y =
      (fun i => if δ i then x i else 0) ⬝ᵥ cut A δ *ᵥ fun j => if δ j then 0 else y j := by
  simp only [dotProduct, Matrix.mulVec, cut, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases Bool.eq_false_or_eq_true (δ i) with hi | hi <;>
    rcases Bool.eq_false_or_eq_true (δ j) with hj | hj <;> simp [hi, hj]

/-- The moment generating function of a cut form is that of the decoupled form. -/
private lemma lintegral_exp_quadForm_cut_eq (hind : iIndepFun (fun i ω => X ω i) μ)
    (hX : ∀ i, AEMeasurable (fun ω => X ω i) μ) (A : Matrix n n ℝ) (δ : n → Bool) (lam : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (rexp (lam * quadForm (cut A δ) (X ω))) ∂μ =
      ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (rexp (lam * (X ω ⬝ᵥ cut A δ *ᵥ X ω'))) ∂μ ∂μ := by
  classical
  have := hind.isProbabilityMeasure
  set S : Finset n := Finset.univ.filter fun i => δ i = true
  set T : Finset n := Finset.univ.filter fun i => δ i = false
  have hST : Disjoint S T := by
    rw [Finset.disjoint_filter]
    intro i _ h
    simp [h]
  have hind' := hind.indepFun_finset₀ S T hST hX
  set eS : (S → ℝ) → n → ℝ := fun y i => if hi : i ∈ S then y ⟨i, hi⟩ else 0
  set eT : (T → ℝ) → n → ℝ := fun y i => if hi : i ∈ T then y ⟨i, hi⟩ else 0
  have hmS : Measurable eS := measurable_pi_lambda _ fun i => by
    by_cases hi : i ∈ S
    · simp only [eS, hi, dite_true]
      exact measurable_pi_apply _
    · simp only [eS, hi, dite_false]
      exact measurable_const
  have hmT : Measurable eT := measurable_pi_lambda _ fun i => by
    by_cases hi : i ∈ T
    · simp only [eT, hi, dite_true]
      exact measurable_pi_apply _
    · simp only [eT, hi, dite_false]
      exact measurable_const
  have hUW := hind'.comp hmS hmT
  set U : Ω → n → ℝ := eS ∘ fun ω (i : S) => X ω i
  set W : Ω → n → ℝ := eT ∘ fun ω (i : T) => X ω i
  have hU : ∀ ω, U ω = fun i => if δ i then X ω i else 0 := by
    intro ω
    ext i
    by_cases h : δ i <;> simp [U, eS, S, h]
  have hW : ∀ ω, W ω = fun j => if δ j then 0 else X ω j := by
    intro ω
    ext j
    by_cases h : δ j <;> simp [W, eT, T, h]
  have hXm : AEMeasurable X μ := aemeasurable_pi_lambda _ hX
  have hUm : AEMeasurable U μ := by
    have h' := hmS.comp_aemeasurable (aemeasurable_pi_lambda _ fun (i : S) => hX i)
    exact h'
  have hWm : AEMeasurable W μ := by
    have h' := hmT.comp_aemeasurable (aemeasurable_pi_lambda _ fun (i : T) => hX i)
    exact h'
  have hc : Continuous fun p : (n → ℝ) × (n → ℝ) => rexp (lam * (p.1 ⬝ᵥ cut A δ *ᵥ p.2)) :=
    (continuous_const.mul (continuous_fst.dotProduct
      (continuous_const.matrix_mulVec continuous_snd))).rexp
  have hf : Measurable fun p : (n → ℝ) × (n → ℝ) =>
      ENNReal.ofReal (rexp (lam * (p.1 ⬝ᵥ cut A δ *ᵥ p.2))) :=
    ENNReal.measurable_ofReal.comp hc.measurable
  have key := lintegral_comp_eq_lintegral_lintegral hUW hUm hWm hf
  calc ∫⁻ ω, ENNReal.ofReal (rexp (lam * quadForm (cut A δ) (X ω))) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (rexp (lam * (U ω ⬝ᵥ cut A δ *ᵥ W ω))) ∂μ := by
        refine lintegral_congr fun ω => ?_
        rw [hU, hW, ← dotProduct_mulVec_cut, quadForm, star_trivial]
    _ = ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (rexp (lam * (U ω ⬝ᵥ cut A δ *ᵥ W ω'))) ∂μ ∂μ := key
    _ = ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (rexp (lam * (X ω ⬝ᵥ cut A δ *ᵥ X ω'))) ∂μ ∂μ := by
        refine lintegral_congr fun ω => lintegral_congr fun ω' => ?_
        rw [hU, hW, ← dotProduct_mulVec_cut]

/-- The moment generating function of a cut form. -/
private lemma lintegral_exp_quadForm_cut_le (hind : iIndepFun (fun i ω => X ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ) (A : Matrix n n ℝ) (δ : n → Bool)
    {lam : ℝ} (hlam : 9 * (c ^ 2 * lam ^ 2 * specNorm A ^ 2) ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (rexp (lam * quadForm (cut A δ) (X ω))) ∂μ ≤
      ENNReal.ofReal (rexp (9 / 16 * (c ^ 2 * lam ^ 2 * frobNorm A ^ 2))) := by
  rw [lintegral_exp_quadForm_cut_eq hind (fun i => (h i).aemeasurable) A δ lam]
  have hinner : ∀ ω, ∫⁻ ω', ENNReal.ofReal (rexp (lam * (X ω ⬝ᵥ cut A δ *ᵥ X ω'))) ∂μ ≤
      ENNReal.ofReal (rexp (c * lam ^ 2 / 2 * ‖WithLp.toLp 2 ((cut A δ)ᵀ *ᵥ X ω)‖ ^ 2)) := by
    intro ω
    have heq : ∀ ω', X ω ⬝ᵥ cut A δ *ᵥ X ω' = ((cut A δ)ᵀ *ᵥ X ω) ⬝ᵥ X ω' := fun ω' => by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp only [heq]
    refine (lintegral_exp_mul_dotProduct_le hind h _ lam).trans (le_of_eq ?_)
    congr 2
    ring
  have hS := specNorm_cut_le A δ
  have hF := frobNorm_cut_sq_le A δ
  have hc : (0 : ℝ) ≤ c := c.coe_nonneg
  have hsmall : 18 * (c * (c * lam ^ 2 / 2) * specNorm (cut A δ)ᵀ ^ 2) ≤ 1 := by
    rw [specNorm_transpose]
    have h2 : specNorm (cut A δ) ^ 2 ≤ specNorm A ^ 2 :=
      pow_le_pow_left₀ (specNorm_nonneg _) hS 2
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ c ^ 2 * lam ^ 2)]
  calc ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (rexp (lam * (X ω ⬝ᵥ cut A δ *ᵥ X ω'))) ∂μ ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (rexp (c * lam ^ 2 / 2 * ‖WithLp.toLp 2 ((cut A δ)ᵀ *ᵥ X ω)‖ ^ 2))
          ∂μ := lintegral_mono hinner
    _ ≤ ENNReal.ofReal (rexp (9 / 8 * (c * (c * lam ^ 2 / 2) * frobNorm (cut A δ)ᵀ ^ 2))) :=
        lintegral_exp_mul_norm_mulVec_sq_le hind h _ (by positivity) hsmall
    _ ≤ ENNReal.ofReal (rexp (9 / 16 * (c ^ 2 * lam ^ 2 * frobNorm A ^ 2))) := by
        refine ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_)
        rw [frobNorm_transpose]
        nlinarith [mul_le_mul_of_nonneg_left hF (by positivity : (0 : ℝ) ≤ c ^ 2 * lam ^ 2)]

/-- The moment generating function of the off-diagonal form, by the average over cuts. -/
private lemma lintegral_exp_quadForm_sub_diagonal_le [DecidableEq n]
    (hind : iIndepFun (fun i ω => X ω i) μ) (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ)
    (A : Matrix n n ℝ) {l : ℝ} (hl : 12 * (c * specNorm A * |l|) ≤ 1) :
    ∫⁻ ω, ENNReal.ofReal (rexp (l * quadForm (A - Matrix.diagonal A.diag) (X ω))) ∂μ ≤
      ENNReal.ofReal (rexp (9 * (c ^ 2 * l ^ 2 * frobNorm A ^ 2))) := by
  set w : ℝ := (1 / 2 : ℝ) ^ Fintype.card n
  set B := ENNReal.ofReal (rexp (9 * (c ^ 2 * l ^ 2 * frobNorm A ^ 2)))
  have hw0 : 0 ≤ w := by positivity
  have hlam : 9 * (c ^ 2 * (4 * l) ^ 2 * specNorm A ^ 2) ≤ 1 := by
    have h0 : 0 ≤ c * specNorm A * |l| := by positivity
    have h1 : (12 * (c * specNorm A * |l|)) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hl
    calc 9 * (c ^ 2 * (4 * l) ^ 2 * specNorm A ^ 2) = (12 * (c * specNorm A * |l|)) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, sq_abs]
          ring
      _ ≤ 1 := h1
  have hcut : ∀ δ, ∫⁻ ω, ENNReal.ofReal (rexp (4 * l * quadForm (cut A δ) (X ω))) ∂μ ≤ B := by
    intro δ
    refine (lintegral_exp_quadForm_cut_le hind h A δ hlam).trans (le_of_eq ?_)
    congr 2
    ring
  have hXm : AEMeasurable X μ := aemeasurable_pi_lambda _ fun i => (h i).aemeasurable
  have hmeas : ∀ δ, AEMeasurable
      (fun ω => ENNReal.ofReal (rexp (4 * l * quadForm (cut A δ) (X ω)))) μ := by
    intro δ
    have hc : Measurable fun x : n → ℝ => ENNReal.ofReal (rexp (4 * l * quadForm (cut A δ) x)) :=
      ENNReal.measurable_ofReal.comp
        ((continuous_const.mul (continuous_quadForm _)).rexp).measurable
    have h' := hc.comp_aemeasurable hXm
    exact h'
  calc ∫⁻ ω, ENNReal.ofReal (rexp (l * quadForm (A - Matrix.diagonal A.diag) (X ω))) ∂μ
      ≤ ∫⁻ ω, ∑ δ : n → Bool, ENNReal.ofReal w *
          ENNReal.ofReal (rexp (4 * l * quadForm (cut A δ) (X ω))) ∂μ := by
        refine lintegral_mono fun ω => ?_
        calc ENNReal.ofReal (rexp (l * quadForm (A - Matrix.diagonal A.diag) (X ω)))
            ≤ ENNReal.ofReal (∑ δ : n → Bool, w * rexp (4 * l * quadForm (cut A δ) (X ω))) :=
              ENNReal.ofReal_le_ofReal (exp_mul_quadForm_sub_diagonal_le A l (X ω))
          _ = _ := by
              rw [ENNReal.ofReal_sum_of_nonneg fun δ _ => by positivity]
              exact Finset.sum_congr rfl fun δ _ => ENNReal.ofReal_mul hw0
    _ = ∑ δ : n → Bool, ENNReal.ofReal w *
          ∫⁻ ω, ENNReal.ofReal (rexp (4 * l * quadForm (cut A δ) (X ω))) ∂μ := by
        rw [lintegral_finsetSum' _ fun δ _ => (hmeas δ).const_mul _]
        exact Finset.sum_congr rfl fun δ _ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∑ _δ : n → Bool, ENNReal.ofReal w * B := by
        gcongr with δ
        exact hcut δ
    _ = B := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun _ _ => hw0, sum_weight,
          ENNReal.ofReal_one, one_mul]

/-- A random variable whose exponential moments, as lower integrals, are bounded on the window
is sub-exponential. -/
private lemma hasSubexponentialMGF_of_lintegral_le {Y : Ω → ℝ} {v b : ℝ≥0}
    (hY : AEMeasurable Y μ)
    (h : ∀ l : ℝ, b * |l| < 1 →
      ∫⁻ ω, ENNReal.ofReal (rexp (l * Y ω)) ∂μ ≤ ENNReal.ofReal (rexp (v * l ^ 2 / 2))) :
    HasSubexponentialMGF Y v b μ := by
  have hm : ∀ l : ℝ, AEStronglyMeasurable (fun ω => rexp (l * Y ω)) μ := fun l =>
    (measurable_exp.comp_aemeasurable (hY.const_mul l)).aestronglyMeasurable
  have hint : ∀ l : ℝ, b * |l| < 1 → Integrable (fun ω => rexp (l * Y ω)) μ := fun l hl =>
    ⟨hm l, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (exp_pos _).le)).mpr
      ((h l hl).trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, fun l hl => ?_⟩
  rw [mgf, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (exp_pos _).le) (hm l)]
  exact ENNReal.toReal_le_of_le_ofReal (exp_pos _).le (h l hl)

/-- The off-diagonal part of a quadratic form in independent coordinates, each sub-Gaussian with
proxy `c`, is sub-exponential with variance proxy `18 c² ‖A‖_F²` and scale `12 c ‖A‖`. The
off-diagonal part `∑_{i ≠ j} A i j X i X j` is written `quadForm (A - diagonal (diag A)) X`; the
norms are those of `A` itself. This is the off-diagonal step of the Hanson–Wright inequality
([Vershynin2018], proof of Theorem 6.2.1), with the decoupling constant `4` of the random cuts
and explicit constants in place of the source's unspecified ones. -/
theorem hasSubexponentialMGF_quadForm_sub_diagonal [DecidableEq n]
    (hind : iIndepFun (fun i ω => X ω i) μ) (h : ∀ i, HasSubgaussianMGF (fun ω => X ω i) c μ)
    (A : Matrix n n ℝ) :
    HasSubexponentialMGF (fun ω => quadForm (A - Matrix.diagonal A.diag) (X ω))
      (18 * c ^ 2 * (frobNorm A).toNNReal ^ 2) (12 * c * (specNorm A).toNNReal) μ := by
  have hXm : AEMeasurable X μ := aemeasurable_pi_lambda _ fun i => (h i).aemeasurable
  have hY : AEMeasurable (fun ω => quadForm (A - Matrix.diagonal A.diag) (X ω)) μ := by
    have h' := (continuous_quadForm (A - Matrix.diagonal A.diag)).measurable.comp_aemeasurable hXm
    exact h'
  refine hasSubexponentialMGF_of_lintegral_le hY fun l hl => ?_
  have hb : ((12 * c * (specNorm A).toNNReal : ℝ≥0) : ℝ) = 12 * c * specNorm A := by
    push_cast
    rw [Real.coe_toNNReal _ (specNorm_nonneg A)]
  have hl' : 12 * (c * specNorm A * |l|) ≤ 1 := by
    rw [hb] at hl
    linarith
  refine (lintegral_exp_quadForm_sub_diagonal_le hind h A hl').trans (le_of_eq ?_)
  congr 2
  push_cast
  rw [Real.coe_toNNReal _ (frobNorm_nonneg A)]
  ring

end NLAlib
