/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.QueryModel.HiddenHaar
public import NLAlib.RandomMatrix.Haar.Uniqueness
public import NLAlib.Probability.Measurability.Matrix
public import NLAlib.ForMathlib.Data.Matrix.ColumnRowPartitioned
public import NLAlib.ForMathlib.MeasureTheory.Measure.Prod
public import NLAlib.RandomMatrix.Gaussian.Rank
public import NLAlib.Matrix.Basic.Projector
public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Matrix.Norms.Frobenius
public import Mathlib.Probability.IdentDistrib
public import NLAlib.LowerBounds.QueryModel.Basic
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.ForMathlib.Probability.Independence.Basic
/-!
# Gaussian innovations of adaptive query transcripts

A newly revealed hidden direction can be coupled with a standard Gaussian column by resampling
the unobserved Haar rotation in the stabilizer of the preceding transcript. Singleton innovations
handle dependent directions without padding frames. Replacing the seed columns in their order
preserves the joint Gaussian law and its independence of the initial transcript summary.

## Main results

* `NLAlib.exists_measurable_gaussianBlock_of_ordered_queries`: a measurable Gaussian coupling
  of ordered hidden left-query vectors, jointly independent of an initial transcript summary.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

section StabilizerInnovation

variable {n b c : Type*} [Fintype n] [Fintype b] [Fintype c]
  [DecidableEq n] [DecidableEq b]

/-- A stabilizer Haar rotation sends a fixed complementary frame to compressed Haar law. -/
private theorem map_conjTranspose_stabRand_mul (V : Matrix n c ℝ) (F : Matrix n b ℝ)
    (hF : HasOrthonormalCols F) (hEF : (1 - rangeProjector V) * F = F) :
    (gaussianMatrix n n).map (fun Z => (stabRand V Z)ᴴ * F) =
      (gaussianMatrix n b).map (fun Z => polarFactor ((1 - rangeProjector V) * Z)) := by
  let ρ := (gaussianMatrix n n).map (stabRand V)
  let ν := ρ.map (fun S => Sᴴ * F)
  have hm : Measurable (fun S : Matrix n n ℝ => Sᴴ * F) := by fun_prop
  have hSm := measurable_stabRand_right V
  have hρ : ∀ᵐ S ∂ρ, HasOrthonormalCols S ∧ S * V = V := by
    apply (ae_map_iff hSm.aemeasurable ?_).2
    · exact Filter.Eventually.of_forall (stabRand_spec V)
    · exact isClosed_setOf_hasOrthonormalCols.measurableSet.inter
        (measurableSet_eq_fun (by fun_prop) measurable_const)
  have hPF : rangeProjector V * F = 0 := by
    have h := hEF
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_self] at h
    exact h
  have hν : ∀ᵐ X ∂ν, HasOrthonormalCols X ∧ (1 - rangeProjector V) * X = X := by
    apply (ae_map_iff hm.aemeasurable ?_).2
    · filter_upwards [hρ] with S hS
      refine ⟨hS.1.conjTranspose.mul hF, ?_⟩
      have hSP : S * rangeProjector V = rangeProjector V := by
        rw [← mul_pinv, ← Matrix.mul_assoc, hS.2]
      have hPS : rangeProjector V * Sᴴ = rangeProjector V := by
        simpa only [Matrix.conjTranspose_mul, conjTranspose_rangeProjector] using
          congrArg Matrix.conjTranspose hSP
      rw [Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc, hPS, hPF, sub_zero]
    · exact isClosed_setOf_hasOrthonormalCols.measurableSet.inter
        (measurableSet_eq_fun (by fun_prop) measurable_id)
  have hinv : ∀ s : Matrix n n ℝ, HasOrthonormalCols s →
      s * (1 - (1 - rangeProjector V)) = 1 - (1 - rangeProjector V) →
      ν.map (s * ·) = ν := by
    intro s hs hsP
    have hsP' : s * rangeProjector V = rangeProjector V := by
      simpa only [sub_sub_cancel] using hsP
    have hsV : s * V = V := by
      calc s * V = s * (rangeProjector V * V) := by rw [rangeProjector_mul_self]
        _ = V := by rw [← Matrix.mul_assoc, hsP', rangeProjector_mul_self]
    have hsTV : sᴴ * V = V := by
      calc sᴴ * V = sᴴ * (s * V) := by rw [hsV]
        _ = V := by rw [← Matrix.mul_assoc, hs.conjTranspose_mul_self, Matrix.one_mul]
    have hright := map_mul_right_stabRand V hs.conjTranspose hsTV
    have hsm : Measurable (s * · : Matrix n b ℝ → Matrix n b ℝ) := by fun_prop
    have hrt : Measurable (· * sᴴ : Matrix n n ℝ → Matrix n n ℝ) := by fun_prop
    change (ρ.map (fun S => Sᴴ * F)).map (s * ·) = ρ.map (fun S => Sᴴ * F)
    rw [Measure.map_map hsm hm]
    calc ρ.map ((s * ·) ∘ fun S => Sᴴ * F)
        = ρ.map ((fun S => Sᴴ * F) ∘ (· * sᴴ)) := by
          congr 1
          funext S
          simp only [Function.comp_apply, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = (ρ.map (· * sᴴ)).map (fun S => Sᴴ * F) := (Measure.map_map hm hrt).symm
      _ = ρ.map (fun S => Sᴴ * F) := by rw [hright]
  have : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hSm.aemeasurable
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hm.aemeasurable
  have h := eq_map_polarFactor_mul_of_forall_map_mul_left_eq
    (isStarProjection_one_sub_rangeProjector V) hν hinv
  change ν = _ at h
  simpa only [ν, ρ, Measure.map_map hm hSm, Function.comp_def] using h

/-- Gaussianization of a fixed complementary frame after an independent stabilizer rotation. -/
private theorem map_stabRand_gaussianize (V : Matrix n c ℝ) (F : Matrix n b ℝ)
    (hF : HasOrthonormalCols F) (hEF : (1 - rangeProjector V) * F = F)
    (hb : Fintype.card b ≤ (1 - rangeProjector V).rank) :
    ((gaussianMatrix n n).prod (gaussianMatrix n b)).map
      (fun x => rangeProjector V * x.2 + (stabRand V x.1)ᴴ * F *
        CFC.sqrt (((1 - rangeProjector V) * x.2)ᴴ * ((1 - rangeProjector V) * x.2))) =
      gaussianMatrix n b := by
  let μ := (gaussianMatrix n n).prod (gaussianMatrix n b)
  have hfw : Measurable (fun W : Matrix n n ℝ => (stabRand V W)ᴴ * F) := by fun_prop
  have hW : HasLaw (fun x : Matrix n n ℝ × Matrix n b ℝ => x.1)
      (gaussianMatrix n n) μ := ⟨measurable_fst.aemeasurable, by simp [μ]⟩
  have hY : HasLaw (fun x : Matrix n n ℝ × Matrix n b ℝ => x.2)
      (gaussianMatrix n b) μ := ⟨measurable_snd.aemeasurable, by simp [μ]⟩
  have hFW : HasLaw (fun x : Matrix n n ℝ × Matrix n b ℝ => (stabRand V x.1)ᴴ * F)
      ((gaussianMatrix n b).map fun Z => polarFactor ((1 - rangeProjector V) * Z)) μ := by
    refine ⟨hfw.comp_aemeasurable hW.aemeasurable, ?_⟩
    change μ.map ((fun W => (stabRand V W)ᴴ * F) ∘ Prod.fst) = _
    rw [← AEMeasurable.map_map_of_aemeasurable hfw.aemeasurable hW.aemeasurable, hW.map_eq]
    exact map_conjTranspose_stabRand_mul V F hF hEF
  have hInd : IndepFun (fun x : Matrix n n ℝ × Matrix n b ℝ => (stabRand V x.1)ᴴ * F)
      (fun x => x.2) μ := indepFun_prod hfw measurable_id
  have h := hasLaw_one_sub_mul_add_mul_sqrt_of_hasLaw_gaussianMatrix
    (isStarProjection_one_sub_rangeProjector V) hb hFW hY hInd
  simpa only [sub_sub_cancel, Matrix.mul_assoc] using h.map_eq

/-- An invariant randomization and constant randomized section laws give a product law. -/
private theorem map_prod_of_invariant_randomization {α ω ζ δ : Type*} [MeasurableSpace α]
    [MeasurableSpace ω] [MeasurableSpace ζ] [MeasurableSpace δ]
    (ρ : Measure α) (σ : Measure ω) (γ : Measure ζ)
    [SFinite ρ] [SFinite σ] [SFinite γ]
    (T : α → δ) (hT : Measurable T) (R : α × ω → α) (hR : Measurable R)
    (hInv : (ρ.prod σ).map R = ρ) (hTR : ∀ x w, T (R (x, w)) = T x)
    (K : α × ζ → ζ) (hK : Measurable K)
    (hsec : ∀ᵐ x ∂ρ, (σ.prod γ).map (fun p => K (R (x, p.1), p.2)) = γ) :
    (ρ.prod γ).map (fun p => (T p.1, K p)) = (ρ.map T).prod γ := by
  let L : α × ζ → δ × ζ := fun p => (T p.1, K p)
  have hL : Measurable L := (hT.comp measurable_fst).prodMk hK
  let A : α × (ω × ζ) → α × ζ := fun p => (p.1, K (R (p.1, p.2.1), p.2.2))
  have hA : Measurable A := measurable_fst.prodMk
    (hK.comp ((hR.comp (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd)))
  have hAmap : (ρ.prod (σ.prod γ)).map A = ρ.prod γ :=
    Measure.map_prod_eq_prod_of_ae_map_eq ρ (σ.prod γ)
      (F := fun x p => K (R (x, p.1), p.2)) hA.snd hsec
  have hTout : Measurable (Prod.map T (id : ζ → ζ)) := hT.prodMap measurable_id
  have hRout : Measurable (Prod.map R (id : ζ → ζ)) := hR.prodMap measurable_id
  have hleft : (ρ.prod γ).map L =
      (((ρ.prod σ).prod γ).map (Prod.map R (id : ζ → ζ))).map L := by
    rw [← Measure.map_prod_map (ρ.prod σ) γ hR measurable_id, Measure.map_id, hInv]
  rw [hleft, Measure.map_map hL hRout]
  have hfun : L ∘ Prod.map R (id : ζ → ζ) =
      (Prod.map T (id : ζ → ζ) ∘ A) ∘ MeasurableEquiv.prodAssoc := by
    funext p
    change (T (R (p.1.1, p.1.2)), K (R (p.1.1, p.1.2), p.2)) =
      (T p.1.1, K (R (p.1.1, p.1.2), p.2))
    rw [hTR]
  rw [hfun, ← Measure.map_map (hTout.comp hA) MeasurableEquiv.prodAssoc.measurable,
    Measure.prodAssoc_prod, ← Measure.map_map hTout hA, hAmap,
    ← Measure.map_prod_map ρ γ hT measurable_id, Measure.map_id]

/-- The hidden residual commutes with rotations that fix the revealed subspace. -/
private theorem innovation_conjTranspose_mulVec (V : Matrix n c ℝ) {S : Matrix n n ℝ}
    (hS : HasOrthonormalCols S) (hSV : S * V = V) (v : n → ℝ) :
    (1 - rangeProjector V) *ᵥ (Sᴴ *ᵥ v) = Sᴴ *ᵥ ((1 - rangeProjector V) *ᵥ v) := by
  have hTV : Sᴴ * V = V := by
    calc Sᴴ * V = Sᴴ * (S * V) := by rw [hSV]
      _ = V := by rw [← Matrix.mul_assoc, hS.conjTranspose_mul_self, Matrix.one_mul]
  have hSP : S * rangeProjector V = rangeProjector V := by
    rw [← mul_pinv, ← Matrix.mul_assoc, hSV]
  have hTP : Sᴴ * rangeProjector V = rangeProjector V := by
    rw [← mul_pinv, ← Matrix.mul_assoc, hTV]
  have hPT : rangeProjector V * Sᴴ = rangeProjector V := by
    simpa only [Matrix.conjTranspose_mul, conjTranspose_rangeProjector] using
      congrArg Matrix.conjTranspose hSP
  have hcomm : (1 - rangeProjector V) * Sᴴ = Sᴴ * (1 - rangeProjector V) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hTP, hPT]
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]

/-- The norm of the hidden innovation is unchanged by a stabilizer rotation. -/
private theorem norm_innovation_conjTranspose_mulVec (V : Matrix n c ℝ) {S : Matrix n n ℝ}
    (hS : HasOrthonormalCols S) (hSV : S * V = V) (v : n → ℝ) :
    ‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ (Sᴴ *ᵥ v))‖ =
      ‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖ := by
  rw [innovation_conjTranspose_mulVec V hS hSV, hS.conjTranspose.norm_toLp_mulVec]

/-- The unit column in the direction of the component outside the revealed subspace. -/
private noncomputable def normalizedInnovationColumn (V : Matrix n c ℝ) (v : n → ℝ) :
    Matrix n Unit ℝ := Matrix.replicateCol Unit
      (‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖⁻¹ • ((1 - rangeProjector V) *ᵥ v))

/-- Normalization of the innovation is equivariant under stabilizer rotations. -/
private theorem normalizedInnovationColumn_conjTranspose_mulVec (V : Matrix n c ℝ)
    {S : Matrix n n ℝ} (hS : HasOrthonormalCols S) (hSV : S * V = V) (v : n → ℝ) :
    normalizedInnovationColumn V (Sᴴ *ᵥ v) = Sᴴ * normalizedInnovationColumn V v := by
  unfold normalizedInnovationColumn
  rw [norm_innovation_conjTranspose_mulVec V hS hSV,
    innovation_conjTranspose_mulVec V hS hSV, ← Matrix.mulVec_smul, Matrix.replicateCol_mulVec]

open scoped Classical in
/-- A Gaussian innovation aligned with the newly exposed direction. -/
private noncomputable def innovationGaussianize (V : Matrix n c ℝ) (v : n → ℝ)
    (Z : Matrix n Unit ℝ) : Matrix n Unit ℝ :=
  if ‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖ = 0 then Z else
    rangeProjector V * Z + normalizedInnovationColumn V v *
      CFC.sqrt (((1 - rangeProjector V) * Z)ᴴ * ((1 - rangeProjector V) * Z))

/-- Stabilizing the hidden matrix rotates only the chosen innovation column. -/
private theorem innovationGaussianize_conjTranspose_mulVec (V : Matrix n c ℝ)
    {S : Matrix n n ℝ} (hS : HasOrthonormalCols S) (hSV : S * V = V)
    (v : n → ℝ) (Z : Matrix n Unit ℝ) :
    innovationGaussianize V (Sᴴ *ᵥ v) Z =
      if ‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖ = 0 then Z else
        rangeProjector V * Z + Sᴴ * normalizedInnovationColumn V v *
          CFC.sqrt (((1 - rangeProjector V) * Z)ᴴ * ((1 - rangeProjector V) * Z)) := by
  unfold innovationGaussianize
  rw [norm_innovation_conjTranspose_mulVec V hS hSV,
    normalizedInnovationColumn_conjTranspose_mulVec V hS hSV]

/-- Gaussianization remains standard Gaussian even when the query has no new component. -/
private theorem map_innovationGaussianize_of_frame (V : Matrix n c ℝ) (v : n → ℝ)
    (hF : ‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖ ≠ 0 →
      HasOrthonormalCols (normalizedInnovationColumn V v))
    (hEF : (1 - rangeProjector V) * normalizedInnovationColumn V v =
      normalizedInnovationColumn V v) :
    ((gaussianMatrix n n).prod (gaussianMatrix n Unit)).map
      (fun p => innovationGaussianize V ((stabRand V p.1)ᴴ *ᵥ v) p.2) =
        gaussianMatrix n Unit := by
  classical
  by_cases hv : ‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖ = 0
  · have heq : (fun p : Matrix n n ℝ × Matrix n Unit ℝ =>
        innovationGaussianize V ((stabRand V p.1)ᴴ *ᵥ v) p.2) = Prod.snd := by
      funext p
      rw [innovationGaussianize_conjTranspose_mulVec V
        (stabRand_spec V p.1).1 (stabRand_spec V p.1).2, if_pos hv]
    rw [heq, Measure.map_snd_prod]
    simp
  · have hb : Fintype.card Unit ≤ (1 - rangeProjector V).rank := by
      have h := Matrix.rank_mul_le_left (1 - rangeProjector V) (normalizedInnovationColumn V v)
      rwa [hEF, (hF hv).rank_eq] at h
    have heq : (fun p : Matrix n n ℝ × Matrix n Unit ℝ =>
        innovationGaussianize V ((stabRand V p.1)ᴴ *ᵥ v) p.2) =
        fun p => rangeProjector V * p.2 + (stabRand V p.1)ᴴ *
          normalizedInnovationColumn V v *
            CFC.sqrt (((1 - rangeProjector V) * p.2)ᴴ * ((1 - rangeProjector V) * p.2)) := by
      funext p
      rw [innovationGaussianize_conjTranspose_mulVec V
        (stabRand_spec V p.1).1 (stabRand_spec V p.1).2, if_neg hv]
    rw [heq]
    exact map_stabRand_gaussianize V (normalizedInnovationColumn V v) (hF hv) hEF hb

/-- The normalized residual frame gives a Gaussian innovation law in every dimension. -/
private theorem map_innovationGaussianize (V : Matrix n c ℝ) (v : n → ℝ) :
    ((gaussianMatrix n n).prod (gaussianMatrix n Unit)).map
      (fun p => innovationGaussianize V ((stabRand V p.1)ᴴ *ᵥ v) p.2) =
        gaussianMatrix n Unit := by
  apply map_innovationGaussianize_of_frame V v
  · intro hv
    unfold normalizedInnovationColumn
    apply hasOrthonormalCols_replicateCol
    rw [WithLp.toLp_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv]
  · unfold normalizedInnovationColumn
    rw [← Matrix.replicateCol_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      (isStarProjection_one_sub_rangeProjector V).mul_self]

/-- Hidden-coordinate columns exposed by a two-sided transcript. -/
private def stabilizerRevealed {β : Type*} {q : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β)
    (τ : Fin q → (n → ℝ) × (n → ℝ)) : Matrix n (Fin q ⊕ Fin q) ℝ :=
  Matrix.fromCols (alg.rightQueryMatrix τ) (Matrix.of fun r j => (τ j).2 r)

omit [Fintype n] [DecidableEq n] in
/-- The exposed block is a measurable function of a transcript. -/
private theorem measurable_stabilizerRevealed {β : Type*} [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β}
    (halg : alg.IsMeasurable) : Measurable (stabilizerRevealed alg) := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun j => ?_
  cases j with
  | inl j =>
    change Measurable (fun τ : Fin q → (n → ℝ) × (n → ℝ) => (alg.rightQueryMatrix τ) r j)
    exact (measurable_pi_apply j).comp
      ((measurable_pi_apply r).comp halg.measurable_rightQueryMatrix)
  | inr j =>
    change Measurable (fun τ : Fin q → (n → ℝ) × (n → ℝ) => (τ j).2 r)
    exact (measurable_pi_apply r).comp (measurable_snd.comp (measurable_pi_apply j))

/-- Haar hidden matrices may be resampled within the stabilizer of a transcript. -/
private theorem map_transcript_stabRand {β : Type*} [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β}
    (halg : alg.IsMeasurable) :
    ((haarFrame n n).prod (gaussianMatrix n n)).map
      (fun p => (alg.transcript (twoSidedMulVec p.1),
        p.1 * stabRand (stabilizerRevealed alg (alg.transcript (twoSidedMulVec p.1))) p.2)) =
      (haarFrame n n).map (fun U => (alg.transcript (twoSidedMulVec U), U)) := by
  let μ := (haarFrame n n).prod (gaussianMatrix n n)
  have hU : HasLaw (fun p : Matrix n n ℝ × Matrix n n ℝ => p.1) (haarFrame n n) μ :=
    ⟨measurable_fst.aemeasurable, by simp [μ]⟩
  have hW : HasLaw (fun p : Matrix n n ℝ × Matrix n n ℝ => p.2) (gaussianMatrix n n) μ :=
    ⟨measurable_snd.aemeasurable, by simp [μ]⟩
  let S := fun τ W => stabRand (stabilizerRevealed alg τ) W
  have hSm : Measurable (Function.uncurry S) :=
    Measurable.stabRand ((measurable_stabilizerRevealed halg).comp measurable_fst) measurable_snd
  have hfix (τ : Fin q → (n → ℝ) × (n → ℝ)) (W : Matrix n n ℝ) :
      S τ W * alg.rightQueryMatrix τ = alg.rightQueryMatrix τ ∧
        S τ W * Matrix.of (fun r j => (τ j).2 r) = Matrix.of (fun r j => (τ j).2 r) := by
    have h := (stabRand_spec (stabilizerRevealed alg τ) W).2
    change S τ W * Matrix.fromCols _ _ = Matrix.fromCols _ _ at h
    rw [Matrix.mul_fromCols] at h
    exact Matrix.fromCols_inj h
  have h := halg.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant_of_indepFun
    hU hW.aemeasurable (indepFun_prod measurable_id measurable_id)
    hSm (fun τ W => (stabRand_spec (stabilizerRevealed alg τ) W).1)
    (fun τ W => (hfix τ W).1) (fun τ W => (hfix τ W).2)
  have hm : Measurable (fun U : Matrix n n ℝ => (alg.transcript (twoSidedMulVec U), U)) :=
    (halg.measurable_transcript (Measurable.twoSidedMulVec measurable_fst measurable_snd)).prodMk
      measurable_id
  calc μ.map (fun p => (alg.transcript (twoSidedMulVec p.1), p.1 * S _ p.2))
      = μ.map (fun p => (alg.transcript (twoSidedMulVec p.1), p.1)) := h.map_eq.symm
    _ = (haarFrame n n).map (fun U => (alg.transcript (twoSidedMulVec U), U)) := by
      change μ.map ((fun U => (alg.transcript (twoSidedMulVec U), U)) ∘ Prod.fst) = _
      rw [← Measure.map_map hm measurable_fst, Measure.map_fst_prod]
      simp

/-- The square root on real square matrices is measurable. -/
private theorem measurable_sqrt_unit :
    Measurable (CFC.sqrt : Matrix Unit Unit ℝ → Matrix Unit Unit ℝ) := by
  classical
  have h : Measurable ({a : Matrix Unit Unit ℝ | 0 ≤ a}.piecewise CFC.sqrt 0) := by
    open scoped Matrix.Norms.L2Operator in
    exact CFC.continuousOn_sqrt.measurable_piecewise continuousOn_const
      isClosed_Ici.measurableSet
  convert h using 1
  funext a
  by_cases ha : 0 ≤ a
  · exact (Set.piecewise_eq_of_mem (s := {a : Matrix Unit Unit ℝ | 0 ≤ a}) _ _ ha).symm
  · rw [Set.piecewise_eq_of_notMem (s := {a : Matrix Unit Unit ℝ | 0 ≤ a}) _ _ ha,
      CFC.sqrt_of_not_nonneg ha, Pi.zero_apply]

/-- The normalized innovation column is jointly measurable. -/
private theorem measurable_normalizedInnovationColumn {α : Type*} [MeasurableSpace α]
    {V : α → Matrix n c ℝ} {v : α → (n → ℝ)} (hV : Measurable V) (hv : Measurable v) :
    Measurable (fun a => normalizedInnovationColumn (V a) (v a)) := by
  have hE : Measurable (fun a => 1 - rangeProjector (V a)) :=
    measurable_const.matrix_sub (measurable_rangeProjector.comp hV)
  have hr := hE.matrix_mulVec hv
  have hnorm : Measurable (fun a => ‖WithLp.toLp 2 ((1 - rangeProjector (V a)) *ᵥ v a)‖) :=
    ((WithLp.measurable_toLp _ _).comp hr).norm
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  change Measurable (fun a => ‖WithLp.toLp 2 ((1 - rangeProjector (V a)) *ᵥ v a)‖⁻¹ *
    ((1 - rangeProjector (V a)) *ᵥ v a) i)
  exact hnorm.inv.mul ((measurable_pi_apply i).comp hr)

/-- The Gaussian innovation kernel is jointly measurable. -/
private theorem measurable_innovationGaussianize {α : Type*} [MeasurableSpace α]
    {V : α → Matrix n c ℝ} {v : α → (n → ℝ)} {Z : α → Matrix n Unit ℝ}
    (hV : Measurable V) (hv : Measurable v) (hZ : Measurable Z) :
    Measurable (fun a => innovationGaussianize (V a) (v a) (Z a)) := by
  have hP : Measurable (fun a => rangeProjector (V a)) := measurable_rangeProjector.comp hV
  have hE : Measurable (fun a => 1 - rangeProjector (V a)) := measurable_const.matrix_sub hP
  have hnorm : Measurable (fun a => ‖WithLp.toLp 2 ((1 - rangeProjector (V a)) *ᵥ v a)‖) :=
    ((WithLp.measurable_toLp _ _).comp (hE.matrix_mulVec hv)).norm
  have hN := measurable_normalizedInnovationColumn hV hv
  have hB := hE.matrix_mul hZ
  unfold innovationGaussianize
  exact Measurable.ite (measurableSet_eq_fun hnorm measurable_const) hZ
    ((hP.matrix_mul hZ).matrix_add
      (hN.matrix_mul (measurable_sqrt_unit.comp
        ((Measurable.matrix_conjTranspose (by fun_prop) hB).matrix_mul hB))))

/-- One newly exposed hidden-coordinate query admits a Gaussian coupling independent of history. -/
private theorem map_transcript_innovationGaussianize {β : Type*} [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β}
    (halg : alg.IsMeasurable) (x : (Fin q → (n → ℝ) × (n → ℝ)) → (n → ℝ))
    (hx : Measurable x) :
    ((haarFrame n n).prod (gaussianMatrix n Unit)).map
      (fun p => (alg.transcript (twoSidedMulVec p.1),
        innovationGaussianize (stabilizerRevealed alg (alg.transcript (twoSidedMulVec p.1)))
          (p.1ᴴ *ᵥ x (alg.transcript (twoSidedMulVec p.1))) p.2)) =
      ((haarFrame n n).map (fun U => alg.transcript (twoSidedMulVec U))).prod
        (gaussianMatrix n Unit) := by
  let A := (Fin q → (n → ℝ) × (n → ℝ)) × Matrix n n ℝ
  let f : Matrix n n ℝ → A := fun U => (alg.transcript (twoSidedMulVec U), U)
  have hf : Measurable f :=
    (halg.measurable_transcript (Measurable.twoSidedMulVec measurable_fst measurable_snd)).prodMk
      measurable_id
  let ρ := (haarFrame n n).map f
  let σ := gaussianMatrix n n
  let γ := gaussianMatrix n Unit
  let R : A × Matrix n n ℝ → A := fun p =>
    (p.1.1, p.1.2 * stabRand (stabilizerRevealed alg p.1.1) p.2)
  have hV : Measurable (fun p : A × Matrix n n ℝ => stabilizerRevealed alg p.1.1) :=
    (measurable_stabilizerRevealed halg).comp (measurable_fst.comp measurable_fst)
  have hR : Measurable R := (measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).matrix_mul (Measurable.stabRand hV measurable_snd))
  have hInv : (ρ.prod σ).map R = ρ := by
    have hp : ρ.prod σ = ((haarFrame n n).prod σ).map (Prod.map f (id : Matrix n n ℝ → _)) := by
      simpa only [ρ, Measure.map_id] using
        Measure.map_prod_map (haarFrame n n) σ hf measurable_id
    rw [hp, Measure.map_map hR (hf.prodMap measurable_id)]
    exact map_transcript_stabRand halg
  let K : A × Matrix n Unit ℝ → Matrix n Unit ℝ := fun p =>
    innovationGaussianize (stabilizerRevealed alg p.1.1) (p.1.2ᴴ *ᵥ x p.1.1) p.2
  have hK : Measurable K := measurable_innovationGaussianize
    ((measurable_stabilizerRevealed halg).comp (measurable_fst.comp measurable_fst))
    ((Measurable.matrix_conjTranspose (by fun_prop)
      (measurable_snd.comp measurable_fst)).matrix_mulVec
      (hx.comp (measurable_fst.comp measurable_fst))) measurable_snd
  have hsec : ∀ᵐ a ∂ρ, (σ.prod γ).map (fun p => K (R (a, p.1), p.2)) = γ := by
    apply Filter.Eventually.of_forall
    intro a
    have heq : (fun p : Matrix n n ℝ × Matrix n Unit ℝ => K (R (a, p.1), p.2)) =
        fun p => innovationGaussianize (stabilizerRevealed alg a.1)
          ((stabRand (stabilizerRevealed alg a.1) p.1)ᴴ *ᵥ (a.2ᴴ *ᵥ x a.1)) p.2 := by
      funext p
      simp only [K, R, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec]
    rw [heq]
    exact map_innovationGaussianize (stabilizerRevealed alg a.1) (a.2ᴴ *ᵥ x a.1)
  have hstep := map_prod_of_invariant_randomization ρ σ γ Prod.fst measurable_fst R hR hInv
    (fun _ _ => rfl) K hK hsec
  have hp : ρ.prod γ = ((haarFrame n n).prod γ).map (Prod.map f (id : Matrix n Unit ℝ → _)) := by
    simpa only [ρ, Measure.map_id] using
      Measure.map_prod_map (haarFrame n n) γ hf measurable_id
  have hL : Measurable (fun p : A × Matrix n Unit ℝ => (p.1.1, K p)) :=
    (measurable_fst.comp measurable_fst).prodMk hK
  rw [hp, Measure.map_map hL (hf.prodMap measurable_id)] at hstep
  have hρ : ρ.map Prod.fst = (haarFrame n n).map (fun U => alg.transcript (twoSidedMulVec U)) := by
    dsimp only [ρ]
    rw [Measure.map_map measurable_fst hf]
    rfl
  rw [hρ] at hstep
  exact hstep

/-- The one-query coupling law transfers to any space carrying independent Haar and Gaussian
data. -/
private theorem hasLaw_transcript_innovationGaussianize {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {β : Type*} [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β}
    (halg : alg.IsMeasurable) (x : (Fin q → (n → ℝ) × (n → ℝ)) → (n → ℝ))
    (hx : Measurable x) {U : Ω → Matrix n n ℝ} {Z : Ω → Matrix n Unit ℝ}
    (hU : HasLaw U (haarFrame n n) μ) (hZ : HasLaw Z (gaussianMatrix n Unit) μ)
    (hUZ : IndepFun U Z μ) :
    HasLaw (fun ω => (alg.transcript (twoSidedMulVec (U ω)),
        innovationGaussianize (stabilizerRevealed alg (alg.transcript (twoSidedMulVec (U ω))))
          ((U ω)ᴴ *ᵥ x (alg.transcript (twoSidedMulVec (U ω)))) (Z ω)))
      (((haarFrame n n).map (fun U => alg.transcript (twoSidedMulVec U))).prod
        (gaussianMatrix n Unit)) μ := by
  have := hU.isProbabilityMeasure
  have hpair : HasLaw (fun ω => (U ω, Z ω))
      ((haarFrame n n).prod (gaussianMatrix n Unit)) μ := by
    refine ⟨hU.aemeasurable.prodMk hZ.aemeasurable, ?_⟩
    rw [(indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hZ.aemeasurable).1 hUZ,
      hU.map_eq, hZ.map_eq]
  let τ := fun U : Matrix n n ℝ => alg.transcript (twoSidedMulVec U)
  have hτ : Measurable τ :=
    halg.measurable_transcript (Measurable.twoSidedMulVec measurable_fst measurable_snd)
  let φ : Matrix n n ℝ × Matrix n Unit ℝ →
      (Fin q → (n → ℝ) × (n → ℝ)) × Matrix n Unit ℝ := fun p =>
    (τ p.1, innovationGaussianize (stabilizerRevealed alg (τ p.1)) (p.1ᴴ *ᵥ x (τ p.1)) p.2)
  have hφ : Measurable φ := (hτ.comp measurable_fst).prodMk
    (measurable_innovationGaussianize
      ((measurable_stabilizerRevealed halg).comp (hτ.comp measurable_fst))
      ((Measurable.matrix_conjTranspose (by fun_prop) measurable_fst).matrix_mulVec
        (hx.comp (hτ.comp measurable_fst))) measurable_snd)
  refine ⟨hφ.comp_aemeasurable hpair.aemeasurable, ?_⟩
  change μ.map (φ ∘ fun ω => (U ω, Z ω)) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hφ.aemeasurable hpair.aemeasurable, hpair.map_eq]
  exact map_transcript_innovationGaussianize halg x hx

end StabilizerInnovation

section InnovationCapture

variable {n c : Type*} [Fintype n] [Fintype c] [DecidableEq n]

/-- A normalized innovation scaled by a nonzero radius captures the queried vector modulo the
previously revealed column space. -/
private theorem mem_sup_span_singleton_of_normalized_innovation
    (V : Matrix n c ℝ) (v z : n → ℝ) {r : ℝ} (hr : r ≠ 0)
    (hv : ‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖ ≠ 0) :
    v ∈ LinearMap.range V.mulVecLin ⊔ Submodule.span ℝ
      {rangeProjector V *ᵥ z + r •
        (‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖⁻¹ •
          ((1 - rangeProjector V) *ᵥ v))} := by
  classical
  let P := rangeProjector V
  let s := ‖WithLp.toLp 2 ((1 - P) *ᵥ v)‖
  let g := P *ᵥ z + r • (s⁻¹ • ((1 - P) *ᵥ v))
  let T := LinearMap.range V.mulVecLin ⊔ Submodule.span ℝ {g}
  have hP (w : n → ℝ) : P *ᵥ w ∈ LinearMap.range V.mulVecLin := by
    rw [← range_rangeProjector V]
    exact ⟨w, rfl⟩
  have hPg : P *ᵥ z ∈ T := Submodule.mem_sup_left (hP z)
  have hg : g ∈ T := Submodule.mem_sup_right
    (Submodule.subset_span (Set.mem_singleton g))
  have hs : s ≠ 0 := hv
  have hcoef : s / r * (r * s⁻¹) = 1 := by field_simp
  have hrepr : v = P *ᵥ v + (s / r) • (g - P *ᵥ z) := by
    simp only [g, add_sub_cancel_left, smul_smul, hcoef, one_smul]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
  change v ∈ T
  rw [hrepr]
  exact T.add_mem (Submodule.mem_sup_left (hP v))
    (T.smul_mem _ (T.sub_mem hg hPg))

/-- If the innovation is zero, the vector was already revealed. -/
private theorem mem_range_of_innovation_eq_zero (V : Matrix n c ℝ) (v : n → ℝ)
    (hv : (1 - rangeProjector V) *ᵥ v = 0) : v ∈ LinearMap.range V.mulVecLin := by
  apply rangeProjector_mulVec_eq_self_iff.mp
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  exact hv.symm

/-- A full-rank innovation block captures its frame modulo the revealed subspace. -/
private theorem range_le_sup_of_innovation_block {b : Type*} [Fintype b] [DecidableEq b]
    (V : Matrix n c ℝ) (F G : Matrix n b ℝ) (S : Matrix b b ℝ) (hS : IsUnit S)
    (hG : (1 - rangeProjector V) * G = F * S) :
    LinearMap.range F.mulVecLin ≤ LinearMap.range V.mulVecLin ⊔
      LinearMap.range G.mulVecLin := by
  have hrange : LinearMap.range (F * S).mulVecLin = LinearMap.range F.mulVecLin :=
    rangeProjector_inj.mp (rangeProjector_mul_of_isUnit F hS)
  rw [← hrange, ← hG]
  rintro _ ⟨x, rfl⟩
  rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  apply Submodule.sub_mem
  · exact Submodule.mem_sup_right ⟨x, rfl⟩
  · apply Submodule.mem_sup_left
    rw [← range_rangeProjector V]
    exact ⟨G *ᵥ x, rfl⟩

omit [DecidableEq n] in
/-- The square root of the one-column Gram matrix is its vector norm. -/
private theorem sqrt_gram_replicateCol_unit (v : n → ℝ) :
    CFC.sqrt ((Matrix.replicateCol Unit v)ᴴ * Matrix.replicateCol Unit v) =
      ‖WithLp.toLp 2 v‖ • (1 : Matrix Unit Unit ℝ) := by
  have hgram : (Matrix.replicateCol Unit v)ᴴ * Matrix.replicateCol Unit v =
      ‖WithLp.toLp 2 v‖ ^ 2 • (1 : Matrix Unit Unit ℝ) := by
    have h := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 v)
    ext a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.replicateCol_apply,
      RCLike.star_def, RCLike.conj_mul, Matrix.smul_apply, Matrix.one_apply,
      Subsingleton.elim a b, if_true, smul_eq_mul, mul_one]
    exact_mod_cast h.symm
  apply CFC.sqrt_unique
  · rw [hgram, smul_mul_smul_comm, Matrix.one_mul, ← sq]
  · exact smul_nonneg (norm_nonneg _) zero_le_one

/-- The normalized nonzero residual is an orthonormal one-column frame. -/
private theorem hasOrthonormalCols_normalized_innovation
    (V : Matrix n c ℝ) (v : n → ℝ)
    (hv : ‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖ ≠ 0) :
    HasOrthonormalCols (Matrix.replicateCol Unit
      (‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖⁻¹ •
        ((1 - rangeProjector V) *ᵥ v))) := by
  apply hasOrthonormalCols_replicateCol
  rw [WithLp.toLp_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv]

/-- The normalized residual lies in the complementary projection. -/
private theorem projection_mul_normalized_innovation
    (V : Matrix n c ℝ) (v : n → ℝ) :
    (1 - rangeProjector V) * Matrix.replicateCol Unit
      (‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖⁻¹ •
        ((1 - rangeProjector V) *ᵥ v)) =
      Matrix.replicateCol Unit
      (‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖⁻¹ •
        ((1 - rangeProjector V) *ᵥ v)) := by
  rw [← Matrix.replicateCol_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    (isStarProjection_one_sub_rangeProjector V).mul_self]

/-- A nonzero innovation ensures that the complementary projection has positive rank. -/
private theorem one_le_rank_of_innovation_ne_zero
    (V : Matrix n c ℝ) (v : n → ℝ)
    (hv : ‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖ ≠ 0) :
    1 ≤ (1 - rangeProjector V).rank := by
  let F := Matrix.replicateCol Unit
    (‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖⁻¹ •
      ((1 - rangeProjector V) *ᵥ v))
  have hF : HasOrthonormalCols F := hasOrthonormalCols_normalized_innovation V v hv
  have hEF : (1 - rangeProjector V) * F = F := projection_mul_normalized_innovation V v
  calc
    1 = F.rank := by rw [hF.rank_eq, Fintype.card_unit]
    _ = ((1 - rangeProjector V) * F).rank := congrArg Matrix.rank hEF.symm
    _ ≤ (1 - rangeProjector V).rank := Matrix.rank_mul_le_left _ _

/-- The matrix form of a Gaussianized singleton captures the query modulo the revealed space. -/
private theorem mem_sup_range_of_innovation_matrix
    (V : Matrix n c ℝ) (v : n → ℝ) (Z : Matrix n Unit ℝ)
    (S : Matrix Unit Unit ℝ) (hS : IsUnit S)
    (hv : ‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖ ≠ 0) :
    v ∈ LinearMap.range V.mulVecLin ⊔ LinearMap.range
      (rangeProjector V * Z + Matrix.replicateCol Unit
        (‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖⁻¹ •
          ((1 - rangeProjector V) *ᵥ v)) * S).mulVecLin := by
  let E := 1 - rangeProjector V
  let s := ‖WithLp.toLp 2 (E *ᵥ v)‖
  let f := s⁻¹ • (E *ᵥ v)
  let F := Matrix.replicateCol Unit f
  let G := rangeProjector V * Z + F * S
  let T := LinearMap.range V.mulVecLin ⊔ LinearMap.range G.mulVecLin
  have hEF : E * F = F := projection_mul_normalized_innovation V v
  have hEP : E * rangeProjector V = 0 := by
    dsimp only [E]
    rw [Matrix.sub_mul, Matrix.one_mul, rangeProjector_mul_rangeProjector, sub_self]
  have hEG : E * G = F * S := by
    dsimp only [G]
    rw [Matrix.mul_add, ← Matrix.mul_assoc, hEP, Matrix.zero_mul, zero_add,
      ← Matrix.mul_assoc, hEF]
  have hFle : LinearMap.range F.mulVecLin ≤ T :=
    range_le_sup_of_innovation_block V F G S hS hEG
  have hf : f ∈ T := hFle ⟨fun _ => 1, by
    ext i
    simp [F, Matrix.mulVec, dotProduct]⟩
  have hPv : rangeProjector V *ᵥ v ∈ T := by
    apply Submodule.mem_sup_left
    rw [← range_rangeProjector V]
    exact ⟨v, rfl⟩
  have hs : s ≠ 0 := hv
  have hrepr : v = rangeProjector V *ᵥ v + s • f := by
    dsimp only [f]
    rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
    dsimp only [E]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
  change v ∈ T
  rw [hrepr]
  exact T.add_mem hPv (T.smul_mem s hf)

/-- A Gaussianized singleton captures the queried vector almost surely. -/
private theorem ae_mem_sup_range_innovationGaussianize
    (V : Matrix n c ℝ) (v : n → ℝ) :
    ∀ᵐ Z ∂gaussianMatrix n Unit,
      v ∈ LinearMap.range V.mulVecLin ⊔
        LinearMap.range (innovationGaussianize V v Z).mulVecLin := by
  classical
  by_cases hv : ‖WithLp.toLp 2 ((1 - rangeProjector V) *ᵥ v)‖ = 0
  · have hv' : (1 - rangeProjector V) *ᵥ v = 0 := by
      simpa only [norm_eq_zero, WithLp.toLp_eq_zero] using hv
    exact Filter.Eventually.of_forall fun Z =>
      Submodule.mem_sup_left (mem_range_of_innovation_eq_zero V v hv')
  · have hr : Fintype.card Unit ≤ (1 - rangeProjector V).rank := by
      simpa using one_le_rank_of_innovation_ne_zero V v hv
    filter_upwards [ae_isUnit_conjTranspose_mul_self_mul_of_hasLaw_gaussianMatrix hr
      (HasLaw.id (μ := gaussianMatrix n Unit))] with Z hZ
    have hS : IsUnit (CFC.sqrt (((1 - rangeProjector V) * Z)ᴴ *
        ((1 - rangeProjector V) * Z))) :=
      (CFC.isUnit_sqrt_iff _ (Matrix.posSemidef_conjTranspose_mul_self _).nonneg).mpr hZ
    simpa only [innovationGaussianize, if_neg hv, normalizedInnovationColumn] using
      mem_sup_range_of_innovation_matrix V v Z _ hS hv

/-- Freeze a measurable family of previously revealed spaces to get capture on the product. -/
private theorem ae_prod_mem_sup_range_innovationGaussianize {α : Type*} [MeasurableSpace α]
    (ρ : Measure α) (V : α → Matrix n c ℝ) (v : α → n → ℝ)
    (hV : Measurable V) (hv : Measurable v)
    (hK : Measurable (fun p : α × Matrix n Unit ℝ =>
      innovationGaussianize (V p.1) (v p.1) p.2)) :
    ∀ᵐ p ∂ρ.prod (gaussianMatrix n Unit), v p.1 ∈ LinearMap.range (V p.1).mulVecLin ⊔
      LinearMap.range (innovationGaussianize (V p.1) (v p.1) p.2).mulVecLin := by
  have hM : Measurable (fun p : α × Matrix n Unit ℝ =>
      Matrix.fromCols (V p.1) (innovationGaussianize (V p.1) (v p.1) p.2)) := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    cases j with
    | inl j =>
      exact (measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp (hV.comp measurable_fst))
    | inr j =>
      exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hK)
  have hset : MeasurableSet {p : α × Matrix n Unit ℝ |
      v p.1 ∈ LinearMap.range (V p.1).mulVecLin ⊔
        LinearMap.range (innovationGaussianize (V p.1) (v p.1) p.2).mulVecLin} := by
    simp only [← Matrix.range_fromCols_eq_sup, ← rangeProjector_mulVec_eq_self_iff]
    exact measurableSet_eq_fun
      ((measurable_rangeProjector.comp hM).matrix_mulVec (hv.comp measurable_fst))
      (hv.comp measurable_fst)
  apply (Measure.ae_prod_iff_ae_ae hset).mpr
  exact Filter.Eventually.of_forall fun t => ae_mem_sup_range_innovationGaussianize (V t) (v t)

end InnovationCapture

/-! ### Transporting joint laws through measurable reconstructions -/

section Transport

variable {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω}

/-- A joint-law identity transports through any measurable reconstruction, including when the
reconstruction agrees with the mixed arrays only almost surely. -/
private theorem identDistrib_of_joint_reconstruction
    {A : Ω → α} {X Y : Ω → β} {H H' : Ω → γ} {F : α × β → γ}
    (h : IdentDistrib (fun ω => (A ω, X ω)) (fun ω => (A ω, Y ω)) μ μ)
    (hF : Measurable F)
    (hH : H =ᵐ[μ] fun ω => F (A ω, X ω))
    (hH' : H' =ᵐ[μ] fun ω => F (A ω, Y ω)) : IdentDistrib H H' μ μ := by
  have hc := h.comp hF
  exact ((IdentDistrib.of_ae_eq hc.aemeasurable_fst hH.symm).symm.trans hc).trans
    (IdentDistrib.of_ae_eq hc.aemeasurable_snd hH'.symm)

/-- Iterating adjacent identical distributions gives the law of the endpoint mixed array. -/
private theorem identDistrib_zero_of_forall_succ {H : ℕ → Ω → γ} {m : ℕ}
    (h0 : AEMeasurable (H 0) μ)
    (hstep : ∀ i < m, IdentDistrib (H i) (H (i + 1)) μ μ) :
    IdentDistrib (H 0) (H m) μ μ := by
  have h : ∀ i ≤ m, IdentDistrib (H 0) (H i) μ μ := by
    intro i hi
    induction i with
    | zero => exact IdentDistrib.refl h0
    | succ i ih => exact (ih (Nat.le_of_succ_le hi)).trans (hstep i hi)
  exact h m le_rfl

/-- It suffices to identify the law of each updated block jointly with a summary that reconstructs
both neighboring mixed arrays. The summary and block spaces may vary from pass to pass. -/
private theorem identDistrib_zero_of_joint_reconstructions
    {T V : ℕ → Type*} [∀ i, MeasurableSpace (T i)] [∀ i, MeasurableSpace (V i)]
    {H : ℕ → Ω → γ} {m : ℕ}
    (A : (i : ℕ) → Ω → T i) (X Y : (i : ℕ) → Ω → V i)
    (F : (i : ℕ) → T i × V i → γ)
    (h0 : AEMeasurable (H 0) μ)
    (hlaw : ∀ i < m,
      IdentDistrib (fun ω => (A i ω, X i ω)) (fun ω => (A i ω, Y i ω)) μ μ)
    (hF : ∀ i < m, Measurable (F i))
    (hleft : ∀ i < m, H i =ᵐ[μ] fun ω => F i (A i ω, X i ω))
    (hright : ∀ i < m, H (i + 1) =ᵐ[μ] fun ω => F i (A i ω, Y i ω)) :
    IdentDistrib (H 0) (H m) μ μ := by
  refine identDistrib_zero_of_forall_succ h0 fun i hi => ?_
  exact identDistrib_of_joint_reconstruction (hlaw i hi) (hF i hi)
    (hleft i hi) (hright i hi)

/-- The hidden vectors fixed by transcript-preserving rotations depend measurably on the
transcript of a measurable two-sided algorithm. -/
private theorem measurable_coupling_revealed {n m δ : Type*} [MeasurableSpace δ] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) q δ}
    (halg : alg.IsMeasurable) :
    Measurable (fun τ : Fin q → (m → ℝ) × (n → ℝ) =>
      Matrix.fromCols (alg.rightQueryMatrix τ) (Matrix.of fun r j => (τ j).2 r)) := by
  have hQ := halg.measurable_rightQueryMatrix (𝕜 := ℝ)
  refine measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun j => ?_
  rcases j with j | j
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply r).comp hQ)
  · exact (measurable_pi_apply r).comp (measurable_snd.comp (measurable_pi_apply j))


/-- A chosen column of a Gaussian matrix and all the remaining columns have the product law. -/
private theorem hasLaw_col_otherCols {n J : Type*} [Fintype n] [Fintype J] [DecidableEq J]
    {Z : Ω → Matrix n J ℝ} (hZ : HasLaw Z (gaussianMatrix n J) μ) (i : J) :
    HasLaw (fun ω => (Matrix.replicateCol Unit ((Z ω).col i),
      (Z ω).submatrix id (Subtype.val : {j // j ≠ i} → J)))
      ((gaussianMatrix n Unit).prod (gaussianMatrix n {j // j ≠ i})) μ := by
  have := hZ.isProbabilityMeasure
  have hcur : HasLaw (fun ω => Matrix.replicateCol Unit ((Z ω).col i))
      (gaussianMatrix n Unit) μ :=
    hasLaw_submatrix_of_hasLaw_gaussianMatrix hZ Function.injective_id
      (Function.injective_of_subsingleton (fun _ : Unit => i))
  have hrest : HasLaw (fun ω => (Z ω).submatrix id (Subtype.val : {j // j ≠ i} → J))
      (gaussianMatrix n {j // j ≠ i}) μ :=
    hasLaw_submatrix_of_hasLaw_gaussianMatrix hZ Function.injective_id Subtype.val_injective
  refine (indepFun_iff_hasLaw_prodMk_prod hcur hrest).1 ?_
  have hind := (iIndepFun_col_of_hasLaw_gaussianMatrix hZ).indepFun_finset₀ {i}
    (Finset.univ.filter (· ≠ i)) (by simp) fun j =>
      (hasLaw_col_of_hasLaw_gaussianMatrix hZ j).aemeasurable
  have h₁ : Measurable (fun f : ({i} : Finset J) → n → ℝ =>
      Matrix.replicateCol Unit (f ⟨i, Finset.mem_singleton_self i⟩)) := by
    exact measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun _ =>
      (measurable_pi_apply r).comp (measurable_pi_apply _)
  have h₂ : Measurable (fun f : (Finset.univ.filter (· ≠ i) : Finset J) → n → ℝ =>
      (fun r (j : {j // j ≠ i}) => f ⟨j.1, by simpa using j.2⟩ r :
        Matrix n {j // j ≠ i} ℝ)) := by
    exact measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun j =>
      (measurable_pi_apply r).comp (measurable_pi_apply _)
  exact hind.comp h₁ h₂

/-- A joint-law identity remains true after adjoining an independent variable on a product
space. -/
private theorem identDistrib_prodMap_id {δ : Type*} [MeasurableSpace δ]
    {ρ : Measure α} {η : Measure δ} [SFinite ρ] [SFinite η] {f g : α → β}
    (hf : Measurable f) (hg : Measurable g) (hfg : ρ.map f = ρ.map g) :
    IdentDistrib (Prod.map f id) (Prod.map g id) (ρ.prod η) (ρ.prod η) := by
  refine ⟨(hf.prodMap measurable_id).aemeasurable,
    (hg.prodMap measurable_id).aemeasurable, ?_⟩
  rw [← Measure.map_prod_map _ _ hf measurable_id,
    ← Measure.map_prod_map _ _ hg measurable_id, hfg]


/-- Splitting off one Gaussian column commutes with adjoining an independent base variable. -/
private theorem hasLaw_base_col_otherCols {n J : Type*} [Fintype n] [Fintype J]
    [DecidableEq J] (ρ : Measure α) [SFinite ρ] (i : J) :
    HasLaw (fun x : α × Matrix n J ℝ =>
      ((x.1, Matrix.replicateCol Unit (x.2.col i)),
        x.2.submatrix id (Subtype.val : {j // j ≠ i} → J)))
      ((ρ.prod (gaussianMatrix n Unit)).prod (gaussianMatrix n {j // j ≠ i}))
      (ρ.prod (gaussianMatrix n J)) := by
  let S : Matrix n J ℝ → Matrix n Unit ℝ × Matrix n {j // j ≠ i} ℝ :=
    fun Z => (Matrix.replicateCol Unit (Z.col i), Z.submatrix id Subtype.val)
  have hS : Measurable S := by
    refine (measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun _ => ?_).prodMk ?_
    · exact (measurable_pi_apply i).comp (measurable_pi_apply r)
    · exact measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun j =>
        (measurable_pi_apply j.val).comp (measurable_pi_apply r)
  have hSlaw := hasLaw_col_otherCols (HasLaw.id (μ := gaussianMatrix n J)) i
  have hsplit : (ρ.prod (gaussianMatrix n J)).map (Prod.map id S) =
      ρ.prod ((gaussianMatrix n Unit).prod (gaussianMatrix n {j // j ≠ i})) := by
    rw [← Measure.map_prod_map _ _ measurable_id hS, Measure.map_id]
    exact congrArg (Measure.prod ρ) (by simpa only [S, id_eq] using hSlaw.map_eq)
  have hassoc := (measurePreserving_prodAssoc ρ (gaussianMatrix n Unit)
    (gaussianMatrix n {j // j ≠ i})).symm
  refine ⟨(hassoc.measurable.comp (measurable_id.prodMap hS)).aemeasurable, ?_⟩
  change (ρ.prod (gaussianMatrix n J)).map
    (MeasurableEquiv.prodAssoc.symm ∘ Prod.map id S) = _
  rw [← Measure.map_map hassoc.measurable (measurable_id.prodMap hS), hsplit,
    hassoc.map_eq]

/-- If a single-seed kernel preserves its joint law with a base summary, then the same identity
holds jointly with every other column of a Gaussian seed matrix. -/
private theorem map_summary_otherCols_kernel {n J τ : Type*} [Fintype n] [Fintype J]
    [MeasurableSpace τ] (ρ : Measure α) [SFinite ρ] (i : J)
    (T : α → τ) (K : α × Matrix n Unit ℝ → Matrix n Unit ℝ)
    (hT : Measurable T) (hK : Measurable K)
    (hkernel : (ρ.prod (gaussianMatrix n Unit)).map (fun x => (T x.1, K x)) =
      (ρ.map T).prod (gaussianMatrix n Unit)) :
    (ρ.prod (gaussianMatrix n J)).map (fun x =>
      ((T x.1, x.2.submatrix id (Subtype.val : {j // j ≠ i} → J)),
        K (x.1, Matrix.replicateCol Unit (x.2.col i)))) =
    (ρ.prod (gaussianMatrix n J)).map (fun x =>
      ((T x.1, x.2.submatrix id (Subtype.val : {j // j ≠ i} → J)),
        Matrix.replicateCol Unit (x.2.col i))) := by
  classical
  let f : α × Matrix n Unit ℝ → τ × Matrix n Unit ℝ := fun x => (T x.1, K x)
  let g : α × Matrix n Unit ℝ → τ × Matrix n Unit ℝ := fun x => (T x.1, x.2)
  have hf : Measurable f := (hT.comp measurable_fst).prodMk hK
  have hg : Measurable g := (hT.comp measurable_fst).prodMk measurable_snd
  have hraw : (ρ.prod (gaussianMatrix n Unit)).map g =
      (ρ.map T).prod (gaussianMatrix n Unit) := by
    have heq : g = Prod.map T id := by
      funext x
      exact (Prod.map_apply' T id x).symm
    rw [heq]
    simpa only [Measure.map_id] using
      (Measure.map_prod_map ρ (gaussianMatrix n Unit) hT measurable_id).symm
  have hfg : (ρ.prod (gaussianMatrix n Unit)).map f =
      (ρ.prod (gaussianMatrix n Unit)).map g := hkernel.trans hraw.symm
  have hpair := identDistrib_prodMap_id (η := gaussianMatrix n {j // j ≠ i}) hf hg hfg
  let P : (τ × Matrix n Unit ℝ) × Matrix n {j // j ≠ i} ℝ →
      (τ × Matrix n {j // j ≠ i} ℝ) × Matrix n Unit ℝ :=
    fun x => ((x.1.1, x.2), x.1.2)
  have hP : Measurable P := (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  have hmap := (hpair.comp hP).map_eq
  have hsplit := hasLaw_base_col_otherCols (n := n) ρ i
  let C : α × Matrix n J ℝ →
      (α × Matrix n Unit ℝ) × Matrix n {j // j ≠ i} ℝ :=
    fun x => ((x.1, Matrix.replicateCol Unit (x.2.col i)),
      x.2.submatrix id Subtype.val)
  have hC : Measurable C := by
    refine (measurable_fst.prodMk ?_).prodMk ?_
    · exact measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun _ =>
        (measurable_pi_apply i).comp ((measurable_pi_apply r).comp measurable_snd)
    · exact measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun j =>
        (measurable_pi_apply j.val).comp ((measurable_pi_apply r).comp measurable_snd)
  change (ρ.prod (gaussianMatrix n J)).map ((P ∘ Prod.map f id) ∘ C) =
    (ρ.prod (gaussianMatrix n J)).map ((P ∘ Prod.map g id) ∘ C)
  rw [← Measure.map_map (hP.comp (hf.prodMap measurable_id)) hC,
    ← Measure.map_map (hP.comp (hg.prodMap measurable_id)) hC, hsplit.map_eq]
  exact hmap

end Transport

section CanonicalBlock

variable {β : Type*} {n J : Type*} [Fintype n] [Fintype J] [DecidableEq n]

/-- Hidden vectors exposed before one selected left query. -/
private def canonicalRevealed {q : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β)
    (i : ℕ) (U : Matrix n n ℝ) : Matrix n (Fin i ⊕ Fin i) ℝ :=
  stabilizerRevealed (alg.truncate i) ((alg.truncate i).transcript (twoSidedMulVec U))

/-- The hidden coordinates of a selected left query. -/
private def canonicalLeft {q : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β)
    (i : ℕ) (U : Matrix n n ℝ) : n → ℝ :=
  Uᴴ *ᵥ (alg.queryAt (twoSidedMulVec U) i).2

/-- The measurable matrix whose selected columns are aligned Gaussian innovations. -/
private noncomputable def canonicalGaussianBlock {q : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β)
    (times : J → ℕ) (p : Matrix n n ℝ × Matrix n J ℝ) : Matrix n J ℝ :=
  fun r j => (innovationGaussianize (canonicalRevealed alg (times j) p.1)
    (canonicalLeft alg (times j) p.1) (Matrix.replicateCol Unit (p.2.col j))) r ()

omit [DecidableEq n] in
private theorem measurable_canonicalRevealed [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β}
    (halg : alg.IsMeasurable) {i : ℕ} (hi : i ≤ q) :
    Measurable (canonicalRevealed alg i) :=
  (measurable_stabilizerRevealed (halg.truncate hi)).comp
    ((halg.truncate hi).measurable_transcript
      (Measurable.twoSidedMulVec measurable_fst measurable_snd))

omit [DecidableEq n] in
private theorem measurable_canonicalLeft [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β}
    (halg : alg.IsMeasurable) {i : ℕ} (hi : i < q) :
    Measurable (canonicalLeft alg i) := by
  have hH := halg.measurable_history (O := twoSidedMulVec (𝕜 := ℝ) (m := n) (n := n))
    (Measurable.twoSidedMulVec measurable_fst measurable_snd) hi.le
  exact (Measurable.matrix_conjTranspose (by fun_prop) measurable_id).matrix_mulVec
    (measurable_snd.comp ((halg.measurable_query i hi).comp hH))

omit [Fintype J] in
private theorem measurable_canonicalGaussianBlock [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β}
    (halg : alg.IsMeasurable) (times : J → ℕ) (ht : ∀ j, times j < q) :
    Measurable (canonicalGaussianBlock alg times) := by
  refine measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun j => ?_
  have hZ : Measurable (fun p : Matrix n n ℝ × Matrix n J ℝ =>
      Matrix.replicateCol Unit (p.2.col j)) :=
    measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun _ =>
      (measurable_pi_apply j).comp ((measurable_pi_apply a).comp measurable_snd)
  exact (measurable_pi_apply ()).comp ((measurable_pi_apply r).comp
    (measurable_innovationGaussianize
      ((measurable_canonicalRevealed halg (ht j).le).comp measurable_fst)
      ((measurable_canonicalLeft halg (ht j)).comp measurable_fst) hZ))

private theorem ae_canonicalGaussianBlock_capture [MeasurableSpace β] {q : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β}
    (halg : alg.IsMeasurable) (times : J → ℕ) (ht : ∀ j, times j < q) :
    ∀ᵐ p ∂(haarFrame n n).prod (gaussianMatrix n J), ∀ j,
      canonicalLeft alg (times j) p.1 ∈
        LinearMap.range (canonicalRevealed alg (times j) p.1).mulVecLin ⊔
          LinearMap.range (canonicalGaussianBlock alg times p).mulVecLin := by
  classical
  apply Filter.eventually_all.mpr
  intro j
  have hV := measurable_canonicalRevealed halg (ht j).le
  have hv := measurable_canonicalLeft halg (ht j)
  have hK := measurable_innovationGaussianize
    (hV.comp (measurable_fst : Measurable (Prod.fst :
      Matrix n n ℝ × Matrix n Unit ℝ → Matrix n n ℝ)))
    (hv.comp measurable_fst) measurable_snd
  have hcap := ae_prod_mem_sup_range_innovationGaussianize (haarFrame n n)
    (canonicalRevealed alg (times j)) (canonicalLeft alg (times j)) hV hv hK
  let C : Matrix n J ℝ → Matrix n Unit ℝ := fun Z => Matrix.replicateCol Unit (Z.col j)
  have hC : Measurable C := measurable_pi_iff.2 fun r => measurable_pi_iff.2 fun _ =>
    (measurable_pi_apply j).comp (measurable_pi_apply r)
  have hClaw : (gaussianMatrix n J).map C = gaussianMatrix n Unit := by
    exact (hasLaw_submatrix_of_hasLaw_gaussianMatrix (HasLaw.id (μ := gaussianMatrix n J))
      Function.injective_id (Function.injective_of_subsingleton (fun _ : Unit => j))).map_eq
  have hmap : ((haarFrame n n).prod (gaussianMatrix n J)).map (Prod.map id C) =
      (haarFrame n n).prod (gaussianMatrix n Unit) := by
    rw [← Measure.map_prod_map _ _ measurable_id hC, Measure.map_id, hClaw]
  rw [← hmap] at hcap
  have hpull := ae_of_ae_map (measurable_id.prodMap hC).aemeasurable hcap
  refine hpull.mono fun p hp => ?_
  have hsub : LinearMap.range (innovationGaussianize
      (canonicalRevealed alg (times j) p.1) (canonicalLeft alg (times j) p.1)
      (C p.2)).mulVecLin ≤ LinearMap.range (canonicalGaussianBlock alg times p).mulVecLin := by
    rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
    apply Submodule.span_mono
    rintro _ ⟨u, rfl⟩
    cases u
    exact ⟨j, rfl⟩
  exact (sup_le_sup_left hsub _) hp

end CanonicalBlock

section CanonicalPrefix

variable {β : Type*} {n : Type*} [Fintype n] [DecidableEq n]

/-- Prefix of a transcript, with zero entries outside its available length. -/
private def canonicalPrefix {s : ℕ} (τ : Fin s → (n → ℝ) × (n → ℝ)) (t : ℕ) :
    Fin t → (n → ℝ) × (n → ℝ) :=
  fun j => if h : j.val < s then τ ⟨j.val, h⟩ else 0

omit [Fintype n] [DecidableEq n] in
/-- Zero-padded transcript prefixes are measurable. -/
private theorem measurable_canonicalPrefix (s t : ℕ) :
    Measurable (fun τ : Fin s → (n → ℝ) × (n → ℝ) => canonicalPrefix τ t) := by
  refine measurable_pi_iff.2 fun j => ?_
  unfold canonicalPrefix
  split_ifs with h
  · exact measurable_pi_apply (⟨j, h⟩ : Fin s)
  · exact measurable_const

omit [DecidableEq n] in
/-- Restricting the actual transcript gives the earlier transcript. -/
private theorem canonicalPrefix_transcript {q s t : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β)
    (ht : t ≤ s) (U : Matrix n n ℝ) :
    canonicalPrefix ((alg.truncate s).transcript (twoSidedMulVec U)) t =
      (alg.truncate t).transcript (twoSidedMulVec U) := by
  funext j
  unfold canonicalPrefix
  rw [dif_pos (j.isLt.trans_le ht), QueryAlgorithm.transcript_truncate,
    QueryAlgorithm.transcript_truncate, QueryAlgorithm.history_apply,
    QueryAlgorithm.history_apply]

/-- A previous innovation is reconstructed from its response in a later transcript. -/
private noncomputable def canonicalPrior {q s : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β)
    (t : ℕ) (ht : t < s) (τ : Fin s → (n → ℝ) × (n → ℝ))
    (Z : Matrix n Unit ℝ) : Matrix n Unit ℝ :=
  innovationGaussianize (stabilizerRevealed (alg.truncate t) (canonicalPrefix τ t))
    (τ ⟨t, ht⟩).2 Z

/-- Previous innovation reconstruction is jointly measurable in transcript and seed. -/
private theorem measurable_canonicalPrior [MeasurableSpace β] {q s : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β}
    (halg : alg.IsMeasurable) (t : ℕ) (ht : t < s) (htq : t ≤ q) :
    Measurable (fun p : (Fin s → (n → ℝ) × (n → ℝ)) × Matrix n Unit ℝ =>
      canonicalPrior alg t ht p.1 p.2) := by
  have hτ : Measurable (fun p : (Fin s → (n → ℝ) × (n → ℝ)) × Matrix n Unit ℝ =>
      p.1 (⟨t, ht⟩ : Fin s)) :=
    (measurable_pi_apply (⟨t, ht⟩ : Fin s)).comp measurable_fst
  exact measurable_innovationGaussianize
    ((measurable_stabilizerRevealed (halg.truncate htq)).comp
      ((measurable_canonicalPrefix s t).comp measurable_fst))
    (measurable_snd.comp hτ) measurable_snd

/-- Earlier innovations agree exactly with reconstruction from a later actual transcript. -/
private theorem canonicalPrior_eq {q s t : ℕ}
    (alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β)
    (ht : t < s) (U : Matrix n n ℝ) (Z : Matrix n Unit ℝ) :
    canonicalPrior alg t ht ((alg.truncate s).transcript (twoSidedMulVec U)) Z =
      innovationGaussianize (canonicalRevealed alg t U) (canonicalLeft alg t U) Z := by
  unfold canonicalPrior canonicalRevealed canonicalLeft
  rw [canonicalPrefix_transcript alg ht.le U]
  simp only [QueryAlgorithm.transcript_truncate, QueryAlgorithm.history_apply, twoSidedMulVec]

end CanonicalPrefix

section ProgressiveArray

private def progressiveMixed {α n J : Type*} [Fintype J]
    (K : J → α × Matrix n Unit ℝ → Matrix n Unit ℝ)
    (e : J ≃ Fin (Fintype.card J)) (t : ℕ) (x : α × Matrix n J ℝ) : Matrix n J ℝ :=
  fun r j => if (e j).val < t then K j (x.1, Matrix.replicateCol Unit (x.2.col j)) r ()
    else x.2 r j


/-- Reconstruct a mixed array from its current column, the outside seeds and its summary. -/
private def progressiveReconstruct
    {σ n J : Type*} [Fintype J] [DecidableEq J]
    {T : J → Type*} (e : J ≃ Fin (Fintype.card J)) (t : ℕ) (j : J)
    (RB : T j → σ) (RK : (l : J) → T j × Matrix n Unit ℝ → Matrix n Unit ℝ) :
    ((T j × Matrix n {l // l ≠ j} ℝ) × Matrix n Unit ℝ) → σ × Matrix n J ℝ :=
  fun y => (RB y.1.1, fun r l => if hl : l = j then y.2 r () else
    if (e l).val < t then RK l (y.1.1, Matrix.replicateCol Unit
      (fun a => y.1.2 a ⟨l, hl⟩)) r () else y.1.2 r ⟨l, hl⟩)

/-- Mixed-array reconstruction is measurable whenever its previous-coordinate kernels are. -/
private theorem measurable_progressiveReconstruct
    {σ n J : Type*} [MeasurableSpace σ] [Fintype J] [DecidableEq J]
    {T : J → Type*} [∀ j, MeasurableSpace (T j)]
    (e : J ≃ Fin (Fintype.card J)) (t : ℕ) (j : J)
    (RB : T j → σ) (RK : (l : J) → T j × Matrix n Unit ℝ → Matrix n Unit ℝ)
    (hRB : Measurable RB) (hRK : ∀ l, Measurable (RK l)) :
    Measurable (progressiveReconstruct e t j RB RK) := by
  unfold progressiveReconstruct
  refine (hRB.comp measurable_fst.fst).prodMk
    (measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun l => ?_)
  by_cases hl : l = j
  · simp only [hl, dite_true]
    exact (measurable_pi_apply ()).comp ((measurable_pi_apply r).comp measurable_snd)
  · simp only [hl, dite_false]
    split_ifs with hel
    · exact (measurable_pi_apply ()).comp ((measurable_pi_apply r).comp
        ((hRK l).comp (measurable_fst.fst.prodMk
          (measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun _ =>
            (measurable_pi_apply (⟨l, hl⟩ : {l // l ≠ j})).comp
              ((measurable_pi_apply a).comp measurable_fst.snd)))))
    · exact (measurable_pi_apply (⟨l, hl⟩ : {l // l ≠ j})).comp
        ((measurable_pi_apply r).comp measurable_fst.snd)

/-- Replacing the next coordinate preserves the law of the mixed array. -/
private theorem map_progressiveGaussianArray_succ
    {α σ n J : Type*} [MeasurableSpace α] [MeasurableSpace σ] [Fintype n] [Fintype J]
    (ρ : Measure α) [SFinite ρ] (e : J ≃ Fin (Fintype.card J))
    {T : J → Type*} [∀ j, MeasurableSpace (T j)]
    (A : (j : J) → α → T j) (B : α → σ)
    (K : J → α × Matrix n Unit ℝ → Matrix n Unit ℝ)
    (RB : (j : J) → T j → σ)
    (RK : (j l : J) → T j × Matrix n Unit ℝ → Matrix n Unit ℝ)
    (t : ℕ) (j : J) (hej : (e j).val = t)
    (hA : Measurable (A j)) (hK : Measurable (K j))
    (hRB : Measurable (RB j)) (hRK : ∀ l, Measurable (RK j l))
    (hrecB : ∀ a, RB j (A j a) = B a)
    (hrecK : ∀ l, (e l).val < (e j).val → ∀ a z, RK j l (A j a, z) = K l (a, z))
    (hkernel : (ρ.prod (gaussianMatrix n Unit)).map
      (fun x => (A j x.1, K j x)) = (ρ.map (A j)).prod (gaussianMatrix n Unit)) :
    (ρ.prod (gaussianMatrix n J)).map (fun x => (B x.1, progressiveMixed K e (t + 1) x)) =
      (ρ.prod (gaussianMatrix n J)).map (fun x => (B x.1, progressiveMixed K e t x)) := by
  classical
  let μ := ρ.prod (gaussianMatrix n J)
  let H : ℕ → α × Matrix n J ℝ → σ × Matrix n J ℝ :=
    fun t x => (B x.1, progressiveMixed K e t x)
  let F := progressiveReconstruct e t j (RB j) (RK j)
  have hF := measurable_progressiveReconstruct e t j (RB j) (RK j) hRB hRK
  let L : α × Matrix n J ℝ → (T j × Matrix n {l // l ≠ j} ℝ) × Matrix n Unit ℝ :=
    fun x => ((A j x.1, x.2.submatrix id Subtype.val),
      Matrix.replicateCol Unit (x.2.col j))
  let R : α × Matrix n J ℝ → (T j × Matrix n {l // l ≠ j} ℝ) × Matrix n Unit ℝ :=
    fun x => ((A j x.1, x.2.submatrix id Subtype.val),
      K j (x.1, Matrix.replicateCol Unit (x.2.col j)))
  have hcol : Measurable (fun x : α × Matrix n J ℝ =>
      Matrix.replicateCol Unit (x.2.col j)) :=
    measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun _ =>
      (measurable_pi_apply j).comp ((measurable_pi_apply r).comp measurable_snd)
  have hout : Measurable (fun x : α × Matrix n J ℝ =>
      x.2.submatrix id (Subtype.val : {l // l ≠ j} → J)) :=
    measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun l =>
      (measurable_pi_apply l.val).comp ((measurable_pi_apply r).comp measurable_snd)
  have hL : Measurable L := (hA.comp measurable_fst).prodMk hout |>.prodMk hcol
  have hR : Measurable R := (hA.comp measurable_fst).prodMk hout |>.prodMk
    (hK.comp (measurable_fst.prodMk hcol))
  have hFL : F ∘ L = H t := by
    funext x
    apply Prod.ext
    · exact hrecB x.1
    · ext r l
      by_cases hl : l = j
      · subst l
        simp only [Function.comp_apply, F, progressiveReconstruct, L, H, progressiveMixed,
          dite_true,
          Matrix.replicateCol_apply, Matrix.col_apply, hej, lt_self_iff_false, if_false]
      · simp only [Function.comp_apply, F, progressiveReconstruct, L, H, progressiveMixed,
          dif_neg hl,
          Matrix.submatrix_apply, id_eq]
        split_ifs with hel
        · rw [hrecK l (by omega)]
          rfl
        · rfl
  have hFR : F ∘ R = H (t + 1) := by
    funext x
    apply Prod.ext
    · exact hrecB x.1
    · ext r l
      by_cases hl : l = j
      · subst l
        simp only [Function.comp_apply, F, progressiveReconstruct, R, H, progressiveMixed,
          dite_true,
          hej, Nat.lt_succ_self, if_true]
      · have hne : (e l).val ≠ t := by
          intro he
          exact hl (e.injective (Fin.ext (he.trans hej.symm)))
        simp only [Function.comp_apply, F, progressiveReconstruct, R, H, progressiveMixed,
          dif_neg hl,
          Matrix.submatrix_apply, id_eq]
        by_cases hlt : (e l).val < t
        · have hlt' : (e l).val < t + 1 := by omega
          simp only [if_pos hlt, if_pos hlt']
          rw [hrecK l (by omega)]
          rfl
        · have hlt' : ¬ (e l).val < t + 1 := by omega
          simp only [if_neg hlt, if_neg hlt']
  have hm := map_summary_otherCols_kernel ρ j (A j) (K j) hA hK hkernel
  change μ.map R = μ.map L at hm
  change μ.map (H (t + 1)) = μ.map (H t)
  rw [← hFR, ← hFL, ← Measure.map_map hF hR, ← Measure.map_map hF hL, hm]

/-- Progressively replacing independent Gaussian columns preserves their joint law with a base
summary, when earlier replacements are recoverable from each later summary and their own seed. -/
private theorem map_progressiveGaussianArray
    {α σ n J : Type*} [MeasurableSpace α] [MeasurableSpace σ] [Fintype n] [Fintype J]
    (ρ : Measure α) [SFinite ρ] (e : J ≃ Fin (Fintype.card J))
    {T : J → Type*} [∀ j, MeasurableSpace (T j)]
    (A : (j : J) → α → T j) (B : α → σ)
    (K : J → α × Matrix n Unit ℝ → Matrix n Unit ℝ)
    (RB : (j : J) → T j → σ)
    (RK : (j l : J) → T j × Matrix n Unit ℝ → Matrix n Unit ℝ)
    (hA : ∀ j, Measurable (A j)) (hB : Measurable B) (hK : ∀ j, Measurable (K j))
    (hRB : ∀ j, Measurable (RB j)) (hRK : ∀ j l, Measurable (RK j l))
    (hrecB : ∀ j a, RB j (A j a) = B a)
    (hrecK : ∀ j l, (e l).val < (e j).val → ∀ a z, RK j l (A j a, z) = K l (a, z))
    (hkernel : ∀ j, (ρ.prod (gaussianMatrix n Unit)).map
      (fun x => (A j x.1, K j x)) = (ρ.map (A j)).prod (gaussianMatrix n Unit)) :
    (ρ.prod (gaussianMatrix n J)).map (fun x =>
      (B x.1, (fun r j => K j (x.1, Matrix.replicateCol Unit (x.2.col j)) r () : Matrix n J ℝ))) =
        (ρ.map B).prod (gaussianMatrix n J) := by
  let μ := ρ.prod (gaussianMatrix n J)
  let H : ℕ → α × Matrix n J ℝ → σ × Matrix n J ℝ :=
    fun t x => (B x.1, progressiveMixed K e t x)
  have hstep : ∀ t < Fintype.card J, μ.map (H (t + 1)) = μ.map (H t) := by
    intro t ht
    let j : J := e.symm ⟨t, ht⟩
    have hej : (e j).val = t := congrArg Fin.val (e.apply_symm_apply ⟨t, ht⟩)
    exact map_progressiveGaussianArray_succ ρ e A B K RB RK t j hej
      (hA j) (hK j) (hRB j) (hRK j) (hrecB j) (hrecK j) (hkernel j)
  have hend : ∀ t ≤ Fintype.card J, μ.map (H t) = μ.map (H 0) := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih => exact (hstep t ht).trans (ih (Nat.le_of_succ_le ht))
  have h0 : H 0 = Prod.map B id := by
    funext x
    apply Prod.ext
    · rfl
    · ext r j
      simp only [H, progressiveMixed, Nat.not_lt_zero, if_false, Prod.map_apply', id_eq]
  have hlast : H (Fintype.card J) = fun x =>
      (B x.1, (fun r j => K j (x.1,
        Matrix.replicateCol Unit (x.2.col j)) r () : Matrix n J ℝ)) := by
    funext x
    apply Prod.ext
    · rfl
    · ext r j
      exact if_pos (e j).isLt
  rw [← hlast]
  change μ.map (H (Fintype.card J)) = _
  rw [hend _ le_rfl, h0, ← Measure.map_prod_map _ _ hB measurable_id, Measure.map_id]

end ProgressiveArray

/-- Ordered Gaussian innovations retain their complete joint product law with every measurable
summary of an initial transcript prefix. -/
private theorem map_summary_canonicalGaussianBlock
    {β σ n J : Type*} [MeasurableSpace β] [MeasurableSpace σ]
    [Fintype n] [Fintype J] [DecidableEq n] {q start : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β}
    (halg : alg.IsMeasurable) (times : J → ℕ) (ht : ∀ j, times j < q)
    (e : J ≃ Fin (Fintype.card J))
    (horder : ∀ i j, (e i).val < (e j).val → times i < times j)
    (hstartq : start ≤ q) (hstart : ∀ j, start ≤ times j)
    (b : (Fin start → (n → ℝ) × (n → ℝ)) → σ) (hb : Measurable b) :
    ((haarFrame n n).prod (gaussianMatrix n J)).map (fun p =>
      (b ((alg.truncate start).transcript (twoSidedMulVec p.1)),
        canonicalGaussianBlock alg times p)) =
      ((haarFrame n n).map (fun U =>
        b ((alg.truncate start).transcript (twoSidedMulVec U)))).prod (gaussianMatrix n J) := by
  classical
  let A := fun j (U : Matrix n n ℝ) =>
    (alg.truncate (times j)).transcript (twoSidedMulVec U)
  let B := fun U : Matrix n n ℝ => b ((alg.truncate start).transcript (twoSidedMulVec U))
  let K := fun j (p : Matrix n n ℝ × Matrix n Unit ℝ) =>
    innovationGaussianize (canonicalRevealed alg (times j) p.1)
      (canonicalLeft alg (times j) p.1) p.2
  let RB := fun j (τ : Fin (times j) → (n → ℝ) × (n → ℝ)) => b (canonicalPrefix τ start)
  let RK := fun j l (p : (Fin (times j) → (n → ℝ) × (n → ℝ)) × Matrix n Unit ℝ) =>
    if h : times l < times j then canonicalPrior alg (times l) h p.1 p.2 else 0
  have hA : ∀ j, Measurable (A j) := fun j => (halg.truncate (ht j).le).measurable_transcript
    (Measurable.twoSidedMulVec measurable_fst measurable_snd)
  have hB : Measurable B := hb.comp ((halg.truncate hstartq).measurable_transcript
    (Measurable.twoSidedMulVec measurable_fst measurable_snd))
  have hK : ∀ j, Measurable (K j) := fun j => measurable_innovationGaussianize
    ((measurable_canonicalRevealed halg (ht j).le).comp measurable_fst)
    ((measurable_canonicalLeft halg (ht j)).comp measurable_fst) measurable_snd
  have hRB : ∀ j, Measurable (RB j) := fun j => hb.comp (measurable_canonicalPrefix _ _)
  have hRK : ∀ j l, Measurable (RK j l) := by
    intro j l
    by_cases h : times l < times j
    · simp only [RK, dif_pos h]
      exact measurable_canonicalPrior halg _ h (ht l).le
    · simp only [RK, dif_neg h]
      exact measurable_const
  have hrecB : ∀ j U, RB j (A j U) = B U := by
    intro j U
    exact congrArg b (canonicalPrefix_transcript alg (hstart j) U)
  have hrecK : ∀ j l, (e l).val < (e j).val → ∀ U z,
      RK j l (A j U, z) = K l (U, z) := by
    intro j l hlt U z
    have htime := horder l j hlt
    simp only [RK, dif_pos htime]
    exact canonicalPrior_eq alg htime U z
  have hkernel : ∀ j, ((haarFrame n n).prod (gaussianMatrix n Unit)).map
      (fun p => (A j p.1, K j p)) =
        ((haarFrame n n).map (A j)).prod (gaussianMatrix n Unit) := by
    intro j
    have hx : Measurable (fun τ => (alg.query (times j) τ).2) :=
      measurable_snd.comp (halg.measurable_query _ (ht j))
    have h := map_transcript_innovationGaussianize (halg.truncate (ht j).le)
      (fun τ => (alg.query (times j) τ).2) hx
    simpa only [A, K, canonicalRevealed, canonicalLeft, QueryAlgorithm.queryAt,
      QueryAlgorithm.transcript_truncate] using h
  exact map_progressiveGaussianArray (haarFrame n n) e A B K RB RK
    hA hB hK hRB hRK hrecB hrecK hkernel

/-- **Gaussian coupling of ordered left-query innovations**: for a measurable two-sided query
algorithm on a Haar orthogonal matrix, select distinct rounds in increasing order. If the rounds
follow a fixed initial transcript prefix, their hidden left-query vectors are captured, almost
surely, by the vectors already revealed and a jointly standard Gaussian block independent of
every measurable summary of that prefix. The block has one column per selected round. The
coupled block is a measurable function of the Haar matrix and an independent Gaussian block of
the same size. This singleton form of the deferred-decision construction supports the batched
Krylov coupling; [Shamir2026, Lemma 4] gives the sequential-query argument. -/
theorem exists_measurable_gaussianBlock_of_ordered_queries
    {β σ n J : Type*} [MeasurableSpace β] [MeasurableSpace σ]
    [Fintype n] [Fintype J] [DecidableEq n] {q start : ℕ}
    {alg : QueryAlgorithm ((n → ℝ) × (n → ℝ)) ((n → ℝ) × (n → ℝ)) q β}
    (halg : alg.IsMeasurable) (times : J → ℕ) (ht : ∀ j, times j < q)
    (e : J ≃ Fin (Fintype.card J))
    (horder : ∀ i j, (e i).val < (e j).val → times i < times j)
    (hstartq : start ≤ q) (hstart : ∀ j, start ≤ times j)
    (b : (Fin start → (n → ℝ) × (n → ℝ)) → σ) (hb : Measurable b) :
    ∃ G : Matrix n n ℝ × Matrix n J ℝ → Matrix n J ℝ, Measurable G ∧
      ((haarFrame n n).prod (gaussianMatrix n J)).map (fun p =>
        (b ((alg.truncate start).transcript (twoSidedMulVec p.1)), G p)) =
        ((haarFrame n n).map (fun U =>
          b ((alg.truncate start).transcript (twoSidedMulVec U)))).prod
            (gaussianMatrix n J) ∧
      ∀ᵐ p ∂(haarFrame n n).prod (gaussianMatrix n J), ∀ j,
        p.1ᴴ *ᵥ (alg.queryAt (twoSidedMulVec p.1) (times j)).2 ∈
          LinearMap.range (Matrix.fromCols
            ((alg.truncate (times j)).rightQueryMatrix
              ((alg.truncate (times j)).transcript (twoSidedMulVec p.1)))
            (Matrix.of fun r l =>
              (((alg.truncate (times j)).transcript (twoSidedMulVec p.1)) l).2 r)).mulVecLin ⊔
            LinearMap.range (G p).mulVecLin := by
  refine ⟨canonicalGaussianBlock alg times, measurable_canonicalGaussianBlock halg times ht,
    map_summary_canonicalGaussianBlock halg times ht e horder hstartq hstart b hb, ?_⟩
  exact ae_canonicalGaussianBlock_capture halg times ht

end NLAlib
