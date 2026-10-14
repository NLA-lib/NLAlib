/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Algebra.MvPolynomial
public import NLAlib.Matrix.Basic.Gram
public import NLAlib.RandomMatrix.Gaussian.Basic

/-!
# The rank of a Gaussian matrix

A nonzero polynomial in independent real coordinates with an atomless law is almost surely
nonzero. Minors are polynomials in the entries, so a standard Gaussian matrix has full rank almost
surely, and so does every Gaussian sketch `A G` up to the rank of `A`:
`rank (A G) = min (rank A) (card n)` almost surely. In particular `(A G)ᴴ (A G)` is almost surely
invertible when `card n ≤ rank A`.

## Main results

* `NLAlib.ae_eval_ne_zero_of_ne_zero`.
* `NLAlib.ae_rank_eq_min_of_hasLaw_gaussianMatrix`.
* `NLAlib.ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`.
* `NLAlib.ae_isUnit_conjTranspose_mul_self_mul_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → Matrix m n ℝ}

/-- The `Fin n` case of `ae_eval_ne_zero_of_ne_zero`, by induction on `n`: split off the first
coordinate, where the polynomial has finitely many roots. -/
private theorem ae_eval_ne_zero_fin {ν : Measure ℝ} [IsProbabilityMeasure ν]
    [NullSingletonClass ν] :
    ∀ (n : ℕ) (f : MvPolynomial (Fin n) ℝ), f ≠ 0 →
      ∀ᵐ x ∂Measure.pi fun _ : Fin n => ν, MvPolynomial.eval x f ≠ 0 := by
  intro n
  induction n with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x hx => hf ?_
    apply MvPolynomial.funext
    intro y
    have : y = x := Subsingleton.elim _ _
    subst this
    simpa using hx
  | succ n ih =>
    intro f hf
    set g := MvPolynomial.finSuccEquiv ℝ n f with hg
    have hg0 : g ≠ 0 := by
      intro h; apply hf
      exact (MvPolynomial.finSuccEquiv ℝ n).injective (by rw [← hg, h, map_zero])
    have hih := ih g.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hg0)
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    let T : Set (ℝ × (Fin n → ℝ)) :=
      {q | MvPolynomial.eval (Fin.cons q.1 q.2 : Fin (n + 1) → ℝ) f = 0}
    have hT : MeasurableSet T := by
      have hcont : Continuous fun q : ℝ × (Fin n → ℝ) =>
          MvPolynomial.eval (Fin.cons q.1 q.2 : Fin (n + 1) → ℝ) f := by
        apply (MvPolynomial.continuous_eval f).comp
        refine continuous_pi fun i => ?_
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using continuous_fst
        · simp only [Fin.cons_succ]; exact (continuous_apply j).comp continuous_snd
      exact hcont.measurable (measurableSet_singleton 0)
    have hpre : MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 ⁻¹' T =
        {x | MvPolynomial.eval x f = 0} := by
      ext x
      have hx : (Fin.cons (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 x).1
          (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0 x).2 : Fin (n + 1) → ℝ) = x := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [MeasurableEquiv.piFinSuccAbove_apply]
        · simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.tail]
      simp only [Set.mem_preimage, T, Set.mem_ofPred_eq]
      rw [hx]
    rw [← hpre, hmp.measure_preimage hT.nullMeasurableSet, Measure.prod_apply_symm hT]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hih] with s hs
    have hpoly : Polynomial.map (MvPolynomial.eval s) g ≠ 0 := by
      intro h0
      apply hs
      have := congrArg (fun q => Polynomial.coeff q g.natDegree) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
      exact this
    have hfin : ((fun y => (y, s)) ⁻¹' T).Finite := by
      refine (Polynomial.roots
        (Polynomial.map (MvPolynomial.eval s) g)).toFinset.finite_toSet.subset ?_
      intro y hy
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, T, MvPolynomial.eval_eq_eval_mv_eval']
        at hy
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hpoly,
        Polynomial.IsRoot.def]
      exact hy
    simpa using hfin.measure_zero ν

/-- A nonzero polynomial in independent coordinates with an atomless law is almost surely
nonzero. -/
theorem ae_eval_ne_zero_of_ne_zero {ι : Type*} [Fintype ι] {ν : Measure ℝ}
    [IsProbabilityMeasure ν] [NullSingletonClass ν] {f : MvPolynomial ι ℝ} (hf : f ≠ 0) :
    ∀ᵐ x ∂Measure.pi fun _ : ι => ν, MvPolynomial.eval x f ≠ 0 := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hg : MvPolynomial.rename e f ≠ 0 := by
    intro h; apply hf
    exact MvPolynomial.rename_injective e e.injective (by rw [h, map_zero])
  have h := ae_eval_ne_zero_fin (ν := ν) _ _ hg
  have hmp := measurePreserving_arrowCongr' (fun _ : Fin (Fintype.card ι) => ν)
    (fun _ : ι => ν) e.symm (MeasurableEquiv.refl ℝ) fun _ => MeasurePreserving.id _
  have hmeas : MeasurableSet {x : ι → ℝ | MvPolynomial.eval x f ≠ 0} :=
    ((MvPolynomial.continuous_eval f).measurable (measurableSet_singleton 0)).compl
  rw [← hmp.map_eq, ae_map_iff hmp.measurable.aemeasurable hmeas]
  filter_upwards [h] with y hy
  rw [MvPolynomial.eval_rename] at hy
  exact hy

/-- A matrix `A` with `q ≤ rank A` maps some `q` vectors to independent ones. -/
private theorem exists_rank_mul_eq {l : Type*} [Finite l] (A : Matrix l m ℝ) {q : ℕ}
    (hq : q ≤ A.rank) : ∃ Z : Matrix m (Fin q) ℝ, (A * Z).rank = q := by
  have := Fintype.ofFinite l
  let b : Module.Basis (Fin A.rank) ℝ (LinearMap.range A.mulVecLin) :=
    Module.finBasis ℝ (LinearMap.range A.mulVecLin)
  let e : Fin q ↪ Fin A.rank := Fin.castLEEmb hq
  have hpre : ∀ i : Fin A.rank, ∃ z : m → ℝ, A *ᵥ z = (b i : l → ℝ) :=
    fun i => (b i).property
  choose z hz using hpre
  let Z : Matrix m (Fin q) ℝ := Matrix.of fun i j => z (e j) i
  have hli : LinearIndependent ℝ (fun j : Fin q => (b (e j) : l → ℝ)) :=
    (b.linearIndependent.map' (LinearMap.range A.mulVecLin).subtype
      (Submodule.ker_subtype _)).comp e e.injective
  have hrow : ((A * Z)ᵀ).row = fun j => A *ᵥ z (e j) := rfl
  have hliRow : LinearIndependent ℝ ((A * Z)ᵀ).row := by
    rw [hrow]
    simpa only [hz] using hli
  refine ⟨Z, ?_⟩
  simpa only [Matrix.rank_transpose, Fintype.card_fin] using hliRow.rank_matrix

/-- The determinant of the Gram matrix of `A X E`, as a polynomial in the entries of `X`. -/
private theorem eval_det_gram {l k : Type*} [Fintype l] [Fintype k] [DecidableEq k]
    (A : Matrix l m ℝ) (E : Matrix n k ℝ) (G : Matrix m n ℝ) :
    MvPolynomial.eval (Function.uncurry G)
      ((A.map MvPolynomial.C * Matrix.mvPolynomialX m n ℝ * E.map MvPolynomial.C)ᵀ *
        (A.map MvPolynomial.C * Matrix.mvPolynomialX m n ℝ * E.map MvPolynomial.C)).det =
      ((A * G * E)ᴴ * (A * G * E)).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [Matrix.map_mul, Matrix.transpose_map]
  have hA : (A.map MvPolynomial.C).map (MvPolynomial.eval (Function.uncurry G)) = A := by
    ext i j
    simp
  have hE : (E.map MvPolynomial.C).map (MvPolynomial.eval (Function.uncurry G)) = E := by
    ext i j
    simp
  have hX : (Matrix.mvPolynomialX m n ℝ).map (MvPolynomial.eval (Function.uncurry G)) = G := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mvPolynomialX_apply, MvPolynomial.eval_X]
    rfl
  rw [hA, hE, hX]

/-- **The rank of a Gaussian sketch**: `rank (A G) = min (rank A) (card n)` almost surely. -/
theorem ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix {l : Type*} [Finite l] (A : Matrix l m ℝ)
    (hX : HasLaw X (gaussianMatrix m n) μ) :
    ∀ᵐ ω ∂μ, (A * X ω).rank = min A.rank (Fintype.card n) := by
  classical
  have := Fintype.ofFinite l
  set q := min A.rank (Fintype.card n)
  obtain ⟨Z, hZ⟩ := exists_rank_mul_eq A (min_le_left A.rank (Fintype.card n))
  let c : Fin q ↪ n :=
    (Fin.castLEEmb (min_le_right _ _)).trans (Fintype.equivFin n).symm.toEmbedding
  let E : Matrix n (Fin q) ℝ := (1 : Matrix n n ℝ).submatrix id c
  have hEE : Eᵀ * E = 1 := by
    rw [show Eᵀ * E = Eᵀ.submatrix id c by simpa using Matrix.mul_submatrix_one (Equiv.refl n) c Eᵀ,
      Matrix.transpose_submatrix, Matrix.transpose_one, Matrix.submatrix_submatrix]
    exact Matrix.submatrix_one_embedding c
  let Y := A.map MvPolynomial.C * Matrix.mvPolynomialX m n ℝ * E.map MvPolynomial.C
  have hrank : ∀ G : Matrix m n ℝ, ((A * G * E)ᴴ * (A * G * E)).det ≠ 0 →
      (A * G * E).rank = q := fun G hG => by
    have h := isUnit_conjTranspose_mul_self_iff_rank.1
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hG))
    rwa [Fintype.card_fin] at h
  have hp : (Yᵀ * Y).det ≠ 0 := by
    intro h0
    have h := eval_det_gram A E (Z * Eᵀ)
    rw [h0, map_zero, Matrix.mul_assoc A, Matrix.mul_assoc Z, hEE, Matrix.mul_one] at h
    have hZ' := isUnit_conjTranspose_mul_self_iff_rank.2 (hZ.trans (Fintype.card_fin q).symm)
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hZ').ne_zero h.symm
  have hU := hasLaw_uncurry_of_hasLaw_gaussianMatrix hX
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hae : ∀ᵐ x ∂gaussianVector (m × n), MvPolynomial.eval x (Yᵀ * Y).det ≠ 0 :=
    ae_eval_ne_zero_of_ne_zero hp
  rw [← hU.map_eq] at hae
  filter_upwards [ae_of_ae_map hU.aemeasurable hae] with ω hω
  rw [eval_det_gram] at hω
  refine le_antisymm (le_min (Matrix.rank_mul_le_left _ _) (Matrix.rank_le_card_width _)) ?_
  rw [← hrank (X ω) hω]
  exact Matrix.rank_mul_le_left _ _

/-- A standard Gaussian matrix has full rank almost surely. -/
theorem ae_rank_eq_min_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    ∀ᵐ ω ∂μ, (X ω).rank = min (Fintype.card m) (Fintype.card n) := by
  classical
  filter_upwards [ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix (1 : Matrix m m ℝ) hX] with ω hω
  rwa [Matrix.one_mul, Matrix.rank_one] at hω

/-- The Gram matrix of a Gaussian sketch is almost surely invertible when the sketch is no wider
than the rank of `A`. -/
theorem ae_isUnit_conjTranspose_mul_self_mul_of_hasLaw_gaussianMatrix [DecidableEq n] {l : Type*}
    [Fintype l] {A : Matrix l m ℝ} (hA : Fintype.card n ≤ A.rank)
    (hX : HasLaw X (gaussianMatrix m n) μ) :
    ∀ᵐ ω ∂μ, IsUnit ((A * X ω)ᴴ * (A * X ω)) := by
  filter_upwards [ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix A hX] with ω hω
  rw [min_eq_right hA] at hω
  exact isUnit_conjTranspose_mul_self_iff_rank.2 hω

end NLAlib
