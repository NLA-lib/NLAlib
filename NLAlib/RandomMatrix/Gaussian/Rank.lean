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

A nonzero polynomial in independent real or complex coordinates with an atomless law is almost
surely nonzero. Minors are polynomials in the entries, so a standard Gaussian matrix has full rank
almost
surely, and so does every Gaussian sketch $\mathbf{A}\mathbf{G}$ up to the rank of $\mathbf{A}$:
$\operatorname{rank}(\mathbf{A}\mathbf{G}) = \min(\operatorname{rank} \mathbf{A}, \lvert n \rvert)$
almost surely, for $\mathbf{G}$ of size $m \times n$. In particular
$(\mathbf{A}\mathbf{G})^{\mathsf{H}}(\mathbf{A}\mathbf{G})$ is almost surely invertible when
$\lvert n \rvert \le \operatorname{rank} \mathbf{A}$.

A nonzero two-sided linear image of a standard Gaussian matrix takes any given value with
probability zero, the measure-zero step of the exact range-recovery lower bound.

## Main results

* `NLAlib.ae_eval_ne_zero_of_ne_zero`.
* `NLAlib.ae_rank_eq_min_of_hasLaw_gaussianMatrix`.
* `NLAlib.ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`.
* `NLAlib.ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix`.
* `NLAlib.ae_isUnit_conjTranspose_mul_self_mul_of_hasLaw_gaussianMatrix`.
* `NLAlib.measure_mul_mul_eq_eq_zero_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → Matrix m n ℝ}

/-- The `Fin n` case of `ae_eval_ne_zero_of_ne_zero`, by induction on $n$: split off the first
coordinate, where the polynomial has finitely many roots. -/
private theorem ae_eval_ne_zero_fin {𝕜 : Type*} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {ν : Measure 𝕜} [IsProbabilityMeasure ν]
    [NullSingletonClass ν] :
    ∀ (n : ℕ) (f : MvPolynomial (Fin n) 𝕜), f ≠ 0 →
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
    set g := MvPolynomial.finSuccEquiv 𝕜 n f with hg
    have hg0 : g ≠ 0 := by
      intro h; apply hf
      exact (MvPolynomial.finSuccEquiv 𝕜 n).injective (by rw [← hg, h, map_zero])
    have hih := ih g.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hg0)
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    let T : Set (𝕜 × (Fin n → 𝕜)) :=
      {q | MvPolynomial.eval (Fin.cons q.1 q.2 : Fin (n + 1) → 𝕜) f = 0}
    have hT : MeasurableSet T := by
      have hcont : Continuous fun q : 𝕜 × (Fin n → 𝕜) =>
          MvPolynomial.eval (Fin.cons q.1 q.2 : Fin (n + 1) → 𝕜) f := by
        apply (MvPolynomial.continuous_eval f).comp
        refine continuous_pi fun i => ?_
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using continuous_fst
        · simp only [Fin.cons_succ]; exact (continuous_apply j).comp continuous_snd
      exact hcont.measurable (measurableSet_singleton 0)
    have hpre : MeasurableEquiv.piFinSuccAbove (fun _ => 𝕜) 0 ⁻¹' T =
        {x | MvPolynomial.eval x f = 0} := by
      ext x
      have hx : (Fin.cons (MeasurableEquiv.piFinSuccAbove (fun _ => 𝕜) 0 x).1
          (MeasurableEquiv.piFinSuccAbove (fun _ => 𝕜) 0 x).2 : Fin (n + 1) → 𝕜) = x := by
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
theorem ae_eval_ne_zero_of_ne_zero {𝕜 : Type*} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {ι : Type*} [Fintype ι] {ν : Measure 𝕜}
    [IsProbabilityMeasure ν] [NullSingletonClass ν] {f : MvPolynomial ι 𝕜} (hf : f ≠ 0) :
    ∀ᵐ x ∂Measure.pi fun _ : ι => ν, MvPolynomial.eval x f ≠ 0 := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hg : MvPolynomial.rename e f ≠ 0 := by
    intro h; apply hf
    exact MvPolynomial.rename_injective e e.injective (by rw [h, map_zero])
  have h := ae_eval_ne_zero_fin (ν := ν) _ _ hg
  have hmp := measurePreserving_arrowCongr' (fun _ : Fin (Fintype.card ι) => ν)
    (fun _ : ι => ν) e.symm (MeasurableEquiv.refl 𝕜) fun _ => MeasurePreserving.id _
  have hmeas : MeasurableSet {x : ι → 𝕜 | MvPolynomial.eval x f ≠ 0} :=
    ((MvPolynomial.continuous_eval f).measurable (measurableSet_singleton 0)).compl
  rw [← hmp.map_eq, ae_map_iff hmp.measurable.aemeasurable hmeas]
  filter_upwards [h] with y hy
  rw [MvPolynomial.eval_rename] at hy
  exact hy

/-- A matrix $\mathbf{A}$ with $q \le \operatorname{rank} \mathbf{A}$ maps some $q$ vectors to
independent ones. -/
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

/-- The determinant of the Gram matrix of $\mathbf{A}\mathbf{X}\mathbf{E}$, as a polynomial in the
entries of $\mathbf{X}$. -/
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

/-- The rank of a Gaussian sketch: for a fixed $\mathbf{A}$ and a standard Gaussian
$m \times n$ matrix $\mathbf{G}$,
$\operatorname{rank}(\mathbf{A}\mathbf{G}) = \min(\operatorname{rank} \mathbf{A}, \lvert n \rvert)$
almost surely. -/
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

/-- A Gaussian sketch keeps a small rank: for a fixed $\mathbf{Z}$ with
$\operatorname{rank}\mathbf{Z} \le \lvert n \rvert$ and a standard Gaussian $m \times n$ matrix
$\mathbf{G}$,
$\operatorname{rank}(\mathbf{G}^{\mathsf{H}}\mathbf{Z}) = \operatorname{rank}\mathbf{Z}$
almost surely: the rank hypothesis `(Ωᴴ * Z).rank = Z.rank` of the structural bound of the range
finder, for a frame $\mathbf{Z}$ with at most $\lvert n \rvert$ columns. -/
theorem ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix {p : Type*} [Fintype p]
    (Z : Matrix m p ℝ) (hX : HasLaw X (gaussianMatrix m n) μ) (hZ : Z.rank ≤ Fintype.card n) :
    ∀ᵐ ω ∂μ, ((X ω)ᴴ * Z).rank = Z.rank := by
  filter_upwards [ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix Zᴴ hX] with ω hω
  rw [← Matrix.rank_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hω, Matrix.rank_conjTranspose, min_eq_left hZ]

/-- A standard Gaussian $m \times n$ matrix has full rank almost surely:
$\operatorname{rank} \mathbf{G} = \min(\lvert m \rvert, \lvert n \rvert)$. -/
theorem ae_rank_eq_min_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix m n) μ) :
    ∀ᵐ ω ∂μ, (X ω).rank = min (Fintype.card m) (Fintype.card n) := by
  classical
  filter_upwards [ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix (1 : Matrix m m ℝ) hX] with ω hω
  rwa [Matrix.one_mul, Matrix.rank_one] at hω

/-- The Gram matrix of a Gaussian sketch is almost surely invertible when the sketch is no wider
than the rank of $\mathbf{A}$: if $\lvert n \rvert \le \operatorname{rank} \mathbf{A}$, then
$(\mathbf{A}\mathbf{G})^{\mathsf{H}}(\mathbf{A}\mathbf{G})$ is invertible almost surely. -/
theorem ae_isUnit_conjTranspose_mul_self_mul_of_hasLaw_gaussianMatrix [DecidableEq n] {l : Type*}
    [Fintype l] {A : Matrix l m ℝ} (hA : Fintype.card n ≤ A.rank)
    (hX : HasLaw X (gaussianMatrix m n) μ) :
    ∀ᵐ ω ∂μ, IsUnit ((A * X ω)ᴴ * (A * X ω)) := by
  filter_upwards [ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix A hX] with ω hω
  rw [min_eq_right hA] at hω
  exact isUnit_conjTranspose_mul_self_iff_rank.2 hω

end NLAlib


open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n] {X : Ω → Matrix m n ℝ}

/-- A Gaussian matrix hits a point of a nonzero linear image with probability zero: for a
standard Gaussian $\mathbf{X} \in \mathbb{R}^{m \times n}$, matrices
$\mathbf{N} \ne \mathbf{0}$ and $\mathbf{F} \ne \mathbf{0}$ and any $\mathbf{C}$,
$\mathbb{P}[\mathbf{N}\mathbf{X}\mathbf{F} = \mathbf{C}] = 0$. -/
theorem measure_mul_mul_eq_eq_zero_of_hasLaw_gaussianMatrix {p r : Type*}
    (hX : HasLaw X (gaussianMatrix m n) μ) {N : Matrix p m ℝ} {F : Matrix n r ℝ} (hN : N ≠ 0)
    (hF : F ≠ 0) (C : Matrix p r ℝ) :
    μ {ω | N * X ω * F = C} = 0 := by
  obtain ⟨i, a, hia⟩ : ∃ i a, N i a ≠ 0 := by
    by_contra h; push Not at h; exact hN (Matrix.ext h)
  obtain ⟨b, j, hbj⟩ : ∃ b j, F b j ≠ 0 := by
    by_contra h; push Not at h; exact hF (Matrix.ext h)
  set c : m × n → ℝ := fun q => N i q.1 * F q.2 j with hc
  have hc0 : ‖WithLp.toLp 2 c‖₊ ^ 2 ≠ 0 := by
    refine pow_ne_zero _ (nnnorm_ne_zero_iff.mpr fun h => mul_ne_zero hia hbj ?_)
    exact congrFun (congrArg WithLp.ofLp h) (a, b)
  have hY := hasLaw_dotProduct_of_hasLaw_gaussianVector
    (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX) c
  have key : ∀ ω, (N * X ω * F) i j = c ⬝ᵥ Function.uncurry (X ω) := by
    intro ω
    simp only [Matrix.mul_apply, dotProduct, hc, Finset.sum_mul, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
      rw [mul_right_comm]; rfl
  have := nullSingletonClass_gaussianReal (μ := 0) hc0
  refine measure_mono_null (t := (fun ω => c ⬝ᵥ Function.uncurry (X ω)) ⁻¹' {C i j})
    (fun ω hω => ?_) ?_
  · simp only [Set.mem_ofPred_eq] at hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ← key, hω]
  · rw [← Measure.map_apply_of_aemeasurable hY.aemeasurable (measurableSet_singleton _),
      hY.map_eq]
    exact measure_singleton _

end NLAlib
