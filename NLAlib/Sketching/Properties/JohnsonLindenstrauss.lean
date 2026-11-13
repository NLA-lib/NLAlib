/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Sym.Card
public import NLAlib.ForMathlib.Data.Finset.Max
public import NLAlib.ForMathlib.LinearAlgebra.Dimension.Constructions
public import NLAlib.Matrix.Norms.Net
public import NLAlib.Probability.Law
public import NLAlib.Probability.Tail
public import NLAlib.Sketching.Properties.FixedSubspace
public import NLAlib.Sketching.Properties.Oblivious

/-!
# The Johnson–Lindenstrauss property

A random sketch $\mathbf{S}$ with values in $\Bbbk^{k \times n}$ has the *distributional
Johnson–Lindenstrauss property* with distortion $\varepsilon$ and failure probability $\delta$
when, for every unit vector $\mathbf{x}$,
$\mathbb{P}[\varepsilon \le \lvert \|\mathbf{S}\mathbf{x}\|^2 - 1 \rvert] \le \delta$; it has the
*JL moment property* with exponent $p$ when
$\mathbb{E}\lvert \|\mathbf{S}\mathbf{x}\|^2 - 1 \rvert^p \le \varepsilon^p \delta$ for unit
$\mathbf{x}$. The moment property implies the tail property (Markov); conversely a
sub-exponential JL tail at every distortion gives the moment property at every exponent, through
the named bound `NLAlib.subexponentialMomentBound` (<!-- value subexponentialMomentBound v b p -->
$p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^{p}\Gamma(p)$); the moment property at $p = \log(1/\delta)$ is
Kane and Nelson's [KaneNelson2014]. Both scale to every nonzero vector; the tail
property gives the Johnson–Lindenstrauss lemma for finitely many points by a union bound over
pairs. The moment property also gives approximate matrix multiplication
(`NLAlib.Sketching.Properties.MatrixMultiplication`).

Both are stated with the non-strict threshold event $\{\varepsilon \le X\}$.

**From the JL property to subspace embeddings.** A distributional JL tail at $\varepsilon$ makes
any sketch $\mathbf{S}$ a subspace embedding with constants $1 \mp (5/4)\varepsilon$ of a fixed
$\mathbf{U}$ with orthonormal columns, failing with probability at most $21^{D} \delta$,
$D = \lvert p \rvert \dim_{\mathbb{R}} \Bbbk$ the real dimension of $\Bbbk^p$: on a $1/10$-net
of the unit sphere of $\Bbbk^p$ (`NLAlib.exists_finset_specNorm_le_div_of_isHermitian`, at most
$21^{D}$ points), the Hermitian error
$\mathbf{E} = (\mathbf{S}\mathbf{U})^{\mathsf{H}} (\mathbf{S}\mathbf{U}) - \mathbf{I}$ has
$\lvert \operatorname{Re} \mathbf{x}^{\mathsf{H}} \mathbf{E} \mathbf{x} \rvert
= \lvert \|\mathbf{S}\mathbf{U}\mathbf{x}\|^2 - 1 \rvert < \varepsilon$ off the union of the JL
events, hence $\|\mathbf{E}\|_2 < (5/4)\varepsilon$. The real dimension is $\lvert p \rvert$ over
$\mathbb{R}$ and $2 \lvert p \rvert$ over $\mathbb{C}$, so the factor is $21^{\lvert p \rvert}$
and $441^{\lvert p \rvert}$. Any family with a JL tail and no Gram-level tail gets its OSE here.
Conversely an OSE for dimension $1$ with constants strictly inside $1 \mp \varepsilon$ has the
JL property at $\varepsilon$ (`NLAlib.IsObliviousSubspaceEmbedding.hasJLProperty`), the route of
the SRHT.
Degenerate cases: for empty $p$ every sketch is an embedding; for $\varepsilon \le 0$ and nonempty
$p$ the JL hypothesis bounds the whole space. No
hypothesis on $\varepsilon$; $\delta \ge 0$ is needed for the union bound over an empty net and
for `mono`.

## Main definitions

* `NLAlib.HasJLProperty S ε δ μ`, `NLAlib.HasJLMoment S ε δ p μ`.

## Main results

* `NLAlib.HasJLProperty.measureReal_exists_abs_norm_mulVec_sq_sub_ge_le`: the JL lemma.
* `NLAlib.HasJLMoment.hasJLProperty`: moments give tails.
* `NLAlib.hasJLMoment_of_forall_hasJLProperty`: sub-exponential tails at every distortion give
  moments at every exponent.
* `NLAlib.HasJLMoment.integral_abs_norm_mulVec_sq_sub_rpow_le`: the moment bound for every
  $\mathbf{x}$.
* `NLAlib.HasJLMoment.integrable_abs_frobNorm_mul_sq_sub_rpow`,
  `NLAlib.HasJLMoment.integral_abs_frobNorm_mul_sq_sub_rpow_le`,
  `NLAlib.HasJLMoment.measureReal_abs_frobNorm_mul_sq_sub_ge_le`: Frobenius-norm preservation, the
  moment bound summed over the columns of a matrix, any field.
* `NLAlib.HasJLProperty.hasSubspaceEmbedding`: JL plus a net, for a fixed $\mathbf{U}$.
* `NLAlib.HasJLProperty.isObliviousSubspaceEmbedding`: the oblivious form.
* `NLAlib.IsObliviousSubspaceEmbedding.hasJLProperty`: an OSE for dimension one has the JL
  property.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n : Type*} [Fintype k] [Fintype n] {S : Ω → Matrix k n 𝕜} {ε ε' δ δ' p : ℝ}

/-- **Distributional Johnson–Lindenstrauss property** on unit vectors: for every unit
$\mathbf{x}$, $\mathbb{P}[\varepsilon \le \lvert \|\mathbf{S}\mathbf{x}\|^2 - 1 \rvert] \le \delta$.
[Woodruff2014, proof of Lemma 18]; [MartinssonTropp2020, §8.6]. -/
def HasJLProperty (S : Ω → Matrix k n 𝕜) (ε δ : ℝ) (μ : Measure Ω) : Prop :=
  ∀ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 →
    μ.real {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1|} ≤ δ

/-- **JL moment property** with real exponent $p$: for every unit $\mathbf{x}$, the $p$-th moment
is integrable and
$\mathbb{E}\lvert \|\mathbf{S}\mathbf{x}\|^2 - 1 \rvert^p \le \varepsilon^p \delta$. Junk for
$\varepsilon < 0$ (real powers of negative numbers). [Woodruff2014, Definition 12]. -/
structure HasJLMoment (S : Ω → Matrix k n 𝕜) (ε δ p : ℝ) (μ : Measure Ω) : Prop where
  /-- The $p$-th moment of the distortion is finite at every unit vector. -/
  integrable : ∀ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 →
    Integrable (fun ω => |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1| ^ p) μ
  /-- The $p$-th moment of the distortion is at most $\varepsilon^p \delta$ at every unit
  vector. -/
  integral_le : ∀ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 →
    ∫ ω, |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1| ^ p ∂μ ≤ ε ^ p * δ

/-- The distortion at $\mathbf{x} \ne \mathbf{0}$, to the power $p$, is $\|\mathbf{x}\|^{2p}$
times that at a unit vector. -/
private theorem abs_sub_rpow_eq {x u : n → 𝕜} (hu : ∀ A : Matrix k n 𝕜,
      ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2 =
        ‖WithLp.toLp 2 x‖ ^ 2 * (‖WithLp.toLp 2 (A *ᵥ u)‖ ^ 2 - 1)) (A : Matrix k n 𝕜) :
    |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2| ^ p =
      ‖WithLp.toLp 2 x‖ ^ (2 * p) * |‖WithLp.toLp 2 (A *ᵥ u)‖ ^ 2 - 1| ^ p := by
  rw [hu, abs_mul, abs_of_nonneg (sq_nonneg _), Real.mul_rpow (sq_nonneg _) (abs_nonneg _),
    Real.rpow_mul (norm_nonneg _), Real.rpow_two]

/-- The JL property depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.hasJLProperty_iff {ν : Measure (Matrix k n 𝕜)}
    (hS : HasLaw S ν μ) : HasJLProperty S ε δ μ ↔ HasJLProperty id ε δ ν := by
  refine forall₂_congr fun x _ => ?_
  have hc : Continuous fun A : Matrix k n 𝕜 => |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - 1| := by
    fun_prop
  rw [hS.measureReal_eq (p := fun A => ε ≤ |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - 1|)
    (measurableSet_le measurable_const hc.measurable)]
  rfl

/-- The JL moment property depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.hasJLMoment_iff {ν : Measure (Matrix k n 𝕜)}
    (hS : HasLaw S ν μ) : HasJLMoment S ε δ p μ ↔ HasJLMoment id ε δ p ν := by
  have hm (x : n → 𝕜) : AEStronglyMeasurable
      (fun A : Matrix k n 𝕜 => |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - 1| ^ p) ν := by
    have hc : Continuous fun A : Matrix k n 𝕜 => |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - 1| := by
      fun_prop
    exact (hc.measurable.pow_const p).aestronglyMeasurable
  have hint (x : n → 𝕜) : ∫ ω, |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1| ^ p ∂μ =
      ∫ A, |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - 1| ^ p ∂ν := hS.integral_comp (hm x)
  constructor
  · intro h
    exact ⟨fun x hx => (hS.integrable_comp_iff (hm x)).1 (h.integrable x hx),
      fun x hx => (hint x).symm.trans_le (h.integral_le x hx)⟩
  · intro h
    exact ⟨fun x hx => (hS.integrable_comp_iff (hm x)).2 (h.integrable x hx),
      fun x hx => (hint x).trans_le (h.integral_le x hx)⟩

/-- The JL property holds with any larger distortion and failure probability. -/
theorem HasJLProperty.mono [IsFiniteMeasure μ] (h : HasJLProperty S ε δ μ) (hε : ε ≤ ε')
    (hδ : δ ≤ δ') : HasJLProperty S ε' δ' μ := by
  exact fun x hx => (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω =>
    hε.trans hω)).trans ((h x hx).trans hδ)

/-- The JL moment property holds with any larger distortion and failure probability, for
$0 \le \varepsilon$, $0 \le p$, $0 \le \delta$. -/
theorem HasJLMoment.mono (h : HasJLMoment S ε δ p μ) (hε : ε ≤ ε') (hδ : δ ≤ δ') (hε0 : 0 ≤ ε)
    (hp : 0 ≤ p) (hδ0 : 0 ≤ δ) : HasJLMoment S ε' δ' p μ := by
  refine ⟨h.integrable, fun x hx => (h.integral_le x hx).trans ?_⟩
  have hε' : 0 ≤ ε' := hε0.trans hε
  calc ε ^ p * δ ≤ ε' ^ p * δ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hε0 hε hp) hδ0
    _ ≤ ε' ^ p * δ' := mul_le_mul_of_nonneg_left hδ (Real.rpow_nonneg hε' p)

/-- The JL property at a nonzero vector $\mathbf{x}$:
$\mathbb{P}[\varepsilon \|\mathbf{x}\|^2 \le \lvert \|\mathbf{S}\mathbf{x}\|^2 - \|\mathbf{x}\|^2
\rvert] \le \delta$. -/
theorem HasJLProperty.measureReal_abs_norm_mulVec_sq_sub_ge_le (h : HasJLProperty S ε δ μ)
    {x : n → 𝕜} (hx : x ≠ 0) :
    μ.real {ω | ε * ‖WithLp.toLp 2 x‖ ^ 2 ≤
      |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2|} ≤ δ := by
  obtain ⟨u, hu, hSu⟩ := exists_norm_eq_one_and_norm_mulVec_sq_sub_norm_sq_eq (k := k) hx
  have hc0 : 0 < ‖WithLp.toLp 2 x‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])) 2
  have e : {ω | ε * ‖WithLp.toLp 2 x‖ ^ 2 ≤
      |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2|} =
      {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ u)‖ ^ 2 - 1|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hSu, abs_mul, abs_of_pos hc0]
    constructor
    · intro h'
      exact le_of_mul_le_mul_right (by rwa [mul_comm _ |_|] at h') hc0
    · intro h'
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left h' hc0.le
  rw [e]
  exact h u hu

/-- **Johnson–Lindenstrauss lemma**: for finitely many points $\mathbf{x}_i$, $i \in \iota$, and
$\delta \ge 0$, the probability that some pairwise difference $\mathbf{x}_i - \mathbf{x}_j \ne
\mathbf{0}$ has its squared norm distorted by a factor $\varepsilon$ or more,
$$\varepsilon \|\mathbf{x}_i - \mathbf{x}_j\|^2
\le \bigl\lvert \|\mathbf{S}(\mathbf{x}_i - \mathbf{x}_j)\|^2 - \|\mathbf{x}_i - \mathbf{x}_j\|^2
\bigr\rvert,$$
is at most $\binom{\lvert \iota \rvert}{2} \delta$ (union over unordered pairs).
[Woodruff2014, Definition 3]; there inner products on a finite set, here squared norms of
differences.
Result: jl-lemma -/
theorem HasJLProperty.measureReal_exists_abs_norm_mulVec_sq_sub_ge_le (h : HasJLProperty S ε δ μ)
    (hδ : 0 ≤ δ) {ι : Type*} [Fintype ι] (x : ι → n → 𝕜) :
    μ.real {ω | ∃ i j, x i ≠ x j ∧ ε * ‖WithLp.toLp 2 (x i - x j)‖ ^ 2 ≤
      |‖WithLp.toLp 2 (S ω *ᵥ (x i - x j))‖ ^ 2 - ‖WithLp.toLp 2 (x i - x j)‖ ^ 2|} ≤
      (Fintype.card ι).choose 2 * δ := by
  classical
  set P : (n → 𝕜) → Ω → Prop := fun v ω => ε * ‖WithLp.toLp 2 v‖ ^ 2 ≤
    |‖WithLp.toLp 2 (S ω *ᵥ v)‖ ^ 2 - ‖WithLp.toLp 2 v‖ ^ 2| with hP
  have hPneg (v : n → 𝕜) (ω : Ω) : P (-v) ω ↔ P v ω := by
    simp only [hP, Matrix.mulVec_neg, WithLp.toLp_neg, norm_neg]
  let F : Sym2 ι → Set Ω := Sym2.lift ⟨fun i j => {ω | x i ≠ x j ∧ P (x i - x j) ω},
    fun i j => by
      ext ω
      simp only [Set.mem_ofPred_eq, ne_comm (a := x i), ← neg_sub (x i) (x j), hPneg]⟩
  have hF (i j : ι) : F s(i, j) = {ω | x i ≠ x j ∧ P (x i - x j) ω} := Sym2.lift_mk _ i j
  have e : {ω | ∃ i j, x i ≠ x j ∧ P (x i - x j) ω} = ⋃ z : {z : Sym2 ι // ¬ z.IsDiag}, F z := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, j, hne, hω⟩
      refine ⟨⟨s(i, j), fun hd => hne (by rw [Sym2.mk_isDiag_iff.1 hd])⟩, ?_⟩
      rw [hF]
      exact ⟨hne, hω⟩
    · rintro ⟨⟨z, hz⟩, hω⟩
      induction z using Sym2.ind with
      | _ i j =>
        rw [hF] at hω
        exact ⟨i, j, hω⟩
  have hle (z : {z : Sym2 ι // ¬ z.IsDiag}) : μ.real (F z) ≤ δ := by
    obtain ⟨z, hz⟩ := z
    induction z using Sym2.ind with
    | _ i j =>
      rw [hF]
      by_cases hne : x i = x j
      · simp only [hne, ne_eq, not_true_eq_false, false_and, Set.ofPred_false, measureReal_empty]
        exact hδ
      · have hs : {ω | x i ≠ x j ∧ P (x i - x j) ω} = {ω | P (x i - x j) ω} := by
          ext ω
          simp only [Set.mem_ofPred_eq, ne_eq, hne, not_false_eq_true, true_and]
        rw [hs]
        exact h.measureReal_abs_norm_mulVec_sq_sub_ge_le (sub_ne_zero.2 hne)
  change μ.real {ω | ∃ i j, x i ≠ x j ∧ P (x i - x j) ω} ≤ _
  rw [e]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  refine (Finset.sum_le_sum fun z _ => hle z).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Sym2.card_subtype_not_diag, nsmul_eq_mul]

/-- **Moments give tails**: for $\varepsilon > 0$ and $p > 0$, the JL moment property implies the
JL property with the same $\varepsilon$ and $\delta$ (Markov's inequality in $L^p$).
[Woodruff2014, §2.2]. -/
theorem HasJLMoment.hasJLProperty (h : HasJLMoment S ε δ p μ) (hε : 0 < ε) (hp : 0 < p) :
    HasJLProperty S ε δ μ := by
  intro x hx
  refine (measureReal_abs_ge_le_integral_rpow_div hp (h.integrable x hx) hε).trans ?_
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hε p), mul_comm]
  exact h.integral_le x hx

/-- **Moments from tails**: under a finite measure, if $\mathbf{S}$ is almost everywhere
measurable and has the JL property at every distortion $t > 0$ with failure probability
$2\exp(-\min(t^2/(2v), t/(2b)))$, $v, b > 0$, then for $\varepsilon > 0$ and $p > 0$ it has the
JL moment property with exponent $p$ and failure
probability <!-- value subexponentialMomentBound v b p -->
$$\delta = \frac{p(2v)^{p/2}\Gamma(p/2) + 2p(2b)^{p}\Gamma(p)}{\varepsilon^p}\,,$$
the numerator being `NLAlib.subexponentialMomentBound v b p`, the layer-cake integral of the
tail (`NLAlib.integral_rpow_le_of_measureReal_ge_le_two_mul_exp`). The converse direction of
`NLAlib.HasJLMoment.hasJLProperty`. [Woodruff2014, Definition 12] for the property; that dense
sketches have it at $p = \log(1/\delta)$ follows from [KaneNelson2014, Remark 22]. -/
theorem hasJLMoment_of_forall_hasJLProperty [IsFiniteMeasure μ] (hS : AEMeasurable S μ)
    {v b : ℝ} (hv : 0 < v) (hb : 0 < b)
    (h : ∀ t : ℝ, 0 < t →
      HasJLProperty S t (2 * Real.exp (-min (t ^ 2 / (2 * v)) (t / (2 * b)))) μ)
    (hε : 0 < ε) (hp : 0 < p) :
    HasJLMoment S ε (subexponentialMomentBound v b p / ε ^ p) p μ := by
  have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
  have key (x : n → 𝕜) (hx : ‖WithLp.toLp 2 x‖ = 1) :=
    integral_rpow_le_of_measureReal_ge_le_two_mul_exp (μ := μ)
      (f := fun ω => |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1|)
      (by fun_prop) (ae_of_all _ fun ω => abs_nonneg _) hv hb hp fun t ht => h t ht x hx
  refine ⟨fun x hx => (key x hx).1, fun x hx => ?_⟩
  rw [mul_div_cancel₀ _ hεp.ne']
  exact (key x hx).2

/-- The $p$-th moment of the distortion at any vector is integrable. -/
theorem HasJLMoment.integrable_abs_norm_mulVec_sq_sub_rpow (h : HasJLMoment S ε δ p μ)
    (hp : 0 < p) (x : n → 𝕜) :
    Integrable (fun ω => |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2| ^ p) μ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Matrix.mulVec_zero, WithLp.toLp_zero, norm_zero, sub_self, abs_zero,
      Real.zero_rpow hp.ne']
    exact integrable_zero _ _ _
  obtain ⟨u, hu, hSu⟩ := exists_norm_eq_one_and_norm_mulVec_sq_sub_norm_sq_eq (k := k) hx
  simp only [abs_sub_rpow_eq hSu]
  exact (h.integrable u hu).const_mul _

/-- The JL moment bound at any vector, for $p > 0$:
$\mathbb{E}\lvert \|\mathbf{S}\mathbf{x}\|^2 - \|\mathbf{x}\|^2 \rvert^p
\le \varepsilon^p \delta \|\mathbf{x}\|^{2p}$. -/
theorem HasJLMoment.integral_abs_norm_mulVec_sq_sub_rpow_le (h : HasJLMoment S ε δ p μ)
    (hp : 0 < p) (x : n → 𝕜) :
    ∫ ω, |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2| ^ p ∂μ ≤
      ε ^ p * δ * ‖WithLp.toLp 2 x‖ ^ (2 * p) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Matrix.mulVec_zero, WithLp.toLp_zero, norm_zero, sub_self, abs_zero,
      Real.zero_rpow hp.ne', integral_zero, Real.zero_rpow (mul_pos two_pos hp).ne', mul_zero,
      le_refl]
  obtain ⟨u, hu, hSu⟩ := exists_norm_eq_one_and_norm_mulVec_sq_sub_norm_sq_eq (k := k) hx
  simp only [abs_sub_rpow_eq hSu]
  rw [integral_const_mul, mul_comm (ε ^ p * δ)]
  exact mul_le_mul_of_nonneg_left (h.integral_le u hu) (Real.rpow_nonneg (norm_nonneg _) _)

/-! ### Frobenius-norm preservation -/

section Frobenius

variable {q : Type*} [Fintype q]

/-- The Frobenius distortion is at most the sum of the column distortions. -/
private theorem abs_frobNorm_mul_sq_sub_le_sum (A : Matrix k n 𝕜) (X : Matrix n q 𝕜) :
    |frobNorm (A * X) ^ 2 - frobNorm X ^ 2| ≤
      ∑ j, |‖WithLp.toLp 2 (A *ᵥ X.col j)‖ ^ 2 - ‖WithLp.toLp 2 (X.col j)‖ ^ 2| := by
  rw [frobNorm_sq_eq_sum_col, frobNorm_sq_eq_sum_col, ← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- The $p$-th power of the Frobenius distortion
$\lvert\|\mathbf{S}\mathbf{X}\|_{\mathsf{F}}^2 - \|\mathbf{X}\|_{\mathsf{F}}^2\rvert$ is
integrable, for $p \ge 1$; the matrix twin of
`NLAlib.HasJLMoment.integrable_abs_norm_mulVec_sq_sub_rpow`. -/
theorem HasJLMoment.integrable_abs_frobNorm_mul_sq_sub_rpow (h : HasJLMoment S ε δ p μ)
    (hp : 1 ≤ p) (hS : AEMeasurable S μ) (X : Matrix n q 𝕜) :
    Integrable (fun ω => |frobNorm (S ω * X) ^ 2 - frobNorm X ^ 2| ^ p) μ := by
  have hp0 : 0 < p := by linarith
  have hc : Continuous fun A : Matrix k n 𝕜 =>
      ∑ j, |‖WithLp.toLp 2 (A *ᵥ X.col j)‖ ^ 2 - ‖WithLp.toLp 2 (X.col j)‖ ^ 2| :=
    continuous_finsetSum _ fun j _ => by fun_prop
  have hsum := integrable_rpow_sum
    (Y := fun j ω => |‖WithLp.toLp 2 (S ω *ᵥ X.col j)‖ ^ 2 - ‖WithLp.toLp 2 (X.col j)‖ ^ 2|)
    (fun j ω => abs_nonneg _) hp
    ((hc.measurable.comp_aemeasurable hS).pow_const p).aestronglyMeasurable
    (fun j => h.integrable_abs_norm_mulVec_sq_sub_rpow hp0 _)
  have hF : Continuous fun A : Matrix k n 𝕜 => |frobNorm (A * X) ^ 2 - frobNorm X ^ 2| :=
    (((continuous_frobNorm.comp (by fun_prop)).pow 2).sub continuous_const).abs
  refine hsum.mono' ((hF.measurable.comp_aemeasurable hS).pow_const p).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (abs_frobNorm_mul_sq_sub_le_sum _ _) hp0.le

/-- **Frobenius-norm preservation from the JL moment property**: for $\varepsilon \ge 0$ and
$p \ge 1$,
$$\mathbb{E}\bigl\lvert\|\mathbf{S}\mathbf{X}\|_{\mathsf{F}}^2 - \|\mathbf{X}\|_{\mathsf{F}}^2
\bigr\rvert^p \le (\varepsilon\|\mathbf{X}\|_{\mathsf{F}}^2)^p\,\delta\,.$$
The matrix twin of `NLAlib.HasJLMoment.integral_abs_norm_mulVec_sq_sub_rpow_le`. Any field: only
the vector property is used, column by column, with Jensen's inequality for the weights
$\|\mathbf{X}_{:,j}\|^2/\|\mathbf{X}\|_{\mathsf{F}}^2$ (`NLAlib.integral_rpow_sum_le`). As a
remark, the distortion is the trace of the approximate-multiplication error at
$\mathbf{A} = \mathbf{B} = \mathbf{X}$, which the Frobenius bound on that error does not
control without a rank bound. [Woodruff2014, proof of Theorem 13], the same summation over
columns; [CohenElderMuscoMuscoPersu2015, §7, discussion after Lemma 11], stated there as standard
for embedding matrices.
Result: jl-moment-frobenius -/
theorem HasJLMoment.integral_abs_frobNorm_mul_sq_sub_rpow_le (h : HasJLMoment S ε δ p μ)
    (hε : 0 ≤ ε) (hp : 1 ≤ p) (hS : AEMeasurable S μ) (X : Matrix n q 𝕜) :
    ∫ ω, |frobNorm (S ω * X) ^ 2 - frobNorm X ^ 2| ^ p ∂μ ≤ (ε * frobNorm X ^ 2) ^ p * δ := by
  have hp0 : 0 < p := by linarith
  rcases eq_or_ne X 0 with rfl | hX
  · simp only [Matrix.mul_zero, frobNorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_self, abs_zero, Real.zero_rpow hp0.ne', integral_zero, mul_zero, zero_mul,
      le_refl]
  have hF0 : 0 < frobNorm X ^ 2 :=
    pow_pos (lt_of_le_of_ne (frobNorm_nonneg _) (Ne.symm (mt frobNorm_eq_zero_iff.1 hX))) 2
  set F := frobNorm X ^ 2 with hF
  set Y : q → Ω → ℝ :=
    fun j ω => |‖WithLp.toLp 2 (S ω *ᵥ X.col j)‖ ^ 2 - ‖WithLp.toLp 2 (X.col j)‖ ^ 2| with hYdef
  have hc : Continuous fun A : Matrix k n 𝕜 =>
      ∑ j, |‖WithLp.toLp 2 (A *ᵥ X.col j)‖ ^ 2 - ‖WithLp.toLp 2 (X.col j)‖ ^ 2| :=
    continuous_finsetSum _ fun j _ => by fun_prop
  have hm : AEStronglyMeasurable (fun ω => (∑ j, Y j ω) ^ p) μ :=
    ((hc.measurable.comp_aemeasurable hS).pow_const p).aestronglyMeasurable
  have hY0 : ∀ j ω, 0 ≤ Y j ω := fun j ω => abs_nonneg _
  have hYint : ∀ j, Integrable (fun ω => Y j ω ^ p) μ :=
    fun j => h.integrable_abs_norm_mulVec_sq_sub_rpow hp0 _
  refine (integral_mono (h.integrable_abs_frobNorm_mul_sq_sub_rpow hp hS X)
    (integrable_rpow_sum hY0 hp hm hYint) fun ω => Real.rpow_le_rpow (abs_nonneg _)
      (abs_frobNorm_mul_sq_sub_le_sum _ _) hp0.le).trans ?_
  refine integral_rpow_sum_le hY0 hp hm (w := fun j => ‖WithLp.toLp 2 (X.col j)‖ ^ 2 / F)
    (fun j => by positivity) ?_ (fun j hj ω => ?_) hYint (fun j => ?_)
  · rw [← Finset.sum_div, ← frobNorm_sq_eq_sum_col, ← hF, div_self hF0.ne']
  · have hx : X.col j = 0 := by
      have := (div_eq_zero_iff.1 hj).resolve_right hF0.ne'
      rwa [sq_eq_zero_iff, norm_eq_zero, WithLp.toLp_eq_zero] at this
    simp only [hYdef, hx, Matrix.mulVec_zero, WithLp.toLp_zero, norm_zero, sub_self, abs_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  · refine (h.integral_abs_norm_mulVec_sq_sub_rpow_le hp0 (X.col j)).trans_eq ?_
    rw [Real.div_rpow (sq_nonneg _) hF0.le, Real.mul_rpow hε hF0.le,
      Real.rpow_mul (norm_nonneg _), Real.rpow_two]
    have hFp : 0 < F ^ p := Real.rpow_pos_of_pos hF0 p
    field_simp

/-- **Frobenius-norm preservation, tail form**: for $\varepsilon > 0$, $p \ge 1$ and
$\mathbf{X} \ne \mathbf{0}$,
$$\mathbb{P}\bigl[\varepsilon\|\mathbf{X}\|_{\mathsf{F}}^2 \le
\bigl\lvert\|\mathbf{S}\mathbf{X}\|_{\mathsf{F}}^2 - \|\mathbf{X}\|_{\mathsf{F}}^2\bigr\rvert\bigr]
\le \delta\,,$$
from `NLAlib.HasJLMoment.integral_abs_frobNorm_mul_sq_sub_rpow_le` by Markov's inequality; the
matrix twin of `NLAlib.HasJLProperty.measureReal_abs_norm_mulVec_sq_sub_ge_le` through
`NLAlib.HasJLMoment.hasJLProperty`. [Woodruff2014, proof of Theorem 13];
[CohenElderMuscoMuscoPersu2015, §7, discussion after Lemma 11].
Result: jl-moment-frobenius -/
theorem HasJLMoment.measureReal_abs_frobNorm_mul_sq_sub_ge_le (h : HasJLMoment S ε δ p μ)
    (hε : 0 < ε) (hp : 1 ≤ p) (hS : AEMeasurable S μ) {X : Matrix n q 𝕜} (hX : X ≠ 0) :
    μ.real {ω | ε * frobNorm X ^ 2 ≤ |frobNorm (S ω * X) ^ 2 - frobNorm X ^ 2|} ≤ δ := by
  have hp0 : 0 < p := by linarith
  have ht : 0 < ε * frobNorm X ^ 2 := mul_pos hε
    (pow_pos (lt_of_le_of_ne (frobNorm_nonneg _) (Ne.symm (mt frobNorm_eq_zero_iff.1 hX))) 2)
  refine (measureReal_abs_ge_le_integral_rpow_div hp0
    (h.integrable_abs_frobNorm_mul_sq_sub_rpow hp hS X) ht).trans ?_
  rw [div_le_iff₀ (Real.rpow_pos_of_pos ht p), mul_comm]
  exact h.integral_abs_frobNorm_mul_sq_sub_rpow_le hε.le hp hS X

end Frobenius

/-! ### From the JL property to subspace embeddings -/

/-- The quadratic form of the Gram error of $\mathbf{A}\mathbf{U}$ at $\mathbf{x}$ is the
distortion of $\mathbf{U}\mathbf{x}$:
$\operatorname{Re} \mathbf{x}^{\mathsf{H}} \bigl((\mathbf{A}\mathbf{U})^{\mathsf{H}}
(\mathbf{A}\mathbf{U}) - \mathbf{I}\bigr) \mathbf{x}
= \|\mathbf{A}\mathbf{U}\mathbf{x}\|^2 - \|\mathbf{x}\|^2$. -/
private theorem re_quadForm_gram_sub_one {p : Type*} [Fintype p] [DecidableEq p]
    (U : Matrix n p 𝕜)
    (A : Matrix k n 𝕜) (x : p → 𝕜) :
    RCLike.re (quadForm ((A * U)ᴴ * (A * U) - 1) x) =
      ‖WithLp.toLp 2 (A *ᵥ (U *ᵥ x))‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [quadForm_sub_left, map_sub, quadForm_conjTranspose_mul_self, quadForm_one,
    RCLike.ofReal_re, RCLike.ofReal_re, Matrix.mulVec_mulVec]

/-- **JL plus a net**: a JL tail at $\varepsilon$ with failure probability $\delta \ge 0$, under a
finite measure, makes $\mathbf{S}$ a subspace embedding of a fixed $\mathbf{U}$ with orthonormal
columns with constants $1 \mp (5/4)\varepsilon$, failing with probability at most
$21^{\lvert p \rvert \dim_{\mathbb{R}} \Bbbk} \delta$.
[Vershynin2018, proof of Theorem 4.6.1, (4.22)]; [Woodruff2014, Lemma 5 and
Theorem 6], there with a $1/4$-net (Vershynin: constants $1 \mp 2\varepsilon$, $9^d$ points) and a
$1/2$-net with $O(\varepsilon)$ (Woodruff). The net here has radius $\eta = 1/10$: a JL family
with a sub-Gaussian exponent $\varepsilon^2$ needs $(1 - 2\eta)^{-2}(d \log(1 + 2/\eta) +
\log(2/\delta))$ rows up to its constant, and both terms are smaller at $\eta = 1/10$
($1.5625 \cdot (3.04d + \log(2/\delta))$) than at $\eta = 1/4$ ($4 \cdot (2.20d + \log(2/\delta))$),
so the radius-$1/4$ statement is not kept beside it. -/
theorem HasJLProperty.hasSubspaceEmbedding [IsFiniteMeasure μ] {p : Type*} [Fintype p]
    [DecidableEq p] {U : Matrix n p 𝕜} (h : HasJLProperty S ε δ μ) (hδ : 0 ≤ δ)
    (hU : HasOrthonormalCols U) :
    HasSubspaceEmbedding S U (1 - 5 / 4 * ε) (1 + 5 / 4 * ε)
      (21 ^ (Fintype.card p * Module.finrank ℝ 𝕜) * δ) μ := by
  rcases isEmpty_or_nonempty p with hp | hp
  · have hall : ∀ ω, IsSubspaceEmbedding (S ω) U (1 - 5 / 4 * ε) (1 + 5 / 4 * ε) := fun ω =>
      ⟨by unfold IsSubspaceInjection; exact le_of_eq (Subsingleton.elim _ _),
        le_of_eq (Subsingleton.elim _ _)⟩
    unfold HasSubspaceEmbedding
    simp only [hall, not_true_eq_false, Set.ofPred_false, measureReal_empty]
    positivity
  have h9 : (1 : ℝ) ≤ 21 ^ (Fintype.card p * Module.finrank ℝ 𝕜) := one_le_pow₀ (by norm_num)
  obtain ⟨x₀⟩ := hp
  rcases le_or_gt ε 0 with hε | hε
  · -- the JL event at any unit vector is everything
    have hx₀ : ‖WithLp.toLp 2 (U *ᵥ Pi.single x₀ (1 : 𝕜))‖ = 1 := by
      rw [hU.norm_toLp_mulVec, PiLp.toLp_single, PiLp.norm_single, norm_one]
    have huniv := h _ hx₀
    have e : {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ (U *ᵥ Pi.single x₀ (1 : 𝕜)))‖ ^ 2 - 1|} =
        Set.univ := Set.eq_univ_of_forall fun ω => hε.trans (abs_nonneg _)
    rw [e] at huniv
    unfold HasSubspaceEmbedding
    calc _ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ ≤ δ := huniv
      _ ≤ _ := le_mul_of_one_le_left hδ h9
  obtain ⟨net, hcard, hunit, hnet⟩ :=
    exists_finset_specNorm_le_div_of_isHermitian 𝕜 p (ε := 1 / 10) (by norm_num) (by norm_num)
  rw [Module.finrank_fun] at hcard
  norm_num at hcard
  refine hU.hasSubspaceEmbedding_of_measureReal_le ?_
  have hsub : {ω | 5 / 4 * ε ≤ specNorm ((S ω * U)ᴴ * (S ω * U) - 1)} ⊆
      ⋃ x ∈ net, {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ (U *ᵥ x))‖ ^ 2 - 1|} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hnot hω
    obtain ⟨M, hM0, hMε, hM⟩ := Finset.exists_le_lt_of_forall_lt net
      (fun x => |‖WithLp.toLp 2 (S ω *ᵥ (U *ᵥ x))‖ ^ 2 - 1|) hε hnot
    have hH : ((S ω * U)ᴴ * (S ω * U) - 1).IsHermitian :=
      (Matrix.isHermitian_conjTranspose_mul_self _).sub Matrix.isHermitian_one
    have hn := hnet _ hH hM0 fun x hx => by
      rw [re_quadForm_gram_sub_one, hunit x hx, one_pow]
      exact hM x hx
    rw [show M / (1 - 2 * (1 / 10 : ℝ)) = 5 / 4 * M by ring] at hn
    linarith
  calc μ.real {ω | 5 / 4 * ε ≤ specNorm ((S ω * U)ᴴ * (S ω * U) - 1)}
    _ ≤ μ.real (⋃ x ∈ net, {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ (U *ᵥ x))‖ ^ 2 - 1|}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ x ∈ net, μ.real {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ (U *ᵥ x))‖ ^ 2 - 1|} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ net, δ := Finset.sum_le_sum fun x hx =>
      h _ (by rw [hU.norm_toLp_mulVec, hunit x hx])
    _ = net.card * δ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr

/-- **JL plus a net, oblivious form**: a JL tail at $\varepsilon$ with failure probability
$\delta \ge 0$, under a finite measure, makes $\mathbf{S}$ an oblivious subspace embedding for
dimension $d$ with constants $1 \mp (5/4)\varepsilon$ and failure probability
$21^{d \dim_{\mathbb{R}} \Bbbk} \delta$ (a net of radius $1/10$). From
`NLAlib.HasJLProperty.hasSubspaceEmbedding` at
`Fin (min d (card n))` by `NLAlib.IsObliviousSubspaceEmbedding.of_hasOrthonormalCols` and `mono`.
[Vershynin2018, proof of Theorem 4.6.1, (4.22)]; [Woodruff2014, Theorem 6]. -/
theorem HasJLProperty.isObliviousSubspaceEmbedding [IsFiniteMeasure μ]
    (h : HasJLProperty S ε δ μ) (hδ : 0 ≤ δ) (d : ℕ) :
    IsObliviousSubspaceEmbedding S d (1 - 5 / 4 * ε) (1 + 5 / 4 * ε)
      (21 ^ (d * Module.finrank ℝ 𝕜) * δ) μ := by
  have hd : Fintype.card (Fin (min d (Fintype.card n))) ≤ Fintype.card n := by
    rw [Fintype.card_fin]; exact min_le_right _ _
  have h' := IsObliviousSubspaceEmbedding.of_hasOrthonormalCols hd
    fun U hU => h.hasSubspaceEmbedding hδ hU
  rw [Fintype.card_fin] at h'
  intro U hU
  refine (h' U (le_min hU (Matrix.rank_le_card_width U))).mono le_rfl le_rfl ?_
  gcongr
  · norm_num
  · exact min_le_left _ _

/-! ### From subspace embeddings to the JL property -/

/-- **An OSE for dimension one has the JL property**: under a finite measure, if $\mathbf{S}$ is
an oblivious subspace embedding for dimension $1$ with constants $a, b$ and failure probability
$\delta$, and $1 - \varepsilon < a$, $b < 1 + \varepsilon$, then it has the JL property with
distortion $\varepsilon$ and failure probability $\delta$: at the column $\mathbf{x}$, of rank at
most $1$, the embedding gives $a \le \|\mathbf{S}\mathbf{x}\|^2 \le b$. The strict inequalities
are needed, since the JL event $\{\varepsilon \le \lvert\cdot\rvert\}$ is non-strict and a discrete
law may charge its boundary. The converse of `NLAlib.HasJLProperty.isObliviousSubspaceEmbedding`
at $d = 1$, without its net factor. [Woodruff2014, Definitions 2 and 3], there for
$1 \mp \varepsilon$. -/
theorem IsObliviousSubspaceEmbedding.hasJLProperty [IsFiniteMeasure μ] {a b : ℝ}
    (h : IsObliviousSubspaceEmbedding S 1 a b δ μ) (ha : 1 - ε < a) (hb : b < 1 + ε) :
    HasJLProperty S ε δ μ := by
  intro x hx
  have hU : (Matrix.replicateCol Unit x).rank ≤ 1 :=
    (Matrix.rank_le_card_width _).trans_eq Fintype.card_unit
  refine (measureReal_mono fun ω hω => ?_).trans (h.hasSubspaceEmbedding hU)
  intro hemb
  have hy : x ∈ LinearMap.range (Matrix.replicateCol Unit x).mulVecLin :=
    ⟨fun _ => 1, by
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.replicateCol_apply]⟩
  obtain ⟨h1, h2⟩ := isSubspaceEmbedding_iff_forall_mem_range.mp hemb x hy
  rw [hx, one_pow, mul_one] at h1 h2
  have hω' : ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1| := hω
  rw [le_abs] at hω'
  rcases hω' with h3 | h3 <;> linarith

end NLAlib
