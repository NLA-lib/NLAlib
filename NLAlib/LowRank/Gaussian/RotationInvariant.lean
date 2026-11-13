/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.LowRank.Gaussian.RangeFinderTail
public import NLAlib.LowRank.Gaussian.RotationInvariantFactor
public import NLAlib.LowRank.Random.Nystrom
public import NLAlib.RandomMatrix.Haar.Transfer

/-!
# The randomized SVD with a rotation-invariant test matrix

A random test matrix $\mathbf{X}$ of size $n \times \ell$ is rotation invariant when its law
$\nu$ is a left unitarily invariant probability measure (`NLAlib.IsLeftUnitarilyInvariant`:
$\mathbf{U}\mathbf{X}$ has the law of $\mathbf{X}$ for every orthogonal $\mathbf{U}$); with full
column rank almost surely this is the full-rank rotation-invariant embedding of Epperly and
Webber. The standard Gaussian and the Haar frame (for $\ell \le n$) are instances. For such a
test matrix the range projector $\mathbf{P}_{\mathbf{A}\mathbf{X}}$ has the law of
$\mathbf{P}_{\mathbf{A}\mathbf{G}}$ for a standard Gaussian $\mathbf{G}$
(`NLAlib.hasLaw_rangeProjector_mul_of_isLeftUnitarilyInvariant`), and every error of the
randomized SVD is a measurable function of that projector. So the Gaussian expectations of
`NLAlib.LowRank.Gaussian.RangeFinder` and the Gaussian tails of
`NLAlib.LowRank.Gaussian.RangeFinderTail` hold verbatim.

The hypotheses are `HasLaw X ν μ` with `[IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]`
and `∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec`. The second is unsatisfiable for $\ell > n$; a Haar
frame of that shape has orthonormal rows and recovers the matrix almost surely
(`NLAlib.ae_rank_mul_eq_min_of_hasLaw_haarFrame`). The late-truncated Frobenius error is
transferred through its choice-free form (`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq`).

**Nyström.** For positive semidefinite $\mathbf{H}$, $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$ has
the law of $\mathsf{nystrom}(\mathbf{H}, \mathbf{G})$ for a standard Gaussian $\mathbf{G}$, and the
Nyström expectations and tails hold with the Gaussian constants. Each is the rotation-invariant
statement for the randomized SVD at a factor $\mathbf{F}$ with
$\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$, through the Gram correspondence
(`NLAlib.conjTranspose_mul_self_sub_nystrom`); the spectral error of truncated Nyström adds reverse
Eckart–Young (`NLAlib.LowRank.Random.Nystrom`) and is stated for a measurable selector and,
directly, for `truncatedSVD`, which is Borel measurable (`NLAlib.measurable_truncatedSVD`).

## Main results

* `NLAlib.ae_rsvd_eq_self_of_isLeftUnitarilyInvariant`: exact recovery at
  $\operatorname{rank}\mathbf{A} \le \ell$.
* the Gram form, in the `NLAlib.SymmetricGauge` namespace:
  `integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_isLeftUnitarilyInvariant`.
* `NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant`: HMT Theorem 10.5 and
  Epperly and Webber's Theorem 3.1, squared (the printed first-moment form follows by Jensen).
* `NLAlib.integral_specNorm_sub_rsvd_le_of_isLeftUnitarilyInvariant`: HMT Theorem 10.6.
* `NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_isLeftUnitarilyInvariant`: the
  truncated output.
* the Gram-form tail (TW Theorem 8.1 (RSVD1)), in the `NLAlib.SymmetricGauge` namespace:
  `measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_isLeftUnitarilyInvariant`.
* Epperly and Webber's sharp bounds, with a rank parameter $r \ge \operatorname{rank}$ and the
  factor <!-- value rotationInvariantFactor r \ell q -->
  $(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))$:
  in the `Matrix.PosSemidef` namespace,
  `integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant_of_rank_le` (their Theorem
  3.6(a)), its Gaussian twin
  `integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix_of_rank_le` and the truncated
  decay form
  `integral_nuclearNorm_sub_truncatedSVD_nystrom_le_add_of_isLeftUnitarilyInvariant_of_rank_le`;
  `NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant_of_rank_le` (their Theorem
  3.2) and its Gaussian twin
  `NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_of_rank_le`. The HMT forms
  above are their instances $r = n$.
* Nyström, in the `Matrix.PosSemidef` namespace: `hasLaw_nystrom_of_isLeftUnitarilyInvariant`
  (the law of the output), `integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant`,
  `integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant`,
  `integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_isLeftUnitarilyInvariant` (MT Theorem
  14.1, for a measurable selector) and its direct form
  `integral_specNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant`,
  `ae_nystrom_eq_self_of_isLeftUnitarilyInvariant`; in the
  `NLAlib.SymmetricGauge` namespace,
  `integral_matrixNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant` and
  `measureReal_matrixNorm_sub_nystrom_gt_le_of_isLeftUnitarilyInvariant`.
* the asymptotic forms, $O(k/\varepsilon)$ samples for relative error $1 + \varepsilon$, of
  `NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant` and of the two Nyström
  trace bounds: `NLAlib.exists_forall_` followed by their names (without `Matrix.PosSemidef`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] {X : Ω → Matrix n l ℝ}

omit [Fintype n] in
/-- $\mathbf{P} \mapsto \mathbf{A} - \mathbf{P}\mathbf{A}$ is measurable. -/
private theorem measurable_sub_mul (A : Matrix m n ℝ) :
    Measurable fun P : Matrix m m ℝ => A - P * A :=
  measurable_const.matrix_sub (measurable_id.matrix_mul measurable_const)

variable [DecidableEq n] {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν]
  [IsLeftUnitarilyInvariant ν]

/-! ### Exact recovery -/

/-- A rotation-invariant sketch at least as wide as the rank recovers the matrix: if
$\operatorname{rank}\mathbf{A} \le \ell$, then $\mathsf{rsvd}(\mathbf{A}, \mathbf{X}) =
\mathbf{A}$ almost surely, for a test matrix $\mathbf{X}$ with a left unitarily invariant law
and full column rank almost surely. -/
theorem ae_rsvd_eq_self_of_isLeftUnitarilyInvariant (A : Matrix m n ℝ)
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)
    (hA : A.rank ≤ Fintype.card l) : ∀ᵐ ω ∂μ, rsvd A (X ω) = A := by
  filter_upwards [ae_rank_mul_eq_min_of_isLeftUnitarilyInvariant A hX hXr] with ω hω
  exact rsvd_eq_self_of_rank_eq (hω.trans (min_eq_left hA))

/-! ### Expectations -/

namespace SymmetricGauge

/-- **The expected error of the randomized SVD, Gram form, rotation-invariant test matrices**:
for a test matrix $\mathbf{X}$ with a left unitarily invariant law and full column rank almost
surely (Gaussian, Haar, ...), $k + 2 \le \ell$ and every unitarily invariant norm,
$$\mathbb{E}\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))\bigr\|_{\Phi} \le
\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{k}{\ell - k - 1}\,
\|\mathbf{E}\|_{\mathsf{F}}^2\,,\qquad
\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\,,$$
the bound of the Gaussian test matrix (in this namespace,
`integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix`).
[TroppWebber2023, Theorem 8.1 (RSVD2)]; [EpperlyWebber2026, Theorem 3.1]; there for Gaussian test
matrices and Schatten $p \ge 2$ (TW), or rotation-invariant ones and the Frobenius norm (EW).
Result: randomized-svd-expected-error -/
theorem integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_isLeftUnitarilyInvariant
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        Φ (Finsupp.single 0 1) * ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
          frobNorm (A - truncatedSVD A k) ^ 2 := by
  have hg : Measurable fun P : Matrix m m ℝ => Φ.matrixNorm ((A - P * A)ᴴ * (A - P * A)) :=
    Φ.measurable_matrixNorm.comp ((Measurable.matrix_conjTranspose continuous_star.measurable
      (measurable_sub_mul A)).matrix_mul (measurable_sub_mul A))
  refine (integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant A hX hXr
    (f := fun Ω => Φ.matrixNorm ((A - rsvd A Ω)ᴴ * (A - rsvd A Ω))) hg fun _ => rfl).trans_le ?_
  exact integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix Φ A
    HasLaw.id hk

end SymmetricGauge

/-- **The average spectral error of the randomized SVD, rotation-invariant test matrices**: for a
test matrix $\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely
and $k + 2 \le \ell$, <!-- value gaussianPinvSpecNormBound k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_2 \le
\Bigl(1 + \sqrt{\tfrac{k}{\ell - k - 1}}\Bigr)\sigma_k(\mathbf{A}) +
\frac{e}{\ell - k}\sqrt{(\ell + k - 1)/2}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}\,,$$
the bound of the Gaussian test matrix
(`NLAlib.integral_specNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix`).
[HalkoMartinssonTropp2011, Theorem 10.6]; [MartinssonTropp2020, Theorem 11.5]; there for Gaussian
test matrices, with the constant $e\sqrt{k + p}/p$, $p = \ell - k$.
Result: randomized-svd-average-spectral-error -/
theorem integral_specNorm_sub_rsvd_le_of_isLeftUnitarilyInvariant (A : Matrix m n ℝ)
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ∂μ ≤
      (1 + √((k : ℝ) / ((Fintype.card l : ℝ) - k - 1))) * singularValues A k +
        gaussianPinvSpecNormBound k (Fintype.card l) * frobNorm (A - truncatedSVD A k) := by
  refine (integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant A hX hXr
    (f := fun Ω => specNorm (A - rsvd A Ω)) (measurable_specNorm.comp (measurable_sub_mul A))
    fun _ => rfl).trans_le ?_
  exact integral_specNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix A HasLaw.id hk

/-- **The expected error of the truncated randomized SVD, Frobenius norm, rotation-invariant test
matrices**: for a test matrix $\mathbf{X}$ with a left unitarily invariant law and full column
rank almost surely and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{A} -
\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
for every choice of the truncation. The error is transferred to the Gaussian through its
choice-free form, the squared error of the untruncated output plus the tail sum of squared
singular values of $\mathsf{rsvd}(\mathbf{A}, \mathbf{X})$.
[HalkoMartinssonTropp2011, Theorem 10.5]; [Woodruff2014, Lemma 48]; there for Gaussian test
matrices and the untruncated output, with Woodruff's truncation for free.
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_isLeftUnitarilyInvariant
    (A : Matrix m n ℝ) (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)
    {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have hg : Measurable fun P : Matrix m m ℝ => frobNorm (A - P * A) ^ 2 +
      ∑ i ∈ Finset.Ico k (min (Fintype.card m) (Fintype.card n)), singularValues (P * A) i ^ 2 :=
    ((measurable_frobNorm.comp (measurable_sub_mul A)).pow_const 2).add
      (Finset.measurable_sum _ fun i _ => ((measurable_singularValues i).comp
        (measurable_id.matrix_mul measurable_const)).pow_const 2)
  refine (integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant A hX hXr
    (f := fun Ω => frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2) hg fun Ω => ?_).trans_le ?_
  · rw [frobNorm_sub_truncatedSVD_rsvd_sq, frobNorm_sub_truncatedSVD_sq]
    rfl
  exact integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix A HasLaw.id hk

/-! ### Tails -/

namespace SymmetricGauge

/-- **The tail of the randomized SVD, Gram form, rotation-invariant test matrices**: for a test
matrix $\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely,
$d = \ell - k + 1$, every unitarily invariant norm, $s \ge 0$ and $t > 0$,
$$\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))\bigr\|_{\Phi} \le
\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{tk}{d}\,
\bigl(\|\mathbf{E}\|_{\mathsf{F}} + s\,\sigma_k(\mathbf{A})\bigr)^2\,,\qquad
\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\,,$$
outside probability <!-- value gaussianPinvFrobTail k d t -->
$e^{-s^2/2} + 2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$, the tail of the Gaussian test
matrix (in this namespace,
`measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix`).
[TroppWebber2023, Theorem 8.1 (RSVD1)]; there for Gaussian test matrices and Schatten norms
$p \ge 2$, with the noise term $(utk/d)\|\mathbf{E}\|_{\mathsf{F}}^2$ and the failure probability
$e^{-(u-2)/4} + \sqrt{\pi k}\,(t/e)^{-d/2}$, which follow from this bound at $s = \sqrt{u} - 1$; the
library's second failure term is smaller.
Result: randomized-svd-tail -/
theorem measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_isLeftUnitarilyInvariant
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    μ.real {ω | Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        Φ (Finsupp.single 0 1) * (t * k / d) *
          (frobNorm (A - truncatedSVD A k) + s * singularValues A k) ^ 2 <
        Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))} ≤
      Real.exp (-s ^ 2 / 2) + gaussianPinvFrobTail k d t := by
  have hg : Measurable fun P : Matrix m m ℝ => Φ.matrixNorm ((A - P * A)ᴴ * (A - P * A)) :=
    Φ.measurable_matrixNorm.comp ((Measurable.matrix_conjTranspose continuous_star.measurable
      (measurable_sub_mul A)).matrix_mul (measurable_sub_mul A))
  refine (measureReal_gt_eq_measureReal_gaussianMatrix_of_isLeftUnitarilyInvariant A hX hXr
    (f := fun Ω => Φ.matrixNorm ((A - rsvd A Ω)ᴴ * (A - rsvd A Ω))) hg (fun _ => rfl) _).trans_le ?_
  exact measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix Φ
    A HasLaw.id hd hs ht

end SymmetricGauge

/-! ### Nyström -/

/-- **Nyström with a rotation-invariant test matrix has the Gaussian law**: for positive
semidefinite $\mathbf{H}$ and a test matrix $\mathbf{X}$ with a left unitarily invariant law and
full column rank almost surely, $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$ has the law of
$\mathsf{nystrom}(\mathbf{H}, \mathbf{G})$ for a standard Gaussian $\mathbf{G}$. Nyström depends
on the test matrix only through the range projector $\mathbf{P}_{\mathbf{H}^{1/2}\mathbf{X}}$
(`Matrix.PosSemidef.nystrom_eq`), whose law is the Gaussian one
(`NLAlib.hasLaw_rangeProjector_mul_of_isLeftUnitarilyInvariant`). Every rotation-invariant
Nyström statement is a consequence.
[TroppYurtseverUdellCevher2017a, Proposition A.2 and proof of Theorem A.1];
[EpperlyWebber2026, Fact 6.1(b)]; there as "we may assume the test matrix is Gaussian", here as
a law statement for every full-rank rotation-invariant law.
Result: gaussian-haar-range-transfer -/
theorem _root_.Matrix.PosSemidef.hasLaw_nystrom_of_isLeftUnitarilyInvariant {H : Matrix n n ℝ}
    (hH : H.PosSemidef) (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) :
    HasLaw (fun ω => nystrom H (X ω)) ((gaussianMatrix n l).map (nystrom H)) μ := by
  obtain ⟨S, hS⟩ : ∃ S : Matrix n n ℝ,
      ∀ G : Matrix n l ℝ, nystrom H G = S * rangeProjector (S * G) * S :=
    ⟨_, hH.nystrom_eq⟩
  have hg : Measurable fun P : Matrix n n ℝ => S * P * S :=
    (measurable_const.matrix_mul measurable_id).matrix_mul measurable_const
  have hm : Measurable fun G : Matrix n l ℝ => rangeProjector (S * G) := by
    fun_prop
  have h := HasLaw.fun_comp (Y := fun P : Matrix n n ℝ => S * P * S) ⟨hg.aemeasurable, rfl⟩
    (hasLaw_rangeProjector_mul_of_isLeftUnitarilyInvariant S hX hXr)
  rw [Measure.map_map hg hm] at h
  have e1 : (fun ω => nystrom H (X ω)) = fun ω => S * rangeProjector (S * X ω) * S :=
    funext fun ω => hS (X ω)
  have e2 : nystrom H = (fun P : Matrix n n ℝ => S * P * S) ∘ fun G => rangeProjector (S * G) :=
    funext hS
  rw [e1, e2]
  exact h

namespace SymmetricGauge

/-- **The expected error of randomized Nyström, every unitarily invariant norm, rotation-invariant
test matrices**: for positive semidefinite $\mathbf{H}$, a test matrix $\mathbf{X}$ with a left
unitarily invariant law and full column rank almost surely (Gaussian, Haar, ...) and
$k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{\Phi} \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{\Phi} + \Phi(\mathbf{e}_0)\,
\frac{k}{\ell - k - 1}\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
the bound of the Gaussian test matrix (in this namespace,
`integral_matrixNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix`); the rotation-invariant Gram form
of the randomized SVD at a factor of $\mathbf{H}$.
[TroppWebber2023, Corollary 8.2 (NysSVD2)]; [TroppYurtseverUdellCevher2017a, Theorem A.1];
[EpperlyWebber2026, Theorem 3.1 and Fact 3.5]; there for Gaussian test matrices and Schatten
norms (TW), or the trace (TYUC, EW).
Result: randomized-nystrom-expected-error -/
theorem integral_matrixNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant (Φ : SymmetricGauge)
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, Φ.matrixNorm (H - nystrom H (X ω)) ∂μ ≤
      Φ.matrixNorm (H - truncatedSVD H k) +
        Φ (Finsupp.single 0 1) * ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
          nuclearNorm (H - truncatedSVD H k) := by
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  simp only [Matrix.star_eq_conjTranspose, conjTranspose_mul_self_sub_nystrom,
    Φ.matrixNorm_conjTranspose_mul_self_sub_truncatedSVD,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact Φ.integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_isLeftUnitarilyInvariant F hX
    hXr hk

end SymmetricGauge

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The expected trace error of truncated Nyström, rotation-invariant test matrices**: for
positive semidefinite $\mathbf{H}$, a test matrix $\mathbf{X}$ with a left unitarily invariant law
and full column rank almost surely, $k + 2 \le \ell$ and every choice of the truncation,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_*
\le \Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,:$$
the squared Frobenius error of the truncated randomized SVD of a factor
(`NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_isLeftUnitarilyInvariant`). A Haar
frame is an instance (`NLAlib.isLeftUnitarilyInvariant_haarFrame`, and
`NLAlib.ae_rank_mul_eq_min_of_hasLaw_haarFrame` at $\mathbf{A} = \mathbf{I}$ for $\ell \le n$).
Incomparable with the decay form with Epperly and Webber's factor,
`Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_add_of_isLeftUnitarilyInvariant_of_rank_le`,
which is better for rank close to $\ell$ or a decaying tail. Asymptotic form:
`NLAlib.exists_forall_integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant`.
[TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.1)]; there for Gaussian or orthonormal test
matrices, with $1 \le k$ and $\ell \le n$.
Result: randomized-nystrom-expected-error -/
theorem
_root_.Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * nuclearNorm (H - truncatedSVD H k) := by
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  simp only [Matrix.star_eq_conjTranspose,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_isLeftUnitarilyInvariant F hX hXr hk

/-- **$O(k/\varepsilon)$ samples suffice for truncated Nyström, rotation-invariant test
matrices**, trace: there are absolute constants $C, \varepsilon_0 > 0$ such that for positive
semidefinite $\mathbf{H}$, a test matrix $\mathbf{X}$ with a left unitarily invariant law and
full column rank almost surely, $0 < \varepsilon \le \varepsilon_0$ and $\ell \ge Ck/\varepsilon$,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_*
\le (1 + \varepsilon)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,.$$
The asymptotic form of
`Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant`;
the proof takes $C = 3$ and $\varepsilon_0 = 1$.
[TroppYurtseverUdellCevher2017a, §4, after Theorem 4.1]; there $\ell = (1 + 1/\varepsilon)k + 1$,
for Gaussian or orthonormal test matrices.
Asymptotic:
Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant
Result: randomized-nystrom-expected-error -/
theorem
    exists_forall_integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω n l : Type} [MeasurableSpace Ω] [Fintype n] [Fintype l]
      [DecidableEq n] (μ : Measure Ω) (ν : Measure (Matrix n l ℝ)) [IsProbabilityMeasure ν]
      [IsLeftUnitarilyInvariant ν] (H : Matrix n n ℝ) (X : Ω → Matrix n l ℝ) (k : ℕ) (ε : ℝ),
      H.PosSemidef → HasLaw X ν μ → (∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) →
      0 < ε → ε ≤ ε₀ → C * ((k : ℝ) / ε) ≤ Fintype.card l →
      ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
        (1 + ε) * nuclearNorm (H - truncatedSVD H k) := by
  refine ⟨3, 1, by norm_num, one_pos, ?_⟩
  intro Ω n l _ _ _ _ μ ν _ _ H X k ε hH hX hXr hε hε1 hl
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := hX.isProbabilityMeasure
    simp only [truncatedSVD_zero, sub_zero, integral_const, probReal_univ, one_smul]
    nlinarith [nuclearNorm_nonneg H]
  obtain ⟨hkl, hg⟩ := gaussianProjectionFactor_le_one_add_of_three_mul_div_le hk hε hε1 hl
  exact (hH.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant hX hXr
    hkl).trans (mul_le_mul_of_nonneg_right hg (nuclearNorm_nonneg _))

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The expected spectral error of truncated Nyström, rotation-invariant test matrices**
(Martinsson and Tropp's Theorem 14.1): for positive semidefinite $\mathbf{H}$, a test matrix
$\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely,
$k + 2 \le \ell$ and a measurable choice $\mathbf{Y}$ of best rank-$k$ approximations of
$\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$,
$$\mathbb{E}\|\mathbf{H} - \mathbf{Y}\|_2 \le \lambda_k(\mathbf{H}) + \frac{k}{\ell - k - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
eigenvalues indexed from $0$.
Direct form at `truncatedSVD`:
`Matrix.PosSemidef.integral_specNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant`.
[MartinssonTropp2020, Theorem 14.1]; [TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.2)]; there
for Gaussian (MT, TYUC) or orthonormal (TYUC) test matrices, with $1 \le k < \ell \le n$.
Result: randomized-nystrom-expected-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_isLeftUnitarilyInvariant
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ} (hk : k + 2 ≤ Fintype.card l)
    {Y : Ω → Matrix n n ℝ} (hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω))
    (hYm : AEStronglyMeasurable Y μ) :
    ∫ ω, specNorm (H - Y ω) ∂μ ≤
      singularValues H k +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k) := by
  have := hX.isProbabilityMeasure
  have h1 :=
    hH.integral_specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_isBestRankApprox_nystrom
      hX.aemeasurable hY hYm
  have h2 :=
    hH.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant hX hXr hk
  rw [gaussianProjectionFactor_def] at h2
  linarith

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The expected spectral error of truncated Nyström, rotation-invariant test matrices**
(Martinsson and Tropp's Theorem 14.1): for positive semidefinite $\mathbf{H}$, a test matrix
$\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely and
$k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_2 \le
\lambda_k(\mathbf{H}) + \frac{k}{\ell - k - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
eigenvalues indexed from $0$. The direct form of
`Matrix.PosSemidef.integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_isLeftUnitarilyInvariant`,
which covers any other measurable choice of the truncation.
[MartinssonTropp2020, Theorem 14.1]; [TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.2)]; there
for Gaussian (MT, TYUC) or orthonormal (TYUC) test matrices, with $1 \le k < \ell \le n$.
Result: randomized-nystrom-expected-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      singularValues H k +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k) :=
  hH.integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_isLeftUnitarilyInvariant hX hXr hk
    (fun _ => isBestRankApprox_truncatedSVD _ k)
    ((measurable_truncatedSVD k).comp_aemeasurable
      ((measurable_nystrom H).comp_aemeasurable hX.aemeasurable)).aestronglyMeasurable

namespace SymmetricGauge

/-- **The tail of randomized Nyström, every unitarily invariant norm, rotation-invariant test
matrices**: for positive semidefinite $\mathbf{H}$, a test matrix $\mathbf{X}$ with a left
unitarily invariant law and full column rank almost surely, $d = \ell - k + 1$, $s \ge 0$ and
$t > 0$,
$$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{\Phi} \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{tk}{d}\,
\bigl(\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*^{1/2} +
s\,\sigma_k(\mathbf{H})^{1/2}\bigr)^2$$
outside probability <!-- value gaussianPinvFrobTail k d t -->
$e^{-s^2/2} + 2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$, the tail of the Gaussian test
matrix (in this namespace,
`measureReal_matrixNorm_sub_nystrom_gt_le_of_hasLaw_gaussianMatrix`).
[TroppWebber2023, Corollary 8.2 (NysSVD1)]; there for Gaussian test matrices and Schatten norms,
with the noise term $(utk/d)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$ and the failure
probability $e^{-(u-2)/4} + \sqrt{\pi k}\,(t/e)^{-d/2}$, which follow from this bound at
$s = \sqrt{u} - 1$.
Result: randomized-nystrom-tail -/
theorem measureReal_matrixNorm_sub_nystrom_gt_le_of_isLeftUnitarilyInvariant
    (Φ : SymmetricGauge) {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    μ.real {ω | Φ.matrixNorm (H - truncatedSVD H k) + Φ (Finsupp.single 0 1) * (t * k / d) *
        (√(nuclearNorm (H - truncatedSVD H k)) + s * √(singularValues H k)) ^ 2 <
        Φ.matrixNorm (H - nystrom H (X ω))} ≤
      Real.exp (-s ^ 2 / 2) + gaussianPinvFrobTail k d t := by
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  simp only [Matrix.star_eq_conjTranspose, conjTranspose_mul_self_sub_nystrom,
    Φ.matrixNorm_conjTranspose_mul_self_sub_truncatedSVD,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD, singularValues_conjTranspose_mul_self]
  rw [Real.sqrt_sq (frobNorm_nonneg _), Real.sqrt_sq (singularValues_nonneg _ _)]
  exact
    Φ.measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_isLeftUnitarilyInvariant
      F hX hXr hd hs ht

end SymmetricGauge

/-- A rotation-invariant sketch at least as wide as the rank makes Nyström exact: for
positive semidefinite $\mathbf{H}$ with $\operatorname{rank}\mathbf{H} \le \ell$ and a test matrix
$\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely,
$\mathsf{nystrom}(\mathbf{H}, \mathbf{X}) = \mathbf{H}$ almost surely. -/
theorem _root_.Matrix.PosSemidef.ae_nystrom_eq_self_of_isLeftUnitarilyInvariant
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) (hHl : H.rank ≤ Fintype.card l) :
    ∀ᵐ ω ∂μ, nystrom H (X ω) = H := by
  filter_upwards [ae_rank_mul_eq_min_of_isLeftUnitarilyInvariant H hX hXr] with ω hω
  exact hH.nystrom_eq_self_of_rank_eq (hω.trans (min_eq_left hHl))

/-! ### Epperly and Webber's sharp bounds

The rank-parameter forms. The reduction to a diagonal matrix, the cyclic average of its tail and
the transfer to the Gaussian are private steps of the Nyström bound; the randomized SVD bound is
its Gram form. -/

/-- The trace error of Nyström is monotone in the positive semidefinite matrix. -/
private theorem nuclearNorm_sub_nystrom_le_of_le {ι : Type*} [Fintype ι] {D D' : Matrix ι ι ℝ}
    (hD : D.PosSemidef) (h : D ≤ D') (G : Matrix ι l ℝ) :
    nuclearNorm (D - nystrom D G) ≤ nuclearNorm (D' - nystrom D' G) := by
  have hD' : D'.PosSemidef := by simpa using hD.add (Matrix.le_iff.mp h)
  rw [(Matrix.le_iff.mp (hD.nystrom_le G)).nuclearNorm_eq_re_trace,
    (Matrix.le_iff.mp (hD'.nystrom_le G)).nuclearNorm_eq_re_trace]
  exact re_trace_le_re_trace_of_le (hD.sub_nystrom_le_sub_nystrom h G)

/-- Relabelling the rows of a standard Gaussian test matrix leaves the expected trace error of
Nyström unchanged, after relabelling the matrix. -/
private theorem nuclearNorm_submatrix_sub_nystrom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) (D : Matrix ι ι ℝ) (G : Matrix ι l ℝ) :
    nuclearNorm (D.submatrix e e - nystrom (D.submatrix e e) G) =
      nuclearNorm (D - nystrom D (selectionMatrix e * G)) := by
  have h := nystrom_conjTranspose_mul_mul (selectionMatrix e : Matrix ι ι ℝ) D G
  rw [conjTranspose_selectionMatrix_mul_mul_selectionMatrix,
    conjTranspose_selectionMatrix_mul_mul_selectionMatrix] at h
  rw [h]
  exact nuclearNorm_submatrix_equiv (D - nystrom D (selectionMatrix e * G)) e e

/-- The average of the cyclic shifts of the tail block in
`integral_nuclearNorm_diagonal_sub_nystrom_le`:
the mean over $k$ of $\operatorname{diag}(a, \boldsymbol{\sigma}_2)$ shifted by $k$ is
$\operatorname{diag}(a\mathbf{I}, \bar\sigma_2\mathbf{I})$, $\bar\sigma_2$ the mean of
$\boldsymbol{\sigma}_2$. -/
private theorem sum_smul_submatrix_sumCongr_addRight {s : Type*} [DecidableEq s] {d : ℕ}
    [NeZero d] (a : ℝ) (σ₂ : Fin d → ℝ) :
    ∑ k : Fin d, (1 / d : ℝ) • (Matrix.diagonal (Sum.elim (fun _ : s => a) σ₂)).submatrix
        (Equiv.sumCongr (Equiv.refl s) (Equiv.addRight k))
        (Equiv.sumCongr (Equiv.refl s) (Equiv.addRight k)) =
      Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0
        (((∑ j, σ₂ j) / d) • (1 : Matrix (Fin d) (Fin d) ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set e : Fin d → (s ⊕ Fin d) ≃ (s ⊕ Fin d) := fun k =>
    Equiv.sumCongr (Equiv.refl s) (Equiv.addRight k)
  rw [Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal, Matrix.fromBlocks_diagonal]
  have e1 : ∀ k, (Matrix.diagonal (Sum.elim (fun _ : s => a) σ₂)).submatrix
      (Equiv.sumCongr (Equiv.refl s) (Equiv.addRight k)) (Equiv.sumCongr (Equiv.refl s)
        (Equiv.addRight k)) = Matrix.diagonal (Sum.elim (fun _ : s => a) σ₂ ∘ e k) := fun k =>
    Matrix.submatrix_diagonal_equiv _ _
  simp only [e1]
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with hij
  · subst hij
    cases i with
    | inl i =>
      simp only [Function.comp, e, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply,
        Sum.elim_inl, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    | inr j =>
      simp only [Function.comp, e, Equiv.sumCongr_apply, Sum.map_inr, Equiv.coe_addRight,
        Sum.elim_inr, ← Finset.mul_sum]
      rw [show (∑ k : Fin d, σ₂ (j + k)) = ∑ k, σ₂ k from
        Equiv.sum_comp (Equiv.addLeft j) σ₂]
      ring
  · simp

/-- **The diagonal case of the sharp Nyström bound** (Epperly and Webber's §6.3 at a fixed
eigenbasis): for a standard Gaussian test matrix on $(s \oplus \mathrm{Fin}\,d) \times l$, the
expected trace error of Nyström for
$\operatorname{diag}(\boldsymbol{\sigma}_1, \boldsymbol{\sigma}_2)$ with
$\boldsymbol{\sigma}_1 \le a$ is at most the factor times $\sum_j \sigma_{2,j}$. -/
private theorem integral_nuclearNorm_diagonal_sub_nystrom_le {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ' : Measure Ω'} {s : Type*} [Fintype s] [DecidableEq s] {d : ℕ} [NeZero d]
    {G : Ω' → Matrix (s ⊕ Fin d) l ℝ} (hG : HasLaw G (gaussianMatrix (s ⊕ Fin d) l) μ')
    {σ₁ : s → ℝ} {σ₂ : Fin d → ℝ} {a : ℝ} (h₁ : ∀ i, 0 ≤ σ₁ i) (ha : ∀ i, σ₁ i ≤ a)
    (ha0 : 0 ≤ a) (h₂ : ∀ j, 0 ≤ σ₂ j) (hsl : Fintype.card s + 2 ≤ Fintype.card l)
    (hlr : Fintype.card l ≤ Fintype.card s + d) :
    ∫ ω, nuclearNorm (Matrix.diagonal (Sum.elim σ₁ σ₂) -
        nystrom (Matrix.diagonal (Sum.elim σ₁ σ₂)) (G ω)) ∂μ' ≤
      rotationInvariantFactor (Fintype.card s + d) (Fintype.card l) (Fintype.card s) *
        ∑ j, σ₂ j := by
  classical
  have := hG.isProbabilityMeasure_iff.2 inferInstance
  set Da := Matrix.diagonal (Sum.elim (fun _ : s => a) σ₂)
  have hDa : Da.PosSemidef := Matrix.PosSemidef.diagonal fun i => by cases i <;> simp [ha0, h₂]
  have hD : (Matrix.diagonal (Sum.elim σ₁ σ₂)).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i => by cases i <;> simp [h₁, h₂]
  have hle : Matrix.diagonal (Sum.elim σ₁ σ₂) ≤ Da := by
    rw [Matrix.le_iff, Matrix.diagonal_sub]
    refine Matrix.PosSemidef.diagonal fun i => ?_
    cases i <;> simp [ha]
  -- the cyclic shifts of the tail block
  set e : Fin d → (s ⊕ Fin d) ≃ (s ⊕ Fin d) := fun k =>
    Equiv.sumCongr (Equiv.refl s) (Equiv.addRight k)
  set Dk : Fin d → Matrix (s ⊕ Fin d) (s ⊕ Fin d) ℝ := fun k => Da.submatrix (e k) (e k)
  have hDk : ∀ k, (Dk k).PosSemidef := fun k => hDa.submatrix _
  have hf : Measurable fun Y : Matrix (s ⊕ Fin d) l ℝ => nuclearNorm (Da - nystrom Da Y) :=
    continuous_nuclearNorm.measurable.comp (measurable_const.sub (measurable_nystrom Da))
  have hshift : ∀ k, ∫ ω, nuclearNorm (Dk k - nystrom (Dk k) (G ω)) ∂μ' =
      ∫ ω, nuclearNorm (Da - nystrom Da (G ω)) ∂μ' := by
    intro k
    have hP : HasOrthonormalCols (selectionMatrix (e k) : Matrix (s ⊕ Fin d) (s ⊕ Fin d) ℝ)ᴴ :=
      (hasOrthonormalCols_selectionMatrix (e k).injective).conjTranspose_of_card_eq rfl
    have hPG := hasLaw_const_mul_of_hasLaw_gaussianMatrix hG hP
    simp only [Dk, nuclearNorm_submatrix_sub_nystrom]
    exact (hPG.integral_comp hf.aestronglyMeasurable).trans
      (hG.integral_comp hf.aestronglyMeasurable).symm
  -- the average of the shifts
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set w : ℝ := 1 / d
  have hw : 0 ≤ w := by positivity
  set b₀ : ℝ := (∑ j, σ₂ j) / d
  have hb₀ : 0 ≤ b₀ := div_nonneg (Finset.sum_nonneg fun j _ => h₂ j) hd0.le
  have hbar : ∑ k, w • Dk k = Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0
      (b₀ • (1 : Matrix (Fin d) (Fin d) ℝ)) := sum_smul_submatrix_sumCongr_addRight a σ₂
  have hDbar : (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0
      (b₀ • (1 : Matrix (Fin d) (Fin d) ℝ))).PosSemidef := by
    rw [← hbar]
    exact Matrix.posSemidef_sum _ fun k _ => (hDk k).smul hw
  have hpt : ∀ ω, w * ∑ k, nuclearNorm (Dk k - nystrom (Dk k) (G ω)) ≤
      nuclearNorm (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0
        (b₀ • (1 : Matrix (Fin d) (Fin d) ℝ)) - nystrom (Matrix.fromBlocks (a • (1 : Matrix s s ℝ))
          0 0 (b₀ • (1 : Matrix (Fin d) (Fin d) ℝ))) (G ω)) := by
    intro ω
    have h := sum_smul_sub_nystrom_le Finset.univ (fun k _ => hDk k) (fun k _ => hw) (G ω)
    rw [hbar] at h
    rw [(Matrix.le_iff.mp (hDbar.nystrom_le (G ω))).nuclearNorm_eq_re_trace]
    refine le_of_eq_of_le ?_ (re_trace_le_re_trace_of_le h)
    rw [Matrix.trace_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_smul, (Matrix.le_iff.mp ((hDk k).nystrom_le (G ω))).nuclearNorm_eq_re_trace,
      RCLike.re_to_real, RCLike.re_to_real, smul_eq_mul]
  -- integrate
  have hint : ∀ k, Integrable (fun ω => nuclearNorm (Dk k - nystrom (Dk k) (G ω))) μ' :=
    fun k => (hDk k).integrable_nuclearNorm_sub_nystrom hG.aemeasurable
  have hYr : ∀ᵐ ω ∂μ', Function.Injective (G ω).mulVec := by
    filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hG] with ω hω
    rw [mulVec_injective_iff_rank_eq, hω, Fintype.card_sum, Fintype.card_fin]
    exact min_eq_right hlr
  have hLa := integral_nuclearNorm_fromBlocks_sub_nystrom_le_of_isLeftUnitarilyInvariant hG hYr
    hsl ha0 hb₀
  rw [Fintype.card_fin] at hLa
  calc ∫ ω, nuclearNorm (Matrix.diagonal (Sum.elim σ₁ σ₂) -
        nystrom (Matrix.diagonal (Sum.elim σ₁ σ₂)) (G ω)) ∂μ'
      ≤ ∫ ω, nuclearNorm (Da - nystrom Da (G ω)) ∂μ' :=
        integral_mono (hD.integrable_nuclearNorm_sub_nystrom hG.aemeasurable)
          (hDa.integrable_nuclearNorm_sub_nystrom hG.aemeasurable)
          fun ω => nuclearNorm_sub_nystrom_le_of_le hD hle (G ω)
    _ = ∫ ω, w * ∑ k, nuclearNorm (Dk k - nystrom (Dk k) (G ω)) ∂μ' := by
        rw [integral_const_mul, integral_finsetSum _ fun k _ => hint k]
        simp only [hshift, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, w]
        field_simp
    _ ≤ _ := integral_mono ((integrable_finsetSum _ fun k _ => hint k).const_mul w)
        (hDbar.integrable_nuclearNorm_sub_nystrom hG.aemeasurable) hpt
    _ ≤ _ := hLa
    _ = _ := by
        simp only [b₀]
        field_simp

omit [DecidableEq n] in
/-- The sharp Nyström bound for a standard Gaussian test matrix when the rank parameter is at most
the dimension. -/
private theorem integral_nuclearNorm_sub_nystrom_le_of_rank_le_of_le_card {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} {G : Ω' → Matrix n l ℝ}
    (hG : HasLaw G (gaussianMatrix n l) μ') {H : Matrix n n ℝ} (hH : H.PosSemidef) {r q : ℕ}
    (hr : H.rank ≤ r) (hrn : r ≤ Fintype.card n) (hlr : Fintype.card l ≤ r)
    (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - nystrom H (G ω)) ∂μ' ≤
      rotationInvariantFactor r (Fintype.card l) q * nuclearNorm (H - truncatedSVD H q) := by
  classical
  obtain ⟨U, hU, hHU⟩ := hH.isHermitian.exists_eq_mul_diagonal_mul_conjTranspose
  set d := r - q
  have hd : q + d = r := by omega
  have : NeZero d := ⟨by omega⟩
  set ι : Fin q ⊕ Fin d → Fin (Fintype.card n) :=
    Sum.elim (fun i => ⟨i, by omega⟩) fun j => ⟨q + j, by omega⟩
  have hι : Function.Injective ι := by
    rintro (x | x) (y | y) h <;> simp only [ι, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h <;>
      first | (congr 1; exact Fin.ext (by omega)) | (exfalso; omega)
  set V := U.submatrix (Equiv.refl n) ι
  have hV : HasOrthonormalCols V := hU.submatrix (Equiv.refl n) hι
  set w : Fin q ⊕ Fin d → ℝ := fun c => eigenvalue H (ι c)
  have hzero : ∀ j : Fin (Fintype.card n), j ∉ Finset.univ.image ι → eigenvalue H j = 0 := by
    intro j hj
    have hjr : r ≤ (j : ℕ) := by
      by_contra hjr
      refine hj (Finset.mem_image.mpr ?_)
      by_cases hjq : (j : ℕ) < q
      · exact ⟨Sum.inl ⟨j, hjq⟩, Finset.mem_univ _, Fin.ext rfl⟩
      · exact ⟨Sum.inr ⟨j - q, by omega⟩, Finset.mem_univ _, Fin.ext (by simp [ι]; omega)⟩
    rw [← hH.singularValues_eq_eigenvalue]
    exact (singularValues_eq_zero_iff H).mpr (hr.trans hjr)
  have hHV : H = V * Matrix.diagonal w * Vᴴ := by
    conv_lhs => rw [hHU]
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, star_trivial,
      V, Matrix.submatrix_apply, Equiv.refl_apply, w, RCLike.ofReal_real_eq_id, id]
    rw [← Finset.sum_image (f := fun j => U a j * eigenvalue H j * U b j) (fun x _ y _ h => hι h)]
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
    rw [hzero j hj, mul_zero, zero_mul]
  -- compress to the leading `r` eigenvectors
  have hpt : ∀ ω, nuclearNorm (H - nystrom H (G ω)) =
      nuclearNorm (Matrix.diagonal w - nystrom (Matrix.diagonal w) (Vᴴ * G ω)) := by
    intro ω
    have h := nystrom_conjTranspose_mul_mul Vᴴ (Matrix.diagonal w) (G ω)
    rw [Matrix.conjTranspose_conjTranspose] at h
    rw [hHV, h, ← Matrix.sub_mul, ← Matrix.mul_sub, hV.nuclearNorm_mul_conjTranspose_right,
      hV.nuclearNorm_mul_left]
  have hVG : HasLaw (fun ω => Vᴴ * G ω) (gaussianMatrix (Fin q ⊕ Fin d) l) μ' :=
    hasLaw_const_mul_of_hasLaw_gaussianMatrix hG (by rwa [Matrix.conjTranspose_conjTranspose])
  have hw : w = Sum.elim (fun i : Fin q => eigenvalue H i)
      fun j : Fin d => eigenvalue H (q + j) := by
    funext c
    cases c <;> rfl
  have hcore := integral_nuclearNorm_diagonal_sub_nystrom_le hVG
    (σ₁ := fun i : Fin q => eigenvalue H i) (σ₂ := fun j : Fin d => eigenvalue H (q + j))
    (a := eigenvalue H 0) (fun i => hH.eigenvalue_nonneg _)
    (fun i => hH.eigenvalue_antitone (Nat.zero_le _)) (hH.eigenvalue_nonneg _)
    (fun j => hH.eigenvalue_nonneg _) (by rw [Fintype.card_fin]; exact hq)
    (by rw [Fintype.card_fin]; omega)
  rw [Fintype.card_fin, hd, ← hw] at hcore
  have htail : ∑ j : Fin d, eigenvalue H (q + j) = nuclearNorm (H - truncatedSVD H q) := by
    have hrank : (H - truncatedSVD H q).rank ≤ d := by
      rw [← singularValues_eq_zero_iff, singularValues_sub_truncatedSVD, hd]
      exact (singularValues_eq_zero_iff H).mpr hr
    rw [nuclearNorm_eq_sum_range _ hrank, Fin.sum_univ_eq_sum_range (fun j => eigenvalue H (q + j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [singularValues_sub_truncatedSVD, hH.singularValues_eq_eigenvalue]
  rw [← htail]
  simp only [hpt]
  exact hcore

omit [DecidableEq n] [IsLeftUnitarilyInvariant ν] in
/-- A test matrix with full column rank almost surely is no wider than tall. -/
private theorem card_le_of_ae_injective (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) : Fintype.card l ≤ Fintype.card n := by
  have := hX.isProbabilityMeasure_iff.2 inferInstance
  obtain ⟨ω, hω⟩ := hXr.exists
  rw [← mulVec_injective_iff_rank_eq.mp hω]
  exact Matrix.rank_le_card_height _

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The sharp expected trace error of randomized Nyström, rotation-invariant test matrices**:
for positive semidefinite $\mathbf{H}$ of rank at most $r$, a test matrix $\mathbf{X}$ with a left
unitarily invariant law and full column rank almost surely (Gaussian, Haar, ...),
$\ell \le r$ and $q + 2 \le \ell$, <!-- value rotationInvariantFactor r \ell q -->
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_* \le
\frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_*\,.$$
At $r = \operatorname{rank}\mathbf{H}$ the supremum
of the ratio over rank-$r$ matrices equals the factor ([EpperlyWebber2026, Theorem 3.6(b)]); at
$r = n$ the bound needs no knowledge of the rank. The factor is at most HMT's
(`NLAlib.rotationInvariantFactor_le_gaussianProjectionFactor`), so this sharpens
`Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant`, its
instance $r = n$. The proof passes to a Gaussian test matrix, compresses $\mathbf{H}$ to its
leading $r$ eigenvectors, raises the top $q$ eigenvalues to $\lambda_0(\mathbf{H})$ (monotonicity
of the Schur complement), averages the tail over its cyclic shifts (concavity) and ends at the
two-eigenvalue instance
`NLAlib.integral_nuclearNorm_fromBlocks_sub_nystrom_le_of_isLeftUnitarilyInvariant`.
[EpperlyWebber2026, Theorem 3.6(a)]; there over $\mathbb{R}$ and $\mathbb{C}$ with
$r = \operatorname{rank}\mathbf{H} \ge \ell$ and a minimum over $q$; here over $\mathbb{R}$, any
$r \ge \max(\operatorname{rank}\mathbf{H}, \ell)$, at each $q$.
Result: randomized-nystrom-expected-error -/
theorem
    _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant_of_rank_le
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {r q : ℕ} (hr : H.rank ≤ r)
    (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ ≤
      rotationInvariantFactor r (Fintype.card l) q * nuclearNorm (H - truncatedSVD H q) := by
  have hln := card_le_of_ae_injective hX hXr
  obtain ⟨S, hS⟩ : ∃ S : Matrix n n ℝ,
      ∀ G : Matrix n l ℝ, nystrom H G = S * rangeProjector (S * G) * S :=
    ⟨_, hH.nystrom_eq⟩
  have hg : Measurable fun P : Matrix n n ℝ => nuclearNorm (H - S * P * S) :=
    continuous_nuclearNorm.measurable.comp
      (measurable_const.sub
        ((measurable_const.matrix_mul measurable_id).matrix_mul measurable_const))
  rw [integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant S hX hXr
    (f := fun Y => nuclearNorm (H - nystrom H Y)) hg fun Y => by rw [hS]]
  by_cases hrn : r ≤ Fintype.card n
  · exact integral_nuclearNorm_sub_nystrom_le_of_rank_le_of_le_card HasLaw.id hH hr hrn hlr hq
  · refine (integral_nuclearNorm_sub_nystrom_le_of_rank_le_of_le_card HasLaw.id hH
      (Matrix.rank_le_card_height H) le_rfl hln hq).trans ?_
    exact mul_le_mul_of_nonneg_right
      (rotationInvariantFactor_le_rotationInvariantFactor hq hln (by omega)) (nuclearNorm_nonneg _)

/-- **The sharp expected error of the randomized SVD, rotation-invariant test matrices**: for
$\mathbf{A}$ of rank at most $r$, a test matrix $\mathbf{X}$ with a left unitarily invariant law
and full column rank almost surely, $\ell \le r$ and
$q + 2 \le \ell$, <!-- value rotationInvariantFactor r \ell q -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 \le
\frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2\,;$$
the factor is at most HMT's, so this sharpens
`NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant`, its instance $r = n$. The
Nyström bound at $\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$, by the Gram correspondence
(`NLAlib.nuclearNorm_conjTranspose_mul_self_sub_nystrom`).
[EpperlyWebber2026, Theorem 3.2]; there with $r = \operatorname{rank}\mathbf{A} \ge \ell$ and a
minimum over $q$, over $\mathbb{R}$ and $\mathbb{C}$.
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant_of_rank_le
    (A : Matrix m n ℝ) (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)
    {r q : ℕ} (hr : A.rank ≤ r) (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      rotationInvariantFactor r (Fintype.card l) q * frobNorm (A - truncatedSVD A q) ^ 2 := by
  have h :=
    Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant_of_rank_le
      (Matrix.posSemidef_conjTranspose_mul_self A) hX hXr
      (by rwa [Matrix.rank_conjTranspose_mul_self]) hlr hq
  simpa only [nuclearNorm_conjTranspose_mul_self_sub_nystrom,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD] using h

omit [DecidableEq n] in
/-- **The sharp expected trace error of randomized Nyström, Gaussian test matrices**: for positive
semidefinite $\mathbf{H}$ of rank at most $r$, a standard Gaussian $n \times \ell$ test matrix
$\mathbf{X}$, $\ell \le r$ and $q + 2 \le \ell$, <!-- value rotationInvariantFactor r \ell q -->
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_* \le
\frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_*\,,$$
for every $\ell$ (for $\ell > n$ Nyström is exact almost surely). The Gaussian instance of
`Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant_of_rank_le`, and
the sharper form of `Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix`
(HMT's factor).
[EpperlyWebber2026, Theorem 3.6(a)]; there with $r = \operatorname{rank}\mathbf{H} \ge \ell$ and a
minimum over $q$.
Result: randomized-nystrom-expected-error -/
theorem
    _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix_of_rank_le
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ}
    (hr : H.rank ≤ r) (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ ≤
      rotationInvariantFactor r (Fintype.card l) q * nuclearNorm (H - truncatedSVD H q) := by
  classical
  have := hX.isProbabilityMeasure
  by_cases hln : Fintype.card l ≤ Fintype.card n
  · refine hH.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant_of_rank_le hX ?_ hr
      hlr hq
    filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hX] with ω hω
    rw [mulVec_injective_iff_rank_eq, hω, min_eq_right hln]
  · have h0 : ∀ᵐ ω ∂μ, nystrom H (X ω) = H := by
      filter_upwards [ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix H hX] with ω hω
      exact hH.nystrom_eq_self_of_rank_eq
        (hω.trans (min_eq_left ((Matrix.rank_le_card_height H).trans (by omega))))
    rw [integral_congr_ae (h0.mono fun ω h => by rw [h, sub_self])]
    simp only [nuclearNorm_zero, integral_zero]
    exact mul_nonneg (rotationInvariantFactor_nonneg hq hlr) (nuclearNorm_nonneg _)

omit [DecidableEq n] in
/-- **The sharp expected error of the randomized SVD, Gaussian test matrices**: for $\mathbf{A}$
of rank at most $r$, a standard Gaussian $n \times \ell$ test matrix $\mathbf{X}$, $\ell \le r$
and $q + 2 \le \ell$, <!-- value rotationInvariantFactor r \ell q -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 \le
\frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2\,,$$
for every $\ell$. The sharper form of
`NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix` (HMT's factor); the Nyström
bound at $\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$ by the Gram correspondence.
[EpperlyWebber2026, Theorem 3.2]; [HalkoMartinssonTropp2011, Theorem 10.5]; there (EW) with
$r = \operatorname{rank}\mathbf{A} \ge \ell$ and a minimum over $q$, (HMT) with HMT's factor.
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_of_rank_le
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {r q : ℕ} (hr : A.rank ≤ r)
    (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      rotationInvariantFactor r (Fintype.card l) q * frobNorm (A - truncatedSVD A q) ^ 2 := by
  classical
  have h :=
    Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix_of_rank_le
      (Matrix.posSemidef_conjTranspose_mul_self A) hX
      (by rwa [Matrix.rank_conjTranspose_mul_self]) hlr hq
  simpa only [nuclearNorm_conjTranspose_mul_self_sub_nystrom,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD] using h

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Truncated Nyström exploits spectral decay, with Epperly and Webber's factor**: for positive
semidefinite $\mathbf{H}$ of rank at most $r$, a test matrix $\mathbf{X}$ with a left unitarily
invariant law and full column rank almost surely, any target rank $k$, a comparison rank $q$ with
$q + 2 \le \ell \le r$ and every choice of the
truncation, <!-- value rotationInvariantFactor r \ell q -->
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_* \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_* + \frac{r - \ell}{r - q}
\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_*\,.$$
Better than
`Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_add_of_hasLaw_gaussianMatrix`'s
$1 + q/(\ell-q-1)$ by the factor $(r-\ell)/(r-q)$. Incomparable with
`Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant` at
$q = k$ as well: better iff $(r-\ell)(\ell-1) < k(r-k)$, that is for rank close to $\ell$ (at
$r = \ell$ it gives the best rank-$k$ error with constant one); for $q > k$ better when the tail
decays. From the constant-one truncation lemma
`NLAlib.SymmetricGauge.matrixNorm_sub_truncatedSVD_nystrom_le` and
`Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant_of_rank_le`.
[TroppYurtseverUdellCevher2017a, Theorem 4.2 (4.3)]; [EpperlyWebber2026, Theorem 3.6(a)]; there
(TYUC) with the constant $2$ and HMT's factor.
Result: randomized-nystrom-expected-error -/
theorem
    _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_add_of_isLeftUnitarilyInvariant_of_rank_le
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) (k : ℕ) {r q : ℕ} (hr : H.rank ≤ r)
    (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      nuclearNorm (H - truncatedSVD H k) +
        rotationInvariantFactor r (Fintype.card l) q * nuclearNorm (H - truncatedSVD H q) := by
  have := hX.isProbabilityMeasure_iff.2 inferInstance
  have hpt : ∀ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ≤
      nuclearNorm (H - truncatedSVD H k) + nuclearNorm (H - nystrom H (X ω)) := fun ω => by
    simpa only [lpGauge_one_matrixNorm] using
      (lpGauge 1).matrixNorm_sub_truncatedSVD_nystrom_le hH (X ω) k
  have hN := hH.integrable_nuclearNorm_sub_nystrom hX.aemeasurable
  have hI : Integrable (fun ω => nuclearNorm (H - truncatedSVD H k) +
      nuclearNorm (H - nystrom H (X ω))) μ := (integrable_const _).add hN
  refine (integral_mono (hH.integrable_nuclearNorm_sub_truncatedSVD_nystrom hX.aemeasurable k)
    hI hpt).trans ?_
  rw [integral_add (integrable_const _) hN, integral_const, probReal_univ, one_smul]
  exact add_le_add le_rfl
    (hH.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant_of_rank_le hX hXr hr hlr hq)

/-- **The expected error of the randomized SVD, Frobenius norm, rotation-invariant test
matrices**: for a test matrix $\mathbf{X}$ with a left unitarily invariant law and full column
rank almost surely and $k + 2 \le \ell$, <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,,$$
with HMT's factor. The instance $r = n$ of
`NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant_of_rank_le`, with Epperly and
Webber's factor bounded by HMT's; kept for the form consumers cite. Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant`.
[EpperlyWebber2026, Theorem 3.1]; [HalkoMartinssonTropp2011, Theorem 10.5]; there (EW) over
$\mathbb{R}$ and $\mathbb{C}$ with a minimum over the number $q$ of directions, here over
$\mathbb{R}$ at $q = k$. [EpperlyWebber2026, Theorem 3.1] and [HalkoMartinssonTropp2011,
Theorem 10.5] print the first-moment form <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}} \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)^{1/2}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}\,,$$
which follows from this bound by Jensen's inequality
(`ProbabilityTheory.integral_le_sqrt_integral_sq`).
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant (A : Matrix m n ℝ)
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have hln := card_le_of_ae_injective hX hXr
  refine (integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant_of_rank_le A hX hXr
    (Matrix.rank_le_card_width A) hln hk).trans ?_
  exact mul_le_mul_of_nonneg_right (rotationInvariantFactor_le_gaussianProjectionFactor hk hln)
    (sq_nonneg _)

/-- **$O(k/\varepsilon)$ samples suffice for the randomized SVD, rotation-invariant test
matrices**, Frobenius norm: there are absolute constants $C, \varepsilon_0 > 0$ such that for a
test matrix $\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely,
$k \ge 1$, $0 < \varepsilon \le \varepsilon_0$ and $\ell \ge Ck/\varepsilon$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
The asymptotic form of `NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant`; the
proof takes $C = 3$ and $\varepsilon_0 = 1$.
[EpperlyWebber2026, §4.2]; there as the count $2\ell \ge (2/\varepsilon + 2)k$ of products.
Asymptotic: NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant
Result: randomized-svd-expected-error -/
theorem exists_forall_integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [DecidableEq n] (μ : Measure Ω) (ν : Measure (Matrix n l ℝ))
      [IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν] (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (k : ℕ) (ε : ℝ),
      HasLaw X ν μ → (∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) → 0 < k → 0 < ε → ε ≤ ε₀ →
      C * ((k : ℝ) / ε) ≤ Fintype.card l →
      ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤ (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  refine ⟨3, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ _ μ ν _ _ A X k ε hX hXr hk hε hε1 hl
  obtain ⟨hkl, hg⟩ := gaussianProjectionFactor_le_one_add_of_three_mul_div_le hk hε hε1 hl
  exact (integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant A hX hXr hkl).trans
    (mul_le_mul_of_nonneg_right hg (sq_nonneg _))

/-- **The expected trace error of randomized Nyström, rotation-invariant test matrices**: for
positive semidefinite $\mathbf{H}$, a test matrix $\mathbf{X}$ with a left unitarily invariant law
and full column rank almost surely and
$k + 2 \le \ell$, <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_* \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
with HMT's factor. The instance $r = n$ of
`Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant_of_rank_le`,
with Epperly and Webber's factor bounded by HMT's. A Haar frame (`NLAlib.haarFrame`) is an
instance: its law is left unitarily invariant (`NLAlib.isLeftUnitarilyInvariant_haarFrame`), and
for $\ell \le n$ it has full column rank almost surely
(`NLAlib.ae_rank_mul_eq_min_of_hasLaw_haarFrame` at $\mathbf{A} = \mathbf{I}$). Asymptotic form:
`NLAlib.exists_forall_integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant`.
[EpperlyWebber2026, Theorem 3.1 and Fact 3.5]; [TroppYurtseverUdellCevher2017a, Theorem A.1];
there with a minimum over the comparison rank, for orthonormal test matrices (TYUC) or
rotation-invariant ones (EW, the Nyström twin of their Theorem 3.1); here at one rank.
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * nuclearNorm (H - truncatedSVD H k) := by
  have hln := card_le_of_ae_injective hX hXr
  refine (hH.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant_of_rank_le hX hXr
    (Matrix.rank_le_card_width H) hln hk).trans ?_
  exact mul_le_mul_of_nonneg_right (rotationInvariantFactor_le_gaussianProjectionFactor hk hln)
    (nuclearNorm_nonneg _)

/-- **$O(k/\varepsilon)$ samples suffice for randomized Nyström, rotation-invariant test
matrices**, trace: there are absolute constants $C, \varepsilon_0 > 0$ such that for positive
semidefinite $\mathbf{H}$, a test matrix $\mathbf{X}$ with a left unitarily invariant law and
full column rank almost surely, $k \ge 1$, $0 < \varepsilon \le \varepsilon_0$ and
$\ell \ge Ck/\varepsilon$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_* \le
(1 + \varepsilon)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,.$$
The asymptotic form of
`Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant`; the proof
takes $C = 3$ and $\varepsilon_0 = 1$.
[EpperlyWebber2026, §4.2 and Fact 3.5]; [TroppYurtseverUdellCevher2017a, §4, after Theorem 4.1];
there (EW) for the randomized SVD, the Gram twin, and (TYUC) for the truncated output of Gaussian
or orthonormal test matrices, whose error is the larger.
Asymptotic: Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant
Result: randomized-nystrom-expected-error -/
theorem exists_forall_integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω n l : Type} [MeasurableSpace Ω] [Fintype n] [Fintype l]
      [DecidableEq n] (μ : Measure Ω) (ν : Measure (Matrix n l ℝ)) [IsProbabilityMeasure ν]
      [IsLeftUnitarilyInvariant ν] (H : Matrix n n ℝ) (X : Ω → Matrix n l ℝ) (k : ℕ) (ε : ℝ),
      H.PosSemidef → HasLaw X ν μ → (∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) →
      0 < k → 0 < ε → ε ≤ ε₀ → C * ((k : ℝ) / ε) ≤ Fintype.card l →
      ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ ≤
        (1 + ε) * nuclearNorm (H - truncatedSVD H k) := by
  refine ⟨3, 1, by norm_num, one_pos, ?_⟩
  intro Ω n l _ _ _ _ μ ν _ _ H X k ε hH hX hXr hk hε hε1 hl
  obtain ⟨hkl, hg⟩ := gaussianProjectionFactor_le_one_add_of_three_mul_div_le hk hε hε1 hl
  exact (hH.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant hX hXr hkl).trans
    (mul_le_mul_of_nonneg_right hg (nuclearNorm_nonneg _))

end NLAlib
