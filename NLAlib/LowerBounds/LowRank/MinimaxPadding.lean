/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Matrix.PosDef
public import NLAlib.LowerBounds.LowRank.Minimax
public import NLAlib.Matrix.Spectral.LowRankPadding

/-!
# Fixed-batch low-rank lower bounds in larger dimensions

An algorithm on a larger ambient space can be simulated on a coordinate subspace: restrict its
queries, pad oracle responses with zeros and compress its returned factors. The simulation
preserves query rounds, seed measurability and pass labels. A successful approximation to a
zero-padded PSD input compresses to a successful approximation on the original coordinates.
Consequently the fixed-batch Frobenius lower bounds hold in every dimension at least their
selected hard dimension, with their original accuracy cutoffs and tail multiplicities.

## Main results

* `NLAlib.run_compressFactorQueryAlgorithm`: exact oracle simulation.
* `NLAlib.isMeasurableFamily_compressFactorQueryAlgorithm`: seed/history measurability.
* `NLAlib.isPassStructured_compressFactorQueryAlgorithm`: original pass labels are retained.
* `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt_of_card_le`:
  equispaced lower bound in every sufficiently large ambient dimension.
* `NLAlib.div_chebyshevQueryFactor_mul_lt_of_pass_lt_of_card_le`:
  the Chebyshev analogue.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {d p n k S : Type*} {q : ℕ}

/-- Compress a matrix–vector query algorithm to the first summand of a coordinate decomposition
$d\oplus p\simeq n$. Each large query is restricted to $d$; responses are padded with zeros;
the two returned low-rank factors are restricted to the same coordinates. No matrix is supplied
to the algorithm. The number of query rounds is unchanged. -/
def compressFactorQueryAlgorithm (e : d ⊕ p ≃ n)
    (alg : QueryAlgorithm (n → ℝ) (n → ℝ) q (Matrix n k ℝ × Matrix k n ℝ)) :
    QueryAlgorithm (d → ℝ) (d → ℝ) q (Matrix d k ℝ × Matrix k d ℝ) :=
  ((alg.mapQuery (fun v i => v (e (Sum.inl i)))).comapResponse
    (fun w i => Sum.elim w (fun _ : p => 0) (e.symm i))).mapOutput
      (fun z => (z.1.submatrix (fun i => e (Sum.inl i)) id,
        z.2.submatrix id (fun i => e (Sum.inl i))))

/-- The compressed algorithm run on $\mathbf{A}$ returns the restricted factors of the original
algorithm run on the reindexed zero padding of $\mathbf{A}$. This is an equality of runs for
every seed, with no probabilistic hypotheses. -/
theorem run_compressFactorQueryAlgorithm [Fintype d] [Finite p] [Fintype n]
    (e : d ⊕ p ≃ n)
    (alg : QueryAlgorithm (n → ℝ) (n → ℝ) q (Matrix n k ℝ × Matrix k n ℝ))
    (A : Matrix d d ℝ) :
    (compressFactorQueryAlgorithm e alg).run A.mulVec =
      let z := alg.run (Matrix.reindex e e
        (Matrix.fromBlocks A (0 : Matrix d p ℝ) (0 : Matrix p d ℝ) 0)).mulVec
      (z.1.submatrix (fun i => e (Sum.inl i)) id,
        z.2.submatrix id (fun i => e (Sum.inl i))) := by
  have : Fintype p := Fintype.ofFinite p
  unfold compressFactorQueryAlgorithm
  rw [QueryAlgorithm.run_mapOutput, QueryAlgorithm.run_comapResponse, QueryAlgorithm.run_mapQuery]
  have hO : ((fun w i => Sum.elim w (fun _ : p => 0) (e.symm i)) ∘ A.mulVec) ∘
      (fun v i => v (e (Sum.inl i))) = (Matrix.reindex e e
        (Matrix.fromBlocks A (0 : Matrix d p ℝ) (0 : Matrix p d ℝ) 0)).mulVec := by
    funext v i
    simp only [Function.comp_apply, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv,
      Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero]
    rfl
  rw [hO]

/-- Restriction, zero padding and factor compression preserve joint seed/history measurability.
This allows the simulated algorithm to meet the same lower-bound model as the original one. -/
theorem isMeasurableFamily_compressFactorQueryAlgorithm [MeasurableSpace S]
    (e : d ⊕ p ≃ n)
    {alg : S → QueryAlgorithm (n → ℝ) (n → ℝ) q (Matrix n k ℝ × Matrix k n ℝ)}
    (h : QueryAlgorithm.IsMeasurableFamily alg) :
    QueryAlgorithm.IsMeasurableFamily (fun s => compressFactorQueryAlgorithm e (alg s)) := by
  have hrestrict : Measurable (fun v : n → ℝ => fun i : d => v (e (Sum.inl i))) := by
    fun_prop
  have hpad : Measurable (fun w : d → ℝ => fun i : n =>
      Sum.elim w (fun _ : p => 0) (e.symm i)) := by
    refine measurable_pi_iff.2 fun i => ?_
    cases he : e.symm i with
    | inl j => simpa only [he, Sum.elim_inl] using measurable_pi_apply j
    | inr j =>
        simpa only [he, Sum.elim_inr] using
          (measurable_const : Measurable fun _ : d → ℝ => (0 : ℝ))
  have hout : Measurable (fun z : Matrix n k ℝ × Matrix k n ℝ =>
      (z.1.submatrix (fun i => e (Sum.inl i)) id,
        z.2.submatrix id (fun i => e (Sum.inl i)))) := by
    apply Measurable.prodMk
    · exact Matrix.measurable_iff.2 fun i j =>
        (Matrix.measurable_apply (e (Sum.inl i)) j).comp measurable_fst
    · exact Matrix.measurable_iff.2 fun i j =>
        (Matrix.measurable_apply i (e (Sum.inl j))).comp measurable_snd
  exact ((h.mapQuery hrestrict).comapResponse hpad).mapOutput hout

/-- Compression keeps the original pass labels and hence the original number of batches. -/
theorem isPassStructured_compressFactorQueryAlgorithm (e : d ⊕ p ≃ n)
    {alg : QueryAlgorithm (n → ℝ) (n → ℝ) q (Matrix n k ℝ × Matrix k n ℝ)}
    {pass : ℕ → ℕ} (h : alg.IsPassStructured pass) :
    (compressFactorQueryAlgorithm e alg).IsPassStructured pass :=
  ((h.mapQuery _).comapResponse _).mapOutput _

/-- Uniform success on every PSD matrix in the larger space implies uniform success of the
compressed algorithm on every PSD matrix in the hard coordinate space. The error contracts
under factor restriction and zero padding cannot increase the optimal residual. -/
theorem forall_le_measureReal_frobNorm_sub_mul_sq_le_compressFactorQueryAlgorithm
    [Fintype d] [Finite p] [Fintype n] [Fintype k]
    [MeasurableSpace S] (ρ : Measure S) [IsFiniteMeasure ρ] (e : d ⊕ p ≃ n)
    (alg : S → QueryAlgorithm (n → ℝ) (n → ℝ) q (Matrix n k ℝ × Matrix k n ℝ))
    {ε α : ℝ} (hε : 0 ≤ ε)
    (hsucc : ∀ A : Matrix n n ℝ, A.PosSemidef → α ≤ ρ.real {s |
      frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    ∀ A : Matrix d d ℝ, A.PosSemidef → α ≤ ρ.real {s |
      frobNorm (A - ((compressFactorQueryAlgorithm e (alg s)).run A.mulVec).1 *
        ((compressFactorQueryAlgorithm e (alg s)).run A.mulVec).2) ^ 2 ≤
          (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2} := by
  intro A hA
  have : Fintype p := Fintype.ofFinite p
  let B := Matrix.reindex e e
    (Matrix.fromBlocks A (0 : Matrix d p ℝ) (0 : Matrix p d ℝ) 0)
  have hB : B.PosSemidef :=
    (hA.fromBlocks_zero₁₂_zero₂₁ (Matrix.PosSemidef.zero :
      (0 : Matrix p p ℝ).PosSemidef)).submatrix e.symm
  have hprincipal : B.submatrix (fun i => e (Sum.inl i)) (fun i => e (Sum.inl i)) = A := by
    ext i j
    simp [B, Matrix.reindex_apply]
  have hopt : frobNorm (B - truncatedSVD B (Fintype.card k)) ≤
      frobNorm (A - truncatedSVD A (Fintype.card k)) := by
    dsimp only [B]
    rw [Matrix.reindex_apply, frobNorm_submatrix_sub_truncatedSVD]
    exact frobNorm_fromBlocks_sub_truncatedSVD_le A (Fintype.card k)
  refine (hsucc B hB).trans (measureReal_mono (Set.ofPred_subset_ofPred.2 fun s hs => ?_))
  have hi : Function.Injective (fun i : d => e (Sum.inl i)) :=
    e.injective.comp Sum.inl_injective
  have herr := frobNorm_submatrix_sub_mul_le B ((alg s).run B.mulVec).1
    ((alg s).run B.mulVec).2 hi hi
  rw [hprincipal] at herr
  simp only [run_compressFactorQueryAlgorithm]
  exact (pow_le_pow_left₀ (frobNorm_nonneg _) herr 2).trans (hs.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (frobNorm_nonneg _) hopt 2) (by linarith)))

variable [Fintype n] [Fintype k] {m : Type*} [Fintype m]

/-- The equispaced fixed-batch Frobenius query lower bound in every ambient dimension at least
$\lvert k\rvert+(r+1)\lvert m\rvert$. Let $\lvert k\rvert>0$, $\varepsilon>0$ with cutoff
at most <!-- value equispacedAccuracyBound r -->$1/(512\cdot4^{r+1}(r+1)(r+2)^2)$, and
$\lvert m\rvert=\lfloor\lvert k\rvert/(\varepsilon(r+1)(r+2))\rfloor$. A jointly measurable
seeded algorithm whose pass labels are below $r$ and which returns factors of inner dimension
$\lvert k\rvert$ with squared relative Frobenius error at most $1+\varepsilon$, with probability
at least $1/2$ on every PSD input in the ambient space, uses <!-- value equispacedQueryFactor r -->
$$q>\frac{\lvert k\rvert}{256\cdot4^{r+1}(r+1)(r+2)\varepsilon}$$
matrix–vector queries. The seed law is an arbitrary probability measure.
No printed source for this dimension-transfer form. -/
theorem div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt_of_card_le
    [Nonempty k] [MeasurableSpace S] {r : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hεr : ε ≤ equispacedAccuracyBound r)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) /
      (ε * ((r : ℝ) + 1) * (r + 2))⌋₊)
    (hdim : Fintype.card (k ⊕ (Fin (r + 1) × m)) ≤ Fintype.card n)
    {alg : S → QueryAlgorithm (n → ℝ) (n → ℝ) q (Matrix n k ℝ × Matrix k n ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < r)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix n n ℝ, A.PosSemidef → 1 / 2 ≤ ρ.real {s |
      frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (equispacedQueryFactor r * ε) < q := by
  classical
  let extra := Fin (Fintype.card n - Fintype.card (k ⊕ (Fin (r + 1) × m)))
  have hcard : Fintype.card ((k ⊕ (Fin (r + 1) × m)) ⊕ extra) = Fintype.card n := by
    rw [Fintype.card_sum]
    simp only [extra, Fintype.card_fin]
    omega
  let e := Fintype.equivOfCardEq hcard
  exact div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt hε hεr hm
    (isMeasurableFamily_compressFactorQueryAlgorithm e halg)
    (fun s => isPassStructured_compressFactorQueryAlgorithm e (hpass s)) hp ρ
    (forall_le_measureReal_frobNorm_sub_mul_sq_le_compressFactorQueryAlgorithm ρ e alg hε.le hsucc)

/-- The Chebyshev fixed-batch Frobenius query lower bound in every ambient dimension at least
$\lvert k\rvert+(r+1)\lvert m\rvert$. Let $\lvert k\rvert>0$, $\varepsilon>0$ with cutoff
at most <!-- value chebyshevAccuracyBound r -->$1/(25088(r+1)^3(r+2))$, and
$\lvert m\rvert=\lfloor\lvert k\rvert/(16\varepsilon(r+1)^3)\rfloor$. A jointly measurable
seeded algorithm whose pass labels are below $r$ and which returns factors of inner dimension
$\lvert k\rvert$ with squared relative Frobenius error at most $1+\varepsilon$, with probability
at least $1/2$ on every PSD input in the ambient space, uses <!-- value chebyshevQueryFactor r -->
$$q>\frac{\lvert k\rvert}{12544(r+1)^3\varepsilon}$$
matrix–vector queries. The seed law is an arbitrary probability measure.
No printed source for this dimension-transfer form. -/
theorem
div_chebyshevQueryFactor_mul_lt_of_pass_lt_of_card_le
    [Nonempty k] [MeasurableSpace S] {r : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hεr : ε ≤ chebyshevAccuracyBound r)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) / (16 * ε * ((r : ℝ) + 1) ^ 3)⌋₊)
    (hdim : Fintype.card (k ⊕ (Fin (r + 1) × m)) ≤ Fintype.card n)
    {alg : S → QueryAlgorithm (n → ℝ) (n → ℝ) q (Matrix n k ℝ × Matrix k n ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < r)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix n n ℝ, A.PosSemidef → 1 / 2 ≤ ρ.real {s |
      frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (chebyshevQueryFactor r * ε) < q := by
  classical
  let extra := Fin (Fintype.card n - Fintype.card (k ⊕ (Fin (r + 1) × m)))
  have hcard : Fintype.card ((k ⊕ (Fin (r + 1) × m)) ⊕ extra) = Fintype.card n := by
    rw [Fintype.card_sum]
    simp only [extra, Fintype.card_fin]
    omega
  let e := Fintype.equivOfCardEq hcard
  exact div_chebyshevQueryFactor_mul_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt
    hε hεr hm (isMeasurableFamily_compressFactorQueryAlgorithm e halg)
    (fun s => isPassStructured_compressFactorQueryAlgorithm e (hpass s)) hp ρ
    (forall_le_measureReal_frobNorm_sub_mul_sq_le_compressFactorQueryAlgorithm ρ e alg hε.le hsucc)

end NLAlib
