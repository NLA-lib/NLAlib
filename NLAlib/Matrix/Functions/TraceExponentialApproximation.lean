/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.Exponential
public import NLAlib.Matrix.Spectral.SimpleSpectrum
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import NLAlib.Matrix.Spectral.Simultaneous
public import NLAlib.ForMathlib.Probability.Moments.CompactLaplaceTransform
public import NLAlib.ForMathlib.Analysis.SpecificLimits.StrictAntiApproximation

/-!
# Weak approximation of exponential trace measures

A commuting pencil gives an explicit atomic measure. Compactly supported measures pass to a
limit of Hermitian pencils with distinct slopes.

## Main results

* `NLAlib.exists_isCompactExpRepresentation_re_trace_exp_of_diagonal_simple`.
-/
@[expose] public section

open Matrix MeasureTheory Set Filter

open scoped Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem re_trace_exp_unitary_conj (V : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    (NormedSpace.exp ((V : Matrix ι ι ℂ) * A * (V : Matrix ι ι ℂ)ᴴ)).trace.re =
      (NormedSpace.exp A).trace.re :=
  (hasOrthonormalCols_iff_mem_unitaryGroup.mpr V.property).re_trace_exp_mul_mul_conjTranspose rfl A

private theorem re_trace_exp_diagonal_real (a : ι → ℝ) :
    (NormedSpace.exp (diagonal (fun i => (a i : ℂ)))).trace.re = ∑ i, Real.exp (a i) := by
  rw [Matrix.exp_diagonal, Matrix.trace_diagonal, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp, Complex.ofReal_re]

/-- In a simultaneous unitary diagonalization the trace pencil is a finite sum of scalar
exponentials, for every real parameter. -/
theorem re_trace_exp_add_smul_eq_sum_of_diagonalization
    (A H U : Matrix ι ι ℂ) (a b : ι → ℝ) (hU : HasOrthonormalCols U)
    (hA : Uᴴ * A * U = diagonal (fun i => (a i : ℂ)))
    (hH : Uᴴ * H * U = diagonal (fun i => (b i : ℂ))) (t : ℝ) :
    (NormedSpace.exp (A + t • H)).trace.re = ∑ i, Real.exp (a i + t * b i) := by
  let V : unitary (Matrix ι ι ℂ) :=
    ⟨Uᴴ, by simpa only [Unitary.mem_iff, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
      using And.intro (mul_eq_one_comm.mp hU.conjTranspose_mul_self) hU.conjTranspose_mul_self⟩
  have hconj : (V : Matrix ι ι ℂ) * (A + t • H) *
      (V : Matrix ι ι ℂ)ᴴ = diagonal (fun i => ((a i + t * b i : ℝ) : ℂ)) := by
    change Uᴴ * (A + t • H) * Uᴴᴴ = _
    rw [conjTranspose_conjTranspose, mul_add, add_mul, Matrix.mul_smul,
      Matrix.smul_mul, hA, hH]
    ext i j
    by_cases hij : i = j <;> simp [hij, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.real_smul]
  rw [← re_trace_exp_unitary_conj V, hconj, re_trace_exp_diagonal_real]

/-- A commuting Hermitian pencil admits a finite positive Borel measure on the
direction's spectral interval representing its trace exponential at every real
parameter. Includes repeated eigenvalues and the empty matrix, whose measure is
zero. -/
theorem exists_isCompactExpRepresentation_re_trace_exp_of_commute
    (A H : Matrix ι ι ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hAH : Commute A H) :
    ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
      (fun t : ℝ => (NormedSpace.exp (A + t • H)).trace.re)
          (sInf (spectrum ℝ H)) (sSup (spectrum ℝ H)) := by
  obtain ⟨U, a, b, hU, hUA, hUH⟩ :=
    (hA.commute_iff_exists_eq_mul_diagonal_mul_conjTranspose hH).mp hAH
  let V : unitary (Matrix ι ι ℂ) := ⟨U, hasOrthonormalCols_iff_mem_unitaryGroup.mp hU⟩
  have hb (i : ι) : b i ∈ Icc (sInf (spectrum ℝ H)) (sSup (spectrum ℝ H)) := by
    have hi := mem_spectrum_of_eq_mul_diagonal_mul_conjTranspose b V hUH i
    have hfin : (spectrum ℝ H).Finite := by
      rw [hH.spectrum_real_eq_range_eigenvalues]
      exact finite_range _
    exact ⟨csInf_le hfin.bddBelow hi, le_csSup hfin.bddAbove hi⟩
  refine ⟨exponentialAtomicMeasure a b, ?_⟩
  have hr := isCompactExpRepresentation_exponentialAtomicMeasure a b hb
  convert hr using 1
  funext t
  apply re_trace_exp_add_smul_eq_sum_of_diagonalization A H U a b hU _ _ t
  · rw [hUA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU.conjTranspose_mul_self,
      Matrix.one_mul, Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one]
    rfl
  · rw [hUH, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU.conjTranspose_mul_self,
      Matrix.one_mul, Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one]
    rfl

/-- Positive representations on a common compact interval pass to limits of
both matrices in a pencil. The positivity of approximating measures is retained
by compactness; no positivity or representation hypothesis is imposed on the
limiting pencil. -/
private theorem exists_isCompactExpRepresentation_re_trace_exp_of_tendsto
    {I : Type*} {l : Filter I} [l.NeBot]
    (Aₙ Hₙ : I → Matrix ι ι ℂ) (A H : Matrix ι ι ℂ) (a b : ℝ)
    (hA : Filter.Tendsto Aₙ l (𝓝 A)) (hH : Filter.Tendsto Hₙ l (𝓝 H))
    (hrep : ∀ᶠ k in l, ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
      (fun t : ℝ => (NormedSpace.exp (Aₙ k + t • Hₙ k)).trace.re) a b) :
    ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
      (fun t : ℝ => (NormedSpace.exp (A + t • H)).trace.re) a b := by
  apply exists_isCompactExpRepresentation_of_tendsto a b _ _ hrep
  intro t
  exact continuous_re_trace_exp.continuousAt.tendsto.comp
    (hA.add (Filter.Tendsto.smul tendsto_const_nhds hH))

end NLAlib

open Matrix MeasureTheory Set Filter

open scoped Matrix.Norms.L2Operator Topology

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive-measure representation for every simple real diagonal direction
implies the representation for arbitrary Hermitian directions. The approximation
stays in the limiting direction's exact spectral interval; repeated eigenvalues,
scalar directions, and empty dimension are all included. The simple diagonal
case is the explicit remaining premise of this reduction theorem. -/
theorem exists_isCompactExpRepresentation_re_trace_exp_of_diagonal_simple
    (A H : Matrix n n ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian)
    (hsimple : ∀ (C : Matrix n n ℂ), C.IsHermitian →
      ∀ (b : n → ℝ), Function.Injective b → ∀ l u : ℝ, l ≤ u →
        (∀ i, b i ∈ Icc l u) → ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
          (fun t : ℝ => (NormedSpace.exp (C + t • diagonal (fun i => (b i : ℂ)))).trace.re) l u) :
    ∃ ν : FiniteMeasure ℝ, IsCompactExpRepresentation ν
      (fun t : ℝ => (NormedSpace.exp (A + t • H)).trace.re)
          (sInf (spectrum ℝ H)) (sSup (spectrum ℝ H)) := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    have := hn
    exact exists_isCompactExpRepresentation_re_trace_exp_of_commute A H hA hH
      (Subsingleton.elim _ _)
  | inr hn =>
    have := hn
    let l := sInf (spectrum ℝ H)
    let u := sSup (spectrum ℝ H)
    have hfin : (spectrum ℝ H).Finite := by
      rw [hH.spectrum_real_eq_range_eigenvalues]
      exact finite_range _
    have hbmem (i : n) : hH.eigenvalues i ∈ Icc l u := by
      have hi := hH.eigenvalues_mem_spectrum_real i
      exact ⟨csInf_le hfin.bddBelow hi, le_csSup hfin.bddAbove hi⟩
    let E := Unitary.conjStarAlgAut ℝ (Matrix n n ℂ) (star hH.eigenvectorUnitary)
    have hEH : E H = diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
      simpa only [E, Function.comp_def, RCLike.ofReal_eq_complex_ofReal,
        Unitary.conjStarAlgAut_apply] using
        hH.conjStarAlgAut_star_eigenvectorUnitary
    have hlu : l ≤ u := by
      obtain ⟨i⟩ := hn
      exact (hbmem i).1.trans (hbmem i).2
    by_cases hsame : l = u
    · have hscalar : H = (l : ℝ) • (1 : Matrix n n ℂ) := by
        apply E.injective
        change E H = E ((l : ℝ) • (1 : Matrix n n ℂ))
        rw [hEH, map_smul, map_one]
        have heig (i : n) : hH.eigenvalues i = l := by
          have hi := hbmem i
          rw [← hsame] at hi
          exact le_antisymm hi.2 hi.1
        ext i j
        by_cases hij : i = j <;> simp [hij, heig, Complex.real_smul]
      apply exists_isCompactExpRepresentation_re_trace_exp_of_commute A H hA hH
      rw [hscalar]
      exact (Commute.one_right A).smul_right l
    have hlt : l < u := lt_of_le_of_ne hlu hsame
    let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
    have hb0mem (i : Fin (Fintype.card n)) : hH.eigenvalues₀ i ∈ Icc l u := by
      simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using hbmem (e i)
    obtain ⟨v, hvstrict, hvmem, hvlim⟩ :=
      Fin.exists_strictAnti_tendsto_mem_Icc hH.eigenvalues₀_antitone hlt hb0mem
    let b : ℕ → n → ℝ := fun k i => v k (e.symm i)
    have hbinj (k : ℕ) : Function.Injective (b k) :=
      (hvstrict k).injective.comp e.symm.injective
    have hbinterval (k : ℕ) (i : n) : b k i ∈ Icc l u := hvmem k (e.symm i)
    have hblim : Tendsto b atTop (𝓝 hH.eigenvalues) := by
      apply tendsto_pi_nhds.mpr
      intro i
      exact (tendsto_pi_nhds.mp hvlim) (e.symm i)
    let K : ℕ → Matrix n n ℂ := fun k => diagonal (fun i => (b k i : ℂ))
    have hKlim : Tendsto K atTop (𝓝 (E H)) := by
      rw [hEH]
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_pi_nhds.mpr
      intro j
      by_cases hij : i = j
      · subst j
        simpa only [K, diagonal_apply_eq, Function.comp_def] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hblim) i)
      · simpa only [K, diagonal_apply_ne _ hij] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    have hEA : (E A).IsHermitian :=
      Matrix.isHermitian_mul_mul_conjTranspose _ hA
    obtain ⟨ν, hν⟩ := exists_isCompactExpRepresentation_re_trace_exp_of_tendsto
      (fun _ : ℕ => E A) K (E A) (E H) l u tendsto_const_nhds hKlim
      (Eventually.of_forall fun k => hsimple (E A) hEA (b k) (hbinj k) l u hlu (hbinterval k))
    refine ⟨ν, ?_⟩
    convert hν using 1
    funext t
    rw [← map_smul E, ← map_add E]
    exact (re_trace_exp_unitary_conj (star hH.eigenvectorUnitary) (A + t • H)).symm

end NLAlib
