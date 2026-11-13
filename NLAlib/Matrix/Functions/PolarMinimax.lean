/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.SingularValueFilters
public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Polynomial.Approximation.GreedyOddMinimax

/-!
# Greedy odd-polynomial polar iterations

Horner evaluation on the column Gram matrix realizes scalar odd minimax compositions on
each singular direction. Zero singular values stay at zero. The proof adapts the original
NLAlib atlas at commit 77514ce.

## Main results

* `NLAlib.IsSVD.oddMatrixIterate_eq`: fixed-frame matrix realization.
* `NLAlib.IsGreedyOddMinimax.specNorm_polarFactor_sub_oddMatrixIterate_le`: minimax rate.
* `NLAlib.forall_specNorm_polarFactor_sub_oddMatrixIterate_le_iff`: worst-case equality.
-/

@[expose] public section

open Matrix Polynomial Finset Filter Set
open scoped Matrix.Norms.L2Operator Topology
namespace NLAlib

variable {𝕜 m n r : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [Fintype r]
variable [DecidableEq n] [DecidableEq r]

/-- Horner evaluation of a degree-at-most $q$ Gram polynomial. The linear endpoint evaluates
a scalar multiple of the supplied matrix directly. [AmselPerssonMuscoGower2026, Appendix E]. -/
noncomputable def gramHorner : ℕ → (ℕ → ℝ) → Matrix n n 𝕜 → Matrix n n 𝕜
  | 0, c, _ => c 0 • 1
  | 1, c, S => c 0 • 1 + c 1 • S
  | q + 2, c, S => c 0 • 1 + S * gramHorner (q + 1) (fun j => c (j + 1)) S

/-- The finite matrix polynomial evaluated by the Horner recursion.
[AmselPerssonMuscoGower2026, Appendix E]. -/
theorem gramHorner_eq_sum (q : ℕ) (c : ℕ → ℝ) (S : Matrix n n 𝕜) :
    gramHorner q c S = ∑ j ∈ range (q + 1), c j • S ^ j := by
  induction q using Nat.twoStepInduction generalizing c with
  | zero => simp [gramHorner]
  | one => simp [gramHorner, Finset.sum_range_succ]
  | more q _ ih =>
    conv_rhs => rw [Finset.sum_range_succ']
    rw [gramHorner, ih]
    simp only [pow_zero, Matrix.mul_sum, Matrix.mul_smul, ← pow_succ']
    rw [add_comm]

/-- The Gram Horner recurrence evaluates an ordinary polynomial supplied through its
coefficients, including zero polynomials and padded degrees. [AmselPerssonMuscoGower2026,
Appendix E]. -/
theorem gramHorner_coeff {q : ℕ} (p : ℝ[X]) (hp : p.natDegree ≤ q) (A : Matrix n n 𝕜) :
    gramHorner q p.coeff A = aeval A p := by
  calc
    _ = aeval A (∑ j ∈ range (q + 1), C (p.coeff j) * X ^ j) := by
      simp [gramHorner_eq_sum, Algebra.algebraMap_eq_smul_one]
    _ = _ := congrArg (aeval A) (p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hp)).symm

/-- For arbitrary coefficient data, the Gram Horner recurrence evaluates the Mathlib polynomial
formed from exactly its first $q+1$ entries. [AmselPerssonMuscoGower2026, Appendix E]. -/
theorem gramHorner_eq_aeval (q : ℕ) (c : ℕ → ℝ) (A : Matrix n n 𝕜) :
    gramHorner q c A = aeval A (Polynomial.ofFn (q + 1) (fun i => c i)) := by
  rw [← gramHorner_coeff _ (Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) _))]
  simp only [gramHorner_eq_sum]
  exact Finset.sum_congr rfl fun i hi => by rw [ofFn_coeff_eq_val_of_lt _ (mem_range.mp hi)]

/-- A sequence of odd polynomial updates with supplied coefficients. Each term is evaluated
as a Gram polynomial by Horner recursion and multiplied by the rectangular input.
[AmselPerssonMuscoGower2026, §2].
Algorithm: polar-minimax-polynomial -/
noncomputable def oddMatrixIterate (q : ℕ) (c : ℕ → ℕ → ℝ) (A : Matrix m n 𝕜) :
    ℕ → Matrix m n 𝕜
  | 0 => A
  | k + 1 =>
    let X := oddMatrixIterate q c A k
    X * gramHorner q (c k) (Xᴴ * X)

/-- **Odd polynomial polar iterates in singular coordinates.** For arbitrary coefficients the
matrix iteration preserves a supplied singular frame and composes the scalar odd polynomials
on its diagonal, even if intermediate values change sign. [AmselPerssonMuscoGower2026, §2].
Result: polar-minimax-polynomial-iteration -/
theorem IsSVD.oddMatrixIterate_eq {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {V : Matrix n r 𝕜}
    {σ : r → ℝ} (h : IsSVD A U σ V) (q : ℕ) (c : ℕ → ℕ → ℝ) (k : ℕ) :
    oddMatrixIterate q c A k =
      U * diagonal (fun i => ((oddScalarComposition q c (σ i) k : ℝ) : 𝕜)) * Vᴴ := by
  induction k with
  | zero => exact h.eq
  | succ k ih =>
    rw [oddMatrixIterate, gramHorner_eq_aeval, ih,
      h.hasOrthonormalCols_left.mul_aeval_conjTranspose_mul_self h.hasOrthonormalCols_right]
    simp only [← oddScalarUpdate_eq_mul_eval, oddScalarComposition]

/-- The exact spectral-norm error on any compact SVD is the supremum of the scalar errors
on its positive singular coordinates. [AmselPerssonMuscoGower2026, Theorem 3.3],
allowing deficient rank and an empty compact SVD. -/
theorem IsSVD.specNorm_polarFactor_sub_oddMatrixIterate {A : Matrix m n 𝕜}
    {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V)
    (hp : ∀ i, 0 < σ i) (q : ℕ) (c : ℕ → ℕ → ℝ) (k : ℕ) :
    specNorm (polarFactor A - oddMatrixIterate q c A k) =
      ‖fun i => 1 - oddScalarComposition q c (σ i) k‖ := by
  rw [h.polarFactor_eq, h.oddMatrixIterate_eq]
  simp only [if_neg (hp _).ne']
  change _ = ‖(fun _ : r => (1 : ℝ)) - (fun i => oddScalarComposition q c (σ i) k)‖
  simpa only [RCLike.ofReal_one] using
    h.hasOrthonormalCols_left.specNorm_sub_mul_diagonal_mul_conjTranspose
      h.hasOrthonormalCols_right (fun _ => 1) (fun i => oddScalarComposition q c (σ i) k)

/-- **Greedy minimax polar error.** For a genuinely minimizing update on each attained
interval, if the positive singular values of the input belong to $[a,1]$ with $0<a\le1$,
then after $k\ge1$ updates the spectral error is at most $1-l_k$. The endpoint bound
`IsGreedyOddMinimax.one_sub_le_pow` gives the rate $(1-a^2)^{(q+1)^k}$.
[AmselPerssonMuscoGower2026, Theorem 3.3 and Appendix D], with the theorem's exponent.
Result: polar-minimax-polynomial-iteration -/
theorem IsGreedyOddMinimax.specNorm_polarFactor_sub_oddMatrixIterate_le {q : ℕ} {a : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q a c l u)
    (ha : 0 < a) (ha1 : a ≤ 1) (A : Matrix m n 𝕜)
    (hA : ∀ i, 0 < singularValues A i → singularValues A i ∈ Icc a 1)
    {T : ℕ} (hT : 1 ≤ T) :
    specNorm (polarFactor A - oddMatrixIterate q c A T) ≤ 1 - l T := by
  classical
  obtain ⟨U, V, hS⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  have hp (i : Fin A.rank) : 0 < singularValues A i := (singularValues_pos_iff A).mpr i.isLt
  have hb := h.abs_one_sub_oddScalarComposition_le ha ha1 hT (x := a) ⟨le_rfl, ha1⟩
  rw [hS.specNorm_polarFactor_sub_oddMatrixIterate hp]
  exact (pi_norm_le_iff_of_nonneg ((abs_nonneg _).trans hb)).mpr fun i =>
    h.abs_one_sub_oddScalarComposition_le ha ha1 hT (hA i (hp i))

/-- **Greedy minimax polar convergence rate.** If the positive singular values of a rectangular
matrix belong to $[a,1]$ with $0<a\le1$, the degree-$2q+1$ greedy filters give spectral
error at most $(1-a^2)^{(q+1)^k}$ after $k\ge 1$ updates. The estimate also holds for a
rank-deficient input. [AmselPerssonMuscoGower2026, Theorem 3.3 and Appendix D].
Result: polar-minimax-polynomial-iteration -/
theorem IsGreedyOddMinimax.specNorm_polarFactor_sub_oddMatrixIterate_le_pow {q : ℕ} {a : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax q a c l u)
    (ha : 0 < a) (ha1 : a ≤ 1) (A : Matrix m n 𝕜)
    (hA : ∀ i, 0 < singularValues A i → singularValues A i ∈ Icc a 1)
    {k : ℕ} (hk : 1 ≤ k) :
    specNorm (polarFactor A - oddMatrixIterate q c A k) ≤ (1 - a ^ 2) ^ ((q + 1) ^ k) :=
  (h.specNorm_polarFactor_sub_oddMatrixIterate_le ha ha1 A hA hk).trans (h.one_sub_le_pow ha ha1 hk)

/-- For positive Gram degree, the genuine greedy iteration converges to the polar factor
when the positive singular values lie in a known interval $[a,1]$ with $a>0$.
[AmselPerssonMuscoGower2026, Theorem 3.3]. -/
theorem IsGreedyOddMinimax.tendsto_oddMatrixIterate {q : ℕ} {a : ℝ}
    {c : ℕ → ℕ → ℝ} {l u : ℕ → ℝ} (h : IsGreedyOddMinimax (q + 1) a c l u)
    (ha : 0 < a) (ha1 : a ≤ 1) (A : Matrix m n 𝕜)
    (hA : ∀ i, 0 < singularValues A i → singularValues A i ∈ Icc a 1) :
    Tendsto (oddMatrixIterate (q + 1) c A) atTop (𝓝 (polarFactor A)) := by
  have h0 : 0 ≤ 1 - a ^ 2 := by nlinarith
  have h1 : 1 - a ^ 2 < 1 := by nlinarith [sq_pos_of_pos ha]
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < (q + 1) + 1))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun k => norm_nonneg _) _ hp
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  change ‖oddMatrixIterate (q + 1) c A k - polarFactor A‖ ≤
    (1 - a ^ 2) ^ ((q + 1 + 1) ^ k)
  rw [← specNorm_eq_norm, specNorm_sub_comm]
  exact h.specNorm_polarFactor_sub_oddMatrixIterate_le_pow ha ha1 A hA hk

private theorem exists_single_frame [Nonempty m] : ∃ U : Matrix m Unit 𝕜, HasOrthonormalCols U := by
  classical
  let i : m := Classical.choice inferInstance
  refine ⟨replicateCol Unit (Pi.single i 1), hasOrthonormalCols_replicateCol ?_⟩
  change ‖EuclideanSpace.single i (1 : 𝕜)‖ = 1
  simp

/-- **Worst-case polar error on a spectral interval.** In any nonempty rectangular shape,
a uniform error bound over inputs whose nonzero singular values lie in a positive interval
holds exactly when it holds for the scalar composition throughout that interval. A rank-one
input realizes every positive scalar in the interval. [AmselPerssonMuscoGower2026, Theorem 3.3].
Result: polar-minimax-polynomial-iteration -/
theorem forall_specNorm_polarFactor_sub_oddMatrixIterate_le_iff [Nonempty m] [Nonempty n]
    (q : ℕ) (c : ℕ → ℕ → ℝ) (T : ℕ) {a b ε : ℝ} (ha : 0 < a) :
    (∀ A : Matrix m n 𝕜, (∀ i, 0 < singularValues A i → singularValues A i ∈ Icc a b) →
      specNorm (polarFactor A - oddMatrixIterate q c A T) ≤ ε) ↔
      0 ≤ ε ∧ ∀ x ∈ Icc a b, |1 - oddScalarComposition q c x T| ≤ ε := by
  classical
  constructor
  · intro h
    have hε := h 0 (by simp)
    refine ⟨(specNorm_nonneg _).trans hε, ?_⟩
    intro x hx
    obtain ⟨U, hU⟩ := exists_single_frame (m := m) (𝕜 := 𝕜)
    obtain ⟨V, hV⟩ := exists_single_frame (m := n) (𝕜 := 𝕜)
    let A := U * diagonal (fun _ : Unit => (x : 𝕜)) * Vᴴ
    have hx0 := ha.trans_le hx.1
    have hS : IsSVD A U (fun _ => x) V := ⟨hU, hV, fun _ => hx0.le, rfl⟩
    have hr : A.rank = 1 := by simp [hS.rank_eq, hx0.ne']
    have hσ : ∀ i, 0 < singularValues A i → singularValues A i ∈ Icc a b := by
      intro i hi
      have hk := (singularValues_pos_iff A).mp hi
      rw [hr] at hk
      have : i = 0 := by omega
      subst i
      rw [singularValues_zero_eq_specNorm, hS.specNorm_eq]
      simpa only [pi_norm_const, Real.norm_eq_abs, abs_of_pos hx0] using hx
    have he := h A hσ
    rw [hS.specNorm_polarFactor_sub_oddMatrixIterate (fun _ => hx0)] at he
    simpa only [pi_norm_const, Real.norm_eq_abs] using he
  · rintro ⟨hε, h⟩ A hA
    obtain ⟨U, V, hS⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
    have hp (i : Fin A.rank) : 0 < singularValues A i := (singularValues_pos_iff A).mpr i.isLt
    rw [hS.specNorm_polarFactor_sub_oddMatrixIterate hp]
    exact (pi_norm_le_iff_of_nonneg hε).mpr fun i => h _ (hA i (hp i))

end NLAlib
