/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.SingularValueFilters
public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Polynomial.Approximation.NewtonSchulz
public import NLAlib.Matrix.Basic.Gram
public import NLAlib.Matrix.Norms.Loewner

/-!
# Inverse-free rectangular polar iteration

The library scalar cubic acts on the singular directions. The defect estimates start
after its first update, including when the initial defect exceeds one. The argument
adapts the original NLAlib atlas at commit 77514ce.

## Main results

* `NLAlib.columnGramDefect_polarSchulzStep`: the exact defect polynomial.
* `NLAlib.specNorm_columnGramDefect_polarSchulzIterate_succ_le`: quadratic defect contraction.
* `NLAlib.tendsto_polarSchulzIterate`: convergence to the polar factor.
-/

@[expose] public section

open Matrix Polynomial Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace NLAlib

variable {𝕜 m n r : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [Fintype r]
variable [DecidableEq n] [DecidableEq r]

/-- One cubic step for the rectangular polar factor, evaluated using its column Gram matrix.
[Higham2008, §8.3]. -/
noncomputable def polarSchulzStep (A : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  (1 / 2 : ℝ) • (A * ((3 : ℝ) • 1 - Aᴴ * A))

/-- The inverse-free polar Newton–Schulz iteration.
[Higham2008, §8.3].
Algorithm: polar-newton-schulz -/
noncomputable def polarSchulzIterate (A : Matrix m n 𝕜) (k : ℕ) : Matrix m n 𝕜 :=
  polarSchulzStep^[k] A

/-- The deviation of a column Gram matrix from the identity, with the sign for which
the defect is positive semidefinite after the first admissible polar step. -/
noncomputable def columnGramDefect (A : Matrix m n 𝕜) : Matrix n n 𝕜 := 1 - Aᴴ * A

/-- **Cubic polar-step defect.** For every real or complex rectangular matrix, the Gram defect
$\mathbf{E}=\mathbf{I}-\mathbf{X}^{\mathsf{H}}\mathbf{X}$ after one cubic step obeys
$$\mathbf{E}_+=\frac14
\mathbf{E}^2(3\mathbf{I}+\mathbf{E}).$$ [Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem columnGramDefect_polarSchulzStep (X : Matrix m n 𝕜) :
    columnGramDefect (polarSchulzStep X) =
      (1 / 4 : ℝ) • (columnGramDefect X ^ 2 * ((3 : ℝ) • 1 + columnGramDefect X)) := by
  let S := Xᴴ * X
  let L := (3 : ℝ) • (1 : Matrix n n 𝕜) - S
  have hS : Sᴴ = S := by simp [S]
  have hL : Lᴴ = L := by simp [L, hS]
  have hG : (polarSchulzStep X)ᴴ * polarSchulzStep X = (1 / 4 : ℝ) • (L * S * L) := by
    change ((1 / 2 : ℝ) • (X * L))ᴴ * ((1 / 2 : ℝ) • (X * L)) = _
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hL,
      star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    norm_num only [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
    simp only [S, Matrix.mul_assoc]
  rw [columnGramDefect, hG]
  calc
    _ = (1 / 4 : ℝ) • ((4 : ℝ) • (1 : Matrix n n 𝕜) - L * S * L) := by module
    _ = _ := by
      congr 1
      dsimp only [L, S, columnGramDefect]
      noncomm_ring
      module

private theorem polarSchulzStep_eq_aeval (A : Matrix m n 𝕜) :
    polarSchulzStep A = A * aeval (Aᴴ * A) (C (2⁻¹ : ℝ) * (C 3 - X) : ℝ[X]) := by
  simp only [map_mul, map_sub, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, polarSchulzStep, one_div]

/-- **Singular directions of the inverse-free polar iteration.** The kth matrix iterate
acts by the kth iterate of the real cubic on each supplied singular coordinate.
[Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem IsSVD.polarSchulzIterate_eq {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (k : ℕ) :
    polarSchulzIterate A k =
      U * diagonal (fun i => (((newtonSchulz^[k]) (σ i) : ℝ) : 𝕜)) * Vᴴ := by
  induction k with
  | zero => exact h.eq
  | succ k ih =>
    change polarSchulzStep^[k + 1] A = _
    rw [Function.iterate_succ_apply']
    change polarSchulzStep (polarSchulzIterate A k) = _
    rw [polarSchulzStep_eq_aeval, ih,
      h.hasOrthonormalCols_left.mul_aeval_conjTranspose_mul_self h.hasOrthonormalCols_right]
    simp only [eval_mul, eval_sub, eval_C, eval_X, Function.iterate_succ_apply', newtonSchulz,
      div_eq_mul_inv]
    congr 2
    funext i
    congr 1
    ring_nf

omit [DecidableEq n] in
private theorem IsSVD.sq_lt_three {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (hA : specNorm A < √3) (i : r) :
    σ i ^ 2 < 3 := by
  have hs : σ i < √3 := (le_abs_self _).trans_lt <|
    (norm_le_pi_norm σ i).trans_lt (h.specNorm_eq ▸ hA)
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), h.nonneg i]

private theorem isSVD_polarSchulzIterate {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (hp : ∀ i, 0 < σ i)
    (hA : specNorm A < √3) (k : ℕ) :
    IsSVD (polarSchulzIterate A k) U (fun i => (newtonSchulz^[k]) (σ i)) V := by
  refine ⟨h.hasOrthonormalCols_left, h.hasOrthonormalCols_right, ?_, h.polarSchulzIterate_eq k⟩
  intro i
  cases k with
  | zero => exact (hp i).le
  | succ k => exact (newtonSchulz_iterate_mem_Ioc (hp i) (h.sq_lt_three hA i) k).1.le

private theorem IsSVD.columnGramDefect_eq {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (hp : ∀ i, 0 < σ i)
    (hc : Fintype.card n = Fintype.card r) (hA : specNorm A < √3) (k : ℕ) :
    columnGramDefect (polarSchulzIterate A k) =
      V * diagonal (fun i => ((1 - ((newtonSchulz^[k]) (σ i)) ^ 2 : ℝ) : 𝕜)) * Vᴴ := by
  have hI : (1 : Matrix n n 𝕜) = V * diagonal (fun _ : r => (1 : 𝕜)) * Vᴴ := by
    simpa only [Matrix.diagonal_one, Matrix.mul_one] using
      (h.hasOrthonormalCols_right.mul_conjTranspose_self_of_card_eq hc).symm
  rw [columnGramDefect, hI, (isSVD_polarSchulzIterate h hp hA k).conjTranspose_mul_self_eq,
    ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  simp only [RCLike.ofReal_sub, RCLike.ofReal_one]

private theorem IsSVD.specNorm_columnGramDefect_eq {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (hp : ∀ i, 0 < σ i)
    (hc : Fintype.card n = Fintype.card r) (hA : specNorm A < √3) (k : ℕ) :
    specNorm (columnGramDefect (polarSchulzIterate A k)) =
      ‖fun i => 1 - ((newtonSchulz^[k]) (σ i)) ^ 2‖ := by
  rw [h.columnGramDefect_eq hp hc hA,
    h.hasOrthonormalCols_right.specNorm_mul_diagonal_mul_conjTranspose h.hasOrthonormalCols_right]

omit [DecidableEq n] in
private theorem exists_compactSVD_of_injective (A : Matrix m n 𝕜)
    (hr : Function.Injective A.mulVec) :
    ∃ (U : Matrix m (Fin A.rank) 𝕜) (V : Matrix n (Fin A.rank) 𝕜),
      IsSVD A U (fun i : Fin A.rank => singularValues A i) V ∧
      (∀ i : Fin A.rank, 0 < singularValues A i) ∧ Fintype.card n = Fintype.card (Fin A.rank) := by
  obtain ⟨U, V, h⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  refine ⟨U, V, h, fun i => (singularValues_pos_iff A).mpr i.isLt, ?_⟩
  rw [Fintype.card_fin, ← mulVec_injective_iff_rank_eq.mp hr]

/-- A cubic polar step sends every rectangular matrix of spectral norm at most two to a
matrix of spectral norm at most one. [Higham2008, §8.3]. -/
theorem specNorm_polarSchulzStep_le_one {X : Matrix m n 𝕜} (hX : specNorm X ≤ 2) :
    specNorm (polarSchulzStep X) ≤ 1 := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD X le_rfl X.rank_le_card_height X.rank_le_card_width
  change specNorm (polarSchulzIterate X 1) ≤ 1
  rw [h.polarSchulzIterate_eq, h.hasOrthonormalCols_left.specNorm_mul_diagonal_mul_conjTranspose
    h.hasOrthonormalCols_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  exact fun i => abs_newtonSchulz_le_one <|
    (norm_le_pi_norm (fun j : Fin X.rank => singularValues X j) i).trans (h.specNorm_eq ▸ hX)

/-- Every cubic iterate after the first has spectral norm at most one if the initial spectral
norm is at most two, including for deficient inputs. [Higham2008, §8.3]. -/
theorem specNorm_polarSchulzIterate_succ_le_one (A : Matrix m n 𝕜) (hA : specNorm A ≤ 2) (k : ℕ) :
    specNorm (polarSchulzIterate A (k + 1)) ≤ 1 := by
  induction k with
  | zero => exact specNorm_polarSchulzStep_le_one hA
  | succ k ih =>
    unfold polarSchulzIterate
    rw [Function.iterate_succ_apply']
    exact specNorm_polarSchulzStep_le_one (ih.trans (by norm_num))

/-- For a rectangular contraction $\mathbf{X}$, its column Gram defect
$\mathbf{I}-\mathbf{X}^{\mathsf{H}}\mathbf{X}$ is positive semidefinite. -/
theorem posSemidef_columnGramDefect_of_specNorm_le_one {X : Matrix m n 𝕜}
    (hX : specNorm X ≤ 1) : (columnGramDefect X).PosSemidef := by
  have hs : specNorm X ^ 2 ≤ 1 := by nlinarith [specNorm_nonneg X]
  simpa only [one_smul, Matrix.le_iff, columnGramDefect] using
    (specNorm_sq_le_iff_conjTranspose_mul_self_le zero_le_one).mp hs

/-- **Positivity after the first inverse-free polar step.** For an arbitrary rectangular input
of spectral norm at most two, every subsequent Gram defect is positive semidefinite.
[Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem posSemidef_columnGramDefect_polarSchulzIterate (A : Matrix m n 𝕜)
    (hA : specNorm A ≤ 2) (k : ℕ) :
    (columnGramDefect (polarSchulzIterate A (k + 1))).PosSemidef :=
  posSemidef_columnGramDefect_of_specNorm_le_one
    (specNorm_polarSchulzIterate_succ_le_one A hA k)

/-- **Rank preservation by the inverse-free polar iteration.** At initial spectral norm below
$\sqrt{3}$, every Newton–Schulz iterate has the same rank as its input, including at rank zero.
In particular a full-column-rank input retains full column rank. [Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem rank_polarSchulzIterate (A : Matrix m n 𝕜) (hA : specNorm A < √3) (k : ℕ) :
    (polarSchulzIterate A k).rank = A.rank := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  have hp (i : Fin A.rank) : 0 < singularValues A i := (singularValues_pos_iff A).mpr i.isLt
  have hpos (i : Fin A.rank) : 0 < (newtonSchulz^[k]) (singularValues A i) := by
    cases k with
    | zero => exact hp i
    | succ k => exact (newtonSchulz_iterate_mem_Ioc (hp i) (h.sq_lt_three hA i) k).1
  rw [(isSVD_polarSchulzIterate h hp hA k).rank_eq,
    Finset.filter_eq_self.mpr (fun i _ => (hpos i).ne'), Finset.card_univ, Fintype.card_fin]

/-- **Polar Gram defect below one.** A full-column-rank input of spectral norm below
$\sqrt{3}$ has a strict Gram defect contraction after one or more steps.
[Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem specNorm_columnGramDefect_polarSchulzIterate_lt_one (A : Matrix m n 𝕜)
    (hA : specNorm A < √3) (hr : Function.Injective A.mulVec) (k : ℕ) :
    specNorm (columnGramDefect (polarSchulzIterate A (k + 1))) < 1 := by
  classical
  obtain ⟨U, V, h, hp, hc⟩ := exists_compactSVD_of_injective A hr
  simp only [h.specNorm_columnGramDefect_eq hp hc hA]
  apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
  intro i
  obtain ⟨hp, hle⟩ := newtonSchulz_iterate_mem_Ioc (hp i) (h.sq_lt_three hA i) k
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> nlinarith [sq_pos_of_pos hp, sq_nonneg ((newtonSchulz^[k + 1])
    (singularValues A i) - 1)]

/-- At any rectangular contraction $\mathbf{X}$, the Gram defect after one cubic step
has spectral norm at most $\|\mathbf{I}-\mathbf{X}^{\mathsf{H}}\mathbf{X}\|_2^2$.
[Higham2008, §8.3]. -/
theorem specNorm_columnGramDefect_polarSchulzStep_le {X : Matrix m n 𝕜}
    (hX : specNorm X ≤ 1) :
    specNorm (columnGramDefect (polarSchulzStep X)) ≤ specNorm (columnGramDefect X) ^ 2 := by
  let E := columnGramDefect X
  have hE : E.PosSemidef := posSemidef_columnGramDefect_of_specNorm_le_one hX
  have hle : E ≤ 1 := sub_le_self _ (Matrix.posSemidef_conjTranspose_mul_self X).nonneg
  have hnorm := (hE.specNorm_le_specNorm_of_le hle).trans specNorm_one_le
  have hfactor : specNorm ((3 : ℝ) • (1 : Matrix n n 𝕜) + E) ≤ 4 := by
    apply (specNorm_add_le _ _).trans
    rw [specNorm_real_smul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    linarith [specNorm_one_le (𝕜 := 𝕜) (n := n)]
  rw [columnGramDefect_polarSchulzStep, specNorm_real_smul]
  change |(1 / 4 : ℝ)| * specNorm (E ^ 2 * ((3 : ℝ) • 1 + E)) ≤ specNorm E ^ 2
  have hm := (specNorm_mul_le _ _).trans (mul_le_mul (specNorm_pow_le E 2) hfactor
    (specNorm_nonneg _) (sq_nonneg _))
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  linarith

/-- **Quadratic Gram defect contraction.** For any rectangular input of spectral norm at
most two, each subsequent defect norm is at most the square of the preceding one.
[Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem specNorm_columnGramDefect_polarSchulzIterate_succ_le (A : Matrix m n 𝕜)
    (hA : specNorm A ≤ 2) (k : ℕ) :
    specNorm (columnGramDefect (polarSchulzIterate A (k + 2))) ≤
      specNorm (columnGramDefect (polarSchulzIterate A (k + 1))) ^ 2 := by
  unfold polarSchulzIterate
  rw [Function.iterate_succ_apply']
  exact specNorm_columnGramDefect_polarSchulzStep_le
    (specNorm_polarSchulzIterate_succ_le_one A hA k)

private theorem IsSVD.norm_defect_coeff_le {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (k : ℕ) :
    ‖fun i => (1 : ℝ) - ((newtonSchulz^[k]) (σ i)) ^ 2‖ ≤
      specNorm (columnGramDefect (polarSchulzIterate A k)) := by
  let X := polarSchulzIterate A k
  let D := diagonal (fun i => (((newtonSchulz^[k]) (σ i) : ℝ) : 𝕜))
  have hXV : X * V = U * D := by
    rw [show X = _ from h.polarSchulzIterate_eq k]
    simp only [D, Matrix.mul_assoc, h.hasOrthonormalCols_right.conjTranspose_mul_self,
      Matrix.mul_one]
  have hcomp : Vᴴ * columnGramDefect X * V =
      diagonal (fun i => ((1 - ((newtonSchulz^[k]) (σ i)) ^ 2 : ℝ) : 𝕜)) := by
    rw [columnGramDefect, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      h.hasOrthonormalCols_right.conjTranspose_mul_self]
    have hh : Vᴴ * (Xᴴ * X) * V = (X * V)ᴴ * (X * V) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [hh, hXV, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      h.hasOrthonormalCols_left.conjTranspose_mul_cancel_left]
    simp only [D, Matrix.conjTranspose_diagonal_ofReal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one, Matrix.diagonal_sub, RCLike.ofReal_sub, RCLike.ofReal_one,
      sq, RCLike.ofReal_mul]
  have hbound : specNorm (Vᴴ * columnGramDefect X * V) ≤ specNorm (columnGramDefect X) := by
    apply (specNorm_mul_le _ _).trans
    exact mul_le_of_le_one_right (specNorm_nonneg _)
      h.hasOrthonormalCols_right.specNorm_le_one |>.trans
        (h.hasOrthonormalCols_right.specNorm_conjTranspose_mul_le _)
  rw [hcomp, specNorm_diagonal] at hbound
  apply le_trans _ hbound
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  simpa only [RCLike.norm_ofReal, Real.norm_eq_abs] using (norm_le_pi_norm
    (fun j => ((1 - ((newtonSchulz^[k]) (σ j)) ^ 2 : ℝ) : 𝕜)) i)

/-- **Polar error controlled by the Gram defect.** At initial spectral norm at most
$\sqrt{3}$, the Gram defect bounds the distance of each subsequent iterate from the
original polar factor, including rank-deficient inputs. [Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem specNorm_polarFactor_sub_polarSchulzIterate_le (A : Matrix m n 𝕜)
    (hA : specNorm A ≤ √3) (k : ℕ) :
    specNorm (polarFactor A - polarSchulzIterate A (k + 1)) ≤
      specNorm (columnGramDefect (polarSchulzIterate A (k + 1))) := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  have hp (i : Fin A.rank) : 0 < singularValues A i := (singularValues_pos_iff A).mpr i.isLt
  rw [h.polarFactor_eq, h.polarSchulzIterate_eq]
  simp only [if_neg (hp _).ne']
  have he := h.hasOrthonormalCols_left.specNorm_sub_mul_diagonal_mul_conjTranspose
    h.hasOrthonormalCols_right (fun _ : Fin A.rank => (1 : ℝ))
    (fun i : Fin A.rank => (newtonSchulz^[k + 1]) (singularValues A i))
  simp only [RCLike.ofReal_one] at he
  rw [he, ← h.polarSchulzIterate_eq]
  apply le_trans _ (h.norm_defect_coeff_le (k + 1))
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  have hs : singularValues A i ≤ √3 := (le_abs_self _).trans <|
    (norm_le_pi_norm (fun j : Fin A.rank => singularValues A j) i).trans (h.specNorm_eq ▸ hA)
  have hsq : singularValues A i ^ 2 ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hp i]
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm]
  exact (abs_iterate_newtonSchulz_sub_one_le (hp i).le hsq k).trans <|
    (le_abs_self _).trans (norm_le_pi_norm
      (fun j : Fin A.rank => 1 - ((newtonSchulz^[k + 1]) (singularValues A j)) ^ 2) i)

/-- **Polar Gram defect rate.** For any rectangular input with spectral norm at most two,
the defect after $k+1$ steps is at most the first defect norm raised to $2^k$.
[Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem specNorm_columnGramDefect_polarSchulzIterate_le_pow (A : Matrix m n 𝕜)
    (hA : specNorm A ≤ 2) (k : ℕ) :
    specNorm (columnGramDefect (polarSchulzIterate A (k + 1))) ≤
      specNorm (columnGramDefect (polarSchulzIterate A 1)) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    exact (specNorm_columnGramDefect_polarSchulzIterate_succ_le A hA k).trans <| by
      simpa only [← pow_mul, Nat.pow_succ] using
        pow_le_pow_left₀ (specNorm_nonneg _) ih 2

/-- **Convergence of the inverse-free polar iteration.** For every real or complex rectangular
matrix of spectral norm below the square root of three, the cubic iterates converge to its
canonical polar factor, including rank-deficient inputs. [Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem tendsto_polarSchulzIterate (A : Matrix m n 𝕜) (hA : specNorm A < √3) :
    Tendsto (polarSchulzIterate A) atTop (𝓝 (polarFactor A)) := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  have hp (i : Fin A.rank) : 0 < singularValues A i := (singularValues_pos_iff A).mpr i.isLt
  let F (f : Fin A.rank → ℝ) := U * diagonal (fun i => (f i : 𝕜)) * Vᴴ
  have hc : Continuous F := by dsimp [F]; fun_prop
  have hs : Tendsto (fun k (i : Fin A.rank) => (newtonSchulz^[k]) (singularValues A i))
      atTop (𝓝 (fun _ : Fin A.rank => (1 : ℝ))) :=
    tendsto_pi_nhds.mpr fun i => tendsto_iterate_newtonSchulz (hp i) (h.sq_lt_three hA i)
  convert! hc.continuousAt.tendsto.comp hs using 1
  · exact funext fun k => h.polarSchulzIterate_eq k
  · apply congrArg nhds
    simpa only [F, RCLike.ofReal_one, if_neg (hp _).ne'] using h.polarFactor_eq

end NLAlib
