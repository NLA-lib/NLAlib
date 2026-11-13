/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Matrix.Functions.SingularValueFilters
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FieldSimp

/-!
# Rectangular polar Newton iteration

Inverse averaging preserves singular directions and rank. The scalar Cayley coordinate squares
at each step. The argument adapts the original NLAlib atlas, commit 77514ce.

## Main results

* `NLAlib.IsSVD.polarNewtonIterate_eq`: closed form in a compact singular frame.
* `NLAlib.IsSVD.specNorm_polarFactor_sub_polarNewtonIterate_le`: spectral-norm bound.
* `NLAlib.tendsto_polarNewtonIterate`: convergence on rectangular matrices.
-/

@[expose] public section

open Filter Matrix
open scoped Matrix.Norms.L2Operator Topology
namespace NLAlib

/-- The positive scalar Newton recurrence in each fixed singular direction. -/
private noncomputable def polarNewtonScalar (s : ℝ) : ℕ → ℝ
  | 0 => s
  | k + 1 => (polarNewtonScalar s k + (polarNewtonScalar s k)⁻¹) / 2

/-- Positivity is preserved by every scalar Newton step. -/
private theorem polarNewtonScalar_pos {s : ℝ} (hs : 0 < s) (k : ℕ) :
    0 < polarNewtonScalar s k := by
  induction k with
  | zero => exact hs
  | succ k ih => dsimp only [polarNewtonScalar]; positivity

/-- The Cayley coordinate of a positive number lies strictly between minus
one and one. -/
private theorem abs_cayley_lt_one {s : ℝ} (hs : 0 < s) : |(s - 1) / (s + 1)| < 1 := by
  rw [abs_div, abs_of_pos (by linarith : 0 < s + 1), div_lt_one (by linarith)]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- A scalar Newton step squares its Cayley coordinate exactly. -/
private theorem cayley_polarNewton_step {s : ℝ} (hs : 0 < s) :
    (((s + s⁻¹) / 2) - 1) / (((s + s⁻¹) / 2) + 1) = ((s - 1) / (s + 1)) ^ 2 := by
  have hs0 : s ≠ 0 := hs.ne'
  have hp : s + 1 ≠ 0 := by linarith
  have hd : (s + s⁻¹) / 2 + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The Cayley coordinate of the actual recurrence is its initial coordinate
raised to `2^k`. -/
private theorem cayley_polarNewtonScalar {s : ℝ} (hs : 0 < s) (k : ℕ) :
    (polarNewtonScalar s k - 1) / (polarNewtonScalar s k + 1) =
      ((s - 1) / (s + 1)) ^ (2 ^ k) := by
  induction k with
  | zero => simp [polarNewtonScalar]
  | succ k ih =>
    rw [polarNewtonScalar, cayley_polarNewton_step (polarNewtonScalar_pos hs k), ih,
      ← pow_mul, pow_succ]

/-- Exact closed form of every scalar iterate, including the initial value.
Higham (1986), equations (3.4)–(3.7). -/
private theorem polarNewtonScalar_eq {s : ℝ} (hs : 0 < s) (k : ℕ) :
    polarNewtonScalar s k =
      (1 + ((s - 1) / (s + 1)) ^ (2 ^ k)) /
        (1 - ((s - 1) / (s + 1)) ^ (2 ^ k)) := by
  rw [← cayley_polarNewtonScalar hs k]
  have hp := polarNewtonScalar_pos hs k
  have hd : polarNewtonScalar s k + 1 ≠ 0 := by linarith
  have hn : 1 - (polarNewtonScalar s k - 1) / (polarNewtonScalar s k + 1) ≠ 0 := by
    rw [ne_eq, sub_eq_zero, eq_div_iff hd]
    intro h
    linarith
  field_simp
  ring

/-- Every positive scalar starting point converges to one. -/
private theorem tendsto_polarNewtonScalar {s : ℝ} (hs : 0 < s) :
    Tendsto (polarNewtonScalar s) atTop (𝓝 1) := by
  have hc : ‖(s - 1) / (s + 1)‖ < 1 := abs_cayley_lt_one hs
  have ht := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).add ht).div
    ((tendsto_const_nhds (x := (1 : ℝ))).sub ht)
    (by norm_num : (1 : ℝ) - 0 ≠ 0))
  have he : (fun k => (1 + ((s - 1) / (s + 1)) ^ (2 ^ k)) /
      (1 - ((s - 1) / (s + 1)) ^ (2 ^ k))) = polarNewtonScalar s := by
    funext k
    exact (polarNewtonScalar_eq hs k).symm
  have hlim' : Tendsto (fun k => (1 + ((s - 1) / (s + 1)) ^ (2 ^ k)) /
      (1 - ((s - 1) / (s + 1)) ^ (2 ^ k))) atTop (𝓝 1) := by
    convert! hlim using 1
    norm_num
  rwa [he] at hlim'

/-- Uniform explicit Newton error for any bound on the initial Cayley coordinate.
The bound retains the denominator needed at the initial iteration.
Higham (1986), §3.2. -/
private theorem abs_polarNewtonScalar_sub_one_le {s r : ℝ} (hs : 0 < s)
    (hr : 0 ≤ r) (hr1 : r < 1) (hcr : |(s - 1) / (s + 1)| ≤ r) (k : ℕ) :
    |polarNewtonScalar s k - 1| ≤ 2 * r ^ (2 ^ k) / (1 - r ^ (2 ^ k)) := by
  let c := ((s - 1) / (s + 1)) ^ (2 ^ k)
  have hrp : r ^ (2 ^ k) < 1 := pow_lt_one₀ hr hr1 (by positivity)
  have hcp : |c| ≤ r ^ (2 ^ k) := by
    simpa only [c, abs_pow] using pow_le_pow_left₀ (abs_nonneg _) hcr (2 ^ k)
  have hden : 0 < 1 - c := by have := le_abs_self c; linarith
  have he : polarNewtonScalar s k - 1 = 2 * c / (1 - c) := by
    rw [polarNewtonScalar_eq hs]
    change (1 + c) / (1 - c) - 1 = _
    field_simp
    ring
  rw [he, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hden]
  apply div_le_div₀ (mul_nonneg (by norm_num) (pow_nonneg hr _))
    (mul_le_mul_of_nonneg_left hcp (by norm_num)) (by linarith)
  have := le_abs_self c
  linarith

variable {𝕜 m n r : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

/-- The inverse-averaging iteration on rectangular real or complex matrices.
[Higham2008, §8.3]; the adjoint of the pseudoinverse gives the fixed-rank extension.
Algorithm: polar-newton -/
noncomputable def polarNewtonIterate (A : Matrix m n 𝕜) : ℕ → Matrix m n 𝕜
  | 0 => A
  | k + 1 => (2⁻¹ : ℝ) • (polarNewtonIterate A k + (pinv (polarNewtonIterate A k))ᴴ)

private theorem polarNewtonScalar_nonneg {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    0 ≤ polarNewtonScalar s k := by
  induction k with
  | zero => exact hs
  | succ k ih => simp only [polarNewtonScalar]; positivity

private theorem polarNewtonScalar_eq_zero_iff {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    polarNewtonScalar s k = 0 ↔ s = 0 := by
  rcases hs.eq_or_lt with he | hp
  · subst s
    induction k with
    | zero => simp [polarNewtonScalar]
    | succ k ih => simp [polarNewtonScalar, ih.mpr rfl]
  · simp only [(polarNewtonScalar_pos hp k).ne', hp.ne']

private theorem isSVD_polarNewtonIterate {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (k : ℕ) :
    IsSVD (polarNewtonIterate A k) U (fun i => polarNewtonScalar (σ i) k) V := by
  induction k with
  | zero => exact h
  | succ k hk =>
    refine ⟨h.hasOrthonormalCols_left, h.hasOrthonormalCols_right,
      fun i => polarNewtonScalar_nonneg (h.nonneg i) _, ?_⟩
    rw [polarNewtonIterate, hk.pinv_eq, hk.eq]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_diagonal_ofReal, ← Matrix.mul_assoc]
    rw [← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.smul_mul, ← Matrix.mul_smul]
    rw [Matrix.diagonal_add, ← Matrix.diagonal_smul]
    congr 2
    apply congrArg Matrix.diagonal
    funext i
    simp only [Pi.smul_apply, RCLike.real_smul_eq_coe_mul, polarNewtonScalar,
      RCLike.ofReal_add, RCLike.ofReal_inv, RCLike.ofReal_ofNat,
      div_eq_inv_mul, RCLike.ofReal_mul]


/-- Rank is preserved by every rectangular polar Newton iterate, including a zero input.
[Higham2008, §8.3]. -/
theorem rank_polarNewtonIterate (A : Matrix m n 𝕜) (k : ℕ) :
    (polarNewtonIterate A k).rank = A.rank := by
  classical
  let h := isSVD_svdU_svdV A
  rw [(isSVD_polarNewtonIterate h k).rank_eq, h.rank_eq]
  congr 1
  apply Finset.filter_congr
  intro i _
  exact not_congr (polarNewtonScalar_eq_zero_iff (h.nonneg i) k)

/-- **Polar Newton closed form.** In a compact SVD with strictly positive singular values,
the actual kth iterate retains the singular directions and applies the scalar Cayley formula.
For $c_i=(\sigma_i-1)/(\sigma_i+1)$ the new coefficients are
$$\frac{1+c_i^{2^k}}{1-c_i^{2^k}}.$$ [Higham2008, §8.3].
Result: polar-newton-iteration -/
theorem IsSVD.polarNewtonIterate_eq {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (hσ : ∀ i, 0 < σ i) (k : ℕ) :
    polarNewtonIterate A k = U * diagonal (fun i =>
      (((1 + ((σ i - 1) / (σ i + 1)) ^ (2 ^ k)) /
        (1 - ((σ i - 1) / (σ i + 1)) ^ (2 ^ k)) : ℝ) : 𝕜)) * Vᴴ := by
  simp only [← polarNewtonScalar_eq (hσ _) k]
  exact (isSVD_polarNewtonIterate h k).eq

variable [DecidableEq n]

private theorem IsSVD.polarFactor_eq_of_pos {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (hσ : ∀ i, 0 < σ i) :
    polarFactor A = U * diagonal (fun _ : r => (1 : 𝕜)) * Vᴴ := by
  simpa only [if_neg (hσ _).ne'] using h.polarFactor_eq

/-- **Rectangular polar Newton error bound.** For a compact SVD with positive singular
values, bound every initial Cayley modulus by a number between zero and one, the upper
endpoint excluded. The polar-factor error is at most the resulting
double-exponential bound $$\frac{2 b^{2^k}}{1-b^{2^k}}.$$ [Higham2008, §8.3].
Result: polar-newton-iteration -/
theorem IsSVD.specNorm_polarFactor_sub_polarNewtonIterate_le {A : Matrix m n 𝕜}
    {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V)
    (hσ : ∀ i, 0 < σ i) {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hc : ∀ i, |(σ i - 1) / (σ i + 1)| ≤ b) (k : ℕ) :
    specNorm (polarFactor A - polarNewtonIterate A k) ≤
      2 * b ^ (2 ^ k) / (1 - b ^ (2 ^ k)) := by
  have hp := pow_lt_one₀ hb hb1 (by positivity : 2 ^ k ≠ 0)
  rw [specNorm_sub_comm, h.polarFactor_eq_of_pos hσ, (isSVD_polarNewtonIterate h k).eq]
  have he := h.hasOrthonormalCols_left.specNorm_sub_mul_diagonal_mul_conjTranspose
    h.hasOrthonormalCols_right (fun i => polarNewtonScalar (σ i) k) (fun _ => 1)
  simp only [RCLike.ofReal_one] at he
  rw [he]
  apply (pi_norm_le_iff_of_nonneg
    (div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hb _)) (sub_nonneg.mpr hp.le))).mpr
  exact fun i => abs_polarNewtonScalar_sub_one_le (hσ i) hb hb1 (hc i) k

/-- The sup norm of the Cayley coordinates $(\sigma_i-1)/(\sigma_i+1)$ over the positive
singular values of the input. It is zero when the matrix has rank zero.
[Higham2008, §8.3]. -/
noncomputable def polarNewtonCayleyNorm (A : Matrix m n 𝕜) : ℝ :=
  ‖fun i : Fin A.rank => (singularValues A i - 1) / (singularValues A i + 1)‖

omit [DecidableEq n] in
/-- The initial Cayley modulus of any real or complex rectangular matrix is less than one.
[Higham2008, §8.3]. -/
theorem polarNewtonCayleyNorm_lt_one (A : Matrix m n 𝕜) : polarNewtonCayleyNorm A < 1 := by
  apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
  exact fun i => abs_cayley_lt_one ((singularValues_pos_iff A).mpr i.isLt)

/-- **Polar Newton rate from the initial matrix.** For a rectangular matrix let $b$ be the
largest absolute Cayley coordinate on its positive singular values, with $b=0$ at rank zero.
The polar error after $k$ updates is at most
$$\frac{2 b^{2^k}}{1-b^{2^k}}.$$ [Higham2008, §8.3].
Result: polar-newton-iteration -/
theorem specNorm_polarFactor_sub_polarNewtonIterate_le (A : Matrix m n 𝕜) (k : ℕ) :
    specNorm (polarFactor A - polarNewtonIterate A k) ≤
      2 * (polarNewtonCayleyNorm A) ^ (2 ^ k) / (1 - (polarNewtonCayleyNorm A) ^ (2 ^ k)) := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  exact h.specNorm_polarFactor_sub_polarNewtonIterate_le
    (fun i => (singularValues_pos_iff A).mpr i.isLt) (norm_nonneg _)
    (polarNewtonCayleyNorm_lt_one A)
    (fun i => norm_le_pi_norm (fun j : Fin A.rank =>
      (singularValues A j - 1) / (singularValues A j + 1)) i) k

/-- **Rectangular polar Newton convergence.** The actual inverse-averaging iterates tend to
the canonical polar factor of any real or complex matrix, including rank-deficient and empty
inputs. [Higham2008, §8.3].
Result: polar-newton-iteration -/
theorem tendsto_polarNewtonIterate (A : Matrix m n 𝕜) :
    Tendsto (polarNewtonIterate A) atTop (𝓝 (polarFactor A)) := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  have hp (i : Fin A.rank) : 0 < singularValues A i := (singularValues_pos_iff A).mpr i.isLt
  let F (f : Fin A.rank → ℝ) := U * diagonal (fun i => (f i : 𝕜)) * Vᴴ
  have hc : Continuous F := by dsimp [F]; fun_prop
  have hs : Tendsto (fun k (i : Fin A.rank) => polarNewtonScalar (singularValues A i) k)
      atTop (𝓝 (fun _ : Fin A.rank => (1 : ℝ))) :=
    tendsto_pi_nhds.mpr (fun i => tendsto_polarNewtonScalar (hp i))
  convert! hc.continuousAt.tendsto.comp hs using 1
  · exact funext fun k => (isSVD_polarNewtonIterate h k).eq
  · apply congrArg nhds
    simpa only [F, RCLike.ofReal_one] using h.polarFactor_eq_of_pos hp

end NLAlib
