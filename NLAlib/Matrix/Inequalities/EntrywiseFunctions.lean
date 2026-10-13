/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.LinearAlgebra.Vandermonde
public import NLAlib.Matrix.Inequalities.HadamardProduct

/-!
# Entrywise functions of positive semidefinite matrices

By the Schur product theorem, entrywise powers of a positive semidefinite matrix are positive
semidefinite, hence so is the entrywise image under any power series with nonnegative
coefficients, in particular the entrywise exponential. These are the facts behind positive
definite kernels (polynomial and exponential kernels).

## Main results

* `Matrix.PosSemidef.map_pow`: entrywise powers.
* `Matrix.PosSemidef.map_of_hasSum`: entrywise power series with nonnegative coefficients.
* `Matrix.PosSemidef.map_exp`: the entrywise exponential of a real positive semidefinite matrix.
* `Matrix.PosSemidef.posDef_map_exp_iff`: it is positive definite exactly when the rows are
  distinct.
* `Matrix.PosSemidef.map_pow_le_map_pow_of_le`: monotonicity of entrywise powers.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*}

/-! ### Entrywise powers -/

/-- One more entrywise power is one more Hadamard factor. -/
private theorem map_pow_succ (A : Matrix n n 𝕜) (k : ℕ) :
    (A.map fun t => t ^ (k + 1)) = (A.map fun t => t ^ k) ⊙ A := by
  ext i j
  simp only [Matrix.map_apply, Matrix.hadamard_apply, pow_succ]

/-- **Entrywise powers of a positive semidefinite matrix are positive semidefinite.**
[HornJohnson2013, Theorem 7.5.9]. Port of `NLAlib.posSemidef_map_pow`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.map_pow [Finite n] {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (k : ℕ) : (A.map fun t => t ^ k).PosSemidef := by
  induction k with
  | zero =>
    have h := Matrix.posSemidef_vecMulVec_self_star fun _ : n => (1 : 𝕜)
    have e : (A.map fun t => t ^ 0) =
        Matrix.vecMulVec (fun _ => 1) (star fun _ : n => (1 : 𝕜)) := by
      ext i j
      simp only [Matrix.map_apply, pow_zero, Matrix.vecMulVec_apply, Pi.star_apply, star_one,
        mul_one]
    rwa [e]
  | succ k ih =>
    rw [map_pow_succ]
    exact ih.hadamard hA

/-- Entrywise powers are monotone on positive semidefinite matrices: `0 ≤ B ≤ A` gives
`B^{∘k} ≤ A^{∘k}`. [HornJohnson1991, §5.2 context].
Port of `NLAlib.map_pow_le_map_pow_of_posSemidef_le`, there over `ℝ`. -/
theorem _root_.Matrix.PosSemidef.map_pow_le_map_pow_of_le [Finite n] {A B : Matrix n n 𝕜}
    (hB : B.PosSemidef) (h : B ≤ A) (k : ℕ) : (B.map fun t => t ^ k) ≤ A.map fun t => t ^ k := by
  have hA : A.PosSemidef := by
    have h' := hB.add (Matrix.le_iff.mp h)
    rwa [add_sub_cancel] at h'
  induction k with
  | zero =>
    refine le_of_eq ?_
    ext i j
    simp only [Matrix.map_apply, pow_zero]
  | succ k ih =>
    rw [map_pow_succ, map_pow_succ]
    refine le_trans ?_ ((hA.map_pow k).hadamard_le_hadamard_of_le h)
    rw [Matrix.hadamard_comm _ B, Matrix.hadamard_comm _ B]
    exact hB.hadamard_le_hadamard_of_le ih

/-! ### Power series with nonnegative coefficients -/

/-- Convergence of a scalar power series at every entry is convergence of the series of
entrywise powers. -/
private theorem hasSum_smul_map_pow {A : Matrix n n ℝ} {c : ℕ → ℝ} {f : ℝ → ℝ}
    (h : ∀ i j, HasSum (fun k => c k * A i j ^ k) (f (A i j))) :
    HasSum (fun k => c k • A.map fun t => t ^ k) (A.map f) := by
  refine Pi.hasSum.mpr fun i => Pi.hasSum.mpr fun j => ?_
  simpa only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] using h i j

/-- **Entrywise power series with nonnegative coefficients preserve positive semidefiniteness.**
If `f t = ∑ c k t ^ k` with `c k ≥ 0` at every entry of the real positive semidefinite matrix
`A`, then `A.map f` is positive semidefinite.
[HornJohnson2013, Theorem 7.5.9]; [HornJohnson1991, Theorem 6.3.6 context].
Port of `NLAlib.posSemidef_map_of_nonneg_powerSeries`.
Result: schur-product-power-series -/
theorem _root_.Matrix.PosSemidef.map_of_hasSum [Finite n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) {c : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) {f : ℝ → ℝ}
    (h : ∀ i j, HasSum (fun k => c k * A i j ^ k) (f (A i j))) : (A.map f).PosSemidef :=
  Matrix.PosSemidef.of_hasSum (fun k => (hA.map_pow k).smul (hc k)) (hasSum_smul_map_pow h)

/-- The exponential series at a real number, with the coefficient first. -/
private theorem hasSum_inv_factorial_mul_pow (x : ℝ) :
    HasSum (fun k => (k.factorial : ℝ)⁻¹ * x ^ k) (Real.exp x) := by
  simpa only [Real.exp_eq_exp_ℝ, div_eq_mul_inv, mul_comm] using
    NormedSpace.expSeries_div_hasSum_exp x

/-- The entrywise exponential is the sum of the series of entrywise powers. -/
private theorem hasSum_inv_factorial_smul_map_pow (A : Matrix n n ℝ) :
    HasSum (fun k => (k.factorial : ℝ)⁻¹ • A.map fun t => t ^ k) (A.map Real.exp) :=
  hasSum_smul_map_pow fun i j => hasSum_inv_factorial_mul_pow (A i j)

/-- **The entrywise exponential of a positive semidefinite matrix is positive semidefinite.**
[HornJohnson2013, Theorem 7.5.9]. Port of `NLAlib.posSemidef_map_exp`. -/
theorem _root_.Matrix.PosSemidef.map_exp [Finite n] {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef :=
  hA.map_of_hasSum (fun k => inv_nonneg.mpr k.factorial.cast_nonneg) fun i j =>
    hasSum_inv_factorial_mul_pow (A i j)

/-- The entrywise exponential is monotone on positive semidefinite matrices.
Port of `NLAlib.map_exp_le_map_exp_of_posSemidef_le`. -/
theorem _root_.Matrix.PosSemidef.map_exp_le_map_exp_of_le [Finite n] {A B : Matrix n n ℝ}
    (hB : B.PosSemidef) (h : B ≤ A) : B.map Real.exp ≤ A.map Real.exp := by
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_hasSum (fun k => ?_)
    ((hasSum_inv_factorial_smul_map_pow A).sub (hasSum_inv_factorial_smul_map_pow B)))
  rw [← smul_sub]
  exact (Matrix.le_iff.mp (hB.map_pow_le_map_pow_of_le h k)).smul
    (inv_nonneg.mpr k.factorial.cast_nonneg)

/-! ### Strict positivity of the entrywise exponential -/

/-- An entrywise power of a rank-one Gram matrix is the rank-one Gram matrix of the powers. -/
private theorem map_pow_vecMulVec (b : n → ℝ) (k : ℕ) :
    ((Matrix.vecMulVec b b).map fun t => t ^ k) =
      Matrix.vecMulVec (fun i => b i ^ k) (star fun i => b i ^ k) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.vecMulVec_apply, mul_pow, star_trivial]

/-- The quadratic form of the first `N` terms of the entrywise exponential series of a rank-one
Gram matrix is a weighted sum of squares of moments. -/
private theorem quadForm_sum_inv_factorial_smul_map_pow_vecMulVec [Fintype n] (b x : n → ℝ)
    (N : ℕ) :
    quadForm (∑ k ∈ Finset.range N,
      (k.factorial : ℝ)⁻¹ • (Matrix.vecMulVec b b).map fun t => t ^ k) x =
      ∑ k ∈ Finset.range N, (k.factorial : ℝ)⁻¹ * (∑ i, x i * b i ^ k) ^ 2 := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, quadForm_zero_left]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, quadForm_add_left, ih, map_pow_vecMulVec,
      quadForm_smul_left, quadForm_vecMulVec_star]
    simp only [star_trivial, RCLike.ofReal_real_eq_id, id_eq, Real.norm_eq_abs, sq_abs,
      dotProduct, mul_comm]

/-- The first `card n` terms of the entrywise exponential series of the Gram matrix of distinct
real numbers already form a positive definite matrix, by the Vandermonde determinant. -/
private theorem posDef_sum_inv_factorial_smul_map_pow_vecMulVec [Fintype n] {b : n → ℝ}
    (hb : Function.Injective b) :
    (∑ k ∈ Finset.range (Fintype.card n),
      (k.factorial : ℝ)⁻¹ • (Matrix.vecMulVec b b).map fun t => t ^ k).PosDef := by
  have hBB : (Matrix.vecMulVec b b).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star b
  have hH := Matrix.posSemidef_sum (Finset.range (Fintype.card n)) fun k _ =>
    (hBB.map_pow k).smul (inv_nonneg.mpr (k.factorial.cast_nonneg (α := ℝ)))
  refine posDef_iff_quadForm_pos.mpr ⟨hH.isHermitian, fun x hx => ?_⟩
  refine lt_of_le_of_ne (hH.quadForm_nonneg x) fun h0 => hx ?_
  rw [quadForm_sum_inv_factorial_smul_map_pow_vecMulVec] at h0
  have hmom (k : Fin (Fintype.card n)) : ∑ i, x i * b i ^ (k : ℕ) = 0 := by
    have hk := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (inv_nonneg.mpr (j.factorial.cast_nonneg (α := ℝ))) (sq_nonneg _)).mp h0.symm
      k (Finset.mem_range.mpr k.isLt)
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hk).resolve_left
      (inv_ne_zero (Nat.cast_ne_zero.mpr (k : ℕ).factorial_ne_zero)))
  let e : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
  have hzero : (fun i => x (e i)) = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (hb.comp e.injective) fun k => by
      rw [← hmom k]
      exact e.sum_comp fun i => x i * b i ^ (k : ℕ)
  funext i
  simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using congrFun hzero (e.symm i)

/-- The entrywise exponential of the Gram matrix of distinct real numbers is positive
definite. -/
private theorem posDef_map_exp_vecMulVec [Finite n] {b : n → ℝ} (hb : Function.Injective b) :
    ((Matrix.vecMulVec b b).map Real.exp).PosDef := by
  have := Fintype.ofFinite n
  have hBB : (Matrix.vecMulVec b b).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star b
  have hle : (∑ k ∈ Finset.range (Fintype.card n),
      (k.factorial : ℝ)⁻¹ • (Matrix.vecMulVec b b).map fun t => t ^ k) ≤
      (Matrix.vecMulVec b b).map Real.exp :=
    sum_le_hasSum _ (fun k _ => Matrix.nonneg_iff_posSemidef.mpr
        ((hBB.map_pow k).smul (inv_nonneg.mpr (k.factorial.cast_nonneg (α := ℝ)))))
      (hasSum_inv_factorial_smul_map_pow _)
  have h := (posDef_sum_inv_factorial_smul_map_pow_vecMulVec hb).add_posSemidef
    (Matrix.le_iff.mp hle)
  rwa [add_sub_cancel] at h

/-- A real matrix with distinct rows has distinct entries in some combination of its columns:
finitely many hyperplanes do not cover a real vector space. -/
private theorem exists_injective_mulVec [Fintype n] {A : Matrix n n ℝ}
    (hA : Function.Injective A.row) :
    ∃ z : n → ℝ, Function.Injective (A *ᵥ z) := by
  let f (p : {p : n × n // p.1 ≠ p.2}) : Module.Dual ℝ (n → ℝ) :=
    dotProductBilin ℝ ℝ (A.row p.1.1 - A.row p.1.2)
  have hf (p : {p : n × n // p.1 ≠ p.2}) : ∃ z, f p z ≠ 0 := by
    by_contra hn
    exact p.2 (hA (sub_eq_zero.mp (dotProduct_eq_zero _ (not_exists_not.mp hn))))
  obtain ⟨z, hz⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  refine ⟨z, fun i j hij => by_contra fun hne => hz ⟨(i, j), hne⟩ ?_⟩
  change (A.row i - A.row j) ⬝ᵥ z = 0
  rw [sub_dotProduct]
  exact sub_eq_zero.mpr hij

/-- A real positive semidefinite matrix with distinct rows dominates the Gram matrix of distinct
real numbers. -/
private theorem exists_injective_vecMulVec_le [Finite n] {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (hrows : Function.Injective A.row) :
    ∃ b : n → ℝ, Function.Injective b ∧ Matrix.vecMulVec b b ≤ A := by
  have := Fintype.ofFinite n
  obtain ⟨z, hz⟩ := exists_injective_mulVec hrows
  have hq : 0 ≤ quadForm A z := hA.quadForm_nonneg z
  have hq' : (0 : ℝ) < 1 + quadForm A z := by linarith
  refine ⟨(1 + quadForm A z)⁻¹ • A *ᵥ z, fun i j hij => hz ?_, ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul, mul_right_inj' (inv_ne_zero hq'.ne')] using hij
  have hB : (Matrix.vecMulVec ((1 + quadForm A z)⁻¹ • A *ᵥ z)
      (star ((1 + quadForm A z)⁻¹ • A *ᵥ z))).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star _
  rw [← star_trivial ((1 + quadForm A z)⁻¹ • A *ᵥ z)]
  refine (hB.isHermitian.le_iff_re_quadForm_le hA.isHermitian).mpr fun x => ?_
  have hcs := hA.norm_sq_star_dotProduct_mulVec_le x z
  have hx : 0 ≤ quadForm A x := hA.quadForm_nonneg x
  rw [quadForm_vecMulVec_star]
  simp only [star_trivial, RCLike.ofReal_real_eq_id, id_eq, Real.norm_eq_abs, sq_abs,
    RCLike.re_to_real, dotProduct_smul, smul_eq_mul, mul_pow, dotProduct_comm _ x] at hcs ⊢
  rw [inv_pow, inv_mul_le_iff₀ (pow_pos hq' 2)]
  nlinarith [mul_nonneg hx hq, mul_nonneg (mul_nonneg hx hq) hq]

/-- **The entrywise exponential of a positive semidefinite matrix is positive definite exactly
when its rows are distinct.** [HornJohnson2013, Theorem 7.5.9 context].
Port of `NLAlib.posDef_map_exp_iff_rows_injective`.
Result: exponential-kernel -/
theorem _root_.Matrix.PosSemidef.posDef_map_exp_iff [Finite n] {A : Matrix n n ℝ}
    (hA : A.PosSemidef) : (A.map Real.exp).PosDef ↔ Function.Injective A.row := by
  classical
  have := Fintype.ofFinite n
  refine ⟨fun h i j hij => ?_, fun hrows => ?_⟩
  · refine (Matrix.linearIndependent_rows_iff_isUnit.mpr h.isUnit).injective ?_
    funext k
    exact congrArg Real.exp (congrFun hij k)
  · obtain ⟨b, hb, hle⟩ := exists_injective_vecMulVec_le hA hrows
    have hBB : (Matrix.vecMulVec b b).PosSemidef := by
      simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star b
    have h := (posDef_map_exp_vecMulVec hb).add_posSemidef
      (Matrix.le_iff.mp (hBB.map_exp_le_map_exp_of_le hle))
    rwa [add_sub_cancel] at h

/-- The Gram matrix `exp (b i * b j)` of distinct real numbers is positive definite.
Port of `NLAlib.posDef_sum_inv_factorial_map_pow_vecMulVec_of_injective`, in the limit. -/
theorem posDef_of_exp_mul [Finite n] {b : n → ℝ} (hb : Function.Injective b) :
    (Matrix.of fun i j => Real.exp (b i * b j)).PosDef :=
  posDef_map_exp_vecMulVec hb

end NLAlib
