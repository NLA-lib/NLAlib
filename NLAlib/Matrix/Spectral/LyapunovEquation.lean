/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.HermitianPart
public import NLAlib.Matrix.Inequalities.Order
public import NLAlib.Matrix.Norms.UnitarilyInvariant
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Continuous Lyapunov equations

The condition `hermitianPart A ≤ (-a) • 1` with $a>0$ gives unique solutions of
$\mathbf{A}\mathbf{X}+\mathbf{X}\mathbf{A}^{\mathsf{H}}=-\mathbf{Q}$,
preservation of Hermitian symmetry and positive semidefiniteness, and inverse bounds with
constant $1/(2a)$. The coefficient matrix may be nonnormal. All results include empty index types.

Adapted from `tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`,
`Matrix/Equations/LyapunovCoercivity.lean` and `LyapunovDissipative.lean`, using native Loewner
hypotheses and direct matrix equations.

## Main results

* `NLAlib.frobInner_mul_add_mul_conjTranspose_le`: Frobenius coercivity.
* `NLAlib.SymmetricGauge.matrixNorm_le_div_of_hermitianPart_le`: inverse estimate for every
  unitarily invariant norm and arbitrary matrix errors.
* `NLAlib.existsUnique_mul_add_mul_conjTranspose_eq_neg`: a unique solution for every forcing.
* `Matrix.IsHermitian.isHermitian_of_mul_add_mul_conjTranspose_eq_neg`: Hermitian preservation.
* `Matrix.PosSemidef.posSemidef_of_mul_add_mul_conjTranspose_eq_neg`: positivity preservation.
-/

@[expose] public section

open scoped Matrix MatrixOrder ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Lyapunov coercivity, Frobenius inner product.** If
$\tfrac12(\mathbf{A}+\mathbf{A}^{\mathsf{H}})\preceq-a\mathbf{I}$, then every matrix
$\mathbf{E}$ satisfies
$$\langle\mathbf{E},\mathbf{A}\mathbf{E}+\mathbf{E}\mathbf{A}^{\mathsf{H}}
\rangle_{\mathsf{F}}\le-2a\|\mathbf{E}\|_{\mathsf{F}}^2\,.$$
Here $a$ is any real number; no positivity or Hermitian assumption on $\mathbf{E}$ is needed.
No printed source. Adapted from `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`, `frobInner_lyapunov_le`.
Result: lyapunov-coercivity -/
theorem frobInner_mul_add_mul_conjTranspose_le {A : Matrix n n 𝕜} {a : ℝ}
    (hA : hermitianPart A ≤ (-a) • (1 : Matrix n n 𝕜)) (E : Matrix n n 𝕜) :
    frobInner E (A * E + E * Aᴴ) ≤ -2 * a * frobNorm E ^ 2 := by
  have hleft (F : Matrix n n 𝕜) : frobInner F (A * F) ≤ -a * frobNorm F ^ 2 := by
    have hpair : frobInner F (hermitianPart A * F) = frobInner F (A * F) := by
      have hadj : frobInner F (Aᴴ * F) = frobInner F (A * F) := by
        rw [← frobInner_mul_left A F F, frobInner_comm (A * F) F]
      rw [hermitianPart, Matrix.smul_mul, Matrix.add_mul, frobInner_smul_right,
        frobInner_add_right, hadj]
      ring
    have ht := re_trace_le_re_trace_of_le
      (conjTranspose_mul_mul_le_conjTranspose_mul_mul hA F)
    have htr : frobInner F (hermitianPart A * F) ≤ -a * frobNorm F ^ 2 := by
      simpa only [frobInner_eq_re_trace, ← Matrix.mul_assoc, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, Matrix.trace_smul, RCLike.smul_re,
        ← frobNorm_sq_eq_re_trace] using ht
    rwa [hpair] at htr
  have hl := hleft E
  have hr := hleft Eᴴ
  have he : frobInner E (E * Aᴴ) = frobInner Eᴴ (A * Eᴴ) := by
    rw [← frobInner_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  rw [frobNorm_conjTranspose] at hr
  rw [frobInner_add_right, he]
  linarith

private theorem IsSVD.mul_le_neg_re_conjTranspose_mul_add_mul_mul
    {r : Type*} [Fintype r] [DecidableEq r] {E : Matrix n n 𝕜}
    {U V : Matrix n r 𝕜} {σ : r → ℝ} (hS : IsSVD E U σ V)
    {A : Matrix n n 𝕜} {a : ℝ}
    (hA : hermitianPart A ≤ (-a) • (1 : Matrix n n 𝕜)) (i : r) :
    2 * a * σ i ≤ -RCLike.re ((Uᴴ * (A * E + E * Aᴴ) * V) i i) := by
  have hd (W : Matrix n r 𝕜) (hW : HasOrthonormalCols W) :
      RCLike.re ((Wᴴ * A * W) i i) ≤ -a := by
    have h := (RCLike.nonneg_iff.mp
      ((Matrix.le_iff.mp (hW.hermitianPart_conjTranspose_mul_mul_le hA)).diag_nonneg
        (i := i))).1
    simp only [Matrix.sub_apply, map_sub, Matrix.smul_apply, Matrix.one_apply_eq,
      RCLike.smul_re, RCLike.one_re, mul_one, hermitianPart, Matrix.add_apply,
      Matrix.conjTranspose_apply, map_add, RCLike.star_def, RCLike.conj_re] at h
    linarith
  have hR : Uᴴ * (A * E + E * Aᴴ) * V =
      (Uᴴ * A * U) * Matrix.diagonal (fun j => ((σ j : ℝ) : 𝕜)) +
        Matrix.diagonal (fun j => ((σ j : ℝ) : 𝕜)) * (Vᴴ * A * V)ᴴ := by
    rw [Matrix.mul_add, Matrix.add_mul]
    congr 1
    · calc Uᴴ * (A * E) * V = (Uᴴ * A) * (E * V) := by
            simp only [Matrix.mul_assoc]
        _ = (Uᴴ * A * U) * Matrix.diagonal (fun j => ((σ j : ℝ) : 𝕜)) := by
            rw [hS.mul_right_eq]
            simp only [Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc Uᴴ E Aᴴ, hS.conjTranspose_mul_eq]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hR, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, map_add,
    RCLike.re_mul_ofReal, RCLike.re_ofReal_mul, Matrix.conjTranspose_apply,
    RCLike.star_def, RCLike.conj_re]
  have hl := mul_le_mul_of_nonneg_right (hd U hS.hasOrthonormalCols_left) (hS.nonneg i)
  have hr := mul_le_mul_of_nonneg_right (hd V hS.hasOrthonormalCols_right) (hS.nonneg i)
  nlinarith

private theorem mul_kyFanNorm_le_of_hermitianPart_le {A : Matrix n n 𝕜} {a : ℝ}
    (hA : hermitianPart A ≤ (-a) • (1 : Matrix n n 𝕜)) (E : Matrix n n 𝕜) (k : ℕ) :
    2 * a * kyFanNorm k E ≤ kyFanNorm k (A * E + E * Aᴴ) := by
  classical
  rw [← kyFanNorm_min_card k E, ← kyFanNorm_min_card k (A * E + E * Aᴴ), min_self]
  let j := min k (Fintype.card n)
  have hj : j ≤ Fintype.card n := min_le_right _ _
  obtain ⟨U, V, hS⟩ := exists_isSVD E E.rank_le_card_width le_rfl le_rfl
  have hU : HasOrthonormalCols (U.submatrix id (Fin.castLE hj)) :=
    hS.hasOrthonormalCols_left.submatrix (Equiv.refl n) (Fin.castLE_injective hj)
  have hV : HasOrthonormalCols (V.submatrix id (Fin.castLE hj)) :=
    hS.hasOrthonormalCols_right.submatrix (Equiv.refl n) (Fin.castLE_injective hj)
  have ht := re_trace_conjTranspose_mul_mul_le_kyFanNorm (-(A * E + E * Aᴴ)) hU hV
  rw [Fintype.card_fin, kyFanNorm_neg] at ht
  have htrace : RCLike.re (((U.submatrix id (Fin.castLE hj))ᴴ * (-(A * E + E * Aᴴ)) *
      V.submatrix id (Fin.castLE hj)).trace) =
      ∑ i : Fin j, -RCLike.re ((Uᴴ * (A * E + E * Aᴴ) * V)
        (Fin.castLE hj i) (Fin.castLE hj i)) := by
    rw [conjTranspose_submatrix_mul_mul_submatrix, Matrix.mul_neg, Matrix.neg_mul]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply,
      Matrix.neg_apply, map_sum, map_neg]
  rw [htrace] at ht
  have hsum : 2 * a * kyFanNorm j E ≤
      ∑ i : Fin j, -RCLike.re ((Uᴴ * (A * E + E * Aᴴ) * V)
        (Fin.castLE hj i) (Fin.castLE hj i)) := by
    rw [kyFanNorm, ← Fin.sum_univ_eq_sum_range (fun i => singularValues E i) j, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact hS.mul_le_neg_re_conjTranspose_mul_add_mul_mul hA (Fin.castLE hj i)
  exact hsum.trans ht

/-- **Lyapunov coercivity, unitarily invariant inverse estimate.** For $a>0$ and
$\tfrac12(\mathbf{A}+\mathbf{A}^{\mathsf{H}})\preceq-a\mathbf{I}$, every matrix
$\mathbf{E}$ and every symmetric gauge $\Phi$ satisfy
$$\|\mathbf{E}\|_{\Phi}\le
\frac{\|\mathbf{A}\mathbf{E}+\mathbf{E}\mathbf{A}^{\mathsf{H}}\|_{\Phi}}{2a}\,.$$
This includes Frobenius, spectral, and nuclear norms without requiring Hermitian errors.
Applying it to the difference between an exact and an approximate solution bounds the error
by the residual. The constant is attained for $\mathbf{A}=-a\mathbf{I}$ on a nonempty
index type. No printed source. Generalizes the Frobenius and Hermitian spectral estimates in
`tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`,
`frobNorm_le_lyapunov_div` and `specNorm_le_lyapunov_div`.
Result: lyapunov-coercivity -/
theorem SymmetricGauge.matrixNorm_le_div_of_hermitianPart_le (Φ : SymmetricGauge)
    {A : Matrix n n 𝕜} {a : ℝ} (ha : 0 < a)
    (hA : hermitianPart A ≤ (-a) • (1 : Matrix n n 𝕜)) (E : Matrix n n 𝕜) :
    Φ.matrixNorm E ≤ Φ.matrixNorm (A * E + E * Aᴴ) / (2 * a) := by
  have ha' : 0 < 2 * a := by positivity
  have h := Φ.matrixNorm_le_of_forall_kyFanNorm_le
    (A := ((2 * a : ℝ) : 𝕜) • E) (B := A * E + E * Aᴴ) fun k => by
      rw [kyFanNorm_smul, RCLike.norm_ofReal, abs_of_pos ha']
      exact mul_kyFanNorm_le_of_hermitianPart_le hA E k
  rw [Φ.matrixNorm_smul, RCLike.norm_ofReal, abs_of_pos ha'] at h
  exact (le_div_iff₀ ha').2 (by simpa only [mul_comm] using h)

/-- **Continuous Lyapunov equation, unique solvability.** If $a>0$ and
$\tfrac12(\mathbf{A}+\mathbf{A}^{\mathsf{H}})\preceq-a\mathbf{I}$, every forcing
$\mathbf{Q}$ has a unique solution of
$\mathbf{A}\mathbf{X}+\mathbf{X}\mathbf{A}^{\mathsf{H}}=-\mathbf{Q}$.
The coefficient and forcing need not be Hermitian, and the index type may be empty.
No printed source. Adapted from `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`, `existsUnique_lyapunov_of_quadratic_bound`.
Result: lyapunov-equation -/
theorem existsUnique_mul_add_mul_conjTranspose_eq_neg {A : Matrix n n 𝕜} {a : ℝ}
    (ha : 0 < a) (hA : hermitianPart A ≤ (-a) • (1 : Matrix n n 𝕜))
    (Q : Matrix n n 𝕜) : ∃! X : Matrix n n 𝕜, A * X + X * Aᴴ = -Q := by
  let L : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜 :=
    { toFun := fun E => A * E + E * Aᴴ
      map_add' := fun E F => by simp only [Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c E => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply] }
  have hi : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro E hE
    have hb := (lpGauge 2).matrixNorm_le_div_of_hermitianPart_le ha hA E
    simp only [lpGauge_two_matrixNorm] at hb
    change A * E + E * Aᴴ = 0 at hE
    rw [hE, frobNorm_zero, zero_div] at hb
    exact frobNorm_eq_zero_iff.mp (le_antisymm hb (frobNorm_nonneg E))
  have hs : Function.Surjective L := LinearMap.injective_iff_surjective.mp hi
  obtain ⟨X, hX⟩ := hs (-Q)
  refine ⟨X, hX, ?_⟩
  intro Y hY
  exact hi (hY.trans hX.symm)

/-- Hermitian forcing $\mathbf{Q}$ has a Hermitian Lyapunov solution $\mathbf{X}$ when
$a>0$, $\tfrac12(\mathbf{A}+\mathbf{A}^{\mathsf{H}})\preceq-a\mathbf{I}$, and
$\mathbf{A}\mathbf{X}+\mathbf{X}\mathbf{A}^{\mathsf{H}}=-\mathbf{Q}$.
Adapted from `tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`,
`isHermitian_lyapunov_solution`. -/
theorem _root_.Matrix.IsHermitian.isHermitian_of_mul_add_mul_conjTranspose_eq_neg
    {A Q X : Matrix n n 𝕜} (hQ : Q.IsHermitian) {a : ℝ} (ha : 0 < a)
    (hA : hermitianPart A ≤ (-a) • (1 : Matrix n n 𝕜))
    (hX : A * X + X * Aᴴ = -Q) : X.IsHermitian := by
  have hstar := congrArg Matrix.conjTranspose hX
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_neg, hQ.eq] at hstar
  have he : A * Xᴴ + Xᴴ * Aᴴ = -Q := by
    rw [add_comm]
    exact hstar
  obtain ⟨Y, _, huniq⟩ := existsUnique_mul_add_mul_conjTranspose_eq_neg ha hA Q
  exact (huniq Xᴴ he).trans (huniq X hX).symm

/-- **Continuous Lyapunov equation, positivity.** If $a>0$,
$\tfrac12(\mathbf{A}+\mathbf{A}^{\mathsf{H}})\preceq-a\mathbf{I}$, and
$\mathbf{Q}$ is positive semidefinite, every solution of
$\mathbf{A}\mathbf{X}+\mathbf{X}\mathbf{A}^{\mathsf{H}}=-\mathbf{Q}$ is positive
semidefinite. The coefficient matrix may be nonnormal, and empty index types are included.
No printed source. Adapted from `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`,
`posSemidef_lyapunov_solution_of_quadratic_bound`.
Result: lyapunov-equation -/
theorem _root_.Matrix.PosSemidef.posSemidef_of_mul_add_mul_conjTranspose_eq_neg
    {A Q X : Matrix n n 𝕜} (hQ : Q.PosSemidef) {a : ℝ} (ha : 0 < a)
    (hA : hermitianPart A ≤ (-a) • (1 : Matrix n n 𝕜))
    (hX : A * X + X * Aᴴ = -Q) : X.PosSemidef := by
  have hH := hQ.isHermitian.isHermitian_of_mul_add_mul_conjTranspose_eq_neg ha hA hX
  apply hH.posSemidef_iff_eigenvalue_nonneg.mpr
  intro k
  by_cases hk : k < Fintype.card n
  · obtain ⟨v, hvnorm, hv⟩ := hH.exists_norm_eq_one_and_mulVec_eq hk
    have hq := re_quadForm_le_re_quadForm_of_le hA v
    rw [re_quadForm_hermitianPart, re_quadForm_real_smul_one, hvnorm,
      one_pow, mul_one] at hq
    have he : RCLike.re (quadForm (A * X + X * Aᴴ) v) =
        2 * eigenvalue X k * RCLike.re (quadForm A v) := by
      rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)] at hv
      have hve : star v ᵥ* X = (eigenvalue X k : 𝕜) • star v := by
        calc star v ᵥ* X = star (X *ᵥ v) := by rw [Matrix.star_mulVec, hH.eq]
          _ = (eigenvalue X k : 𝕜) • star v := by
            rw [hv, star_smul]
            simp only [RCLike.star_def, RCLike.conj_ofReal]
      have hq' : quadForm (A * X + X * Aᴴ) v =
          (eigenvalue X k : 𝕜) * (quadForm A v + quadForm Aᴴ v) := by
        simp only [quadForm, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec]
        rw [hv, Matrix.mulVec_smul, dotProduct_smul, Matrix.dotProduct_mulVec (star v) X, hve,
          smul_dotProduct]
        simp only [smul_eq_mul]
        ring
      rw [hq', RCLike.re_ofReal_mul, map_add, ← star_quadForm,
        RCLike.star_def, RCLike.conj_re]
      ring
    rw [hX, quadForm_neg_left, map_neg] at he
    have hn := hQ.re_quadForm_nonneg v
    by_contra hneg
    have hl : eigenvalue X k < 0 := lt_of_not_ge hneg
    have hprod := mul_pos_of_neg_of_neg hl (lt_of_le_of_lt hq (neg_neg_of_pos ha))
    nlinarith
  · rw [eigenvalue_of_card_le X (Nat.le_of_not_lt hk)]

end NLAlib
