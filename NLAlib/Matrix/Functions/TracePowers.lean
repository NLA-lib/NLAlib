/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import NLAlib.Matrix.Basic.Selection
public import NLAlib.Matrix.Functions.TraceFunctions

/-!
# Traces of powers and of products of matrix functions

For Hermitian $\mathbf{A}$ and $\mathbf{B}$ with unitary diagonalisations, the trace
$\operatorname{tr}(f(\mathbf{A}) g(\mathbf{B}))$ is a nonnegative combination of the products
$f(\lambda_i(\mathbf{A})) g(\lambda_j(\mathbf{B}))$, with weights the squared overlaps of the
eigenvectors. Scalar inequalities in two variables therefore lift to trace inequalities. This file
records the lifting principle and the trace-power inequalities that the moment method and the
method of exchangeable pairs for random matrices use.

## Main results

* `NLAlib.HasOrthonormalCols.re_trace_cfc_mul_cfc_eq_sum`: the overlap formula.
* `Matrix.IsHermitian.sum_re_trace_cfc_mul_cfc_le_of_forall`: lifting a two-variable inequality.
* `Matrix.IsHermitian.re_trace_pow_nonneg`, `Matrix.PosSemidef.re_trace_pow_nonneg`,
  `Matrix.IsHermitian.re_trace_pow_le_card_mul_specNorm_pow`: traces of powers through the
  eigenvalues (`Matrix.IsHermitian.re_trace_pow_eq_sum_range_eigenvalue_pow`); the moment bound for
  the spectral norm is `NLAlib.specNorm_pow_le_re_trace_pow`.
* `Matrix.PosSemidef.re_trace_rpow_add_le`: superadditivity of positive trace powers.
* `Matrix.PosDef.trace_pow_pos`, `Matrix.PosSemidef.re_trace_pow_add_le_mul`:
  positivity and submultiplicativity of power traces.
* `Matrix.IsHermitian.re_trace_mul_diagonal_mul_mul_diagonal`:
  $\operatorname{tr}(\mathbf{C} \operatorname{diag}(\mathbf{x}) \mathbf{C}
  \operatorname{diag}(\mathbf{y}))$
  as a weighted sum.
* `Matrix.IsHermitian.re_trace_mul_pow_mul_pow_le`:
  $\operatorname{tr}(\mathbf{C}\mathbf{H}^l\mathbf{C}\mathbf{H}^k)
  \le \operatorname{tr}(\mathbf{C}^2\mathbf{H}^{l+k})$ for even $l + k$.
* `NLAlib.re_trace_cfc_sub_mul_cfc_sub_le`: the mean value trace inequality.
* `Matrix.PosSemidef.re_trace_mul_pow_le_add`,
  `Matrix.PosSemidef.re_trace_mul_le_re_trace_rpow_add`: trace Young. -/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The overlap formula -/

/-- The overlap formula: if
$\mathbf{A} = \mathbf{U}\operatorname{diag}(\mathbf{a})\mathbf{U}^{\mathsf{H}}$ and
$\mathbf{B} = \mathbf{V}\operatorname{diag}(\mathbf{b})\mathbf{V}^{\mathsf{H}}$ with $\mathbf{a}$,
$\mathbf{b}$ real and $\mathbf{U}$, $\mathbf{V}$ unitary (orthonormal columns, as many columns as
rows), then
$$\operatorname{Re} \operatorname{tr}(f(\mathbf{A}) g(\mathbf{B}))
  = \sum_{i, j} \lvert (\mathbf{U}^{\mathsf{H}}\mathbf{V})_{i,j} \rvert^2 f(\mathbf{a}_i)
  g(\mathbf{b}_j) \,.$$ -/
theorem HasOrthonormalCols.re_trace_cfc_mul_cfc_eq_sum {r s : Type*} [Fintype r] [Fintype s]
    [DecidableEq r]
    [DecidableEq s] {A B : Matrix n n 𝕜} {U : Matrix n r 𝕜} {V : Matrix n s 𝕜} {a : r → ℝ}
    {b : s → ℝ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (hr : Fintype.card r = Fintype.card n) (hs : Fintype.card s = Fintype.card n)
    (hA : A = U * Matrix.diagonal (fun i => ((a i : ℝ) : 𝕜)) * Uᴴ)
    (hB : B = V * Matrix.diagonal (fun i => ((b i : ℝ) : 𝕜)) * Vᴴ) (f g : ℝ → ℝ) :
    RCLike.re (cfc f A * cfc g B).trace = ∑ i, ∑ j, ‖(Uᴴ * V) i j‖ ^ 2 * (f (a i) * g (b j)) := by
  rw [HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose hU hr hA,
    HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose hV hs hB]
  have hw : Vᴴ * U = (Uᴴ * V)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h1 : (U * Matrix.diagonal (fun i => ((f (a i) : ℝ) : 𝕜)) * Uᴴ *
      (V * Matrix.diagonal (fun j => ((g (b j) : ℝ) : 𝕜)) * Vᴴ)).trace =
      (Matrix.diagonal (fun i => ((f (a i) : ℝ) : 𝕜)) * (Uᴴ * V) *
        Matrix.diagonal (fun j => ((g (b j) : ℝ) : 𝕜)) * (Uᴴ * V)ᴴ).trace := by
    rw [← hw, Matrix.mul_assoc U, Matrix.mul_assoc U, Matrix.trace_mul_comm U]
    simp only [Matrix.mul_assoc]
  rw [h1]
  generalize Uᴴ * V = W
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, ite_mul,
    mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.conjTranspose_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show ((f (a i) : ℝ) : 𝕜) * W i j * ((g (b j) : ℝ) : 𝕜) * star (W i j) =
      ((f (a i) * g (b j) : ℝ) : 𝕜) * (W i j * star (W i j)) by push_cast; ring,
    RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    RCLike.ofReal_re, mul_comm]

/-- The overlap formula along the sorted eigenvalues, with the weights left abstract: there are
$w_{ij} \ge 0$ with $\operatorname{Re} \operatorname{tr}(f(\mathbf{A}) g(\mathbf{B}))
= \sum_{i, j} w_{ij} f(\lambda_i(\mathbf{A})) g(\lambda_j(\mathbf{B}))$ for all $f$, $g$. -/
private theorem exists_re_trace_cfc_mul_cfc_eq_sum {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    ∃ w : Fin (Fintype.card n) → Fin (Fintype.card n) → ℝ, (∀ i j, 0 ≤ w i j) ∧
      ∀ f g : ℝ → ℝ, RCLike.re (cfc f A * cfc g B).trace =
        ∑ i, ∑ j, w i j * (f (eigenvalue A i) * g (eigenvalue B j)) := by
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  obtain ⟨V, hV, hBV⟩ := hB.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  exact ⟨fun i j => ‖(Uᴴ * V) i j‖ ^ 2, fun i j => by positivity,
    fun f g => HasOrthonormalCols.re_trace_cfc_mul_cfc_eq_sum hU hV hr hr hAU hBV f g⟩

/-- **Lifting a two-variable inequality to traces.** For Hermitian $\mathbf{A}$, $\mathbf{B}$ and
finitely many functions, if $\sum_k f_k(x) g_k(y) \le \sum_k f'_k(x) g'_k(y)$ for all $x$ in the
spectrum of $\mathbf{A}$ and $y$ in that of $\mathbf{B}$, then
$$\sum_k \operatorname{Re} \operatorname{tr}(f_k(\mathbf{A}) g_k(\mathbf{B}))
  \le \sum_k \operatorname{Re} \operatorname{tr}(f'_k(\mathbf{A}) g'_k(\mathbf{B})) \,.$$
[Tropp2015, Proposition 8.3.5]. -/
theorem _root_.Matrix.IsHermitian.sum_re_trace_cfc_mul_cfc_le_of_forall {ι : Type*} [Fintype ι]
    {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {f g f' g' : ι → ℝ → ℝ}
    (h : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ B,
      ∑ k, f k x * g k y ≤ ∑ k, f' k x * g' k y) :
    ∑ k, RCLike.re (cfc (f k) A * cfc (g k) B).trace ≤
      ∑ k, RCLike.re (cfc (f' k) A * cfc (g' k) B).trace := by
  obtain ⟨w, hw0, hw⟩ := exists_re_trace_cfc_mul_cfc_eq_sum hA hB
  have key : ∀ F G : ι → ℝ → ℝ, ∑ k, RCLike.re (cfc (F k) A * cfc (G k) B).trace =
      ∑ i, ∑ j, w i j * ∑ k, F k (eigenvalue A i) * G k (eigenvalue B j) := fun F G => by
    simp only [hw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  rw [key f g, key f' g']
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (h _ (hA.eigenvalue_mem_spectrum i.isLt) _
      (hB.eigenvalue_mem_spectrum j.isLt)) (hw0 i j)

/-! ### Traces of powers -/

/-- The trace of an even power of a Hermitian matrix is nonnegative:
$\operatorname{Re} \operatorname{tr} \mathbf{A}^r \ge 0$ for even $r$. -/
theorem _root_.Matrix.IsHermitian.re_trace_pow_nonneg {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {r : ℕ} (hr : Even r) : 0 ≤ RCLike.re (A ^ r).trace := by
  rw [hA.re_trace_pow_eq_sum_range_eigenvalue_pow]
  exact Finset.sum_nonneg fun i _ => hr.pow_nonneg _

/-- The trace of a power of a positive semidefinite matrix is nonnegative:
$\operatorname{Re} \operatorname{tr} \mathbf{A}^r \ge 0$. -/
theorem _root_.Matrix.PosSemidef.re_trace_pow_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    (r : ℕ) : 0 ≤ RCLike.re (A ^ r).trace := by
  rw [hA.isHermitian.re_trace_pow_eq_sum_range_eigenvalue_pow]
  exact Finset.sum_nonneg fun i _ => pow_nonneg (hA.eigenvalue_nonneg i) r

/-- A positive definite real matrix has positive power trace in nonzero dimension. -/
theorem _root_.Matrix.PosDef.trace_pow_pos [Nonempty n] {R : Matrix n n ℝ}
    (hR : R.PosDef) (k : ℕ) : 0 < Matrix.trace (R ^ k) := by
  rw [← RCLike.re_to_real (x := Matrix.trace (R ^ k)),
    hR.isHermitian.re_trace_pow_eq_sum_range_eigenvalue_pow]
  exact Finset.sum_pos (fun i hi => pow_pos
    (hR.isHermitian.posDef_iff_eigenvalue_pos.mp hR i (Finset.mem_range.mp hi)) k)
    ⟨0, Finset.mem_range.mpr Fintype.card_pos⟩

/-- The product of two power traces of a positive semidefinite matrix dominates
the trace of the combined power. -/
theorem _root_.Matrix.PosSemidef.re_trace_pow_add_le_mul
    {R : Matrix n n 𝕜} (hR : R.PosSemidef) (a b : ℕ) :
    RCLike.re (R ^ (a + b)).trace ≤ RCLike.re (R ^ a).trace * RCLike.re (R ^ b).trace := by
  simp only [hR.isHermitian.re_trace_pow_eq_sum_range_eigenvalue_pow, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [pow_add]
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun j _ => pow_nonneg (hR.eigenvalue_nonneg j) b) hi)
    (pow_nonneg (hR.eigenvalue_nonneg i) a)

/-- The trace of a power is at most the dimension times the power of the spectral norm: for
Hermitian $\mathbf{A}$,
$\operatorname{Re} \operatorname{tr} \mathbf{A}^r \le \lvert n \rvert \, \|\mathbf{A}\|_2^r$. -/
theorem _root_.Matrix.IsHermitian.re_trace_pow_le_card_mul_specNorm_pow {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (r : ℕ) :
    RCLike.re (A ^ r).trace ≤ Fintype.card n * specNorm A ^ r := by
  rw [hA.re_trace_pow_eq_sum_range_eigenvalue_pow]
  have h := Finset.sum_le_card_nsmul (Finset.range (Fintype.card n))
    (fun i => eigenvalue A i ^ r) (specNorm A ^ r) fun i _ =>
      (le_abs_self _).trans ((abs_pow _ _).le.trans
        (pow_le_pow_left₀ (abs_nonneg _) (hA.abs_eigenvalue_le_specNorm i) r))
  rwa [Finset.card_range, nsmul_eq_mul] at h

/-! ### Trace inequalities for powers -/

/-- The rearrangement inequality for two powers with even total degree: for real $x$, $y$ and
$l + k$ even, $x^l y^k + x^k y^l \le x^{l+k} + y^{l+k}$. -/
private theorem pow_mul_pow_add_le {l k : ℕ} (h : Even (l + k)) (x y : ℝ) :
    x ^ l * y ^ k + x ^ k * y ^ l ≤ x ^ (l + k) + y ^ (l + k) := by
  have h1 : ∀ a b : ℕ, x ^ a * y ^ b ≤ |x| ^ a * |y| ^ b := fun a b => by
    rw [← abs_pow, ← abs_pow, ← abs_mul]
    exact le_abs_self _
  have h3 : 0 ≤ (|x| ^ l - |y| ^ l) * (|x| ^ k - |y| ^ k) := by
    rcases le_total |x| |y| with hxy | hxy
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (pow_le_pow_left₀ (abs_nonneg x) hxy l))
        (sub_nonpos.mpr (pow_le_pow_left₀ (abs_nonneg x) hxy k))
    · exact mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (abs_nonneg y) hxy l))
        (sub_nonneg.mpr (pow_le_pow_left₀ (abs_nonneg y) hxy k))
  rw [← h.pow_abs x, ← h.pow_abs y, pow_add, pow_add]
  linarith [h1 l k, h1 k l]

/-- The trace of
$\mathbf{C}\operatorname{diag}(\mathbf{x})\mathbf{C}\operatorname{diag}(\mathbf{y})$
for Hermitian $\mathbf{C}$ and real vectors $\mathbf{x}$, $\mathbf{y}$ is the weighted sum
$$\operatorname{Re} \operatorname{tr}\bigl(\mathbf{C}\operatorname{diag}(\mathbf{x})\mathbf{C}
  \operatorname{diag}(\mathbf{y})\bigr)
  = \sum_{i, j} \lvert \mathbf{C}_{i,j} \rvert^2 \mathbf{x}_j \mathbf{y}_i \,.$$
In an eigenbasis of $\mathbf{H}$ this expresses
$\operatorname{tr}(\mathbf{C} f(\mathbf{H}) \mathbf{C} g(\mathbf{H}))$ through the eigenvalues of
$\mathbf{H}$. -/
theorem _root_.Matrix.IsHermitian.re_trace_mul_diagonal_mul_mul_diagonal {p : Type*} [Fintype p]
    [DecidableEq p]
    {C : Matrix p p 𝕜} (hC : C.IsHermitian) (x y : p → ℝ) :
    RCLike.re (C * Matrix.diagonal (fun i => ((x i : ℝ) : 𝕜)) * C *
      Matrix.diagonal (fun i => ((y i : ℝ) : 𝕜))).trace =
      ∑ i, ∑ j, ‖C i j‖ ^ 2 * (x j * y i) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hs : C j i = star (C i j) := by rw [← Matrix.conjTranspose_apply, hC.eq]
  rw [hs, show C i j * ((x j : ℝ) : 𝕜) * star (C i j) * ((y i : ℝ) : 𝕜) =
      ((x j * y i : ℝ) : 𝕜) * (C i j * star (C i j)) by push_cast; ring,
    RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    RCLike.ofReal_re, mul_comm]

/-- The trace $\operatorname{Re} \operatorname{tr}(\mathbf{C}\mathbf{H}^l\mathbf{C}\mathbf{H}^k)$
as a sum over pairs of eigenvalues of $\mathbf{H}$ with symmetric nonnegative weights. -/
private theorem exists_re_trace_mul_pow_mul_pow_eq_sum {C H : Matrix n n 𝕜} (hC : C.IsHermitian)
    (hH : H.IsHermitian) :
    ∃ w : Fin (Fintype.card n) → Fin (Fintype.card n) → ℝ, (∀ i j, 0 ≤ w i j) ∧
      (∀ i j, w i j = w j i) ∧ ∀ l k : ℕ, RCLike.re (C * H ^ l * C * H ^ k).trace =
        ∑ i, ∑ j, w i j * (eigenvalue H j ^ l * eigenvalue H i ^ k) := by
  obtain ⟨U, hU, hHU⟩ := hH.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  have hC' : (Uᴴ * C * U).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul U hC
  refine ⟨fun i j => ‖(Uᴴ * C * U) i j‖ ^ 2, fun i j => by positivity, fun i j => ?_,
    fun l k => ?_⟩
  · change ‖(Uᴴ * C * U) i j‖ ^ 2 = ‖(Uᴴ * C * U) j i‖ ^ 2
    rw [← hC'.apply i j, norm_star]
  · have hpow : ∀ r : ℕ, H ^ r =
        U * Matrix.diagonal (fun i : Fin (Fintype.card n) => ((eigenvalue H i ^ r : ℝ) : 𝕜)) *
          Uᴴ := fun r => by
      rw [← cfc_pow_id (R := ℝ) H r hH]
      exact HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose hU hr hHU _
    rw [hpow l, hpow k, ← Matrix.IsHermitian.re_trace_mul_diagonal_mul_mul_diagonal hC']
    congr 1
    generalize Matrix.diagonal (fun i : Fin (Fintype.card n) =>
      ((eigenvalue H i ^ l : ℝ) : 𝕜)) = Dl
    generalize Matrix.diagonal (fun i : Fin (Fintype.card n) =>
      ((eigenvalue H i ^ k : ℝ) : 𝕜)) = Dk
    rw [show Uᴴ * C * U * Dl * (Uᴴ * C * U) * Dk = Uᴴ * (C * (U * Dl * Uᴴ) * C * (U * Dk)) by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm Uᴴ]
    simp only [Matrix.mul_assoc]

/-- **Rearranging powers inside a trace**: for Hermitian $\mathbf{C}$, $\mathbf{H}$ and $l + k$
even,
$\operatorname{Re} \operatorname{tr}(\mathbf{C}\mathbf{H}^l\mathbf{C}\mathbf{H}^k)
\le \operatorname{Re} \operatorname{tr}(\mathbf{C}^2\mathbf{H}^{l+k})$. [MackeyEtAl2014, §3]. -/
theorem _root_.Matrix.IsHermitian.re_trace_mul_pow_mul_pow_le {C H : Matrix n n 𝕜}
    (hC : C.IsHermitian)
    (hH : H.IsHermitian) {l k : ℕ} (h : Even (l + k)) :
    RCLike.re (C * H ^ l * C * H ^ k).trace ≤ RCLike.re (C ^ 2 * H ^ (l + k)).trace := by
  obtain ⟨w, hw0, hws, hw⟩ := exists_re_trace_mul_pow_mul_pow_eq_sum hC hH
  have h0 : C ^ 2 * H ^ (l + k) = C * H ^ 0 * C * H ^ (l + k) := by
    rw [pow_zero, Matrix.mul_one, sq]
  rw [h0, hw, hw]
  have hsym : ∀ a b : ℕ, ∑ i, ∑ j, w i j * (eigenvalue H j ^ a * eigenvalue H i ^ b) =
      ∑ i, ∑ j, w i j * (eigenvalue H j ^ b * eigenvalue H i ^ a) := fun a b => by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hws j i, mul_comm (eigenvalue H i ^ a)]
  have hsum : ∑ i, ∑ j, w i j * (eigenvalue H j ^ l * eigenvalue H i ^ k) +
      ∑ i, ∑ j, w i j * (eigenvalue H j ^ k * eigenvalue H i ^ l) ≤
      ∑ i, ∑ j, w i j * (eigenvalue H j ^ 0 * eigenvalue H i ^ (l + k)) +
        ∑ i, ∑ j, w i j * (eigenvalue H j ^ (l + k) * eigenvalue H i ^ 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← mul_add, ← mul_add, pow_zero, pow_zero, one_mul, mul_one]
    exact mul_le_mul_of_nonneg_left
      (by linarith [pow_mul_pow_add_le h (eigenvalue H j) (eigenvalue H i)]) (hw0 i j)
  linarith [hsym l k, hsym 0 (l + k)]

/-! ### The mean value trace inequality -/

/-- The trapezoid bound for a function whose derivative is convex: if $h$ has derivative $h'$
within $s$ and $h'$ is convex on $s$, then for $b < a$ in $s$,
$h(a) - h(b) \le (a - b)(h'(a) + h'(b))/2$. -/
private theorem sub_le_mul_add_div_two {h h' : ℝ → ℝ} {s : Set ℝ}
    (hh : ∀ x ∈ s, HasDerivWithinAt h (h' x) s x) (hh' : ConvexOn ℝ s h') {a b : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) (hba : b < a) : h a - h b ≤ (a - b) * (h' a + h' b) / 2 := by
  have hsub : Set.Icc b a ⊆ s := hh'.1.ordConnected.out hb ha
  have hpos : 0 < a - b := sub_pos.mpr hba
  obtain ⟨c, hc⟩ : ∃ c, c = (h' a - h' b) / (a - b) := ⟨_, rfl⟩
  have hφ : ∀ t ∈ Set.Ioo b a, HasDerivAt
      (fun t => h t - (h' b * (t - b) + c * (t - b) ^ 2 / 2)) (h' t - (h' b + c * (t - b))) t :=
    fun t ht => by
      have hs : s ∈ nhds t := Filter.mem_of_superset (Icc_mem_nhds ht.1 ht.2) hsub
      have h1 := (hh t (hsub (Set.Ioo_subset_Icc_self ht))).hasDerivAt hs
      have h3 : HasDerivAt (fun t : ℝ => t - b) 1 t := (hasDerivAt_id t).sub_const b
      have h2 : HasDerivAt (fun t => h' b * (t - b) + c * (t - b) ^ 2 / 2)
          (h' b + c * (t - b)) t := by
        have h4 := (h3.const_mul (h' b)).fun_add (((h3.fun_pow 2).const_mul c).div_const 2)
        refine h4.congr_deriv ?_
        rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, Nat.cast_ofNat]
        ring
      exact h1.sub h2
  have hcont : ContinuousOn (fun t => h t - (h' b * (t - b) + c * (t - b) ^ 2 / 2))
      (Set.Icc b a) := by
    have h1 : ContinuousOn h (Set.Icc b a) := fun t ht =>
      ((hh t (hsub ht)).continuousWithinAt).mono hsub
    exact h1.sub (by fun_prop)
  have hle := Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc b a) hcont (C := 0)
    (fun t ht => by
      rw [interior_Icc] at ht
      exact (hφ t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [interior_Icc] at ht
      rw [(hφ t ht).deriv, sub_nonpos]
      have hw := hh'.2 hb ha (div_nonneg (sub_nonneg.mpr ht.2.le) hpos.le)
        (div_nonneg (sub_nonneg.mpr ht.1.le) hpos.le) (by field_simp; ring)
      have ht' : ((a - t) / (a - b)) • b + ((t - b) / (a - b)) • a = t := by
        simp only [smul_eq_mul]
        field_simp
        ring
      rw [ht', smul_eq_mul, smul_eq_mul] at hw
      refine hw.trans (le_of_eq ?_)
      rw [hc]
      field_simp
      ring)
    b (Set.left_mem_Icc.mpr hba.le) a (Set.right_mem_Icc.mpr hba.le) hba.le
  have hc' : c * (a - b) = h' a - h' b := by rw [hc, div_mul_cancel₀ _ hpos.ne']
  simp only [sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div, add_zero, sub_zero, zero_mul] at hle
  nlinarith

/-- The scalar mean value inequality behind the mean value trace inequality:
$(g(a) - g(b))(h(a) - h(b)) \le \tfrac12 (g(a) - g(b))(a - b)(h'(a) + h'(b))$ for $g$
non-decreasing and $h'$ convex on $s$. -/
private theorem sub_mul_sub_le_half_mul {g h h' : ℝ → ℝ} {s : Set ℝ} (hg : MonotoneOn g s)
    (hh : ∀ x ∈ s, HasDerivWithinAt h (h' x) s x) (hh' : ConvexOn ℝ s h') {a b : ℝ} (ha : a ∈ s)
    (hb : b ∈ s) :
    (g a - g b) * (h a - h b) ≤ 1 / 2 * ((g a - g b) * (a - b) * (h' a + h' b)) := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · have h1 := sub_le_mul_add_div_two hh hh' hb ha hab
    have h2 : 0 ≤ g b - g a := sub_nonneg.mpr (hg ha hb hab.le)
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  · simp only [sub_self, zero_mul, mul_zero, le_refl]
  · have h1 := sub_le_mul_add_div_two hh hh' ha hb hab
    have h2 : 0 ≤ g a - g b := sub_nonneg.mpr (hg hb ha hab.le)
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]

/-- The trace of $(g(\mathbf{A}) - g(\mathbf{B}))(h(\mathbf{A}) - h(\mathbf{B}))$ as a combination
of traces $\operatorname{tr}(\varphi(\mathbf{A}) \psi(\mathbf{B}))$. -/
private theorem trace_cfc_sub_mul_cfc_sub {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (g h : ℝ → ℝ) :
    ((cfc g A - cfc g B) * (cfc h A - cfc h B)).trace =
      (cfc (fun x => g x * h x) A * cfc (fun _ : ℝ => (1 : ℝ)) B).trace -
        (cfc g A * cfc h B).trace - (cfc h A * cfc g B).trace +
        (cfc (fun _ : ℝ => (1 : ℝ)) A * cfc (fun x => g x * h x) B).trace := by
  have hsA : IsSelfAdjoint A := hA
  have hsB : IsSelfAdjoint B := hB
  have cA : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn
  have cB : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ B) := B.finite_real_spectrum.continuousOn
  rw [cfc_const_one ℝ A hsA, cfc_const_one ℝ B hsB, Matrix.mul_one, Matrix.one_mul,
    cfc_mul g h A (cA _) (cA _), cfc_mul g h B (cB _) (cB _),
    Matrix.trace_mul_comm (cfc h A) (cfc g B)]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  ring

/-- The trace of
$(g(\mathbf{A}) - g(\mathbf{B}))(\mathbf{A} - \mathbf{B})(p(\mathbf{A}) + p(\mathbf{B}))$ as a
combination of traces $\operatorname{tr}(\varphi(\mathbf{A}) \psi(\mathbf{B}))$. -/
private theorem trace_cfc_sub_mul_sub_mul_cfc_add {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (g p : ℝ → ℝ) :
    ((cfc g A - cfc g B) * (A - B) * (cfc p A + cfc p B)).trace =
      (cfc (fun x => g x * x * p x) A * cfc (fun _ : ℝ => (1 : ℝ)) B).trace +
        (cfc (fun x => g x * x) A * cfc p B).trace -
        (cfc (fun x => p x * g x) A * cfc (fun x : ℝ => x) B).trace -
        (cfc g A * cfc (fun x => x * p x) B).trace -
        (cfc (fun x => x * p x) A * cfc g B).trace -
        (cfc (fun x : ℝ => x) A * cfc (fun x => p x * g x) B).trace +
        (cfc p A * cfc (fun x => g x * x) B).trace +
        (cfc (fun _ : ℝ => (1 : ℝ)) A * cfc (fun x => g x * x * p x) B).trace := by
  have hsA : IsSelfAdjoint A := hA
  have hsB : IsSelfAdjoint B := hB
  have cA : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn
  have cB : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ B) := B.finite_real_spectrum.continuousOn
  rw [cfc_const_one ℝ A hsA, cfc_const_one ℝ B hsB, Matrix.mul_one, Matrix.one_mul,
    cfc_mul (fun x => g x * x) p A (cA _) (cA _), cfc_mul (fun x => g x * x) p B (cB _) (cB _),
    cfc_mul g (fun x => x) A (cA _) (cA _), cfc_mul g (fun x => x) B (cB _) (cB _),
    cfc_mul p g A (cA _) (cA _), cfc_mul p g B (cB _) (cB _),
    cfc_mul (fun x => x) p A (cA _) (cA _), cfc_mul (fun x => x) p B (cB _) (cB _),
    cfc_id' ℝ A hsA, cfc_id' ℝ B hsB]
  generalize cfc g A = GA
  generalize cfc g B = GB
  generalize cfc p A = PA
  generalize cfc p B = PB
  have c3 : (GA * B * PA).trace = (PA * GA * B).trace := Matrix.trace_mul_cycle _ _ _
  have c4 : (GA * B * PB).trace = (GA * (B * PB)).trace := by rw [Matrix.mul_assoc]
  have c5 : (GB * A * PA).trace = (A * PA * GB).trace := (Matrix.trace_mul_cycle _ _ _).symm
  have c6 : (GB * A * PB).trace = (A * (PB * GB)).trace := by
    rw [← Matrix.mul_assoc]
    exact (Matrix.trace_mul_cycle _ _ _).symm
  have c7 : (GB * B * PA).trace = (PA * (GB * B)).trace := by
    rw [← Matrix.mul_assoc]
    exact Matrix.trace_mul_cycle _ _ _
  rw [← c3, ← c4, ← c5, ← c6, ← c7]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add]
  ring

/-- **The mean value trace inequality.** For $g$ non-decreasing on $s$, $h$ with derivative $h'$
within $s$ and $h'$ convex on $s$, and Hermitian $\mathbf{A}$, $\mathbf{B}$ with spectrum in $s$,
$$\begin{aligned}
  &\operatorname{Re} \operatorname{tr}\bigl((g(\mathbf{A}) - g(\mathbf{B}))
    (h(\mathbf{A}) - h(\mathbf{B}))\bigr) \\
  &\quad \le \tfrac12 \operatorname{Re} \operatorname{tr}\bigl((g(\mathbf{A}) - g(\mathbf{B}))
    (\mathbf{A} - \mathbf{B})(h'(\mathbf{A}) + h'(\mathbf{B}))\bigr) \,.
\end{aligned}$$
[MackeyEtAl2014, Lemma 3.4].
Result: mean-value-trace-inequality -/
theorem re_trace_cfc_sub_mul_cfc_sub_le {g h h' : ℝ → ℝ} {s : Set ℝ} (hg : MonotoneOn g s)
    (hh : ∀ x ∈ s, HasDerivWithinAt h (h' x) s x) (hh' : ConvexOn ℝ s h') {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAs : spectrum ℝ A ⊆ s)
    (hBs : spectrum ℝ B ⊆ s) :
    RCLike.re ((cfc g A - cfc g B) * (cfc h A - cfc h B)).trace ≤
      1 / 2 * RCLike.re ((cfc g A - cfc g B) * (A - B) * (cfc h' A + cfc h' B)).trace := by
  obtain ⟨w, hw0, hw⟩ := exists_re_trace_cfc_mul_cfc_eq_sum hA hB
  have e1 : RCLike.re ((cfc g A - cfc g B) * (cfc h A - cfc h B)).trace =
      ∑ i, ∑ j, w i j * ((g (eigenvalue A i) - g (eigenvalue B j)) *
        (h (eigenvalue A i) - h (eigenvalue B j))) := by
    rw [trace_cfc_sub_mul_cfc_sub hA hB]
    simp only [map_sub, map_add, hw, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have e2 : RCLike.re ((cfc g A - cfc g B) * (A - B) * (cfc h' A + cfc h' B)).trace =
      ∑ i, ∑ j, w i j * ((g (eigenvalue A i) - g (eigenvalue B j)) *
        (eigenvalue A i - eigenvalue B j) * (h' (eigenvalue A i) + h' (eigenvalue B j))) := by
    rw [trace_cfc_sub_mul_sub_mul_cfc_add hA hB]
    simp only [map_sub, map_add, hw, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e1, e2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_left_comm (1 / 2 : ℝ)]
  exact mul_le_mul_of_nonneg_left (sub_mul_sub_le_half_mul hg hh hh'
    (hAs (hA.eigenvalue_mem_spectrum i.isLt)) (hBs (hB.eigenvalue_mem_spectrum j.isLt))) (hw0 i j)

/-- The mean value trace inequality for powers: for Hermitian $\mathbf{H}$, $\mathbf{K}$ and even
$m$,
$$\operatorname{Re} \operatorname{tr}\bigl((\mathbf{H} - \mathbf{K})
  (\mathbf{H}^{m+1} - \mathbf{K}^{m+1})\bigr)
  \le \frac{m + 1}{2} \operatorname{Re} \operatorname{tr}\bigl((\mathbf{H} - \mathbf{K})^2
  (\mathbf{H}^m + \mathbf{K}^m)\bigr) \,.$$
[MackeyEtAl2014, Lemma 3.4]. -/
theorem _root_.Matrix.IsHermitian.re_trace_sub_mul_pow_sub_pow_le {H K : Matrix n n 𝕜}
    (hH : H.IsHermitian)
    (hK : K.IsHermitian) {m : ℕ} (hm : Even m) :
    RCLike.re ((H - K) * (H ^ (m + 1) - K ^ (m + 1))).trace ≤
      (m + 1 : ℝ) / 2 * RCLike.re ((H - K) ^ 2 * (H ^ m + K ^ m)).trace := by
  have hsH : IsSelfAdjoint H := hH
  have hsK : IsSelfAdjoint K := hK
  have hconv : ConvexOn ℝ Set.univ fun x : ℝ => (m + 1 : ℝ) * x ^ m :=
    hm.convexOn_pow.smul (by positivity)
  have key := re_trace_cfc_sub_mul_cfc_sub_le (g := fun x => x) (h := fun x => x ^ (m + 1))
    (h' := fun x => (m + 1 : ℝ) * x ^ m) (s := Set.univ) (monotone_id.monotoneOn _)
    (fun x _ => by
      have h := (hasDerivAt_pow (m + 1) x).hasDerivWithinAt (s := Set.univ)
      rwa [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h)
    hconv hH hK (Set.subset_univ _) (Set.subset_univ _)
  rw [cfc_id' ℝ H hsH, cfc_id' ℝ K hsK, cfc_pow_id H (m + 1) hsH, cfc_pow_id K (m + 1) hsK,
    cfc_const_mul (m + 1 : ℝ) (fun x => x ^ m) H, cfc_const_mul (m + 1 : ℝ) (fun x => x ^ m) K,
    cfc_pow_id H m hsH, cfc_pow_id K m hsK, ← smul_add, Matrix.mul_smul, Matrix.trace_smul,
    RCLike.smul_re, ← sq] at key
  linarith

/-! ### Trace Young inequalities -/

/-- Young's inequality for natural powers: $(q + 1) x y^q \le x^{q+1} + q y^{q+1}$ for
$x, y \ge 0$. -/
private theorem succ_mul_mul_pow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (q : ℕ) :
    (q + 1 : ℝ) * (x * y ^ q) ≤ x ^ (q + 1) + q * y ^ (q + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : 0 ≤ (x ^ (q + 1) - y ^ (q + 1)) * (x - y) := by
      rcases le_total x y with hxy | hxy
      · exact mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr (pow_le_pow_left₀ hx hxy _)) (sub_nonpos.mpr hxy)
      · exact mul_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hy hxy _)) (sub_nonneg.mpr hxy)
    have h2 := mul_le_mul_of_nonneg_right ih hy
    rw [pow_succ x (q + 1), pow_succ y (q + 1)]
    rw [pow_succ y q] at h1 h2 ⊢
    push_cast
    nlinarith

/-- **The trace Young inequality for powers**: for positive semidefinite $\mathbf{V}$ and
Hermitian $\mathbf{H}$,
$$(q + 1)(2q + 1) \operatorname{tr}(\mathbf{V}\mathbf{H}^{2q})
  \le (2q + 1)^{q+1} \operatorname{tr} \mathbf{V}^{q+1} + q \operatorname{tr} \mathbf{H}^{2q+2}
  \,,$$
traces through their real parts.
[MackeyEtAl2014, proof of Theorem 7.1]. -/
theorem _root_.Matrix.PosSemidef.re_trace_mul_pow_le_add {V H : Matrix n n 𝕜} (hV : V.PosSemidef)
    (hH : H.IsHermitian)
    (q : ℕ) :
    (q + 1 : ℝ) * (2 * q + 1) * RCLike.re (V * H ^ (2 * q)).trace ≤
      (2 * q + 1 : ℝ) ^ (q + 1) * RCLike.re (V ^ (q + 1)).trace +
        q * RCLike.re (H ^ (2 * q + 2)).trace := by
  obtain ⟨w, hw0, hw⟩ := exists_re_trace_cfc_mul_cfc_eq_sum hV.isHermitian hH
  have hsV : IsSelfAdjoint V := hV.isHermitian
  have hsH : IsSelfAdjoint H := hH
  have e1 := hw (fun x => x) (fun x => x ^ (2 * q))
  have e2 := hw (fun x => x ^ (q + 1)) (fun _ => (1 : ℝ))
  have e3 := hw (fun _ => (1 : ℝ)) (fun x => x ^ (2 * q + 2))
  rw [cfc_id' ℝ V hsV, cfc_pow_id H (2 * q) hsH] at e1
  rw [cfc_pow_id V (q + 1) hsV, cfc_const_one ℝ H hsH, Matrix.mul_one] at e2
  rw [cfc_pow_id H (2 * q + 2) hsH, cfc_const_one ℝ V hsV, Matrix.one_mul] at e3
  rw [e1, e2, e3]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hs := succ_mul_mul_pow_le (x := (2 * q + 1) * eigenvalue V i) (y := eigenvalue H j ^ 2)
    (mul_nonneg (by positivity) (hV.eigenvalue_nonneg i)) (sq_nonneg _) q
  rw [mul_pow, ← pow_mul, ← pow_mul, show 2 * (q + 1) = 2 * q + 2 by ring] at hs
  nlinarith [mul_le_mul_of_nonneg_left hs (hw0 i j)]

/-- **Young's inequality for traces**: for positive semidefinite $\mathbf{A}$, $\mathbf{B}$ and
conjugate exponents $p$, $q$ (`Real.HolderConjugate`, so $1/p + 1/q = 1$),
$\operatorname{Re} \operatorname{tr}(\mathbf{A}\mathbf{B})
\le \operatorname{Re} \operatorname{tr} \mathbf{A}^p / p +
\operatorname{Re} \operatorname{tr} \mathbf{B}^q / q$. [Bhatia1997, §IV.2 context]. -/
theorem _root_.Matrix.PosSemidef.re_trace_mul_le_re_trace_rpow_add {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef)
    (hB : B.PosSemidef) {p q : ℝ} (hpq : p.HolderConjugate q) :
    RCLike.re (A * B).trace ≤ RCLike.re (A ^ p).trace / p + RCLike.re (B ^ q).trace / q := by
  obtain ⟨w, hw0, hw⟩ := exists_re_trace_cfc_mul_cfc_eq_sum hA.isHermitian hB.isHermitian
  have hsA : IsSelfAdjoint A := hA.isHermitian
  have hsB : IsSelfAdjoint B := hB.isHermitian
  have e1 := hw (fun x => x) (fun x => x)
  have e2 := hw (fun x => x ^ p) (fun _ => (1 : ℝ))
  have e3 := hw (fun _ => (1 : ℝ)) (fun x => x ^ q)
  rw [cfc_id' ℝ A hsA, cfc_id' ℝ B hsB] at e1
  rw [← CFC.rpow_eq_cfc_real hA.nonneg, cfc_const_one ℝ B hsB, Matrix.mul_one] at e2
  rw [← CFC.rpow_eq_cfc_real hB.nonneg, cfc_const_one ℝ A hsA, Matrix.one_mul] at e3
  rw [e1, e2, e3, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hs := Real.young_inequality_of_nonneg (hA.eigenvalue_nonneg i) (hB.eigenvalue_nonneg j) hpq
  calc w i j * (eigenvalue A i * eigenvalue B j)
      ≤ w i j * (eigenvalue A i ^ p / p + eigenvalue B j ^ q / q) :=
        mul_le_mul_of_nonneg_left hs (hw0 i j)
    _ = w i j * (eigenvalue A i ^ p * 1) / p + w i j * (1 * eigenvalue B j ^ q) / q := by ring

/-! ### Positive trace powers -/

/-- **McCarthy's trace superadditivity.** For positive semidefinite $\mathbf{X},\mathbf{Y}$
and real $p \ge 1$,
$$\operatorname{Re}\operatorname{tr}(\mathbf{X}^p) +
  \operatorname{Re}\operatorname{tr}(\mathbf{Y}^p)
  \le \operatorname{Re}\operatorname{tr}((\mathbf{X}+\mathbf{Y})^p).$$
[PerssonMeyerMusco2025, proof of Lemma 2.3].
Result: trace-power-superadditivity -/
theorem _root_.Matrix.PosSemidef.re_trace_rpow_add_le {X Y : Matrix n n 𝕜}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) {p : ℝ} (hp : 1 ≤ p) :
    RCLike.re (X ^ p).trace + RCLike.re (Y ^ p).trace ≤ RCLike.re ((X + Y) ^ p).trace := by
  -- The two diagonal blocks of the left Gram matrix are X and Y; the right Gram matrix is X + Y.
  let G := Matrix.fromRows (CFC.sqrt X) (CFC.sqrt Y)
  have hs (M : Matrix n n 𝕜) : (CFC.sqrt M)ᴴ = CFC.sqrt M :=
    (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq
  have hG : Gᴴ * G = X + Y := by
    simp only [G, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromCols_mul_fromRows, hs, CFC.sqrt_mul_sqrt_self _ hX.nonneg,
      CFC.sqrt_mul_sqrt_self _ hY.nonneg]
  have hblocks : G * Gᴴ =
      Matrix.fromBlocks X (CFC.sqrt X * CFC.sqrt Y) (CFC.sqrt Y * CFC.sqrt X) Y := by
    simp only [G, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
      Matrix.fromRows_mul_fromCols, hs, CFC.sqrt_mul_sqrt_self _ hX.nonneg,
      CFC.sqrt_mul_sqrt_self _ hY.nonneg]
  have hd₁ : (G * Gᴴ).submatrix Sum.inl Sum.inl = X := hblocks ▸ rfl
  have hd₂ : (G * Gᴴ).submatrix Sum.inr Sum.inr = Y := hblocks ▸ rfl
  let f := fun t : ℝ => t ^ p
  have hGG := Matrix.posSemidef_self_mul_conjTranspose G
  have hj (e : n → n ⊕ n) (he : Function.Injective e) :
      RCLike.re (cfc f ((G * Gᴴ).submatrix e e)).trace ≤
        RCLike.re ((cfc f (G * Gᴴ)).submatrix e e).trace := by
    simpa only [conjTranspose_selectionMatrix_mul_mul_selectionMatrix] using
      re_trace_cfc_conjTranspose_mul_mul_le (convexOn_rpow hp) hGG.isHermitian
        hGG.spectrum_subset_Ici (hasOrthonormalCols_selectionMatrix (𝕜 := 𝕜) he)
  have hh := add_le_add (hj Sum.inl Sum.inl_injective) (hj Sum.inr Sum.inr_injective)
  rw [hd₁, hd₂] at hh
  have ht (M : Matrix (n ⊕ n) (n ⊕ n) 𝕜) :
      (M.submatrix Sum.inl Sum.inl).trace + (M.submatrix Sum.inr Sum.inr).trace = M.trace := by
    simp [Matrix.trace, Fintype.sum_sum_type, Matrix.diag, Matrix.submatrix]
  have hsum := congrArg RCLike.re (ht (cfc f (G * Gᴴ)))
  rw [map_add] at hsum
  rw [hsum] at hh
  rw [CFC.rpow_eq_cfc_real hX.nonneg, CFC.rpow_eq_cfc_real hY.nonneg,
    CFC.rpow_eq_cfc_real (hX.add hY).nonneg]
  -- The two Gram matrices have the same eigenvalues after zero padding.
  apply hh.trans_eq
  rw [← hG, hGG.isHermitian.re_trace_cfc,
    (Matrix.isHermitian_conjTranspose_mul_self G).re_trace_cfc]
  simp_rw [← singularValues_sq_eq_eigenvalue_mul_conjTranspose_self, singularValues_sq]
  apply Eq.symm
  refine Finset.sum_subset (Finset.range_mono (by simp)) ?_
  intro i _ hi
  rw [eigenvalue_of_card_le _ (by simpa using hi)]
  exact Real.zero_rpow (by linarith)

end NLAlib
