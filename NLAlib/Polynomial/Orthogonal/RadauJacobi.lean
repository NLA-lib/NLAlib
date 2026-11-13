/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Gauss

/-!
# The Radau Jacobi matrix

For a finite measure $\mu$ carried by $[a,b]$, positive definite on polynomials of degree less
than $k + 1$, and prescribed endpoint $c \in \{a,b\}$, the Radau rule is the spectral measure
of the Jacobi matrix of order $k + 1$ with its last diagonal entry modified
(`radauJacobiMatrix`, Golub's construction). The identification is
`NLAlib.spectralMeasure_radauJacobiMatrix` in `NLAlib.Krylov.Functions.Quadrature`.
This file proves that $c$ is an eigenvalue when the denominator $\pi_k(c)$ is nonzero, under
the finite-measure, bounded-support and positive-definiteness hypotheses, and that the modified
matrix has the moments of the Jacobi matrix through degree $2k$. The total definitions alone do
not imply a spectral identification when the denominator vanishes.

## Main definitions

* `NLAlib.radauJacobiAlpha`, `NLAlib.radauJacobiMatrix`: the modified Jacobi matrix.

## Main results

* `NLAlib.IsMomentPosDef.radauJacobiMatrix_mulVec_eq`,
  `NLAlib.IsMomentPosDef.mem_spectrum_radauJacobiMatrix`: $c$ is an eigenvalue for a finite
  measure carried by a bounded interval, with positive definiteness and $\pi_k(c) \ne 0$.
* `NLAlib.radauJacobiMatrix_pow_apply_zero_zero`: the moments through degree $2k$.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix

namespace NLAlib

/-! ### The modified Jacobi matrix -/

/-- The **Radau corner** $\tilde\alpha_k = c - \beta_k\pi_{k-1}(c)/\pi_k(c)$ for $k \ge 1$ and
$\tilde\alpha_0 = c$. When $\pi_k(c) \ne 0$, this makes $c$ a zero of the modified recurrence
$\tilde\pi_{k+1} = (x - \tilde\alpha_k)\pi_k - \beta_k\pi_{k-1}$.
For a finite measure carried by a bounded interval, positive definite on polynomials of degree
less than $k + 1$, the nonzero denominator also makes $c$ an eigenvalue of
`radauJacobiMatrix μ c k`. Junk: $c$ when $\pi_k(c) = 0$ ($x/0 = 0$), with no such eigenvalue
claim in that case. [Golub1973, §7, (7.1)–(7.4)];
[GolubMeurant2010, §6.2.2]. -/
noncomputable def radauJacobiAlpha (μ : Measure ℝ) (c : ℝ) : ℕ → ℝ
  | 0 => c
  | k + 1 => c - jacobiBeta μ (k + 1) * (orthogonalPolynomial μ k).eval c /
      (orthogonalPolynomial μ (k + 1)).eval c

/-- The **Radau Jacobi matrix** of order $k + 1$: the Jacobi matrix `jacobiMatrix μ (k + 1)`
with its last diagonal entry $\alpha_k$ replaced by `radauJacobiAlpha μ c k`.
For a finite measure $\mu$ carried by $[a,b]$, positive definite on polynomials of degree less
than $k + 1$, and prescribed endpoint $c \in \{a,b\}$, its spectral measure at
$\sqrt{\mu(\mathbb{R})}\,\mathbf{e}_0$ is the Radau rule with $k$ free nodes
(`NLAlib.spectralMeasure_radauJacobiMatrix`). The matrix is defined for all arguments; if
$\pi_k(c) = 0$, its corner is $c$ by total division, and the spectral-rule identity is not
asserted without the preceding hypotheses.
[Golub1973, §7, (7.1)–(7.4)]; [GolubMeurant2010, §6.2.2]. -/
noncomputable def radauJacobiMatrix (μ : Measure ℝ) (c : ℝ) (k : ℕ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  Matrix.of fun i j =>
    if i = Fin.last k ∧ j = Fin.last k then radauJacobiAlpha μ c k else jacobiMatrix μ (k + 1) i j

/-- The Radau corner at $k = 0$ is $c$, by definition. -/
theorem radauJacobiAlpha_zero (μ : Measure ℝ) (c : ℝ) : radauJacobiAlpha μ c 0 = c := rfl

/-- The Radau corner for $k \ge 1$, by definition. -/
theorem radauJacobiAlpha_succ (μ : Measure ℝ) (c : ℝ) (k : ℕ) :
    radauJacobiAlpha μ c (k + 1) = c - jacobiBeta μ (k + 1) * (orthogonalPolynomial μ k).eval c /
      (orthogonalPolynomial μ (k + 1)).eval c := rfl

variable {μ ν : Measure ℝ} [IsFiniteMeasure μ] {a b c : ℝ}

/-! ### The Radau Jacobi matrix -/

/-- A row of the Radau Jacobi matrix times a vector: the diagonal term and the two entries
beside it. -/
private theorem radauJacobiMatrix_mulVec_apply {k : ℕ} (μ : Measure ℝ) (c : ℝ)
    (w : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    (radauJacobiMatrix μ c k *ᵥ w) i =
      (if i = Fin.last k then radauJacobiAlpha μ c k else jacobiAlpha μ i) * w i +
        (if h : 0 < (i : ℕ) then √(jacobiBeta μ i) * w ⟨i - 1, by omega⟩ else 0) +
        (if h : (i : ℕ) < k then √(jacobiBeta μ (i + 1)) * w ⟨i + 1, by omega⟩ else 0) := by
  obtain ⟨i, hi⟩ := i
  have hterm : ∀ j : Fin (k + 1), radauJacobiMatrix μ c k ⟨i, hi⟩ j * w j =
      (if j = ⟨i, hi⟩ then (if (⟨i, hi⟩ : Fin (k + 1)) = Fin.last k then radauJacobiAlpha μ c k
          else jacobiAlpha μ i) * w j else 0) +
        (if (j : ℕ) + 1 = i then √(jacobiBeta μ i) * w j else 0) +
        (if i + 1 = (j : ℕ) then √(jacobiBeta μ j) * w j else 0) := by
    intro j
    obtain ⟨j, hj⟩ := j
    unfold radauJacobiMatrix jacobiMatrix
    simp only [Matrix.of_apply, Fin.ext_iff, Fin.val_last]
    split_ifs <;> first | omega | (subst_vars; ring)
  have hsub : ∑ x : Fin (k + 1), (if (x : ℕ) + 1 = i then √(jacobiBeta μ i) * w x else 0) =
      if h : 0 < i then √(jacobiBeta μ i) * w ⟨i - 1, by omega⟩ else 0 := by
    split_ifs with h0
    · rw [Finset.sum_eq_single ⟨i - 1, by omega⟩ (fun x _ hx => if_neg fun e => hx (Fin.ext
        (by simp only; omega))) (by simp), if_pos (by simp only; omega)]
    · exact Finset.sum_eq_zero fun x _ => if_neg (by omega)
  have hsup : ∑ x : Fin (k + 1), (if i + 1 = (x : ℕ) then √(jacobiBeta μ x) * w x else 0) =
      if h : i < k then √(jacobiBeta μ (i + 1)) * w ⟨i + 1, by omega⟩ else 0 := by
    split_ifs with h0
    · rw [Finset.sum_eq_single ⟨i + 1, by omega⟩ (fun x _ hx => if_neg fun e => hx (Fin.ext
        (by simp only; omega))) (by simp), if_pos rfl]
    · exact Finset.sum_eq_zero fun x _ => if_neg (by omega)
  simp only [Matrix.mulVec, dotProduct, hterm, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [hsub, hsup]

/-- **The prescribed node is an eigenvalue of the Radau Jacobi matrix**: if a finite measure
$\mu$ supported in $[a, b]$ is positive definite up to degree $k + 1$ and $\pi_k(c) \ne 0$, then
$\tilde{\mathbf{J}}\mathbf{v} = c\,\mathbf{v}$ for the Radau Jacobi matrix $\tilde{\mathbf{J}}$
of order $k + 1$ and $\mathbf{v}_i = \pi_i(c)/\|\pi_i\|$ (the orthonormal polynomials at $c$;
$\mathbf{v}_0 > 0$). [Golub1973, §7, (7.1)–(7.4)]. -/
theorem IsMomentPosDef.radauJacobiMatrix_mulVec_eq {k : ℕ} (h : IsMomentPosDef μ (k + 1))
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc0 : (orthogonalPolynomial μ k).eval c ≠ 0) :
    radauJacobiMatrix μ c k *ᵥ (fun i : Fin (k + 1) => (orthogonalPolynomial μ i).eval c /
        √(∫ x, (orthogonalPolynomial μ i).eval x ^ 2 ∂μ)) =
      c • fun i : Fin (k + 1) => (orthogonalPolynomial μ i).eval c /
        √(∫ x, (orthogonalPolynomial μ i).eval x ^ 2 ∂μ) := by
  have hs : ∀ j ≤ k, √(∫ x, (orthogonalPolynomial μ j).eval x ^ 2 ∂μ) ≠ 0 := fun j hj =>
    (Real.sqrt_pos.mpr ((isMomentPosDef_succ_iff hμ j).mp (h.mono (by omega)))).ne'
  have hsqrtβ : ∀ m, m + 1 ≤ k → √(jacobiBeta μ (m + 1)) =
      √(∫ x, (orthogonalPolynomial μ (m + 1)).eval x ^ 2 ∂μ) /
        √(∫ x, (orthogonalPolynomial μ m).eval x ^ 2 ∂μ) := fun m _ =>
    Real.sqrt_div (integral_nonneg fun x => sq_nonneg _) _
  have hβ : ∀ m, m + 1 ≤ k → jacobiBeta μ (m + 1) =
      (√(∫ x, (orthogonalPolynomial μ (m + 1)).eval x ^ 2 ∂μ)) ^ 2 /
        (√(∫ x, (orthogonalPolynomial μ m).eval x ^ 2 ∂μ)) ^ 2 := fun m _ => by
    rw [Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _),
      Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
    rfl
  have hrec : ∀ m, (orthogonalPolynomial μ (m + 2)).eval c =
      (c - jacobiAlpha μ (m + 1)) * (orthogonalPolynomial μ (m + 1)).eval c -
        jacobiBeta μ (m + 1) * (orthogonalPolynomial μ m).eval c := fun m => by
    simp [orthogonalPolynomial_add_two]
  funext i
  rw [radauJacobiMatrix_mulVec_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  obtain ⟨i, hi⟩ := i
  rcases Nat.lt_or_ge i k with hik | hik
  · rw [if_neg (fun h' => by simp [Fin.ext_iff] at h'; omega), dif_pos hik]
    dsimp only
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have e0 : (orthogonalPolynomial μ 0).eval c = 1 := by simp [orthogonalPolynomial_zero]
      have e1 : (orthogonalPolynomial μ 1).eval c = c - jacobiAlpha μ 0 := by
        simp [orthogonalPolynomial_one]
      have h0 := hs 0 (by omega)
      have h1 := hs 1 (by omega)
      rw [dif_neg (lt_irrefl 0), add_zero, hsqrtβ 0 hik, e0, e1]
      field_simp
      ring
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [dif_pos (by omega : 0 < m + 1)]
      simp only [Nat.add_sub_cancel]
      have h0 := hs m (by omega)
      have h1 := hs (m + 1) (by omega)
      have h2 := hs (m + 1 + 1) hik
      rw [hsqrtβ m (by omega), hsqrtβ (m + 1) hik, hrec m, hβ m (by omega)]
      field_simp
      ring
  · have hik' : i = k := by omega
    subst i
    dsimp only
    rw [if_pos (show (⟨k, hi⟩ : Fin (k + 1)) = Fin.last k from rfl), dif_neg (lt_irrefl _)]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [radauJacobiAlpha_zero]
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [dif_pos (by omega : 0 < m + 1)]
      simp only [Nat.add_sub_cancel]
      have h0 := hs m (by omega)
      have h1 := hs (m + 1) (by omega)
      rw [radauJacobiAlpha_succ, hsqrtβ m le_rfl, hβ m le_rfl]
      field_simp
      ring

/-- The endpoint is an eigenvalue of the Radau Jacobi matrix: if a finite measure $\mu$ supported
in $[a, b]$ is positive definite up to degree $k + 1$ and $c \in \{a, b\}$, then $c$ is in the
spectrum of the Radau Jacobi matrix of order $k + 1$. -/
theorem IsMomentPosDef.mem_spectrum_radauJacobiMatrix {k : ℕ} (h : IsMomentPosDef μ (k + 1))
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b) :
    c ∈ spectrum ℝ (radauJacobiMatrix μ c k) := by
  have hcI : c ∉ Set.Ioo a b := by
    rcases hc with rfl | rfl <;> simp
  have hc0 : (orthogonalPolynomial μ k).eval c ≠ 0 := fun h0 =>
    hcI (h.gaussNodes_subset_Ioo hμ (mem_gaussNodes.mpr h0))
  have hpos : 0 < ∫ x, (1 : ℝ[X]).eval x ^ 2 ∂μ :=
    h 1 one_ne_zero (by simp only [degree_one, Nat.cast_add, Nat.cast_one]; positivity)
  set v : Fin (k + 1) → ℝ := fun i => (orthogonalPolynomial μ i).eval c /
    √(∫ x, (orthogonalPolynomial μ i).eval x ^ 2 ∂μ)
  have hv0 : v ≠ 0 := fun hz => by
    have h0 : v 0 = 0 := congrFun hz 0
    simp only [v, Fin.val_zero, orthogonalPolynomial_zero, eval_one, one_pow] at h0 hpos
    exact (div_ne_zero one_ne_zero (Real.sqrt_pos.mpr hpos).ne') h0
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv0, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    h.radauJacobiMatrix_mulVec_eq hμ hc0, sub_self]

/-- A banded matrix has zero powers off a band of width `i`. -/
private theorem matrix_pow_apply_eq_zero_of_band {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ a b : Fin n, (a : ℕ) + 2 ≤ b ∨ (b : ℕ) + 2 ≤ a → N a b = 0) (i : ℕ) :
    ∀ a b : Fin n, (b : ℕ) + i < a ∨ (a : ℕ) + i < b → (N ^ i) a b = 0 := by
  induction i with
  | zero =>
    intro a b h
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl
    omega
  | succ i ih =>
    intro a b h
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hac : (a : ℕ) + 2 ≤ c ∨ (c : ℕ) + 2 ≤ a
    · rw [hN a c hac, zero_mul]
    · rw [ih c b (by omega), mul_zero]

/-- The powers of the Radau Jacobi matrix agree with those of the Jacobi matrix on the entries
$(a, b)$ with $i + a + b \le 2k$: the only changed entry is the $(k, k)$ loop, which such a walk
never uses. -/
private theorem radauJacobiMatrix_pow_apply_eq (μ : Measure ℝ) (c : ℝ) (k i : ℕ) :
    ∀ a b : Fin (k + 1), (i : ℕ) + a + b ≤ 2 * k →
      (radauJacobiMatrix μ c k ^ i) a b = (jacobiMatrix μ (k + 1) ^ i) a b := by
  have hJ : ∀ a b : Fin (k + 1), (a : ℕ) + 2 ≤ b ∨ (b : ℕ) + 2 ≤ a →
      jacobiMatrix μ (k + 1) a b = 0 := by
    intro a b h
    have h1 : a ≠ b := by rintro rfl; omega
    simp only [jacobiMatrix, Matrix.of_apply]
    rw [if_neg h1, if_neg (by omega), if_neg (by omega)]
  have hM : ∀ a b : Fin (k + 1), ¬(a = Fin.last k ∧ b = Fin.last k) →
      radauJacobiMatrix μ c k a b = jacobiMatrix μ (k + 1) a b := by
    intro a b h
    simp only [radauJacobiMatrix, Matrix.of_apply]
    rw [if_neg h]
  have hMb : ∀ a b : Fin (k + 1), (a : ℕ) + 2 ≤ b ∨ (b : ℕ) + 2 ≤ a →
      radauJacobiMatrix μ c k a b = 0 := by
    intro a b h
    rw [hM a b (by rintro ⟨rfl, rfl⟩; omega), hJ a b h]
  induction i with
  | zero => intro a b _; simp
  | succ i ih =>
    intro a b hab
    rw [pow_succ', Matrix.mul_apply, pow_succ', Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hac : (a : ℕ) + 2 ≤ c ∨ (c : ℕ) + 2 ≤ a
    · rw [hMb a c hac, hJ a c hac, zero_mul, zero_mul]
    by_cases hl : a = Fin.last k ∧ c = Fin.last k
    · obtain ⟨rfl, rfl⟩ := hl
      have hlast : ((Fin.last k : Fin (k + 1)) : ℕ) = k := Fin.val_last k
      rw [matrix_pow_apply_eq_zero_of_band (radauJacobiMatrix μ c k) hMb i (Fin.last k) b
          (Or.inl (by omega)),
        matrix_pow_apply_eq_zero_of_band (jacobiMatrix μ (k + 1)) hJ i (Fin.last k) b
          (Or.inl (by omega))]
      simp
    · rw [hM a c hl, ih c b (by omega)]

/-- The Radau Jacobi matrix keeps the moments of the Jacobi matrix through degree $2k$: for every
measure $\mu$, every $c$ and every $j \le 2k$,
$(\tilde{\mathbf{J}}^j)_{0,0} = (\mathbf{J}_{k+1}^j)_{0,0}$, $\tilde{\mathbf{J}}$ the Radau Jacobi
matrix and $\mathbf{J}_{k+1}$ the Jacobi matrix of order $k + 1$ (they differ only in the
$(k, k)$ entry, which a walk of length at most $2k$ from $0$ to $0$ never reaches). -/
theorem radauJacobiMatrix_pow_apply_zero_zero (μ : Measure ℝ) (c : ℝ) {k j : ℕ}
    (hj : j ≤ 2 * k) : (radauJacobiMatrix μ c k ^ j) 0 0 = (jacobiMatrix μ (k + 1) ^ j) 0 0 :=
  radauJacobiMatrix_pow_apply_eq μ c k j 0 0 (by simpa using hj)

end NLAlib
