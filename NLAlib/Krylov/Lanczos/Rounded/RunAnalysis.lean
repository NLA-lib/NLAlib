/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.Rounded.ScalarTheorem
public import NLAlib.Krylov.FinitePrecision.LanczosFunctions

/-!
# Ritz values, Paige's bound and matrix functions from the actual rounded Lanczos output

The rounded program returns an existing `NLAlib.LanczosRun` tied to its stored words. This file
states on those words the localization of Ritz values at eigenvalues of the input, Paige's bound
on the loss of orthogonality, and the matrix-function approximation built from the stored basis,
tridiagonal matrix and computed input norm. The only new estimate is the error of the computed
start, from the initial-normalization facts of the output.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.RitzValues`, `NLAlib.Krylov.Lanczos.Rounded.Output.ritzValues`:
  every stored Ritz value is close to an eigenvalue, and Paige's bound holds.
* `NLAlib.Krylov.Lanczos.Rounded.FunctionApprox`,
  `NLAlib.Krylov.Lanczos.Rounded.Output.functionApprox`: the error of the stored approximation
  of $f(\mathbf{A})\mathbf{b}$.
* `NLAlib.Krylov.Lanczos.Rounded.Stored.Certification.exec_scalarProgram_ritzValues`: the Ritz
  value statement for the scalar program.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops Polynomial
open scoped Matrix

variable {K : Type} [Inhabited K] {dec : K → ℝ} {n cap : ℕ}
variable {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {E : ℝ} {vs cs : List K}

/-- A positive active prefix of the stored output whose Ritz values lie near eigenvalues of `A`,
within the spectral interval up to the backward radius, and which satisfies Paige's bound on the
component of a Ritz vector along the next stored vector. -/
def RitzValues (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (E : ℝ) (cap : ℕ) (vs cs : List K) : Prop :=
  ∃ m : ℕ, m + 1 ≤ cap ∧
    (m + 1 < cap → dec (vec cs (cap + (m + 1))) = 0) ∧
    ∀ (y : Fin (m + 1) → ℝ) (θ : ℝ),
      tridiagonalMatrix dec cap cs (m + 1) *ᵥ y = θ • y → ‖WithLp.toLp 2 y‖ = 1 →
      (∃ j < n, |θ - eigenvalue A j| ≤ dec (vec cs (cap + (m + 1))) * |y (Fin.last m)| +
        lanczosBackwardFactor (m + 1) * E * specNorm A) ∧
      θ - eigenvalue A 0 ≤ lanczosBackwardFactor (m + 1) * E * specNorm A ∧
      (∀ l, l + 1 = n → eigenvalue A l - θ ≤ lanczosBackwardFactor (m + 1) * E * specNorm A) ∧
      |(basisMatrix dec n vs (m + 1) *ᵥ y) ⬝ᵥ
          (dec (vec cs (cap + (m + 1))) • fun i : Fin n => dec (vec vs ((m + 1) * n + i)))| *
        |y (Fin.last m)| ≤ lanczosGramCommutatorFactor (m + 1) * E * specNorm A

/-- **Ritz values of the actual rounded Lanczos output.** Every eigenvalue $\theta$ of the stored
tridiagonal matrix, with unit eigenvector $\mathbf{y}$, is within
$\beta_q \lvert y_q \rvert$ plus the backward radius of an eigenvalue of $\mathbf{A}$, and
exceeds the extreme eigenvalues by at most that radius; Paige's bound holds for the same
stored vectors. No orthogonality of the stored basis is assumed. [Paige1980, (3.11)–(3.13)] for
Paige's bound; transfer of the run theorems. -/
theorem Output.ritzValues (h : Output dec A rhs E cap vs cs) (hcap : 0 < cap) (hrhs : rhs ≠ 0)
    (hsmall : (cap : ℝ) * E ≤ 1 / 100) : RitzValues dec A E cap vs cs := by
  obtain ⟨done, hd, z, R, _, hp, rfl, rfl, hv, ha, hb, hstop⟩ := h.exists_run hcap hrhs
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt R.k_pos)
  have hbeta : dec (vec cs (cap + (m + 1))) = R.β (m + 1) := by
    rw [hb]
    exact hp.beta _ hd
  refine ⟨m, hd, fun hs => hbeta.trans (by rw [hb]; exact hstop hs), fun y θ hy hyunit => ?_⟩
  have hprecision : ((m + 1 : ℕ) : ℝ) * R.ε ≤ 1 / 100 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hd) R.ε_nonneg).trans hsmall
  have hBasis : basisMatrix dec n vs (m + 1) = R.basis :=
    hp.basisMatrix_eq (D := R.toLanczosData) hd hv
  have hT := hp.tridiagonalMatrix_eq (D := R.toLanczosData) hd ha hb
  have hy' : R.tridiagonal *ᵥ y = θ • y := by rwa [hT] at hy
  have hnext : (fun i : Fin n => dec (vec vs ((m + 1) * n + i))) = R.v (m + 1 + 1) := by
    funext i
    rw [hv]
    exact hp.basis (m + 1) hd i
  rw [hbeta, hBasis, hnext]
  exact ⟨R.exists_abs_sub_eigenvalue_le_of_mulVec_eq_smul hprecision hy' hyunit,
    R.sub_eigenvalue_zero_le_of_mulVec_eq_smul hprecision hy' hyunit,
    fun l hl => R.eigenvalue_last_sub_le_of_mulVec_eq_smul hprecision hy' hyunit hl,
    R.abs_basis_mulVec_dotProduct_mul_abs_le hprecision hy' hyunit⟩

/-- The computed input norm is at most twice the norm of the input, and the normalized first
vector times it is within `3 * E * ‖b‖` of the input. -/
theorem Outcome.norm_sub_smul_normalizedV_le {done : ℕ} {z : Values n}
    (ho : Outcome A rhs E done z) {m : ℕ} (R : LanczosRun n (m + 1)) (hE : R.ε = E)
    (hv : R.v = z.v) (hrhs : rhs ≠ 0) :
    z.initialNorm ≤ 2 * ‖WithLp.toLp 2 rhs‖ ∧
      ‖WithLp.toLp 2 (rhs - z.initialNorm • R.normalizedV 1)‖ ≤ 3 * E * ‖WithLp.toLp 2 rhs‖ := by
  have hE0 : 0 ≤ E := hE ▸ R.ε_nonneg
  have hE1 : E ≤ 1 / 100 := hE ▸ R.ε_le
  have hs0 := ho.norm_nonneg
  have hsne : z.initialNorm ≠ 0 := fun h => hrhs (ho.norm_zero.mp h)
  have hunit := abs_le.mp (ho.initial_unit hsne)
  have hb0 := _root_.norm_nonneg (WithLp.toLp 2 rhs)
  set N := ‖WithLp.toLp 2 (z.v 1)‖ with hN
  have hN0 : 0 ≤ N := _root_.norm_nonneg _
  have hN9 : 9 / 10 ≤ N := by
    by_contra hlt
    nlinarith [not_le.mp hlt, hunit.1]
  have hsN : z.initialNorm * N ≤ (1 + E) * ‖WithLp.toLp 2 rhs‖ := by
    have htri : ‖WithLp.toLp 2 (z.initialNorm • z.v 1)‖ ≤
        ‖WithLp.toLp 2 rhs‖ + ‖WithLp.toLp 2 (rhs - z.initialNorm • z.v 1)‖ := by
      have := norm_sub_le (WithLp.toLp 2 rhs) (WithLp.toLp 2 (rhs - z.initialNorm • z.v 1))
      simpa using this
    have hsmul : ‖WithLp.toLp 2 (z.initialNorm • z.v 1)‖ = z.initialNorm * N := by
      rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hs0]
    linarith [ho.initial_error]
  have hs2 : z.initialNorm ≤ 2 * ‖WithLp.toLp 2 rhs‖ := by nlinarith
  refine ⟨hs2, ?_⟩
  have hdiff : ‖WithLp.toLp 2 (z.v 1 - R.normalizedV 1)‖ ≤ E := by
    have := R.norm_v_sub_normalizedV_le (j := 1) le_rfl (by omega)
    rwa [hv, hE] at this
  have hsplit : rhs - z.initialNorm • R.normalizedV 1 =
      (rhs - z.initialNorm • z.v 1) + z.initialNorm • (z.v 1 - R.normalizedV 1) := by
    rw [smul_sub]
    abel
  rw [hsplit, WithLp.toLp_add]
  refine (norm_add_le _ _).trans ?_
  rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hs0]
  nlinarith [ho.initial_error, mul_le_mul hs2 hdiff (_root_.norm_nonneg _) (by positivity)]

/-- A positive active prefix of the stored output whose approximation
$s\,\mathbf{V} f(\mathbf{T}) \mathbf{e}_1$ of $f(\mathbf{A})\mathbf{b}$, formed from the stored
words and the computed input norm $s$, inherits the error of a polynomial approximation of $f$
of degree below the prefix on the interval widened by the backward radius. -/
def FunctionApprox (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (rhs : Fin n → ℝ)
    (E : ℝ) (cap : ℕ) (vs cs : List K) : Prop :=
  ∃ m : ℕ, m + 1 ≤ cap ∧
    (m + 1 < cap → dec (vec cs (cap + (m + 1))) = 0) ∧
    ∀ (a a' ρ B δ η : ℝ) (f : ℝ → ℝ) (p : ℝ[X]), a < a' → spectrum ℝ A ⊆ Set.Icc a a' →
      0 ≤ ρ → lanczosBackwardFactor (m + 1) * E * specNorm A ≤ ρ → p.degree < (m + 1 : ℕ) →
      Metric.IsUniformApproxOn (fun t => p.eval t) f (Set.Icc (a - ρ) (a' + ρ)) δ →
      0 ≤ B → (∀ t ∈ Set.Icc (a - ρ) (a' + ρ), |f t| ≤ B) → η ≤ 1 →
      Real.sqrt ((m + 1 : ℕ) + 1) * polynomialDerivativeFactor (m + 1) / (a' - a + 2 * ρ) *
        (lanczosBackwardFactor (m + 1) * E * specNorm A) + Real.sqrt (m + 1 : ℕ) * E ≤ η →
      ‖WithLp.toLp 2 (cfc f A *ᵥ rhs - dec (vec cs (2 * cap + 1)) •
          (basisMatrix dec n vs (m + 1) *ᵥ
            (cfc f (tridiagonalMatrix dec cap cs (m + 1)) *ᵥ Pi.single ⟨0, Nat.succ_pos m⟩ 1)))‖ ≤
        3 * E * B * ‖WithLp.toLp 2 rhs‖ +
          2 * ‖WithLp.toLp 2 rhs‖ * (lanczosFunctionApproxFactor (m + 1) * δ + η * B)

/-- Matrix functions from the actual rounded Lanczos output. The vector
$s\,\mathbf{V} f(\mathbf{T}) \mathbf{e}_1$ read from the stored words approximates
$f(\mathbf{A})\mathbf{b}$ up to the polynomial approximation error of $f$ on the spectral
interval widened by the backward radius, with the error of the computed start included. The
small matrix function and the final products are exact: this is a statement about the stored
factors, and no program forms the vector. No printed source; transfer of the run theorems. -/
theorem Output.functionApprox (h : Output dec A rhs E cap vs cs) (hcap : 0 < cap)
    (hrhs : rhs ≠ 0) (hsmall : (cap : ℝ) * E ≤ 1 / 100) :
    FunctionApprox dec A rhs E cap vs cs := by
  obtain ⟨done, hd, z, R, ho, hp, hA, hE, hv, ha, hb, hstop⟩ := h.exists_run hcap hrhs
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt R.k_pos)
  have hbeta : dec (vec cs (cap + (m + 1))) = R.β (m + 1) := by
    rw [hb]
    exact hp.beta _ hd
  refine ⟨m, hd, fun hs => hbeta.trans (by rw [hb]; exact hstop hs), ?_⟩
  intro a a' ρ B δ η f p hab hs hρ0 hρ hpd happ hB hf hη hprec
  subst hA hE
  have hprecision : ((m + 1 : ℕ) : ℝ) * R.ε ≤ 1 / 100 :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hd) R.ε_nonneg).trans hsmall
  have hBasis : basisMatrix dec n vs (m + 1) = R.basis :=
    hp.basisMatrix_eq (D := R.toLanczosData) hd hv
  have hT := hp.tridiagonalMatrix_eq (D := R.toLanczosData) hd ha hb
  have hnorm : dec (vec cs (2 * cap + 1)) = z.initialNorm := hp.initialNorm
  obtain ⟨hs2, hinit⟩ := ho.norm_sub_smul_normalizedV_le R rfl hv hrhs
  have hE' := R.norm_cfc_mulVec_sub_functionApprox_le_of_precision hab hs hprecision hρ hpd happ
    hB hf hη hprec
  have hf' : ∀ t ∈ Set.Icc a a', |f t| ≤ B := fun t ht =>
    hf t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmain := R.norm_cfc_mulVec_sub_le_of_norm_sub_smul_le hs hB hf' ho.norm_nonneg hE' rhs
    (z.initialNorm • R.functionApprox f) hinit (ζ := 0) (by simp)
  rw [hnorm, hBasis, hT]
  have hEb : 0 ≤ lanczosFunctionApproxFactor (m + 1) * δ + η * B := (_root_.norm_nonneg _).trans hE'
  have hprod := mul_le_mul_of_nonneg_right hs2 hEb
  refine le_trans (le_of_eq_of_le ?_ hmain) ?_
  · rfl
  · nlinarith [mul_le_mul_of_nonneg_left hinit hB]

namespace Stored.Certification

variable {domain : (Fin 2 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- **Scalar Lanczos in rounded arithmetic: Ritz values and matrix functions.** Let
$\mathbf{A} \in \mathbb{R}^{n \times n}$ be symmetric, stored entry by entry, let
$\mathbf{b} \ne \mathbf{0}$ and let $k > 0$ be the cap. Run the scalar Lanczos program without
reorthogonalization on a machine in the standard model with unit roundoff $u$, with an allowance
$E$ dominating the rounding of its operations (`Lanczos.Rounded.Precision`) and $k E \le 1/100$.
Then every run succeeds within $33 n^{2} k + 153 n k + 302 k + 58 n + 179$ instructions, and its
stored words satisfy `NLAlib.Krylov.Lanczos.Rounded.RitzValues` (each Ritz value is near an
eigenvalue of $\mathbf{A}$, with Paige's bound) and `NLAlib.Krylov.Lanczos.Rounded.FunctionApprox`
(the stored factors approximate $f(\mathbf{A})\mathbf{b}$).
[Paige1980, (3.11)–(3.13)] for Paige's bound; transfer of the run theorems. -/
theorem exec_scalarProgram_ritzValues (M : Machine ℝ) (u : ℝ)
    (hM : StdModel u id M) (hu : 0 ≤ u) (E : (Fin 2 → ℕ) → ℝ)
    (hprec : ∀ d, domain d → Lanczos.Rounded.Precision
      (ScalarProducts.roundoff u (d 0) * Real.sqrt (d 0)) u (E d) (Blas.seq.err u) (d 0))
    {d : Fin 2 → ℕ} (hd : domain d) (x : (problem domain admitted).Input d)
    (hk : 0 < d 1) (hb : x.val.1.2 ≠ 0) (hs : (d 1 : ℝ) * E d ≤ 1 / 100)
    (I : Interp ScalarOp CmpTst ℝ)
    (hI : (RoundedScalarBlas.model (problem domain admitted) M).contracts d x I) (τ : Tape ℝ) :
    ∃ st, Reference.Execution
        scalarProgram I RoundedScalarBlas.resources (problem domain admitted).formats τ d
        ((problem domain admitted).initial d x) st ∧
      RoundedScalarBlas.resources.work st.cost ≤
        33 * d 0 ^ 2 * d 1 + 153 * d 0 * d 1 + 302 * d 1 + 58 * d 0 + 179 ∧
      ∃ vs cs, st.mem.store.readBlock 2 0 ((d 1 + 1) * d 0) = some vs ∧
        st.mem.store.readBlock 3 0 (2 * d 1 + 2) = some cs ∧
        RitzValues id x.val.1.1 (E d) (d 1) vs cs ∧
        FunctionApprox id x.val.1.1 x.val.1.2 (E d) (d 1) vs cs := by
  obtain ⟨st, hr, hw, vs, cs, hvs, hcs, hout, -⟩ :=
    exec_scalarProgram_work_le_and_ritzResidual M u hM hu E hprec hd x I hI τ
  exact ⟨st, hr, hw, vs, cs, hvs, hcs, hout.ritzValues hk hb hs, hout.functionApprox hk hb hs⟩

end Stored.Certification

end NLAlib.Krylov.Lanczos.Rounded
