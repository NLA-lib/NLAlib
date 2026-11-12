/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Lanczos.RoundedStability
public import NLAlib.Krylov.Lanczos.RoundedSolve

/-!
# Ritz residuals from actual rounded Lanczos output

The same numerical run that accounts for every packed output entry also supplies the existing
finite-precision Ritz residual estimate. Its active prefix excludes initialized zero tails.
The resulting physical Ritz vector need not be unit: the estimate is a residual bound for
that actual vector, without an assumed orthogonality certificate for the rounded basis.

## Main results

* `NLAlib.Krylov.Lanczos.Rounded.PackedOutput.basisMatrix_eq`: physical basis readback.
* `NLAlib.Krylov.Lanczos.Rounded.PackedOutput.tridiagonalMatrix_eq`: coefficient readback.
* `NLAlib.Krylov.Lanczos.Rounded.Output.ritzResidual`: actual rounded Ritz residual.
* `NLAlib.Krylov.Lanczos.Rounded.runs_solve_ritz`: total successful program and residual bound.
-/

@[expose] public section

namespace NLAlib.Krylov.Lanczos.Rounded

open Ops
open scoped Matrix

variable {K : Type} [Inhabited K] {dec : K → ℝ} {n cap q : ℕ}
variable {z : Values n} {vs cs : List K}

/-- The decoded active basis prefix is the basis of the same physically identified
recurrence data. -/
theorem PackedOutput.basisMatrix_eq (h : PackedOutput dec cap z vs cs)
    (hq : q ≤ cap) {D : LanczosData n q} (hv : D.v = z.v) :
    basisMatrix dec n vs q = D.basis := by
  funext i j
  change dec (vec vs (j * n + i)) = D.v (j + 1) i
  rw [hv]
  exact h.basis j (by omega) i

/-- The diagonal and couplings read from storage are the same recurrence's tridiagonal matrix. -/
theorem PackedOutput.tridiagonalMatrix_eq (h : PackedOutput dec cap z vs cs)
    (hq : q ≤ cap) {D : LanczosData n q} (ha : D.α = z.alpha) (hb : D.β = z.beta) :
    tridiagonalMatrix dec cap cs q = D.tridiagonal := by
  funext i j
  simp only [tridiagonalMatrix, LanczosData.tridiagonal, Matrix.of_apply]
  split_ifs
  · rw [ha]
    exact h.alpha i (by omega)
  · rw [hb]
    exact h.beta i (by omega)
  · rw [hb]
    exact h.beta j (by omega)
  · rfl

/-- A positive active prefix of the stored tridiagonal has bounded physical Ritz residuals.
The coefficient vector is unit; its image under the computed basis need not be unit or even
bounded below in norm. The residual factor is the existing six-times-length-times-square-root
factor. This predicate makes no eigenvalue-error claim. -/
def RitzResidual (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (E : ℝ) (cap : ℕ) (vs cs : List K) : Prop :=
    ∃ m : ℕ, m + 1 ≤ cap ∧
      (m + 1 < cap → dec (vec cs (cap + (m + 1))) = 0) ∧
      ∀ (y : Fin (m + 1) → ℝ) (θ : ℝ),
        tridiagonalMatrix dec cap cs (m + 1) *ᵥ y = θ • y →
        ‖WithLp.toLp 2 y‖ = 1 →
        ‖WithLp.toLp 2 (A *ᵥ (basisMatrix dec n vs (m + 1) *ᵥ y) -
          θ • (basisMatrix dec n vs (m + 1) *ᵥ y))‖ ≤
          Real.sqrt (1 + E) * dec (vec cs (cap + (m + 1))) * |y (Fin.last m)| +
            lanczosResidualFactor (m + 1) * E * specNorm A

/-- Every unit eigenpair of the actual active tridiagonal has the standard finite-precision
physical Ritz residual bound. Positive cap and nonzero input give an active prefix; the
linear accumulated precision condition on the cap also bounds its actual executed length.
The basis need not be orthogonal and the physical Ritz vector is not asserted to be unit.
The factor <!-- value lanczosResidualFactor q --> $6q\sqrt{q}$ is the existing recurrence
residual factor at the active length. No printed source; transfer of the pure run bound. -/
theorem Output.ritzResidual {A : Matrix (Fin n) (Fin n) ℝ}
    {rhs : Fin n → ℝ} {E : ℝ} (h : Output dec A rhs E cap vs cs)
    (hcap : 0 < cap) (hrhs : rhs ≠ 0) (hsmall : (cap : ℝ) * E ≤ 1 / 100) :
    RitzResidual dec A E cap vs cs := by
  obtain ⟨done, hd, z, R, _, hp, hA, hE, hv, ha, hb, hstop⟩ :=
    h.exists_run hcap hrhs
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt R.k_pos)
  have hbeta : dec (vec cs (cap + (m + 1))) = R.β (m + 1) := by
    rw [hb]
    exact hp.beta _ hd
  have hterminal : m + 1 < cap → R.β (m + 1) = 0 := by
    intro hs
    rw [hb]
    exact hstop hs
  refine ⟨m, hd, fun hs => hbeta.trans (hterminal hs), ?_⟩
  intro y θ hy hyunit
  have hprecision : ((m + 1 : ℕ) : ℝ) * R.ε ≤ 1 / 100 := by
    rw [hE]
    have hnonneg : 0 ≤ E := hE ▸ R.ε_nonneg
    exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hd) hnonneg).trans hsmall
  have hBasis : basisMatrix dec n vs (m + 1) = R.basis :=
    hp.basisMatrix_eq (D := R.toLanczosData) hd hv
  have hbound := R.norm_mulVec_basis_mulVec_sub_smul_le hprecision
    (by rwa [hp.tridiagonalMatrix_eq (D := R.toLanczosData) hd ha hb] at hy) hyunit
  simpa only [← hBasis, hA, hE, ← hbeta,
    LanczosRun.lastIndex, LanczosData.lastIndex, Nat.add_sub_cancel, Nat.succ_sub_one,
    Fin.last] using hbound

/-- Complete rounded Lanczos output with a Ritz residual bound whenever a nonempty run is
required. Zero cap and zero input retain their existing initialized output meaning. -/
def RitzOutput (dec : K → ℝ) {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rhs : Fin n → ℝ) (E : ℝ) (cap : ℕ) (vs cs : List K) : Prop :=
  Output dec A rhs E cap vs cs ∧
    (cap = 0 ∨ rhs = 0 ∨ RitzResidual dec A E cap vs cs)

/-- Every actual output has a residual guarantee or an explicit zero-cap/zero-input outcome.
There is no assumed successful execution and no division by the physical Ritz-vector norm. -/
theorem Output.ritzOutput {A : Matrix (Fin n) (Fin n) ℝ} {rhs : Fin n → ℝ} {E : ℝ}
    (h : Output dec A rhs E cap vs cs) (hsmall : (cap : ℝ) * E ≤ 1 / 100) :
    RitzOutput dec A rhs E cap vs cs := by
  refine ⟨h, ?_⟩
  by_cases hc : cap = 0
  · exact Or.inl hc
  by_cases hb : rhs = 0
  · exact Or.inr (Or.inl hb)
  exact Or.inr (Or.inr (h.ritzResidual (Nat.pos_of_ne_zero hc) hb hsmall))

variable {Op Tst : Type}
variable [Has ScalarOp Op] [Has Blas1Op Op] [Has OperatorOp Op] [Has CmpTst Tst]

/-- Rounded matvec, scalar, BLAS and comparison contracts, a symmetric input, normalization
precision imply successful Lanczos execution. Under the
linear accumulated precision bound, the same packed output satisfies the physical Ritz
residual estimate, including early termination. No prior successful run is assumed. -/
theorem runs_solve_ritz {M : Machine K} {dec : K → ℝ} {n cap : ℕ}
    {em u E : ℝ} {e : Blas1Err} {A : Matrix (Fin n) (Fin n) ℝ}
    {I : Interp Op Tst K} {ok : ℕ → Prop}
    (hS : IsScalar M I) (hM : StdModel u dec M) (hB : IsBlas1 dec e ok I) (hok : ok n)
    (hA : IsMatvec dec A (em * specNorm A) I) (hCmp : IsCmp dec I)
    (hAT : Aᵀ = A) (hprec : Precision em u E e n)
    (W : Op → List ℕ → ℕ) {τ : Tape K} {μ : Mem K} {B V C : ℕ × ℕ} {bs : List K}
    (hBV : B.1 ≠ V.1) (hBC : B.1 ≠ C.1) (hVC : V.1 ≠ C.1)
    (hl : μ.Live [B, V, C]) (hb : μ.store.readBlock B.1 B.2 n = some bs)
    (hz : μ.Room [V, C] [(cap + 1) * n, 2 * cap + 2])
    (hsmall : (cap : ℝ) * E ≤ 1 / 100) :
    ConditionalRuns I W τ solve (Env.frame [n, cap] [B, V, C]) μ
      (solveCount n cap) (solvePeak W n)
      (fun μ' => μ'.pos = μ.pos ∧ ∃ vs cs,
        μ'.store.readBlock V.1 V.2 ((cap + 1) * n) = some vs ∧
        μ'.store.readBlock C.1 C.2 (2 * cap + 2) = some cs ∧
        RitzOutput dec A (decv dec n bs) E cap vs cs) := by
  refine (runs_solve hS hM hB hok hA hCmp hAT hprec W hBV hBC hVC hl hb hz).mono
    le_rfl le_rfl ?_
  rintro μ' ⟨hpos, vs, cs, hv, hc, hout⟩
  exact ⟨hpos, vs, cs, hv, hc, hout.ritzOutput hsmall⟩

end NLAlib.Krylov.Lanczos.Rounded
