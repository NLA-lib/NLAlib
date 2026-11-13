/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramRounded
public import NLAlib.Krylov.FinitePrecision.BackwardBounds
public import NLAlib.Krylov.FinitePrecision.LanczosFunctions

/-!
# Backward models of actual rounded Lanczos outputs

The active prefix supplies the existing exact backward model. Its geometric perturbation
bound needs only local accuracy; the cubic and quadratic bounds retain their explicit
input-only horizon conditions. Padded zero columns are not additional Lanczos run steps.

## Main results

* `NLAlib.LanczosImplementation.exec_rounded_compiled_backward`: actual execution and model bounds.

The compiled-program corollary retains actual decoded outputs and their input-direction
certificate, so it does not assume an initial direction exactly parallel to the input.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation
open scoped Matrix

variable {P ι K : Type} [DecidableEq P]

private theorem model_bounds {N m q : ℕ} (R : LanczosRun N m) (hm : m ≤ q) :
    frobNorm (R.backwardH - R.dilatedH) ≤
      lanczosSmallRoundoffBackwardFactor q * R.ε *
        (1 + (1 + R.ε) * ∑ i ∈ Finset.range q, (1 + 8 * R.ε) ^ (i + 1)) * specNorm R.H ∧
    ((q : ℝ) * R.ε ≤ 1 / 100 → frobNorm (R.backwardH - R.dilatedH) ≤
      lanczosBackwardFactor q * R.ε * specNorm R.H) ∧
    ((q : ℝ) ^ 2 * R.ε ≤ 1 / 1000 → frobNorm (R.backwardH - R.dilatedH) ≤
      lanczosSmallRoundoffBackwardFactor q * R.ε * specNorm R.H) := by
  have he : 0 ≤ R.ε := R.ε_nonneg
  have hmr : (m : ℝ) ≤ q := by exact_mod_cast hm
  have hsum : ∑ i ∈ Finset.range m, (1 + 8 * R.ε) ^ (i + 1) ≤
      ∑ i ∈ Finset.range q, (1 + 8 * R.ε) ^ (i + 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm) (fun _ _ _ => by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have h := R.frobNorm_backwardH_sub_dilatedH_le_geom_sum
    rw [lanczosSmallRoundoffBackwardFactor_def] at h ⊢
    exact h.trans (by gcongr)
  · intro hwin
    have hsmall : (m : ℝ) * R.ε ≤ 1 / 100 :=
      (mul_le_mul_of_nonneg_right hmr he).trans hwin
    refine (R.frobNorm_backwardH_sub_dilatedH_le hsmall).trans ?_
    simp only [lanczosBackwardFactor_def]
    gcongr
  · intro hwin
    have hsmall : (m : ℝ) ^ 2 * R.ε ≤ 1 / 1000 := by
      refine le_trans ?_ hwin
      gcongr
    refine (R.frobNorm_backwardH_sub_dilatedH_le_of_sq_mul_le hsmall).trans ?_
    simp only [lanczosSmallRoundoffBackwardFactor_def]
    gcongr

/-- Actual stored Lanczos execution yields the canonical Hermitian backward model on its
positive active prefix of a symmetric decoded matrix, preserving every declared decoded
output and the input-direction
mismatch. The local budget is
shown by <!-- value lanczosImplementationRoundoffBound N u -->$\varepsilon=16(N+1)^2u$,
with $\varepsilon\le1/100$; the requested budget and decoded input are nonzero.
The model reproduces the active tridiagonal matrix and terminal coefficient exactly.
Its input-only geometric radius is, with <!-- value lanczosSmallRoundoffBackwardFactor q -->
$$1000q^2\varepsilon
\left(1+(1+\varepsilon)\sum_{i<q}(1+8\varepsilon)^{i+1}\right)
\|\mathbf{A}\|_2.$$
When $q\varepsilon\le1/100$, the cubic radius is
shown by <!-- value lanczosBackwardFactor q -->$400q^3\varepsilon\|\mathbf{A}\|_2$.
When $q^2\varepsilon\le1/1000$, the sharper radius is
shown by <!-- value lanczosSmallRoundoffBackwardFactor q -->
$1000q^2\varepsilon\|\mathbf{A}\|_2$.
The geometric bound requires no accumulated smallness condition and may grow with q.
Zero continuation is recorded separately from the active run; no claim is made that the
padded allocated tridiagonal matrix has only eigenvalues near the input spectrum. -/
theorem exec_rounded_compiled_backward {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K (OpCount P ι)) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (values : ℕ → K)
    (hshape : st.store.shape =
      #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N)])
    (hb : ∀ i : Fin N, ∃ w, st.store.read tag 0 i = some w ∧ dec tag w = b i)
    (hrom : ∀ i < N * N, I.rom i = some (values i))
    (hdecode : ∀ i j : Fin N, dec tag (values (N * j + i)) = A i j)
    (hA : Aᵀ = A)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hq : 0 < q) (hbnz : b ≠ 0) :
    ∃ (out : St P K (OpCount P ι)) (s : ℝ) (m : ℕ) (R : LanczosRun N m),
      (lanczosProg.compiled tag).exec I N ![q] st = some out ∧
      out.store.shape =
        #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1), (tag, 1), (tag, N)] ∧
      HoldsDecoded out.store dec tag 0 0 (fun i (_ : Fin 1) => b i) ∧
      (∃ w, out.store.read tag 4 0 = some w ∧ dec tag w = s) ∧
      (StaticCost.mk (lanczosCount tag N q)
        (fun p => if p = tag then N ^ 2 + N + 3 else 0)
        ((N ^ 2 + N + 3) * I.width tag)).Bounds st out ∧
      0 < s ∧ |‖WithLp.toLp 2 b‖ - s| ≤
        roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 b‖ ∧
      ‖WithLp.toLp 2 (b - s • R.v 1)‖ ≤ u tag * ‖WithLp.toLp 2 b‖ ∧
      ‖WithLp.toLp 2 (b - s • R.normalizedV 1)‖ ≤
        (2 * u tag + roundingFactor (N + 1) (u tag)) * ‖WithLp.toLp 2 b‖ ∧
      0 < m ∧ m ≤ q ∧ R.H = A ∧ R.ε = lanczosImplementationRoundoffBound N (u tag) ∧
      HoldsDecoded out.store dec tag 1 0 (fun i (j : Fin (q + 1)) => R.v (j + 1) i) ∧
      HoldsDecoded out.store dec tag 2 0 (fun (j : Fin q) (_ : Fin 1) => R.α (j + 1)) ∧
      HoldsDecoded out.store dec tag 3 0 (fun (j : Fin (q + 1)) (_ : Fin 1) => R.β j) ∧
      HoldsDecoded out.store dec tag 5 0 (fun i (_ : Fin 1) => R.v q i) ∧
      (∀ i, m + 1 < i → R.v i = 0) ∧ (∀ i, m < i → R.α i = 0 ∧ R.β i = 0) ∧
      (R.β m = 0 → R.v (m + 1) = 0) ∧ (m < q → R.β m = 0) ∧
      let B := R.backwardH
      let d := R.dilatedStart
      let ε := lanczosImplementationRoundoffBound N (u tag)
      B.IsHermitian ∧ ‖WithLp.toLp 2 d‖ = 1 ∧
      lanczosTridiagonal B d m = R.tridiagonal ∧
      lanczosMatrix B d m = R.dilatedBasis ∧
      (lanczosState B d m).beta = R.β m ∧
      frobNorm (B - Matrix.blockDiagonal (fun _ : Fin (m + 1) => A)) ≤
        lanczosSmallRoundoffBackwardFactor q * ε *
          (1 + (1 + ε) * ∑ i ∈ Finset.range q, (1 + 8 * ε) ^ (i + 1)) * specNorm A ∧
      ((q : ℝ) * ε ≤ 1 / 100 →
        frobNorm (B - Matrix.blockDiagonal (fun _ : Fin (m + 1) => A)) ≤
          lanczosBackwardFactor q * ε * specNorm A) ∧
      ((q : ℝ) ^ 2 * ε ≤ 1 / 1000 →
        frobNorm (B - Matrix.blockDiagonal (fun _ : Fin (m + 1) => A)) ≤
          lanczosSmallRoundoffBackwardFactor q * ε * specNorm A) := by
  obtain ⟨out, s, v1, erun, shape, input, norm, cost, hs, hnorm, hs0, hv0,
      hunit, hres, hdir, post⟩ :=
    exec_rounded_compiled I tag hsem hz hc st N q A b values hshape hb hrom hdecode hA hsmall
  rcases post with ⟨hzero, _⟩ |
      ⟨m, R, hmpos, hm, hH, hε, hv1, basis, alpha, beta, prev, hv, hαβ, hlast, hstop⟩
  · exact (hzero.elim (fun hq0 => hq.ne' hq0) hbnz).elim
  · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm (fun h => hbnz (hs0.mp h)))
    have hresR : ‖WithLp.toLp 2 (b - s • R.v 1)‖ ≤ u tag * ‖WithLp.toLp 2 b‖ := by
      simpa only [hv1] using hres
    have hdirR : ‖WithLp.toLp 2 (b - s • R.normalizedV 1)‖ ≤
        (2 * u tag + roundingFactor (N + 1) (u tag)) * ‖WithLp.toLp 2 b‖ := by
      simpa only [LanczosRun.normalizedV, hv1, ite_self] using hdir
    have hbnd := model_bounds R hm
    have hbndA :
        frobNorm (R.backwardH - Matrix.blockDiagonal (fun _ : Fin (m + 1) => A)) ≤
          lanczosSmallRoundoffBackwardFactor q * lanczosImplementationRoundoffBound N (u tag) *
            (1 + (1 + lanczosImplementationRoundoffBound N (u tag)) *
              ∑ i ∈ Finset.range q,
                (1 + 8 * lanczosImplementationRoundoffBound N (u tag)) ^ (i + 1)) * specNorm A ∧
        ((q : ℝ) * lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100 →
          frobNorm (R.backwardH - Matrix.blockDiagonal (fun _ : Fin (m + 1) => A)) ≤
            lanczosBackwardFactor q * lanczosImplementationRoundoffBound N (u tag) * specNorm A) ∧
        ((q : ℝ) ^ 2 * lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 1000 →
          frobNorm (R.backwardH - Matrix.blockDiagonal (fun _ : Fin (m + 1) => A)) ≤
            lanczosSmallRoundoffBackwardFactor q *
              lanczosImplementationRoundoffBound N (u tag) * specNorm A) := by
      simpa only [hH, hε, LanczosRun.dilatedH] using hbnd
    exact ⟨out, s, m, R, erun, shape, input, norm, cost, hsp, hnorm, hresR, hdirR,
      hmpos, hm, hH, hε, basis, alpha, beta, prev, hv, hαβ, hlast, hstop,
      R.isHermitian_backwardH, R.norm_dilatedStart, R.lanczosTridiagonal_backwardH_dilatedStart,
      R.lanczosMatrix_backwardH_dilatedStart, R.lanczosState_backwardH_dilatedStart_beta,
      hbndA.1, hbndA.2.1, hbndA.2.2⟩

end NLAlib.LanczosImplementation
