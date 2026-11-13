/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramRounded
public import NLAlib.Krylov.FinitePrecision.CGEnergyEstimator

/-!
# The backward model and physical energy of the actual rounded CG program

The registered stored-entry tree constructs its own positive-length CGRun under primitive
scalar contracts and an input-only spectral horizon. The same returned decoded iterate is
compared directly in energy with exact CG on its canonical full-prefix backward model.
The perturbation term and physical rounding remainder are retained separately.

## Main results

* `NLAlib.CGImplementation.exec_rounded_compiled_backward`: program execution, backward
  perturbation, exact model trajectory and physical energy comparison.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open Computation
open scoped Matrix

variable {P ι K : Type} [DecidableEq P] {u : P → ℝ} {dec : P → K → ℝ}

/-- The actual stored CG tree, under an unbounded relative-error scalar contract with exact
addition of zero, produces a backward model and a physical-energy certificate. Let $N$ be the
matrix dimension, $q>0$ the requested budget, $\mathbf{b}$ the nonzero decoded input,
with <!-- value cgImplementationRoundoffBound N u -->$\varepsilon=4N^2u$, and
$\kappa=a'/a$. Assume $u<1$, $\varepsilon\le1/100$, symmetric
$\mathbf{A}$ with spectrum in $[a,a']$, $a>0$, and
$q^2\sqrt q\varepsilon\kappa^2\le10^{-5}$. Actual execution completes $0<m\le q$ active
steps, possibly stopping early, and returns the decoded physical vector $\widehat{\mathbf{x}}$.
The canonical model $\mathbf{B}$ has spectrum in $[a/2,a'+a/2]$, starts from
$\mathbf{d}=(\mathbf{b},0,\ldots)$, and its exact CG step lengths and residual norms match
those of the computed run. Its perturbation radius is, with <!-- value cgBackwardFactor m -->
$\delta_m=6000m^2\sqrt{m}\varepsilon\kappa a'$. The physical rounding remainder is,
with <!-- value cgEnergyEstimatorFactor 0 m -->
$R_m=150m(0+m)\varepsilon\kappa\|\mathbf{b}\|^2/a$.
For physical and model solutions $\mathbf{A}\mathbf{x}_\star=\mathbf{b}$ and
$\mathbf{B}\mathbf{y}_\star=\mathbf{d}$, the returned decoded iterate satisfies
$$\left\lvert\|\mathbf{x}_\star-\widehat{\mathbf{x}}\|_{\mathbf{A}}^2-
 \|\mathbf{y}_\star-\mathsf{cgIterate}(\mathbf{B},\mathbf{d},0,m)\|_{\mathbf{B}}^2\right\rvert
 \le 2\|\mathbf{b}\|^2\delta_m/a^2+R_m.$$
The scalar program theorem supplies actual output and resource ties; the energy comparison
uses the canonical direct physical-energy estimator, with no residual-to-energy conversion.
Zero budget or decoded zero input is covered by `exec_rounded_compiled`, without constructing
an impossible zero-length run. -/
theorem exec_rounded_compiled_backward (I : Interp P ι K (OpCount P ι)) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (hu : u tag < 1) (hc : IsUnitCharge I)
    (st : St P K (OpCount P ι)) (N q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → K) (vals : ℕ → K)
    (hshape : st.store.shape = #[(tag, N), (tag, N), (tag, N), (tag, N), (tag, 1)])
    (hb : ∀ i : Fin N, st.store.read tag 0 i = some (b i))
    (hrom : ∀ i < N * N, I.rom i = some (vals i))
    (hdecode : ∀ i j : Fin N, dec tag (vals (i + N * j)) = A i j)
    (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ A ⊆ Set.Icc a a')
    (horizon : CGPrecisionHorizon q (cgImplementationRoundoffBound N (u tag)) (a' / a))
    (hq : 0 < q) (hbnz : (fun i => dec tag (b i)) ≠ 0) :
    ∃ (out : St P K (OpCount P ι)) (flag : ℝ) (m : ℕ) (R : CGRun N m),
      (cgProg.compiled tag).exec I N ![q] st = some out ∧
      out.store.shape = #[(tag, N), (tag, N), (tag, N), (tag, N), (tag, 1)] ∧
      0 < flag ∧ |flag - 1| ≤ u tag ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 0 i = some w ∧ dec tag w = dec tag (b i)) ∧
      (StaticCost.mk (cgCount tag N q) (fun p => if p = tag then N ^ 2 + N + 10 else 0)
        ((N ^ 2 + N + 10) * I.width tag)).Bounds st out ∧
      0 < m ∧ m ≤ q ∧ R.A = A ∧ R.b = (fun i => dec tag (b i)) ∧
      R.ε = cgImplementationRoundoffBound N (u tag) ∧
      (∀ i : Fin N, ∃ wx wr wp, out.store.read tag 1 i = some wx ∧ dec tag wx = R.x m i ∧
        out.store.read tag 2 i = some wr ∧ dec tag wr = R.r m i ∧
        out.store.read tag 3 i = some wp ∧ dec tag wp = R.p m i) ∧
      (∃ w, out.store.read tag 4 0 = some w ∧ dec tag w = if R.r m = 0 then flag else 0) ∧
      (m < q → R.r m = 0) ∧
      let B := R.backwardH
      let d := R.dilatedRhs
      let ε := cgImplementationRoundoffBound N (u tag)
      let δ := cgBackwardFactor m * ε * (a' / a) * a'
      B.PosDef ∧ spectrum ℝ B ⊆ Set.Icc (a / 2) (a' + a / 2) ∧
      frobNorm (B - Matrix.blockDiagonal (fun _ : Fin (m + 1) => A)) ≤ δ ∧
      ‖WithLp.toLp 2 d‖ = ‖WithLp.toLp 2 (fun i => dec tag (b i))‖ ∧
      (∀ j < m, cgAlpha B (cgState B d 0 j) = R.γ j) ∧
      (∀ j ≤ m, ‖WithLp.toLp 2 (cgState B d 0 j).r‖ = R.ρ j) ∧
      (∀ (xs : Fin N → ℝ), A *ᵥ xs = (fun i => dec tag (b i)) →
        ∀ (ys : Fin N × Fin (m + 1) → ℝ), B *ᵥ ys = d →
        |quadForm A (xs - R.x m) - quadForm B (ys - cgIterate B d 0 m)| ≤
          2 * ‖WithLp.toLp 2 (fun i => dec tag (b i))‖ ^ 2 * δ / a ^ 2 +
          cgEnergyEstimatorFactor 0 m * ε * (a' / a) *
            (‖WithLp.toLp 2 (fun i => dec tag (b i))‖ ^ 2 / a)) := by
  obtain ⟨out, flag, erun, shape, hflag, hflagerr, input, hcost, hpost⟩ :=
    exec_rounded_compiled I tag hsem hz hu hc st N q A b vals hshape hb hrom hdecode
      hsmall hA ha hspec horizon
  rcases hpost with ⟨hzero, _⟩ | ⟨m, R, hm, hRA, hRb, hRε, hvec, hstatus, hstop⟩
  · exact (hzero.elim (fun hq0 => (hq.ne' hq0).elim) (fun hb0 => (hbnz hb0).elim))
  · have hprec : 0 ≤ cgImplementationRoundoffBound N (u tag) := hRε ▸ R.ε_nonneg
    have hRsmall : CGPrecisionHorizon m R.ε (a' / a) := by
      rw [hRε]
      exact horizon.mono hprec hm
    have hsR : spectrum ℝ R.A ⊆ Set.Icc a a' := by simpa only [hRA] using hspec
    have hspecB := R.spectrum_backwardH_subset_Icc ha hsR hRsmall
    have hPD := R.isHermitian_backwardH.posDef_of_spectrum_subset_Icc
      (by positivity : (0 : ℝ) < a / 2) hspecB
    refine ⟨out, flag, m, R, erun, shape, hflag, hflagerr, input, hcost,
      R.k_pos, hm, hRA, hRb, hRε, hvec, hstatus, hstop, hPD, hspecB, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [CGRun.dilatedH, hRA, hRε] using
        R.frobNorm_backwardH_sub_dilatedH_le ha hsR hRsmall
    · simpa only [hRb] using R.norm_dilatedRhs
    · exact fun j hj => R.cgAlpha_backwardH ha hsR hRsmall hj
    · exact fun j hj => R.norm_cgState_backwardH_r ha hsR hRsmall hj
    · intro xs hx ys hy
      have hxR : R.A *ᵥ xs = R.b := by simpa only [hRA, hRb] using hx
      simpa only [hRA, hRb, hRε] using
        R.abs_quadForm_sub_x_sub_quadForm_backwardH_sub_cgIterate_le
          ha hsR hRsmall hxR hy (j := m) le_rfl

end NLAlib.CGImplementation
