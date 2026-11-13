/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.IdealCoupling
public import NLAlib.Eigensolvers.SpectralBisection.Global
public import NLAlib.Matrix.FinitePrecision.OpsSamplingMeasurable

/-!
# Numerical probability bound for the actual rounded tape reference

The existing spectral-bisection analysis applies to the same word arithmetic, multiplication,
QR and rounded sampler functions as the program. Exact output coupling transfers its bound to
the shifted indexed tape reference. Numerical accuracy, input conditions, rounding regularity
and the ideal tape law are explicit; no execution-success premise is imposed.

## Main results

* `NLAlib.SpectralBisection.measureReal_not_isApproxDiagonalization_tapeMachine_le`: the probability
  of numerical failure is at most the supplied tolerance.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops MeasureTheory ProbabilityTheory

section Numerical

variable {K : Type} [MeasurableSpace K] [MeasurableSingletonClass K]
  (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
  (roundUnif roundGaussian : ℝ → K)

local notation "F" => M.toFloatMachine dec mm qr (M.uniformSample roundUnif)
  (M.normalSample roundGaussian)

/-- Under the original explicit numerical hypotheses, the actual rounded tape reference
fails to approximately diagonalize the input with probability at most `theta`.
The absolute-error floor is explicit and must satisfy the stated smallness bound.
`Ops.StdModel.isAccurate_toFloatMachine` supplies its zero-floor numerical machine hypothesis from
standard scalar rounding, seed-rounding bounds/ranges, multiplication's radius-preservation
property, and the same matrix routines' accuracy contracts. -/
theorem measureReal_not_isApproxDiagonalization_tapeMachine_le
    {u floor bound cN : ℝ} {muM muQ : ℕ → ℝ}
    (hAcc : FloatMachine.IsAccurate F dec u floor bound muM muQ cN)
    (hUnif : Measurable roundUnif) (hGaussian : Measurable roundGaussian)
    (hUnifRange : (Set.range roundUnif).Countable)
    (hGaussianRange : (Set.range roundGaussian).Countable)
    (hMuM : Monotone muM) (hMuQ : Monotone muQ)
    (hMuM0 : 0 ≤ muM 0) (hMuQ0 : 0 ≤ muQ 0) (hCN : 0 ≤ cN)
    {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) (K × K))
    (hA : (decodeMatrix dec A).IsHermitian) (R0 eps beta : K) {theta : ℝ}
    (hRadius : specNorm (decodeMatrix dec A) ≤ dec R0) (hRadiusPos : 0 < dec R0)
    (hEps : 0 < dec eps) (hEpsMax : dec eps ≤ 2⁻¹ ^ 15)
    (hTheta : 0 < theta) (hThetaMax : theta ≤ 1) (ell : ℕ)
    (hDepth : bisectionDepth (dec eps) ≤ ell) (hBeta : 0 < dec beta)
    (hBetaMax : dec beta ≤ ((ell : ℝ) - 1) ^ 2 * dec eps * √theta /
      (52 * (ell : ℝ) ^ 2 * (2 * ell - 1) *
        √(n * min (n : ℝ) (ell + 1) * min (n : ℝ) (Real.exp 1)) *
        (2 * √2 * √(n : ℝ) + √(Real.log (96 * n * min (n : ℝ) (ell + 1) / theta)))))
    {steps : ℝ}
    (hSteps : steps = newtonSchulzSteps (theta / (12 * n * ell * (ell + 1)))
      (dec beta / (16 * n)))
    (hSign : 146 * n * ell * (ell + 1) * (4 * muM n + 10 + 10 * √(n : ℝ)) * u ≤
      theta * dec beta)
    (hStop : 2048 * (n + steps + 1) * (4 * muM n + 10 + 10 * √(n : ℝ)) * u ≤ dec beta)
    (hDeflate : 16 * (4 * muQ n + 4 * √(n : ℝ) * (cN + 1) + 2 * muM n + 1) * u ≤ dec beta)
    (fuel : ℕ) (hFuel : steps ≤ fuel)
    (hFloorNonneg : 0 ≤ floor)
    (hFloor : floor * (100 * n * √(n : ℝ)) ≤
      min (√(theta / (8 * n * min (n : ℝ) (ell + 1)))) (dec eps * min (dec R0) 1))
    (hBound : 16 * (2 * dec R0 + n + 2 * ell + 2 * √2 * √(n : ℝ) +
      √(Real.log (96 * n * min (n : ℝ) (ell + 1) / theta))) ≤ bound)
    {Omega : Type} [MeasurableSpace Omega] {P : Measure Omega}
    {law : ℕ → Measure ℝ} {ideal : Omega → Tape ℝ}
    (hTape : IsTapeLaw law P ideal)
    (hStream : ∀ d : Computation.Dist, law (distributionStream d) = d.law) (base : ℕ) :
    P.real {omega |
      let T := tapeMachine M dec mm qr n base (roundTape roundUnif roundGaussian (ideal omega))
      let result := eigh T fuel ell A R0 eps beta
        (eighSlotTree T n fuel R0 beta 0 0 ⟨n, A, R0, eps, ell⟩)
      ¬ IsApproxDiagonalization (decodeMatrix dec A) (decodeMatrix dec result.1)
        (fun i => dec (result.2 i)) (2 * dec eps * dec R0) (dec eps / 3)} ≤ theta := by
  have hRegular := M.sampler_regular hUnif hGaussian hUnifRange hGaussianRange
  have hTree := iIndepFun_eighIdealTree_idealTape F hRegular.1 hRegular.2.1
    hRegular.2.2.1 hRegular.2.2.2 n fuel (ell + 1) R0 beta ⟨n, A, R0, eps, ell⟩
    le_rfl (hTape.shift base) hStream
  have hProb := hAcc.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw
    hRegular.1 hRegular.2.1 hRegular.2.2.1 hRegular.2.2.2 hMuM hMuQ hMuM0 hMuQ0 hCN
    hn hA hRadius hRadiusPos hEps hEpsMax hTheta hThetaMax hDepth hBeta hBetaMax hSteps
    hSign hStop hDeflate hFuel hFloorNonneg hFloor hBound hTree.1 hTree.2
  simpa only [eigh_tapeMachine_roundTape] using hProb

end Numerical

end NLAlib.SpectralBisection
