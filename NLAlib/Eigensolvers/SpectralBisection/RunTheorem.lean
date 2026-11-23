/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Randomized
public import NLAlib.Eigensolvers.SpectralBisection.OperationCount
public import NLAlib.Eigensolvers.SpectralBisection.Probability
public import NLAlib.Eigensolvers.SpectralBisection.ProbabilityTransfer

/-!
# Spectral bisection: one statement for a run on a random tape

Three results about the dense spectral bisection program are joined here into one statement
about a run on a random tape: the total certificate with explicit work
(`NLAlib.SpectralBisection.countedBisectionAlgorithm`), the transfer of a reference failure bound to
the
run (`NLAlib.SpectralBisection.measureReal_not_accepts_le_of_wordSpecification`), and the
failure bound of the rounded reference computation
(`NLAlib.SpectralBisection.measureReal_not_isApproxDiagonalization_tapeMachine_le`). The event
of the conclusion contains every failure: a failed execution, a violated work, span, scratch or
memory bound, and an inaccurate output.

## Main results

* `NLAlib.SpectralBisection.measureReal_not_accepts_countedSpecification_le`: the statement.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

open Ops MeasureTheory ProbabilityTheory

variable {K : Type} [Inhabited K] [MeasurableSpace K] [MeasurableSingletonClass K]
  {domain : (Fin 3 → ℕ) → Prop} {admitted : ∃ d, domain d}

/-- The radius of an input: the decoded first parameter word, a bound of the spectral norm. -/
abbrev inputRadius (dec : K → ℝ) {d : Fin 3 → ℕ}
    (x : (problem (K := K) domain admitted).Input d) : ℝ := dec (x.val.1.2 0)

/-- The tolerance of an input: the decoded second parameter word. -/
abbrev inputTolerance (dec : K → ℝ) {d : Fin 3 → ℕ}
    (x : (problem (K := K) domain admitted).Input d) : ℝ := dec (x.val.1.2 1)

/-- The sign-iteration parameter of an input: the decoded third parameter word. -/
abbrev inputBeta (dec : K → ℝ) {d : Fin 3 → ℕ}
    (x : (problem (K := K) domain admitted).Input d) : ℝ := dec (x.val.1.2 2)

/-- **Spectral bisection on a random tape: operation count and accuracy on one event.** Let
$\mathbf{A} \in \mathbb{C}^{n \times n}$ be Hermitian with $\|\mathbf{A}\|_2 \le R$, stored as
$n^2$ pairs of words, with a tolerance $0 < \varepsilon \le 2^{-15}$, a parameter $\beta > 0$,
a recursion depth $L \ge \lceil \log_2 \varepsilon^{-1} \rceil + 5$ and an iteration cap $c$
for the Newton–Schulz sign iteration, at least `newtonSchulzSteps`. The program is the
randomized spectral bisection: at each node it shifts by a random point, computes
a matrix sign by Newton–Schulz iteration, extracts the two invariant subspaces by a
randomized rank-revealing QR, and recurses; it calls matrix multiplication and QR as primitives
whose declared cost at order $j$ is at most $T(j)$, with $T$ monotone and superadditive.
Arithmetic is a floating-point machine accurate with unit roundoff $u$ (`FloatMachine.IsAccurate`),
with $u$ small relative to $\theta \beta$ and $\beta$ (hypotheses `hSign`, `hStop`, `hDeflate`),
and the tape holds independent uniform and standard Gaussian draws, rounded to machine words.

Then, for every interpretation of the primitives that meets the model, with probability at
least $1 - \theta$ over the tape the run succeeds, its work and span are at most
$$(L + 1)\, c\, (362 n^{3} + 146 n^{2} + 222 n) + L\, (1587 n^{3} + 760 n^{2} + 2429 n + 305) +
1599 n^{3} + 818 n^{2} + 2509 n + 680 + (L + 1)(2 c + 11)\, T(n),$$
its scratch and memory are within the polynomial bounds of the specification, and it leaves in
memory a matrix $\mathbf{U}$ and a real vector $\mathbf{d}$ with
$$\|\mathbf{A} - \mathbf{U} \operatorname{diag}(\mathbf{d}) \mathbf{U}^{\mathsf{H}}\|_2
\le 2 \varepsilon R, \qquad
(1 - \varepsilon/3)^{2} \mathbf{I} \preceq \mathbf{U}^{\mathsf{H}} \mathbf{U}
\preceq (1 + \varepsilon/3)^{2} \mathbf{I}.$$

The success, the resource bounds and the stored output equal to the reference computation
hold on every tape; only the accuracy of that output is probabilistic. The first four terms of
the work count the instructions that are not matrix operations and overestimate the scalar
overhead of a level, whose blocks are charged at full order; the last term is the matrix work.
The accuracy is that of [Shah2024, Theorem 4.2] for the rounded reference computation.
Result: spectral-bisection-operation-count-accuracy -/
theorem measureReal_not_accepts_countedSpecification_le
    (M : Machine K) (dec : K → ℝ) (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) (T : ℕ → ℕ)
    (hLit : ∀ d, domain d → IsExactNatLit dec M (max (d 0) 4))
    (hN : ∀ d, domain d → 2 ≤ d 0) (hT : Monotone T)
    (hadd : ∀ i j, T i + T j ≤ T (i + j))
    (hMatrix : ∀ o ds, matrixWork o ds ≤ T (ds.foldr max 0))
    (roundUnif roundGaussian : ℝ → K)
    {u floor bound cN : ℝ} {muM muQ : ℕ → ℝ}
    (hAcc : FloatMachine.IsAccurate (M.toFloatMachine dec mm qr (M.uniformSample roundUnif)
      (M.normalSample roundGaussian)) dec u floor bound muM muQ cN)
    (hUnif : Measurable roundUnif) (hGaussian : Measurable roundGaussian)
    (hUnifRange : (Set.range roundUnif).Countable)
    (hGaussianRange : (Set.range roundGaussian).Countable)
    (hMuM : Monotone muM) (hMuQ : Monotone muQ)
    (hMuM0 : 0 ≤ muM 0) (hMuQ0 : 0 ≤ muQ 0) (hCN : 0 ≤ cN)
    {d : Fin 3 → ℕ} (hd : domain d) (x : (problem (K := K) domain admitted).Input d)
    (hA : (decodeMatrix dec (inputMatrix d x)).IsHermitian) {theta : ℝ}
    (hRadius : specNorm (decodeMatrix dec (inputMatrix d x)) ≤ inputRadius dec x)
    (hRadiusPos : 0 < inputRadius dec x)
    (hEps : 0 < inputTolerance dec x) (hEpsMax : inputTolerance dec x ≤ 2⁻¹ ^ 15)
    (hTheta : 0 < theta) (hThetaMax : theta ≤ 1)
    (hDepth : bisectionDepth (inputTolerance dec x) ≤ d 1) (hBeta : 0 < inputBeta dec x)
    (hBetaMax : inputBeta dec x ≤ ((d 1 : ℝ) - 1) ^ 2 * inputTolerance dec x * √theta /
      (52 * (d 1 : ℝ) ^ 2 * (2 * d 1 - 1) *
        √(d 0 * min (d 0 : ℝ) (d 1 + 1) * min (d 0 : ℝ) (Real.exp 1)) *
        (2 * √2 * √(d 0 : ℝ) + √(Real.log (96 * d 0 * min (d 0 : ℝ) (d 1 + 1) / theta)))))
    {steps : ℝ}
    (hSteps : steps = newtonSchulzSteps (theta / (12 * d 0 * d 1 * (d 1 + 1)))
      (inputBeta dec x / (16 * d 0)))
    (hSign : 146 * d 0 * d 1 * (d 1 + 1) * (4 * muM (d 0) + 10 + 10 * √(d 0 : ℝ)) * u ≤
      theta * inputBeta dec x)
    (hStop : 2048 * (d 0 + steps + 1) * (4 * muM (d 0) + 10 + 10 * √(d 0 : ℝ)) * u ≤
      inputBeta dec x)
    (hDeflate : 16 * (4 * muQ (d 0) + 4 * √(d 0 : ℝ) * (cN + 1) + 2 * muM (d 0) + 1) * u ≤
      inputBeta dec x)
    (hFuel : steps ≤ d 2) (hFloorNonneg : 0 ≤ floor)
    (hFloor : floor * (100 * d 0 * √(d 0 : ℝ)) ≤
      min (√(theta / (8 * d 0 * min (d 0 : ℝ) (d 1 + 1))))
        (inputTolerance dec x * min (inputRadius dec x) 1))
    (hBound : 16 * (2 * inputRadius dec x + d 0 + 2 * d 1 + 2 * √2 * √(d 0 : ℝ) +
      √(Real.log (96 * d 0 * min (d 0 : ℝ) (d 1 + 1) / theta))) ≤ bound)
    (I : Interp DenseOp (CmpTst ⊕ IdxTst) K)
    (hI : (Dense.functionalModel (problem (K := K) domain admitted) M dec (EntryCodec.pair K)
      mm qr (Dense.resources matrixWork matrixWorkspace)).contracts d x I)
    {Omega : Type} [MeasurableSpace Omega] {P : Measure Omega} [IsFiniteMeasure P]
    {law : ℕ → Measure ℝ} {ideal : Omega → Tape ℝ}
    (hTape : IsTapeLaw law P ideal)
    (hStream : ∀ dist : Computation.Dist, law (distributionStream dist) = dist.law) :
    P.real {omega | ¬ (countedSpecification M dec mm qr domain admitted matrixWorkspace T).Accepts
        (bisectionProgram (Op := DenseOp) (Tst := CmpTst ⊕ IdxTst)) I
        (Dense.resources matrixWork matrixWorkspace)
        (roundTape roundUnif roundGaussian (ideal omega)) d x
        (fun _ m => StoresApproxDiagonalization dec (inputMatrix d x)
          (2 * inputTolerance dec x * inputRadius dec x) (inputTolerance dec x / 3)
          (2, 0) (3, 0) m)} ≤ theta := by
  have hn : 1 ≤ d 0 := (hN d hd).trans' (by norm_num)
  have hRef := measureReal_not_isApproxDiagonalization_tapeMachine_le M dec mm qr roundUnif
    roundGaussian hAcc hUnif hGaussian hUnifRange hGaussianRange hMuM hMuQ hMuM0 hMuQ0 hCN hn
    (inputMatrix d x) hA (x.val.1.2 0) (x.val.1.2 1) (x.val.1.2 2) hRadius
    hRadiusPos hEps hEpsMax hTheta hThetaMax (d 1) hDepth hBeta hBetaMax hSteps hSign hStop
    hDeflate (d 2) hFuel hFloorNonneg hFloor hBound hTape hStream 0
  have hRun := measureReal_not_accepts_le_of_wordSpecification M dec mm qr _ _ _ _ _
    (countedBisectionAlgorithm M dec mm qr domain admitted matrixWork matrixWorkspace T hLit hN hT
        hadd
      hMatrix) hd x I hI P (fun omega => roundTape roundUnif roundGaussian (ideal omega)) hRef
  refine (measureReal_mono ?_).trans hRun
  intro omega hbad hacc
  obtain ⟨st, hr, hp, hc, hw, hs, hm, -, hq⟩ := hacc
  exact hbad ⟨st, hr, hp, hc, hw, hs, hm, hq⟩

/-! ### The randomized claim -/

/-- Probability laws for the streams with the law of each sample distribution on its stream. -/
theorem exists_law_distributionStream :
    ∃ law : ℕ → Measure ℝ, (∀ s, IsProbabilityMeasure (law s)) ∧
      ∀ dist : Computation.Dist, law (distributionStream dist) = dist.law := by
  refine ⟨fun s => if s = Stream.unif then Computation.Dist.uniform.law else
    if s = Stream.gauss then Computation.Dist.gaussian.law
    else Computation.Dist.rademacher.law, fun s => ?_, fun dist => ?_⟩
  · dsimp only
    split_ifs <;> infer_instance
  · cases dist <;> simp [distributionStream, Stream.unif, Stream.gauss, Stream.sign]

/-- **The randomized claim of the counted spectral bisection certificate** ([Shah2024,
Theorem 4.2], for the rounded reference computation). The tape is the rounding to machine words,
by `roundUnif` and `roundGaussian`, of a tape with independent entries whose stream of each
distribution has that distribution's law (uniform and standard Gaussian). For a Hermitian input
within its stated radius, a tolerance, a parameter $\beta$ and a failure probability $\theta$
satisfying the stated size, precision, underflow and range conditions, the counted run stores a
matrix and a real vector that diagonalize the input to within $2 \varepsilon R$, with the
matrix within $\varepsilon / 3$ of unitary, except with probability at most $\theta$. -/
noncomputable def countedBisectionClaim (M : Machine K) (dec : K → ℝ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K))
    (matrixWork matrixWorkspace : MatrixOp → List ℕ → ℕ) (T : ℕ → ℕ)
    (hLit : ∀ d, domain d → IsExactNatLit dec M (max (d 0) 4))
    (hN : ∀ d, domain d → 2 ≤ d 0) (hT : Monotone T)
    (hadd : ∀ i j, T i + T j ≤ T (i + j))
    (hMatrix : ∀ o ds, matrixWork o ds ≤ T (ds.foldr max 0))
    (roundUnif roundGaussian : ℝ → K)
    {u floor bound cN : ℝ} {muM muQ : ℕ → ℝ}
    (hAcc : FloatMachine.IsAccurate (M.toFloatMachine dec mm qr (M.uniformSample roundUnif)
      (M.normalSample roundGaussian)) dec u floor bound muM muQ cN)
    (hUnif : Measurable roundUnif) (hGaussian : Measurable roundGaussian)
    (hUnifRange : (Set.range roundUnif).Countable)
    (hGaussianRange : (Set.range roundGaussian).Countable)
    (hMuM : Monotone muM) (hMuQ : Monotone muQ)
    (hMuM0 : 0 ≤ muM 0) (hMuQ0 : 0 ≤ muQ 0) (hCN : 0 ≤ cN) (hFloorNonneg : 0 ≤ floor)
    {theta : ℝ} (hTheta : 0 < theta) (hThetaMax : theta ≤ 1) :
    RandomizedClaim (countedBisectionAlgorithm M dec mm qr domain admitted matrixWork
      matrixWorkspace T hLit hN hT hadd hMatrix) where
  law _ _ := fun Ω _ μ ξ => ∃ (law : ℕ → Measure ℝ) (ideal : Ω → Tape ℝ),
    IsTapeLaw law μ ideal ∧
      (∀ dist : Computation.Dist, law (distributionStream dist) = dist.law) ∧
        ξ = fun ω => roundTape roundUnif roundGaussian (ideal ω)
  admits d x := (decodeMatrix dec (inputMatrix d x)).IsHermitian ∧
    specNorm (decodeMatrix dec (inputMatrix d x)) ≤ inputRadius dec x ∧
    0 < inputRadius dec x ∧ 0 < inputTolerance dec x ∧ inputTolerance dec x ≤ 2⁻¹ ^ 15 ∧
    bisectionDepth (inputTolerance dec x) ≤ d 1 ∧ 0 < inputBeta dec x ∧
    inputBeta dec x ≤ ((d 1 : ℝ) - 1) ^ 2 * inputTolerance dec x * √theta /
      (52 * (d 1 : ℝ) ^ 2 * (2 * d 1 - 1) *
        √(d 0 * min (d 0 : ℝ) (d 1 + 1) * min (d 0 : ℝ) (Real.exp 1)) *
        (2 * √2 * √(d 0 : ℝ) + √(Real.log (96 * d 0 * min (d 0 : ℝ) (d 1 + 1) / theta)))) ∧
    146 * d 0 * d 1 * (d 1 + 1) * (4 * muM (d 0) + 10 + 10 * √(d 0 : ℝ)) * u ≤
      theta * inputBeta dec x ∧
    2048 * (d 0 + newtonSchulzSteps (theta / (12 * d 0 * d 1 * (d 1 + 1)))
        (inputBeta dec x / (16 * d 0)) + 1) * (4 * muM (d 0) + 10 + 10 * √(d 0 : ℝ)) * u ≤
      inputBeta dec x ∧
    16 * (4 * muQ (d 0) + 4 * √(d 0 : ℝ) * (cN + 1) + 2 * muM (d 0) + 1) * u ≤
      inputBeta dec x ∧
    newtonSchulzSteps (theta / (12 * d 0 * d 1 * (d 1 + 1)))
      (inputBeta dec x / (16 * d 0)) ≤ d 2 ∧
    floor * (100 * d 0 * √(d 0 : ℝ)) ≤
      min (√(theta / (8 * d 0 * min (d 0 : ℝ) (d 1 + 1))))
        (inputTolerance dec x * min (inputRadius dec x) 1) ∧
    16 * (2 * inputRadius dec x + d 0 + 2 * d 1 + 2 * √2 * √(d 0 : ℝ) +
      √(Real.log (96 * d 0 * min (d 0 : ℝ) (d 1 + 1) / theta))) ≤ bound
  interprets _ _ _ := True
  event d x _ _ m := StoresApproxDiagonalization dec (inputMatrix d x)
    (2 * inputTolerance dec x * inputRadius dec x) (inputTolerance dec x / 3) (2, 0) (3, 0) m
  bound _ _ := theta
  realizable _ _ _ _ := by
    obtain ⟨law, hprob, hlaw⟩ := exists_law_distributionStream
    obtain ⟨Ω, mΩ, μ, ideal, hξ⟩ := exists_isTapeLaw law
    exact ⟨Ω, mΩ, μ, _, hξ.isProbabilityMeasure, law, ideal, hξ, hlaw, rfl⟩
  holds := fun d hd x hx I hI _ Ω _ μ _ tape hlaw => by
    obtain ⟨law, ideal, hTape, hStream, rfl⟩ := hlaw
    obtain ⟨hA, hRadius, hRadiusPos, hEps, hEpsMax, hDepth, hBeta, hBetaMax, hSign, hStop,
      hDeflate, hFuel, hFloor, hBound⟩ := hx
    exact measureReal_not_accepts_countedSpecification_le M dec mm qr matrixWork matrixWorkspace
      T hLit hN hT hadd hMatrix roundUnif roundGaussian hAcc hUnif hGaussian hUnifRange
      hGaussianRange hMuM hMuQ hMuM0 hMuQ0 hCN hd x hA hRadius hRadiusPos hEps hEpsMax hTheta
      hThetaMax hDepth hBeta hBetaMax rfl hSign hStop hDeflate hFuel hFloorNonneg hFloor hBound
      I hI hTape hStream

end NLAlib.SpectralBisection
