/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.BlockKrylov.Samples
public import NLAlib.LowRank.Gaussian.SmallBlock
public import NLAlib.Ops.Probability

/-!
# Gaussian accuracy of the stored output of the block Golub–Kahan program

A random start block $\mathbf{X}$ determines the tape
`NLAlib.BlockKrylov.packedSampleTape`. On that tape every certified run of the program stores
factors whose product is $\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)$ (`NLAlib.rbki`), for every
sample: there is no failure event of the execution. So every statement about
$\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)$ under a law of $\mathbf{X}$ holds of the stored
output, with the word output, the sample advance, the cleanup and every resource bound on the
same counted run.

The certificate is a parameter: any `NLAlib.Ops.Algorithm` for the problem
`NLAlib.Krylov.GolubKahan.Band.Certification.problem` whose postcondition implies
`NLAlib.Krylov.GolubKahan.Band.Certification.Good`. This covers the abstract driver and its link
with any exact orthogonalization scheme.

Two forms are stated. A tail bound transfers through
`NLAlib.Ops.Algorithm.measureReal_failure_le`, for an arbitrary predicate on the approximation.
The operation core has no transfer of expectations; here the stored output is a function of the
start block that equals $\mathsf{rbki}(\mathbf{A}, \cdot, q)$ everywhere, so integrals of the
stored output are integrals of $\mathsf{rbki}$ and no measurability of the run is needed.

## Main definitions

* `NLAlib.BlockKrylov.storedOutput`: the stored product of the run on the tape of a start block.

## Main results

* `NLAlib.BlockKrylov.measureReal_not_accepts_le`: transfer of a tail bound for an arbitrary
  predicate.
* `NLAlib.BlockKrylov.storedOutput_eq_rbki`, `NLAlib.BlockKrylov.integral_comp_storedOutput`:
  transfer of expectations.
* `NLAlib.BlockKrylov.measureReal_not_accepts_le_of_hasLaw_gaussianMatrix`: the gapped tail bound
  for a Gaussian start block of any size, for the stored output.
*
`NLAlib.BlockKrylov.integral_specNorm_sub_storedOutput_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix`:
  the gapped bound in expectation for a Gaussian start block of at least $t + 2$ columns, for the
  stored output.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.BlockKrylov

open Ops MeasureTheory ProbabilityTheory Krylov.GolubKahan.Band
  Krylov.GolubKahan.Band.Certification

variable {Lo : Type} {L : AccessModel Lo CmpTst problem} {S : Specification Lo CmpTst problem}

/-! ### Tail bounds -/

/-- Transfer of a tail bound to the stored output. Let a program be certified for the block
Golub–Kahan problem with a postcondition that implies the exact-run postcondition, let
$\mathbf{A}$ be the $m \times n$ input matrix, and let $\mathbf{X}$ be a random $n \times b$
matrix on a finite measure space. For every predicate $\Phi$ on $m \times n$ matrices, if
$$\mathbb{P}[\neg\,\Phi(\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q))] \le \delta\,,$$
then with probability at least $1 - \delta$ the run on the tape of $\mathbf{X}$ succeeds within
every budget of the specification, satisfies its postcondition, and its stored product
$\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}}$ satisfies $\Phi$. No law of
$\mathbf{X}$, no measurability of $\Phi$ and no success of the execution is assumed. -/
theorem measureReal_not_accepts_le (alg : Algorithm L S) (stream : ℕ)
    (hgood : ∀ d (x : problem.Input d) τ c μ, S.good d x τ c μ → Good stream d (matrix x) τ μ)
    {d : Fin 4 → ℕ} (input : problem.Input d) (I : Interp Lo CmpTst ℝ)
    (hI : L.contracts d input I) {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsFiniteMeasure P] (X : Ω' → Matrix (Fin (d 1)) (Fin (d 2)) ℝ)
    (Φ : Matrix (Fin (d 0)) (Fin (d 1)) ℝ → Prop) {δ : ℝ}
    (hΦ : P.real {ω | ¬ Φ (rbki (matrix input) (X ω) (d 3))} ≤ δ) :
    P.real {ω | ¬ S.Accepts L.resources d input
      (exec alg.program I L.resources problem.formats (packedSampleTape stream (X ω)) d
        (problem.initial d input))
      (fun c μ => S.good d input (packedSampleTape stream (X ω)) c μ ∧
        Φ (storedProduct (d 0) (d 1) (d 2) (d 3) μ))} ≤ δ := by
  refine alg.measureReal_failure_le (P := problem) trivial input I hI
    (fun ω => packedSampleTape stream (X ω)) (fun ω => Φ (rbki (matrix input) (X ω) (d 3))) _ ?_ P
    hΦ
  intro ω c μ hg hR
  refine ⟨hg, ?_⟩
  rw [storedProduct_eq_rbki_of_packedSampleTape (hgood d input _ c μ hg)]
  exact hR

/-- The gapped tail bound for the stored output with a Gaussian start block of any size. Let a
program be certified for the block Golub–Kahan problem with a postcondition that implies the
exact-run postcondition, let $\mathbf{A}$ be the $m \times n$ input matrix with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, and let $\mathbf{X}$ be a standard Gaussian $n \times b$
matrix (independent standard normal entries), $b \ge 1$. For a head of $r = h + 1$ singular
values, a tail index $t \ge r$, depth $q \ge t$, a gap $\Delta > 0$ with
$\sigma_{i+1}^2 \le (1 - \Delta)\sigma_i^2$ for every $i + 1 < t$, $\delta > 0$ and
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, with probability at least $1 - \delta$
the run on the tape of $\mathbf{X}$ succeeds within every budget of the specification, satisfies
its postcondition, and its stored product
$\widehat{\mathbf{A}} = \mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}}$ satisfies
$$\|\mathbf{A} - \widehat{\mathbf{A}}\|_2^2 \le \sigma_r^2 +
32e^{-8(q-t)\sqrt{\gamma}}\,\Delta^{-2(t-1)}\,\frac{t^3}{\delta^3}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
No success of the execution is assumed.
[MeyerMuscoMusco2023, Theorem 6], there for one start vector, as a number of iterations in
$O(\cdot)$ form with unspecified constants. -/
theorem measureReal_not_accepts_le_of_hasLaw_gaussianMatrix (alg : Algorithm L S) (stream : ℕ)
    (hgood : ∀ d (x : problem.Input d) τ c μ, S.good d x τ c μ → Good stream d (matrix x) τ μ)
    {d : Fin 4 → ℕ} (hb : 0 < d 2) (input : problem.Input d) (I : Interp Lo CmpTst ℝ)
    (hI : L.contracts d input I) {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω')
    (X : Ω' → Matrix (Fin (d 1)) (Fin (d 2)) ℝ)
    (hX : HasLaw X (gaussianMatrix (Fin (d 1)) (Fin (d 2))) P) {h r t : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (hq : t ≤ d 3) {Δ δ : ℝ} (hΔ : 0 < Δ) (hδ : 0 < δ)
    (hgap : ∀ i, i + 1 < t →
      singularValues (matrix input) (i + 1) ^ 2 ≤ (1 - Δ) * singularValues (matrix input) i ^ 2) :
    P.real {ω | ¬ S.Accepts L.resources d input
      (exec alg.program I L.resources problem.formats (packedSampleTape stream (X ω)) d
        (problem.initial d input))
      (fun c μ => S.good d input (packedSampleTape stream (X ω)) c μ ∧
        specNorm ((matrix input) - storedProduct (d 0) (d 1) (d 2) (d 3) μ) ^ 2 ≤
          singularValues (matrix input) r ^ 2 +
            32 * Real.exp (-8 * ((d 3 : ℝ) - t) *
              Real.sqrt (singularGapRatio (matrix input) h t)) *
              Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) *
              frobNorm ((matrix input) - truncatedSVD (matrix input) t) ^ 2)} ≤ δ := by
  have : Nonempty (Fin (d 2)) := ⟨⟨0, hb⟩⟩
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hTail := measureReal_specNorm_sub_rbki_sq_gt_le_of_hasLaw_gaussianMatrix (matrix input) hX
    hr hrt hq hΔ hδ hgap
  refine measureReal_not_accepts_le alg stream hgood input I hI P X
    (fun B => specNorm ((matrix input) - B) ^ 2 ≤ singularValues (matrix input) r ^ 2 +
      32 * Real.exp (-8 * ((d 3 : ℝ) - t) * Real.sqrt (singularGapRatio (matrix input) h t)) *
        Δ⁻¹ ^ (2 * (t - 1)) * ((t : ℝ) ^ 3 / δ ^ 3) *
        frobNorm ((matrix input) - truncatedSVD (matrix input) t) ^ 2) ?_
  simpa only [not_le] using hTail

/-! ### Expectations -/

/-- The stored product $\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}}$ of the run of a
certified program on the tape that carries the start block $\mathbf{X}$, as a function of
$\mathbf{X}$; the zero matrix if the run fails, which a certified run never does. -/
noncomputable def storedOutput (alg : Algorithm L S) (stream : ℕ) {d : Fin 4 → ℕ}
    (input : problem.Input d) (I : Interp Lo CmpTst ℝ) (X : Matrix (Fin (d 1)) (Fin (d 2)) ℝ) :
    Matrix (Fin (d 0)) (Fin (d 1)) ℝ :=
  match exec alg.program I L.resources problem.formats (packedSampleTape stream X) d
      (problem.initial d input) with
  | some st => storedProduct (d 0) (d 1) (d 2) (d 3) st.mem
  | none => 0

/-- The stored output is randomized block Krylov iteration, for every start block. Let a program
be certified for the block Golub–Kahan problem with a postcondition that implies the exact-run
postcondition, and let $\mathbf{A}$ be the $m \times n$ input matrix. For every real $n \times b$
matrix $\mathbf{X}$ the stored product of the run on the tape of $\mathbf{X}$ is
$$\mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}} =
\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q)\,.$$
The equality holds everywhere, not almost surely, so the stored output is measurable in
$\mathbf{X}$ whenever $\mathsf{rbki}$ is. -/
theorem storedOutput_eq_rbki (alg : Algorithm L S) (stream : ℕ)
    (hgood : ∀ d (x : problem.Input d) τ c μ, S.good d x τ c μ → Good stream d (matrix x) τ μ)
    {d : Fin 4 → ℕ} (input : problem.Input d) (I : Interp Lo CmpTst ℝ)
    (hI : L.contracts d input I) (X : Matrix (Fin (d 1)) (Fin (d 2)) ℝ) :
    storedOutput alg stream input I X = rbki (matrix input) X (d 3) := by
  obtain ⟨st, hrun, -, -, -, -, -, hg⟩ :=
    alg.correct d trivial input I hI (packedSampleTape stream X)
  simp only [storedOutput, hrun]
  exact storedProduct_eq_rbki_of_packedSampleTape (hgood d input _ _ _ hg)

/-- Transfer of expectations to the stored output. Let a program be certified for the block
Golub–Kahan problem with a postcondition that implies the exact-run postcondition, let
$\mathbf{A}$ be the $m \times n$ input matrix and $\mathbf{X}$ a random $n \times b$ matrix. For
every real function $f$ of an $m \times n$ matrix, with $\widehat{\mathbf{A}}$ the stored product
of the run on the tape of $\mathbf{X}$,
$$\mathbb{E}\,f(\widehat{\mathbf{A}}) =
\mathbb{E}\,f(\mathsf{rbki}(\mathbf{A}, \mathbf{X}, q))\,.$$
The two integrands are equal at every sample, so no law, measurability or integrability is
assumed. -/
theorem integral_comp_storedOutput (alg : Algorithm L S) (stream : ℕ)
    (hgood : ∀ d (x : problem.Input d) τ c μ, S.good d x τ c μ → Good stream d (matrix x) τ μ)
    {d : Fin 4 → ℕ} (input : problem.Input d) (I : Interp Lo CmpTst ℝ)
    (hI : L.contracts d input I) {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω')
    (X : Ω' → Matrix (Fin (d 1)) (Fin (d 2)) ℝ) (f : Matrix (Fin (d 0)) (Fin (d 1)) ℝ → ℝ) :
    ∫ ω, f (storedOutput alg stream input I (X ω)) ∂P =
      ∫ ω, f (rbki (matrix input) (X ω) (d 3)) ∂P := by
  simp only [storedOutput_eq_rbki alg stream hgood input I hI]

/-- The gapped bound in expectation for the stored output with a Gaussian start block. Let a
program be certified for the block Golub–Kahan problem with a postcondition that implies the
exact-run postcondition, let $\mathbf{A}$ be the $m \times n$ input matrix with singular values
$\sigma_0 \ge \sigma_1 \ge \dots$, and let $\mathbf{X}$ be a standard Gaussian $n \times b$
matrix (independent standard normal entries). For $q \ge 1$ blocks, a head of $r = h + 1$
singular values, a tail index $t \ge r$ with $t + 2 \le b$, and
$\gamma = (\sigma_h - \sigma_t)/(\sigma_h + \sigma_t)$, the stored product
$\widehat{\mathbf{A}} = \mathbf{U}\mathbf{S}^{\mathsf{H}}\mathbf{V}^{\mathsf{H}}$ of the run on
the tape of $\mathbf{X}$ satisfies
$$\mathbb{E}\|\mathbf{A} - \widehat{\mathbf{A}}\|_2^2 \le \sigma_r^2 +
4e^{-8(q-1)\sqrt{\gamma}}\,\frac{t}{b - t - 1}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_t\|_{\mathsf{F}}^2\,.$$
[TroppWebber2023, Theorem 9.2 (RBKI)], there with $m = 2q$ products. -/
theorem integral_specNorm_sub_storedOutput_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (alg : Algorithm L S) (stream : ℕ)
    (hgood : ∀ d (x : problem.Input d) τ c μ, S.good d x τ c μ → Good stream d (matrix x) τ μ)
    {d : Fin 4 → ℕ} (input : problem.Input d) (I : Interp Lo CmpTst ℝ)
    (hI : L.contracts d input I) {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω')
    (X : Ω' → Matrix (Fin (d 1)) (Fin (d 2)) ℝ)
    (hX : HasLaw X (gaussianMatrix (Fin (d 1)) (Fin (d 2))) P) {h r t : ℕ} (hr : h + 1 = r)
    (hrt : r ≤ t) (ht : t + 2 ≤ d 2) (hq : 1 ≤ d 3) :
    ∫ ω, specNorm ((matrix input) - storedOutput alg stream input I (X ω)) ^ 2 ∂P ≤
      singularValues (matrix input) r ^ 2 +
        4 * Real.exp (-8 * ((d 3 : ℝ) - 1) * Real.sqrt (singularGapRatio (matrix input) h t)) *
          ((t : ℝ) / ((d 2 : ℝ) - t - 1)) *
          frobNorm ((matrix input) - truncatedSVD (matrix input) t) ^ 2 := by
  have h := integral_specNorm_sub_rbki_sq_le_singularGapRatio_of_hasLaw_gaussianMatrix
    (matrix input) hX hr hrt (by simpa only [Fintype.card_fin] using ht) hq
  rw [integral_comp_storedOutput alg stream hgood input I hI P X
    (fun B => specNorm ((matrix input) - B) ^ 2)]
  simpa only [Fintype.card_fin] using h

end NLAlib.BlockKrylov
