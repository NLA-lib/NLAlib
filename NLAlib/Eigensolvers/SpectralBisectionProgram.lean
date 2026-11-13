/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.BoundedFormat
public import NLAlib.RandomMatrix.Computation.SpectralBisectionTargets
public import NLAlib.Eigensolvers.SpectralBisectionSamples.Lazy
public import NLAlib.Eigensolvers.SpectralBisectionSamples.IdealMachine
public import NLAlib.Matrix.Computation.SpectralBisectionProgram
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Count
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.Weight

/-!
# Hermitian diagonalization in linear precision, for the program

[Shah2024, Theorem 4.2] for the registered tree `NLAlib.eighProg.compiled`, a program of the model
of computation, by transfer of the shallow theorems on `NLAlib.eigh`
(`NLAlib/Eigensolvers/SpectralBisection/Global.lean`) through the refinement: every run succeeds and
writes `NLAlib.eigh` on the tape machine with the tree of sample positions at the slots, which is
`NLAlib.eigh` on the ideal machine with the tree of ideal samples, independent with law
`NLAlib.eighSampleLaw` on the ideal tape.

The two program conclusions have different scopes. The registered target assumes global
scalar success and bounds failure or inaccurate output. The bounded-format theorem bounds
only the event that a successful execution returns an inaccurate output; it gives no
execution-success probability. The binary128-layout shallow witnesses in
`SpectralBisection/Instance.lean` store arbitrary reals and do not establish successful
finite-word program execution.

## Main results

* `NLAlib.matrixFreeRoundedProbEigh`: the target `NLAlib.MatrixFreeRoundedProbEigh`, from the
  shallow Theorem 4.2 and the weighted kernel bound
  `NLAlib.eighProg.weight_le_of_exec_compiled`.
* `NLAlib.matrixFreeRoundedProb_eighProg_of_logb_le`: the bit count, from the shallow bit count.
* `NLAlib.measureReal_exists_exec_eighProg_and_not_isApproxDiagonalization_le_of_exponentBits_le`: a
  bounded binary format, from the shallow bounded-format theorem, for the runs that succeed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

open Computation

-- A docstring line exceeds 100 characters (one identifier).
set_option linter.style.longLine false in
/-- **Randomized spectral bisection as a program, in finite precision** (the target
`NLAlib.MatrixFreeRoundedProbEigh` holds): the registered tree `eighProg.compiled`, run under any
interpretation whose semantics meets the standard model at unit roundoff $u$ with every value in
range, with exact integer literals, the exact floor conversion and multiplication that does not
enlarge by a factor of modulus at most one, whose kernels meet `NLAlib.IsMatMulErr` and
`NLAlib.IsQRErr` at $u$, and whose tape rounding meets `NLAlib.Computation.IsTapeRounding`, on a
stored $N \times N$ input with Hermitian decoding $\mathbf{A}$, $\|\mathbf{A}\|_2 \le R_0$, and the
precision, floor, range and sample conditions of
`NLAlib.FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw`
at the machine roundoff $(c(\mathrm{uniform}) + 1)u$, fails, exceeds its operation and cell
counts, exceeds the weighted kernel count $(\ell + 1)(2F + 12)\,T(N)$ for a monotone
superadditive cost $T$ of a kernel call by its largest dimension, or returns stored
$\mathbf{U}$, $\mathbf{d}$ that are not an approximate diagonalization of $\mathbf{A}$ with residual
$2\varepsilon R_0$ and $\mathbf{U}$ within $\varepsilon/3$ of unitary with probability at most
$\theta$. Its output is $\mathsf{eigh}(\mathbf{A}, \varepsilon)$ on the machine of the
interpretation. [Shah2024, Theorem 4.2], there for the algorithm, not a program, with an
operation count in flops.
Result: spectral-bisection-rounded-program -/
theorem matrixFreeRoundedProbEigh : MatrixFreeRoundedProbEigh := by
  intro P ι _ p mm qr K _ dec u Ω θ μM μQ c
  refine MatrixFreeRoundedProb.of_exec (fun _ _ _ h => h) ?_ ?_
  · intro N n x I st hI hex
    obtain ⟨ℓ, F, rfl⟩ : ∃ ℓ F, n = ![ℓ, F] := ⟨n 0, n 1, by ext i; fin_cases i <;> rfl⟩
    obtain ⟨hc, hm⟩ := eighProg.cnt_le_of_exec_compiled (fun k => congrFun hI k) p N ℓ F hex
    refine ⟨by simpa [inputState] using hc, fun q => ?_⟩
    have h := hm q
    by_cases hq : q = p
    · subst hq
      simp [inputState, EntryLayout.size_toArray, pairLayout] at h ⊢
      nlinarith
    · simpa [inputState, hq] using h
  intro N n _ x hpre I ρ hidx hI hρO hch Ω' _ μ ξ hξ
  obtain ⟨ℓ, F, rfl⟩ : ∃ ℓ F, n = ![ℓ, F] := ⟨n 0, n 1, by ext i; fin_cases i <;> rfl⟩
  have hlit : IsExactIntLit dec I.sem (N + 4) := hidx.intLit
  have htn : IsExactToNat dec I.sem := hidx.toNat
  obtain ⟨hsem, hmul, ⟨mmR, hmm, hmmE⟩, qrR, hqr, hqrE⟩ := hI
  obtain ⟨hρT, hρs, hρc⟩ := hρO
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hpre
  obtain ⟨hn, hH, hR₀, hR₀pos, hε, hε₁, hθ, hθ₁, hℓ, hβ, hβle, hu0, hcu, hcg, hcgu, hμM, hμQ,
    hμM0, hμQ0, husign, hustop, hudefl, hfuel, hΩ⟩ := hpre
  have hℓ5n : 5 ≤ ℓ := by unfold bisectionDepth at hℓ; omega
  have hℓ5 : (5 : ℝ) ≤ ℓ := by exact_mod_cast hℓ5n
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hs0 := Real.sqrt_nonneg (Real.log (96 * (N : ℝ) * min (N : ℝ) (ℓ + 1) / θ))
  have hs2 : 0 ≤ 2 * √2 * √(N : ℝ) := by positivity
  have hM := isAccurate_eighIdealMachine hsem (fun q k hk => hlit q k (by omega)) htn hmul p
    hmmE hqrE hρT (by linarith) hu0 hcu hcg hcgu (fun d => hμM0.trans (hμM (Nat.zero_le d)))
    (fun d => hμQ0.trans (hμQ (Nat.zero_le d)))
  have hunif := countable_range_uniformUnif I.sem p (hρc .uniform).1 (hρc .uniform).2
  have hgauss := countable_range_gaussianNormal I.sem p (hρc .gaussian).1 (hρc .gaussian).2
  obtain ⟨hind, hlaw⟩ := iIndepFun_eighIdealTree (I.sem.toFloatMachine p
    (fun x => (I.sem.toNat p x).getD 0) mmR qrR (I.sem.uniformUnif p (ρ .uniform 0))
    (I.sem.gaussianNormal p (ρ .gaussian 0))) hunif.2 hunif.1 hgauss.2 hgauss.1 N F (ℓ + 1)
    x.R₀ x.β ⟨N, x.A, x.R₀, x.ε, ℓ⟩ le_rfl hξ
  have hτ : (0 : ℝ) * (100 * N * √(N : ℝ)) ≤
      min (√(θ / (8 * N * min (N : ℝ) (ℓ + 1)))) (dec p x.ε * min (dec p x.R₀) 1) := by
    rw [zero_mul]
    exact le_min (Real.sqrt_nonneg _) (mul_nonneg hε.le (le_min hR₀pos.le zero_le_one))
  have key :=
    FloatMachine.IsAccurate.measureReal_not_isApproxDiagonalization_eigh_le_of_hasLaw_eighSampleLaw
    hM hunif.2 hunif.1 hgauss.2 hgauss.1 hμM hμQ hμM0 hμQ0 (by positivity) hn hH hR₀ hR₀pos hε
    hε₁ hθ hθ₁ hℓ hβ hβle rfl husign hustop hudefl hfuel le_rfl hτ hΩ hind hlaw
  have := hξ.isProbabilityMeasure
  refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top μ _)) key
  intro hAD
  obtain ⟨st₀, hexec⟩ := eighProg.exists_exec_compiled
    (I := { I with tape := fun d i => ρ d i (ξ ω d i) }) hmm hqr hsem p (by nlinarith) N ℓ F
    (by omega) hlit htn x.A x.R₀ x.ε x.β hR₀pos.le
  have hH := eighProg.holds_of_exec_compiled (I := { I with tape := fun d i => ρ d i (ξ ω d i) })
    hmm hqr p (hsem.decidesFlags (fun q k hk => hlit q k (by omega)) p) (hsem.cmp_le p) N ℓ F hlit
    htn x.A x.R₀ x.ε x.β hexec
  have he := eigh_eighTapeMachine_eq_eigh_eighIdealTree I p mmR qrR ρ hρs (ξ ω) F ℓ x.A x.R₀
    x.ε x.β
  dsimp only at hH he
  rw [he] at hH
  refine hω ⟨st₀, hexec, ⟨_, _, hH.1, hH.2, hAD⟩, fun T hT hTs => ?_⟩
  simpa [inputState] using eighProg.weight_le_of_exec_compiled
    (I := { I with tape := fun d i => ρ d i (ξ ω d i) }) (congrFun hch) p N ℓ F hlit htn T hT hTs
    hexec

/-- **The bit count of Hermitian diagonalization, for the program**: the registered tree
`NLAlib.eighProg.compiled` meets the rounded probabilistic model at all sizes $N$ and
$n = (\ell, F)$ (the depth counter and the sign step limit), for every stored input (declared
buffers $0$: the matrix, interleaved and column-major; $1$: $R_0$, $\varepsilon$, $\beta$; $2$, $3$:
$2N^2$ and $N$ empty cells), under every interpretation whose semantics meets the standard model at
$u$ with every value in range, exact integer literals up to $N + 4$, the exact floor conversion and
`MulShrinks`, whose kernels are routines on pairs meeting `IsMatMulErr` and `IsQRErr` at $u$,
floor $0$, range $\Omega$, and every rounding $\rho$ of the tape meeting `IsTapeRounding` at range
$2\Omega$, independent of the position and with countable range and measurable fibres. Let
$u_{\mathrm M} = (c(\mathrm{uniform}) + 1)u$ be the machine roundoff, $c_{\mathrm N} =
2(c(\mathrm{gaussian}) + 3)$ the normal-sampler constant and $\hat\beta$ the bound on $\beta$ of the
shallow theorem. If $N \ge 1$, the decoded matrix $\mathbf{A}$ is Hermitian with
$\|\mathbf{A}\|_2 \le R_0$, $R_0 > 0$, $0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$, $\ell$ is
at least the bisection depth of $\varepsilon$, $\hat\beta/(1 + 2^{-6}) \le \beta \le \hat\beta$ with
$\beta > 0$, $u > 0$, $c(\mathrm{uniform}), c(\mathrm{gaussian}) \ge 0$ with
$(c(\mathrm{gaussian}) + 3)u \le 1/10$, $\mu_{\mathrm{MM}}$ and $\mu_{\mathrm{QR}}$ are monotone and
nonnegative, $\log_2(1/u_{\mathrm M})$ is at least $\log_2(1/\varepsilon) + \tfrac32\log_2(1/\theta)
+ O(\log n + \log\log(1/\varepsilon))$ bits, with the polynomial factor
$n^{2.5}\max(\mu_{\mathrm{MM}}, \sqrt n)$, and at least $\log_2(1/\beta)$ plus the logarithm of the
error factor of the sign steps, the Newton–Schulz step count is at most $F$ and $\Omega$ bounds the
values of the run, then the probability that the run fails, exceeds the counts
`eighCount p mm qr N ℓ F` or $4N^2 + N + 3 + 64(N + 1)^2(\ell + 3)$ cells at tag `p`, or ends with
stored $\mathbf{U}$, $\mathbf{d}$ in declared buffers $2$, $3$ that are not an approximate
diagonalization of $\mathbf{A}$ with residual $2\varepsilon R_0$ and singular values within
$\varepsilon/3$ of $1$ is at most $\theta$. [Shah2024, Theorem 4.2], for the program. No printed
source. -/
theorem matrixFreeRoundedProb_eighProg_of_logb_le (P ι : Type) [DecidableEq P] (p : P)
    (mm qr : ι) (K : Type) [Inhabited K] (dec : P → K → ℝ) (u Ω θ : ℝ) (μM μQ : ℕ → ℝ)
    (c : Dist → ℝ) :
    MatrixFreeRoundedProb p (eighProg.compiled p mm qr) (fun _ _ => True)
      (fun N _ => EighData K N)
      (fun N _ x => ![(pairLayout.toArray x.A).map some, #[some x.R₀, some x.ε, some x.β],
        Array.replicate (2 * (N * N)) none, Array.replicate N none])
      dec (fun N _ => N + 4) (fun N n => eighCount p mm qr N (n 0) (n 1))
      (fun N n q => if q = p then 4 * (N * N) + N + 3 + 64 * (N + 1) ^ 2 * (n 0 + 3) else 0)
      (fun _ _ I => IsRelErrSem (fun _ => u) dec (fun _ _ => True) I.sem ∧ MulShrinks dec I.sem ∧
        (∃ mmR : MatMulMap (K × K), IsMatMulKernel I mm pairLayout mmR ∧
          IsMatMulErr (decodeComplex (dec p)) u 0 Ω μM mmR) ∧
        ∃ qrR : QRMap (K × K), IsQRKernel I qr pairLayout qrR ∧
          IsQRErr (decodeComplex (dec p)) u 0 Ω μQ qrR)
      (fun ρ => IsTapeRounding dec p u 0 (2 * Ω) c ρ ∧
        (∀ (g : Dist) (i j : ℕ) (y : ℝ), ρ g i y = ρ g j y) ∧
        ∀ g : Dist, (Set.range (ρ g 0)).Countable ∧ ∀ z, MeasurableSet (ρ g 0 ⁻¹' {z}))
      (fun N n x =>
        let uM := (c .uniform + 1) * u
        let cN := 2 * (c .gaussian + 3)
        let ℓ := n 0
        let βb := ((ℓ : ℝ) - 1) ^ 2 * dec p x.ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
          √(N * min (N : ℝ) (ℓ + 1) * min (N : ℝ) (Real.exp 1)) *
          (2 * √2 * √(N : ℝ) + √(Real.log (96 * N * min (N : ℝ) (ℓ + 1) / θ))))
        let Nst := newtonSchulzSteps (θ / (12 * N * ℓ * (ℓ + 1))) (dec p x.β / (16 * N))
        1 ≤ N ∧ (decodeMatrix (dec p) x.A).IsHermitian ∧
        specNorm (decodeMatrix (dec p) x.A) ≤ dec p x.R₀ ∧ 0 < dec p x.R₀ ∧
        0 < dec p x.ε ∧ dec p x.ε ≤ 2⁻¹ ^ 15 ∧ 0 < θ ∧ θ ≤ 1 ∧ bisectionDepth (dec p x.ε) ≤ ℓ ∧
        0 < dec p x.β ∧ dec p x.β ≤ βb ∧ βb / (1 + 2⁻¹ ^ 6) ≤ dec p x.β ∧
        0 < u ∧ 0 ≤ c .uniform ∧ 0 ≤ c .gaussian ∧ (c .gaussian + 3) * u ≤ 1 / 10 ∧
        Monotone μM ∧ Monotone μQ ∧ 0 ≤ μM 0 ∧ 0 ≤ μQ 0 ∧
        Real.logb 2 (dec p x.ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
          Real.logb 2 (N * (4 * μM N + 10 + 10 * √(N : ℝ))) +
          1 / 2 * Real.logb 2 (N * min (N : ℝ) (ℓ + 1) * min (N : ℝ) (Real.exp 1)) +
          Real.logb 2 (2 * √2 * √(N : ℝ) + √(Real.log (96 * N * min (N : ℝ) (ℓ + 1) / θ))) +
          Real.logb 2 (ℓ * (ℓ + 1)) +
          Real.logb 2 ((ℓ : ℝ) ^ 2 * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2) + 13 ≤
            Real.logb 2 uM⁻¹ ∧
        Real.logb 2 (dec p x.β)⁻¹ +
          Real.logb 2 (2048 * (N + Nst + 1) * (4 * μM N + 10 + 10 * √(N : ℝ)) +
            16 * (4 * μQ N + 4 * √(N : ℝ) * (cN + 1) + 2 * μM N + 1)) ≤ Real.logb 2 uM⁻¹ ∧
        Nst ≤ n 1 ∧
        16 * (2 * dec p x.R₀ + N + 2 * ℓ + 2 * √2 * √(N : ℝ) +
          √(Real.log (96 * N * min (N : ℝ) (ℓ + 1) / θ))) ≤ Ω)
      (fun N _ x st => ∃ (U : Matrix (Fin N) (Fin N) (K × K)) (d : Fin N → K),
        pairLayout.Holds st.store p 2 0 U ∧ (∀ i : Fin N, st.store.read p 3 i = some (d i)) ∧
        IsApproxDiagonalization (decodeMatrix (dec p) x.A) (decodeMatrix (dec p) U)
          (fun i => dec p (d i)) (2 * dec p x.ε * dec p x.R₀) (dec p x.ε / 3))
      (fun _ _ _ => θ) := by
  refine MatrixFreeRoundedProb.of_exec (fun _ _ _ h => h) ?_ ?_
  · intro N n x I st hI hex
    obtain ⟨ℓ, F, rfl⟩ : ∃ ℓ F, n = ![ℓ, F] := ⟨n 0, n 1, by ext i; fin_cases i <;> rfl⟩
    obtain ⟨hc, hm⟩ := eighProg.cnt_le_of_exec_compiled (fun k => congrFun hI k) p N ℓ F hex
    refine ⟨by simpa [inputState] using hc, fun q => ?_⟩
    have h := hm q
    by_cases hq : q = p
    · subst hq
      simp [inputState, EntryLayout.size_toArray, pairLayout] at h ⊢
      nlinarith
    · simpa [inputState, hq] using h
  intro N n _ x hpre I ρ hidx hI hρO _ Ω' _ μ ξ hξ
  obtain ⟨ℓ, F, rfl⟩ : ∃ ℓ F, n = ![ℓ, F] := ⟨n 0, n 1, by ext i; fin_cases i <;> rfl⟩
  have hlit : IsExactIntLit dec I.sem (N + 4) := hidx.intLit
  have htn : IsExactToNat dec I.sem := hidx.toNat
  obtain ⟨hsem, hmul, ⟨mmR, hmm, hmmE⟩, qrR, hqr, hqrE⟩ := hI
  obtain ⟨hρT, hρs, hρc⟩ := hρO
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hpre
  obtain ⟨hn, hH, hR₀, hR₀pos, hε, hε₁, hθ, hθ₁, hℓ, hβ, hβle, hβge, hu0, hcu, hcg, hcgu, hμM,
    hμQ, hμM0, hμQ0, hbits, hbits', hfuel, hΩ⟩ := hpre
  have hℓ5n : 5 ≤ ℓ := by unfold bisectionDepth at hℓ; omega
  have hℓ5 : (5 : ℝ) ≤ ℓ := by exact_mod_cast hℓ5n
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hs0 := Real.sqrt_nonneg (Real.log (96 * (N : ℝ) * min (N : ℝ) (ℓ + 1) / θ))
  have hs2 : 0 ≤ 2 * √2 * √(N : ℝ) := by positivity
  have hM := isAccurate_eighIdealMachine hsem (fun q k hk => hlit q k (by omega)) htn hmul p
    hmmE hqrE hρT (by linarith) hu0.le hcu hcg hcgu (fun d => hμM0.trans (hμM (Nat.zero_le d)))
    (fun d => hμQ0.trans (hμQ (Nat.zero_le d)))
  have hunif := countable_range_uniformUnif I.sem p (hρc .uniform).1 (hρc .uniform).2
  have hgauss := countable_range_gaussianNormal I.sem p (hρc .gaussian).1 (hρc .gaussian).2
  obtain ⟨hind, hlaw⟩ := iIndepFun_eighIdealTree (I.sem.toFloatMachine p
    (fun x => (I.sem.toNat p x).getD 0) mmR qrR (I.sem.uniformUnif p (ρ .uniform 0))
    (I.sem.gaussianNormal p (ρ .gaussian 0))) hunif.2 hunif.1 hgauss.2 hgauss.1 N F (ℓ + 1)
    x.R₀ x.β ⟨N, x.A, x.R₀, x.ε, ℓ⟩ le_rfl hξ
  have hτ : (0 : ℝ) * (100 * N * √(N : ℝ)) ≤
      min (√(θ / (8 * N * min (N : ℝ) (ℓ + 1)))) (dec p x.ε * min (dec p x.R₀) 1) := by
    rw [zero_mul]
    exact le_min (Real.sqrt_nonneg _) (mul_nonneg hε.le (le_min hR₀pos.le zero_le_one))
  have key := hM.measureReal_not_isApproxDiagonalization_eigh_le_of_logb_le_of_hasLaw_eighSampleLaw
    hunif.2 hunif.1 hgauss.2 hgauss.1 hμM hμQ hμM0 hμQ0 (by positivity) hn hH hR₀ hR₀pos hε
    hε₁ hθ hθ₁ hℓ hβ hβle hβge rfl (mul_pos (by linarith) hu0) hbits hbits' hfuel le_rfl hτ hΩ
    hind hlaw
  have := hξ.isProbabilityMeasure
  refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top μ _)) key
  intro hAD
  obtain ⟨st₀, hexec⟩ := eighProg.exists_exec_compiled
    (I := { I with tape := fun d i => ρ d i (ξ ω d i) }) hmm hqr hsem p (by nlinarith) N ℓ F
    (by omega) hlit htn x.A x.R₀ x.ε x.β hR₀pos.le
  have hH := eighProg.holds_of_exec_compiled (I := { I with tape := fun d i => ρ d i (ξ ω d i) })
    hmm hqr p (hsem.decidesFlags (fun q k hk => hlit q k (by omega)) p) (hsem.cmp_le p) N ℓ F hlit
    htn x.A x.R₀ x.ε x.β hexec
  have he := eigh_eighTapeMachine_eq_eigh_eighIdealTree I p mmR qrR ρ hρs (ξ ω) F ℓ x.A x.R₀
    x.ε x.β
  dsimp only at hH he
  rw [he] at hH
  exact hω ⟨st₀, hexec, _, _, hH.1, hH.2, hAD⟩

/-- The exponent-bit condition of the bounded format puts the smallest normal number
$2^{e_{\min} + p - 1}$ at most $1/2$: it asks for at least $3$ exponent bits. -/
private theorem floor_le_half_of_exponentBits_le (fmt : Float.Model.Format) {N ℓ : ℕ} {e θ : ℝ}
    (he : 0 < e) (he₁ : e ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1)
    (hexp : Real.logb 2 (Real.logb 2 (1536 * (N + ℓ + 2) ^ 3 / (e * θ)) + 2) + 1 ≤
      fmt.exponentBits) :
    (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1) ≤ 1 / 2 := by
  have heθ : e * θ ≤ 1 := mul_le_one₀ (he₁.trans (by norm_num)) hθ.le hθ₁
  have hM : (1 : ℝ) ≤ ((N : ℝ) + ℓ + 2) ^ 3 :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N), (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)])
  have hL : 4 ≤ 1536 * ((N : ℝ) + ℓ + 2) ^ 3 / (e * θ) := by
    rw [le_div_iff₀ (mul_pos he hθ)]
    nlinarith
  have h1 : 2 ≤ Real.logb 2 (1536 * ((N : ℝ) + ℓ + 2) ^ 3 / (e * θ)) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_two]
    linarith
  have h2 : 2 ≤ Real.logb 2 (Real.logb 2 (1536 * ((N : ℝ) + ℓ + 2) ^ 3 / (e * θ)) + 2) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_two]
    linarith
  have hE3 : 3 ≤ fmt.exponentBits := by
    have : (3 : ℝ) ≤ fmt.exponentBits := by linarith
    exact_mod_cast this
  have hτeq : fmt.minExponent + (fmt.mantissaBits : ℤ) - 1 =
      -((2 : ℤ) ^ (fmt.exponentBits - 1) - 2) := by
    simp only [Float.Model.Format.minExponent]; ring
  have h4 : (4 : ℤ) ≤ 2 ^ (fmt.exponentBits - 1) :=
    (show (4 : ℤ) = 2 ^ 2 by norm_num) ▸ pow_le_pow_right₀ (by norm_num) (by omega)
  rw [hτeq]
  calc (2 : ℝ) ^ (-((2 : ℤ) ^ (fmt.exponentBits - 1) - 2)) ≤ 2 ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ one_le_two (by omega)
    _ = 1 / 2 := by norm_num

-- The proof names the general bounded-format theorem, longer than 100 characters.
set_option linter.style.longLine false in
/-- Hermitian diagonalization in a bounded binary format, for the runs of the program that succeed:
let `fmt` be a binary format with at least $2$ exponent bits, unit roundoff $u = 2^{-p}$ ($p$ the
precision), floor $\tau = 2^{e_{\min} + p - 1}$ (the smallest normal number) and largest finite
number $\Omega_F$. Let the semantics of `I` meet the floor model
`NLAlib.Computation.IsFloorRelErrSem` at $u$, $\tau$ and the range condition
$\lvert a\rvert \le \Omega_F$, with `NLAlib.Computation.MulShrinks`, exact integer literals up to
$N + 4$ and the exact floor conversion, and decode every stored value at tag `p` into
$[-\Omega_F, \Omega_F]$; let the kernels of `I` be routines on pairs meeting `NLAlib.IsMatMulErr`
and `NLAlib.IsQRErr` at $u$, floor $\tau$ and range $\Omega_F/2$ with constants $\mu_{\mathrm{MM}}$,
$\mu_{\mathrm{QR}}$ monotone and nonnegative; and let the tape be a position-independent rounding
$\rho$ of an ideal tape $\xi$ of law `NLAlib.Computation.tapeLaw`, meeting
`NLAlib.Computation.IsTapeRounding` at $u$, floor $\tau$, range $\Omega_F$ and constants
$c(d) \ge 0$ with $(c(\mathrm{gaussian}) + 3)u \le 1/10$, with countable ranges and measurable
fibres. Let $u_{\mathrm M} = (c(\mathrm{uniform}) + 1)u$ (the uniform shift rounds a draw and a
product) and $c_{\mathrm N} = 3(c(\mathrm{gaussian}) + 3)$. If $N \ge 1$, the decoded matrix
$\mathbf{A}$ is Hermitian with $\|\mathbf{A}\|_2 \le R_0$, $1/2 \le R_0 \le 1$,
$0 < \varepsilon \le 2^{-15}$, $0 < \theta \le 1$, $\ell$ is at least the bisection depth of
$\varepsilon$, $\hat\beta/(1 + 2^{-6}) \le \beta \le \hat\beta$ with $\beta > 0$ for the bound
$\hat\beta$ of the shallow theorem, $\log_2(1/u_{\mathrm M})$ is at least
$\log_2(1/\varepsilon) + \tfrac32\log_2(1/\theta) + O(\log n + \log\log(1/\varepsilon))$ and at
least $\log_2(1/\beta)$ plus the logarithm of the error factor of the sign steps (with
$c_{\mathrm N}$), the exponent bits are at least
$\log_2(\log_2(1536(N + \ell + 2)^3/(\varepsilon\theta)) + 2) + 1$ and the Newton–Schulz step
count $N_{\mathrm{st}}$ is at most $F$, then the probability that the run succeeds and its output is
not an approximate diagonalization with residual $2\varepsilon R_0$ and singular values within
$\varepsilon/3$ of $1$ is at most $\theta$. This bounds only the runs that succeed: success under
a bounded format (no operation out of range) is not claimed, as it needs a range analysis of
every operation of a run (design note, decision D6), so this is not [Shah2024, Theorem 4.2] end
to end. No printed source. -/
theorem measureReal_exists_exec_eighProg_and_not_isApproxDiagonalization_le_of_exponentBits_le
    {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] (p : P) (mm qr : ι)
    {dec : P → K → ℝ} {I : Interp P ι K C} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
    (hmm : IsMatMulKernel I mm pairLayout mmR) (hqr : IsQRKernel I qr pairLayout qrR)
    (fmt : Float.Model.Format) (hE : 2 ≤ fmt.exponentBits)
    (hsem : IsFloorRelErrSem (fun _ => (2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      (fun _ => (2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) dec
      (fun _ a => |a| ≤ fmt.maxFinite) I.sem)
    (hmul : MulShrinks dec I.sem) (hrange : ∀ x : K, |dec p x| ≤ fmt.maxFinite)
    {N ℓ F : ℕ} (hlit : IsExactIntLit dec I.sem (N + 4))
    (htn : IsExactToNat dec I.sem) {μM μQ : ℕ → ℝ}
    (hmmE : IsMatMulErr (decodeComplex (dec p)) ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) (fmt.maxFinite / 2) μM mmR)
    (hqrE : IsQRErr (decodeComplex (dec p)) ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) (fmt.maxFinite / 2) μQ qrR)
    {ρ : Dist → ℕ → ℝ → K} {c : Dist → ℝ}
    (hρT : IsTapeRounding dec p ((2 : ℝ)⁻¹ ^ fmt.mantissaBits)
      ((2 : ℝ) ^ (fmt.minExponent + fmt.mantissaBits - 1)) fmt.maxFinite c ρ)
    (hρ : ∀ (g : Dist) (i j : ℕ) (y : ℝ), ρ g i y = ρ g j y)
    (hcountu : ∀ g : Dist, (Set.range (ρ g 0)).Countable ∧ ∀ z, MeasurableSet (ρ g 0 ⁻¹' {z}))
    (hcu : 0 ≤ c .uniform) (hcg : 0 ≤ c .gaussian)
    (hcgu : (c .gaussian + 3) * (2 : ℝ)⁻¹ ^ fmt.mantissaBits ≤ 1 / 10)
    (hμM : Monotone μM) (hμQ : Monotone μQ) (hμM₀ : 0 ≤ μM 0) (hμQ₀ : 0 ≤ μQ 0)
    (hn : 1 ≤ N) {A : Matrix (Fin N) (Fin N) (K × K)} (hA : (decodeMatrix (dec p) A).IsHermitian)
    {R₀ ε β : K} {θ : ℝ} (hR₀ : specNorm (decodeMatrix (dec p) A) ≤ dec p R₀)
    (hR₀half : 1 / 2 ≤ dec p R₀) (hR₀one : dec p R₀ ≤ 1) (hε : 0 < dec p ε)
    (hε₁ : dec p ε ≤ 2⁻¹ ^ 15) (hθ : 0 < θ) (hθ₁ : θ ≤ 1) (hℓ : bisectionDepth (dec p ε) ≤ ℓ)
    (hβ : 0 < dec p β)
    (hβle : dec p β ≤ ((ℓ : ℝ) - 1) ^ 2 * dec p ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
      √(N * min (N : ℝ) (ℓ + 1) * min (N : ℝ) (Real.exp 1)) *
      (2 * √2 * √(N : ℝ) + √(Real.log (96 * N * min (N : ℝ) (ℓ + 1) / θ)))))
    (hβge : ((ℓ : ℝ) - 1) ^ 2 * dec p ε * √θ / (52 * (ℓ : ℝ) ^ 2 * (2 * ℓ - 1) *
        √(N * min (N : ℝ) (ℓ + 1) * min (N : ℝ) (Real.exp 1)) *
        (2 * √2 * √(N : ℝ) + √(Real.log (96 * N * min (N : ℝ) (ℓ + 1) / θ)))) /
      (1 + 2⁻¹ ^ 6) ≤ dec p β) {Nst : ℝ}
    (hN : Nst = newtonSchulzSteps (θ / (12 * N * ℓ * (ℓ + 1))) (dec p β / (16 * N)))
    (hbits : Real.logb 2 (dec p ε)⁻¹ + 3 / 2 * Real.logb 2 θ⁻¹ +
      Real.logb 2 (N * (4 * μM N + 10 + 10 * √(N : ℝ))) +
      1 / 2 * Real.logb 2 (N * min (N : ℝ) (ℓ + 1) * min (N : ℝ) (Real.exp 1)) +
      Real.logb 2 (2 * √2 * √(N : ℝ) + √(Real.log (96 * N * min (N : ℝ) (ℓ + 1) / θ))) +
      Real.logb 2 (ℓ * (ℓ + 1)) + Real.logb 2 ((ℓ : ℝ) ^ 2 * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2) +
      13 ≤ Real.logb 2 ((c .uniform + 1) * (2 : ℝ)⁻¹ ^ fmt.mantissaBits)⁻¹)
    (hbits' : Real.logb 2 (dec p β)⁻¹ +
      Real.logb 2 (2048 * (N + Nst + 1) * (4 * μM N + 10 + 10 * √(N : ℝ)) +
      16 * (4 * μQ N + 4 * √(N : ℝ) * (3 * (c .gaussian + 3) + 1) + 2 * μM N + 1)) ≤
        Real.logb 2 ((c .uniform + 1) * (2 : ℝ)⁻¹ ^ fmt.mantissaBits)⁻¹)
    (hexp : Real.logb 2 (Real.logb 2 (1536 * (N + ℓ + 2) ^ 3 / (dec p ε * θ)) + 2) + 1 ≤
      fmt.exponentBits)
    (hfuel : Nst ≤ F) {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ξ : Ω → Dist → ℕ → ℝ} (hξ : HasLaw ξ tapeLaw μ) :
    μ.real {ω | ∃ st', (eighProg.compiled p mm qr).exec
        { I with tape := fun d i => ρ d i (ξ ω d i) } N ![ℓ, F]
        (inputState p [(pairLayout.toArray A).map some, #[some R₀, some ε, some β],
          Array.replicate (2 * (N * N)) none, Array.replicate N none]) = some st' ∧
        ¬ ∃ (U : Matrix (Fin N) (Fin N) (K × K)) (d : Fin N → K),
          pairLayout.Holds st'.store p 2 0 U ∧ (∀ i : Fin N, st'.store.read p 3 i = some (d i)) ∧
          IsApproxDiagonalization (decodeMatrix (dec p) A) (decodeMatrix (dec p) U)
            (fun i => dec p (d i)) (2 * dec p ε * dec p R₀) (dec p ε / 3)} ≤ θ := by
  have hu : (0 : ℝ) < (2 : ℝ)⁻¹ ^ fmt.mantissaBits := by positivity
  have hΩ₁ : 1 ≤ fmt.maxFinite := by
    obtain ⟨z, -, hz⟩ := hlit p 1 (by omega)
    simpa [hz] using hrange z
  have hτ := floor_le_half_of_exponentBits_le fmt hε hε₁ hθ hθ₁ hexp
  have hM := isAccurate_eighIdealMachine_floor hsem (hlit.mono (by omega)) htn hmul p hrange
    hmmE hqrE hρT (by linarith) hΩ₁ hu.le hτ hcu hcg hcgu
    (fun d => hμM₀.trans (hμM (Nat.zero_le d))) (fun d => hμQ₀.trans (hμQ (Nat.zero_le d)))
  have hunif := countable_range_uniformUnif I.sem p (hcountu .uniform).1 (hcountu .uniform).2
  have hgauss := countable_range_gaussianNormal I.sem p (hcountu .gaussian).1 (hcountu .gaussian).2
  obtain ⟨hind, hlaw⟩ := iIndepFun_eighIdealTree (I.sem.toFloatMachine p
    (fun x => (I.sem.toNat p x).getD 0) mmR qrR (I.sem.uniformUnif p (ρ .uniform 0))
    (I.sem.gaussianNormal p (ρ .gaussian 0))) hunif.2 hunif.1 hgauss.2 hgauss.1 N F (ℓ + 1) R₀ β
    ⟨N, A, R₀, ε, ℓ⟩ le_rfl hξ
  have key :=
    hM.measureReal_not_isApproxDiagonalization_eigh_le_of_exponentBits_le_of_logb_le_of_hasLaw_eighSampleLaw
    fmt hE (by positivity) (by linarith) hunif.2 hunif.1 hgauss.2 hgauss.1 hμM hμQ hμM₀ hμQ₀
    (by linarith) hn hA hR₀ hR₀half hR₀one hε hε₁ hθ hθ₁ hℓ hβ hβle hβge hN hbits hbits' hexp
    hfuel hind hlaw
  have := hξ.isProbabilityMeasure
  refine le_trans (measureReal_mono (μ := μ) (fun ω hω => ?_) (measure_ne_top μ _)) key
  obtain ⟨st', hexec, hbad⟩ := hω
  obtain ⟨z, o, hz, ho, hdz, hdo⟩ : ∃ z o : K, I.sem.lit p 0 = some z ∧ I.sem.lit p 1 = some o ∧
      dec p z = 0 ∧ dec p o = 1 := by
    obtain ⟨z, hz, hdz⟩ := hlit p 0 (by omega)
    obtain ⟨o, ho, hdo⟩ := hlit p 1 (by omega)
    exact ⟨z, o, by simpa using hz, by simpa using ho, by simpa using hdz, by simpa using hdo⟩
  have hflag : I.sem.DecidesFlags p :=
    ⟨z, o, hz, ho, by rw [hsem.cmp_eq p z o, hdz, hdo]; norm_num, by rw [hsem.cmp_eq p o o]; simp⟩
  have hH := eighProg.holds_of_exec_compiled (I := { I with tape := fun d i => ρ d i (ξ ω d i) })
    hmm hqr p hflag (hsem.cmp_le p) N ℓ F hlit htn A R₀ ε β hexec
  have he := eigh_eighTapeMachine_eq_eigh_eighIdealTree I p mmR qrR ρ hρ (ξ ω) F ℓ A R₀ ε β
  dsimp only at hH he
  rw [he] at hH
  intro hAD
  exact hbad ⟨_, _, hH.1, hH.2, hAD⟩

end NLAlib
