/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedTheorems
public import NLAlib.Eigensolvers.SmallEig.Theorems

/-!
# The rounded shifted QR algorithm with the small-eigenvalue program

[BanksGarzaVargasSrivastava2022, Theorem 6.3] with no algorithmic oracle: the `SmallEig` kernel the
merged algorithm assumes (`NLAlib.ShiftedQR.IsRandomSmallEig`) is replaced by the program of
[BanksGarzaVargasSrivastava2025, Theorem 1.1] (`NLAlib.SmallEig.smallEigProg`), run as a routine
(`NLAlib.ShiftedQR.roundedShQRWith`). Its words follow those of the merged algorithm, its cap is a
dimension, and its forward contract on the trailing blocks of order $k$ and norm at most
$4\Sigma$ (`NLAlib.SmallEig.smallEigProg_randomSmallEigContract`) gives the merged accuracy and
failure. The headline is conditional only on the two random-matrix theorems (the hypotheses
`NLAlib.ComplexGaussianGapTail`, `NLAlib.ComplexGaussianConditionTail`); with their preferred
forms it is `NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le_of_spec`. One unit
roundoff serves the whole run: $\boldsymbol{u} \le \min(\boldsymbol{u}_{\mathrm{ShQR}},
\boldsymbol{u}^{\mathrm{fwd}}_{\mathrm{SmallEig}})$, $O(\log^4)$ bits up to $(\log\log)^2$.

## Main definitions

* `NLAlib.ShiftedQR.roundedShQRSmallEig`: the program.
* `NLAlib.ShiftedQR.shqrSmallEigParams`, `NLAlib.ShiftedQR.shqrSmallEigCap`,
  `NLAlib.ShiftedQR.shqrSmallEigDims`, `NLAlib.ShiftedQR.uShQRSmallEig`,
  `NLAlib.ShiftedQR.ShQRSmallEigInput`: its words, cap, dimensions, precision and input.

## Main results

* `NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le`: the headline.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_terminates`: termination on every tape.
* `NLAlib.ShiftedQR.logb_inv_uShQRSmallEig_le`, `NLAlib.ShiftedQR.shqrDegree_le_log`: the bits.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_work_le`: the operation count.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_relative`, `NLAlib.ShiftedQR.roundedShQRSmallEig_hermitian`.
* `NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le_of_spec`: with the preferred
  random-matrix theorems.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops SmallEig

/-- **The parameter words of the algorithm with the small-eigenvalue program**: the words of
`NLAlib.ShiftedQR.shqrParams`, followed by the twelve words of
`NLAlib.SmallEig.smallEigForwardParams` at the order bound $k$, the norm bound $4\Sigma$, the
accuracy `NLAlib.ShiftedQR.shqrSmallEigAccuracy` and the failure
`NLAlib.ShiftedQR.shqrSmallEigFailure`. -/
noncomputable def shqrSmallEigParams (n k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail) :
    List ℝ :=
  shqrParams n k B Γ S δ φ ++
    smallEigForwardParams k (4 * S) (shqrSmallEigAccuracy n B Γ S δ)
      (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂

/-- The cap of the small-eigenvalue program in the algorithm. -/
noncomputable def shqrSmallEigCap (n k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℕ :=
  smallEigForwardCap k (4 * S) (shqrSmallEigAccuracy n B Γ S δ)
    (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂

/-- The dimensions of a run: the order $n + 1$, the shift degree $k$, the number of words, the
iteration cap `NLAlib.ShiftedQR.shqrCap` and the cap `NLAlib.ShiftedQR.shqrSmallEigCap`. -/
noncomputable def shqrSmallEigDims (n k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : List ℕ :=
  [n + 1, k, (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length, shqrCap n B Γ S δ,
    shqrSmallEigCap n k B Γ S δ φ c₁ c₂]

/-- **The precision threshold of the algorithm with the small-eigenvalue program**: the minimum of
`NLAlib.ShiftedQR.uShQR` and `NLAlib.SmallEig.uSmallEigForward` at the order bound $k$, the norm
bound $4\Sigma$, the accuracy `NLAlib.ShiftedQR.shqrSmallEigAccuracy` and the failure
`NLAlib.ShiftedQR.shqrSmallEigFailure`. -/
noncomputable def uShQRSmallEig (n k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail) : ℝ :=
  min (uShQR n k B Γ S δ φ)
    (uSmallEigForward k (4 * S) (shqrSmallEigAccuracy n B Γ S δ)
      (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂)

/-- **The memory holding the input** of the algorithm with the small-eigenvalue program: the
views of the matrix, the threshold word, the parameter words, the output and the failure word are
live, have room and are apart; the matrix $\mathbf{H}$, the deflation threshold word and the words
`NLAlib.ShiftedQR.shqrSmallEigParams` are stored. -/
def ShQRSmallEigInput {n : ℕ} (k : ℕ) (B Γ S δ φ : ℝ) (c₁ c₂ : PolyLogTail)
    (a t p out f : ℕ × ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  μ.Live [a, t, p, out, f] ∧
    μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length,
        2 * (n + 1), 1] ∧
    Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length,
        2 * (n + 1), 1] ∧
    HoldsMatrix a H μ.store ∧ μ.store.get t.1 t.2 = some (shqrDeflationThreshold n k B Γ S δ φ) ∧
    μ.store.readBlock p.1 p.2 (shqrSmallEigParams n k B Γ S δ φ c₁ c₂).length =
      some (shqrSmallEigParams n k B Γ S δ φ c₁ c₂)

/-- **The precision threshold is positive**: for tail records with $b_1, b_2 > 0$, $B \ge 1$,
$\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of (eqn:setk) at
$4B$, `NLAlib.ShiftedQR.uShQRSmallEig` is positive, and the small-eigenvalue words have twelve
entries. -/
theorem uShQRSmallEig_pos {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {n k : ℕ}
    {B Γ S δ φ : ℝ} (hB : 1 ≤ B) (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) :
    0 < uShQRSmallEig n k B Γ S δ φ c₁ c₂ ∧
      (smallEigForwardParams k (4 * S) (shqrSmallEigAccuracy n B Γ S δ)
        (shqrSmallEigFailure n B Γ S δ φ) c₁ c₂).length = 12 := by
  sorry

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has SampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The rounded shifted QR algorithm with the small-eigenvalue program**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] with [BanksGarzaVargasSrivastava2025,
Theorem 1.1]): `NLAlib.ShiftedQR.roundedShQRWith` at the program
`NLAlib.SmallEig.smallEigProg` with the Gaussian stream `sG`. The interface is
`[N, k, np, F, T] (A, Thr, P) → (Out, Fl)`. No eigenvalue oracle.
Algorithm: shifted-qr-rounded -/
def roundedShQRSmallEig (sG : ℕ) : Impl O Q :=
  roundedShQRWith (smallEigProg (O := O) (Q := Q) sG)

end Program

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has SampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-- **The rounded shifted QR algorithm with no oracle** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3] with the quantifiers of Theorem 1.4, corrected; `SmallEig` by
[BanksGarzaVargasSrivastava2025, Theorem 1.1 and Corollary 1.3]). Let the machine have the
standard model at $\boldsymbol{u} \le \boldsymbol{u}_0$, index literals, exact natural literals
up to $n + 1$, exact `toNat` and comparisons, a measurable interpretation reading the tape only in
its windows whose draws store the tape entry, a stream $s_U$ uniform on $[0, 1]$ with an exact
polar disk sampler on it and a stream $s_G$ with the standard real Gaussian law; let the eigenvalue
gap and the eigenvector condition of a complex Ginibre perturbation have the tails $c_1$, $c_2$
with $b_1, b_2 > 0$. Let $\mathbf{H}$ of order $n + 1$ be upper Hessenberg,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$ and eigenvalues separated by $\Gamma > 0$,
$\|\mathbf{H}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of
(eqn:setk) at $4B$. Then from a memory holding $\mathbf{H}$, the deflation threshold word and the
words of `NLAlib.ShiftedQR.shqrSmallEigParams`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{roundedShQRSmallEig}(\mathbf{H}) \text{ fails, or writes outside the
  matrix, the output and the failure word, or lists no }
  \operatorname{spec}(\mathbf{H} + \mathbf{E}),\ \|\mathbf{E}\|_2 \le \delta\bigr] \le \varphi\,.$$
Here $\boldsymbol{u}_0$ is `NLAlib.ShiftedQR.uShQRSmallEig`.
[BanksGarzaVargasSrivastava2022, Theorem 6.3]; there `SmallEig` is an oracle.

Note: The run terminates on every tape (`NLAlib.ShiftedQR.roundedShQRSmallEig_terminates`).
General form: `NLAlib.ShiftedQR.roundedShQRWith_measureReal_not_spectrum_le`. -/
theorem roundedShQRSmallEig_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : ComplexGaussianGapTail c₁) (hB : ComplexGaussianConditionTail c₂)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hHS : specNorm H ≤ S) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B))
    (hu : u ≤ uShQRSmallEig n k B Γ S δ φ c₁ c₂)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : ShQRSmallEigInput k B Γ S δ φ c₁ c₂ a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRSmallEig (O := O) (Q := Q) sG).body
      (Env.frame (shqrSmallEigDims n k B Γ S δ φ c₁ c₂) [a, t, p, out, f]) (shqrFp n a out f)
      (ShQRSpectrum out f H δ) μ} ≤ φ := by
  sorry

/-- **The algorithm with the small-eigenvalue program terminates on every tape**: on a scalar
machine with index literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons,
draws that store the tape entry and an exact polar disk sampler, for any $(n + 1) \times (n + 1)$
matrix $\mathbf{H}$ (no structure assumed), any $B, \Gamma, \Sigma, \delta, \varphi$, $k$ the
degree of (eqn:setk) at $4B$ and any tail records, the run of
`NLAlib.ShiftedQR.roundedShQRSmallEig` from `NLAlib.ShiftedQR.ShQRSmallEigInput` succeeds on every
tape and writes only the matrix, the output and the failure word. No unit roundoff, class or
random-matrix hypothesis is needed: the stored cap words are valid. -/
theorem roundedShQRSmallEig_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) (hSmp : IsSample I) {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {c₁ c₂ : PolyLogTail}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ} {B Γ S δ φ : ℝ}
    (hk : k = shqrDegree (4 * B)) {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : ShQRSmallEigInput k B Γ S δ φ c₁ c₂ a t p out f H μ) (τ : Tape ℝ) :
    Writes .total I τ (roundedShQRSmallEig (O := O) (Q := Q) sG).body
      (Env.frame (shqrSmallEigDims n k B Γ S δ φ c₁ c₂) [a, t, p, out, f]) (shqrFp n a out f)
      (fun _ => True) μ := by
  sorry

/-- **The shift degree is $O(\log B\log\log B)$**: there is an absolute constant $c$ with
$k \le c(\log_2(4B) + 1)(\log_2\log_2(16B) + 1)$ for $k$ the degree of (eqn:setk) at $4B$, for
every $B \ge 1$ ([BanksGarzaVargasSrivastava2022, Theorem 1.4], the choice of $k$). -/
theorem shqrDegree_le_log : ∃ c : ℝ, ∀ {B : ℝ}, 1 ≤ B →
    (shqrDegree (4 * B) : ℝ) ≤ c * (Real.logb 2 (4 * B) + 1) *
      (Real.logb 2 (Real.logb 2 (16 * B)) + 1) := by
  sorry

/-- **The bits of precision of the algorithm with the small-eigenvalue program**
([BanksGarzaVargasSrivastava2022, Theorem 1.4] with [BanksGarzaVargasSrivastava2025,
Theorem 1.1]): for tail records with $b_1, b_2 > 0$ there are constants $e_1, e_2, e_3$ such that
for every order $n + 1$, $B \ge 1$, $\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and
$k$ the degree of (eqn:setk) at $4B$,
$$\log_2\frac{1}{\boldsymbol{u}_0} \le e_1 k\log_2 Y + e_2k^2\log_2^2 Y + e_3, \qquad
  Y = \frac{4(n + 1)B\Sigma^2}{\delta\min(\Gamma, \Sigma)\varphi}\,,$$
$\boldsymbol{u}_0$ = `NLAlib.ShiftedQR.uShQRSmallEig`; with `NLAlib.ShiftedQR.shqrDegree_le_log`
this is $O(\log^4 Y)$ up to $(\log\log Y)^2$. -/
theorem logb_inv_uShQRSmallEig_le (c₁ c₂ : PolyLogTail) (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    ∃ e₁ e₂ e₃ : ℝ, ∀ {n k : ℕ} {B Γ S δ φ : ℝ}, 1 ≤ B → 0 < Γ → 0 < δ → δ ≤ S → 0 < φ →
      φ ≤ 1 → k = shqrDegree (4 * B) →
      Real.logb 2 (uShQRSmallEig n k B Γ S δ φ c₁ c₂)⁻¹ ≤
        e₁ * k * Real.logb 2 (4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)) +
          e₂ * k ^ 2 * Real.logb 2 (4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)) ^ 2 + e₃ := by
  sorry

/-- **The operation count of the algorithm with the small-eigenvalue program**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] and [BanksGarzaVargasSrivastava2025, Theorem 1.1],
running times, on every tape): there is an absolute constant $c$ such that the static count of
`NLAlib.ShiftedQR.roundedShQRSmallEig` at the order $n + 1$, the shift degree $k$, $n_p$ words,
the iteration cap $F$ and the cap $T$ has at most
$c(n + 1)^4(k + 1)^5(n_p + 1)(F + 1)(T + 1)^2$ operations and tests: the cost of `SmallEig` is
now counted. -/
theorem roundedShQRSmallEig_work_le (sG : ℕ) : ∃ c : ℕ, ∀ n k np F T : ℕ,
    Count.size (stmtCost (roundedShQRSmallEig (O := O) (Q := Q) sG).body [n + 1, k, np, F, T]) ≤
      c * (n + 1) ^ 4 * (k + 1) ^ 5 * (np + 1) * (F + 1) * (T + 1) ^ 2 := by
  sorry

/-- **The algorithm with no oracle, relative form** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3], the error relative to $\|\mathbf{H}\|_2$): with the machine, streams and tails of
`NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le` written out in the signature:
let $\mathbf{H}$ of order $n + 1$ be upper Hessenberg, in the class $(B, \Gamma)$, with
$\Sigma > 0$, $\|\mathbf{H}\|_2 \le \Sigma \le c\|\mathbf{H}\|_2$, $c \ge 1$,
$0 < \delta \le 1$, $0 < \varphi \le 1$, $k$ the degree of (eqn:setk) at $4B$, and the words and
the precision at the absolute error $\delta\Sigma/c$. Then the probability that the run fails,
writes outside the matrix, the output and the failure word, or lists no spectrum of
$\mathbf{H} + \mathbf{E}$ with $\|\mathbf{E}\|_2 \le \delta\|\mathbf{H}\|_2$ is at most
$\varphi$. -/
theorem roundedShQRSmallEig_relative {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : ComplexGaussianGapTail c₁) (hB : ComplexGaussianConditionTail c₂)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {k : ℕ}
    {B Γ S c δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hS0 : 0 < S) (hHS : specNorm H ≤ S)
    (hSc : S ≤ c * specNorm H) (hc : 1 ≤ c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B))
    (hu : u ≤ uShQRSmallEig n k B Γ S (δ * S / c) φ c₁ c₂)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : ShQRSmallEigInput k B Γ S (δ * S / c) φ c₁ c₂ a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRSmallEig (O := O) (Q := Q) sG).body
      (Env.frame (shqrSmallEigDims n k B Γ S (δ * S / c) φ c₁ c₂) [a, t, p, out, f])
      (shqrFp n a out f) (ShQRSpectrum out f H (δ * specNorm H)) μ} ≤ φ := by
  sorry

/-- **The algorithm with no oracle on Hermitian inputs** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3], at the condition $1$): with the machine, streams and tails written out in the
signature: let $\mathbf{H}$ of order $n + 1$ be upper Hessenberg and Hermitian with eigenvalues
separated by $\Gamma > 0$, $\|\mathbf{H}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$,
$0 < \varphi \le 1$, $k$ the degree of (eqn:setk) at $4$, and the words and the precision at
$B = 1$. Then the probability that the run fails, writes outside the matrix, the output and the
failure word, or lists no spectrum of $\mathbf{H} + \mathbf{E}$ with $\|\mathbf{E}\|_2 \le \delta$
is at most $\varphi$. -/
theorem roundedShQRSmallEig_hermitian {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : ComplexGaussianGapTail c₁) (hB : ComplexGaussianConditionTail c₂)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ} {Γ S δ φ : ℝ}
    (hHess : IsUpperHessenberg H) (hH : H.IsHermitian) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ |hH.eigenvalues i - hH.eigenvalues j|) (hHS : specNorm H ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree 4)
    (hu : u ≤ uShQRSmallEig n k 1 Γ S δ φ c₁ c₂)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} (hin : ShQRSmallEigInput k 1 Γ S δ φ c₁ c₂ a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRSmallEig (O := O) (Q := Q) sG).body
      (Env.frame (shqrSmallEigDims n k 1 Γ S δ φ c₁ c₂) [a, t, p, out, f]) (shqrFp n a out f)
      (ShQRSpectrum out f H δ) μ} ≤ φ := by
  sorry

/-- **The algorithm with no oracle, with the preferred random-matrix theorems**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] with [BanksGarzaVargasSrivastava2025,
Theorem 1.1]): `NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le` with the tails
of the preferred forms of the eigenvalue gap and the eigenvector condition of a complex Ginibre
perturbation (`NLAlib.ComplexGaussianGapPreferred`, `NLAlib.ComplexGaussianConditionPreferred`), at
the records $(1, 3, 2, 0)$ and $(18, 3, 2, 2)$: for the machine, the streams and the input of the
signature, upper Hessenberg $\mathbf{H}$ in the class $(B, \Gamma)$, $\|\mathbf{H}\|_2 \le \Sigma$,
$0 < \delta \le \Sigma$, $0 < \varphi \le 1$, $k$ the degree at $4B$; the probability that the
run fails, writes outside the matrix, the output and the failure word, or lists no spectrum of
$\mathbf{H} + \mathbf{E}$ with $\|\mathbf{E}\|_2 \le \delta$ is at most $\varphi$. The two
hypotheses are discharged when the random-matrix theorems are proved. -/
theorem roundedShQRSmallEig_measureReal_not_spectrum_le_of_spec {Mch : Machine ℝ}
    {I : Interp O Q ℝ} {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) (hA : ComplexGaussianGapPreferred)
    (hB : ComplexGaussianConditionPreferred)
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hHS : specNorm H ≤ S) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B))
    (hu : u ≤ uShQRSmallEig n k B Γ S δ φ ⟨1, 3, 2, 0⟩ ⟨18, 3, 2, 2⟩)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hin : ShQRSmallEigInput k B Γ S δ φ ⟨1, 3, 2, 0⟩ ⟨18, 3, 2, 2⟩ a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRSmallEig (O := O) (Q := Q) sG).body
      (Env.frame (shqrSmallEigDims n k B Γ S δ φ ⟨1, 3, 2, 0⟩ ⟨18, 3, 2, 2⟩) [a, t, p, out, f])
      (shqrFp n a out f) (ShQRSpectrum out f H δ) μ} ≤ φ := by
  sorry

end Theorems

end NLAlib.ShiftedQR
