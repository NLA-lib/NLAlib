/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import NLAlib.Ops.Confined
public import NLAlib.Ops.MonomialWork
public import NLAlib.Ops.Static
public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedDecoupleSpec
public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedDecoupleTermination
public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedTheoremsBits
public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedWorklistTermination

/-!
# The rounded shifted QR algorithm: headline theorems

[BanksGarzaVargasSrivastava2022, Theorem 6.3, with Theorem 1.4's quantifiers, corrected] in
floating point: the rounded deflation worklist (`NLAlib.ShiftedQR.solveRounded`) with the
decoupling loop of Lemma 6.4 (`NLAlib.ShiftedQR.roundedDecouple`: `Regularize`, then
$\mathrm{Sh}_{k,B}$, capped at $F$ rounds) and the `SmallEig` leaf
(`NLAlib.ShiftedQR.smallEigLeaf`), run with the parameter words of
`NLAlib.ShiftedQR.shqrParams` and the threshold word `NLAlib.ShiftedQR.shqrDeflationThreshold`
on a machine with unit roundoff $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$
(`NLAlib.ShiftedQR.uShQR`).

The parameters are those of `NLAlib.ShiftedQR.shqrParams_spec` (condition $4B$, separation
$\Gamma/4$ and iterate norm $4\Sigma$ inside the loop, block norm $2\Sigma$ in the worklist) and of
`NLAlib.ShiftedQR.roundedDecouple_randomDecouplingContract` with $n_{\max} = n$,
$N_{\max} = 2\Sigma$, $S = 4\Sigma$, the loop's threshold word $t_L$
(`NLAlib.ShiftedQR.shqrLoopThreshold`) and $\omega_D$ from it.

What is not claimed: no Hessenberg reduction or preprocessing of a general matrix; nothing on
`SmallEig`'s own cost or precision; no forward error for the eigenvalues; no rounded disk
sampler; nothing for repeated eigenvalues. Modelling choices stronger than the paper: `SmallEig`
reads a fixed window of the uniform stream, and the parameter words are exact reals.

## Main definitions

* `NLAlib.ShiftedQR.roundedShQR`: the program.
* `NLAlib.ShiftedQR.shqrParams`, `NLAlib.ShiftedQR.shqrDims`: its parameter words and
  dimensions.
* `NLAlib.ShiftedQR.ShQRInput`, `NLAlib.ShiftedQR.ShQRSpectrum`: the memory holding the input,
  and the memory holding the spectrum of a nearby matrix.

## Main results

* `NLAlib.ShiftedQR.roundedShQR_measureReal_not_spectrum_le` (T1c): the headline.
* `NLAlib.ShiftedQR.roundedShQR_terminates` (T1d): termination on every tape.
* `NLAlib.ShiftedQR.logb_inv_uShQR_le` (T2): the bits of precision.
* `NLAlib.ShiftedQR.roundedShQR_relative` (T3): the relative backward error.
* `NLAlib.ShiftedQR.roundedShQR_hermitian` (T4): Hermitian inputs.
* `NLAlib.ShiftedQR.roundedShQR_work_le` (T5): the operation count.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The rounded shifted QR algorithm** ([BanksGarzaVargasSrivastava2022, Theorem 6.3]): the
rounded deflation worklist with the decoupling loop of Lemma 6.4 and the `SmallEig` leaf. The
interface is `[N, k, np, F] (A, Thr, P) → (Out, Fl)`: the order, the shift degree, the number of
parameter words and the iteration cap; the matrix (overwritten), the deflation threshold word,
the parameter words; the $2N$ output words and the failure word. -/
def roundedShQR : Impl O Q :=
  solveRounded (roundedDecouple (O := O) (Q := Q)) (smallEigLeaf (O := O) (Q := Q))

end Program

/-- **The parameter words of the rounded shifted QR algorithm** at the order $n + 1$, the shift
degree $k$, the condition bound $B$, the separation $\Gamma$, the norm bound $\Sigma$ (`S`), the
backward error $\delta$ and the failure $\varphi$: the words of
`NLAlib.ShiftedQR.roundedDecoupleParams` with the loop's threshold word $t_L$, Regularize's
radius, the iteration's threshold word, $\gamma = 0.2$, the class constant $4B$, its $\alpha$ and
Exc's $\varepsilon$, and $k = 2^{\log_2 k}$. -/
noncomputable def shqrParams (n k : ℕ) (B Γ S δ φ : ℝ) : List ℝ :=
  roundedDecoupleParams (shqrLoopThreshold n k B Γ S δ φ) (shqrRadius n B Γ S δ)
    (shqrScanThreshold n k B Γ S δ φ) 0.2 (4 * B) (shqrAlpha k (4 * B)) (shqrEps k (4 * B)) k
    (Nat.log 2 k)

/-- The dimensions of a run: the order $n + 1$, the shift degree $k$, the number of parameter
words and the iteration cap $F$ (`NLAlib.ShiftedQR.shqrCap`). -/
noncomputable def shqrDims (n k : ℕ) (B Γ S δ φ : ℝ) : List ℕ :=
  [n + 1, k, (shqrParams n k B Γ S δ φ).length, shqrCap n B Γ S δ]

/-- **The memory holding the input** of the rounded shifted QR algorithm: the views of the
matrix, the threshold word, the parameter words, the output and the failure word are live, have
room and are apart; the matrix $\mathbf{H}$, the deflation threshold word and the parameter words
are stored. -/
def ShQRInput {n : ℕ} (k : ℕ) (B Γ S δ φ : ℝ) (a t p out f : ℕ × ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (μ : Mem ℝ) : Prop :=
  μ.Live [a, t, p, out, f] ∧
    μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ).length, 2 * (n + 1), 1] ∧
    Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ).length, 2 * (n + 1), 1] ∧
    HoldsMatrix a H μ.store ∧ μ.store.get t.1 t.2 = some (shqrDeflationThreshold n k B Γ S δ φ) ∧
    μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ).length = some (shqrParams n k B Γ S δ φ)

/-- **The memory holding the spectrum of a nearby matrix**: the failure word is $0$ and the
output holds all eigenvalues, with multiplicity, of $\mathbf{H} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le e$. -/
def ShQRSpectrum {n : ℕ} (out f : ℕ × ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (e : ℝ)
    (μ' : Mem ℝ) : Prop :=
  μ'.store.get f.1 f.2 = some 0 ∧
    ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧ specNorm E ≤ e ∧
        (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ)

/-- The regions the rounded shifted QR algorithm writes: the matrix, the output and the failure
word. -/
def shqrFp (n : ℕ) (a out f : ℕ × ℕ) : Fp :=
  Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔
    Store.inBlock f.1 f.2 1

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The rounded shifted QR algorithm** (T1c; [BanksGarzaVargasSrivastava2022, Theorem 6.3 with
Theorem 1.4's quantifiers, corrected]). Let $\mathbf{H}$ be upper Hessenberg of order $n + 1$,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\kappa(\mathbf{V}) \le B$
and eigenvalues separated by $\Gamma > 0$, $\|\mathbf{H}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$,
$0 < \varphi \le 1$ and $k$ the degree of (eqn:setk) at $4B$. Let the machine have the standard
model at $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$, exact natural literals up to
$n + 1$, a measurable interpretation reading the tape only in its windows, a stream $s_U$ uniform
on $[0, 1]$, an exact polar disk sampler on it, and a `SmallEig` kernel on it with forward error
$0 \le \beta_{\mathrm{se}} \le$ `shqrSmallEigAccuracy` and failure
$0 \le \varphi_{\mathrm{se}} \le$ `shqrSmallEigFailure`. Then from a memory holding $\mathbf{H}$
and the words of `NLAlib.ShiftedQR.shqrParams`, under a random tape with the stream laws,
`NLAlib.ShiftedQR.roundedShQR` fails to write only the matrix, the output and the failure word,
set the failure word to $0$ and store all eigenvalues, with multiplicity, of
$\mathbf{H} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta$, with probability at most
$\varphi$. The run terminates on every tape (`NLAlib.ShiftedQR.roundedShQR_terminates`). -/
theorem roundedShQR_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} {βse φse : ℝ} (hSE : IsRandomSmallEig law sU βse φse I)
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hHS : specNorm H ≤ S) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) (hβse0 : 0 ≤ βse)
    (hse : βse ≤ shqrSmallEigAccuracy n B Γ S δ) (hφse0 : 0 ≤ φse)
    (hφse : φse ≤ shqrSmallEigFailure n B Γ S δ φ) (hu : u ≤ uShQR n k B Γ S δ φ)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} (hin : ShQRInput k B Γ S δ φ a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQR (O := O) (Q := Q)).body
      (Env.frame (shqrDims n k B Γ S δ φ) [a, t, p, out, f]) (shqrFp n a out f)
      (ShQRSpectrum out f H δ) μ} ≤ φ := by
  have hu0 := hM.roundoff_nonneg
  have hB : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have hSp : 0 < S := hδ.trans_le hδS
  obtain ⟨-, -, SR, IT⟩ := shqrParams_spec hB hΓ hδ hδS hφ hφ1 hk hu0 hu hβse0 hse
  -- explicit, so that the contract's own implicit binders stay bound
  have hD := @roundedDecouple_randomDecouplingContract_of_le_uShQR O Q _ _ _ _ _ _ Mch I u hI win
    hloc hS hM hL n hNat hC hQ law sU βse φse hSE hDisk hU k B Γ S δ φ hB hΓ hδ hδS hφ hφ1 hk
    hβse0 hse hφse0 hu
  have hLeaf := @IsRandomSmallEig.randomLeafContract O Q _ law sU βse φse I hSE hβse0
  have hE := shqrLoopError_le_shqrDecoupleError (n := n) (k := k) (B := B) (Γ := Γ) (δ := δ)
    hSp.le hu0
  set E := (shqrCap n B Γ S δ : ℝ) *
    ((1 + shqrC k (4 * B)) * (4 * S) * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)) with hEdef
  have hE0 : 0 ≤ E := by
    have := shqrC_pos k (by linarith : 0 < 4 * B)
    have : 1 ≤ (1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k := one_le_pow₀ (by nlinarith)
    have : 0 ≤ (1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k - 1 := by linarith
    positivity
  have hφ₁ := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
  have hφD : 0 ≤ (shqrCap n B Γ S δ : ℝ) * (φse + shqrRegularizeFailure n B Γ S δ φ / 2 +
      shqrSmallEigFailure n B Γ S δ φ) := by unfold shqrRegularizeFailure; positivity
  have hc := SR.hc
  have hN : specNorm H + 2 * (n + 1) * (shqrCut n k B Γ S δ φ + E + βse) ≤ 2 * S := by
    have := SR.hN₀; nlinarith
  have hsm : 2 * (n + 1) * (shqrCut n k B Γ S δ φ + E + βse) ≤ Γ / (16 * (n + 1) * B) := by
    have := SR.hsmall; nlinarith
  have hδ' : 2 * (n + 1) * (shqrCut n k B Γ S δ φ + E + βse) ≤ δ := by
    have := SR.hδ; nlinarith
  obtain ⟨hl, hr, ha, hA, ht, hp⟩ := hin
  have h := solveRounded_measureReal_not_spectrum_le hS hM hu0 SR.hu1 hL hNat hQ hC hI hloc _ hD
    _ hLeaf hφD hφse0 hHess hV hHV hκ hΓ hgap SR.hfind SR.hcut hc hβse0 hE0 hN hsm hl hr ha hA
    ht hp hξ
  have := hξ.isProbabilityMeasure
  refine le_trans ?_ (h.trans (IT.hfail φse hφse0 hφse))
  refine measureReal_mono fun ω' hω' hW => hω' ?_
  exact hW.mono le_rfl fun μ' _ ⟨hf, roots, E', hO, hE', hR⟩ =>
    ⟨hf, roots, E', hO, hE'.trans hδ', hR⟩

/-- **The rounded shifted QR algorithm terminates on every tape** (T1d): on a scalar machine
with index literals, natural literals up to $n + 1$ that are exact, exact index conversion and
comparisons, a `SmallEig` kernel meeting `NLAlib.ShiftedQR.IsRandomSmallEig` and an exact polar
disk sampler, for any $(n + 1) \times (n + 1)$ matrix $\mathbf{H}$ (no structure assumed), any
$B, \Gamma, \Sigma, \delta, \varphi$ and $k$ the degree of (eqn:setk) at $4B$, the run of
`NLAlib.ShiftedQR.roundedShQR` from a memory holding the input (`NLAlib.ShiftedQR.ShQRInput`)
succeeds on every tape: the worklist and the decoupling loop are capped, every bounded index read
is an exact natural literal within its bound, and every operation succeeds on stored operands
(`NLAlib.ShiftedQR.solveRounded_terminates`,
`NLAlib.ShiftedQR.roundedDecouple_terminatingDecoupler`). No unit roundoff, class or
precision hypothesis is needed, so this is stronger than the paper, whose loop is uncapped.
Correctness is only the probability statement
(`NLAlib.ShiftedQR.roundedShQR_measureReal_not_spectrum_le`); no all-tape backward error is
claimed. -/
theorem roundedShQR_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    {law : ℕ → Measure ℝ} {sU : ℕ} {βse φse : ℝ} (hSE : IsRandomSmallEig law sU βse φse I)
    (hDisk : IsPolarDiskSampler sU I)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hk : k = shqrDegree (4 * B))
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} (hin : ShQRInput k B Γ S δ φ a t p out f H μ)
    (τ : Tape ℝ) :
    Wp .total I τ (roundedShQR (O := O) (Q := Q)).body
      (Env.frame (shqrDims n k B Γ S δ φ) [a, t, p, out, f]) (fun _ => True) μ := by
  have hkq : k = 2 ^ Nat.log 2 k := by
    rw [hk, shqrDegree, Nat.log_pow (by norm_num)]
  have hD : TerminatingDecoupler n k (shqrCap n B Γ S δ) (shqrParams n k B Γ S δ φ)
      (roundedDecouple (O := O) (Q := Q)) I :=
    roundedDecouple_terminatingDecoupler (O := O) (Q := Q) (F := shqrCap n B Γ S δ) hS hL hNat hC hQ hSE hDisk hkq (shqrLoopThreshold n k B Γ S δ φ) (shqrRadius n B Γ S δ)
    (shqrScanThreshold n k B Γ S δ φ) 0.2 (4 * B) (shqrAlpha k (4 * B)) (shqrEps k (4 * B))
  obtain ⟨hl, hr, ha, hA, ht, hp⟩ := hin
  exact (solveRounded_terminates hS hL hNat hQ hC _ hD _ hSE.terminatingLeaf (tape := τ) hl hr
    ha hA ht hp).wp fun _ _ _ => trivial

/-- **The bits of precision** (T2; [BanksGarzaVargasSrivastava2022, Theorem 1.4], corrected by
errata N8 and N14): there are absolute constants $c_1, c_2$ such that for every order $n + 1$,
$B \ge 1$, $\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of
(eqn:setk) at $4B$,
$$\log_2(1/\boldsymbol{u}_{\mathrm{ShQR}}) \le
  c_1 k \log_2\frac{4(n + 1)B\Sigma^2}{\delta\min(\Gamma, \Sigma)\varphi} + c_2.$$
The argument is scale-invariant ($\delta$ is an absolute error, so $\Sigma^2/(\delta\Gamma)$, not
$\Sigma/(\delta\Gamma)$) and at least $4$; $\min(\Gamma, \Sigma)$ covers $n = 0$, where the gap is
vacuous and $\Gamma$ unbounded (for $n \ge 1$, $\Gamma \le 2\Sigma$). The constants $c_1 = 63$ and
$c_2 = 0$ suffice: $\boldsymbol{u}_{\mathrm{ShQR}}$ is at least the argument to the power
$-(53k + 40)$ (`NLAlib.ShiftedQR.one_le_uShQR_mul`). -/
theorem logb_inv_uShQR_le : ∃ c₁ c₂ : ℝ, ∀ {n k : ℕ} {B Γ S δ φ : ℝ}, 1 ≤ B → 0 < Γ → 0 < δ →
    δ ≤ S → 0 < φ → φ ≤ 1 → k = shqrDegree (4 * B) →
    Real.logb 2 (uShQR n k B Γ S δ φ)⁻¹ ≤
      c₁ * k * Real.logb 2 (4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)) + c₂ := by
  refine ⟨63, 0, fun {n k B Γ S δ φ} hB hΓ hδ hδS hφ hφ1 hk => ?_⟩
  obtain ⟨hY4, h⟩ := one_le_uShQR_mul (n := n) hB hΓ hδ hδS hφ hφ1 hk
  set Y := 4 * (n + 1) * B * S ^ 2 / (δ * min Γ S * φ)
  have hk4 : (4 : ℝ) ≤ k := hk ▸ (shqrDegree_facts (by linarith : (1 : ℝ) ≤ 4 * B)).1
  have hu : 0 < uShQR n k B Γ S δ φ :=
    uShQR_pos (by exact_mod_cast (show (0 : ℝ) < k by linarith)) hB hΓ hδ (hδ.trans_le hδS) hφ
  have hY0 : 0 < Y := by linarith
  have hL : 0 ≤ Real.logb 2 Y := Real.logb_nonneg (by norm_num) (by linarith)
  have h1 : (uShQR n k B Γ S δ φ)⁻¹ ≤ Y ^ (53 * k + 40) := by
    rw [inv_le_iff_one_le_mul₀ hu, mul_comm]; exact h
  calc Real.logb 2 (uShQR n k B Γ S δ φ)⁻¹ ≤ Real.logb 2 (Y ^ (53 * k + 40)) :=
        Real.logb_le_logb_of_le (by norm_num) (inv_pos.mpr hu) h1
    _ = ((53 * k + 40 : ℕ) : ℝ) * Real.logb 2 Y := by rw [Real.logb_pow]
    _ ≤ 63 * k * Real.logb 2 Y := by push_cast; nlinarith
    _ = 63 * k * Real.logb 2 Y + 0 := by ring

/-- **The relative backward error** (T3): under the hypotheses of
`NLAlib.ShiftedQR.roundedShQR_measureReal_not_spectrum_le` with a norm word $\Sigma > 0$,
$\|\mathbf{H}\|_2 \le \Sigma \le c\|\mathbf{H}\|_2$, $c \ge 1$, and $0 < \delta \le 1$, the run
with the parameters at the absolute error $\delta\Sigma/c$ fails to return the spectrum of some
$\mathbf{H} + \mathbf{E}$ with $\|\mathbf{E}\|_2 \le \delta\|\mathbf{H}\|_2$ with probability at
most $\varphi$. -/
theorem roundedShQR_relative {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} {βse φse : ℝ} (hSE : IsRandomSmallEig law sU βse φse I)
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {k : ℕ}
    {B Γ S c δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hS0 : 0 < S) (hHS : specNorm H ≤ S)
    (hSc : S ≤ c * specNorm H) (hc : 1 ≤ c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) (hβse0 : 0 ≤ βse)
    (hse : βse ≤ shqrSmallEigAccuracy n B Γ S (δ * S / c)) (hφse0 : 0 ≤ φse)
    (hφse : φse ≤ shqrSmallEigFailure n B Γ S (δ * S / c) φ)
    (hu : u ≤ uShQR n k B Γ S (δ * S / c) φ)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} (hin : ShQRInput k B Γ S (δ * S / c) φ a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQR (O := O) (Q := Q)).body
      (Env.frame (shqrDims n k B Γ S (δ * S / c) φ) [a, t, p, out, f]) (shqrFp n a out f)
      (ShQRSpectrum out f H (δ * specNorm H)) μ} ≤ φ := by
  have hc0 : 0 < c := by linarith
  have h1 : 0 < δ * S / c := by positivity
  have h2 : δ * S / c ≤ S := by rw [div_le_iff₀ hc0]; nlinarith
  have h3 : δ * S / c ≤ δ * specNorm H := by rw [div_le_iff₀ hc0]; nlinarith
  have hT := roundedShQR_measureReal_not_spectrum_le hS hM hL hNat hQ hC hI hloc hSE hDisk hU
    hHess hV hHV hκ hΓ hgap hHS h1 h2 hφ hφ1 hk hβse0 hse hφse0 hφse hu hin hξ
  have := hξ.isProbabilityMeasure
  refine le_trans ?_ hT
  refine measureReal_mono fun ω' hω' hW => hω' ?_
  exact hW.mono le_rfl fun μ' _ ⟨hf, roots, E, hO, hE, hR⟩ => ⟨hf, roots, E, hO, hE.trans h3, hR⟩

/-- **Hermitian inputs** (T4; [BanksGarzaVargasSrivastava2022, Remark 1.7], at $B = 1$): for a
Hermitian upper Hessenberg (tridiagonal) $\mathbf{H}$ of order $n + 1$ with eigenvalues separated
by $\Gamma > 0$, $\|\mathbf{H}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$, and
the machine, kernels and tape law of `NLAlib.ShiftedQR.roundedShQR_measureReal_not_spectrum_le` at
$B = 1$, no diagonalization is supplied: the unitary eigenvector matrix has condition $1$. So the
run with the parameter words at $B = 1$ fails to write only the matrix, the output and the
failure word, set the failure word to $0$ and store all eigenvalues of some $\mathbf{H} +
\mathbf{E}$, $\|\mathbf{E}\|_2 \le \delta$, with probability at most $\varphi$.

The shift degree is $k = 128$, the degree of (eqn:setk) at $4$: the paper's own (eqn:setk) gives
$k = 64$ at its $B \ge 2\kappa_V = 2$, and the two-level class bookkeeping (the worklist at
condition $2B$, the iterates at $4B$) adds one more doubling. The paper's $k = 2$ for Hermitian
inputs is a different algorithm (exact Ritz values), not $\mathrm{Sh}_{k,B}$ under (eqn:setk),
and is not claimed. -/
theorem roundedShQR_hermitian {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} {βse φse : ℝ} (hSE : IsRandomSmallEig law sU βse φse I)
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ} {Γ S δ φ : ℝ}
    (hHess : IsUpperHessenberg H) (hH : H.IsHermitian) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ |hH.eigenvalues i - hH.eigenvalues j|) (hHS : specNorm H ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree 4)
    (hβse0 : 0 ≤ βse) (hse : βse ≤ shqrSmallEigAccuracy n 1 Γ S δ) (hφse0 : 0 ≤ φse)
    (hφse : φse ≤ shqrSmallEigFailure n 1 Γ S δ φ) (hu : u ≤ uShQR n k 1 Γ S δ φ)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} (hin : ShQRInput k 1 Γ S δ φ a t p out f H μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQR (O := O) (Q := Q)).body
      (Env.frame (shqrDims n k 1 Γ S δ φ) [a, t, p, out, f]) (shqrFp n a out f)
      (ShQRSpectrum out f H δ) μ} ≤ φ := by
  set U := (hH.eigenvectorUnitary : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  have hUo : HasOrthonormalCols U := hH.hasOrthonormalCols_eigenvectorUnitary
  have hHU : H * U = U * Matrix.diagonal fun i => (hH.eigenvalues i : ℂ) := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    refine (congrArg (· * U) h).trans ?_
    rw [Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
    rfl
  have hgap' : ∀ i j, i ≠ j → Γ ≤ ‖(hH.eigenvalues i : ℂ) - (hH.eigenvalues j : ℂ)‖ := by
    intro i j hij
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hgap i j hij
  exact roundedShQR_measureReal_not_spectrum_le hS hM hL hNat hQ hC hI hloc hSE hDisk hU hHess
    hUo.isUnit hHU hUo.pseudoConditionNumber_eq_one.le hΓ hgap' hHS hδ hδS hφ hφ1
    (by rw [mul_one]; exact hk) hβse0 hse hφse0 hφse hu hin hξ

/-- **The operation count** (T5): there is an absolute constant $c$ such that the static count
(`NLAlib.Ops.stmtCost`; every counted run on every tape stays within it,
`NLAlib.Ops.exec_within`) of `NLAlib.ShiftedQR.roundedShQR` at the order $n + 1$, the shift
degree $k$, $n_p$ parameter words and the cap $F$ has at most
$c(n + 1)^4(k + 1)^4(n_p + 1)(F + 1)$ operations and tests, each `SmallEig` call counting one.
The count holds on every tape, not only with probability $1 - \varphi$ (errata N10): the run is
capped. The exponents are a crude static bound: the monomial bound of the tree
(`NLAlib.Ops.size_stmtCost_le_stmtWorkMono`) gives $2011(n + 1)^3(k + 1)^3(n_p + 1)(F + 1)$, and
the order of the count is $N^3F(k^3 + n_pk)$: $2N$ worklist rounds of $F$ iterations, each a
`Find` of $k^3N^2$ (the static supremum over its index words $m \le k$, $he \le k^2$, against
the paper's $k\log k$ steps) and Exc's $n_p$ trials of $kN^2$. -/
theorem roundedShQR_work_le : ∃ c : ℕ, ∀ n k np F : ℕ,
    Count.size (stmtCost (roundedShQR (O := O) (Q := Q)).body [n + 1, k, np, F]) ≤
      c * (n + 1) ^ 4 * (k + 1) ^ 4 * (np + 1) * (F + 1) := by
  refine ⟨2011, fun n k np F => ?_⟩
  have hw : stmtWorkMono (roundedShQR (O := O) (Q := Q)).body
      [⟨1, 1, 0, 0, 0⟩, ⟨1, 0, 1, 0, 0⟩, ⟨1, 0, 0, 1, 0⟩, ⟨1, 0, 0, 0, 1⟩] =
        ⟨2011, 3, 3, 1, 1⟩ := by
    kernel_rfl
  have hσ : SlotsLe (n + 1) (k + 1) (np + 1) (F + 1) [n + 1, k, np, F]
      [⟨1, 1, 0, 0, 0⟩, ⟨1, 0, 1, 0, 0⟩, ⟨1, 0, 0, 1, 0⟩, ⟨1, 0, 0, 0, 1⟩] := by
    simp only [SlotsLe, WorkMono.eval, List.forall₂_cons, List.Forall₂.nil, and_true]
    refine ⟨by simp, by simp, by simp, by simp⟩
  refine (size_stmtCost_le_stmtWorkMono (by omega) _ hσ).trans ?_
  rw [hw, WorkMono.eval]
  have h0 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : (k + 1) ^ 3 ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [pow_one]
  gcongr

end Theorems

end NLAlib.ShiftedQR
