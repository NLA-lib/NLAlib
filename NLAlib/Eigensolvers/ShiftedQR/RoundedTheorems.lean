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
public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecoupleRoutine
public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecoupleSpec
public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecoupleTermination
public import NLAlib.Eigensolvers.ShiftedQR.RoundedTheoremsBits
public import NLAlib.Eigensolvers.ShiftedQR.RoundedWorklistTermination
public import NLAlib.Eigensolvers.ShiftedQR.RoundedParameterChoices

/-!
# The rounded shifted QR algorithm: headline theorems

[BanksGarzaVargasSrivastava2022, Theorem 6.3] with the quantifiers of
[BanksGarzaVargasSrivastava2022, Theorem 1.4], in floating point, corrected: the decoupling loop
is capped, the deflation scan covers the bottom $k$ subdiagonal entries, and the precision
threshold is recomputed for the corrected constants of the blocks. The program is the rounded
deflation worklist (`NLAlib.ShiftedQR.solveRoundedWith`) with the decoupling loop of Lemma 6.4
(`NLAlib.ShiftedQR.roundedDecoupleWith`: `Regularize`, then
$\mathrm{Sh}_{k,B}$, capped at $F$ rounds) and the leaf (`NLAlib.ShiftedQR.seLeaf`), both running
a small-eigenvalue routine; `NLAlib.ShiftedQR.roundedShQR` runs the `SmallEig` kernel
(`NLAlib.ShiftedQR.smallEigKernel`) with the cap $0$. It is run with the parameter words of
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
sampler; nothing for repeated eigenvalues. Modelling assumptions the paper does not make: `SmallEig`
reads a fixed window of the uniform stream, and the parameter words are exact reals. The
realizability of the hypotheses is shown for each separately (the machine, the exact kernels, a
tape law); that one interpretation is measurable (`NLAlib.Ops.Interp.IsMeasurable`) and meets the
`SmallEig` contract at the same time is assumed, not exhibited: `SmallEig` is an oracle
([BanksGarzaVargasSrivastava2022, Definition 1.2]).

## Main definitions

* `NLAlib.ShiftedQR.roundedShQR`: the program.
* `NLAlib.ShiftedQR.shqrParams`, `NLAlib.ShiftedQR.shqrDims`: its parameter words and
  dimensions.
* `NLAlib.ShiftedQR.ShQRInput`, `NLAlib.ShiftedQR.ShQRSpectrum`: the memory holding the input,
  and the memory holding the spectrum of a nearby matrix.

## Main results

* `NLAlib.ShiftedQR.roundedShQR_measureReal_not_spectrum_le`: the headline.
* `NLAlib.ShiftedQR.roundedShQR_terminates`: termination on every tape.
* `NLAlib.ShiftedQR.logb_inv_uShQR_le`: the bits of precision.
* `NLAlib.ShiftedQR.roundedShQR_relative`: the relative backward error.
* `NLAlib.ShiftedQR.roundedShQR_hermitian`: Hermitian inputs.
* `NLAlib.ShiftedQR.roundedShQR_work_le`: the operation count.
* `NLAlib.ShiftedQR.roundedShQRWith`,
  `NLAlib.ShiftedQR.roundedShQRWith_measureReal_not_spectrum_le`,
  `NLAlib.ShiftedQR.roundedShQRWith_terminates`: the algorithm with a small-eigenvalue routine in
  the place of the kernel [BanksGarzaVargasSrivastava2025].

The headline and the operation count concern the same program, not one run. The headline on one run,
with explicit work and span bounds conjoined with correctness, is the certificate
`NLAlib.ShiftedQR.roundedShQRAlgorithm` and its bound
`NLAlib.ShiftedQR.roundedShQR_algorithm_measureReal_not_accepts_le`
(`NLAlib.Eigensolvers.ShiftedQR.RoundedCertificate`).
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The eigenvalue routine of a Schur leaf**: run the Schur leaf `L` on a scoped copy of the
block `Bk` with a scoped accumulator and copy the diagonal of the triangular result to `Ev` (the
eigenvalues of the leaf's perturbed block). `Regularize` needs only these Ritz values. The
interface is `[d, nq, T] (Bk, Qw) → (Ev)`, that of a small-eigenvalue routine. -/
def schurDiag (L : Impl O Q) : Impl O Q := opsImpl% [d, nq, T] (Bk, Qw) → (Ev) {
  let W ← alloc (2 * (d * d));
  let Ub ← alloc (2 * (d * d));
  run (unaryMap (Has.inj ScalarOp.copy)).body [2 * (d * d)] (Bk, W);
  run L.body [d, nq, T] (W, Qw, W, Ub);
  for i < d {
    call (Has.inj ScalarOp.copy) [] (W[2 * (i * d + i)]) → (Ev[2 * i]);
    call (Has.inj ScalarOp.copy) [] (W[2 * (i * d + i) + 1]) → (Ev[2 * i + 1])
  }
}

/-- **The rounded shifted QR algorithm in Schur mode with a Schur leaf**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] with the routine of
[BanksGarzaVargasSrivastava2025, Corollary 1.3], with the Schur form): the worklist
`NLAlib.ShiftedQR.solveRoundedWith` in Schur mode with the decoupling loop
`NLAlib.ShiftedQR.roundedDecoupleWith` (whose Ritz values come from the leaf,
`NLAlib.ShiftedQR.schurDiag L`) and the Schur leaf `L`. The leaf reads the last $12$ parameter
words and the cap $T$. The interface is `[N, k, np, F, T, ns, w] (A, Thr, P, U) → (A, U, Fl)`.
Algorithm: shifted-qr-rounded -/
def roundedShQRWith (L : Impl O Q) : Impl O Q :=
  solveRoundedWith (roundedDecoupleWith (schurDiag L)) L

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
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ).length, 2 * ((n + 1) * (n + 1)), 1] ∧
    Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ).length, 2 * ((n + 1) * (n + 1)), 1] ∧
    (∃ U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix out U μ.store) ∧
    HoldsMatrix a H μ.store ∧ μ.store.get t.1 t.2 = some (shqrDeflationThreshold n k B Γ S δ φ) ∧
    μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ).length = some (shqrParams n k B Γ S δ φ)

/-- **The memory holding the spectrum of a nearby matrix**: the failure word is $0$ and the
output holds all eigenvalues, with multiplicity, of $\mathbf{H} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le e$. -/
def ShQRSpectrum {n : ℕ} (a out f : ℕ × ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (e : ℝ)
    (μ' : Mem ℝ) : Prop :=
  μ'.store.get f.1 f.2 = some 0 ∧
    ∃ (Tm U E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      HoldsMatrix a Tm μ'.store ∧ HoldsMatrix out U μ'.store ∧ Tm.IsUpperTriangular ∧
        specNorm E ≤ e ∧ (H + E).charpoly.roots = (List.ofFn fun i => Tm i i : Multiset ℂ)

/-- The regions the rounded shifted QR algorithm writes: the matrix, the output and the failure
word. -/
def shqrFp (n : ℕ) (a out f : ℕ × ℕ) : Fp :=
  Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
    Store.inBlock out.1 out.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1

section RoutineAt

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The headline's hypotheses, with their long real constants, make elaboration heavy.
/-- The rounded shifted QR algorithm with a small-eigenvalue routine, with the word count $12$
apart from the routine's words `qs` (none, or $12$; `NLAlib.ShiftedQR.RandomSmallEigContractAt`):
the statement of `NLAlib.ShiftedQR.roundedShQRWith_measureReal_not_spectrum_le`, of which
`NLAlib.ShiftedQR.roundedShQR_measureReal_not_spectrum_le` is the case of the kernel and no
words. -/
theorem roundedShQRWith_measureReal_not_spectrum_le_at {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    (hU : law sU = volume.restrict (Set.Icc 0 1))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hHS : specNorm H ≤ S) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) {βse φse : ℝ} {T : ℕ}
    {qs : List ℝ} {SE : Impl O Q}
    (hSE : RandomSmallEigContractAt law βse φse (min k (n + 1)) 12 T (4 * S) qs SE I)
    (hq12 : qs = [] ∨ qs.length = 12) (hβse0 : 0 ≤ βse)
    (hse : βse ≤ shqrSmallEigAccuracy n B Γ S δ)
    (hφse0 : 0 ≤ φse) (hφse : φse ≤ shqrSmallEigFailure n B Γ S δ φ)
    (hu : u ≤ uShQR n k B Γ S δ φ) {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length, 2 * (n + 1), 1])
    (ha : Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length, 2 * (n + 1), 1])
    (hA : HoldsMatrix a H μ.store)
    (ht : μ.store.get t.1 t.2 = some (shqrDeflationThreshold n k B Γ S δ φ))
    (hp : μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ ++ qs).length =
      some (shqrParams n k B Γ S δ φ ++ qs))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRWith SE).body
      (Env.frame [n + 1, k, (shqrParams n k B Γ S δ φ ++ qs).length, shqrCap n B Γ S δ, T,
        shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length), k * (n + 1)]
        [a, t, p, out, a, out, f]) (shqrFp n a out f) (ShQRSpectrum a out f H δ) μ} ≤ φ := sorry

/-- The rounded shifted QR algorithm with a terminating small-eigenvalue routine terminates on
every tape, with the word count $12$ apart from the routine's words `qs` (none, or $12$;
`NLAlib.ShiftedQR.TerminatingSmallEigAt`): the statement of
`NLAlib.ShiftedQR.roundedShQRWith_terminates`, of which `NLAlib.ShiftedQR.roundedShQR_terminates`
is the case of the kernel and no words. -/
theorem roundedShQRWith_terminates_at {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I) {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hk : k = shqrDegree (4 * B)) {T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : TerminatingSmallEigAt (min k (n + 1)) 12 T qs SE I)
    (hq12 : qs = [] ∨ qs.length = 12)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length, 2 * (n + 1), 1])
    (ha : Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length, 2 * (n + 1), 1])
    (hA : HoldsMatrix a H μ.store) {thr : ℝ} (ht : μ.store.get t.1 t.2 = some thr)
    (hp : μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ ++ qs).length =
      some (shqrParams n k B Γ S δ φ ++ qs)) (τ : Tape ℝ) :
    Writes .total I τ (roundedShQRWith SE).body
      (Env.frame [n + 1, k, (shqrParams n k B Γ S δ φ ++ qs).length, shqrCap n B Γ S δ, T,
        shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length), k * (n + 1)]
        [a, t, p, out, a, out, f]) (shqrFp n a out f) (fun _ => True) μ := sorry

end RoutineAt

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- **The bits of precision** ([BanksGarzaVargasSrivastava2022, Theorem 1.4], corrected: the
printed argument $nB/(\delta\Gamma\varphi)$ is not invariant under scaling of $\mathbf{H}$, and
Optimal's rounding constant, [BanksGarzaVargasSrivastava2022, Lemma 4.5], is $kn^{3/2}$ in place
of $2n^2$): there are absolute constants $c_1, c_2$ such that for every order $n + 1$,
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

end Theorems

/-! ### The algorithm with a small-eigenvalue routine -/

section Routine

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]

/-- **The rounded shifted QR algorithm with a small-eigenvalue routine**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] with the quantifiers of Theorem 1.4, corrected).
Let $\mathbf{H}$ be upper Hessenberg of order $n + 1$,
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$ and eigenvalues separated by $\Gamma > 0$,
$\|\mathbf{H}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of
(eqn:setk) at $4B$. Let the machine have the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$, exact natural literals up to $n + 1$, a
measurable interpretation reading the tape only in its windows, a stream $s_U$ uniform on
$[0, 1]$ with an exact polar disk sampler, and a routine `SE` meeting
`NLAlib.ShiftedQR.RandomSmallEigContract` on orders at most $\min(k, n + 1)$ and norms at most
$4\Sigma$, with
the cap $T$, $12$ words `qs`, forward error $0 \le \beta_{\mathrm{se}} \le$
`shqrSmallEigAccuracy` and failure $0 \le \varphi_{\mathrm{se}} \le$ `shqrSmallEigFailure`. Then
from a memory holding $\mathbf{H}$, the deflation threshold word and the words of
`NLAlib.ShiftedQR.shqrParams` followed by `qs`, under a random tape with the stream laws,
`NLAlib.ShiftedQR.roundedShQRWith SE` fails to write only the matrix, the output and the failure
word, set the failure word to $0$ and store all eigenvalues, with multiplicity, of
$\mathbf{H} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta$, with probability at most
$\varphi$. -/
theorem roundedShQRWith_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    (hU : law sU = volume.restrict (Set.Icc 0 1))
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B) (hΓ : 0 < Γ)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hHS : specNorm H ≤ S) (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) {βse φse : ℝ} {T : ℕ}
    {qs : List ℝ} {SE : Impl O Q}
    (hSE : RandomSmallEigContract law βse φse (min k (n + 1)) T (4 * S) qs SE I)
    (hqs : qs.length = 12) (hβse0 : 0 ≤ βse) (hse : βse ≤ shqrSmallEigAccuracy n B Γ S δ)
    (hφse0 : 0 ≤ φse) (hφse : φse ≤ shqrSmallEigFailure n B Γ S δ φ)
    (hu : u ≤ uShQR n k B Γ S δ φ) {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length, 2 * (n + 1), 1])
    (ha : Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length, 2 * (n + 1), 1])
    (hA : HoldsMatrix a H μ.store)
    (ht : μ.store.get t.1 t.2 = some (shqrDeflationThreshold n k B Γ S δ φ))
    (hp : μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ ++ qs).length =
      some (shqrParams n k B Γ S δ φ ++ qs))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRWith SE).body
      (Env.frame [n + 1, k, (shqrParams n k B Γ S δ φ ++ qs).length, shqrCap n B Γ S δ, T,
        shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length), k * (n + 1)]
        [a, t, p, out, a, out, f]) (shqrFp n a out f) (ShQRSpectrum a out f H δ) μ} ≤ φ :=
  roundedShQRWith_measureReal_not_spectrum_le_at hS hM hL hNat hQ hC hI hloc hDisk hU hHess hV hHV
    hκ hΓ hgap hHS hδ hδS hφ hφ1 hk (hqs ▸ hSE.at) (Or.inr hqs) hβse0 hse hφse0 hφse hu hl hr ha
    hA ht hp hξ

/-- **The rounded shifted QR algorithm with a terminating small-eigenvalue routine terminates on
every tape**: on a scalar machine with index literals, exact natural literals up to $n + 1$, exact
`toNat` and comparisons, an exact polar disk sampler, and a routine `SE` that terminates on orders
at most $\min(k, n + 1)$ with the cap $T$ and $12$ words `qs`
(`NLAlib.ShiftedQR.TerminatingSmallEig`), for any
$(n + 1) \times (n + 1)$ matrix $\mathbf{H}$, any $B, \Gamma, \Sigma, \delta, \varphi$ and $k$ the
degree of (eqn:setk) at $4B$, the run of `NLAlib.ShiftedQR.roundedShQRWith SE` from a memory
holding the input with the words `NLAlib.ShiftedQR.shqrParams` followed by `qs` succeeds on every
tape and writes only the matrix, the output and the failure word. -/
theorem roundedShQRWith_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I) {sU : ℕ}
    (hDisk : IsPolarDiskSampler sU I) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hk : k = shqrDegree (4 * B)) {T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : TerminatingSmallEig (min k (n + 1)) T qs SE I) (hqs : qs.length = 12)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length, 2 * (n + 1), 1])
    (ha : Fp.Apart [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length, 2 * (n + 1), 1])
    (hA : HoldsMatrix a H μ.store) {thr : ℝ} (ht : μ.store.get t.1 t.2 = some thr)
    (hp : μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ ++ qs).length =
      some (shqrParams n k B Γ S δ φ ++ qs)) (τ : Tape ℝ) :
    Writes .total I τ (roundedShQRWith SE).body
      (Env.frame [n + 1, k, (shqrParams n k B Γ S δ φ ++ qs).length, shqrCap n B Γ S δ, T,
        shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length), k * (n + 1)]
        [a, t, p, out, a, out, f]) (shqrFp n a out f) (fun _ => True) μ :=
  roundedShQRWith_terminates_at hS hL hNat hQ hC hDisk hk (hqs ▸ hSE.at) (Or.inr hqs) hl hr ha hA ht
    hp τ

end Routine

end NLAlib.ShiftedQR
