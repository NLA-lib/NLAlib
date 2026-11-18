/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.Program
public import NLAlib.Matrix.Perturbation.EigenvalueMatching
public import NLAlib.Ops.Confined
public import NLAlib.Ops.MonomialWork
public import NLAlib.Ops.Static
public import NLAlib.Eigensolvers.SmallEig.Precision

/-!
# The small-eigenvalue solver: headline theorems

[BanksGarzaVargasSrivastava2025, Theorem 1.1] as a theorem about the fixed program
`NLAlib.SmallEig.smallEigProg`: on any complex matrix $\mathbf{M}$ of order at most $n_{\max}$ and
norm at most $\Sigma$, with probability at least $1 - \varphi$ the program stores all eigenvalues
of $\mathbf{M} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta$, at the unit roundoff
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$, conditional on the two random-matrix
theorems (`NLAlib.PolyLogTail.BoundsGinibreGap`, `NLAlib.PolyLogTail.BoundsGinibreCondition`),
which are hypotheses here and proved at the records
`NLAlib.ginibreGapTail` <!-- value ginibreGapTail --> $(10000e, 5, 1/2, 2)$,
`NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail --> $(128e, 3, 2, 2)$ (the
`_unconditional` corollaries). The error is absolute: $\Sigma$ is an input, the paper's relative
form is the corollary `NLAlib.SmallEig.smallEig_relative`. [BanksGarzaVargasSrivastava2025,
Corollary 1.3] is the forward contract on blocks of order at most $k_{\max}$ and norm at most
$\Sigma$ (`NLAlib.SmallEig.smallEigProg_pwrites`), which the shifted QR algorithm
consumes.

What is not claimed: a rounded Gaussian or disk sampler (the draws are exact tape values; their
rounding after the draw is modelled), range safety, the paper's question of $O(n^3)$ work.

## Main results

* `NLAlib.SmallEig.smallEigProg_pwrites`: Theorem 1.1 as a probabilistic block specification.
* `NLAlib.SmallEig.smallEig_measureReal_not_spectrum_le`: Theorem 1.1.
* `NLAlib.SmallEig.smallEig_relative`: the relative form.
* `NLAlib.SmallEig.smallEigProg_pwrites`: Corollary 1.3 as a routine contract.
* `NLAlib.SmallEig.smallEig_measureReal_not_forward_le`: Corollary 1.3 for one input.
* `NLAlib.SmallEig.smallEig_work_le`: the operation count.
* `NLAlib.SmallEig.smallEigProg_pwrites_schur`: Theorem 1.1 in Schur form, the computed
  $(\widehat{\mathbf{U}}_b, \widehat{\mathbf{T}}_b)$ tracked from $(\mathbf{I}, \mathbf{M})$.
* `NLAlib.SmallEig.smallEigProg_randomSchurLeafContract`: the program is a small-block Schur
  solver (`NLAlib.Schur.RandomSchurLeafContract`) at the forward words.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib.SmallEig

open Ops ShiftedQR

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has SampleOp O] [Has DiskSampleOp O]
  [Has CmpTst Q] [Has IdxTst Q]

/-! ### The pieces of the proofs -/

/-- A matrix of order at most $1$ is listed by its diagonal. -/
theorem isEigenvalueListing_diag_of_le_one {d : ℕ} (hd : d ≤ 1) (B : Matrix (Fin d) (Fin d) ℂ) :
    IsEigenvalueListing B fun i => B i i := by
  have hT : B.IsUpperTriangular := fun i j hji => absurd hji (by omega)
  simpa using hT.isEigenvalueListing_diag

/-- **A tracked Schur pair lists a nearby spectrum** (PP3 at the leaf): if the stored pair
$(\widehat{\mathbf{U}}_b, \widehat{\mathbf{T}}_b)$ at `(o, w)` has $\widehat{\mathbf{T}}_b$ upper
triangular and is tracked from $(\mathbf{I}, \mathbf{M})$ with the backward error $\delta$, then
the diagonal of $\widehat{\mathbf{T}}_b$ lists the spectrum of $\mathbf{M} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le \delta$ (`NLAlib.SmallEig.SmallEigSpectrum`). -/
theorem smallEigSpectrum_of_tracked {n : ℕ} {w o : ℕ × ℕ}
    {M Ub Tb : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {εU δ : ℝ} {μ' : Mem ℝ}
    (hP : Schur.HoldsSchurPair w o Ub Tb μ'.store) (hT : Tb.IsUpperTriangular)
    (ht : IsTrackedUnitarySimilar εU δ 1 M Ub Tb) : SmallEigSpectrum w o M δ μ' := by
  obtain ⟨V, ⟨hV, E, hE, rfl⟩, -⟩ := ht
  exact ⟨_, Ub, E, hP.1, hP.2, hT, hE,
    hV.isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul hT⟩

/-- The precision threshold is at most $1/100$: for tail records with $b_1, b_2 > 0$,
$n_{\max} \ge 1$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$,
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ gives $\boldsymbol{u} \le 1/100$. -/
theorem le_one_div_hundred_of_le_uSmallEig {c₁ c₂ : PolyLogTail} (hb₁ : 0 < c₁.b)
    (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : 1 ≤ nmax) {S δ φ u : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S)
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) : u ≤ 1 / 100 := by
  obtain ⟨-, h1, -⟩ := uSmallEig_spec hb₁ hb₂ hn hδ hδS hφ hφ1
  have : uSmallEigBasic nmax ≤ 1 / 20 := min_le_left _ _
  linarith

/-- **The small-eigenvalue program as a probabilistic block** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1]): let the machine have the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ (`NLAlib.SmallEig.uSmallEig` at
$n_{\max}$), index literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons, a
measurable interpretation reading the tape only in its windows, draws that store the tape entry,
a stream $s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on it, and a stream $s_G$ with
the standard real Gaussian law; let the eigenvalue gap and the eigenvector condition of a complex
Ginibre perturbation have the tails $c_1$, $c_2$ with $b_1, b_2 > 0$; let $n + 1 \le n_{\max}$,
$\mathbf{M}$ of order $n + 1$ with $\|\mathbf{M}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$ and
$0 < \varphi \le 1$. Then from a memory holding $\mathbf{M}$ and the words
(`NLAlib.SmallEig.SmallEigInput`), except with probability at most $\varphi$, the run of
`NLAlib.SmallEig.smallEigProg` writes only its output and lists the spectrum of
$\mathbf{M} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta$
(`NLAlib.SmallEig.SmallEigSpectrum`). The order $1$ is copied; otherwise the perturbation
(`NLAlib.SmallEig.ginibrePerturb_pwrites`, $3\varphi/4$), the reduction
(`NLAlib.SmallEig.smallEigProg_reduce_pwrites`) and the core
(`NLAlib.SmallEig.smallEigProg_core_pwrites`, $\varphi/4$) compose by `NLAlib.Ops.PWrites.seq`;
the backward errors $\delta/2 + \delta/8 + \delta/4$ add. -/
theorem smallEigProg_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S δ φ : ℝ} (hMS : specNorm M ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) (w q o : ℕ × ℕ) :
    PWrites law I (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S δ φ c₁ c₂) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1)))) (SmallEigInput nmax S δ φ c₁ c₂ w q o M)
      (SmallEigSpectrum w o M δ) φ :=
  (smallEigProg_pwrites_schur hS hM (le_one_div_hundred_of_le_uSmallEig hb₁ hb₂ (by omega) hδ hδS
    hφ hφ1 hu) hL hNat hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁ hb₂ hn hMS hδ hδS hφ hφ1 hu w q
    o).mono (fun _ h => h) le_rfl (fun _ ⟨_, _, hP, hT, ht⟩ => smallEigSpectrum_of_tracked hP hT ht)
    le_rfl

/-- **The backward listing at $\delta_b$ is a forward one at $\beta$**
([BanksGarzaVargasSrivastava2025, Corollary 1.3], the matching): for $\mathbf{M}$ of order
$n + 1 \le k_{\max}$ with $\|\mathbf{M}\|_2 \le \Sigma$ and $0 < \beta \le \Sigma$, an output
listing the spectrum of $\mathbf{M} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta_b$
(`NLAlib.SmallEig.forwardBackwardError`) is within $\beta$ of a listing of the spectrum of
$\mathbf{M}$, by the Ostrowski–Elsner matching
(`NLAlib.exists_isEigenvalueListing_norm_sub_le_rpow`) and
`NLAlib.SmallEig.forwardBackwardError_spec`. -/
theorem smallEigSpectrum_forward {kmax n : ℕ} (hn : n + 1 ≤ kmax) {S β : ℝ} (hβ : 0 < β)
    (hβS : β ≤ S) {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hMS : specNorm M ≤ S)
    {o : ℕ × ℕ} {μ' : Mem ℝ} {w : ℕ × ℕ}
        (h : SmallEigSpectrum w o M (forwardBackwardError kmax S β) μ') :
    ∃ roots ev : Fin (n + 1) → ℂ, IsEigenvalueListing M ev ∧ (∀ i, ‖roots i - ev i‖ ≤ β) ∧
      HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store := sorry

/-- **The small-eigenvalue solver** ([BanksGarzaVargasSrivastava2025, Theorem 1.1], corrected:
$\Sigma$ an input, the base case of order $1$, every loop capped, the error absolute). Let the
machine have the standard model at $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$, index
literals, exact natural literals up to $n + 1$, exact `toNat` and comparisons, a measurable
interpretation reading the tape only in its windows, draws that store the tape entry, a stream
$s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on it, and a stream $s_G$ with the
standard real Gaussian law; let the eigenvalue gap and the eigenvector condition of a complex
Ginibre perturbation have the tails $c_1$, $c_2$ with $b_1, b_2 > 0$. Let $n + 1 \le n_{\max}$,
$\mathbf{M}$ of order $n + 1$ with $\|\mathbf{M}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$ and
$0 < \varphi \le 1$. Then from a memory holding $\mathbf{M}$ and the words of
`NLAlib.SmallEig.smallEigParams`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{smallEigProg}(\mathbf{M}) \text{ fails, or writes outside its output,
  or lists no } \operatorname{spec}(\mathbf{M} + \mathbf{E}),\ \|\mathbf{E}\|_2 \le \delta\bigr]
  \le \varphi\,.$$
Here $\boldsymbol{u}_{\mathrm{SmallEig}}$ is `NLAlib.SmallEig.uSmallEig` at $n_{\max}$.
[BanksGarzaVargasSrivastava2025, Theorem 1.1]; there $\Sigma$ is not an input (its errata P9,
N4) and the error is relative.

Note: The run terminates on every tape (`NLAlib.SmallEig.smallEigProg_terminates`). The failure
is split in four: the gap, the condition, the norm of the perturbation, and the worklist.
Result: small-eig-backward-error -/
theorem smallEig_measureReal_not_spectrum_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S δ φ : ℝ} (hMS : specNorm M ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂)
    {w q o : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigInput nmax S δ φ c₁ c₂ w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S δ φ c₁ c₂) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1)))) (SmallEigSpectrum w o M δ) μ} ≤ φ :=
  (smallEigProg_pwrites hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁ hb₂ hn hMS hδ hδS hφ
    hφ1 hu w q o).measureReal_not_writes_le hin hξ

/-- **The small-eigenvalue solver, relative form** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], as printed: the error relative to $\|\mathbf{M}\|_2$). With the hypotheses on the
machine, the streams and the tails of `NLAlib.SmallEig.smallEig_measureReal_not_spectrum_le`
written out below: let $n + 1 \le n_{\max}$, $\mathbf{M}$ of order $n + 1$, $c \ge 1$ and
$\Sigma > 0$ with $\|\mathbf{M}\|_2 \le \Sigma \le c\|\mathbf{M}\|_2$, $0 < \varepsilon \le 1$,
$0 < \varphi \le 1$, and $\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ at the absolute
error $\varepsilon\Sigma/c$. Then from a memory holding $\mathbf{M}$ and the words at
$\delta = \varepsilon\Sigma/c$,
$$\mathbb{P}\bigl[\mathsf{smallEigProg}(\mathbf{M}) \text{ fails, or writes outside its output,
  or lists no } \operatorname{spec}(\mathbf{M} + \mathbf{E}),\
  \|\mathbf{E}\|_2 \le \varepsilon\|\mathbf{M}\|_2\bigr] \le \varphi\,.$$
[BanksGarzaVargasSrivastava2025, Theorem 1.1]; the bound $\Sigma$ of the norm is an input there
too (its errata P9, N4).
Result: small-eig-backward-error -/
theorem smallEig_relative {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S c ε φ : ℝ} (hS0 : 0 < S) (hMS : specNorm M ≤ S)
    (hc : 1 ≤ c) (hSM : S ≤ c * specNorm M) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S (ε * S / c) φ c₁ c₂)
    {w q o : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigInput nmax S (ε * S / c) φ c₁ c₂ w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S (ε * S / c) φ c₁ c₂) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1))))
            (SmallEigSpectrum w o M (ε * specNorm M)) μ} ≤ φ := by
  have hc0 : 0 < c := by linarith
  have hδ : 0 < ε * S / c := by positivity
  have hδS : ε * S / c ≤ S := by
    rw [div_le_iff₀ hc0]; nlinarith
  have hδM : ε * S / c ≤ ε * specNorm M := by
    rw [div_le_iff₀ hc0]; nlinarith [mul_le_mul_of_nonneg_left hSM hε.le]
  exact ((smallEigProg_pwrites hS hM hL hNat hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁ hb₂ hn hMS
    hδ hδS hφ hφ1 hu w q o).mono (fun _ h => h) le_rfl
    (fun _ ⟨Tb, Ub, E, hT, hO, hTu, hE, hLst⟩ => ⟨Tb, Ub, E, hT, hO, hTu, hE.trans hδM, hLst⟩)
    le_rfl).measureReal_not_writes_le hin hξ

/-- **The forward error on one input** ([BanksGarzaVargasSrivastava2025, Corollary 1.3]): with the
hypotheses on the machine, the streams and the tails written out in
`NLAlib.SmallEig.smallEigProg_pwrites` (standard model at
$\boldsymbol{u} \le \boldsymbol{u}^{\mathrm{fwd}}_{\mathrm{SmallEig}}$, exact literals up to
$k_{\max}$, a measurable tape-local interpretation, the uniform and Gaussian streams, the tails
with $b_1, b_2 > 0$): for $\mathbf{M}$ of order $n + 1 \le k_{\max}$ with
$\|\mathbf{M}\|_2 \le \Sigma$, $0 < \beta \le \Sigma$ and $0 < \varphi \le 1$, from a memory
holding $\mathbf{M}$ and the words `NLAlib.SmallEig.smallEigForwardParams`,
$$\mathbb{P}\bigl[\mathsf{smallEigProg}(\mathbf{M}) \text{ fails, or writes outside its output,
  or lists no } \boldsymbol{\mu} \text{ with } \lvert\mu_i - \lambda_i\rvert \le \beta\bigr]
  \le \varphi$$
for a listing $\boldsymbol{\lambda}$ of the eigenvalues of $\mathbf{M}$.
Result: small-eig-forward-error -/
theorem smallEig_measureReal_not_forward_le {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    {kmax : ℕ} (hNat : IsExactNatLit id Mch kmax) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {S β φ : ℝ} (hβ : 0 < β) (hβS : β ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEigForward kmax S β φ c₁ c₂) {n : ℕ} (hn : n + 1 ≤ kmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hMS : specNorm M ≤ S) {w q o : ℕ × ℕ}
    {μ : Mem ℝ} (hin : SmallEigInput kmax S (forwardBackwardError kmax S β) φ c₁ c₂ w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n kmax S (forwardBackwardError kmax S β) φ c₁ c₂) [w, q, w, o])
      (Store.inBlock o.1 o.2 (2 * (n + 1)))
      (fun μ' => ∃ roots ev : Fin (n + 1) → ℂ, IsEigenvalueListing M ev ∧
        (∀ i, ‖roots i - ev i‖ ≤ β) ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) μ} ≤ φ := sorry

/-- **The operation count of the small-eigenvalue program** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], running time, on every tape): there is an absolute constant $c$ such that the static
count (`NLAlib.Ops.stmtCost`) of `NLAlib.SmallEig.smallEigProg` at the order $n + 1$, $n_q$ words
and the cap $T$ has at most $c(n + 1)^4(T + 1)^2$ operations and tests. The count holds on every
tape: the loops are capped by $T$ ($m, t, m_2 \le T$, $q \le m$). The paper's count has the factor
$n$ in its last term (its erratum N5). The monomial bound of the tree
(`NLAlib.Ops.size_stmtCost_le_stmtWorkMono`) gives $c = 3473$; the certificate's
`NLAlib.SmallEig.smallEigWork` is larger because its instrumentation also counts the structural
instructions. -/
theorem smallEig_work_le (sG : ℕ) : ∃ c : ℕ, ∀ n nq T : ℕ,
    Count.size (stmtCost (smallEigProg (O := O) (Q := Q) sG).body [n + 1, nq, T]) ≤
      c * (n + 1) ^ 4 * (T + 1) ^ 2 := sorry

/-- **The cap of the small-eigenvalue program is polylogarithmic**: for tail records with
$b_1, b_2 > 0$ there are constants $c$ and $p$ with
$T \le c(\log_2(4(n_{\max} + 1)\Sigma/(\delta\varphi)) + 1)^p$, $T$ = `NLAlib.SmallEig.smallEigCap`,
for every $n_{\max} \ge 1$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$ (the degree, round and
step caps are logarithms of the condition, weight and accuracy thresholds, themselves polynomial in
$n_{\max}\Sigma/(\delta\varphi)$). -/
theorem smallEigCap_le_log (c₁ c₂ : PolyLogTail) (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    ∃ (c : ℝ) (p : ℕ), ∀ {nmax : ℕ} {S δ φ : ℝ}, 1 ≤ nmax → 0 < δ → δ ≤ S → 0 < φ → φ ≤ 1 →
      (smallEigCap nmax S δ φ c₁ c₂ : ℝ) ≤
        c * (Real.logb 2 (4 * (nmax + 1) * S / (δ * φ)) + 1) ^ p :=
  sorry

/-! ### The Schur form -/

/-- The rotation count of the accumulator of `NLAlib.SmallEig.smallEigProg` on blocks of order at
most $k_{\max}$ with the cap $T$: the $k_{\max}^2$ replayed rotations of the reduction and the
replays of the core's $2(k_{\max} + 1)$ rounds at the bottom width $1$, each of a log of
$(T + k_{\max})k_{\max}$ entries and the products of the order-one leaves ($6$). -/
def smallEigLeafRotations (kmax T : ℕ) : ℕ :=
  kmax * kmax + 2 * (kmax + 1) * ((T + kmax) * kmax + 6)

/-- **The small-eigenvalue program in Schur form** ([BanksGarzaVargasSrivastava2025, Theorem 1.1],
with the Schur form): let the machine have the standard model at
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{SmallEig}}$ (`NLAlib.SmallEig.uSmallEig` at
$n_{\max}$) and $\boldsymbol{u} \le 1/100$, index literals, exact natural literals up to
$n + 1$, exact `toNat` and comparisons, a measurable interpretation reading the tape only in its
windows, draws that store the tape entry, a stream $s_U$ uniform on $[0, 1]$ with an exact polar
disk sampler on it, and a stream $s_G$ with the standard real Gaussian law; let the eigenvalue gap
and the eigenvector condition of a complex Ginibre perturbation have the tails $c_1$, $c_2$ with
$b_1, b_2 > 0$; let $n + 1 \le n_{\max}$, $\mathbf{M}$ of order $n + 1$ with
$\|\mathbf{M}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$. Then from a
memory holding $\mathbf{M}$ and the words (`NLAlib.SmallEig.SmallEigInput`), except with
probability at most $\varphi$, the run writes only the block and the accumulator and stores an
upper triangular $\widehat{\mathbf{T}}_b$ and $\widehat{\mathbf{U}}_b$ with
$\|\widehat{\mathbf{U}}_b - \mathbf{V}\|_2 \le (1 + 24\boldsymbol{u})^{R} - 1$ and
$\widehat{\mathbf{T}}_b = \mathbf{V}^{\mathsf H}(\mathbf{M} + \mathbf{E})\mathbf{V}$ for an exact
unitary $\mathbf{V}$ and some $\|\mathbf{E}\|_2 \le \delta$, $R$ =
`NLAlib.SmallEig.smallEigLeafRotations` at $n_{\max}$ and the cap. -/
theorem smallEigProg_pwrites_schur {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu1 : u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S δ φ : ℝ} (hMS : specNorm M ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ c₁ c₂) (w q o : ℕ × ℕ) :
    PWrites law I (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S δ φ c₁ c₂) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1)))) (SmallEigInput nmax S δ φ c₁ c₂ w q o M)
      (fun μ' => ∃ Ub Tb : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        Schur.HoldsSchurPair w o Ub Tb μ'.store ∧ Tb.IsUpperTriangular ∧
        IsTrackedUnitarySimilar
          ((1 + 24 * u) ^ smallEigLeafRotations nmax (smallEigCap nmax S δ φ c₁ c₂) - 1) δ 1 M
          Ub Tb) φ := sorry

/-- **The small-eigenvalue program is a small-block Schur solver**
([BanksGarzaVargasSrivastava2025, Theorem 1.1 and Corollary 1.3], with the Schur form): on the
machine and streams of `NLAlib.SmallEig.smallEigProg_pwrites_schur`, with exact natural literals
up to $d_{\max} \le k_{\max}$, $0 < \beta \le \Sigma$, $0 < \varphi \le 1$ and
$\boldsymbol{u} \le \boldsymbol{u}^{\mathrm{fwd}}_{\mathrm{SmallEig}}$
(`NLAlib.SmallEig.uSmallEigForward`) and $\boldsymbol{u} \le 1/100$, the program with the forward
words `NLAlib.SmallEig.smallEigForwardParams` and cap meets
`NLAlib.Schur.RandomSchurLeafContract` on the orders at most $d_{\max}$ and norms at most
$\Sigma$: the backward error is the backward accuracy
$\delta_b$ = `NLAlib.SmallEig.forwardBackwardError` of $\beta$, the failure $\varphi$ and the
accumulator error $(1 + 24\boldsymbol{u})^R - 1$, $R$ = `NLAlib.SmallEig.smallEigLeafRotations`
at $k_{\max}$ and the cap. Orders $d \le 1$ are kept with the identity accumulator. -/
theorem smallEigProg_randomSchurLeafContract {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu1 : u ≤ 1 / 100) (hL : IsIndexLit Mch I)
    {dmax kmax : ℕ} (hdk : dmax ≤ kmax) (hNat : IsExactNatLit id Mch dmax) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {c₁ c₂ : PolyLogTail}
    (hA : c₁.BoundsGinibreGap) (hB : c₂.BoundsGinibreCondition)
    (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) {S β φ : ℝ} (hβ : 0 < β) (hβS : β ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEigForward kmax S β φ c₁ c₂) :
    Schur.RandomSchurLeafContract law
      ((1 + 24 * u) ^ smallEigLeafRotations kmax (smallEigForwardCap kmax S β φ c₁ c₂) - 1)
      (forwardBackwardError kmax S β) φ dmax S (smallEigForwardParams kmax S β φ c₁ c₂)
      (smallEigForwardCap kmax S β φ c₁ c₂) (smallEigProg (O := O) (Q := Q) sG) I := by
  intro d w p ub B hd hBS
  obtain ⟨hb0, hbS, -⟩ := forwardBackwardError_spec (kmax := kmax) hβ hβS
  have hR0 : 0 ≤ (1 + 24 * u) ^ smallEigLeafRotations kmax
      (smallEigForwardCap kmax S β φ c₁ c₂) - 1 := by
    have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
    have := one_le_pow₀ (M₀ := ℝ) (n := smallEigLeafRotations kmax
      (smallEigForwardCap kmax S β φ c₁ c₂)) (by linarith : (1 : ℝ) ≤ 1 + 24 * u)
    linarith
  rcases d with _ | n
  · have h0 : Mch.lit 0 = 0 := by simpa using hM.lit 0
    have h1 : Mch.lit 1 = 1 := by simpa using hM.lit 1
    refine PWrites.of_writes hφ.le fun μ τ ⟨hW, _, hl, hroom, hap⟩ => ?_
    have hwu : Fp.Disj (Store.inBlock w.1 w.2 (2 * (0 * 0)))
        (Store.inBlock ub.1 ub.2 (2 * (0 * 0))) := by
      simpa using hap.disj_getD_of_lt (i := 0) (j := 2) (by omega) (by simp)
    unfold smallEigProg
    refine ((identityLeaf_writes (O := O) (Q := Q) (τ := τ) hS h0 h1 hl hroom hwu).in_frame rfl
      rfl hl).seq_le le_sup_right ?_
    rintro μ' hfr ⟨-, hU⟩
    refine writes_ifPos (n := 0) rfl ?_
    rw [if_neg (lt_irrefl 0)]
    refine ⟨1, B, ⟨hW.of_eqOff hfr hwu.symm, hU⟩, fun i => i.elim0,
      (IsTrackedUnitarySimilar.refl 1 B).mono hR0 hb0.le⟩
  · have hdk' : n + 1 ≤ kmax := hd.trans hdk
    refine (smallEigProg_pwrites_schur hS hM hu1 hL (hNat.mono hd) hQ hC hI hloc hSmp hDisk hU hG
      hA hB hb₁ hb₂ hdk' hBS hb0 hbS hφ hφ1 hu w p ub).mono ?_ le_rfl (fun _ h => h) le_rfl
    rintro μ ⟨hW, hq, hl, hroom, hap⟩
    simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, Fp.disj_bot_right,
      and_true] at hap
    exact ⟨hW, hq, hl, hroom, hap.1.2, Fp.disj_sup_right.mpr ⟨hap.1.1.symm, hap.2⟩⟩

/-! ### With the proved random-matrix tails -/

/-- **The small-eigenvalue solver, unconditional**.
The unconditional form of `NLAlib.SmallEig.smallEig_measureReal_not_spectrum_le`
([BanksGarzaVargasSrivastava2025, Theorem 1.1]): the eigenvalue-gap and eigenvector-condition tails
of a complex Ginibre perturbation are proved, at the records
`NLAlib.ginibreGapTail` <!-- value ginibreGapTail --> $(10000e, 5, 1/2, 2)$ and
`NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail --> $(128e, 3, 2, 2)$.
Result: small-eig-backward-error -/
theorem smallEig_measureReal_not_spectrum_le_unconditional {Mch : Machine ℝ} {I : Interp O Q ℝ} {u
  : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S δ φ : ℝ} (hMS : specNorm M ≤ S)
    (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hu : u ≤ uSmallEig nmax S δ φ ginibreGapTail ginibreConditionTail)
    {w q o : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigInput nmax S δ φ ginibreGapTail
      ginibreConditionTail w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S δ φ ginibreGapTail
        ginibreConditionTail) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1)))) (SmallEigSpectrum w o M δ) μ} ≤ φ := by
  apply smallEig_measureReal_not_spectrum_le
    (hA := boundsGinibreGap_ginibreGapTail) (hB := boundsGinibreCondition_ginibreConditionTail)
    (hb₁ := ginibreGapTail_b_pos) (hb₂ := ginibreConditionTail_b_pos) <;> assumption

/-- **The small-eigenvalue solver, relative form, unconditional**.
The unconditional form of `NLAlib.SmallEig.smallEig_relative` ([BanksGarzaVargasSrivastava2025,
Theorem 1.1]): the eigenvalue-gap and eigenvector-condition tails of a complex Ginibre perturbation
are proved, at the records `NLAlib.ginibreGapTail` <!-- value ginibreGapTail -->
$(10000e, 5, 1/2, 2)$ and `NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail -->
$(128e, 3, 2, 2)$.
Result: small-eig-backward-error -/
theorem smallEig_relative_unconditional {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {nmax : ℕ} (hn : n + 1 ≤ nmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {S c ε φ : ℝ} (hS0 : 0 < S) (hMS : specNorm M ≤ S)
    (hc : 1 ≤ c) (hSM : S ≤ c * specNorm M) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEig nmax S (ε * S / c) φ ginibreGapTail
      ginibreConditionTail)
    {w q o : ℕ × ℕ} {μ : Mem ℝ} (hin : SmallEigInput nmax S (ε * S / c) φ
      ginibreGapTail ginibreConditionTail w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n nmax S (ε * S / c) φ ginibreGapTail
        ginibreConditionTail) [w, q, w, o])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1))))
            (SmallEigSpectrum w o M (ε * specNorm M)) μ} ≤ φ := by
  apply smallEig_relative
    (hA := boundsGinibreGap_ginibreGapTail) (hB := boundsGinibreCondition_ginibreConditionTail)
    (hb₁ := ginibreGapTail_b_pos) (hb₂ := ginibreConditionTail_b_pos) <;> assumption

/-- **The forward error on one input, unconditional**.
The unconditional form of `NLAlib.SmallEig.smallEig_measureReal_not_forward_le`
([BanksGarzaVargasSrivastava2025, Corollary 1.3]): the eigenvalue-gap and eigenvector-condition
tails of a complex Ginibre perturbation are proved, at the records
`NLAlib.ginibreGapTail` <!-- value ginibreGapTail --> $(10000e, 5, 1/2, 2)$ and
`NLAlib.ginibreConditionTail` <!-- value ginibreConditionTail --> $(128e, 3, 2, 2)$.
Result: small-eig-forward-error -/
theorem smallEig_measureReal_not_forward_le_unconditional {Mch : Machine ℝ} {I : Interp O Q ℝ} {u :
  ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    {kmax : ℕ} (hNat : IsExactNatLit id Mch kmax) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hSmp : IsSample I) {law : ℕ → Measure ℝ} {sU sG : ℕ}
    (hDisk : IsPolarDiskSampler sU I) (hU : law sU = volume.restrict (Set.Icc 0 1))
    (hG : law sG = gaussianReal 0 1) {S β φ : ℝ} (hβ : 0 < β) (hβS : β ≤ S) (hφ : 0 < φ)
    (hφ1 : φ ≤ 1) (hu : u ≤ uSmallEigForward kmax S β φ ginibreGapTail
      ginibreConditionTail) {n : ℕ} (hn : n + 1 ≤ kmax)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hMS : specNorm M ≤ S) {w q o : ℕ × ℕ}
    {μ : Mem ℝ} (hin : SmallEigInput kmax S (forwardBackwardError kmax S β) φ
      ginibreGapTail ginibreConditionTail w q o M μ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω | ¬ Writes .total I (ξ ω) (smallEigProg (O := O) (Q := Q) sG).body
      (Env.frame (smallEigDims n kmax S (forwardBackwardError kmax S β) φ
        ginibreGapTail ginibreConditionTail) [w, q, w, o])
      (Store.inBlock o.1 o.2 (2 * (n + 1)))
      (fun μ' => ∃ roots ev : Fin (n + 1) → ℂ, IsEigenvalueListing M ev ∧
        (∀ i, ‖roots i - ev i‖ ≤ β) ∧
        HoldsMatrix o (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store) μ} ≤ φ := by
  apply smallEig_measureReal_not_forward_le
    (hA := boundsGinibreGap_ginibreGapTail) (hB := boundsGinibreCondition_ginibreConditionTail)
    (hb₁ := ginibreGapTail_b_pos) (hb₂ := ginibreConditionTail_b_pos) <;> assumption

end NLAlib.SmallEig
