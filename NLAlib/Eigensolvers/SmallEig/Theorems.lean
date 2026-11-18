/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SmallEig.ProgramSchur

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

/-- **The backward listing at $\delta_b$ is a forward one at $\beta$**
([BanksGarzaVargasSrivastava2025, Corollary 1.3], the matching): for $\mathbf{M}$ of order
$n + 1 \le k_{\max}$ with $\|\mathbf{M}\|_2 \le \Sigma$ and $0 < \beta \le \Sigma$, if the
stored block $\widehat{\mathbf{T}}_b$ at `w` lists on its diagonal the spectrum of
$\mathbf{M} + \mathbf{E}$ for some $\|\mathbf{E}\|_2 \le \delta_b$
(`NLAlib.SmallEig.forwardBackwardError`), that diagonal is within $\beta$ of a listing of the
spectrum of $\mathbf{M}$, by the Ostrowski–Elsner matching
(`NLAlib.exists_isEigenvalueListing_norm_sub_le_rpow`) and
`NLAlib.SmallEig.forwardBackwardError_spec`. -/
theorem smallEigSpectrum_forward {kmax n : ℕ} (hn : n + 1 ≤ kmax) {S β : ℝ} (hβ : 0 < β)
    (hβS : β ≤ S) {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hMS : specNorm M ≤ S)
    {o : ℕ × ℕ} {μ' : Mem ℝ} {w : ℕ × ℕ}
    (h : SmallEigSpectrum w o M (forwardBackwardError kmax S β) μ') :
    ∃ (Tb : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ev : Fin (n + 1) → ℂ),
      HoldsMatrix w Tb μ'.store ∧ IsEigenvalueListing M ev ∧ ∀ i, ‖Tb i i - ev i‖ ≤ β := by
  obtain ⟨Tb, -, E, hW, -, -, hE, hL⟩ := h
  obtain ⟨-, hbS, h2⟩ := forwardBackwardError_spec (kmax := kmax) hβ hβS
  obtain ⟨ev, hev, hb⟩ := exists_isEigenvalueListing_norm_sub_le_rpow (A' := M) hL
  refine ⟨Tb, ev, hW, hev, fun i => ?_⟩
  rw [norm_sub_rev]
  refine (hb i).trans (le_trans ?_ (h2 n hn))
  have hα : 0 ≤ 1 - 1 / ((n : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hE' : specNorm (M - (M + E)) = specNorm E := by rw [sub_add_cancel_left, specNorm_neg]
  have hsum : specNorm (M + E) + specNorm M ≤ 3 * S := by
    linarith [specNorm_add_le M E]
  have h0 : 0 ≤ specNorm (M + E) + specNorm M := by positivity
  rw [hE']
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 hsum hα) (by positivity))
    (Real.rpow_le_rpow (specNorm_nonneg _) hE (by positivity)) (by positivity)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))

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
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1))))
      (fun μ' => ∃ (Tb : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ev : Fin (n + 1) → ℂ),
        HoldsMatrix w Tb μ'.store ∧ IsEigenvalueListing M ev ∧
          ∀ i, ‖Tb i i - ev i‖ ≤ β) μ} ≤ φ := by
  obtain ⟨hb0, hbS, -⟩ := forwardBackwardError_spec (kmax := kmax) hβ hβS
  exact ((smallEigProg_pwrites hS hM hL (hNat.mono hn) hQ hC hI hloc hSmp hDisk hU hG hA hB hb₁
    hb₂ hn hMS hb0 hbS hφ hφ1 hu w q o).mono (fun _ h => h) le_rfl
    (fun _ h => smallEigSpectrum_forward hn hβ hβS hMS h) le_rfl).measureReal_not_writes_le hin hξ

set_option maxRecDepth 100000 in
/-- **The operation count of the small-eigenvalue program** ([BanksGarzaVargasSrivastava2025,
Theorem 1.1], running time, on every tape): the instrumented static count
(`NLAlib.Ops.stmtCost` of `NLAlib.Ops.Stmt.instrument`, every structural instruction counted) of
`NLAlib.SmallEig.smallEigProg` at the order $n + 1$, $n_q$ words, the cap $T$ and the zero
offsets of its four operands is at most $80390(n + 1)^4(T + 1)^2$. The count holds on every
tape: the loops are capped by $T$ ($m, t, m_2 \le T$, $q \le m$). The paper's count has the factor
$n$ in its last term (its erratum N5). The constant is the monomial bound of the instrumented
tree (`NLAlib.Ops.size_stmtCost_le_stmtWorkMono`); the certificate's
`NLAlib.SmallEig.smallEigWork` also counts the frame of the program. -/
theorem smallEig_work_le (sG n nq T : ℕ) :
    Count.size (stmtCost (smallEigProg (O := O) (Q := Q) sG).body.instrument
      [n + 1, nq, T, 0, 0, 0, 0]) ≤ 80390 * (n + 1) ^ 4 * (T + 1) ^ 2 := by
  have hw : stmtWorkMono (smallEigProg (O := O) (Q := Q) sG).body.instrument
      ([⟨1, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩] ++ List.replicate 4 (WorkMono.const 0)) =
        ⟨80390, [4, 0, 2]⟩ := by
    kernel_rfl
  have hσ : SlotsLe [n + 1, nq + 1, T + 1] [n + 1, nq, T, 0, 0, 0, 0]
      ([⟨1, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩] ++ List.replicate 4 (WorkMono.const 0)) := by
    simp [SlotsLe, WorkMono.eval, WorkMono.const]
  have h := size_stmtCost_le_stmtWorkMono (by simp)
    (smallEigProg (O := O) (Q := Q) sG).body.instrument hσ
  rw [hw] at h
  simpa [WorkMono.eval, mul_assoc] using h

/-- **The cap of the small-eigenvalue program is polylogarithmic**: for tail records with
$b_1, b_2 > 0$ there are constants $c$ and $p$ with
$T \le c(\log_2(4(n_{\max} + 1)\Sigma/(\delta\varphi)) + 1)^p$, $T$ = `NLAlib.SmallEig.smallEigCap`,
for every $n_{\max} \ge 1$, $0 < \delta \le \Sigma$ and $0 < \varphi \le 1$ (the degree, round and
step caps are logarithms of the condition, weight and accuracy thresholds, themselves polynomial in
$n_{\max}\Sigma/(\delta\varphi)$). -/
theorem smallEigCap_le_log (c₁ c₂ : PolyLogTail) (hb₁ : 0 < c₁.b) (hb₂ : 0 < c₂.b) :
    ∃ (c : ℝ) (p : ℕ), ∀ {nmax : ℕ} {S δ φ : ℝ}, 1 ≤ nmax → 0 < δ → δ ≤ S → 0 < φ → φ ≤ 1 →
      (smallEigCap nmax S δ φ c₁ c₂ : ℝ) ≤
        c * (Real.logb 2 (4 * (nmax + 1) * S / (δ * φ)) + 1) ^ p := by
  obtain ⟨c, hc, h⟩ := smallEigCap_le_logb c₁ c₂ hb₁ hb₂
  refine ⟨c, 1, fun {nmax S δ φ} hn hδ hδS hφ hφ1 => (h hn hδ hδS hφ hφ1).trans ?_⟩
  have hn' : (1 : ℝ) ≤ nmax := by exact_mod_cast hn
  have hS : 0 < S := hδ.trans_le hδS
  rw [pow_one]
  have : Real.logb 2 (4 * nmax * S / (δ * φ)) ≤ Real.logb 2 (4 * (nmax + 1) * S / (δ * φ)) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) (by gcongr; linarith)
  exact mul_le_mul_of_nonneg_left (by linarith) hc

/-- **The small-eigenvalue program is a small-block Schur solver**
([BanksGarzaVargasSrivastava2025, Theorem 1.1 and Corollary 1.3], with the Schur form): on the
machine and streams of `NLAlib.SmallEig.smallEigProg_pwrites_schur`, with exact natural literals
up to $d_{\max} \le k_{\max}$, $0 < \beta \le \Sigma$, $0 < \varphi \le 1$ and
$\boldsymbol{u} \le \boldsymbol{u}^{\mathrm{fwd}}_{\mathrm{SmallEig}}$
(`NLAlib.SmallEig.uSmallEigForward`), the program with the forward
words `NLAlib.SmallEig.smallEigForwardParams` and cap meets
`NLAlib.Schur.RandomSchurLeafContract` on the orders at most $d_{\max}$ and norms at most
$\Sigma$: the backward error is the backward accuracy
$\delta_b$ = `NLAlib.SmallEig.forwardBackwardError` of $\beta$, the failure $\varphi$ and the
accumulator error $(1 + 24\boldsymbol{u})^R - 1$, $R$ = `NLAlib.SmallEig.smallEigLeafRotations`
at $k_{\max}$ and the cap. Orders $d \le 1$ are kept with the identity accumulator. -/
theorem smallEigProg_randomSchurLeafContract {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
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
    refine PWrites.of_writes hφ.le fun μ τ ⟨hW, _, hl, hroom, hap⟩ => ?_
    have hwu : Fp.Disj (Store.inBlock w.1 w.2 (2 * (0 * 0)))
        (Store.inBlock ub.1 ub.2 (2 * (0 * 0))) := by
      simpa using hap.disj_getD_of_lt (i := 0) (j := 2) (by omega) (by simp)
    unfold smallEigProg
    have hl4 : μ.Live [w, p, w, ub] := fun x hx => hl x (by simp at hx ⊢; tauto)
    refine (identityLeaf_writes (O := O) (Q := Q) (τ := τ) hS h0 (fun h => absurd h (lt_irrefl 0))
      hroom).frame_seq_le rfl rfl hl4 le_sup_right ?_
    rintro μ' hfr ⟨-, hU⟩
    refine writes_ifPos (n := 0) rfl ?_
    rw [if_neg (lt_irrefl 0)]
    refine ⟨1, B, ⟨hW.of_eqOff hfr hwu.symm, hU⟩, fun i => i.elim0,
      (IsTrackedUnitarySimilar.refl 1 B).mono hR0 hb0.le⟩
  · have hdk' : n + 1 ≤ kmax := hd.trans hdk
    refine (smallEigProg_pwrites_schur hS hM hL (hNat.mono hd) hQ hC hI hloc hSmp hDisk hU hG
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
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock o.1 o.2 (2 * ((n + 1) * (n + 1))))
      (fun μ' => ∃ (Tb : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ev : Fin (n + 1) → ℂ),
        HoldsMatrix w Tb μ'.store ∧ IsEigenvalueListing M ev ∧
          ∀ i, ‖Tb i i - ev i‖ ≤ β) μ} ≤ φ := by
  apply smallEig_measureReal_not_forward_le
    (hA := boundsGinibreGap_ginibreGapTail) (hB := boundsGinibreCondition_ginibreConditionTail)
    (hb₁ := ginibreGapTail_b_pos) (hb₂ := ginibreConditionTail_b_pos) <;> assumption

end NLAlib.SmallEig
