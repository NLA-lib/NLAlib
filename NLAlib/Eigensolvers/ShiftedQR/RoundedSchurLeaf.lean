/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedTheorems
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveCompletion

/-!
# The rounded shifted QR algorithm with a small-block Schur solver

[BanksGarzaVargasSrivastava2022, Theorem 6.3] with the quantifiers of
[BanksGarzaVargasSrivastava2022, Theorem 1.4], in floating point, corrected: the decoupling loop
is capped, the deflation scan covers the bottom $k$ subdiagonal entries, the precision threshold
is recomputed for the corrected constants of the blocks, and the output is a Schur form. The
leaf is any small-block Schur solver meeting `NLAlib.Schur.RandomSchurLeafContract` (the Schur
form of [BanksGarzaVargasSrivastava2022, Definition 1.2]); the program is
`NLAlib.ShiftedQR.roundedShQRWith`, run with the parameter words of
`NLAlib.ShiftedQR.shqrParams` on a machine with unit roundoff at most
$\boldsymbol{u}_{\mathrm{ShQR}}$ (`NLAlib.ShiftedQR.uShQR`) and at most the replay term
(`NLAlib.ShiftedQR.uShQRSchurReplay`).

What is not claimed here: no Hessenberg reduction or preprocessing of a general matrix
(`NLAlib.Eigensolvers.Schur.Dense`); nothing on the leaf's own cost or precision; no forward
error for the eigenvalues; no rounded disk sampler; nothing for repeated eigenvalues. Modelling
assumption the paper does not make: the parameter words are exact reals.

## Main results

* `NLAlib.ShiftedQR.roundedShQRWith_measureReal_not_spectrum_le`,
  `NLAlib.ShiftedQR.roundedShQRWith_terminates`: the algorithm with a small-block Schur solver.
* `NLAlib.ShiftedQR.roundedShQRSchurWith_randomSchurCoreContract`,
  `NLAlib.ShiftedQR.roundedShQRSchurWith_terminatingSchurCore`: the same algorithm as the Schur
  core stage of the dense Schur pipeline.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix
namespace NLAlib.ShiftedQR

open Ops

section Routine

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has DiskSampleOp O] [Has CmpTst Q]
  [Has IdxTst Q]

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The hypotheses, with their long real constants, make elaboration heavy.
/-- **The rounded shifted QR algorithm with a Schur leaf, at an order up to $n + 1$**: with the
machine, the streams, the leaf and the parameters of
`NLAlib.ShiftedQR.roundedShQRWith_measureReal_not_spectrum_le` at the order $n + 1$, for an upper
Hessenberg $\mathbf{H}$ of order $n' + 1 \le n + 1$ in the class $(B, \Gamma)$ with
$\|\mathbf{H}\|_2 \le \Sigma$, except with probability $\varphi$ the run of
`NLAlib.ShiftedQR.roundedShQRWith L` at the order $n' + 1$ sets its flag to $0$ and stores an
upper triangular matrix and an accumulator tracked from $(\mathbf{U}, \mathbf{H})$ with the
backward error $\delta$ (`NLAlib.ShiftedQR.solveRoundedWith_pwrites` with the decoupler of
`NLAlib.ShiftedQR.roundedDecoupleWith_randomDecouplingRoutineContract_of_le_uShQR_at` and the
budget `NLAlib.ShiftedQR.shqrSchurError_le`). -/
theorem roundedShQRWith_pwrites_of_le {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    (hU : law sU = volume.restrict (Set.Icc 0 1)) {k : ℕ} {B Γ S δ φ : ℝ} (hB : 1 ≤ B)
    (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hk : k = shqrDegree (4 * B)) {εL βL φL : ℝ} {T RL : ℕ} {qs : List ℝ} {L : Stmt O Q}
    (hLeaf : Schur.RandomSchurLeafContract law εL βL φL (min k (n + 1)) (4 * S) qs T L I)
    (hqs : qs.length = 12) (hεL : 0 ≤ εL) (hεLR : εL ≤ (1 + 24 * u) ^ RL - 1) (hβL0 : 0 ≤ βL)
    (hβL : βL ≤ SmallEig.forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ))
    (hφL0 : 0 ≤ φL) (hφL : φL ≤ shqrSmallEigFailure n B Γ S δ φ)
    (hu : u ≤ uShQR n k B Γ S δ φ)
    (hur : u ≤ uShQRSchurReplay n k (shqrParams n k B Γ S δ φ ++ qs).length (shqrCap n B Γ S δ)
      RL B Γ S δ)
    {n' : ℕ} (hn' : n' ≤ n) {H V U : Matrix (Fin (n' + 1)) (Fin (n' + 1)) ℂ}
    {d : Fin (n' + 1) → ℂ} (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ B)
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hHS : specNorm H ≤ S) {a t p uo f : ℕ × ℕ} :
    PWrites law I (roundedShQRWith L)
      (Env.frame [n' + 1, k, (shqrParams n k B Γ S δ φ ++ qs).length, shqrCap n B Γ S δ, T,
        shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length), k * (n' + 1)]
        [a, t, p, uo, a, uo, f]) (shqrFp n' a uo f)
      (fun μ => μ.Live [a, t, p, uo, f] ∧
        μ.Room [a, t, p, uo, f] [2 * ((n' + 1) * (n' + 1)), 1,
          (shqrParams n k B Γ S δ φ ++ qs).length, 2 * ((n' + 1) * (n' + 1)), 1] ∧
        ShQRViewsApart (n' + 1) (shqrParams n k B Γ S δ φ ++ qs).length
          a t p uo f ∧
        HoldsMatrix a H μ.store ∧ HoldsMatrix uo U μ.store ∧
        μ.store.get t.1 t.2 = some (shqrDeflationThreshold n k B Γ S δ φ) ∧
        μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ ++ qs).length =
          some (shqrParams n k B Γ S δ φ ++ qs))
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ U' Tm : Matrix (Fin (n' + 1)) (Fin (n' + 1)) ℂ,
          HoldsMatrix a Tm μ'.store ∧ HoldsMatrix uo U' μ'.store ∧ Tm.IsUpperTriangular ∧
          IsTrackedUnitarySimilar ((1 + 24 * u) ^ (2 * (n' + 1) *
            (shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length) *
              (k * (n' + 1)) + 2 * k * (k + 2))) * (1 + εL) ^ (n' + 1) - 1) δ U H U' Tm) φ := by
  set ps := shqrParams n k B Γ S δ φ ++ qs with hps
  set F := shqrCap n B Γ S δ
  have hu0 := hM.roundoff_nonneg
  have hSp : 0 < S := hδ.trans_le hδS
  have hacc0 := shqrSmallEigAccuracy_pos (n := n) hB hΓ hδ hSp
  have haccS := shqrSmallEigAccuracy_le (n := n) hB hΓ hδ hδS
  obtain ⟨-, -, SR, IT⟩ := shqrParams_spec hB hΓ hδ hδS hφ hφ1 hk hu0 hu hacc0.le le_rfl
  have hu1 : u ≤ 1 / 100 := by
    have := (counts_of_le_uShQR hu0 hu).1
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hD : RandomDecouplingRoutineContract law (2 * B) (Γ / 2)
      (F * (φL + shqrRegularizeFailure n B Γ S δ φ / 2 + shqrSmallEigFailure n B Γ S δ φ)) k F
      T n' (2 * S) ps (F * (k + 1 + ps.length)) (k * (n' + 1)) (shqrDecoupled n k B Γ S δ φ)
      (fun _ => F * ((1 + shqrC k (4 * B)) * (4 * S) * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1)))
      (roundedDecoupleWith (schurDiag L)) I := by
    by_cases hkn : k ≤ n + 1
    · rw [min_eq_left hkn] at hLeaf
      exact roundedDecoupleWith_randomDecouplingRoutineContract_of_le_uShQR_at hI hloc hS hM hL
        hNat hC hQ hDisk hU hB hΓ hδ hδS hφ hφ1 hk hacc0.le le_rfl hφL0 hu
        (hLeaf.randomSmallEigContractAt_schurDiag hS hI hloc hqs hφL0 hacc0 haccS hβL)
        (Or.inr hqs) rfl le_rfl hn' (Nat.mul_le_mul_left _ (by omega))
    · intro n'' N w q f lg H' V' d' hk' hn''
      omega
  have hLeaf' : Schur.RandomSchurLeafContract law εL βL φL (min k (n' + 1)) (2 * S) ps T
      (leafOnTailWords L) I := fun B' hd hB' =>
    (hLeaf.onTailWords hqs (shqrParams n k B Γ S δ φ)) B'
      (hd.trans (min_le_min le_rfl (by omega))) (hB'.trans (by linarith))
  have hbud := shqrSchurError_le (n' := n') (ns := F * (k + 1 + ps.length)) (w := k * (n' + 1))
    (φ := φ) hB hΓ hδ hδS hk hu0 hu hur hεLR hβL0 hβL hn'
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega)))
  have hbδ := shqrBudget_le_left (n := n) (B := B) (Γ := Γ) (δ := δ)
  have hbΓ := shqrBudget_le_right (n := n) (B := B) (Γ := Γ) (δ := δ)
  have hE0 : 0 ≤ (F : ℝ) * ((1 + shqrC k (4 * B)) * (4 * S) *
      ((1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k - 1)) := by
    have := shqrC_pos k (by linarith : 0 < 4 * B)
    have : 1 ≤ (1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k :=
      one_le_pow₀ (le_add_of_nonneg_right (by positivity))
    have : 0 ≤ (1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k - 1 := by linarith
    positivity
  have hnn : ((n' : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hn'
  have hΓn : Γ / (16 * (n + 1) * B) ≤ Γ / (16 * (n' + 1) * B) := by gcongr
  have hφR : 0 ≤ shqrRegularizeFailure n B Γ S δ φ := by
    have := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
    unfold shqrRegularizeFailure; positivity
  have hφD : 0 ≤ F * (φL + shqrRegularizeFailure n B Γ S δ φ / 2 +
      shqrSmallEigFailure n B Γ S δ φ) := by
    have := shqrSmallEigFailure_pos (n := n) (B := B) (Γ := Γ) (S := S) (δ := δ) hφ
    positivity
  have hfail : 2 * ((n' : ℝ) + 1) * (F * (φL + shqrRegularizeFailure n B Γ S δ φ / 2 +
      shqrSmallEigFailure n B Γ S δ φ) + φL) ≤ φ :=
    le_trans (by gcongr) (IT.hfail φL hφL0 hφL)
  refine (solveRoundedWith_pwrites hS hM hu0 hu1 hL (hNat.mono (by omega)) hQ hC hI hloc _ hD _
    hLeaf' hφD hφL0 hεL hHess hV hHV hκ hΓ hgap SR.hfind SR.hcut SR.hc hβL0 hE0 (by linarith)
    (by linarith) (hbud.trans (hbΓ.trans hΓn))).mono (fun _ h => h) le_rfl ?_ hfail
  rintro μ' ⟨hf, U', Tm, hTm, hU', hT, htr⟩
  exact ⟨hf, U', Tm, hTm, hU', hT, htr.mono le_rfl (hbud.trans hbδ)⟩

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The headline's hypotheses, with their long real constants, make elaboration heavy.
/-- **The rounded shifted QR algorithm with a small-block Schur solver**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] with the quantifiers of Theorem 1.4, corrected,
with any small-block Schur solver in the place of `SmallEig`). Let the machine have the standard
model at $\boldsymbol{u}$, index literals, exact natural literals up to $n + 1$, exact `toNat` and
comparisons, a measurable interpretation reading the tape only in its windows, and a stream
$s_U$ uniform on $[0, 1]$ with an exact polar disk sampler on it. Let $\mathbf{H}$ be upper
Hessenberg of order $n + 1$, $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$
with $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 \le B$ and eigenvalues separated by $\Gamma > 0$,
$\|\mathbf{H}\|_2 \le \Sigma$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree of
(eqn:setk) at $4B$. Let the leaf `L` be a randomized small-block Schur solver on the orders at
most $\min(k, n + 1)$ and norms at most $4\Sigma$ with the cap $T$ and $12$ words `qs`: except
with probability $\varphi_L$ it stores an upper triangular $\mathbf{T}_b$ and an accumulator
$\mathbf{U}_b$ with $\|\mathbf{U}_b - \mathbf{V}_b\|_2 \le \varepsilon_L$ and $\mathbf{T}_b =
\mathbf{V}_b^{\mathsf H}(\mathbf{B} + \mathbf{F})\mathbf{V}_b$ for an exact unitary
$\mathbf{V}_b$ and $\|\mathbf{F}\|_2 \le \beta_L$, with $\beta_L, \varphi_L \ge 0$,
$0 \le \varepsilon_L \le (1 + 24\boldsymbol{u})^{R_L} - 1$ (a leaf of $R_L$ rotation-equivalents),
$\beta_L$ at most the backward accuracy $\Sigma'(\beta/(4(2k + 1)\Sigma'))^k$ of the forward
accuracy $\beta$ = `shqrSmallEigAccuracy` at $\Sigma' = 4\Sigma$ and
$\varphi_L \le$ `shqrSmallEigFailure`. Let
$\boldsymbol{u} \le \boldsymbol{u}_{\mathrm{ShQR}}$ and $\boldsymbol{u} \le$ the replay term
`NLAlib.ShiftedQR.uShQRSchurReplay` at $R_L$. Then
from a memory holding $\mathbf{H}$, an accumulator $\mathbf{U}_0$, the deflation threshold word
and the words of `shqrParams` followed by `qs`, under a random tape with the stream laws,
$$\mathbb{P}\bigl[\mathsf{roundedShQRWith}_L(\mathbf{H}) \text{ fails, or writes outside the
  matrix, the accumulator and the failure word, or lists no }
  \operatorname{spec}(\mathbf{H} + \mathbf{E}),\ \|\mathbf{E}\|_2 \le \delta\bigr] \le \varphi\,.$$
[BanksGarzaVargasSrivastava2022, Theorem 6.3]; there `SmallEig` is an oracle returning
eigenvalues.

Note: The leaf is a hypothesis, `NLAlib.Schur.RandomSchurLeafContract`: this is the algorithm
with a small-block Schur oracle. The diagonal of the leaf's triangular block serves as its Ritz
values (`NLAlib.ShiftedQR.schurDiag`), turned into forward accuracy by the matching
(`NLAlib.SmallEig.forwardBackwardError`). Instance: `SmallEig`
(`NLAlib.ShiftedQR.roundedShQRSmallEig_measureReal_not_spectrum_le`). The Schur form itself:
`NLAlib.ShiftedQR.roundedShQRSchurWith_randomSchurCoreContract`. -/
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
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hk : k = shqrDegree (4 * B)) {εL βL φL : ℝ} {T : ℕ}
    {qs : List ℝ} {L : Stmt O Q} {RL : ℕ}
    (hLeaf : Schur.RandomSchurLeafContract law εL βL φL (min k (n + 1)) (4 * S) qs T L I)
    (hqs : qs.length = 12) (hεL : 0 ≤ εL) (hεLR : εL ≤ (1 + 24 * u) ^ RL - 1) (hβL0 : 0 ≤ βL)
    (hβL : βL ≤ SmallEig.forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ))
    (hφL0 : 0 ≤ φL) (hφL : φL ≤ shqrSmallEigFailure n B Γ S δ φ)
    (hu : u ≤ uShQR n k B Γ S δ φ)
    (hur : u ≤ uShQRSchurReplay n k (shqrParams n k B Γ S δ φ ++ qs).length (shqrCap n B Γ S δ)
      RL B Γ S δ)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ} {U₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length,
        2 * ((n + 1) * (n + 1)), 1])
    (ha : ShQRViewsApart (n + 1) (shqrParams n k B Γ S δ φ ++ qs).length
          a t p out f)
    (hA : HoldsMatrix a H μ.store) (hU₀ : HoldsMatrix out U₀ μ.store)
    (ht : μ.store.get t.1 t.2 = some (shqrDeflationThreshold n k B Γ S δ φ))
    (hp : μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ ++ qs).length =
      some (shqrParams n k B Γ S δ φ ++ qs))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ξ : Ω → Tape ℝ} (hξ : IsTapeLaw law P ξ) :
    P.real {ω' | ¬ Writes .total I (ξ ω') (roundedShQRWith L)
      (Env.frame [n + 1, k, (shqrParams n k B Γ S δ φ ++ qs).length, shqrCap n B Γ S δ, T,
        shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length), k * (n + 1)]
        [a, t, p, out, a, out, f]) (shqrFp n a out f) (ShQRSpectrum a out f H δ) μ} ≤ φ := by
  have := hξ.isProbabilityMeasure
  have hB : 1 ≤ B := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
  have h := (roundedShQRWith_pwrites_of_le hS hM hL hNat hQ hC hI hloc hDisk hU hB hΓ hδ hδS hφ
    hφ1 hk hLeaf hqs hεL hεLR hβL0 hβL hφL0 hφL hu hur le_rfl hHess hV hHV hκ hgap hHS
    (U := U₀)).measureReal_not_writes_le ⟨hl, hr, ha, hA, hU₀, ht, hp⟩ hξ
  refine le_trans ?_ h
  refine measureReal_mono fun ω' hω' hW => hω' ?_
  refine hW.mono le_rfl fun μ' _ ⟨hf, U', Tm, hTm, hU', hT, htr⟩ => ?_
  obtain ⟨W, ⟨hW, E, hE, rfl⟩, -⟩ := htr
  exact ⟨hf, _, U', E, hTm, hU', hT, hE,
    (hW.isEigenvalueListing_of_isUpperTriangular_conjTranspose_mul_mul hT).charpoly_roots_eq_ofFn⟩

/-- **The rounded shifted QR algorithm with a completing small-block Schur solver terminates on
every tape**: on a scalar machine (no rounding model) with index literals, exact natural literals
up to $n + 1$, exact `toNat` and comparisons and an exact polar disk sampler, and a leaf `L` that
completes on orders at most $\min(k, n + 1)$ with the cap $T$ and $12$ words `qs`
(`NLAlib.ShiftedQR.CompletingLeafRoutine`, no accumulator bound), for any
$(n + 1) \times (n + 1)$ matrix $\mathbf{H}$, accumulator $\mathbf{U}_0$, any
$B, \Gamma, \Sigma, \delta, \varphi$ and $k$ the degree of (eqn:setk) at $4B$, the run of
`NLAlib.ShiftedQR.roundedShQRWith L` from a memory holding the input with the words
`NLAlib.ShiftedQR.shqrParams` followed by `qs` succeeds on every tape and writes only the matrix,
the accumulator and the failure word. -/
theorem roundedShQRWith_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {n : ℕ} (hS : IsScalar Mch I)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {k : ℕ}
    {B Γ S δ φ : ℝ} (hk : k = shqrDegree (4 * B)) {T : ℕ} {qs : List ℝ} {L : Stmt O Q}
    (hLeaf : CompletingLeafRoutine (min k (n + 1)) qs T L I) (hqs : qs.length = 12)
    {a t p out f : ℕ × ℕ} {μ : Mem ℝ}
    {U₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f]
      [2 * ((n + 1) * (n + 1)), 1, (shqrParams n k B Γ S δ φ ++ qs).length,
        2 * ((n + 1) * (n + 1)), 1])
    (ha : ShQRViewsApart (n + 1) (shqrParams n k B Γ S δ φ ++ qs).length
          a t p out f)
    (hA : HoldsMatrix a H μ.store) (hU₀ : HoldsMatrix out U₀ μ.store) {thr : ℝ}
    (ht : μ.store.get t.1 t.2 = some thr)
    (hp : μ.store.readBlock p.1 p.2 (shqrParams n k B Γ S δ φ ++ qs).length =
      some (shqrParams n k B Γ S δ φ ++ qs)) (τ : Tape ℝ) :
    Writes .total I τ (roundedShQRWith L)
      (Env.frame [n + 1, k, (shqrParams n k B Γ S δ φ ++ qs).length, shqrCap n B Γ S δ, T,
        shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length), k * (n + 1)]
        [a, t, p, out, a, out, f]) (shqrFp n a out f) (fun _ => True) μ := by
  have hkq : k = 2 ^ Nat.log 2 k := by rw [hk, shqrDegree, Nat.log_pow (by norm_num)]
  have hD : TerminatingDecouplerRoutine n k (shqrCap n B Γ S δ) T (shqrParams n k B Γ S δ φ ++ qs)
      (shqrCap n B Γ S δ * (k + 1 + (shqrParams n k B Γ S δ φ ++ qs).length)) (k * (n + 1))
      (roundedDecoupleWith (schurDiag L)) I := by
    by_cases hkn : k ≤ n + 1
    · rw [min_eq_left hkn] at hLeaf
      exact roundedDecoupleWith_terminatingDecouplerRoutine_at (F := shqrCap n B Γ S δ) hS hL
        hNat hC hQ hDisk hkq (shqrLoopThreshold n k B Γ S δ φ) (shqrRadius n B Γ S δ)
        (shqrScanThreshold n k B Γ S δ φ) 0.2 (4 * B) (shqrAlpha k (4 * B)) (shqrEps k (4 * B))
        (hLeaf.terminatingSmallEigAt_schurDiag hS hqs) (Or.inr hqs) rfl
        (Nat.mul_le_mul_left _ (by
          simp only [shqrParams, List.length_append, length_roundedDecoupleParams]; omega))
        (Nat.mul_le_mul_left _ (by omega))
    · intro n' w q f tape μ' H' hk' hn'
      omega
  exact (solveRoundedWith_completes hS hL hNat hQ hC _ hD _
    (hLeaf.onTailWords hqs _) (tape := τ) hl hr ha hA hU₀ ht hp).mono le_rfl fun _ _ _ => trivial

/-- **The rounded shifted QR algorithm with any small-block Schur solver is a Schur core**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] in Schur form, with a small-block Schur oracle).
Let the machine have the standard model at $\boldsymbol{u}$, index literals, exact natural
literals up to $n + 1$, exact `toNat` and comparisons, a measurable interpretation reading the
tape only in its windows, and a stream $s_U$ uniform on $[0, 1]$ with an exact polar disk sampler
on it. Let $B \ge 1$, $\Gamma > 0$, $0 < \delta \le \Sigma$, $0 < \varphi \le 1$ and $k$ the degree
of (eqn:setk) at $4B$. Let the leaf `L` be a randomized small-block Schur solver on the orders at
most $\min(k, n + 1)$ and norms at most $4\Sigma$ with the cap $T$ and $12$ words `qs`, with
accumulator error $0 \le \varepsilon_L \le (1 + 24\boldsymbol{u})^{R_L} - 1$, backward error $0 \le
\beta_L \le \Sigma'(\beta/(4(2k + 1)\Sigma'))^k$ ($\beta$ = `shqrSmallEigAccuracy`, $\Sigma' =
4\Sigma$) and failure $0 \le \varphi_L \le$ `shqrSmallEigFailure`; let $\boldsymbol{u} \le
\boldsymbol{u}_{\mathrm{ShQR}}$ and $\boldsymbol{u}$ at most the replay term at $R_L$. Then
`roundedShQRSchurWith L` meets the Schur core contract on the orders at most $n + 1$, the class $(B,
\Gamma)$ and norms at most $\Sigma$, with the words: the deflation threshold, `shqrParams`, `qs`.
Except with probability $\varphi$ its flag is $0$, its matrix upper triangular, and the pair is
tracked from $(\mathbf{U}, \mathbf{H})$ with the backward error $\delta$ and the relative
accumulator error $(1 + 24\boldsymbol{u})^{R} - 1$, $R$ = `NLAlib.ShiftedQR.shqrSchurRotations`
($2(n + 1)(n_s w + 2k(k + 2)) + (n + 1)R_L$).
[BanksGarzaVargasSrivastava2022, Theorem 6.3]; there only the eigenvalues are computed, with an
eigenvalue oracle.

Note: The leaf is a hypothesis (`NLAlib.Schur.RandomSchurLeafContract`): this is the core with a
small-block Schur oracle, the general form of
`NLAlib.ShiftedQR.roundedShQRSchur_randomSchurCoreContract` (the `SmallEig` leaf). The proof is
`NLAlib.ShiftedQR.solveRoundedWith_pwrites` with the decoupler of
`NLAlib.ShiftedQR.roundedDecoupleWith_randomDecouplingRoutineContract_at`
(`NLAlib.ShiftedQR.schurDiag` of the leaf as its eigenvalue routine); the replay term keeps the
replays, the products and the leaf accumulators within a quarter of the merged budget
(`NLAlib.ShiftedQR.shqrSchurError_le`).
Result: shifted-qr-rounded-schur-any-leaf -/
theorem roundedShQRSchurWith_randomSchurCoreContract {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ} {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {sU : ℕ} (hDisk : IsPolarDiskSampler sU I)
    (hU : law sU = volume.restrict (Set.Icc 0 1)) {k : ℕ} {B Γ S δ φ : ℝ} (hB : 1 ≤ B)
    (hΓ : 0 < Γ) (hδ : 0 < δ) (hδS : δ ≤ S) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hk : k = shqrDegree (4 * B)) {εL βL φL : ℝ} {T RL : ℕ} {qs : List ℝ} {L : Stmt O Q}
    (hLeaf : Schur.RandomSchurLeafContract law εL βL φL (min k (n + 1)) (4 * S) qs T L I)
    (hqs : qs.length = 12) (hεL : 0 ≤ εL) (hεLR : εL ≤ (1 + 24 * u) ^ RL - 1) (hβL0 : 0 ≤ βL)
    (hβL : βL ≤ SmallEig.forwardBackwardError k (4 * S) (shqrSmallEigAccuracy n B Γ S δ))
    (hφL0 : 0 ≤ φL) (hφL : φL ≤ shqrSmallEigFailure n B Γ S δ φ)
    (hu : u ≤ uShQR n k B Γ S δ φ)
    (hur : u ≤ uShQRSchurReplay n k (shqrParams n k B Γ S δ φ ++ qs).length (shqrCap n B Γ S δ)
      RL B Γ S δ) :
    Schur.RandomSchurCoreContract law
      ((1 + 24 * u) ^ shqrSchurRotations n k (shqrParams n k B Γ S δ φ ++ qs).length
        (shqrCap n B Γ S δ) RL - 1) δ φ (fun H => IsConditionedDiagonalizable B Γ H) k
      (shqrCap n B Γ S δ) T (n + 1) S
      (shqrDeflationThreshold n k B Γ S δ φ :: (shqrParams n k B Γ S δ φ ++ qs))
      (roundedShQRSchurWith L) I := by
  intro n' a p uo f H U hn hHess hHS ⟨V, d, hV, hHV, hκ, hgap⟩
  have hw := roundedShQRWith_pwrites_of_le (t := p) (p := (p.1, p.2 + 1)) (a := a) (uo := uo)
    (f := f) (U := U) hS hM hL hNat hQ hC hI hloc hDisk hU hB hΓ hδ hδS hφ hφ1 hk hLeaf hqs hεL
    hεLR hβL0 hβL hφL0 hφL hu hur (by omega : n' ≤ n) hHess hV hHV hκ hgap hHS
  set ps := shqrParams n k B Γ S δ φ ++ qs with hps
  set thr := shqrDeflationThreshold n k B Γ S δ φ
  have hu0 := hM.roundoff_nonneg
  unfold roundedShQRSchurWith
  refine (hw.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (fun μ h v hv => by
      have hl := h.1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with h | h | h | h | h | h | h <;> rw [h]
      exacts [hl a (by simp), hl _ (by simp), hl _ (by simp), hl uo (by simp), hl a (by simp),
        hl uo (by simp), hl f (by simp)])).mono ?_ le_rfl ?_ le_rfl
  · rintro μ ⟨hHU, hp, hl, hf, ha⟩
    have hp' : μ.store.readBlock p.1 (p.2 + 1) ps.length = some ps :=
      Store.readBlock_append_right (xs := [thr]) hp
    have ht : μ.store.get p.1 p.2 = some thr := by
      simpa using Store.get_of_readBlock hp (j := 0) (by simp) 0
    have hpl : p.2 + (1 + ps.length) ≤ μ.store.len p.1 := by
      simpa [Nat.add_comm 1] using Store.le_len_of_readBlock hp (by simp)
    simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, sup_bot_eq] at ha
    have hsub1 : Store.inBlock p.1 p.2 1 ≤ Store.inBlock p.1 p.2 (thr :: ps).length :=
      Fp.inBlock_le_inBlock le_rfl (by simp)
    have hsub2 : Store.inBlock p.1 (p.2 + 1) ps.length ≤
        Store.inBlock p.1 p.2 (thr :: ps).length :=
      Fp.inBlock_le_inBlock (by omega) (by simp; omega)
    refine ⟨fun v hv => ?_, ⟨Store.le_len_of_readBlock hHU.1 (by positivity), by omega,
      by dsimp only; omega, Store.le_len_of_readBlock hHU.2 (by positivity), hf, trivial⟩, ?_,
      hHU.1, hHU.2, ht, hp'⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with h | h | h | h | h <;> rw [h]
      exacts [hl a (by simp), hl p (by simp), hl p (by simp), hl uo (by simp), hl f (by simp)]
    · refine ShQRViewsApart.of_apart ?_
      simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, sup_bot_eq]
      exact ⟨⟨ha.1.1.mono le_rfl hsub1, ha.1.1.mono le_rfl hsub2, ha.1.2.1, ha.1.2.2⟩,
        ⟨Fp.disj_inBlock_of_le le_rfl, ha.2.1.1.mono hsub1 le_rfl, ha.2.1.2.mono hsub1 le_rfl⟩,
        ⟨ha.2.1.1.mono hsub2 le_rfl, ha.2.1.2.mono hsub2 le_rfl⟩, ha.2.2.1,
        fun _ _ _ h => h, trivial⟩
  rintro μ' ⟨hf, U', Tm, hTm, hU', hT, htr⟩
  refine ⟨hf, U', Tm, ⟨hTm, hU'⟩, hT, htr.mono ?_ le_rfl⟩
  have hX1 : (1 : ℝ) ≤ 1 + 24 * u := by linarith
  have hεL1 : 1 + εL ≤ (1 + 24 * u) ^ RL := by linarith
  have hY : (1 + εL) ^ (n' + 1) ≤ (1 + 24 * u) ^ (RL * (n' + 1)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by linarith) hεL1 _
  have hE : 2 * (n' + 1) * (shqrCap n B Γ S δ * (k + 1 + ps.length) * (k * (n' + 1)) +
      2 * k * (k + 2)) + RL * (n' + 1) ≤
      shqrSchurRotations n k ps.length (shqrCap n B Γ S δ) RL := by
    unfold shqrSchurRotations shqrSchurLogSize
    have h1 : n' + 1 ≤ n + 1 := by omega
    have := Nat.mul_le_mul_left (shqrCap n B Γ S δ * (k + 1 + ps.length))
      (Nat.mul_le_mul_left k h1)
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1)
      (Nat.add_le_add_right this (2 * k * (k + 2)))
    have := Nat.mul_le_mul_left RL h1
    nlinarith
  calc (1 + 24 * u) ^ (2 * (n' + 1) * (shqrCap n B Γ S δ * (k + 1 + ps.length) *
          (k * (n' + 1)) + 2 * k * (k + 2))) * (1 + εL) ^ (n' + 1) - 1
      ≤ (1 + 24 * u) ^ (2 * (n' + 1) * (shqrCap n B Γ S δ * (k + 1 + ps.length) *
          (k * (n' + 1)) + 2 * k * (k + 2))) * (1 + 24 * u) ^ (RL * (n' + 1)) - 1 := by
        gcongr
    _ ≤ _ := by rw [← pow_add]; gcongr

/-- **The Schur core with any terminating small-block Schur solver terminates on every tape**:
on a scalar machine with the standard model at $\boldsymbol{u} \le 1/100$, index literals, exact
natural literals up to $n + 1$, exact `toNat` and comparisons and an exact polar disk sampler, and
a leaf `L` that terminates on orders at most $\min(k, n + 1)$ with the cap $T$ and $12$ words
`qs`, its accumulator within $0 \le \varepsilon_L \le (1 + 24\boldsymbol{u})^{R_L} - 1$ of a
unitary, `roundedShQRSchurWith L` meets `NLAlib.Schur.TerminatingSchurCore` on the orders at most
$n + 1$ with the relative accumulator error $(1 + 24\boldsymbol{u})^R - 1$,
$R$ = `NLAlib.ShiftedQR.shqrSchurRotations` (`NLAlib.ShiftedQR.solveRoundedWith_terminates`). -/
theorem roundedShQRSchurWith_terminatingSchurCore {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    {n : ℕ} (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu1 : u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {sU : ℕ} (hDisk : IsPolarDiskSampler sU I) {k : ℕ} {B Γ S δ φ : ℝ}
    (hk : k = shqrDegree (4 * B)) {εL : ℝ} {T RL : ℕ} {qs : List ℝ} {L : Stmt O Q}
    (hLeaf : TerminatingLeafRoutine εL (min k (n + 1)) qs T L I) (hqs : qs.length = 12)
    (hεL : 0 ≤ εL) (hεLR : εL ≤ (1 + 24 * u) ^ RL - 1) :
    Schur.TerminatingSchurCore
      ((1 + 24 * u) ^ shqrSchurRotations n k (shqrParams n k B Γ S δ φ ++ qs).length
        (shqrCap n B Γ S δ) RL - 1) k (shqrCap n B Γ S δ) T (n + 1)
      (shqrDeflationThreshold n k B Γ S δ φ :: (shqrParams n k B Γ S δ φ ++ qs))
      (roundedShQRSchurWith L) I := by
  intro n' a p uo f tape μ H U hn hHU hp hl hf ha
  set ps := shqrParams n k B Γ S δ φ ++ qs with hps
  set thr := shqrDeflationThreshold n k B Γ S δ φ
  have hu0 : 0 ≤ u := (abs_nonneg _).trans (by simpa using hM.lit 1)
  have hkq : k = 2 ^ Nat.log 2 k := by rw [hk, shqrDegree, Nat.log_pow (by norm_num)]
  have hD : TerminatingDecouplerRoutine n' k (shqrCap n B Γ S δ) T ps
      (shqrCap n B Γ S δ * (k + 1 + ps.length)) (k * (n' + 1))
      (roundedDecoupleWith (schurDiag L)) I := by
    by_cases hkn : k ≤ n' + 1
    · exact roundedDecoupleWith_terminatingDecouplerRoutine_at (F := shqrCap n B Γ S δ) hS hL
        (hNat.mono (by omega)) hC hQ hDisk hkq (shqrLoopThreshold n k B Γ S δ φ)
        (shqrRadius n B Γ S δ) (shqrScanThreshold n k B Γ S δ φ) 0.2 (4 * B)
        (shqrAlpha k (4 * B)) (shqrEps k (4 * B))
        (CompletingLeafRoutine.terminatingSmallEigAt_schurDiag hS
          (CompletingLeafRoutine.mono_kmax hLeaf.completing (kmax' := k)
            (le_min le_rfl (by omega))) hqs)
        (Or.inr hqs) rfl
        (Nat.mul_le_mul_left _ (by
          simp only [hps, shqrParams, List.length_append, length_roundedDecoupleParams]; omega))
        (Nat.mul_le_mul_left _ (by omega))
    · intro n'' w q f tape μ' H' hk' hn''
      omega
  have hp' : μ.store.readBlock p.1 (p.2 + 1) ps.length = some ps :=
    Store.readBlock_append_right (xs := [thr]) hp
  have ht : μ.store.get p.1 p.2 = some thr := by
    simpa using Store.get_of_readBlock hp (j := 0) (by simp) 0
  have hpl : p.2 + (1 + ps.length) ≤ μ.store.len p.1 := by
    simpa [Nat.add_comm 1] using Store.le_len_of_readBlock hp (by simp)
  simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, sup_bot_eq] at ha
  have hsub1 : Store.inBlock p.1 p.2 1 ≤ Store.inBlock p.1 p.2 (thr :: ps).length :=
    Fp.inBlock_le_inBlock le_rfl (by simp)
  have hsub2 : Store.inBlock p.1 (p.2 + 1) ps.length ≤ Store.inBlock p.1 p.2 (thr :: ps).length :=
    Fp.inBlock_le_inBlock (by omega) (by simp; omega)
  have hw := solveRoundedWith_terminates (n := n') (D := roundedDecoupleWith (schurDiag L))
    (L := leafOnTailWords L) (F := shqrCap n B Γ S δ) (T := T) (tape := tape)
    (t := p) (p := (p.1, p.2 + 1)) hS hM hu1 hL (hNat.mono (by omega)) hQ hC hεL hD
    (TerminatingLeafRoutine.onTailWords
      (hLeaf.mono_kmax (kmax' := min k (n' + 1)) (min_le_min le_rfl (by omega))) hqs _)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with h | h | h | h | h <;> rw [h]
      exacts [hl a (by simp), hl p (by simp), hl p (by simp), hl uo (by simp), hl f (by simp)])
    ⟨Store.le_len_of_readBlock hHU.1 (by positivity), by omega, by dsimp only; omega,
      Store.le_len_of_readBlock hHU.2 (by positivity), hf, trivial⟩
    (ShQRViewsApart.of_apart (by
      simp only [Fp.Apart, Fp.blocks_cons, Fp.blocks_nil, Fp.disj_sup_right, sup_bot_eq]
      exact ⟨⟨ha.1.1.mono le_rfl hsub1, ha.1.1.mono le_rfl hsub2, ha.1.2.1, ha.1.2.2⟩,
        ⟨Fp.disj_inBlock_of_le le_rfl, ha.2.1.1.mono hsub1 le_rfl, ha.2.1.2.mono hsub1 le_rfl⟩,
        ⟨ha.2.1.1.mono hsub2 le_rfl, ha.2.1.2.mono hsub2 le_rfl⟩, ha.2.2.1,
        fun _ _ _ h => h, trivial⟩))
    hHU.1 hHU.2 ht hp'
  unfold roundedShQRSchurWith
  refine (hw.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with h | h | h | h | h | h | h <;> rw [h]
      exacts [hl a (by simp), hl p (by simp), hl p (by simp), hl uo (by simp), hl a (by simp),
        hl uo (by simp), hl f (by simp)])).mono le_rfl ?_
  rintro μ' - ⟨U', Tm, V, hTm, hU', hV, hb⟩
  refine ⟨U', Tm, V, ⟨hTm, hU'⟩, hV, hb.trans (mul_le_mul_of_nonneg_right ?_ (specNorm_nonneg _))⟩
  have hX1 : (1 : ℝ) ≤ 1 + 24 * u := by linarith
  have hY : (1 + εL) ^ (n' + 1) ≤ (1 + 24 * u) ^ (RL * (n' + 1)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hE : 2 * (n' + 1) * (shqrCap n B Γ S δ * (k + 1 + ps.length) * (k * (n' + 1)) +
      2 * k * (k + 2)) + RL * (n' + 1) ≤
      shqrSchurRotations n k ps.length (shqrCap n B Γ S δ) RL := by
    unfold shqrSchurRotations shqrSchurLogSize
    have h1 : n' + 1 ≤ n + 1 := by omega
    have := Nat.mul_le_mul_left (shqrCap n B Γ S δ * (k + 1 + ps.length)) (Nat.mul_le_mul_left k h1)
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1)
      (Nat.add_le_add_right this (2 * k * (k + 2)))
    have := Nat.mul_le_mul_left RL h1
    nlinarith
  calc (1 + 24 * u) ^ (2 * (n' + 1) * (shqrCap n B Γ S δ * (k + 1 + ps.length) * (k * (n' + 1)) +
          2 * k * (k + 2))) * (1 + εL) ^ (n' + 1) - 1
      ≤ (1 + 24 * u) ^ (2 * (n' + 1) * (shqrCap n B Γ S δ * (k + 1 + ps.length) *
          (k * (n' + 1)) + 2 * k * (k + 2))) * (1 + 24 * u) ^ (RL * (n' + 1)) - 1 := by
        gcongr
    _ ≤ _ := by rw [← pow_add]; gcongr

end Routine

end NLAlib.ShiftedQR
