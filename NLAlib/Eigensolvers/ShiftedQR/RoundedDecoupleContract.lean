/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedDecouple

/-!
# The rounded decoupling loop meets the randomized decoupling contract

The capped rounded decoupling loop of [BanksGarzaVargasSrivastava2022, Lemma 6.4] in floating point
(`NLAlib.ShiftedQR.roundedDecoupleWith`), with a small-eigenvalue routine that meets its randomized
contract, meets the randomized decoupling contract: from the loop's specification, opening the
slotted log, the iterations and the exit, it stores an upper Hessenberg perturbed unitary similarity
of the input, named by the unitary of its log, that is decoupled at the bottom, except with the sum
of the failure probabilities of its rounds.

## Main results

* `NLAlib.ShiftedQR.roundedDecouple_pwrites_of_loop`: the loop from its rounds.
* `NLAlib.ShiftedQR.roundedDecoupleWith_randomDecouplingRoutineContract_at`: the randomized
  decoupling contract.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix
namespace NLAlib.ShiftedQR

open Ops
variable {n : ℕ}

section Iteration

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has EigenvalueKernelOp O] in
/-- The decoupling loop from its rounds: the allocation of the scan registers and the two
index reads of $m$ and $n_0$ from the parameter words (`NLAlib.Ops.PWrites.allocs`,
`NLAlib.Ops.PWrites.bindIdx`) carry a probabilistic specification of
`NLAlib.ShiftedQR.roundedDecoupleLoopWith` at every fresh buffer to
`NLAlib.ShiftedQR.roundedDecoupleWith` from the precondition of
`NLAlib.ShiftedQR.RandomDecouplingRoutineContract`. -/
theorem roundedDecouple_pwrites_of_loop {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hQ : IsToNat id I) {law : ℕ → Measure ℝ}
    {k q F T : ℕ} {SE : Impl O Q} (hqk : q ≤ k)
    {w p f lg : ℕ × ℕ} {ns ws : ℕ} {ps qs : List ℝ} {tL R tv γ Bi α ε : ℝ}
    (hps : ps = roundedDecoupleParams tL R tv γ Bi α ε k q ++ qs)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e ωD φ : ℝ} (hφ : 0 ≤ φ)
    (hloop : ∀ L, lg.1 < L → (∀ b ∈ [w, p, f], b.1 ≠ lg.1) →
      PWrites law I (roundedDecoupleLoopWith SE).body
      (Env.frame [n + 1, k, ps.length, F, T, q, (excNet ε).length, ws]
        [w, p, (L, 0), w, f, lg])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock L 0 5 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))
      (fun μ => DecoupleLoopCtx n L w p f ps μ ∧ HoldsMatrix w H μ.store ∧
        HoldsSlottedLog lg ns ws [] [] μ.store)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ (Ls : List (Option (List GivensEntry))) (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
        Ls.length = ns ∧ (∀ x ∈ slotEntries ws Ls, x.1 + 1 < n + 1) ∧
        HoldsSlottedLog lg ns ws Ls [] μ'.store ∧
        IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries ws Ls)) H H' e ∧
            IsUpperHessenberg H' ∧
        (∃ j : Fin n, n ≤ (j : ℕ) + k ∧ ‖H' j.succ j.castSucc‖ ≤ ωD) ∧
        HoldsMatrix w H' μ'.store) φ) :
    PWrites law I (roundedDecoupleWith SE).body
      (Env.frame [n + 1, k, ps.length, F, T, ns, ws] [w, p, w, f, lg])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))
      (fun μ => μ.Live [lg] ∧ lg.2 + ns * (1 + 5 * ws) ≤ μ.store.len lg.1 ∧
        (∀ b ∈ [w, p, f], b.1 ≠ lg.1) ∧ HoldsMatrix w H μ.store ∧
            μ.store.readBlock p.1 p.2 ps.length = some ps ∧
        μ.Live [w, p, w, f] ∧ w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 ∧
        f.2 + 1 ≤ μ.store.len f.1 ∧
        Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1) ∧
        Fp.Disj (Store.inBlock p.1 p.2 ps.length)
          (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1))
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ (Ls : List (Option (List GivensEntry))) (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
        Ls.length = ns ∧ (∀ x ∈ slotEntries ws Ls, x.1 + 1 < n + 1) ∧
        HoldsSlottedLog lg ns ws Ls [] μ'.store ∧
        IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries ws Ls)) H H' e ∧
            IsUpperHessenberg H' ∧
        (∃ j : Fin n, n ≤ (j : ℕ) + k ∧ ‖H' j.succ j.castSucc‖ ≤ ωD) ∧
        HoldsMatrix w H' μ'.store) φ := by
  have hlen : ps.length = 10 + 2 * (excNet ε).length + qs.length := by
    rw [hps, List.length_append, length_roundedDecoupleParams]
  unfold roundedDecoupleWith
  refine PWrites.allocs (lens := [.const 5]) (ns := [5]) rfl
    (Pre₁ := fun L μ => DecoupleLoopCtx n L w p f ps μ ∧ HoldsMatrix w H μ.store ∧
      lg.1 < L ∧ (∀ b ∈ [w, p, f], b.1 ≠ lg.1) ∧ μ.Live [lg] ∧
      lg.2 + ns * (1 + 5 * ws) ≤ μ.store.len lg.1) ?_ ?_ fun L => ?_
  · rintro μ s₁ ⟨hlgl, hroom, hv, hW, hp, hl, hrw, hrf, hWF, hPWF⟩ hlen' hlens hBelow
    obtain ⟨h1, h2, h3, h4⟩ : w.1 < μ.store.length ∧ p.1 < μ.store.length ∧
        f.1 < μ.store.length ∧ lg.1 < μ.store.length :=
      ⟨hl w (by simp), hl p (by simp), hl f (by simp), hlgl lg (by simp)⟩
    simp only [List.length_cons, List.length_nil] at hlen'
    refine ⟨⟨h1, h2, h3, by simp [Mem.Live, hlen']; omega, hBelow.readBlock_of h2 hp,
      by rw [(hBelow w.1 h1).1]; exact hrw, by rw [(hBelow f.1 h3).1]; exact hrf,
      by simpa using (hlens 0 (by simp)).ge, hWF, hPWF⟩, hW.of_below hBelow h1, h4, hv,
      by simp [Mem.Live, hlen']; omega, by rw [(hBelow lg.1 h4).1]; exact hroom⟩
  · rintro μ ⟨hlgl, -, -, -, -, hl, -⟩ st st' pos hBelow ⟨hf0, Ls, H', h0, h1, h2, h3, h4, h5,
      hW'⟩
    exact ⟨hBelow.get_of (hl f (by simp)) hf0, Ls, H', h0, h1,
      h2.of_below hBelow (hlgl lg (by simp)), h3, h4, h5,
      hW'.of_below hBelow (hl w (by simp))⟩
  by_cases hLg : lg.1 < L ∧ ∀ b ∈ [w, p, f], b.1 ≠ lg.1
  swap
  · exact PWrites.of_writes hφ fun μ _ h => absurd ⟨h.2.2.1, h.2.2.2.1⟩ hLg
  obtain ⟨hlgL, hv⟩ := hLg
  have hget : ∀ μ, DecoupleLoopCtx n L w p f ps μ → ∀ j < 10,
      μ.store.get p.1 (p.2 + j) = some (ps.getD j 0) :=
    fun μ h j hj => Store.get_of_readBlock h.2.2.2.2.1 (by rw [hlen]; omega) 0
  have h8 : ∀ μ, DecoupleLoopCtx n L w p f ps μ →
      I.index (Has.inj IdxTst.toNat) [(p.1, p.2 + 8)] μ = some q := fun μ h =>
    hQ.index_eq_of_decode_nat (hget μ h 8 (by omega))
      (by
        subst hps
        rw [List.getD_append _ _ _ _ (by rw [length_roundedDecoupleParams]; omega)]
        rfl)
  have h9 : ∀ μ, DecoupleLoopCtx n L w p f ps μ →
      I.index (Has.inj IdxTst.toNat) [(p.1, p.2 + 9)] μ = some (excNet ε).length := fun μ h =>
    hQ.index_eq_of_decode_nat (hget μ h 9 (by omega))
      (by
        subst hps
        rw [List.getD_append _ _ _ _ (by rw [length_roundedDecoupleParams]; omega)]
        rfl)
  refine PWrites.bindIdx hI (a := [(p.1, p.2 + 8)]) rfl rfl
    (fun μ ⟨hctx, _⟩ => ⟨q, hqk, h8 μ hctx⟩) fun v hv' => ?_
  by_cases hvq : v = q
  swap
  · exact PWrites.of_writes hφ fun μ _ ⟨⟨hctx, _⟩, hv''⟩ =>
      (hvq (Option.some.inj (hv''.symm.trans (h8 μ hctx)))).elim
  subst v
  refine PWrites.bindIdx hI (a := [(p.1, p.2 + 9)]) rfl rfl
    (fun μ ⟨⟨hctx, _⟩, _⟩ => ⟨(excNet ε).length, by rw [hlen]; omega, h9 μ hctx⟩)
    fun v hv' => ?_
  by_cases hvq : v = (excNet ε).length
  swap
  · exact PWrites.of_writes hφ fun μ _ ⟨⟨⟨hctx, _⟩, _⟩, hv''⟩ =>
      (hvq (Option.some.inj (hv''.symm.trans (h9 μ hctx)))).elim
  subst hvq
  have hRL : Store.inBlock L 0 5 ≤ Fp.above L := fun b i h => (show L ≤ b from h.1 ▸ le_rfl)
  have hwl : w.1 ≠ lg.1 := hv w (by simp)
  have hpl : p.1 ≠ lg.1 := hv p (by simp)
  have hfl : f.1 ≠ lg.1 := hv f (by simp)
  refine (PWrites.seq (φ₁ := 0) hI hloc hφ ?_ (((hloop L hlgL hv).mono
    (Pre' := fun μ => (DecoupleLoopCtx n L w p f ps μ ∧ HoldsMatrix w H μ.store ∧
      HoldsSlottedLog lg ns ws [] [] μ.store) ∧ μ.Live [lg]) (fun μ h => h.1) le_rfl
    (fun _ h => h) le_rfl).in_frame rfl rfl fun μ h => by
      have h1 := h.1.1.2.2.2.1
      have h2 := h.2
      simp only [Mem.live_cons, Mem.live_nil, and_true] at h1 h2 ⊢
      tauto)).mono (fun μ h => h)
    (sup_le (le_sup_right.trans le_sup_left) (sup_le (sup_le
      (le_sup_left.trans le_sup_left) (hRL.trans le_sup_right))
      (le_sup_right.trans le_sup_left))) (fun _ h => h) (by simp)
  refine PWrites.of_writes le_rfl fun μ τ h => ?_
  obtain ⟨⟨⟨hctx, hW, -, -, hlgl, hroom⟩, -⟩, -⟩ := h
  refine ((slottedLogOpen_writes (τ := τ) (μ := μ) (ns := ns) (w := ws) (lg := lg) hS hM
    hroom).in_frame rfl rfl hlgl).mono le_rfl ?_
  rintro μ' hfr ⟨-, hlog⟩
  exact ⟨⟨hctx.of_eqOff_log hpl (le_sup_right) hfr,
    hW.of_eqOff hfr (Fp.disj_inBlock_of_ne (Ne.symm hwl)), hlog⟩, hlgl.congr hfr.length_eq⟩
-- The loop's program term and the hypotheses of the iteration make elaboration heavy.
set_option maxHeartbeats 4000000 in
-- (heavy elaboration, see above)
omit [Has EigenvalueKernelOp O] in
/-- **The rounded decoupling loop with a small-eigenvalue routine meets the randomized decoupling
contract**, with the parameter words `NLAlib.ShiftedQR.roundedDecoupleParams` followed by the
routine's words `qs` (none, or $12$) and the routine meeting
`NLAlib.ShiftedQR.RandomSmallEigContractAt` with the word count $12$. The rounded decoupling loop
meets the randomized decoupling contract ([BanksGarzaVargasSrivastava2022, Lemma 6.4] in floating
point, corrected): on a machine with the standard model at $\boldsymbol{u} < 1$, exact natural
literals up to $n_{\max} + 1$, a measurable interpretation reading the tape only in its windows, a
`SmallEig` kernel and an exact polar disk sampler, `NLAlib.ShiftedQR.roundedDecoupleWith` with the
parameter words `NLAlib.ShiftedQR.roundedDecoupleParams` meets
`NLAlib.ShiftedQR.RandomDecouplingContract` on the class (condition $2B$, separation $g/2$) for
orders up to $n_c + 1$ and norms up to $N_{\max}$, for any $n_c \le n_{\max}$ and a log width $w \ge
kn_c$, with failure probability $F(\varphi_{\mathrm{se}} + \varphi_R/2 + \varphi)$, the level
$\omega_D$ and the backward error $FE$, $E = (1 + C)S((1 + 300(n_{\max}+1)^2\boldsymbol{u})^k - 1)$.
The hypotheses are those of `NLAlib.ShiftedQR.shIteration_pwrites` at the order $n_{\max} + 1$, the
class constant $B_i \ge 4B$ and the iterate norm $S$, and the loop's: the scan thresholds $(1 +
\boldsymbol{u})^2 t \le (1 - \boldsymbol{u})^2 t_L \le (1 - \boldsymbol{u})^4\omega_D^2$, the cap
$(1 + \boldsymbol{u})^2((1.002(1 - \gamma))^F N_{\max})^2 \le t_L$, the iterate norms $N_{\max} + FE
\le S$ and the class preservation $FE \le (g/2)/(16(n_{\max} + 1) \cdot 2B)$. Each round is one
iteration (`NLAlib.ShiftedQR.shIteration_pwrites`) and a scan; the iterates stay in the class
(condition $4B$, separation $g/4$,
`NLAlib.IsPerturbedUnitarySimilar.exists_pseudoConditionNumber_le_and_le_norm_sub`); a coupled
matrix had its potential contracted, so after $F$ rounds the scan passes
(`NLAlib.exists_norm_subdiag_le_hessenbergPotential`), and the failures of the rounds add
(`NLAlib.Ops.PWrites.whileFuel`). -/
theorem roundedDecoupleWith_randomDecouplingRoutineContract_at {M : Machine ℝ} {I : Interp O Q ℝ}
    {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u < 1) (hL : IsIndexLit M I) {nmax : ℕ}
    (hNat : IsExactNatLit id M (nmax + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} {β φse : ℝ}
    (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse) (hDisk : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k q F : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    {B g Bi Nmax S ω ωD tL tv R φR α γ φ C ε : ℝ} (hg : 0 < g) (hBi : 4 * B ≤ Bi)
    (hS0 : 0 ≤ S) (hBk : Bi ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hgapS : 2 * ω ^ 2 / S ≤ g / 4)
    (hR : 0 < R) (hφR : 0 < φR) (hφR1 : φR ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φR / (2 * k))) (hnu : (nmax + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((nmax + 1 : ℕ) : ℝ) * √((nmax + 1 : ℕ) : ℝ) * u) *
      ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((nmax + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxuR : 300 * (nmax + 1) ^ 2 * u ≤
      (16 * Bi)⁻¹ * (R * √(φR / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hboundR : (66 + 2 * 1.1) * Bi * S * ((2 + 2 * 1.1) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(nmax + 1) * (300 * (nmax + 1) ^ 2 * u) ≤ ω / 2)
    (hα : α = (1.01 * Bi) ^ ((4 * q : ℝ) / 2 ^ q)) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * Bi ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ 2)) ^
        ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2) (hφ : 0 < φ) (hφ1 : φ ≤ 1 / 5)
    (hd : R * √(φR / (2 * k)) / 2 ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((nmax + 1 : ℕ) : ℝ))) / 4)
    (hC1 : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹)) ≤ C)
    (hxu : 300 * (nmax + 1) ^ 2 * u ≤
      (8004 * Bi)⁻¹ * (R * √(φR / (2 * k)) / 2 / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * Bi * S * ((2 + 2 * C) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(nmax + 1) * (300 * (nmax + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hexc1 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * S)) ≤ 0.005 * ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * ω))
    (hexc2 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * S)) ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((nmax + 1 : ℕ) : ℝ))) / 8)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) (hthr : (1 + u) ^ 2 * tv ≤ (1 - u) ^ 2 * tL)
    (hcut : tL ≤ (1 - u) ^ 2 * ωD ^ 2) (hωD : 0 ≤ ωD)
    (hfuel : (1 + u) ^ 2 * ((1.002 * (1 - γ)) ^ F * Nmax) ^ 2 ≤ tL)
    (hSN : Nmax + F * ((1 + C) * S * ((1 + 300 * (nmax + 1) ^ 2 * u) ^ k - 1)) ≤ S)
    (hsmall : F * ((1 + C) * S * ((1 + 300 * (nmax + 1) ^ 2 * u) ^ k - 1)) ≤
      g / 2 / (16 * (nmax + 1) * (2 * B))) {T : ℕ} {qs : List ℝ} {SE : Impl O Q}
    (hSE : RandomSmallEigContractAt law β φse k 12 T S qs SE I)
    (hq12 : qs = [] ∨ qs.length = 12) {ps : List ℝ}
    (hps : ps = roundedDecoupleParams tL R tv γ Bi α ε k q ++ qs) {ns ws : ℕ}
    (hns : F * (k + 1 + (excNet ε).length) ≤ ns) {nc : ℕ} (hnc : nc ≤ nmax)
    (hws : k * nc ≤ ws) :
    RandomDecouplingRoutineContract law (2 * B) (g / 2) (F * (φse + φR / 2 + φ)) k F T nc Nmax
      ps ns ws ωD
      (fun _ => F * ((1 + C) * S * ((1 + 300 * (nmax + 1) ^ 2 * u) ^ k - 1)))
      (roundedDecoupleWith SE) I := by
  intro n N w p f lg H V d hkn hn hN hHess hnorm hV hHV hκ hgap
  have hws' : k * n ≤ ws := (Nat.mul_le_mul_left k hn).trans hws; replace hn := hn.trans hnc
  have hu := hM.roundoff_nonneg
  set E := (1 + C) * S * ((1 + 300 * (nmax + 1) ^ 2 * u) ^ k - 1) with hEdef
  have hnn : (n : ℝ) + 1 ≤ nmax + 1 := by exact_mod_cast Nat.succ_le_succ hn
  have hnn' : ((n + 1 : ℕ) : ℝ) ≤ ((nmax + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hn
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hB0 : 1 / 2 ≤ B := by
    have := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
    linarith
  have hBi0 : 0 ≤ Bi := by linarith
  have hα0 : 0 ≤ α := hα ▸ Real.rpow_nonneg (by positivity) _
  have hε0 : 0 ≤ ε := hε ▸ Real.rpow_nonneg (div_nonneg (by nlinarith) (by positivity)) _
  have hC0 : 0 ≤ C := by
    have : 0 ≤ 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
        (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
          Bi ^ ((k : ℝ)⁻¹)) := by positivity
    linarith
  have hx : 300 * ((n : ℝ) + 1) ^ 2 * u ≤ 300 * (nmax + 1) ^ 2 * u := by gcongr
  have hE0 : 0 ≤ E := by
    have : 1 ≤ (1 + 300 * ((nmax : ℝ) + 1) ^ 2 * u) ^ k := one_le_pow₀ (by nlinarith)
    have : 0 ≤ (1 + 300 * ((nmax : ℝ) + 1) ^ 2 * u) ^ k - 1 := by linarith
    positivity
  have hEn : (1 + C) * S * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1) ≤ E := by
    rw [hEdef]; gcongr
  have hgB : g / 2 / (16 * (nmax + 1) * (2 * B)) ≤ g / 2 / (16 * (n + 1) * (2 * B)) := by gcongr
  have hc0 : 0 ≤ 1.002 * (1 - γ) := by nlinarith
  have htv0 : 0 ≤ tv := le_trans (by positivity) hthrω
  have hp1 : 0 < (1 - u) ^ 2 := by nlinarith
  have htL0 : 0 ≤ tL := le_of_mul_le_mul_left
    (by nlinarith [mul_nonneg (sq_nonneg (1 + u)) htv0] : (1 - u) ^ 2 * 0 ≤ (1 - u) ^ 2 * tL) hp1
  have htL : tv ≤ tL := by
    have h1 : tv ≤ (1 + u) ^ 2 * tv := le_mul_of_one_le_left htv0 (by nlinarith)
    have h2 : (1 - u) ^ 2 * tL ≤ tL := mul_le_of_le_one_left htL0 (by nlinarith)
    linarith
  have hωL : (1 + u) ^ 2 * ω ^ 2 ≤ tL := hthrω.trans htL
  -- the iteration's hypotheses at the order `n + 1`
  have hNat' : IsExactNatLit id M (n + 1) := hNat.mono (by omega)
  have hnu' : (n + 1 : ℝ) * u ≤ 1 / 2500 := le_trans (by gcongr) hnu
  have huo' : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) *
      ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k :=
    le_trans (by gcongr) huo
  have huo1' : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1 :=
    le_trans (by gcongr) huo1
  have hxuR' := hx.trans hxuR
  have hxu' := hx.trans hxu
  have hboundR' : (66 + 2 * 1.1) * Bi * S * ((2 + 2 * 1.1) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2 := le_trans (by gcongr) hboundR
  have hbound' : (66 + 2 * C) * Bi * S * ((2 + 2 * C) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω := le_trans (by gcongr) hbound
  have hd' : R * √(φR / (2 * k)) / 2 ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4 := hd.trans (by gcongr)
  have hexc2' : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * S)) ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8 := hexc2.trans (by gcongr)
  have hlen : ps.length = 10 + 2 * (excNet ε).length + qs.length := by
    rw [hps, List.length_append, length_roundedDecoupleParams]
  have hψH : hessenbergPotential k H ≤ Nmax :=
    ((hessenbergPotential_le_specNorm (by omega) hkn H).trans hnorm).trans hN
  have hiE : ∀ i < F, (i : ℝ) * E ≤ F * E := fun i hi =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) hE0
  refine (roundedDecouple_pwrites_of_loop (lg := lg) (ns := ns) (ws := ws) hI hloc hS hM hQ
    (by rw [hkq]; exact Nat.lt_two_pow_self.le) hps (by positivity) fun L hlgL hlgv => ?_).mono
    (fun μ ⟨hW, hp, hl, hv, hrw, hrf, hrl, hap, hpd⟩ => ?_) le_rfl
    (fun _ ⟨a, Ls, H', h⟩ => ⟨a, H', Ls, h⟩) le_rfl
  · exact roundedDecoupleLoop_pwrites hI hloc hS hM hu1 hL hNat' hC (by omega) hkn
      (by rw [hps]; rfl) (by rw [hlen]; omega) hHess hψH hthr hcut hωD hc0 hE0 (by positivity)
      hfuel hns hlgv hlgL fun i hi =>
      roundedDecoupleIteration_pwrites (L := L) (i := i) (p := p) hI hloc hS hM hu1 hL hNat' hC
        hQ hβ0 hφse hDisk hU hkq hk hkn hV hHV hκ hg hgap ((hiE i hi).trans (hsmall.trans hgB))
        (by linarith [hiE i hi]) hEn hps hBi hBk hω hωL hgapS hR hφR hφR1 hβ hdη hnu' huo' huo1'
        hxuR' hboundR' hα hγ hγ1 hε hε2 hφ hφ1 hd' hC1 hxu' hbound' hexc1 hexc2' hthrω
        ((Nat.mul_le_mul_right _ hi).trans hns) hws' hlgv hSE hq12
  · simp only [Fp.Apart, Fp.blocks_cons, Fp.disj_sup_right] at hap
    refine ⟨hl.mono (by simp), hrl, hv, hW, hp, hl.mono (by simp), hrw, hrf, hap.1.1,
      hpd.mono le_rfl le_sup_left⟩

end Iteration

end NLAlib.ShiftedQR
