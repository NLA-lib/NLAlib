/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedHeadline
public import NLAlibScaffold.Eigensolvers.ShiftedQR.RoundedIteration

/-!
# The rounded decoupling loop with randomized iterations
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

def roundedDecouple : Impl O Q :=
  opsImpl% [N, k, np, F] (W, P) → (W, Fl) {
    let R ← alloc 5;
    let m ← index (Has.inj IdxTst.toNat) (P[8]) ≤ k;
    let n0 ← index (Has.inj IdxTst.toNat) (P[9]) ≤ np;
    run (bottomScan (O := O) (Q := Q)).body [N, k] (W, P, R);
    while j < F, (Has.inj CmpTst.isZero) [] (R[3]) {
      run (shIteration (O := O) (Q := Q)).body [N, m, k, n0]
        (W, P[1], P[2], P[3], P[4], P[5], P[6], P[7], P[10], W, Fl);
      run (bottomScan (O := O) (Q := Q)).body [N, k] (W, P, R)
    } then {
      if (Has.inj CmpTst.isPos) [] (R[3]) {
        call (Has.inj IndexOp.lit) [0] () → (Fl)
      } else {
        call (Has.inj IndexOp.lit) [1] () → (Fl)
      }
    }
  }

end Program

/-- **The parameter words of the decoupling loop**: the loop's scan threshold $t_L$, then the
words of `NLAlib.ShiftedQR.shIteration` (the radius $R$ and the `Optimal` word of `Regularize`, the
iteration's threshold $t$, the words of `Sh` and its net) with the class constant $B$,
$\theta = 1.01 \cdot 0.998^{-1/k}(2B^4)^{1/(2k)}$, the exceptional spacing $\varepsilon$, and the
two index words $m$ ($k = 2^m$) and the net size $n_0$; the net follows at offset $10$. -/
noncomputable def roundedDecoupleParams (tL R tv γ B α ε : ℝ) (k q : ℕ) : List ℝ :=
  [tL, R, 0.999 * (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ k, tv,
    (1 - γ) ^ k, (2 : ℝ) ^ ((k : ℝ)⁻¹) *
      ((1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * B ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α * B ^ ((k : ℝ)⁻¹)),
    ε / 2, 1.0015 * (1 - γ), (q : ℝ), ((excNet ε).length : ℝ)] ++
    (excNet ε).flatMap fun z => [z.re, z.im]

theorem length_roundedDecoupleParams (tL R tv γ B α ε : ℝ) (k q : ℕ) :
    (roundedDecoupleParams tL R tv γ B α ε k q).length = 10 + 2 * (excNet ε).length := by
  simp [roundedDecoupleParams, List.length_flatMap]
  omega

/-- The operands of the decoupling loop at the order $n + 1$ with the scan registers at the
fresh buffer $L$: the matrix, the parameter words and the flag lie below $L$, are live and have
room, the parameter words are stored, and the matrix, the flag and the parameter words are apart.
-/
def DecoupleLoopCtx (n L : ℕ) (w q f : ℕ × ℕ) (ps : List ℝ) (μ : Mem ℝ) : Prop :=
  w.1 < L ∧ q.1 < L ∧ f.1 < L ∧ μ.Live [w, q, (L, 0), f] ∧
    μ.store.readBlock q.1 q.2 ps.length = some ps ∧
    w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 ∧ f.2 + 1 ≤ μ.store.len f.1 ∧
    5 ≤ μ.store.len L ∧
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1) ∧
    Fp.Disj (Store.inBlock q.1 q.2 ps.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)

/-- The operands of the decoupling loop survive the writes of a round (the matrix, the flag and
the scan registers). -/
theorem DecoupleLoopCtx.of_eqOff {n L : ℕ} {w q f : ℕ × ℕ} {ps : List ℝ} {μ μ' : Mem ℝ}
    (h : DecoupleLoopCtx n L w q f ps μ) {F : Fp}
    (hF : F ≤ Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
      Store.inBlock L 0 5) (hfr : μ.store.EqOff F μ'.store) :
    DecoupleLoopCtx n L w q f ps μ' := by
  obtain ⟨hw, hq, hf, hl, hp, hrw, hrf, hrL, hWF, hPWF⟩ := h
  have hQR : Fp.Disj (Store.inBlock q.1 q.2 ps.length) (Store.inBlock L 0 5) :=
    Fp.disj_inBlock_of_ne (by omega)
  refine ⟨hw, hq, hf, hl.congr hfr.length_eq,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _)
      ((Fp.disj_sup_right.mpr ⟨hPWF, hQR⟩).symm.mono hF le_rfl) hp,
    by rw [hfr.len_eq]; exact hrw, by rw [hfr.len_eq]; exact hrf,
    by rw [hfr.len_eq]; exact hrL, hWF, hPWF⟩

variable {n : ℕ}

/-- **The state of the decoupling loop after an iteration**, before its scan: `w` holds an upper
Hessenberg perturbed unitary similarity $\mathbf{H}'$ of $\mathbf{H}$ with error $iE$ that is
decoupled at the bottom in the iteration's scan form ($(1 - \boldsymbol{u})^2\lvert h\rvert^2
\le t$) or has $\psi_k(\mathbf{H}') \le c^i\psi_k(\mathbf{H})$. -/
def DecoupleLoopMid (u : ℝ) (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (tv c E : ℝ)
    (w : ℕ × ℕ) (i : ℕ) (μ : Mem ℝ) : Prop :=
  ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsPerturbedUnitarySimilar H H' (i * E) ∧
    IsUpperHessenberg H' ∧ HoldsMatrix w H' μ.store ∧
    ((∃ j : Fin n, n ≤ (j : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' j.succ j.castSucc‖ ^ 2 ≤ tv) ∨
      hessenbergPotential k H' ≤ c ^ i * hessenbergPotential k H)

/-- **The state of the decoupling loop before round $i$**: `w` holds an upper Hessenberg
perturbed unitary similarity $\mathbf{H}'$ of $\mathbf{H}$ with error $iE$, and the scan flag in
the registers `r` is $1$ with a bottom subdiagonal entry that passed the loop's test
($(1 - \boldsymbol{u})^2\lvert h\rvert^2 \le t_L$), or $0$ with every bottom entry failing it
($t_L < (1 + \boldsymbol{u})^2\lvert h\rvert^2$) and $\psi_k(\mathbf{H}') \le
c^i\psi_k(\mathbf{H})$. -/
def DecoupleLoopState (u : ℝ) (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (tL c E : ℝ)
    (w r : ℕ × ℕ) (i : ℕ) (μ : Mem ℝ) : Prop :=
  ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsPerturbedUnitarySimilar H H' (i * E) ∧
    IsUpperHessenberg H' ∧ HoldsMatrix w H' μ.store ∧
    ((μ.store.get r.1 (r.2 + 3) = some 1 ∧ ∃ j : Fin n, n ≤ (j : ℕ) + k ∧
        (1 - u) ^ 2 * ‖H' j.succ j.castSucc‖ ^ 2 ≤ tL) ∨
      (μ.store.get r.1 (r.2 + 3) = some 0 ∧
        (∀ j : Fin n, n ≤ (j : ℕ) + k → tL < (1 + u) ^ 2 * ‖H' j.succ j.castSucc‖ ^ 2) ∧
        hessenbergPotential k H' ≤ c ^ i * hessenbergPotential k H))

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has IdxTst Q] in
/-- **The scan of the decoupling loop**: from the state after an iteration, the rounded bottom
scan with the loop's threshold $t_L$ (the first parameter word) reaches the state before the
next round. An entry that passed the iteration's test,
$(1 - \boldsymbol{u})^2\lvert h\rvert^2 \le t$, passes the loop's when
$(1 + \boldsymbol{u})^2 t \le (1 - \boldsymbol{u})^2 t_L$, so a matrix the scan finds coupled has
had its potential contracted. -/
theorem roundedDecoupleScan_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u < 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {μ : Mem ℝ} {k L : ℕ}
    (hk : k ≤ n) {w q f : ℕ × ℕ} {ps : List ℝ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {tL tv c E : ℝ} {i : ℕ} (hps : ps.getD 0 0 = tL) (hps0 : 0 < ps.length)
    (hthr : (1 + u) ^ 2 * tv ≤ (1 - u) ^ 2 * tL) (hctx : DecoupleLoopCtx n L w q f ps μ)
    (hmid : DecoupleLoopMid u k H tv c E w i μ) :
    Writes .total I τ (bottomScan (O := O) (Q := Q)).body (Env.frame [n + 1, k] [w, q, (L, 0)])
      (Store.inBlock L 0 5)
      (fun μ' => DecoupleLoopCtx n L w q f ps μ' ∧ DecoupleLoopState u k H tL c E w (L, 0) i μ')
      μ := by
  have hu := hM.roundoff_nonneg
  obtain ⟨hw, hq, hf, hl, hp, hrw, hrf, hrL, hWF, hPWF⟩ := id hctx
  obtain ⟨H', hHH', hHess', hW, hdec⟩ := hmid
  have hRW : Fp.Disj (Store.inBlock (L, 0).1 (L, 0).2 5)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) := Fp.disj_inBlock_of_ne (by simp; omega)
  have hRT : Fp.Disj (Store.inBlock (L, 0).1 (L, 0).2 5) (Store.inBlock q.1 q.2 1) :=
    Fp.disj_inBlock_of_ne (by simp; omega)
  have ht : μ.store.get q.1 q.2 = some tL := by
    have h := Store.get_of_readBlock hp hps0 0
    rwa [Nat.add_zero, hps] at h
  refine (bottomScan_writes (τ := τ) hS hM hu hu1.le hL hNat hC hk hW ht
    (hl.mono (by simp)) (by simpa using hrL) hRW hRT).mono le_rfl ?_
  rintro μ' hfr ⟨-, hscan⟩
  refine ⟨hctx.of_eqOff (by simp) hfr, H', hHH', hHess', hW.of_eqOff hfr hRW, ?_⟩
  rcases hscan with ⟨h1, j, hj, -, hjt⟩ | ⟨h0, hall⟩
  · exact Or.inl ⟨by simpa using h1, j, hj, hjt⟩
  · refine Or.inr ⟨by simpa using h0, hall, ?_⟩
    rcases hdec with ⟨j, hj, hjt⟩ | hψ
    · exfalso
      have h1 := hall j hj
      have hu0 : 0 < (1 - u) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (1 + u), mul_le_mul_of_nonneg_left hjt (sq_nonneg (1 + u)),
        mul_lt_mul_of_pos_left h1 hu0]
    · exact hψ

/-- An outcome of an iteration is in the measurable form of
`NLAlib.ShiftedQR.measurableSet_iterationOutcome` with any larger error. -/
theorem mem_iterationOutcome_of_shIterationOutcome {u : ℝ} {k : ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {γ tv ε E : ℝ} {a : ℕ × ℕ} {F : Fp}
    {m m' : Mem ℝ} (hH : HoldsMatrix a H m.store) (hfr : m.store.EqOff F m'.store)
    (h : ShIterationOutcome u k H γ tv ε a m') (hE : ε ≤ E) :
    m.store.EqOff F m'.store ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (m'.store.get a.1 (a.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilar (storedMatrix a (n + 1) (n + 1) m.store)
        (storedMatrix a (n + 1) (n + 1) m'.store) E ∧
      IsUpperHessenberg (storedMatrix a (n + 1) (n + 1) m'.store) ∧
      ((∃ i : Fin n, n ≤ (i : ℕ) + k ∧
          (1 - u) ^ 2 * ‖storedMatrix a (n + 1) (n + 1) m'.store i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
        hessenbergPotential k (storedMatrix a (n + 1) (n + 1) m'.store) ≤
          1.002 * (1 - γ) * hessenbergPotential k (storedMatrix a (n + 1) (n + 1) m.store)) := by
  obtain ⟨H', hsim, hHess, hA, hdec⟩ := h
  rw [← hH.eq_storedMatrix, ← hA.eq_storedMatrix]
  exact ⟨hfr, fun j hj => by rw [Store.get_of_readBlock hA hj 0]; rfl, hsim.mono hE, hHess, hdec⟩

end Theorems

section Iteration

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

set_option maxHeartbeats 1000000 in
/-- **One iteration of the decoupling loop on the good tapes**: from the state before round $i$
with the scan flag $0$, the iterate is in the class of `NLAlib.ShiftedQR.shIteration_pwrites`
(condition at most $4B \le B_i$ and separation at least $g/4 \ge 2\omega^2/S$ by
`NLAlib.IsPerturbedUnitarySimilar.exists_pseudoConditionNumber_le_and_le_norm_sub`, norm at most
$\|\mathbf{H}\|_2 + iE \le S$, and $\psi_k \ge \omega$ because every bottom entry failed the
loop's test), so the iteration reaches the state after round $i$ except with probability at most
$\varphi_{\mathrm{se}} + \varphi_R/2 + \varphi$. One good set serves every iterate
(`NLAlib.Ops.PWrites.pstep_of_forall`). -/
theorem roundedDecoupleIteration_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u < 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} {β φse : ℝ} (hSE : IsRandomSmallEig law s₀ β φse I)
    (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse) (hDisk : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k q L i : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    (hkn : k ≤ n) {w p f : ℕ × ℕ} {ps : List ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    {B g Bi S ω tL tv R φR α γ φ C ε E : ℝ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ 2 * B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g / 2 ≤ ‖d i - d j‖)
    (hiE : i * E ≤ g / 2 / (16 * (n + 1) * (2 * B))) (hSi : specNorm H + i * E ≤ S)
    (hE : (1 + C) * S * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1) ≤ E)
    (hps : ps = roundedDecoupleParams tL R tv γ Bi α ε k q) (hBi : 4 * B ≤ Bi)
    (hBk : Bi ^ ((2 : ℝ) / k) ≤ 2) (hω : 0 < ω) (hωL : (1 + u) ^ 2 * ω ^ 2 ≤ tL)
    (hgapS : 2 * ω ^ 2 / S ≤ g / 4)
    (hR : 0 < R) (hφR : 0 < φR) (hφR1 : φR ≤ 1)
    (hβ : β + R + 2 * u * (S + β + R) ≤ ω ^ 2 / (20 * 101 * S))
    (hdη : 4 * u * (S + β + R) ≤ R * √(φR / (2 * k))) (hnu : (n + 1 : ℝ) * u ≤ 1 / 2500)
    (huo : 30000 * k * (((n + 1 : ℕ) : ℝ) * √((n + 1 : ℕ) : ℝ) * u) * ((2 + 2 * 1.1) * S) ^ k ≤
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹) * ω) ^ k)
    (huo1 : 100000 * ((n + 1 + k : ℕ) : ℝ) ^ 2 * u ≤ 1)
    (hxuR : 300 * (n + 1) ^ 2 * u ≤
      (16 * Bi)⁻¹ * (R * √(φR / (2 * k)) / 2 / ((2 + 2 * 1.1) * S)) ^ k)
    (hboundR : (66 + 2 * 1.1) * Bi * S * ((2 + 2 * 1.1) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ ω / 2)
    (hα : α = (1.01 * Bi) ^ ((4 * q : ℝ) / 2 ^ q)) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hε : ε = (0.998 * (1 - γ) * (1 - γ) / ((13 * Bi ^ 4) ^ ((k : ℝ)⁻¹) * α ^ 2 *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) ^ 2)) ^
        ((k : ℝ) / (k - 1))) (hε2 : ε ≤ 1 / 2) (hφ : 0 < φ) (hφ1 : φ ≤ 1 / 5)
    (hd : R * √(φR / (2 * k)) / 2 ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 4)
    (hC1 : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹)) ≤ C)
    (hxu : 300 * (n + 1) ^ 2 * u ≤
      (8004 * Bi)⁻¹ * (R * √(φR / (2 * k)) / 2 / ((2 + 2 * C) * S)) ^ k)
    (hbound : (66 + 2 * C) * Bi * S * ((2 + 2 * C) * S / (R * √(φR / (2 * k)) / 2)) ^ k *
      √(n + 1) * (300 * (n + 1) ^ 2 * u) ≤ 0.001 * ω)
    (hexc1 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * S)) ≤ 0.005 * ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * ω))
    (hexc2 : 6 * u * (1.1 * S + 3 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * S)) ≤ ε * ((1.998 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹) * ω) * √(φ / (11 * ((n + 1 : ℕ) : ℝ))) / 8)
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) :
    PWrites law I (shIteration (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, (excNet ε).length] [w, (p.1, p.2 + 1), (p.1, p.2 + 2),
        (p.1, p.2 + 3), (p.1, p.2 + 4), (p.1, p.2 + 5), (p.1, p.2 + 6), (p.1, p.2 + 7),
        (p.1, p.2 + 10), w, f])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ => DecoupleLoopCtx n L w p f ps μ ∧
        DecoupleLoopState u k H tL (1.002 * (1 - γ)) E w (L, 0) i μ ∧
        μ.store.get L 3 = some 0)
      (fun μ' => DecoupleLoopCtx n L w p f ps μ' ∧
        DecoupleLoopMid u k H tv (1.002 * (1 - γ)) E w (i + 1) μ') (φse + φR / 2 + φ) := by
  have hu := hM.roundoff_nonneg
  have hφ0 : 0 ≤ φse + φR / 2 + φ := by positivity
  by_cases hD : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock f.1 f.2 1) ∧ Fp.Disj (Store.inBlock p.1 p.2 ps.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
  swap
  · exact PWrites.of_writes hφ0 fun μ _ h => absurd ⟨h.1.2.2.2.2.2.2.2.2.1,
      h.1.2.2.2.2.2.2.2.2.2⟩ hD
  obtain ⟨haf, hPWF⟩ := hD
  have hlen : ps.length = 10 + 2 * (excNet ε).length := by
    rw [hps, length_roundedDecoupleParams]
  have hio : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock (p.1, p.2 + 1).1 (p.1, p.2 + 1).2 1 ⊔
        Store.inBlock (p.1, p.2 + 2).1 (p.1, p.2 + 2).2 1 ⊔
        Store.inBlock (p.1, p.2 + 3).1 (p.1, p.2 + 3).2 1 ⊔
        Store.inBlock (p.1, p.2 + 4).1 (p.1, p.2 + 4).2 1 ⊔
        Store.inBlock (p.1, p.2 + 5).1 (p.1, p.2 + 5).2 1 ⊔
        Store.inBlock (p.1, p.2 + 6).1 (p.1, p.2 + 6).2 1 ⊔
        Store.inBlock (p.1, p.2 + 7).1 (p.1, p.2 + 7).2 1 ⊔
        Store.inBlock (p.1, p.2 + 10).1 (p.1, p.2 + 10).2 (2 * (excNet ε).length)) :=
    hPWF.symm.mono le_rfl (by rw [hlen]; fp_sub)
  have hB0 : 1 / 2 ≤ B := by
    have := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
    linarith
  have hBi0 : 0 ≤ Bi := by linarith
  have hα0 : 0 ≤ α := hα ▸ Real.rpow_nonneg (by positivity) _
  have hC0 : 0 ≤ 1 + C := by
    have : 0 ≤ 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
        (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
          Bi ^ ((k : ℝ)⁻¹)) := by positivity
    linarith
  have hcu : 0 ≤ (1 + 300 * (n + 1) ^ 2 * u) ^ k - 1 := by
    have : 1 ≤ (1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k := one_le_pow₀ (by nlinarith)
    linarith
  let ι := {x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ // IsUpperHessenberg x ∧ specNorm x ≤ S ∧
    ω ≤ hessenbergPotential k x ∧ ∃ (Vx : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
      (dx : Fin (n + 1) → ℂ), IsUnit Vx ∧ x * Vx = Vx * Matrix.diagonal dx ∧
      pseudoConditionNumber Vx ≤ Bi ∧ ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖dx i - dx j‖}
  have hst := PWrites.pstep_of_forall hI hloc (fun x : ι =>
    have hx := x.2.2.2.2.choose_spec.choose_spec
    shIteration_pwrites hI hloc hS hM hu1.le hL hNat hC hQ hSE hβ0 hφse hDisk hU hkq hk hkn haf
      hio x.2.1 hx.1 hx.2.1 hx.2.2.1 hBk hω x.2.2.2.1 x.2.2.1 hx.2.2.2 hR hφR hφR1 hβ hdη hnu
      huo huo1 hxuR hboundR hα hγ hγ1 hε hε2 hφ hφ1 hd hC1 hxu hbound hexc1 hexc2 hthrω)
    (measurableSet_iterationOutcome (n := n) u k (1.002 * (1 - γ)) tv E w
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1))
    (fun x _ _ hP hfr hO => mem_iterationOutcome_of_shIterationOutcome hP.2.1 hfr hO
      ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left x.2.2.1 hC0) hcu).trans hE))
  -- the iterate of a state with the scan flag `0`
  have hiter : ∀ μ, DecoupleLoopCtx n L w p f ps μ →
      DecoupleLoopState u k H tL (1.002 * (1 - γ)) E w (L, 0) i μ → μ.store.get L 3 = some 0 →
      ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsPerturbedUnitarySimilar H H' (i * E) ∧
        IsUpperHessenberg H' ∧ HoldsMatrix w H' μ.store ∧
        (∀ j : Fin n, n ≤ (j : ℕ) + k → tL < (1 + u) ^ 2 * ‖H' j.succ j.castSucc‖ ^ 2) ∧
        hessenbergPotential k H' ≤ (1.002 * (1 - γ)) ^ i * hessenbergPotential k H := by
    rintro μ - ⟨H', hHH', hHess', hW, ⟨h1, -⟩ | ⟨-, hall, hψ⟩⟩ h0
    · simp only [zero_add] at h1
      rw [h0] at h1
      norm_num at h1
    · exact ⟨H', hHH', hHess', hW, hall, hψ⟩
  refine PStep.mono hst (fun μ ⟨hctx, hstate, h0⟩ => ?_)
    (fun μ μ' ⟨hctx, hstate, h0⟩ hT => ?_) le_rfl
  · obtain ⟨H', hHH', hHess', hW, hall, -⟩ := hiter μ hctx hstate h0
    obtain ⟨V', d', hV', hHV', hκ', hsep'⟩ :=
      hHH'.exists_pseudoConditionNumber_le_and_le_norm_sub hV hHV hκ (by positivity) hgap hiE
    have hnorm : specNorm H' ≤ S := hHH'.specNorm_le.trans hSi
    have hψω : ω ≤ hessenbergPotential k H' := by
      by_contra hlt
      push Not at hlt
      obtain ⟨j, hj, hjle⟩ := exists_norm_subdiag_le_hessenbergPotential (by omega) hkn H'
      have h1 := hall j hj
      have h2 : ‖H' j.succ j.castSucc‖ ^ 2 ≤ ω ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hjle.trans hlt.le) 2
      nlinarith [sq_nonneg (1 + u)]
    obtain ⟨-, -, -, hl, hp, -, hrf, -, -, -⟩ := hctx
    rw [hps] at hp
    have hget : ∀ j < 10, μ.store.get p.1 (p.2 + j) =
        some ((roundedDecoupleParams tL R tv γ Bi α ε k q).getD j 0) := fun j hj =>
      Store.get_of_readBlock hp (by rw [length_roundedDecoupleParams]; omega) 0
    have hnet := Store.readBlock_sub hp (o := 10) (n := 2 * (excNet ε).length)
      (by rw [length_roundedDecoupleParams])
    refine ⟨⟨H', hHess', hnorm, hψω, V', d', hV', hHV', hκ'.trans (by linarith),
      fun i j hij => hgapS.trans ((by ring : g / 2 / 2 = g / 4) ▸ hsep' i j hij)⟩, ?_,
      hW, hget 1 (by omega), hget 2 (by omega), hget 3 (by omega), hget 4 (by omega),
      hget 5 (by omega), hget 6 (by omega), hget 7 (by omega), ?_, by omega⟩
    · simp only [Mem.live_cons] at hl ⊢
      tauto
    · have hfl : (List.flatMap (fun z : ℂ => [z.re, z.im]) (excNet ε)).length =
          2 * (excNet ε).length := by simp [List.length_flatMap, mul_comm]
      simpa [roundedDecoupleParams, List.take_of_length_le hfl.le] using hnet
  · obtain ⟨H', hHH', -, hW, -, hψ⟩ := hiter μ hctx hstate h0
    obtain ⟨hfr, H'', hsim, hHess'', hW'', hdec⟩ := shIterationOutcome_of_mem hW hT
    refine ⟨hfr, hctx.of_eqOff le_sup_left hfr, H'', (hHH'.trans hsim).mono
      (le_of_eq (by push_cast; ring)), hHess'', hW'', hdec.imp id fun h => ?_⟩
    have hc0 : 0 ≤ 1.002 * (1 - γ) := by nlinarith
    calc hessenbergPotential k H'' ≤ 1.002 * (1 - γ) * hessenbergPotential k H' := h
      _ ≤ 1.002 * (1 - γ) * ((1.002 * (1 - γ)) ^ i * hessenbergPotential k H) :=
        mul_le_mul_of_nonneg_left hψ hc0
      _ = (1.002 * (1 - γ)) ^ (i + 1) * hessenbergPotential k H := by ring

end Iteration


end NLAlib.ShiftedQR
