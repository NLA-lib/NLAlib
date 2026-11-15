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

[BanksGarzaVargasSrivastava2022, Lemma 6.4] in floating point: the decoupler of the rounded
worklist scans the bottom $k$ subdiagonal entries and, while none passes, runs one iteration
(`NLAlib.ShiftedQR.shIteration`: `Regularize`, then $\mathrm{Sh}_{k,B}$), for at most $F$
rounds. On the good tapes each iteration decouples the matrix at the bottom or contracts
$\psi_k$ by $1.002(1 - \gamma)$, so a matrix still coupled after $F$ rounds is impossible, and
the failure probabilities of the rounds add (`NLAlib.Ops.PWrites.whileFuel`). The scan of the
loop has its own threshold $t_L$: the iteration certifies only
$(1 - \boldsymbol{u})^2\lvert h\rvert^2 \le t$, which a rounded scan with the same threshold can
miss, so $(1 + \boldsymbol{u})^2 t \le (1 - \boldsymbol{u})^2 t_L$.

## Main definitions

* `NLAlib.ShiftedQR.roundedDecouple`: the program; `NLAlib.ShiftedQR.roundedDecoupleParams`:
  its parameter words.
* `NLAlib.ShiftedQR.DecoupleLoopCtx`, `NLAlib.ShiftedQR.DecoupleLoopState`,
  `NLAlib.ShiftedQR.DecoupleLoopMid`: the operands and the states of the loop.

## Main results

* `NLAlib.ShiftedQR.roundedDecoupleScan_writes`,
  `NLAlib.ShiftedQR.roundedDecoupleIteration_pwrites`: the scan and the iteration of a round.
* `NLAlib.ShiftedQR.roundedDecouple_randomDecouplingContract`: the loop meets
  `NLAlib.ShiftedQR.RandomDecouplingContract` (P11p).
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib.ShiftedQR

open Ops

section Program

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- The exit of the decoupling loop: the flag is $0$ if the last scan passed (scan flag `R[3]`
positive) and $1$ otherwise. The interface is `[] (R) → (Fl)`. -/
def roundedDecoupleExit : Impl O Q :=
  opsImpl% [] (R) → (Fl) {
    if (Has.inj CmpTst.isPos) [] (R[3]) {
      call (Has.inj IndexOp.lit) [0] () → (Fl)
    } else {
      call (Has.inj IndexOp.lit) [1] () → (Fl)
    }
  }

/-- The rounds of the decoupling loop with the scan registers `R` and the index words $m$
($k = 2^m$) and $n_0$ (the net size) as dimensions: scan the bottom $k$ subdiagonal entries with
the threshold `P[0]`, and while none passed, for at most $F$ rounds, run
`NLAlib.ShiftedQR.shIteration` with the words `P[1..7]` and the net at `P[10]`, then scan again;
then `NLAlib.ShiftedQR.roundedDecoupleExit`. The interface is
`[N, k, np, F, m, n0] (W, P, R) → (W, Fl)`. -/
def roundedDecoupleLoop : Impl O Q :=
  opsImpl% [N, k, np, F, m, n0] (W, P, R) → (W, Fl) {
    run (bottomScan (O := O) (Q := Q)).body [N, k] (W, P, R);
    while j < F, (Has.inj CmpTst.isZero) [] (R[3]) {
      run (shIteration (O := O) (Q := Q)).body [N, m, k, n0]
        (W, P[1], P[2], P[3], P[4], P[5], P[6], P[7], P[10], W, Fl);
      run (bottomScan (O := O) (Q := Q)).body [N, k] (W, P, R)
    } then {
      run (roundedDecoupleExit (O := O) (Q := Q)).body [] (R, Fl)
    }
  }

/-- **The rounded decoupling loop** ([BanksGarzaVargasSrivastava2022, Lemma 6.4]): allocate the
scan registers `R`, read the index words $m$ ($k = 2^m$) and $n_0$ (the net size) from
`P[8]`, `P[9]`, and run `NLAlib.ShiftedQR.roundedDecoupleLoop`. The interface is
`[N, k, np, F] (W, P) → (W, Fl)`, that of the worklist's decoupler. -/
def roundedDecouple : Impl O Q :=
  opsImpl% [N, k, np, F] (W, P) → (W, Fl) {
    let R ← alloc 5;
    let m ← index (Has.inj IdxTst.toNat) (P[8]) ≤ k;
    let n0 ← index (Has.inj IdxTst.toNat) (P[9]) ≤ np;
    run (roundedDecoupleLoop (O := O) (Q := Q)).body [N, k, np, F, m, n0] (W, P, R, W, Fl)
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

/-- The number of parameter words of the decoupling loop. -/
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

/-- **The iterate of a round**: in the state before round $i$ with the scan flag $0$, the
iterate $\mathbf{H}'$ of a block of condition at most $2B$ and separation $g/2$ has, when
$iE \le (g/2)/(16(n+1)2B)$, condition at most $4B \le B_i$ and separation
$g/4 \ge 2\omega^2/S$
(`NLAlib.IsPerturbedUnitarySimilar.exists_pseudoConditionNumber_le_and_le_norm_sub`),
norm at most $\|\mathbf{H}\|_2 + iE \le S$, and $\psi_k(\mathbf{H}') \ge \omega$, because every
bottom entry failed the loop's test and one of them is at most $\psi_k$
(`NLAlib.exists_norm_subdiag_le_hessenbergPotential`). -/
theorem DecoupleLoopState.exists_iterate {u : ℝ} {k L i : ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {w : ℕ × ℕ}
    {B g Bi S ω tL c E : ℝ} {μ : Mem ℝ} (hst : DecoupleLoopState u k H tL c E w (L, 0) i μ)
    (h0 : μ.store.get L 3 = some 0) (hk : 0 < k) (hkn : k ≤ n) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ 2 * B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g / 2 ≤ ‖d i - d j‖)
    (hiE : i * E ≤ g / 2 / (16 * (n + 1) * (2 * B))) (hSi : specNorm H + i * E ≤ S)
    (hBi : 4 * B ≤ Bi) (hωL : (1 + u) ^ 2 * ω ^ 2 ≤ tL) (hgapS : 2 * ω ^ 2 / S ≤ g / 4) :
    ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsPerturbedUnitarySimilar H H' (i * E) ∧
      IsUpperHessenberg H' ∧ HoldsMatrix w H' μ.store ∧
      hessenbergPotential k H' ≤ c ^ i * hessenbergPotential k H ∧ specNorm H' ≤ S ∧
      ω ≤ hessenbergPotential k H' ∧ ∃ (Vx : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
        (dx : Fin (n + 1) → ℂ), IsUnit Vx ∧ H' * Vx = Vx * Matrix.diagonal dx ∧
        pseudoConditionNumber Vx ≤ Bi ∧ ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖dx i - dx j‖ := by
  obtain ⟨H', hHH', hHess', hW, ⟨h1, -⟩ | ⟨-, hall, hψ⟩⟩ := hst
  · simp only [zero_add] at h1
    rw [h0] at h1
    norm_num at h1
  obtain ⟨V', d', hV', hHV', hκ', hsep'⟩ :=
    hHH'.exists_pseudoConditionNumber_le_and_le_norm_sub hV hHV hκ (by positivity) hgap hiE
  refine ⟨H', hHH', hHess', hW, hψ, hHH'.specNorm_le.trans hSi, ?_, V', d', hV', hHV',
    hκ'.trans (by linarith), fun i j hij => hgapS.trans ((by ring : g / 2 / 2 = g / 4) ▸
      hsep' i j hij)⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨j, hj, hjle⟩ := exists_norm_subdiag_le_hessenbergPotential hk hkn H'
  have h1 := hall j hj
  have h2 : ‖H' j.succ j.castSucc‖ ^ 2 ≤ ω ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hjle.trans hlt.le) 2
  nlinarith [sq_nonneg (1 + u)]

/-- The words of an iteration read from the parameter words of the loop
(`NLAlib.ShiftedQR.roundedDecoupleParams`): the operands are live, the first ten words and the
net are stored, and the flag has room. -/
theorem DecoupleLoopCtx.iteration_words {L : ℕ} {w p f : ℕ × ℕ} {ps : List ℝ}
    {tL R tv γ Bi α ε : ℝ} {k q : ℕ} {μ : Mem ℝ} (hctx : DecoupleLoopCtx n L w p f ps μ)
    (hps : ps = roundedDecoupleParams tL R tv γ Bi α ε k q) :
    μ.Live [w, (p.1, p.2 + 1), (p.1, p.2 + 2), (p.1, p.2 + 3),
      (p.1, p.2 + 4), (p.1, p.2 + 5), (p.1, p.2 + 6), (p.1, p.2 + 7), (p.1, p.2 + 10), f] ∧
      (∀ j < 10, μ.store.get p.1 (p.2 + j) =
        some ((roundedDecoupleParams tL R tv γ Bi α ε k q).getD j 0)) ∧
      μ.store.readBlock p.1 (p.2 + 10) (2 * (excNet ε).length) =
        some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧ f.2 < μ.store.len f.1 := by
  obtain ⟨-, -, -, hl, hp, -, hrf, -, -, -⟩ := hctx
  rw [hps] at hp
  have hnet := Store.readBlock_sub hp (o := 10) (n := 2 * (excNet ε).length)
    (by rw [length_roundedDecoupleParams])
  have hfl : (List.flatMap (fun z : ℂ => [z.re, z.im]) (excNet ε)).length =
      2 * (excNet ε).length := by simp [List.length_flatMap, mul_comm]
  refine ⟨?_, fun j hj => Store.get_of_readBlock hp (by rw [length_roundedDecoupleParams]; omega) 0,
    by simpa [roundedDecoupleParams, List.take_of_length_le hfl.le] using hnet, by omega⟩
  simp only [Mem.live_cons] at hl ⊢
  tauto

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

omit [Has ScalarOp O] [Has IdxTst Q] in
/-- **The exit of the decoupling loop**: from the state before round $i \le F$ at the cap or
with a scan that passed, the loop sets the flag to $0$ and holds an upper Hessenberg perturbed
unitary similarity with error $FE$ and a bottom entry of modulus at most $\omega_D$
($t_L \le (1 - \boldsymbol{u})^2\omega_D^2$). At the cap the scan has passed: a coupled matrix
has $\psi_k \le c^F\psi_k(\mathbf{H}) \le c^F N_{\max}$, and one of its bottom entries is at most
$\psi_k$, which fails the loop's test when $(1 + \boldsymbol{u})^2(c^F N_{\max})^2 \le t_L$. -/
theorem roundedDecoupleExit_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hu1 : u < 1)
    (hL : IsIndexLit M I) (hC : IsCmp id I) (h0lit : M.lit (0 : ℚ) = 0) {τ : Tape ℝ}
    {μ : Mem ℝ} {k L i F : ℕ} (hk : 0 < k) (hkn : k ≤ n) {w p f : ℕ × ℕ} {ps : List ℝ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {tL c E ωD Nmax : ℝ}
    (hcut : tL ≤ (1 - u) ^ 2 * ωD ^ 2) (hωD : 0 ≤ ωD) (hc0 : 0 ≤ c) (hE0 : 0 ≤ E)
    (hψH : hessenbergPotential k H ≤ Nmax) (hfuel : (1 + u) ^ 2 * (c ^ F * Nmax) ^ 2 ≤ tL)
    (hiF : i ≤ F) (hctx : DecoupleLoopCtx n L w p f ps μ)
    (hst : DecoupleLoopState u k H tL c E w (L, 0) i μ)
    (hend : i = F ∨ I.test (Has.inj CmpTst.isZero) [] [(L, 3)] μ = some false) :
    Writes .total I τ (roundedDecoupleExit (O := O) (Q := Q)).body (Env.frame [] [(L, 0), f])
      (Store.inBlock f.1 f.2 1)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        IsPerturbedUnitarySimilar H H' (F * E) ∧ IsUpperHessenberg H' ∧
        (∃ j : Fin n, n ≤ (j : ℕ) + k ∧ ‖H' j.succ j.castSucc‖ ≤ ωD) ∧
        HoldsMatrix w H' μ'.store) μ := by
  have hp1 : 0 < (1 - u) ^ 2 := by nlinarith
  obtain ⟨H', hHH', hHess', hW', ⟨h1, j, hj, hjt⟩ | ⟨h0, hall, hψ⟩⟩ := hst
  · simp only [zero_add] at h1
    refine writes_ite (a := [(L, 3)]) rfl rfl (hC.test_isPos h1) ?_
    rw [show decide (0 < id (1 : ℝ)) = true by simp, if_pos rfl]
    refine (writes_indexLit hL rfl rfl (by have := hctx.2.2.2.2.2.2.1; omega)).mono le_rfl ?_
    rintro μ' hfr ⟨-, hF⟩
    have hh : (1 - u) ^ 2 * ‖H' j.succ j.castSucc‖ ^ 2 ≤ (1 - u) ^ 2 * ωD ^ 2 := hjt.trans hcut
    exact ⟨by simpa [h0lit] using hF, H', hHH'.mono
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hiF) hE0), hHess',
      ⟨j, hj, (pow_le_pow_iff_left₀ (norm_nonneg _) hωD two_ne_zero).mp
        (le_of_mul_le_mul_left hh hp1)⟩, hW'.of_eqOff hfr hctx.2.2.2.2.2.2.2.2.1.symm⟩
  · exfalso
    simp only [zero_add] at h0
    rcases hend with rfl | htest
    · obtain ⟨j, hj, hjle⟩ := exists_norm_subdiag_le_hessenbergPotential hk hkn H'
      have h1 := hall j hj
      have h2 : ‖H' j.succ j.castSucc‖ ≤ c ^ i * Nmax :=
        hjle.trans (hψ.trans (mul_le_mul_of_nonneg_left hψH (pow_nonneg hc0 _)))
      have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg (1 + u))
      linarith
    · rw [hC.test_isZero h0] at htest
      simp at htest

end Theorems

section Iteration

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

set_option maxHeartbeats 1000000 in
-- The hypothesis list of the iteration, with its long real constants, makes elaboration heavy.
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
  refine PStep.mono hst (fun μ ⟨hctx, hstate, h0⟩ => ?_)
    (fun μ μ' ⟨hctx, hstate, h0⟩ hT => ?_) le_rfl
  · obtain ⟨H', -, hHess', hW, -, hnorm, hψω, V', d', hV', hHV', hκ', hsep'⟩ :=
      hstate.exists_iterate h0 (by omega) hkn hV hHV hκ hg hgap hiE hSi hBi hωL hgapS
    obtain ⟨hl, hget, hnet, hf⟩ := hctx.iteration_words hps
    exact ⟨⟨H', hHess', hnorm, hψω, V', d', hV', hHV', hκ', hsep'⟩, hl, hW, hget 1 (by omega),
      hget 2 (by omega), hget 3 (by omega), hget 4 (by omega), hget 5 (by omega),
      hget 6 (by omega), hget 7 (by omega), hnet, hf⟩
  · obtain ⟨H', hHH', -, hW, hψ, -⟩ :=
      hstate.exists_iterate h0 (by omega) hkn hV hHV hκ hg hgap hiE hSi hBi hωL hgapS
    obtain ⟨hfr, H'', hsim, hHess'', hW'', hdec⟩ := shIterationOutcome_of_mem hW hT
    refine ⟨hfr, hctx.of_eqOff le_sup_left hfr, H'', (hHH'.trans hsim).mono
      (le_of_eq (by push_cast; ring)), hHess'', hW'', hdec.imp id fun h => ?_⟩
    have hc0 : 0 ≤ 1.002 * (1 - γ) := by nlinarith
    calc hessenbergPotential k H'' ≤ 1.002 * (1 - γ) * hessenbergPotential k H' := h
      _ ≤ 1.002 * (1 - γ) * ((1.002 * (1 - γ)) ^ i * hessenbergPotential k H) :=
        mul_le_mul_of_nonneg_left hψ hc0
      _ = (1.002 * (1 - γ)) ^ (i + 1) * hessenbergPotential k H := by ring

/-- **The rounds of the decoupling loop on the good tapes**: if each iteration from the state
before round $i < F$ with the scan flag $0$ reaches the state after it except with probability
at most $\varphi \ge 0$, then from a stored upper Hessenberg $\mathbf{H}$ with
$\psi_k(\mathbf{H}) \le N_{\max}$ the initial scan, the at most $F$ rounds (iteration and scan,
`NLAlib.ShiftedQR.roundedDecoupleScan_writes`) and the exit
(`NLAlib.ShiftedQR.roundedDecoupleExit_writes`) set the flag to $0$ and hold an upper Hessenberg
perturbed unitary similarity with error $FE$ and a bottom entry of modulus at most $\omega_D$,
except with probability at most $F\varphi$ (`NLAlib.Ops.PWrites.whileFuel`). -/
theorem roundedDecoupleLoop_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u < 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {law : ℕ → Measure ℝ}
    {k q n0 F L : ℕ} (hk : 0 < k) (hkn : k ≤ n) {w p f : ℕ × ℕ} {ps : List ℝ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {tL tv c E ωD Nmax φ : ℝ}
    (hps : ps.getD 0 0 = tL) (hps0 : 0 < ps.length) (hHess : IsUpperHessenberg H)
    (hψH : hessenbergPotential k H ≤ Nmax) (hthr : (1 + u) ^ 2 * tv ≤ (1 - u) ^ 2 * tL)
    (hcut : tL ≤ (1 - u) ^ 2 * ωD ^ 2) (hωD : 0 ≤ ωD) (hc0 : 0 ≤ c) (hE0 : 0 ≤ E)
    (hφ : 0 ≤ φ) (hfuel : (1 + u) ^ 2 * (c ^ F * Nmax) ^ 2 ≤ tL)
    (hit : ∀ i < F, PWrites law I (shIteration (O := O) (Q := Q)).body
      (Env.frame [n + 1, q, k, n0] [w, (p.1, p.2 + 1), (p.1, p.2 + 2), (p.1, p.2 + 3),
        (p.1, p.2 + 4), (p.1, p.2 + 5), (p.1, p.2 + 6), (p.1, p.2 + 7), (p.1, p.2 + 10), w, f])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ => DecoupleLoopCtx n L w p f ps μ ∧ DecoupleLoopState u k H tL c E w (L, 0) i μ ∧
        μ.store.get L 3 = some 0)
      (fun μ' => DecoupleLoopCtx n L w p f ps μ' ∧ DecoupleLoopMid u k H tv c E w (i + 1) μ')
      φ) :
    PWrites law I (roundedDecoupleLoop (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, ps.length, F, q, n0] [w, p, (L, 0), w, f])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock L 0 5)
      (fun μ => DecoupleLoopCtx n L w p f ps μ ∧ HoldsMatrix w H μ.store)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        IsPerturbedUnitarySimilar H H' (F * E) ∧ IsUpperHessenberg H' ∧
        (∃ j : Fin n, n ≤ (j : ℕ) + k ∧ ‖H' j.succ j.castSucc‖ ≤ ωD) ∧
        HoldsMatrix w H' μ'.store) (F * φ) := by
  have h0lit : M.lit (0 : ℚ) = 0 := by simpa using hNat 0 (Nat.zero_le _)
  have hlive3 : ∀ μ, DecoupleLoopCtx n L w p f ps μ → μ.Live [w, p, (L, 0)] := fun μ h =>
    h.2.2.2.1.mono (by simp)
  unfold roundedDecoupleLoop
  refine (PWrites.seq (φ₁ := 0) hI hloc (by positivity) ?scan
    (PWrites.whileFuel (F := Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock f.1 f.2 1 ⊔ Store.inBlock L 0 5)
      (G := Store.inBlock f.1 f.2 1) (N := F) hI hloc rfl
      (fun i μ => DecoupleLoopCtx n L w p f ps μ ∧ DecoupleLoopState u k H tL c E w (L, 0) i μ)
      (fun _ => φ) (fun _ _ => hφ) le_rfl (fun _ h => h) ?test ?body ?exit)).mono (fun _ h => h)
    (sup_le le_sup_right (sup_le le_rfl (le_sup_of_le_left le_sup_right))) (fun _ h => h) ?phi
  case scan =>
    exact (PWrites.of_writes le_rfl fun μ τ ⟨hctx, hW⟩ =>
      roundedDecoupleScan_writes (τ := τ) (i := 0) (tv := tv) (E := E) (c := c) hS hM hu1 hL
        hNat hC hkn hps hps0 hthr hctx ⟨H, by simpa using IsPerturbedUnitarySimilar.refl H,
          hHess, hW, Or.inr (by simp)⟩).in_frame rfl rfl fun μ h => hlive3 μ h.1
  case phi =>
    simp only [zero_add, add_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact le_rfl
  case test =>
    rintro i - μ ⟨-, H', -, -, -, ⟨h1, -⟩ | ⟨h0, -⟩⟩
    · simp only [zero_add] at h1
      exact ⟨_, (Interp.testAt_eq (a := [(L, 3)]) rfl rfl).trans (hC.test_isZero h1)⟩
    · simp only [zero_add] at h0
      exact ⟨_, (Interp.testAt_eq (a := [(L, 3)]) rfl rfl).trans (hC.test_isZero h0)⟩
  case body =>
    intro i hi
    refine (PWrites.seq hI hloc le_rfl ((hit i hi).in_frame rfl rfl fun μ h => ?_)
      ((PWrites.of_writes le_rfl fun μ τ ⟨hctx, hmid⟩ =>
        roundedDecoupleScan_writes (τ := τ) hS hM hu1 hL hNat hC hkn hps hps0 hthr hctx
          hmid).in_frame rfl rfl fun μ h => hlive3 μ h.1)).mono
      (fun μ ⟨⟨hctx, hst⟩, htest⟩ => ⟨hctx, hst, ?_⟩) (sup_le le_sup_left le_sup_right)
      (fun _ h => h) (by simp)
    · have := h.1.2.2.2.1
      simp only [Mem.live_cons, Mem.live_nil, and_true] at this ⊢
      tauto
    obtain ⟨H', -, -, -, ⟨h1, -⟩ | ⟨h0, -⟩⟩ := hst
    · simp only [zero_add] at h1
      rw [Interp.testAt_eq (a := [(L, 3)]) rfl rfl, hC.test_isZero h1] at htest
      simp at htest
    · simpa using h0
  case exit =>
    intro i hi
    refine (PWrites.of_writes le_rfl fun μ τ h => ?_).in_frame rfl rfl fun μ h =>
      h.1.1.2.2.2.1.mono (by simp)
    obtain ⟨⟨hctx, hst⟩, hend⟩ := h
    rw [Interp.testAt_eq (a := [(L, 3)]) rfl rfl] at hend
    exact roundedDecoupleExit_writes hu1 hL hC h0lit hk hkn hcut hωD hc0 hE0 hψH hfuel hi hctx
      hst hend

/-- **The decoupling loop from its rounds**: the allocation of the scan registers and the two
index reads of $m$ and $n_0$ from the parameter words (`NLAlib.Ops.PWrites.allocs`,
`NLAlib.Ops.PWrites.bindIdx`) carry a probabilistic specification of
`NLAlib.ShiftedQR.roundedDecoupleLoop` at every fresh buffer to `NLAlib.ShiftedQR.roundedDecouple`
from the precondition of `NLAlib.ShiftedQR.RandomDecouplingContract`. -/
theorem roundedDecouple_pwrites_of_loop {I : Interp O Q ℝ} (hI : I.IsMeasurable)
    (hQ : IsToNat id I) {law : ℕ → Measure ℝ} {k q F : ℕ} (hqk : q ≤ k) {w p f : ℕ × ℕ}
    {ps : List ℝ} {tL R tv γ Bi α ε : ℝ} (hps : ps = roundedDecoupleParams tL R tv γ Bi α ε k q)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e ωD φ : ℝ} (hφ : 0 ≤ φ)
    (hloop : ∀ L, PWrites law I (roundedDecoupleLoop (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, ps.length, F, q, (excNet ε).length] [w, p, (L, 0), w, f])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock L 0 5)
      (fun μ => DecoupleLoopCtx n L w p f ps μ ∧ HoldsMatrix w H μ.store)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        IsPerturbedUnitarySimilar H H' e ∧ IsUpperHessenberg H' ∧
        (∃ j : Fin n, n ≤ (j : ℕ) + k ∧ ‖H' j.succ j.castSucc‖ ≤ ωD) ∧
        HoldsMatrix w H' μ'.store) φ) :
    PWrites law I (roundedDecouple (O := O) (Q := Q)).body
      (Env.frame [n + 1, k, ps.length, F] [w, p, w, f])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ => HoldsMatrix w H μ.store ∧ μ.store.readBlock p.1 p.2 ps.length = some ps ∧
        μ.Live [w, p, w, f] ∧ w.2 + 2 * ((n + 1) * (n + 1)) ≤ μ.store.len w.1 ∧
        f.2 + 1 ≤ μ.store.len f.1 ∧
        Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1)))) (Store.inBlock f.1 f.2 1) ∧
        Fp.Disj (Store.inBlock p.1 p.2 ps.length)
          (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1))
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        IsPerturbedUnitarySimilar H H' e ∧ IsUpperHessenberg H' ∧
        (∃ j : Fin n, n ≤ (j : ℕ) + k ∧ ‖H' j.succ j.castSucc‖ ≤ ωD) ∧
        HoldsMatrix w H' μ'.store) φ := by
  have hlen : ps.length = 10 + 2 * (excNet ε).length := by
    rw [hps, length_roundedDecoupleParams]
  unfold roundedDecouple
  refine PWrites.allocs (lens := [.const 5]) (ns := [5]) rfl
    (Pre₁ := fun L μ => DecoupleLoopCtx n L w p f ps μ ∧ HoldsMatrix w H μ.store) ?_ ?_
    fun L => ?_
  · rintro μ s₁ ⟨hW, hp, hl, hrw, hrf, hWF, hPWF⟩ hlen' hlens hBelow
    have h1 : w.1 < μ.store.length := hl w (by simp)
    have h2 : p.1 < μ.store.length := hl p (by simp)
    have h3 : f.1 < μ.store.length := hl f (by simp)
    have hl0 := hlens 0 (by simp)
    simp only [List.length_cons, List.length_nil] at hlen'
    refine ⟨⟨h1, h2, h3, ?_, hBelow.readBlock_of h2 hp, by rw [(hBelow w.1 h1).1]; exact hrw,
      by rw [(hBelow f.1 h3).1]; exact hrf, by simpa using hl0.ge, hWF, hPWF⟩,
      hW.of_below hBelow h1⟩
    simp only [Mem.Live, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, hlen']
    omega
  · rintro μ ⟨-, -, hl, -⟩ st st' pos hBelow ⟨hf0, H', h1, h2, h3, hW'⟩
    exact ⟨hBelow.get_of (hl f (by simp)) hf0, H', h1, h2, h3,
      hW'.of_below hBelow (hl w (by simp))⟩
  have hget : ∀ μ, DecoupleLoopCtx n L w p f ps μ → ∀ j < 10,
      μ.store.get p.1 (p.2 + j) = some (ps.getD j 0) :=
    fun μ h j hj => Store.get_of_readBlock h.2.2.2.2.1 (by rw [hlen]; omega) 0
  have h8 : ∀ μ, DecoupleLoopCtx n L w p f ps μ →
      I.index (Has.inj IdxTst.toNat) [(p.1, p.2 + 8)] μ = some q := fun μ h =>
    hQ.index_eq_of_decode_nat (hget μ h 8 (by omega)) (by subst hps; rfl)
  have h9 : ∀ μ, DecoupleLoopCtx n L w p f ps μ →
      I.index (Has.inj IdxTst.toNat) [(p.1, p.2 + 9)] μ = some (excNet ε).length := fun μ h =>
    hQ.index_eq_of_decode_nat (hget μ h 9 (by omega)) (by subst hps; rfl)
  refine PWrites.bindIdx hI (a := [(p.1, p.2 + 8)]) rfl rfl
    (fun μ ⟨hctx, _⟩ => ⟨q, hqk, h8 μ hctx⟩) fun v hv => ?_
  by_cases hvq : v = q
  swap
  · exact PWrites.of_writes hφ fun μ _ ⟨⟨hctx, _⟩, hv'⟩ =>
      (hvq (Option.some.inj (hv'.symm.trans (h8 μ hctx)))).elim
  subst v
  refine PWrites.bindIdx hI (a := [(p.1, p.2 + 9)]) rfl rfl
    (fun μ ⟨⟨hctx, _⟩, _⟩ => ⟨(excNet ε).length, by rw [hlen]; omega, h9 μ hctx⟩)
    fun v hv => ?_
  by_cases hvq : v = (excNet ε).length
  swap
  · exact PWrites.of_writes hφ fun μ _ ⟨⟨⟨hctx, _⟩, _⟩, hv'⟩ =>
      (hvq (Option.some.inj (hv'.symm.trans (h9 μ hctx)))).elim
  subst hvq
  have hRL : Store.inBlock L 0 5 ≤ Fp.above L := fun b i h => (show L ≤ b from h.1 ▸ le_rfl)
  refine ((hloop L).in_frame rfl rfl fun μ h => h.1.2.2.2.1.mono (by simp)).mono ?_
    (sup_le_sup_left hRL _) (fun _ h => h) le_rfl
  exact fun μ h => h.1.1

set_option maxHeartbeats 4000000 in
-- The loop's program term and the hypotheses of the iteration make elaboration heavy.
/-- **The rounded decoupling loop meets the randomized decoupling contract**
([BanksGarzaVargasSrivastava2022, Lemma 6.4] in floating point, corrected): on a machine with the
standard model at $\boldsymbol{u} < 1$, exact natural literals up to $n_{\max} + 1$, a measurable
interpretation reading the tape only in its windows, a `SmallEig` kernel and an exact polar disk
sampler, `NLAlib.ShiftedQR.roundedDecouple` with the parameter words
`NLAlib.ShiftedQR.roundedDecoupleParams` meets `NLAlib.ShiftedQR.RandomDecouplingContract` on the
class (condition $2B$, separation $g/2$) for orders up to $n_{\max} + 1$ and norms up to
$N_{\max}$, with failure probability $F(\varphi_{\mathrm{se}} + \varphi_R/2 + \varphi)$, the level
$\omega_D$ and the backward error $FE$, $E = (1 + C)S((1 + 300(n_{\max}+1)^2\boldsymbol{u})^k - 1)$.
The hypotheses are those of `NLAlib.ShiftedQR.shIteration_pwrites` at the order $n_{\max} + 1$,
the class constant $B_i \ge 4B$ and the iterate norm $S$, and the loop's: the scan thresholds
$(1 + \boldsymbol{u})^2 t \le (1 - \boldsymbol{u})^2 t_L \le (1 - \boldsymbol{u})^4\omega_D^2$,
the cap $(1 + \boldsymbol{u})^2((1.002(1 - \gamma))^F N_{\max})^2 \le t_L$, the iterate norms
$N_{\max} + FE \le S$ and the class preservation $FE \le (g/2)/(16(n_{\max} + 1) \cdot 2B)$.
Each round is one iteration (P10b) and a scan; the iterates stay in the class (condition $4B$,
separation $g/4$,
`NLAlib.IsPerturbedUnitarySimilar.exists_pseudoConditionNumber_le_and_le_norm_sub`);
a coupled matrix had its potential contracted, so after $F$ rounds the scan passes
(`NLAlib.exists_norm_subdiag_le_hessenbergPotential`), and the failures of the rounds add
(`NLAlib.Ops.PWrites.whileFuel`). -/
theorem roundedDecouple_randomDecouplingContract {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u < 1) (hL : IsIndexLit M I) {nmax : ℕ}
    (hNat : IsExactNatLit id M (nmax + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} {β φse : ℝ} (hSE : IsRandomSmallEig law s₀ β φse I)
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
      g / 2 / (16 * (nmax + 1) * (2 * B))) :
    RandomDecouplingContract law (2 * B) (g / 2) (F * (φse + φR / 2 + φ)) k F nmax Nmax
      (roundedDecoupleParams tL R tv γ Bi α ε k q) ωD
      (fun _ => F * ((1 + C) * S * ((1 + 300 * (nmax + 1) ^ 2 * u) ^ k - 1)))
      (roundedDecouple (O := O) (Q := Q)) I := by
  intro n N w p f H V d hkn hn hN hHess hnorm hV hHV hκ hgap
  have hu := hM.roundoff_nonneg
  set E := (1 + C) * S * ((1 + 300 * (nmax + 1) ^ 2 * u) ^ k - 1) with hEdef
  set ps := roundedDecoupleParams tL R tv γ Bi α ε k q with hps
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
  have hgB : g / 2 / (16 * (nmax + 1) * (2 * B)) ≤ g / 2 / (16 * (n + 1) * (2 * B)) := by
    gcongr
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
  have hlen := length_roundedDecoupleParams tL R tv γ Bi α ε k q
  have hψH : hessenbergPotential k H ≤ Nmax :=
    ((hessenbergPotential_le_specNorm (by omega) hkn H).trans hnorm).trans hN
  have hiE : ∀ i < F, (i : ℝ) * E ≤ F * E := fun i hi =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) hE0
  refine roundedDecouple_pwrites_of_loop hI hQ (by rw [hkq]; exact Nat.lt_two_pow_self.le) rfl
    (by positivity) fun L => ?_
  exact roundedDecoupleLoop_pwrites hI hloc hS hM hu1 hL hNat' hC (by omega) hkn rfl
    (by rw [hlen]; omega) hHess hψH hthr hcut hωD hc0 hE0 (by positivity) hfuel fun i hi =>
    roundedDecoupleIteration_pwrites (L := L) (i := i) (p := p) hI hloc hS hM hu1 hL hNat' hC
      hQ hSE hβ0 hφse hDisk hU hkq hk hkn hV hHV hκ hg hgap ((hiE i hi).trans (hsmall.trans hgB))
      (by linarith [hiE i hi]) hEn rfl hBi hBk hω hωL hgapS hR hφR hφR1 hβ hdη hnu' huo' huo1'
      hxuR' hboundR' hα hγ hγ1 hε hε2 hφ hφ1 hd' hC1 hxu' hbound' hexc1 hexc2' hthrω

end Iteration


end NLAlib.ShiftedQR
