/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedHeadline
public import NLAlib.Eigensolvers.ShiftedQR.RoundedIteration
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveBackward
public import NLAlib.Matrix.FinitePrecision.GivensLogClose
public import NLAlib.Eigensolvers.ShiftedQR.RoundedIterationAt

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

The operand-form lemmas of this file are about trees shared by
`NLAlib.ShiftedQR.shqrSmallEigRoutine`.

## Main definitions

* `NLAlib.ShiftedQR.roundedDecoupleWith`: the program with a small-eigenvalue routine;
  `NLAlib.ShiftedQR.roundedDecoupleWith`: the program with the `SmallEig` kernel;
  `NLAlib.ShiftedQR.roundedDecoupleParams`: its parameter words.
* `NLAlib.ShiftedQR.DecoupleLoopCtx`, `NLAlib.ShiftedQR.DecoupleLoopState`,
  `NLAlib.ShiftedQR.DecoupleLoopMid`: the operands and the states of the loop.

## Main results

* `NLAlib.ShiftedQR.roundedDecoupleScan_writes`,
  `NLAlib.ShiftedQR.roundedDecoupleIteration_pwrites`: the scan and the iteration of a round.
* `NLAlib.ShiftedQR.roundedDecoupleLoop_pwrites`: the capped loop of rounds; the contract is
  `NLAlib.ShiftedQR.roundedDecoupleWith_randomDecouplingRoutineContract_at`.
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
def roundedDecoupleExit : Stmt O Q :=
  ops% [] (R) → (Fl) {
    if (Has.inj CmpTst.isPos) [] (R[3]) {
      call (Has.inj IndexOp.lit) [0] () → (Fl)
    } else {
      call (Has.inj IndexOp.lit) [1] () → (Fl)
    }
  }

/-- The rounds of the decoupling loop with a small-eigenvalue routine, with the scan registers `R`
and the index words $m$ ($k = 2^m$) and $n_0$ (the net size) as dimensions: scan the bottom $k$
subdiagonal entries with the threshold `P[0]`, and while none passed, for at most $F$ rounds, run
`NLAlib.ShiftedQR.shIterationWith` with the words `P[1..7]`, the net at `P[10]`, the routine's
$12$ words as the tail `P[np - 12]` of the parameter words and the cap $T$, recording round $j$'s
$k + 1 + n_0$ trial sites in the slots $j(k + 1 + n_0), \dots$ of the log `Lg` (slot width $w$),
then scan again; then `NLAlib.ShiftedQR.roundedDecoupleExit`. The interface is
`[N, k, np, F, T, m, n0, w] (W, P, R) → (W, Fl, Lg)`. -/
def roundedDecoupleLoopWith (SE : Stmt O Q) : Stmt O Q :=
  ops% [N, k, np, F, T, m, n0, w] (W, P, R) → (W, Fl, Lg) {
    run (bottomScan (O := O) (Q := Q)) [N, k] (W, P, R);
    while j < F, (Has.inj CmpTst.isZero) [] (R[3]) {
      run (shIterationWith SE) [N, m, k, n0, 12, T, w, j * (k + 1 + n0)]
        (W, P[1], P[2], P[3], P[4], P[5], P[6], P[7], P[10], P[np - 12], W, Fl, Lg);
      run (bottomScan (O := O) (Q := Q)) [N, k] (W, P, R)
    } then {
      run (roundedDecoupleExit (O := O) (Q := Q)) [] (R, Fl)
    }
  }

/-- **The rounded decoupling loop with a small-eigenvalue routine, recording its rotations**
([BanksGarzaVargasSrivastava2022, Lemma 6.4]): allocate the scan registers, read the index words
$m$ ($k = 2^m$) and $n_0$ from `P[8]`, `P[9]`, zero-fill the slotted log `Lg` of `ns` slots of
`w` entries (`NLAlib.slottedLogOpen`), and run `NLAlib.ShiftedQR.roundedDecoupleLoopWith`. The
interface is `[N, k, np, F, T, ns, w] (W, P) → (W, Fl, Lg)`, that of the decoupling routine of
`NLAlib.ShiftedQR.solveRoundedWith`; it needs $F(k + 1 + n_0) \le n_s$ and $k(N - 1) \le w$. -/
def roundedDecoupleWith (SE : Stmt O Q) : Stmt O Q :=
  ops% [N, k, np, F, T, ns, w] (W, P) → (W, Fl, Lg) {
    let R ← alloc 5;
    let m ← index (Has.inj IdxTst.toNat) (P[8]) ≤ k;
    let n0 ← index (Has.inj IdxTst.toNat) (P[9]) ≤ np;
    run (slottedLogOpen (O := O) (Q := Q)) [ns, w] (Lg);
    run (roundedDecoupleLoopWith SE) [N, k, np, F, T, m, n0, w] (W, P, R, W, Fl, Lg)
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

/-- The operands of the decoupling loop survive the writes of a round and of the log, in a
buffer apart from the parameter words. -/
theorem DecoupleLoopCtx.of_eqOff_log {n L : ℕ} {w q f lg : ℕ × ℕ} {ps : List ℝ} {N : ℕ}
    {μ μ' : Mem ℝ} (h : DecoupleLoopCtx n L w q f ps μ) (hq : q.1 ≠ lg.1) {F : Fp}
    (hF : F ≤ Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
      Store.inBlock L 0 5 ⊔ Store.inBlock lg.1 lg.2 N) (hfr : μ.store.EqOff F μ'.store) :
    DecoupleLoopCtx n L w q f ps μ' := by
  obtain ⟨hw, hq', hf, hl, hp, hrw, hrf, hrL, hWF, hPWF⟩ := h
  have hQR : Fp.Disj (Store.inBlock q.1 q.2 ps.length) (Store.inBlock L 0 5) :=
    Fp.disj_inBlock_of_ne (by omega)
  refine ⟨hw, hq', hf, hl.congr hfr.length_eq,
    hfr.keep (Store.readsOnly_readBlock _ _ _ _)
      ((Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨hPWF, hQR⟩,
        Fp.disj_inBlock_of_ne hq⟩).symm.mono hF le_rfl) hp,
    by rw [hfr.len_eq]; exact hrw, by rw [hfr.len_eq]; exact hrf,
    by rw [hfr.len_eq]; exact hrL, hWF, hPWF⟩

variable {n : ℕ}

/-- **The state of the decoupling loop after an iteration**, before its scan: `w` holds an upper
Hessenberg perturbed unitary similarity $\mathbf{H}'$ of $\mathbf{H}$ with error $iE$ that is
decoupled at the bottom in the iteration's scan form ($(1 - \boldsymbol{u})^2\lvert h\rvert^2
\le t$) or has $\psi_k(\mathbf{H}') \le c^i\psi_k(\mathbf{H})$. The first `i s` slots of the log at
`lg` (`ns` slots of `ws` entries, `s` per round) are closed and the similarity is by the exact
unitary of their valid entries. -/
def DecoupleLoopMid (u : ℝ) (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (tv c E : ℝ)
    (w : ℕ × ℕ) (i : ℕ) (lg : ℕ × ℕ) (ns ws s : ℕ) (μ : Mem ℝ) : Prop :=
  ∃ Ls : List (Option (List GivensEntry)), Ls.length = i * s ∧
    (∀ x ∈ slotEntries ws Ls, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns ws Ls [] μ.store ∧
  ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
    IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries ws Ls)) H H' (i * E) ∧
    IsUpperHessenberg H' ∧ HoldsMatrix w H' μ.store ∧
    ((∃ j : Fin n, n ≤ (j : ℕ) + k ∧ (1 - u) ^ 2 * ‖H' j.succ j.castSucc‖ ^ 2 ≤ tv) ∨
      hessenbergPotential k H' ≤ c ^ i * hessenbergPotential k H)

/-- **The state of the decoupling loop before round $i$**: `w` holds an upper Hessenberg
perturbed unitary similarity $\mathbf{H}'$ of $\mathbf{H}$ with error $iE$, and the scan flag in
the registers `r` is $1$ with a bottom subdiagonal entry that passed the loop's test
($(1 - \boldsymbol{u})^2\lvert h\rvert^2 \le t_L$), or $0$ with every bottom entry failing it
($t_L < (1 + \boldsymbol{u})^2\lvert h\rvert^2$) and $\psi_k(\mathbf{H}') \le
c^i\psi_k(\mathbf{H})$. The first `i s` slots of the log at `lg` (`ns` slots of `ws` entries, `s`
per round) are closed and the similarity is by the exact unitary of their valid entries. -/
def DecoupleLoopState (u : ℝ) (k : ℕ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (tL c E : ℝ)
    (w r : ℕ × ℕ) (i : ℕ) (lg : ℕ × ℕ) (ns ws s : ℕ) (μ : Mem ℝ) : Prop :=
  ∃ Ls : List (Option (List GivensEntry)), Ls.length = i * s ∧
    (∀ x ∈ slotEntries ws Ls, x.1 + 1 < n + 1) ∧ HoldsSlottedLog lg ns ws Ls [] μ.store ∧
  ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
    IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries ws Ls)) H H' (i * E) ∧
    IsUpperHessenberg H' ∧ HoldsMatrix w H' μ.store ∧
    ((μ.store.get r.1 (r.2 + 3) = some 1 ∧ ∃ j : Fin n, n ≤ (j : ℕ) + k ∧
        (1 - u) ^ 2 * ‖H' j.succ j.castSucc‖ ^ 2 ≤ tL) ∨
      (μ.store.get r.1 (r.2 + 3) = some 0 ∧
        (∀ j : Fin n, n ≤ (j : ℕ) + k → tL < (1 + u) ^ 2 * ‖H' j.succ j.castSucc‖ ^ 2) ∧
        hessenbergPotential k H' ≤ c ^ i * hessenbergPotential k H))

/-- The iterate of a round: in the state before round $i$ with the scan flag $0$, the
iterate $\mathbf{H}'$ of a block of condition at most $2B$ and separation $g/2$ has, when
$iE \le (g/2)/(16(n+1)2B)$, condition at most $4B \le B_i$ and separation
$g/4 \ge 2\omega^2/S$
(`NLAlib.IsPerturbedUnitarySimilar.exists_pseudoConditionNumber_le_and_le_norm_sub`),
norm at most $\|\mathbf{H}\|_2 + iE \le S$, and $\psi_k(\mathbf{H}') \ge \omega$, because every
bottom entry failed the loop's test and one of them is at most $\psi_k$
(`NLAlib.exists_norm_subdiag_le_hessenbergPotential`). -/
theorem DecoupleLoopState.exists_iterate {u : ℝ} {k L i : ℕ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {w : ℕ × ℕ}
    {B g Bi S ω tL c E : ℝ} {μ : Mem ℝ} {lg : ℕ × ℕ} {ns ws s : ℕ}
    (hst : DecoupleLoopState u k H tL c E w (L, 0) i lg ns ws s μ)
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
  obtain ⟨_, -, -, -, H', hHH', hHess', hW, ⟨h1, -⟩ | ⟨-, hall, hψ⟩⟩ := hst
  · simp only [zero_add] at h1
    rw [h0] at h1
    norm_num at h1
  have hHH'' := hHH'.isPerturbedUnitarySimilar
  obtain ⟨V', d', hV', hHV', hκ', hsep'⟩ :=
    hHH''.exists_pseudoConditionNumber_le_and_le_norm_sub hV hHV hκ (by positivity) hgap hiE
  refine ⟨H', hHH'', hHess', hW, hψ, hHH''.specNorm_le.trans hSi, ?_, V', d', hV', hHV',
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
theorem DecoupleLoopCtx.iteration_words {L : ℕ} {w p f : ℕ × ℕ} {ps qs : List ℝ}
    {tL R tv γ Bi α ε : ℝ} {k q : ℕ} {μ : Mem ℝ} (hctx : DecoupleLoopCtx n L w p f ps μ)
    (hps : ps = roundedDecoupleParams tL R tv γ Bi α ε k q ++ qs) :
    μ.Live [w, (p.1, p.2 + 1), (p.1, p.2 + 2), (p.1, p.2 + 3),
      (p.1, p.2 + 4), (p.1, p.2 + 5), (p.1, p.2 + 6), (p.1, p.2 + 7), (p.1, p.2 + 10), f] ∧
      (∀ j < 10, μ.store.get p.1 (p.2 + j) =
        some ((roundedDecoupleParams tL R tv γ Bi α ε k q).getD j 0)) ∧
      μ.store.readBlock p.1 (p.2 + 10) (2 * (excNet ε).length) =
        some ((excNet ε).flatMap fun z => [z.re, z.im]) ∧ f.2 < μ.store.len f.1 := by
  obtain ⟨-, -, -, hl, hp, -, hrf, -, -, -⟩ := hctx
  rw [hps] at hp
  replace hp := Store.readBlock_append_left hp
  have hnet := Store.readBlock_sub hp (o := 10) (n := 2 * (excNet ε).length)
    (by rw [length_roundedDecoupleParams])
  have hfl : (List.flatMap (fun z : ℂ => [z.re, z.im]) (excNet ε)).length =
      2 * (excNet ε).length := by simp [List.length_flatMap, mul_comm]
  refine ⟨?_, fun j hj => Store.get_of_readBlock hp (by rw [length_roundedDecoupleParams]; omega) 0,
    by simpa [roundedDecoupleParams, List.take_of_length_le hfl.le] using hnet, by omega⟩
  simp only [Mem.live_cons] at hl ⊢
  tauto

/-- The words of the small-eigenvalue routine in the decoupling loop: with the parameter words
`NLAlib.ShiftedQR.roundedDecoupleParams` followed by `qs` (none, or $12$), the words `qs` are
stored at the view `P[np - 12]`, apart from the matrix and the flag. -/
theorem DecoupleLoopCtx.routine_words {L : ℕ} {w p f : ℕ × ℕ} {ps qs : List ℝ}
    {tL R tv γ Bi α ε : ℝ} {k q : ℕ} {μ : Mem ℝ} (hctx : DecoupleLoopCtx n L w p f ps μ)
    (hps : ps = roundedDecoupleParams tL R tv γ Bi α ε k q ++ qs)
    (hq12 : qs = [] ∨ qs.length = 12) :
    μ.store.readBlock p.1 (p.2 + (ps.length - 12)) qs.length = some qs ∧
      Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
        (Store.inBlock p.1 (p.2 + (ps.length - 12)) qs.length) := by
  subst hps
  obtain ⟨hq, hsub⟩ := readBlock_tail_twelve hq12 hctx.2.2.2.2.1
  exact ⟨hq, hctx.2.2.2.2.2.2.2.2.2.symm.mono le_rfl
    (Fp.inBlock_le_inBlock (by omega) (by omega))⟩

section Theorems

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

omit [Has IdxTst Q] in
/-- The scan of the decoupling loop: from the state after an iteration, the rounded bottom
scan with the loop's threshold $t_L$ (the first parameter word) reaches the state before the
next round. An entry that passed the iteration's test,
$(1 - \boldsymbol{u})^2\lvert h\rvert^2 \le t$, passes the loop's when
$(1 + \boldsymbol{u})^2 t \le (1 - \boldsymbol{u})^2 t_L$, so a matrix the scan finds coupled has
had its potential contracted.
Also in the tree of `NLAlib.SmallEig.smallEigRoutine`.
A step in the proof of `NLAlib.ShiftedQR.roundedDecoupleIteration_pwrites`,
`NLAlib.ShiftedQR.roundedDecoupleLoop_pwrites`. -/
theorem roundedDecoupleScan_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u < 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {μ : Mem ℝ} {k L : ℕ}
    (hk : k ≤ n) {w q f : ℕ × ℕ} {ps : List ℝ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {tL tv c E : ℝ} {i : ℕ} (hps : ps.getD 0 0 = tL) (hps0 : 0 < ps.length)
    (hthr : (1 + u) ^ 2 * tv ≤ (1 - u) ^ 2 * tL) (hctx : DecoupleLoopCtx n L w q f ps μ)
    {lg : ℕ × ℕ} {ns ws s : ℕ} (hlgL : lg.1 ≠ L)
    (hmid : DecoupleLoopMid u k H tv c E w i lg ns ws s μ) :
    Writes .total I τ (bottomScan (O := O) (Q := Q)) (Env.frame [n + 1, k] [w, q, (L, 0)])
      (Store.inBlock L 0 5)
      (fun μ' => DecoupleLoopCtx n L w q f ps μ' ∧
          DecoupleLoopState u k H tL c E w (L, 0) i lg ns ws s μ')
      μ := by
  have hu := hM.roundoff_nonneg
  obtain ⟨hw, hq, hf, hl, hp, hrw, hrf, hrL, hWF, hPWF⟩ := id hctx
  obtain ⟨Ls, hLs, hpl, hlog, H', hHH', hHess', hW, hdec⟩ := hmid
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
  refine ⟨hctx.of_eqOff (by simp) hfr, Ls, hLs, hpl,
    hfr.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (Fp.disj_inBlock_of_ne (Ne.symm hlgL)) hlog,
    H', hHH', hHess', hW.of_eqOff hfr hRW, ?_⟩
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

/-- The outcomes of a round of the decoupling loop form a measurable set: the pairs of a
memory before and after with the frame `F`, an initialised matrix at `w` after, and the matrix
read after an upper Hessenberg perturbed unitary similarity of the loop's input $\mathbf{H}$ with
error $\varepsilon$ by the unitary of the log read after, decoupled at the bottom (a bottom
subdiagonal entry with $(1 - \boldsymbol{u})^2\lvert h\rvert^2 \le t$) or with potential at most
$c\,\psi_k(\mathbf{H})$, and the log after holding `j` closed slots with planes below $n$
(`NLAlib.measurableSet_exists_holdsSlottedLog_append`). -/
theorem measurableSet_decoupleRoundOutcome (u : ℝ) (k : ℕ)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (tv c ε : ℝ) (w lg : ℕ × ℕ) (ns ws j : ℕ)
    (F : Fp) :
    MeasurableSet {x : Mem ℝ × Mem ℝ | x.1.store.EqOff F x.2.store ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (x.2.store.get w.1 (w.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilarBy
        (givensLog (n + 1) (slotEntries ws (slottedLogRead lg ns ws x.2.store))) H
        (storedMatrix w (n + 1) (n + 1) x.2.store) ε ∧
      IsUpperHessenberg (storedMatrix w (n + 1) (n + 1) x.2.store) ∧
      ((∃ i : Fin n, n ≤ (i : ℕ) + k ∧
          (1 - u) ^ 2 * ‖storedMatrix w (n + 1) (n + 1) x.2.store i.succ i.castSucc‖ ^ 2 ≤ tv) ∨
        hessenbergPotential k (storedMatrix w (n + 1) (n + 1) x.2.store) ≤
          c * hessenbergPotential k H) ∧
      ∃ Ls : List (Option (List GivensEntry)), Ls.length = j ∧
        (∀ e ∈ slotEntries ws Ls, e.1 + 1 < n + 1) ∧
        HoldsSlottedLog lg ns ws ([] ++ Ls) [] x.2.store} := by
  have hm := measurable_storedMatrix w (n + 1) (n + 1)
  have h2 : Measurable fun x : Mem ℝ × Mem ℝ => storedMatrix w (n + 1) (n + 1) x.2.store :=
    hm.comp measurable_snd
  have hV : Measurable fun x : Mem ℝ × Mem ℝ =>
      givensLog (n + 1) (slotEntries ws (slottedLogRead lg ns ws x.2.store)) :=
    (measurable_givensLog_slottedLogRead lg ns ws (n + 1)).comp measurable_snd
  have hent (i j : Fin (n + 1)) : Measurable fun x : Mem ℝ × Mem ℝ =>
      storedMatrix w (n + 1) (n + 1) x.2.store i j := (Matrix.measurable_apply i j).comp h2
  have hpot : Measurable fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => hessenbergPotential k A :=
    (Finset.measurable_prod _ fun i _ =>
      ((Matrix.measurable_apply i.succ i.castSucc).norm)).pow_const _
  simp only [Set.ofPred_and, Set.ofPred_or]
  refine (Mem.measurableSet_eqOff F).inter ((measurable_snd (measurableSet_forall_isSome w _)).inter
    (((isClosed_setOf_isPerturbedUnitarySimilarBy ε).measurableSet.preimage
      (hV.prodMk (measurable_const.prodMk h2))).inter
      ((?_ : MeasurableSet _).inter (((?_ : MeasurableSet _).union
        (measurableSet_le (hpot.comp h2) measurable_const)).inter
          (measurable_snd
            (measurableSet_exists_holdsSlottedLog_append lg ns ws (n + 1) j []))))))
  · simp only [IsUpperHessenberg, Set.ofPred_forall]
    refine .iInter fun i => .iInter fun j => ?_
    by_cases hij : (j : ℕ) + 1 < i
    · simpa [hij] using measurableSet_eq_fun (hent i j) measurable_const
    · simp [hij]
  · simp only [Set.ofPred_exists, Set.ofPred_and]
    exact .iUnion fun i => (MeasurableSet.const _).inter
      (measurableSet_le (((hent _ _).norm.pow_const 2).const_mul _) measurable_const)

/-- The constants of an iteration of the decoupling loop are nonnegative: $1 + C \ge 0$ and
$(1 + 300(n + 1)^2\boldsymbol{u})^k - 1 \ge 0$. -/
theorem decoupleIteration_consts {u B Bi α C : ℝ} {k q : ℕ}
    {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hu : 0 ≤ u) (hV : IsUnit V)
    (hκ : pseudoConditionNumber V ≤ 2 * B) (hBi : 4 * B ≤ Bi)
    (hα : α = (1.01 * Bi) ^ ((4 * q : ℝ) / 2 ^ q))
    (hC1 : 1.1 + 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
      (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
        Bi ^ ((k : ℝ)⁻¹)) ≤ C) :
    0 ≤ 1 + C ∧ 0 ≤ (1 + 300 * (n + 1) ^ 2 * u) ^ k - 1 := by
  have hB0 : 1 / 2 ≤ B := by
    have := (one_le_pseudoConditionNumber hV.ne_zero).trans hκ
    linarith
  have hBi0 : 0 ≤ Bi := by linarith
  have hα0 : 0 ≤ α := hα ▸ Real.rpow_nonneg (by positivity) _
  refine ⟨?_, ?_⟩
  · have : 0 ≤ 2.1 * ((2.002 : ℝ) ^ ((k : ℝ)⁻¹) *
        (1.01 * (0.998 : ℝ) ^ (-(k : ℝ)⁻¹) * (2 * Bi ^ 4) ^ ((2 * k : ℝ)⁻¹)) * α *
          Bi ^ ((k : ℝ)⁻¹)) := by positivity
    linarith
  · have : 1 ≤ (1 + 300 * ((n : ℝ) + 1) ^ 2 * u) ^ k := one_le_pow₀ (by nlinarith)
    linarith

/-- The views of an iteration in the parameter words of the decoupling loop are apart from the
matrix and the flag. -/
theorem decoupleIteration_views {w p f : ℕ × ℕ} {ps qs : List ℝ} {ε : ℝ}
    (hPWF : Fp.Disj (Store.inBlock p.1 p.2 ps.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1))
    (hlen : ps.length = 10 + 2 * (excNet ε).length + qs.length)
    (hq12 : qs = [] ∨ qs.length = 12) :
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock p.1 (p.2 + (ps.length - 12)) qs.length) ∧
    Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (Store.inBlock (p.1, p.2 + 1).1 (p.1, p.2 + 1).2 1 ⊔
        Store.inBlock (p.1, p.2 + 2).1 (p.1, p.2 + 2).2 1 ⊔
        Store.inBlock (p.1, p.2 + 3).1 (p.1, p.2 + 3).2 1 ⊔
        Store.inBlock (p.1, p.2 + 4).1 (p.1, p.2 + 4).2 1 ⊔
        Store.inBlock (p.1, p.2 + 5).1 (p.1, p.2 + 5).2 1 ⊔
        Store.inBlock (p.1, p.2 + 6).1 (p.1, p.2 + 6).2 1 ⊔
        Store.inBlock (p.1, p.2 + 7).1 (p.1, p.2 + 7).2 1 ⊔
        Store.inBlock (p.1, p.2 + 10).1 (p.1, p.2 + 10).2 (2 * (excNet ε).length)) := by
  refine ⟨?_, hPWF.symm.mono le_rfl (by rw [hlen]; fp_sub)⟩
  rcases hq12 with rfl | h
  · exact fun _ _ _ h => by obtain ⟨-, h1, h2⟩ := h; simp at h2; omega
  · exact hPWF.symm.mono le_rfl (Fp.inBlock_le_inBlock (by omega) (by omega))

/-- An outcome of the iteration of round $i$, from the state of the loop before it (the log `LL`
of $is$ slots, the iterate $\mathbf{H}_1$ by its unitary from $\mathbf{H}$ with error $iE$ and
potential at most $c^i\psi_k(\mathbf{H})$, $c = 1.002(1 - \gamma)$), is an outcome of the round in
the measurable form of `NLAlib.ShiftedQR.measurableSet_decoupleRoundOutcome`. -/
theorem mem_decoupleRoundOutcome {u : ℝ} {k : ℕ} {H H₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {γ tv E E' : ℝ} {w lg : ℕ × ℕ} {ns ws i s : ℕ} {LL : List (Option (List GivensEntry))}
    {F : Fp} {m m' : Mem ℝ} (hLL : LL.length = i * s)
    (hby : IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries ws LL)) H H₁ (i * E))
    (hpl : ∀ e ∈ slotEntries ws LL, e.1 + 1 < n + 1)
    (hψ : hessenbergPotential k H₁ ≤ (1.002 * (1 - γ)) ^ i * hessenbergPotential k H)
    (hc0 : 0 ≤ 1.002 * (1 - γ)) (hE' : E' ≤ E) (hfr : m.store.EqOff F m'.store)
    (hO : ShIterationOutcomeBy u k H₁ γ tv E' w lg ns ws LL s m') :
    m.store.EqOff F m'.store ∧
      (∀ j < 2 * ((n + 1) * (n + 1)), (m'.store.get w.1 (w.2 + j)).isSome) ∧
      IsPerturbedUnitarySimilarBy
        (givensLog (n + 1) (slotEntries ws (slottedLogRead lg ns ws m'.store))) H
        (storedMatrix w (n + 1) (n + 1) m'.store) ((i + 1) * E) ∧
      IsUpperHessenberg (storedMatrix w (n + 1) (n + 1) m'.store) ∧
      ((∃ j : Fin n, n ≤ (j : ℕ) + k ∧
          (1 - u) ^ 2 * ‖storedMatrix w (n + 1) (n + 1) m'.store j.succ j.castSucc‖ ^ 2 ≤ tv) ∨
        hessenbergPotential k (storedMatrix w (n + 1) (n + 1) m'.store) ≤
          (1.002 * (1 - γ)) ^ (i + 1) * hessenbergPotential k H) ∧
      ∃ Ls : List (Option (List GivensEntry)), Ls.length = (i + 1) * s ∧
        (∀ e ∈ slotEntries ws Ls, e.1 + 1 < n + 1) ∧
        HoldsSlottedLog lg ns ws ([] ++ Ls) [] m'.store := by
  obtain ⟨Ls, hLs, hplLs, hlog', H'', hby', hHess'', hW'', hdec''⟩ := hO
  rw [← hW''.eq_storedMatrix]
  refine ⟨hfr, fun j hj => by rw [Store.get_of_readBlock hW'' hj 0]; rfl, ?_, hHess'',
    hdec''.imp id fun h => ?_, LL ++ Ls, by rw [List.length_append, hLL, hLs, ← Nat.succ_mul],
    fun e he => ?_, by rwa [List.nil_append]⟩
  · rw [hlog'.slotEntries_slottedLogRead, slotEntries_append, givensLog_append]
    exact (hby.trans hby').mono (by linarith)
  · calc hessenbergPotential k H'' ≤ 1.002 * (1 - γ) * hessenbergPotential k H₁ := h
      _ ≤ 1.002 * (1 - γ) * ((1.002 * (1 - γ)) ^ i * hessenbergPotential k H) :=
        mul_le_mul_of_nonneg_left hψ hc0
      _ = (1.002 * (1 - γ)) ^ (i + 1) * hessenbergPotential k H := by ring
  · rw [slotEntries_append, List.mem_append] at he
    exact he.elim (hpl e) (hplLs e)

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
/-- The exit of the decoupling loop: from the state before round $i \le F$ at the cap or
with a scan that passed, the loop sets the flag to $0$ and holds an upper Hessenberg perturbed
unitary similarity with error $FE$ and a bottom entry of modulus at most $\omega_D$
($t_L \le (1 - \boldsymbol{u})^2\omega_D^2$). At the cap the scan has passed: a coupled matrix
has $\psi_k \le c^F\psi_k(\mathbf{H}) \le c^F N_{\max}$, and one of its bottom entries is at most
$\psi_k$, which fails the loop's test when $(1 + \boldsymbol{u})^2(c^F N_{\max})^2 \le t_L$.
Also in the tree of `NLAlib.SmallEig.smallEigRoutine`.
Shared by the trees of `NLAlib.ShiftedQR.roundedDecoupleLoopWith`,
`NLAlib.SmallEig.decoupleLast`. -/
theorem roundedDecoupleExit_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} (hu1 : u < 1)
    (hL : IsIndexLit M I) (hC : IsCmp id I) (h0lit : M.lit (0 : ℚ) = 0) {τ : Tape ℝ}
    {μ : Mem ℝ} {k L i F : ℕ} (hk : 0 < k) (hkn : k ≤ n) {w p f : ℕ × ℕ} {ps : List ℝ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {tL c E ωD Nmax : ℝ}
    (hcut : tL ≤ (1 - u) ^ 2 * ωD ^ 2) (hωD : 0 ≤ ωD) (hc0 : 0 ≤ c) (hE0 : 0 ≤ E)
    (hψH : hessenbergPotential k H ≤ Nmax) (hfuel : (1 + u) ^ 2 * (c ^ F * Nmax) ^ 2 ≤ tL)
    (hiF : i ≤ F) (hctx : DecoupleLoopCtx n L w p f ps μ)
    {lg : ℕ × ℕ} {ns ws s : ℕ}
    (hst : DecoupleLoopState u k H tL c E w (L, 0) i lg ns ws s μ)
    (hend : i = F ∨ I.test (Has.inj CmpTst.isZero) [] [(L, 3)] μ = some false) :
    Writes .total I τ (roundedDecoupleExit (O := O) (Q := Q)) (Env.frame [] [(L, 0), f])
      (Store.inBlock f.1 f.2 1)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        IsPerturbedUnitarySimilar H H' (F * E) ∧ IsUpperHessenberg H' ∧
        (∃ j : Fin n, n ≤ (j : ℕ) + k ∧ ‖H' j.succ j.castSucc‖ ≤ ωD) ∧
        HoldsMatrix w H' μ'.store) μ := by
  have hp1 : 0 < (1 - u) ^ 2 := by nlinarith
  obtain ⟨_, -, -, -, H', hHH', hHess', hW', ⟨h1, j, hj, hjt⟩ | ⟨h0, hall, hψ⟩⟩ := hst
  · simp only [zero_add] at h1
    refine writes_ite (a := [(L, 3)]) rfl rfl (hC.test_isPos h1) ?_
    rw [if_pos (by simp)]
    refine (writes_indexLit hL rfl rfl (by have := hctx.2.2.2.2.2.2.1; omega)).mono le_rfl ?_
    rintro μ' hfr ⟨-, hF⟩
    have hh : (1 - u) ^ 2 * ‖H' j.succ j.castSucc‖ ^ 2 ≤ (1 - u) ^ 2 * ωD ^ 2 := hjt.trans hcut
    exact ⟨by simpa [h0lit] using hF, H', hHH'.isPerturbedUnitarySimilar.mono
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

omit [Has ScalarOp O] [Has IdxTst Q] in
/-- The exit of the decoupling loop on any scan flag: on every tape, from any word at `r[3]`
and room for the flag `f`, `NLAlib.ShiftedQR.roundedDecoupleExit` writes only the flag and
stores a word there.
Also in the tree of `NLAlib.SmallEig.smallEigRoutine`.
Shared by the trees of `NLAlib.ShiftedQR.roundedDecoupleLoopWith`,
`NLAlib.SmallEig.decoupleLast`. -/
theorem roundedDecoupleExit_writes_word {M : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit M I) (hC : IsCmp id I) {τ : Tape ℝ} {μ : Mem ℝ} {r f : ℕ × ℕ} {x : ℝ}
    (hx : μ.store.get r.1 (r.2 + 3) = some x) (hf : f.2 < μ.store.len f.1) :
    Writes .total I τ (roundedDecoupleExit (O := O) (Q := Q)) (Env.frame [] [r, f])
      (Store.inBlock f.1 f.2 1) (fun μ' => ∃ x, μ'.store.get f.1 f.2 = some x) μ := by
  unfold roundedDecoupleExit
  refine writes_ite (a := [(r.1, r.2 + 3)]) rfl rfl (hC.test_isPos hx) ?_
  split_ifs <;>
  · refine (writes_indexLit hL rfl rfl hf).mono le_rfl ?_
    rintro μ' - ⟨-, hF⟩
    exact ⟨_, hF⟩

end Theorems

section Iteration

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has EigenvalueKernelOp O]
  [Has DiskSampleOp O] [Has CmpTst Q] [Has IdxTst Q]

-- The hypothesis list of the iteration, with its long real constants, makes elaboration heavy.
set_option maxHeartbeats 1000000 in
-- (the reason is stated above)
omit [Has EigenvalueKernelOp O] in
/-- One iteration of the decoupling loop on the good tapes: from the state before round $i$
with the scan flag $0$, the iterate is in the class of `NLAlib.ShiftedQR.shIteration_pwrites`
(condition at most $4B \le B_i$ and separation at least $g/4 \ge 2\omega^2/S$ by
`NLAlib.IsPerturbedUnitarySimilar.exists_pseudoConditionNumber_le_and_le_norm_sub`, norm at most
$\|\mathbf{H}\|_2 + iE \le S$, and $\psi_k \ge \omega$ because every bottom entry failed the
loop's test), so the iteration reaches the state after round $i$ except with probability at most
$\varphi_{\mathrm{se}} + \varphi_R/2 + \varphi$. One good set serves every iterate
(`NLAlib.Ops.PWrites.pstep_of_forall`).
A step in the proof of `NLAlib.ShiftedQR.roundedDecoupleWith_randomDecouplingRoutineContract_at`. -/
theorem roundedDecoupleIteration_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u < 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) (hQ : IsToNat id I)
    {law : ℕ → Measure ℝ} {s₀ : ℕ} {β φse : ℝ}
    (hβ0 : 0 ≤ β) (hφse : 0 ≤ φse) (hDisk : IsPolarDiskSampler s₀ I)
    (hU : law s₀ = volume.restrict (Set.Icc 0 1)) {k q L i : ℕ} (hkq : k = 2 ^ q) (hk : 2 ≤ k)
    (hkn : k ≤ n) {w p f lg : ℕ × ℕ} {ns ws : ℕ} {ps qs : List ℝ}
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ}
    {B g Bi S ω tL tv R φR α γ φ C ε E : ℝ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (hκ : pseudoConditionNumber V ≤ 2 * B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g / 2 ≤ ‖d i - d j‖)
    (hiE : i * E ≤ g / 2 / (16 * (n + 1) * (2 * B))) (hSi : specNorm H + i * E ≤ S)
    (hE : (1 + C) * S * ((1 + 300 * (n + 1) ^ 2 * u) ^ k - 1) ≤ E)
    (hps : ps = roundedDecoupleParams tL R tv γ Bi α ε k q ++ qs) (hBi : 4 * B ≤ Bi)
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
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) {T : ℕ} {SE : Stmt O Q}
    (hj : (i + 1) * (k + 1 + (excNet ε).length) ≤ ns) (hw : k * n ≤ ws)
    (hlgv : ∀ b ∈ [w, p, f], b.1 ≠ lg.1)
    (hSE : RandomSmallEigContractAt law β φse k 12 T S qs SE I) (hq12 : qs = [] ∨ qs.length = 12) :
    PWrites law I (shIterationWith SE)
      (Env.frame [n + 1, q, k, (excNet ε).length, 12, T, ws, i * (k + 1 + (excNet ε).length)]
          [w, (p.1, p.2 + 1), (p.1, p.2 + 2),
        (p.1, p.2 + 3), (p.1, p.2 + 4), (p.1, p.2 + 5), (p.1, p.2 + 6), (p.1, p.2 + 7),
        (p.1, p.2 + 10), (p.1, p.2 + (ps.length - 12)), w, f, lg])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))
      (fun μ => DecoupleLoopCtx n L w p f ps μ ∧
        DecoupleLoopState u k H tL (1.002 * (1 - γ)) E w (L, 0) i lg ns ws
            (k + 1 + (excNet ε).length) μ ∧
        μ.store.get L 3 = some 0)
      (fun μ' => DecoupleLoopCtx n L w p f ps μ' ∧
        DecoupleLoopMid u k H tv (1.002 * (1 - γ)) E w (i + 1) lg ns ws
            (k + 1 + (excNet ε).length) μ') (φse + φR / 2 + φ) := by
  have hφ0 : 0 ≤ φse + φR / 2 + φ := by positivity
  by_cases hD : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock f.1 f.2 1) ∧ Fp.Disj (Store.inBlock p.1 p.2 ps.length)
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
  swap
  · exact PWrites.of_writes hφ0 fun μ _ h => absurd ⟨h.1.2.2.2.2.2.2.2.2.1,
      h.1.2.2.2.2.2.2.2.2.2⟩ hD
  obtain ⟨haf, hPWF⟩ := hD
  obtain ⟨hqw, hio⟩ := decoupleIteration_views hPWF
    (by rw [hps, List.length_append, length_roundedDecoupleParams]) hq12
  obtain ⟨hC0, hcu⟩ := decoupleIteration_consts (n := n) (k := k) hM.roundoff_nonneg hV hκ hBi hα
    hC1
  have hc0 : 0 ≤ 1.002 * (1 - γ) := by nlinarith
  have hpl : p.1 ≠ lg.1 := hlgv p (by simp)
  have hlgv' : ∀ b ∈ [w, (p.1, p.2 + 1), (p.1, p.2 + 2), (p.1, p.2 + 3), (p.1, p.2 + 4),
      (p.1, p.2 + 5), (p.1, p.2 + 6), (p.1, p.2 + 7), (p.1, p.2 + 10),
      (p.1, p.2 + (ps.length - 12)), f], b.1 ≠ lg.1 := by
    intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact hpl | exact hlgv _ (by simp)
  let ι := {x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ × List (Option (List GivensEntry)) //
    IsUpperHessenberg x.1 ∧ specNorm x.1 ≤ S ∧ ω ≤ hessenbergPotential k x.1 ∧
    (∃ (Vx : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (dx : Fin (n + 1) → ℂ), IsUnit Vx ∧
      x.1 * Vx = Vx * Matrix.diagonal dx ∧ pseudoConditionNumber Vx ≤ Bi ∧
      ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖dx i - dx j‖) ∧
    x.2.length = i * (k + 1 + (excNet ε).length) ∧
    IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries ws x.2)) H x.1 (i * E) ∧
    (∀ e ∈ slotEntries ws x.2, e.1 + 1 < n + 1) ∧
    hessenbergPotential k x.1 ≤ (1.002 * (1 - γ)) ^ i * hessenbergPotential k H}
  have hst := PWrites.pstep_of_forall hI hloc (fun x : ι => by
    have hx := x.2.2.2.2.1.choose_spec.choose_spec
    have h := shIterationWith_pwrites_at hI hloc hS hM hu1.le hL hNat hC hQ hβ0 hφse hDisk hU hkq
      hk hkn haf hio x.2.1 hx.1 hx.2.1 hx.2.2.1 hBk hω x.2.2.2.1 x.2.2.1 hx.2.2.2 hR hφR hφR1 hβ
      hdη hnu huo huo1 hxuR hboundR hα hγ hγ1 hε hε2 hφ hφ1 hd hC1 hxu hbound hexc1 hexc2 hthrω hSE
      (qw := (p.1, p.2 + (ps.length - 12))) hqw (LL := x.1.2) (lg := lg) (ns := ns)
      (by rw [x.2.2.2.2.2.1, ← Nat.succ_mul]; exact hj) hw hlgv'
    rw [x.2.2.2.2.2.1] at h
    exact h)
    (measurableSet_decoupleRoundOutcome (n := n) u k H tv ((1.002 * (1 - γ)) ^ (i + 1))
      ((i + 1) * E) w lg ns ws ((i + 1) * (k + 1 + (excNet ε).length))
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws))))
    (fun x m m' hP hfr hO => ?_)
  · refine PStep.mono hst (fun μ ⟨hctx, hstate, h0⟩ => ?_)
      (fun μ μ' ⟨hctx, hstate, h0⟩ hT => ?_) le_rfl
    · obtain ⟨H', -, hHess', hW, -, hnorm, hψω, V', d', hV', hHV', hκ', hsep'⟩ :=
        hstate.exists_iterate h0 (by omega) hkn hV hHV hκ hg hgap hiE hSi hBi hωL hgapS
      obtain ⟨Ls, hLs, hplL, hlog, H₁, hby, -, hW₁, hdec₁⟩ := hstate
      have hHH : H₁ = H' := by rw [hW₁.eq_storedMatrix, hW.eq_storedMatrix]
      subst hHH
      have hψ : hessenbergPotential k H₁ ≤ (1.002 * (1 - γ)) ^ i * hessenbergPotential k H := by
        rcases hdec₁ with ⟨h1, -⟩ | ⟨-, -, hψ⟩
        · simp only [zero_add] at h1
          rw [h0] at h1
          norm_num at h1
        · exact hψ
      obtain ⟨hl, hget, hnet, hf⟩ := hctx.iteration_words hps
      have hlgl : lg.1 < μ.store.length := by
        have : i * (k + 1 + (excNet ε).length) < ns :=
          (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self i) (by omega)).trans_le hj
        exact Store.lt_length_of_get (hlog.2.2.2.1 (by rw [hLs]; exact this)).1
      refine ⟨⟨(H₁, Ls), hHess', hnorm, hψω, ⟨V', d', hV', hHV', hκ', hsep'⟩, hLs, hby, hplL, hψ⟩,
        ?_, hW, (hctx.routine_words hps hq12).1, hget 1 (by omega),
        hget 2 (by omega), hget 3 (by omega), hget 4 (by omega), hget 5 (by omega),
        hget 6 (by omega), hget 7 (by omega), hnet, hf, hlog, by simpa [Mem.Live] using hlgl⟩
      have hpl' : p.1 < μ.store.length := hctx.2.2.2.1 p (by simp)
      simp only [Mem.live_cons] at hl ⊢
      tauto
    · obtain ⟨hfr, hsome, hby, hHess, hdec, Ls, hLs, hplLs, hlog⟩ := hT
      rw [List.nil_append] at hlog
      refine ⟨hfr, hctx.of_eqOff_log hpl (sup_le (le_sup_left.trans le_sup_left)
        le_sup_right) hfr, Ls, hLs, hplLs, hlog, storedMatrix w (n + 1) (n + 1) μ'.store,
        ?_, hHess, holdsMatrix_storedMatrix hsome, hdec⟩
      rw [← hlog.slotEntries_slottedLogRead]
      exact hby.mono (le_of_eq (by push_cast; ring))
  exact mem_decoupleRoundOutcome x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.1
    x.2.2.2.2.2.2.2.2 hc0 (by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left x.2.2.1 hC0) hcu
      linarith) hfr hO

omit [Has EigenvalueKernelOp O] in
/-- The rounds of the decoupling loop on the good tapes: if each iteration from the state
before round $i < F$ with the scan flag $0$ reaches the state after it except with probability
at most $\varphi \ge 0$, then from a stored upper Hessenberg $\mathbf{H}$ with
$\psi_k(\mathbf{H}) \le N_{\max}$ the initial scan, the at most $F$ rounds (iteration and scan,
`NLAlib.ShiftedQR.roundedDecoupleScan_writes`) and the exit
(`NLAlib.ShiftedQR.roundedDecoupleExit_writes`) set the flag to $0$ and hold an upper Hessenberg
perturbed unitary similarity with error $FE$ and a bottom entry of modulus at most $\omega_D$,
except with probability at most $F\varphi$ (`NLAlib.Ops.PWrites.whileFuel`).
A step in the proof of `NLAlib.ShiftedQR.roundedDecoupleWith_randomDecouplingRoutineContract_at`. -/
theorem roundedDecoupleLoop_pwrites {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u < 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {law : ℕ → Measure ℝ}
    {k q n0 F L T : ℕ} {SE : Stmt O Q} (hk : 0 < k)
        (hkn : k ≤ n) {w p f lg : ℕ × ℕ} {ns ws : ℕ} {ps : List ℝ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {tL tv c E ωD Nmax φ : ℝ}
    (hps : ps.getD 0 0 = tL) (hps0 : 0 < ps.length) (hHess : IsUpperHessenberg H)
    (hψH : hessenbergPotential k H ≤ Nmax) (hthr : (1 + u) ^ 2 * tv ≤ (1 - u) ^ 2 * tL)
    (hcut : tL ≤ (1 - u) ^ 2 * ωD ^ 2) (hωD : 0 ≤ ωD) (hc0 : 0 ≤ c) (hE0 : 0 ≤ E)
    (hφ : 0 ≤ φ) (hfuel : (1 + u) ^ 2 * (c ^ F * Nmax) ^ 2 ≤ tL)
    (hj : F * (k + 1 + n0) ≤ ns) (hlgv : ∀ b ∈ [w, p, f], b.1 ≠ lg.1)
    (hlgL : lg.1 < L)
    (hit : ∀ i < F, PWrites law I (shIterationWith SE)
      (Env.frame [n + 1, q, k, n0, 12, T, ws, i * (k + 1 + n0)]
          [w, (p.1, p.2 + 1), (p.1, p.2 + 2), (p.1, p.2 + 3),
        (p.1, p.2 + 4), (p.1, p.2 + 5), (p.1, p.2 + 6), (p.1, p.2 + 7), (p.1, p.2 + 10),
        (p.1, p.2 + (ps.length - 12)), w, f, lg])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))
      (fun μ => DecoupleLoopCtx n L w p f ps μ ∧
          DecoupleLoopState u k H tL c E w (L, 0) i lg ns ws (k + 1 + n0) μ ∧
        μ.store.get L 3 = some 0)
      (fun μ' => DecoupleLoopCtx n L w p f ps μ' ∧
          DecoupleLoopMid u k H tv c E w (i + 1) lg ns ws (k + 1 + n0) μ')
      φ) :
    PWrites law I (roundedDecoupleLoopWith SE)
      (Env.frame [n + 1, k, ps.length, F, T, q, n0, ws] [w, p, (L, 0), w, f, lg])
      (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock L 0 5 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))
      (fun μ => DecoupleLoopCtx n L w p f ps μ ∧ HoldsMatrix w H μ.store ∧
        HoldsSlottedLog lg ns ws [] [] μ.store)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ (Ls : List (Option (List GivensEntry))) (H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
        Ls.length = ns ∧ (∀ x ∈ slotEntries ws Ls, x.1 + 1 < n + 1) ∧
        HoldsSlottedLog lg ns ws Ls [] μ'.store ∧
        IsPerturbedUnitarySimilarBy (givensLog (n + 1) (slotEntries ws Ls)) H H' (F * E) ∧
            IsUpperHessenberg H' ∧
        (∃ j : Fin n, n ≤ (j : ℕ) + k ∧ ‖H' j.succ j.castSucc‖ ≤ ωD) ∧
        HoldsMatrix w H' μ'.store) (F * φ) := by
  have h0lit : M.lit (0 : ℚ) = 0 := by simpa using hNat 0 (Nat.zero_le _)
  have hlive3 : ∀ μ, DecoupleLoopCtx n L w p f ps μ → μ.Live [w, p, (L, 0)] := fun μ h =>
    h.2.2.2.1.mono (by simp)
  have hlgL' : lg.1 ≠ L := by omega
  have hpl : p.1 ≠ lg.1 := hlgv p (by simp)
  have hfl : f.1 ≠ lg.1 := hlgv f (by simp)
  unfold roundedDecoupleLoopWith
  refine (PWrites.seq (φ₁ := 0) hI hloc (by positivity) ?scan
    (PWrites.whileFuel (F := Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock f.1 f.2 1 ⊔ Store.inBlock L 0 5 ⊔ Store.inBlock lg.1 lg.2 (ns * (1 + 5 * ws)))
      (G := Store.inBlock f.1 f.2 1) (N := F) hI hloc rfl
      (fun i μ => DecoupleLoopCtx n L w p f ps μ ∧
        DecoupleLoopState u k H tL c E w (L, 0) i lg ns ws (k + 1 + n0) μ)
      (fun _ => φ) (fun _ _ => hφ) le_rfl (fun _ h => h) ?test ?body ?exit)).mono (fun _ h => h)
    (sup_le (le_sup_of_le_left le_sup_right) (sup_le le_rfl
      (le_sup_of_le_left (le_sup_of_le_left le_sup_right)))) (fun _ h => h) ?phi
  case scan =>
    exact (PWrites.of_writes le_rfl fun μ τ ⟨hctx, hW, hlog⟩ =>
      roundedDecoupleScan_writes (τ := τ) (i := 0) (tv := tv) (E := E) (c := c) hS hM hu1 hL
        hNat hC hkn hps hps0 hthr hctx hlgL' ⟨[], by simp, by simp [slotEntries], hlog, H,
          by simpa [slotEntries] using IsPerturbedUnitarySimilarBy.refl H,
          hHess, hW, Or.inr (by simp)⟩).in_frame rfl rfl fun μ h => hlive3 μ h.1
  case phi =>
    simp only [zero_add, add_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact le_rfl
  case test =>
    rintro i - μ ⟨-, _, -, -, -, H', -, -, -, ⟨h1, -⟩ | ⟨h0, -⟩⟩
    · simp only [zero_add] at h1
      exact ⟨_, (Interp.testAt_eq (a := [(L, 3)]) rfl rfl).trans (hC.test_isZero h1)⟩
    · simp only [zero_add] at h0
      exact ⟨_, (Interp.testAt_eq (a := [(L, 3)]) rfl rfl).trans (hC.test_isZero h0)⟩
  case body =>
    intro i hi
    refine (PWrites.seq hI hloc le_rfl ((hit i hi).in_frame rfl rfl fun μ h => ?_)
      ((PWrites.of_writes le_rfl fun μ τ ⟨hctx, hmid⟩ =>
        roundedDecoupleScan_writes (τ := τ) hS hM hu1 hL hNat hC hkn hps hps0 hthr hctx hlgL'
          hmid).in_frame rfl rfl fun μ h => hlive3 μ h.1)).mono
      (fun μ ⟨⟨hctx, hst⟩, htest⟩ => ⟨hctx, hst, ?_⟩)
      (sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (le_sup_right.trans le_sup_left))
      (fun _ h => h) (by simp)
    · have := h.1.2.2.2.1
      have hlg : lg.1 < μ.store.length := by
        obtain ⟨_, hLs, -, hlog, -⟩ := h.2.1
        have : i * (k + 1 + n0) < ns :=
          (Nat.mul_lt_mul_of_pos_right hi (by omega)).trans_le hj
        exact Store.lt_length_of_get (hlog.2.2.2.1 (by rw [hLs]; exact this)).1
      simp only [Mem.live_cons, Mem.live_nil, and_true] at this ⊢
      tauto
    obtain ⟨_, -, -, -, H', -, -, -, ⟨h1, -⟩ | ⟨h0, -⟩⟩ := hst
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
    obtain ⟨Ls, hLs, hplLs, hlog, H₁, hby, -, hW₁, -⟩ := id hst
    refine (roundedDecoupleExit_writes hu1 hL hC h0lit hk hkn hcut hωD hc0 hE0 hψH hfuel hi hctx
      hst hend).mono le_rfl ?_
    rintro μ' hfr ⟨hf0, H', -, hHess', hdec, hW'⟩
    have hW₁' := hW₁.of_eqOff hfr hctx.2.2.2.2.2.2.2.2.1.symm
    have hHH : H₁ = H' := by rw [hW₁'.eq_storedMatrix, hW'.eq_storedMatrix]
    subst hHH
    have hLn : Ls.length ≤ ns := by
      rw [hLs]; exact (Nat.mul_le_mul_right _ hi).trans hj
    refine ⟨hf0, Ls ++ List.replicate (ns - Ls.length) none, H₁, by simp; omega,
      by rw [slotEntries_append_replicate_none]; exact hplLs,
      (hfr.keep (readsOnly_holdsSlottedLog _ _ _ _ _) (Fp.disj_inBlock_of_ne hfl) hlog).close,
      by rw [slotEntries_append_replicate_none]
         exact hby.mono (mul_le_mul_of_nonneg_right (by exact_mod_cast hi : (i : ℝ) ≤ F) hE0),
      hHess', hdec, hW'⟩

end Iteration
end NLAlib.ShiftedQR
