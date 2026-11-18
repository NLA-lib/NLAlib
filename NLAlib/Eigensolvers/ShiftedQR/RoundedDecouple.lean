/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedHeadline
public import NLAlib.Eigensolvers.ShiftedQR.RoundedIteration
public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveBackward

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

* `NLAlib.ShiftedQR.roundedDecoupleWith`: the program with a small-eigenvalue routine;
  `NLAlib.ShiftedQR.roundedDecouple`: the program with the `SmallEig` kernel;
  `NLAlib.ShiftedQR.roundedDecoupleParams`: its parameter words.
* `NLAlib.ShiftedQR.DecoupleLoopCtx`, `NLAlib.ShiftedQR.DecoupleLoopState`,
  `NLAlib.ShiftedQR.DecoupleLoopMid`: the operands and the states of the loop.

## Main results

* `NLAlib.ShiftedQR.roundedDecoupleScan_writes`,
  `NLAlib.ShiftedQR.roundedDecoupleIteration_pwrites`: the scan and the iteration of a round.
* `NLAlib.ShiftedQR.roundedDecoupleWith_randomDecouplingRoutineContract_at`,
  `NLAlib.ShiftedQR.roundedDecouple_randomDecouplingContract`: the loop meets the randomized
  decoupling contract.
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

/-- The rounds of the decoupling loop with a small-eigenvalue routine, with the scan registers `R`
and the index words $m$ ($k = 2^m$) and $n_0$ (the net size) as dimensions: scan the bottom $k$
subdiagonal entries with the threshold `P[0]`, and while none passed, for at most $F$ rounds, run
`NLAlib.ShiftedQR.shIterationWith` with the words `P[1..7]`, the net at `P[10]`, the routine's
$12$ words as the tail `P[np - 12]` of the parameter words and the cap $T$, recording round $j$'s
$k + 1 + n_0$ trial sites in the slots $j(k + 1 + n_0), \dots$ of the log `Lg` (slot width $w$),
then scan again; then `NLAlib.ShiftedQR.roundedDecoupleExit`. The interface is
`[N, k, np, F, T, m, n0, w] (W, P, R) → (W, Fl, Lg)`. -/
def roundedDecoupleLoopWith (SE : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, T, m, n0, w] (W, P, R) → (W, Fl, Lg) {
    run (bottomScan (O := O) (Q := Q)).body [N, k] (W, P, R);
    while j < F, (Has.inj CmpTst.isZero) [] (R[3]) {
      run (shIterationWith SE).body [N, m, k, n0, 12, T, w, j * (k + 1 + n0)]
        (W, P[1], P[2], P[3], P[4], P[5], P[6], P[7], P[10], P[np - 12], W, Fl, Lg);
      run (bottomScan (O := O) (Q := Q)).body [N, k] (W, P, R)
    } then {
      run (roundedDecoupleExit (O := O) (Q := Q)).body [] (R, Fl)
    }
  }

/-- **The rounded decoupling loop with a small-eigenvalue routine, recording its rotations**
([BanksGarzaVargasSrivastava2022, Lemma 6.4]): allocate the scan registers, read the index words
$m$ ($k = 2^m$) and $n_0$ from `P[8]`, `P[9]`, zero-fill the slotted log `Lg` of `ns` slots of
`w` entries (`NLAlib.slottedLogOpen`), and run `NLAlib.ShiftedQR.roundedDecoupleLoopWith`. The
interface is `[N, k, np, F, T, ns, w] (W, P) → (W, Fl, Lg)`, that of the decoupling routine of
`NLAlib.ShiftedQR.solveRoundedWith`; it needs $F(k + 1 + n_0) \le n_s$ and $k(N - 1) \le w$. -/
def roundedDecoupleWith (SE : Impl O Q) : Impl O Q :=
  opsImpl% [N, k, np, F, T, ns, w] (W, P) → (W, Fl, Lg) {
    let R ← alloc 5;
    let m ← index (Has.inj IdxTst.toNat) (P[8]) ≤ k;
    let n0 ← index (Has.inj IdxTst.toNat) (P[9]) ≤ np;
    run (slottedLogOpen (O := O) (Q := Q)).body [ns, w] (Lg);
    run (roundedDecoupleLoopWith SE).body [N, k, np, F, T, m, n0, w] (W, P, R, W, Fl, Lg)
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
        pseudoConditionNumber Vx ≤ Bi ∧ ∀ i j, i ≠ j → 2 * ω ^ 2 / S ≤ ‖dx i - dx j‖ := sorry

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
had its potential contracted. -/
theorem roundedDecoupleScan_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu1 : u < 1) (hL : IsIndexLit M I)
    (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I) {τ : Tape ℝ} {μ : Mem ℝ} {k L : ℕ}
    (hk : k ≤ n) {w q f : ℕ × ℕ} {ps : List ℝ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {tL tv c E : ℝ} {i : ℕ} (hps : ps.getD 0 0 = tL) (hps0 : 0 < ps.length)
    (hthr : (1 + u) ^ 2 * tv ≤ (1 - u) ^ 2 * tL) (hctx : DecoupleLoopCtx n L w q f ps μ)
    {lg : ℕ × ℕ} {ns ws s : ℕ}
    (hmid : DecoupleLoopMid u k H tv c E w i lg ns ws s μ) :
    Writes .total I τ (bottomScan (O := O) (Q := Q)).body (Env.frame [n + 1, k] [w, q, (L, 0)])
      (Store.inBlock L 0 5)
      (fun μ' => DecoupleLoopCtx n L w q f ps μ' ∧
          DecoupleLoopState u k H tL c E w (L, 0) i lg ns ws s μ')
      μ := sorry

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
$\psi_k$, which fails the loop's test when $(1 + \boldsymbol{u})^2(c^F N_{\max})^2 \le t_L$. -/
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
    Writes .total I τ (roundedDecoupleExit (O := O) (Q := Q)).body (Env.frame [] [(L, 0), f])
      (Store.inBlock f.1 f.2 1)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧ ∃ H' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        IsPerturbedUnitarySimilar H H' (F * E) ∧ IsUpperHessenberg H' ∧
        (∃ j : Fin n, n ≤ (j : ℕ) + k ∧ ‖H' j.succ j.castSucc‖ ≤ ωD) ∧
        HoldsMatrix w H' μ'.store) μ := sorry

omit [Has ScalarOp O] [Has IdxTst Q] in
/-- The exit of the decoupling loop on any scan flag: on every tape, from any word at `r[3]`
and room for the flag `f`, `NLAlib.ShiftedQR.roundedDecoupleExit` writes only the flag and
stores a word there. -/
theorem roundedDecoupleExit_writes_word {M : Machine ℝ} {I : Interp O Q ℝ}
    (hL : IsIndexLit M I) (hC : IsCmp id I) {τ : Tape ℝ} {μ : Mem ℝ} {r f : ℕ × ℕ} {x : ℝ}
    (hx : μ.store.get r.1 (r.2 + 3) = some x) (hf : f.2 < μ.store.len f.1) :
    Writes .total I τ (roundedDecoupleExit (O := O) (Q := Q)).body (Env.frame [] [r, f])
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

-- The default heartbeat budget does not cover the elaboration of this statement.
set_option maxHeartbeats 1000000 in
-- The hypothesis list of the iteration, with its long real constants, makes elaboration heavy.
omit [Has EigenvalueKernelOp O] in
/-- One iteration of the decoupling loop on the good tapes: from the state before round $i$
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
    (hthrω : (1 + u) ^ 2 * ω ^ 2 ≤ tv) {T : ℕ} {SE : Impl O Q}
    (hj : (i + 1) * (k + 1 + (excNet ε).length) ≤ ns) (hw : k * n ≤ ws)
    (hlgv : ∀ b ∈ [w, p, f], b.1 ≠ lg.1) (hlgL : lg.1 < L)
    (hSE : RandomSmallEigContractAt law β φse k 12 T S qs SE I) (hq12 : qs = [] ∨ qs.length = 12) :
    PWrites law I (shIterationWith SE).body
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
            (k + 1 + (excNet ε).length) μ') (φse + φR / 2 + φ) :=
  sorry

omit [Has EigenvalueKernelOp O] in
/-- The rounds of the decoupling loop on the good tapes: if each iteration from the state
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
    {k q n0 F L T : ℕ} {SE : Impl O Q} (hk : 0 < k)
        (hkn : k ≤ n) {w p f lg : ℕ × ℕ} {ns ws : ℕ} {ps : List ℝ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {tL tv c E ωD Nmax φ : ℝ}
    (hps : ps.getD 0 0 = tL) (hps0 : 0 < ps.length) (hHess : IsUpperHessenberg H)
    (hψH : hessenbergPotential k H ≤ Nmax) (hthr : (1 + u) ^ 2 * tv ≤ (1 - u) ^ 2 * tL)
    (hcut : tL ≤ (1 - u) ^ 2 * ωD ^ 2) (hωD : 0 ≤ ωD) (hc0 : 0 ≤ c) (hE0 : 0 ≤ E)
    (hφ : 0 ≤ φ) (hfuel : (1 + u) ^ 2 * (c ^ F * Nmax) ^ 2 ≤ tL)
    (hj : F * (k + 1 + n0) ≤ ns) (hw : k * n ≤ ws) (hlgv : ∀ b ∈ [w, p, f], b.1 ≠ lg.1)
    (hlgL : lg.1 < L)
    (hit : ∀ i < F, PWrites law I (shIterationWith SE).body
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
    PWrites law I (roundedDecoupleLoopWith SE).body
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
        HoldsMatrix w H' μ'.store) (F * φ) := sorry

omit [Has EigenvalueKernelOp O] in
/-- The decoupling loop from its rounds: the allocation of the scan registers and the two
index reads of $m$ and $n_0$ from the parameter words (`NLAlib.Ops.PWrites.allocs`,
`NLAlib.Ops.PWrites.bindIdx`) carry a probabilistic specification of
`NLAlib.ShiftedQR.roundedDecoupleLoopWith` at every fresh buffer to
`NLAlib.ShiftedQR.roundedDecoupleWith` from the precondition of
`NLAlib.ShiftedQR.RandomDecouplingRoutineContract`. -/
theorem roundedDecouple_pwrites_of_loop {I : Interp O Q ℝ} (hI : I.IsMeasurable)
    (hQ : IsToNat id I) {law : ℕ → Measure ℝ} {k q F T : ℕ} {SE : Impl O Q} (hqk : q ≤ k)
    {w p f lg : ℕ × ℕ} {ns ws : ℕ} {ps qs : List ℝ} {tL R tv γ Bi α ε : ℝ}
    (hps : ps = roundedDecoupleParams tL R tv γ Bi α ε k q ++ qs)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e ωD φ : ℝ} (hφ : 0 ≤ φ)
    (hloop : ∀ L lg, PWrites law I (roundedDecoupleLoopWith SE).body
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
        HoldsMatrix w H' μ'.store) φ := sorry
set_option maxHeartbeats 4000000 in
-- The loop's program term and the hypotheses of the iteration make elaboration heavy.
omit [Has EigenvalueKernelOp O] in
/-- **The rounded decoupling loop with a small-eigenvalue routine meets the randomized decoupling
contract**, with the parameter words `NLAlib.ShiftedQR.roundedDecoupleParams` followed by the
routine's words `qs` (none, or $12$) and the routine meeting
`NLAlib.ShiftedQR.RandomSmallEigContractAt` with the word count $12$: the merged statement
`NLAlib.ShiftedQR.roundedDecouple_randomDecouplingContract` is the case of the kernel and no
words. The rounded decoupling loop meets the randomized decoupling contract
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
Each round is one iteration (`NLAlib.ShiftedQR.shIteration_pwrites`) and a scan; the iterates stay
in the class (condition $4B$, separation $g/4$,
`NLAlib.IsPerturbedUnitarySimilar.exists_pseudoConditionNumber_le_and_le_norm_sub`);
a coupled matrix had its potential contracted, so after $F$ rounds the scan passes
(`NLAlib.exists_norm_subdiag_le_hessenbergPotential`), and the failures of the rounds add
(`NLAlib.Ops.PWrites.whileFuel`). -/
theorem roundedDecoupleWith_randomDecouplingRoutineContract {M : Machine ℝ} {I : Interp O Q ℝ}
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
    (hns : F * (k + 1 + (excNet ε).length) ≤ ns) (hws : k * nmax ≤ ws) :
    RandomDecouplingRoutineContract law (2 * B) (g / 2) (F * (φse + φR / 2 + φ)) k F T nmax Nmax
      ps ns ws ωD
      (fun _ => F * ((1 + C) * S * ((1 + 300 * (nmax + 1) ^ 2 * u) ^ k - 1)))
      (roundedDecoupleWith SE) I := sorry
end Iteration

end NLAlib.ShiftedQR
