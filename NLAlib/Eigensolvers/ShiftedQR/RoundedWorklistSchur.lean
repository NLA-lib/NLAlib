/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolveSchur

/-!
# The rounded deflation worklist in Schur mode with randomized routines

[BanksGarzaVargasSrivastava2022, Theorem 6.3] in floating point and in Schur form, at the level
of the worklist: the decoupler and the Schur leaf are randomized, each meeting its guarantee on a
good set of tapes (`NLAlib.Ops.PWrites`). On the good tapes every round keeps the value state
`NLAlib.ShiftedQR.SchurReached`: the stored matrix has the shape `NLAlib.ShiftedQR.SchurShape`
and is tracked with the stored accumulator from the input pair, with one more round error $e$
and one more accumulator factor per round (`NLAlib.ShiftedQR.SchurShape`,
`NLAlib.ShiftedQR.leafUpdate_isTrackedUnitarySimilar`,
`NLAlib.ShiftedQR.decoupleUpdateMatrix_isPerturbedUnitarySimilarBy`). The blocks handed to the
decoupler stay in its class, the bottom scan always finds a cut, and the failure probabilities of
the at most $2(n + 1)$ rounds add (`NLAlib.Ops.PWrites.whileFuel`).

## Main results

* `NLAlib.ShiftedQR.roundedWorklistRound_pwrites`, `NLAlib.ShiftedQR.roundedWorklist_pwrites`:
  a round and the capped loop on the good tapes.
* `NLAlib.ShiftedQR.solveRoundedWith_pwrites`: the worklist in Schur mode as a probabilistic
  block specification.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops MeasureTheory
open scoped Matrix

variable {O Q : Type}

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- The leaf call of a round: the Schur leaf on the work matrix, its accumulator in `Ub`. -/
def roundedLeafCall (L : Stmt O Q) : Stmt O Q :=
  Stmt.frame [IExp.var 8, IExp.var 2, IExp.var 4]
    [{ buf := 5, off := IExp.var 14 }, { buf := 2, off := IExp.var 11 },
      { buf := 5, off := IExp.var 14 }, { buf := 6, off := IExp.var 15 }] L

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The leaf call of a round on the good tapes: from the copied state of round
$j < 2(n + 1)$ on the range $(lo, d)$, $d \le k$, a Schur leaf meeting
`NLAlib.Schur.RandomSchurLeafContract` on orders at most $\min(k, n + 1)$ and norms at most
$N_0$ stores, except with probability at most $\varphi_L$, an upper triangular block and an
accumulator tracked from the block before with errors $(\varepsilon_L, \beta)$. -/
theorem roundedLeafCall_pwrites {I : Interp O Q ℝ} (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {εL β φL N₀ u e : ℝ} {n k F T ns w m : ℕ} {ps : List ℝ} (L : Stmt O Q)
    (hLeaf : Schur.RandomSchurLeafContract law εL β φL (min k (n + 1)) N₀ ps T L I)
    {H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (he0 : 0 ≤ e)
    (hN₀ : specNorm H + 2 * (n + 1) * e ≤ N₀) {thr : ℝ} {a t p uo f st wk ub r : ℕ × ℕ}
    {j lo d : ℕ} (hj : j < 2 * (n + 1)) (hdk : d ≤ k) (hdn : d ≤ n + 1) :
    PWrites law I (roundedLeafCall L)
      (Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d] [a, t, p, st, uo, wk, ub, r, f])
      (Store.inBlock wk.1 wk.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d)))
      (SchurPopped true n H U u εL e m thr ps a t p uo f st wk ub r j lo d)
      (fun μ₁ => ∃ μ, SchurPopped true n H U u εL e m thr ps a t p uo f st wk ub r j lo d μ ∧
        μ.store.EqOff
          (Store.inBlock wk.1 wk.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d)))
          μ₁.store ∧
        (∀ i < 2 * (d * d), (μ₁.store.get wk.1 (wk.2 + i)).isSome) ∧
        (∀ i < 2 * (d * d), (μ₁.store.get ub.1 (ub.2 + i)).isSome) ∧
        (storedMatrix wk d d μ₁.store).IsUpperTriangular ∧
        IsTrackedUnitarySimilar εL β 1 (storedMatrix wk d d μ.store)
          (storedMatrix ub d d μ₁.store) (storedMatrix wk d d μ₁.store)) φL := by
  set FL := Store.inBlock wk.1 wk.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d))
  let ι := {B : Matrix (Fin d) (Fin d) ℂ // specNorm B ≤ N₀}
  have hfam := fun x : ι => ((hLeaf (w := wk) (p := p) (ub := ub) x.1
    (le_min hdk hdn) x.2).in_frame (ρ := Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d]
      [a, t, p, st, uo, wk, ub, r, f]) (ds := [IExp.var 8, IExp.var 2, IExp.var 4])
      (args := [{ buf := 5, off := IExp.var 14 }, { buf := 2, off := IExp.var 11 },
        { buf := 5, off := IExp.var 14 }, { buf := 6, off := IExp.var 15 }]) rfl rfl
      (fun μ h => by
        have := h.2.2.1
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl <;> exact this _ (by simp))).mono
      (Pre' := fun μ => SchurPopped true n H U u εL e m thr ps a t p uo f st wk ub r j lo d μ ∧
        HoldsMatrix wk x.1 μ.store ∧ μ.store.readBlock p.1 p.2 ps.length = some ps ∧
        μ.Live [wk, p, ub] ∧ ub.2 + 2 * (d * d) ≤ μ.store.len ub.1 ∧
        Fp.Apart [wk, p, ub] [2 * (d * d), ps.length, 2 * (d * d)])
      (fun _ h => h.2) le_rfl (fun _ h => h) le_rfl
  refine PStep.mono (PWrites.pstep_of_forall hI hloc hfam
    (measurableSet_schurLeafOutcome d εL β wk ub FL) ?_) (fun μ hμ => ?_)
    (fun μ μ' hP hT => ⟨hT.1, μ, hP, hT⟩) le_rfl
  · rintro x μ μ' ⟨-, hB, -⟩ hfr ⟨Ub, Tb, ⟨hTb, hUb⟩, hup, htr⟩
    refine ⟨hfr, fun i hi => by rw [Store.get_of_readBlock hTb hi 0]; rfl,
      fun i hi => by rw [Store.get_of_readBlock hUb hi 0]; rfl, ?_, ?_⟩
    · rwa [← hTb.eq_storedMatrix]
    · rwa [← hB.eq_storedMatrix, ← hTb.eq_storedMatrix, ← hUb.eq_storedMatrix]
  · obtain ⟨hG, ht, hp, hf, rs, done, A, U', hSt, hA, hU', hW, hsh, hcnt, htr⟩ := hμ
    have hmem : (lo, d) ∈ rs ++ [(lo, d)] := by simp
    have hfit0 := hsh.1.2.1 _ (List.mem_append_left _ hmem)
    simp only at hfit0
    have hnB := (hsh.deflationInv (H := A) (V := 1) (ε := 0)
      (by simpa using IsPerturbedUnitarySimilarBy.refl A)).specNorm_subBlock_le hmem
    have hnA := htr.specNorm_le_add
    have : (j : ℝ) * e ≤ 2 * (n + 1) * e :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj.le) he0
    have hsq := Nat.mul_le_mul hdn hdn
    have g : ∀ i j : Fin 9, i ≠ j → ¬(i = 1 ∧ j = 2) ∧ ¬(i = 2 ∧ j = 1) → _ :=
      fun i j h h' => hG.disj' i j h h'
    have hWd : Store.inBlock wk.1 wk.2 (2 * (d * d)) ≤
        Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
    have hUd : Store.inBlock ub.1 ub.2 (2 * (d * d)) ≤
        Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
    have hWU : Fp.Disj (Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1)))) := by
      simpa [schurBlock] using g 6 7 (by simp) (by decide)
    have hPW : Fp.Disj (Store.inBlock p.1 p.2 ps.length)
        (Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1)))) := by
      simpa [schurBlock] using g 2 6 (by simp) (by decide)
    have hPU : Fp.Disj (Store.inBlock p.1 p.2 ps.length)
        (Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1)))) := by
      simpa [schurBlock] using g 2 7 (by simp) (by decide)
    refine ⟨⟨subBlock A (lo, d), by linarith⟩, ⟨hG, ht, hp, hf, rs, done, A, U', hSt, hA, hU', hW,
      hsh, hcnt, htr⟩, hW rfl, hp, hG.live_of_subset (by simp),
      by have := hG.room.2.2.2.2.2.2.2.1; omega, ?_⟩
    exact ⟨Fp.disj_sup_right.mpr ⟨(hPW.mono le_rfl hWd).symm,
        Fp.disj_sup_right.mpr ⟨hWU.mono hWd hUd, fun _ _ _ h => h⟩⟩,
      Fp.disj_sup_right.mpr ⟨hPU.mono le_rfl hUd, fun _ _ _ h => h⟩, fun _ _ _ h => h, trivial⟩

omit [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The leaf branch of a round on the good tapes: from the copied state of round
$j < 2(n + 1)$ on the range $(lo, d)$, $d \le k$, $d \le n + 1$, the leaf call
(`NLAlib.ShiftedQR.roundedLeafCall_pwrites`) and the rest of the branch
(`NLAlib.ShiftedQR.roundedLeafRest_reached`) reach the state before round $j + 1$, except with
probability at most $\varphi_L$. -/
theorem roundedLeafBranch_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hI : I.IsMeasurable) {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o))
    {law : ℕ → Measure ℝ} {εL β φL N₀ e : ℝ} {n k F T ns w m : ℕ} (hm2 : 2 * k * (k + 2) ≤ m)
    {ps : List ℝ} (L : Stmt O Q)
    (hLeaf : Schur.RandomSchurLeafContract law εL β φL (min k (n + 1)) N₀ ps T L I)
    (hεL : 0 ≤ εL) (he : β + (8 * (n + 1) * (k + 2) * u * N₀ + 2 * εL * N₀) ≤ e)
    (hroom : 2 * (n + 1) * (8 * (n + 1) * (k + 2) * u * N₀) ≤ N₀)
    {H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (he0 : 0 ≤ e)
    (hN₀ : specNorm H + 2 * (n + 1) * e ≤ N₀) {thr : ℝ} {a t p uo f st wk ub r : ℕ × ℕ}
    {j lo d : ℕ} (hj : j < 2 * (n + 1)) (hdk : d ≤ k) (hdn : d ≤ n + 1) :
    PWrites law I ((roundedLeafCall L).seq (roundedLeafRest (O := O) (Q := Q)))
      (Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d] [a, t, p, st, uo, wk, ub, r, f])
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (SchurPopped true n H U u εL e m thr ps a t p uo f st wk ub r j lo d)
      (SchurReached n H U u εL e m thr ps a t p uo f st wk ub r (j + 1)) φL := by
  have hsq := Nat.mul_le_mul hdn hdn
  refine (PWrites.seq hI hloc le_rfl (roundedLeafCall_pwrites hI hloc L hLeaf he0 hN₀ hj hdk hdn)
    (PWrites.of_writes (F := schurRoundFp (n + 1) a uo f st wk ub r) le_rfl
      fun μ₁ τ hμ₁ => ?_)).mono (fun _ h => h) (sup_le (by fp_sub [schurRoundFp]) le_rfl)
    (fun _ h => h) (by simp)
  obtain ⟨μ, ⟨hG, ht, hp, hf, rs, done, A, U', hSt, hA, hU', hW, hsh, hcnt, htr⟩, hfr, hiW, hiU,
    hup, htrL⟩ := hμ₁
  have g : ∀ i j : Fin 9, i ≠ j → ¬(i = 1 ∧ j = 2) ∧ ¬(i = 2 ∧ j = 1) → _ :=
    fun i j h h' => hG.disj' i j h h'
  have hWd : Store.inBlock wk.1 wk.2 (2 * (d * d)) ≤
      Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  have hUd : Store.inBlock ub.1 ub.2 (2 * (d * d)) ≤
      Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  have hX : ∀ i : Fin 9, i ≠ 6 → i ≠ 7 → Fp.Disj
      (Store.inBlock wk.1 wk.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d)))
      (schurBlock (n + 1) ps.length a t p uo f st wk ub r i) :=
    fun i h6 h7 => Fp.disj_sup_left.mpr ⟨(g 6 i (Ne.symm h6) SchurGeometry.side).mono hWd le_rfl,
      (g 7 i (Ne.symm h7) SchurGeometry.side).mono hUd le_rfl⟩
  have hlen0 := (hsh.deflationInv (H := A) (V := 1) (ε := 0)
    (by simpa using IsPerturbedUnitarySimilarBy.refl A)).length_le
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen0
  have hB : storedMatrix wk d d μ.store = subBlock A (lo, d) := (hW rfl).eq_storedMatrix.symm
  rw [hB] at htrL
  refine (roundedLeafRest_reached (F := F) (T := T) (ns := ns) (w := w) hS hM hu0 hu hm2 hεL
    he hroom he0 hN₀ hj hdk (hG.of_eqOff hfr)
    (hfr.keep (Store.readsOnly_get _ _ _) (by simpa [schurBlock] using hX 4 (by simp) (by simp))
      hf) (hA.of_eqOff hfr (hX 0 (by simp) (by simp))) (hU'.of_eqOff hfr (hX 3 (by simp) (by simp)))
    (holdsMatrix_storedMatrix hiW) (holdsMatrix_storedMatrix hiU)
    (hSt.of_eqOff hfr ((by simpa [schurBlock] using hX 5 (by simp) (by simp) :
      Fp.Disj _ (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))).mono le_rfl
        (Fp.inBlock_le_inBlock le_rfl (by omega)))) hsh hcnt htr htrL hup).mono le_rfl ?_
  intro μ' hfr' hcore
  exact SchurReached.of_core hG ht hp (hfr.trans' hfr') (sup_le (by fp_sub [schurRoundFp]) le_rfl)
    hcore

/-- The copied state of round `j` on the range $(lo, d)$ with a fresh log
buffer `Lc` of `ns` slots of `w` entries on top of the views. -/
def SchurPoppedLog (n : ℕ) (H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (u εL e : ℝ) (m : ℕ)
    (thr : ℝ) (ps : List ℝ) (a t p uo f st wk ub r : ℕ × ℕ) (j lo d ns w Lc : ℕ) (μ : Mem ℝ) :
    Prop :=
  SchurPopped true n H U u εL e m thr ps a t p uo f st wk ub r j lo d μ ∧
    μ.store.length = Lc + 1 ∧ μ.store.len Lc = ns * (1 + 5 * w) ∧
    ∀ v ∈ [a, t, p, uo, f, st, wk, ub, r], v.1 < Lc

/-- The decoupling call of the large branch, on the work matrix with the scoped log. -/
def roundedDecoupleCall (D : Stmt O Q) : Stmt O Q :=
  Stmt.frame [IExp.var 8, IExp.var 1, IExp.var 2, IExp.var 3, IExp.var 4, IExp.var 5,
      IExp.var 6]
    [{ buf := 5, off := IExp.var 14 }, { buf := 2, off := IExp.var 11 },
      { buf := 5, off := IExp.var 14 }, { buf := 7, off := IExp.var 16 },
      { buf := 8, off := IExp.const 0 }] D

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The decoupling call of a round on the good tapes: from the copied state of round
$j < 2(n + 1)$ on the range $(lo, d + 1)$, $k \le d$, with the scoped log at `Lc`, the copied
block is in the decoupler's class (norm at most $N_0$, condition at most $2B$, separation $g/2$,
by `NLAlib.DeflationInv.exists_pseudoConditionNumber_subBlock_le_and_le_norm_sub`), so a
decoupler meeting `NLAlib.ShiftedQR.RandomDecouplingRoutineContract` returns, except with
probability at most $\varphi_D$, the flag $0$, a closed log and an upper Hessenberg perturbed
unitary similarity of the block by the log's unitary with error $\varepsilon(N_0)$ and a
bottom-$k$ subdiagonal entry of modulus at most $\omega$. -/
theorem roundedDecoupleCall_pwrites {I : Interp O Q ℝ} (hI : I.IsMeasurable)
    {win : O → List ℕ → ℕ} (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {B g φD N₀ u εL e ω : ℝ} {n k F T ns w m : ℕ} {ps : List ℝ} {ε : ℝ → ℝ} (D : Stmt O Q)
    (hD : RandomDecouplingRoutineContract law (2 * B) (g / 2) φD k F T n N₀ ps ns w ω ε D I)
    {H U V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {dd : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal dd) (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g ≤ ‖dd i - dd j‖) (he0 : 0 ≤ e)
    (hN₀ : specNorm H + 2 * (n + 1) * e ≤ N₀) (hsmall : 2 * (n + 1) * e ≤ g / (16 * (n + 1) * B))
    {thr : ℝ} {a t p uo f st wk ub r : ℕ × ℕ} {j lo d Lc : ℕ} (hj : j < 2 * (n + 1))
    (hk : k ≤ d) (hdn : d ≤ n) :
    PWrites law I (roundedDecoupleCall D)
      ⟨(Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d + 1] [a, t, p, st, uo, wk, r, f]).idx,
        (Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d + 1] [a, t, p, st, uo, wk, r, f]).buf ++
          [Lc]⟩
      (Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
        Store.inBlock Lc 0 (ns * (1 + 5 * w)))
      (SchurPoppedLog n H U u εL e m thr ps a t p uo f st wk ub r j lo (d + 1) ns w Lc)
      (fun μ₁ => ∃ μ, SchurPoppedLog n H U u εL e m thr ps a t p uo f st wk ub r j lo (d + 1) ns w
          Lc μ ∧
        (μ, μ₁) ∈ {x : Mem ℝ × Mem ℝ | x.1.store.EqOff
            (Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
              Store.inBlock Lc 0 (ns * (1 + 5 * w))) x.2.store ∧
          x.2.store.get f.1 f.2 = some 0 ∧
          (∀ j < 2 * ((d + 1) * (d + 1)), (x.2.store.get wk.1 (wk.2 + j)).isSome) ∧
          IsPerturbedUnitarySimilarBy
            (givensLog (d + 1) (slotEntries w (slottedLogRead (Lc, 0) ns w x.2.store)))
            (storedMatrix wk (d + 1) (d + 1) x.1.store)
            (storedMatrix wk (d + 1) (d + 1) x.2.store) (ε N₀) ∧
          IsUpperHessenberg (storedMatrix wk (d + 1) (d + 1) x.2.store) ∧
          (∃ i : Fin d, d ≤ (i : ℕ) + k ∧
            ‖storedMatrix wk (d + 1) (d + 1) x.2.store i.succ i.castSucc‖ ≤ ω) ∧
          ∃ Ls : List (Option (List GivensEntry)), Ls.length = ns ∧
            (∀ e ∈ slotEntries w Ls, e.1 + 1 < d + 1) ∧
            HoldsSlottedLog (Lc, 0) ns w ([] ++ Ls) [] x.2.store}) φD := by
  set FD := Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
    Store.inBlock Lc 0 (ns * (1 + 5 * w))
  let ι := {Hb : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ // IsUpperHessenberg Hb ∧
    specNorm Hb ≤ N₀ ∧ ∃ (Vr : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (dr : Fin (d + 1) → ℂ),
      IsUnit Vr ∧ Hb * Vr = Vr * Matrix.diagonal dr ∧ pseudoConditionNumber Vr ≤ 2 * B ∧
      ∀ i j, i ≠ j → g / 2 ≤ ‖dr i - dr j‖}
  have hfam := fun x : ι =>
    have hx := x.2.2.2.choose_spec.choose_spec
    ((hD (n := d) (N := N₀) (w₀ := wk) (q := p) (f := f) (lg := (Lc, 0)) x.1 _ _ hk hdn le_rfl
      x.2.1 x.2.2.1 hx.1 hx.2.1 hx.2.2.1 hx.2.2.2).in_frame
      (ρ := ⟨(Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d + 1]
        [a, t, p, st, uo, wk, r, f]).idx, (Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d + 1]
        [a, t, p, st, uo, wk, r, f]).buf ++ [Lc]⟩)
      (ds := [IExp.var 8, IExp.var 1, IExp.var 2, IExp.var 3, IExp.var 4, IExp.var 5, IExp.var 6])
      (args := [{ buf := 5, off := IExp.var 14 }, { buf := 2, off := IExp.var 11 },
        { buf := 5, off := IExp.var 14 }, { buf := 7, off := IExp.var 16 },
        { buf := 8, off := IExp.const 0 }]) rfl rfl fun μ h => h.2.2.1).mono
      (Pre' := fun μ => SchurPoppedLog n H U u εL e m thr ps a t p uo f st wk ub r j lo (d + 1) ns
        w Lc μ ∧ HoldsMatrix wk x.1 μ.store ∧
        μ.store.readBlock p.1 p.2 ps.length = some ps ∧ μ.Live [wk, p, wk, f, (Lc, 0)] ∧
        (∀ b ∈ [wk, p, f], b.1 ≠ (Lc, 0).1) ∧
        wk.2 + 2 * ((d + 1) * (d + 1)) ≤ μ.store.len wk.1 ∧
        f.2 + 1 ≤ μ.store.len f.1 ∧ (Lc, 0).2 + ns * (1 + 5 * w) ≤ μ.store.len (Lc, 0).1 ∧
        Fp.Apart [wk, f, (Lc, 0)] [2 * ((d + 1) * (d + 1)), 1, ns * (1 + 5 * w)] ∧
        Fp.Disj (Store.inBlock p.1 p.2 ps.length)
          (Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
            Store.inBlock (Lc, 0).1 (Lc, 0).2 (ns * (1 + 5 * w))))
      (fun _ h => h.2) le_rfl (fun _ h => h) le_rfl
  refine PStep.mono (PWrites.pstep_of_forall hI hloc hfam
    (measurableSet_schurDecoupleOutcome d k (ε N₀) ω wk f (Lc, 0) ns w FD) ?_)
    (fun μ hμ => ?_) (fun μ μ' hP hT => ⟨hT.1, μ, hP, hT⟩) le_rfl
  · rintro x μ μ' ⟨-, hB, -⟩ hfr ⟨hf0, H', Ls, hLs, hpl, hlog, hby, hHess, hsm, hW'⟩
    rw [hB.eq_storedMatrix, hW'.eq_storedMatrix, hlog.slotEntries_read hLs] at hby
    rw [hW'.eq_storedMatrix] at hHess hsm
    exact ⟨hfr, hf0, fun i hi => by rw [Store.get_of_readBlock hW' hi 0]; rfl, hby, hHess, hsm,
      Ls, hLs, hpl, hlog⟩
  · obtain ⟨⟨hG, ht, hp, hf, rs, done, A, U', hSt, hA, hU', hW, hsh, hcnt, htr⟩, hlen, hL0,
      hv⟩ := hμ
    have hmem : (lo, d + 1) ∈ rs ++ [(lo, d + 1)] := by simp
    have hd : d + 1 ≤ n + 1 := by
      have := hsh.1.2.1 _ (List.mem_append_left _ hmem); simp at this; omega
    have hnB := (hsh.deflationInv (H := A) (V := 1) (ε := 0)
      (by simpa using IsPerturbedUnitarySimilarBy.refl A)).specNorm_subBlock_le hmem
    have hnA := htr.specNorm_le_add
    have hje : (j : ℝ) * e ≤ 2 * (n + 1) * e :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj.le) he0
    obtain ⟨Vt, hVt, hUt⟩ := htr
    obtain ⟨Vr, dr, hVr, hHVr, hκr, hgr⟩ :=
      (hsh.deflationInv hVt).exists_pseudoConditionNumber_subBlock_le_and_le_norm_sub hV hHV hκ hg
        hgap (by linarith) hmem
    have hWw : Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ≤
        Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))) := by
      have := Nat.mul_le_mul hd hd; fp_sub
    have hW' : ∀ i : Fin 9, i ≠ 6 → Fp.Disj (Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))))
        (schurBlock (n + 1) ps.length a t p uo f st wk ub r i) :=
      fun i hi => hG.disj' 6 i (Ne.symm hi)
    have hLW : Fp.Disj (Store.inBlock Lc 0 (ns * (1 + 5 * w))) (Store.inBlock wk.1 wk.2
        (2 * ((d + 1) * (d + 1)))) := Fp.disj_inBlock_of_ne (by have := hv wk (by simp); omega)
    have hLF : Fp.Disj (Store.inBlock Lc 0 (ns * (1 + 5 * w))) (Store.inBlock f.1 f.2 1) :=
      Fp.disj_inBlock_of_ne (by have := hv f (by simp); omega)
    refine ⟨⟨subBlock A (lo, d + 1), hsh.2.2.1 _ hmem, by linarith, Vr, dr, hVr, hHVr, hκr, hgr⟩,
      ⟨⟨hG, ht, hp, hf, rs, done, A, U', hSt, hA, hU', hW, hsh, hcnt, ⟨Vt, hVt, hUt⟩⟩, hlen, hL0,
        hv⟩, hW rfl, hp, fun z hz => ?_, ?_, ?_, hG.room.2.2.2.2.1, by simp [hL0], ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with h | h | h | h | h <;> rw [h]
      · exact hG.live _ (by simp)
      · exact hG.live _ (by simp)
      · exact hG.live _ (by simp)
      · exact hG.live _ (by simp)
      · change Lc < μ.store.length; omega
    · intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with h | h | h <;> rw [h] <;> simp only <;>
        [have := hv wk (by simp); have := hv p (by simp); have := hv f (by simp)] <;> omega
    · have := hG.room.2.2.2.2.2.2.1; have := Nat.mul_le_mul hd hd; omega
    · exact ⟨Fp.disj_sup_right.mpr ⟨(hW' 4 (by simp)).mono hWw (by simp [schurBlock]),
        Fp.disj_sup_right.mpr ⟨hLW.symm, fun _ _ _ h => h⟩⟩,
        Fp.disj_sup_right.mpr ⟨hLF.symm, fun _ _ _ h => h⟩, fun _ _ _ h => h, trivial⟩
    · exact Fp.disj_sup_right.mpr ⟨Fp.disj_sup_right.mpr ⟨((hW' 2 (by simp)).mono hWw le_rfl).symm,
        (by simpa [schurBlock] using hG.disj' 2 4 (by simp))⟩,
        Fp.disj_inBlock_of_ne (by have := hv p (by simp); omega)⟩

/-- The core survives dropping scratch buffers above its views. -/
theorem SchurReachedCore.of_below {n : ℕ} {H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {u εL e : ℝ} {m j L : ℕ} {a uo f st : ℕ × ℕ} {s s' : Store ℝ} {pos : ℕ}
    (h : SchurReachedCore n H U u εL e m a uo f st j ⟨s, pos⟩) (hBelow : Store.Below L s s')
    (ha : a.1 < L) (hu : uo.1 < L) (hf : f.1 < L) (hs : st.1 < L) :
    SchurReachedCore n H U u εL e m a uo f st j ⟨s', pos⟩ := by
  obtain ⟨hf0, rs, done, A, U', hSt, hA, hU', hrest⟩ := h
  exact ⟨((hBelow f.1 hf).2 _).trans hf0, rs, done, A, U', hSt.of_below hBelow hs,
    hA.of_below hBelow ha, hU'.of_below hBelow hu, hrest⟩

/-- The large branch of a round on the good tapes: from the copied state of round
$j < 2(n + 1)$ on the range $(lo, d + 1)$, $k \le d$, the scoped log, the decoupling call
(`NLAlib.ShiftedQR.roundedDecoupleCall_pwrites`) and the rest of the branch
(`NLAlib.ShiftedQR.roundedLargeRest_reached`) reach the state before round $j + 1$, except with
probability at most $\varphi_D$.

Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and `NLAlib.SmallEig.smallEigRoutine`,
on their scratch. -/
theorem roundedLarge_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {B g φD N₀ εL e ω c thr : ℝ}
    {k F T ns w m : ℕ} (hm : ns * w ≤ m) {ps : List ℝ} {ε : ℝ → ℝ} (D : Stmt O Q)
    (hD : RandomDecouplingRoutineContract law (2 * B) (g / 2) φD k F T n N₀ ps ns w ω ε D I)
    {H U V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {dd : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal dd) (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g ≤ ‖dd i - dd j‖) (hεL : 0 ≤ εL)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (he : ε N₀ + 78 * u * (ns * w : ℕ) * N₀ + c ≤ e)
    (hroom : 2 * (n + 1) * (78 * u * (ns * w : ℕ) * N₀) ≤ N₀) (he0 : 0 ≤ e)
    (hN₀ : specNorm H + 2 * (n + 1) * e ≤ N₀) (hsmall : 2 * (n + 1) * e ≤ g / (16 * (n + 1) * B))
    {a t p uo f st wk ub r : ℕ × ℕ} {j lo d : ℕ} (hj : j < 2 * (n + 1)) (hk : k ≤ d)
    (hdn : d ≤ n) :
    PWrites law I (roundedProcessLargeWith D)
      (Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d + 1] [a, t, p, st, uo, wk, r, f])
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (SchurPopped true n H U u εL e m thr ps a t p uo f st wk ub r j lo (d + 1))
      (SchurReached n H U u εL e m thr ps a t p uo f st wk ub r (j + 1)) φD := by
  have hd : d + 1 ≤ n + 1 := by omega
  have hWw : Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ≤
      Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))) := by
    have := Nat.mul_le_mul hd hd; fp_sub
  rw [roundedProcessLargeWith_body]
  change PWrites law I
    (Stmt.allocs [IExp.var 5 * (IExp.const 1 + IExp.const 5 * IExp.var 6)] _) _ _ _ _ _
  refine PWrites.mono_eqOff (Post := SchurReachedCore n H U u εL e m a uo f st (j + 1))
    (PWrites.allocs (ns := [ns * (1 + 5 * w)]) (by simp [IExp.evalList, IExp.eval, Env.frame])
      (Pre₁ := fun Lc μ => SchurPoppedLog n H U u εL e m thr ps a t p uo f st wk ub r j lo (d + 1)
        ns w Lc μ) ?_ ?_ fun Lc => ?_) (fun _ h => h)
    (fun μ μ' hμ hfr hcore => SchurReached.of_core hμ.1 hμ.2.1 hμ.2.2.1 hfr le_rfl hcore)
  · rintro μ s₁ ⟨hG, ht, hp, hf, rs, done, A, U', hSt, hA, hU', hW, hrest⟩ hlen hlens hBelow
    simp only [List.length_cons, List.length_nil] at hlen
    have hv : ∀ v ∈ [a, t, p, uo, f, st, wk, ub, r], v.1 < μ.store.length :=
      fun v hv => hG.live v hv
    exact ⟨⟨hG.of_below (s := s₁) (by omega) hBelow,
      ((hBelow t.1 (hv t (by simp))).2 _).trans ht,
      (hBelow.readBlock (hv p (by simp)) p.2 ps.length).trans hp,
      ((hBelow f.1 (hv f (by simp))).2 _).trans hf, rs, done, A, U',
      hSt.of_below hBelow (hv st (by simp)), hA.of_below hBelow (hv a (by simp)),
      hU'.of_below hBelow (hv uo (by simp)), fun h => (hW h).of_below hBelow (hv wk (by simp)),
      hrest⟩, hlen, by simpa using hlens 0 (by simp), hv⟩
  · intro μ hμ s s' pos hBelow hcore
    have hv : ∀ v ∈ [a, t, p, uo, f, st, wk, ub, r], v.1 < μ.store.length :=
      fun v hv => hμ.1.live v hv
    exact hcore.of_below hBelow (hv a (by simp)) (hv uo (by simp)) (hv f (by simp))
      (hv st (by simp))
  simp only [List.length_cons, List.length_nil]
  set FD := Store.inBlock wk.1 wk.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1 ⊔
    Store.inBlock Lc 0 (ns * (1 + 5 * w))
  have hDF : FD ≤ schurRoundFp (n + 1) a uo f st wk ub r ⊔ Fp.above Lc :=
    sup_le (sup_le (hWw.trans (by fp_sub [schurRoundFp])) (by fp_sub [schurRoundFp]))
      (fun b z h => Or.inr (show Lc ≤ b from h.1 ▸ le_rfl))
  refine (PWrites.seq hI hloc le_rfl (roundedDecoupleCall_pwrites (m := m) (εL := εL) (u := u)
    (thr := thr) (ub := ub) (uo := uo) (st := st) (a := a) (t := t) (r := r) (U := U) (j := j)
    (lo := lo) (Lc := Lc) hI hloc D hD hV hHV hκ hg hgap he0 hN₀ hsmall hj hk hdn)
    (PWrites.of_writes (F := schurRoundFp (n + 1) a uo f st wk ub r) le_rfl
      fun μ₁ τ hμ₁ => ?_)).mono (fun _ h => h) (sup_le hDF le_sup_left) (fun _ h => h)
      (by simp)
  obtain ⟨μ, ⟨⟨hG, ht, hp, hf, rs, done, A, U', hSt, hA, hU', hW, hsh, hcnt, htr⟩, hlen, hL0,
    hv⟩, hfr, hf0, hinit, hby, hHess, hsm, Ls, hLs, hpl, hlog⟩ := hμ₁
  have hW' : ∀ i : Fin 9, i ≠ 6 → Fp.Disj (Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))))
      (schurBlock (n + 1) ps.length a t p uo f st wk ub r i) :=
    fun i hi => hG.disj' 6 i (Ne.symm hi)
  have hDX : ∀ (i : Fin 9), i ≠ 6 → i ≠ 4 →
      ([a, t, p, uo, f, st, wk, ub, r] : List (ℕ × ℕ)).getD i (0, 0) ∈
        [a, t, p, uo, f, st, wk, ub, r] →
      Fp.Disj FD (schurBlock (n + 1) ps.length a t p uo f st wk ub r i) :=
    fun i h6 h4 hm => Fp.disj_sup_left.mpr ⟨Fp.disj_sup_left.mpr ⟨(hW' i h6).mono hWw le_rfl,
      hG.disj' 4 i (Ne.symm h4)⟩, Fp.disj_inBlock_of_ne (by have := hv _ hm; omega)⟩
  have hlen0 := (hsh.deflationInv (H := A) (V := 1) (ε := 0)
    (by simpa using IsPerturbedUnitarySimilarBy.refl A)).length_le
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen0
  have hlog' : HoldsSlottedLog (Lc, 0) ns w Ls [] μ₁.store := hlog
  rw [← (hW rfl).eq_storedMatrix, ← hlog'.slotEntries_read hLs] at hby
  exact roundedLargeRest_reached hS hM hu0 hu hL hNat hQ hC hm hj hk hεL hfind hcut hc he hroom he0
    hN₀ (hG.of_eqOff hfr)
    (hfr.keep (Store.readsOnly_get _ _ _) (hDX 1 (by simp) (by simp) (by simp)) ht) hf0
    (hfr.keep (readsOnly_holdsMatrix _ _) (hDX 0 (by simp) (by simp) (by simp)) hA)
    (hfr.keep (readsOnly_holdsMatrix _ _) (hDX 3 (by simp) (by simp) (by simp)) hU')
    (holdsMatrix_storedMatrix hinit)
    (hSt.of_eqOff hfr ((by simpa [schurBlock] using hDX 5 (by simp) (by simp) (by simp) :
      Fp.Disj FD (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))).mono le_rfl
      (Fp.inBlock_le_inBlock le_rfl (by omega))))
    hsh hcnt htr hlog' hLs hpl (by have := hfr.length_eq; simp only at this; omega) hv hby hHess
    hsm

/-- Processing a popped range on the good tapes: from the popped state of round
$j < 2(n + 1)$ on the range $(lo, d)$, $lo + d \le n + 1$, the copy of its block, then the leaf
branch (order at most $k$) or the large branch reach the state before round $j + 1$, except with
probability at most $\varphi_L + \varphi_D$.

Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and `NLAlib.SmallEig.smallEigRoutine`,
on their scratch. -/
theorem roundedRange_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {B g φD φL N₀ εL β e ω c thr : ℝ} {k F T ns w m : ℕ} (hm1 : ns * w ≤ m)
    (hm2 : 2 * k * (k + 2) ≤ m) {ps : List ℝ} {ε : ℝ → ℝ} (D : Stmt O Q)
    (hD : RandomDecouplingRoutineContract law (2 * B) (g / 2) φD k F T n N₀ ps ns w ω ε D I)
    (L : Stmt O Q)
    (hLeaf : Schur.RandomSchurLeafContract law εL β φL (min k (n + 1)) N₀ ps T L I)
    (hφD : 0 ≤ φD) (hφL : 0 ≤ φL)
    {H U V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {dd : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal dd) (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g ≤ ‖dd i - dd j‖) (hεL : 0 ≤ εL)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (heD : ε N₀ + 78 * u * (ns * w : ℕ) * N₀ + c ≤ e)
    (heL : β + (8 * (n + 1) * (k + 2) * u * N₀ + 2 * εL * N₀) ≤ e)
    (hroomD : 2 * (n + 1) * (78 * u * (ns * w : ℕ) * N₀) ≤ N₀)
    (hroomL : 2 * (n + 1) * (8 * (n + 1) * (k + 2) * u * N₀) ≤ N₀) (he0 : 0 ≤ e)
    (hN₀ : specNorm H + 2 * (n + 1) * e ≤ N₀) (hsmall : 2 * (n + 1) * e ≤ g / (16 * (n + 1) * B))
    {a t p uo f st wk ub r : ℕ × ℕ} {j lo d : ℕ} (hj : j < 2 * (n + 1)) (hd : lo + d ≤ n + 1) :
    PWrites law I (roundedProcessRangeWith D L)
      (Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d] [a, t, p, st, uo, wk, ub, r, f])
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (SchurPopped false n H U u εL e m thr ps a t p uo f st wk ub r j lo d)
      (SchurReached n H U u εL e m thr ps a t p uo f st wk ub r (j + 1)) (φL + φD) := by
  have hsq := Nat.mul_le_mul (show d ≤ n + 1 by omega) (show d ≤ n + 1 by omega)
  have hWd : Store.inBlock wk.1 wk.2 (2 * (d * d)) ≤
      Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  have hcopy : PWrites law I (Stmt.frame [IExp.var 0, IExp.var 7, IExp.var 8]
      [{ buf := 0, off := IExp.var 9 }, { buf := 5, off := IExp.var 14 }]
      (copyToWork (Op := O) (Tst := Q)))
      (Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d] [a, t, p, st, uo, wk, ub, r, f])
      (Store.inBlock wk.1 wk.2 (2 * (d * d)))
      (SchurPopped false n H U u εL e m thr ps a t p uo f st wk ub r j lo d)
      (SchurPopped true n H U u εL e m thr ps a t p uo f st wk ub r j lo d) 0 :=
    PWrites.of_writes le_rfl fun μ τ hμ => by
      obtain ⟨hG, ht, hp, hf, rs, done, A, U', hSt, hA, hU', -, hrest⟩ := hμ
      have hlAW : μ.Live [a, wk] := hG.live_of_subset (by simp)
      have g : ∀ i : Fin 9, i ≠ 6 → _ := fun i h => (hG.disj' 6 i (Ne.symm h)).mono hWd le_rfl
      refine ((copyToWork_writes (τ := τ) (lo := lo) (d := d) hS hlAW hA hd
        (by have := hG.room.2.2.2.2.2.2.1; omega)
        (by simpa [schurBlock] using (g 0 (by simp)).symm)).in_frame rfl rfl hlAW).mono le_rfl ?_
      rintro μ₁ hfr₁ ⟨-, hW₁⟩
      have hlen0 := (hrest.1.deflationInv (H := A) (V := 1) (ε := 0)
        (by simpa using IsPerturbedUnitarySimilarBy.refl A)).length_le
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen0
      exact ⟨hG.of_eqOff hfr₁,
        hfr₁.keep (Store.readsOnly_get _ _ _) (by simpa [schurBlock] using g 1 (by simp)) ht,
        hfr₁.keep (Store.readsOnly_readBlock _ _ _ _)
          (by simpa [schurBlock] using g 2 (by simp)) hp,
        hfr₁.keep (Store.readsOnly_get _ _ _) (by simpa [schurBlock] using g 4 (by simp)) hf,
        rs, done, A, U', hSt.of_eqOff hfr₁ ((by simpa [schurBlock] using g 5 (by simp) :
          Fp.Disj _ (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))).mono le_rfl
            (Fp.inBlock_le_inBlock le_rfl (by omega))),
        hA.of_eqOff hfr₁ (by simpa [schurBlock] using g 0 (by simp)),
        hU'.of_eqOff hfr₁ (by simpa [schurBlock] using g 3 (by simp)), fun _ => hW₁, hrest⟩
  unfold roundedProcessRangeWith
  by_cases hs : d ≤ k
  · refine (PWrites.seq hI hloc (by positivity) hcopy (PWrites.seq hI hloc hφD
      (PWrites.ifPos (n := k + 1 - d) rfl hφL
        (fun _ => roundedLeafBranch_pwrites (F := F) (ns := ns) (w := w) hS hM hu0 hu hI hloc
          hm2 L hLeaf hεL heL hroomL he0
          hN₀ hj hs (by omega))
        (fun h0 => absurd h0 (by omega)))
      (PWrites.ifPos (F := ⊥) (n := d - k) rfl hφD (fun h => absurd h (by omega))
        fun _ _ h => h))).mono
      (fun _ h => h) (sup_le (hWd.trans (by fp_sub [schurRoundFp])) (sup_le le_rfl bot_le))
      (fun _ h => h) (by simp)
  · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    refine (PWrites.seq hI hloc (by positivity) hcopy (PWrites.seq hI hloc hφD
      (PWrites.ifPos (F := ⊥) (n := k + 1 - (d' + 1)) rfl hφL (fun h => absurd h (by omega))
        fun _ _ h => h)
      (PWrites.ifPos (n := d' + 1 - k) rfl hφD (fun _ => (roundedLarge_pwrites hS hM hu0 hu hL
        hNat hQ hC hI hloc hm1 D hD hV hHV hκ hg hgap hεL hfind hcut hc heD hroomD he0 hN₀ hsmall
        hj (by omega) (by omega)).in_frame rfl rfl fun μ h => h.1.live_of_subset (by simp))
        (fun h0 => absurd h0 (by omega))))).mono
      (fun _ h => h) (sup_le (hWd.trans (by fp_sub [schurRoundFp])) (sup_le bot_le le_rfl))
      (fun _ h => h) (by simp)

/-- One round on the good tapes: from the state before round $j < 2(n + 1)$ with a positive
stack count, the pop, the two bounded index reads and the processing of the popped range
(`NLAlib.ShiftedQR.roundedRange_pwrites`) reach the state before round $j + 1$, except with
probability at most $\varphi_L + \varphi_D$.

Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and `NLAlib.SmallEig.smallEigRoutine`,
on their scratch. -/
theorem roundedWorklistRound_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {B g φD φL N₀ εL β e ω c thr : ℝ} {k F T ns w m : ℕ} (hm1 : ns * w ≤ m)
    (hm2 : 2 * k * (k + 2) ≤ m) {ps : List ℝ} {ε : ℝ → ℝ} (D : Stmt O Q)
    (hD : RandomDecouplingRoutineContract law (2 * B) (g / 2) φD k F T n N₀ ps ns w ω ε D I)
    (L : Stmt O Q)
    (hLeaf : Schur.RandomSchurLeafContract law εL β φL (min k (n + 1)) N₀ ps T L I)
    (hφD : 0 ≤ φD) (hφL : 0 ≤ φL)
    {H U V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {dd : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal dd) (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g ≤ ‖dd i - dd j‖) (hεL : 0 ≤ εL)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (heD : ε N₀ + 78 * u * (ns * w : ℕ) * N₀ + c ≤ e)
    (heL : β + (8 * (n + 1) * (k + 2) * u * N₀ + 2 * εL * N₀) ≤ e)
    (hroomD : 2 * (n + 1) * (78 * u * (ns * w : ℕ) * N₀) ≤ N₀)
    (hroomL : 2 * (n + 1) * (8 * (n + 1) * (k + 2) * u * N₀) ≤ N₀) (he0 : 0 ≤ e)
    (hN₀ : specNorm H + 2 * (n + 1) * e ≤ N₀) (hsmall : 2 * (n + 1) * e ≤ g / (16 * (n + 1) * B))
    {a t p uo f st wk ub r : ℕ × ℕ} {j : ℕ} (hj : j < 2 * (n + 1)) :
    PWrites law I (roundedWorklistRoundWith D L)
      (Env.frame [n + 1, k, ps.length, F, T, ns, w] [a, t, p, st, uo, wk, ub, r, f])
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (fun μ => SchurReached n H U u εL e m thr ps a t p uo f st wk ub r j μ ∧
        ∃ cnt : ℕ, μ.store.get st.1 st.2 = some (cnt : ℝ) ∧ 0 < cnt)
      (SchurReached n H U u εL e m thr ps a t p uo f st wk ub r (j + 1)) (φL + φD) := by
  unfold roundedWorklistRoundWith
  refine (PWrites.seq (F₂ := schurRoundFp (n + 1) a uo f st wk ub r) (φ₁ := 0)
    (φ₂ := φL + φD) (Mid := fun μ₁ => ∃ lo d : ℕ,
      SchurPopped false n H U u εL e m thr ps a t p uo f st wk ub r j lo d μ₁ ∧
        μ₁.store.get r.1 r.2 = some (lo : ℝ) ∧ μ₁.store.get r.1 (r.2 + 1) = some (d : ℝ))
    hI hloc (by positivity)
    (PWrites.of_writes (F := Store.inBlock st.1 st.2 1 ⊔ Store.inBlock r.1 r.2 2) le_rfl
      fun μ τ hμ => ?_) ?_).mono
    (fun _ h => h) (sup_le (by fp_sub [schurRoundFp]) le_rfl) (fun _ h => h) (by simp)
  · obtain ⟨⟨hG, ht, hp, hf, rs, done, A, U', hSt, hA, hU', hsh, hcnt, htr⟩, cnt, hcount,
      hpos⟩ := hμ
    obtain rfl | ⟨rs', ⟨lo, d⟩, rfl⟩ := List.eq_nil_or_concat rs
    · have hc0 : (cnt : ℝ) = 0 := Option.some.inj (hcount.symm.trans (by simpa using hSt.1))
      exact absurd (by exact_mod_cast hc0 : cnt = 0) (by omega)
    rw [List.concat_eq_append] at hSt hsh hcnt
    have hlen0 := (hsh.deflationInv (H := A) (V := 1) (ε := 0)
      (by simpa using IsPerturbedUnitarySimilarBy.refl A)).length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen0 hcnt
    have g : ∀ i j : Fin 9, i ≠ j → ¬(i = 1 ∧ j = 2) ∧ ¬(i = 2 ∧ j = 1) → _ :=
      fun i j h h' => hG.disj' i j h h'
    have hRS : Fp.Disj (Store.inBlock r.1 r.2 2) (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) :=
      (by simpa [schurBlock] using g 8 5 (by simp) (by decide) : Fp.Disj (Store.inBlock r.1 r.2 5)
        (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))).mono (by fp_sub) le_rfl
    have hlSR : μ.Live [st, r] := hG.live_of_subset (by simp)
    refine ((rangePop_writes_of_isExactNatLit (τ := τ) hS hL hQ hNat hSt (by omega)
      (by simpa only [Nat.add_assoc] using hG.room.2.2.2.2.2.1)
      (by have := hG.room.2.2.2.2.2.2.2.2.1; omega) hlSR hRS).in_frame rfl rfl hlSR).mono
      le_rfl ?_
    rintro μ₁ hfr₁ ⟨-, hSt₁, hRange⟩
    have hpd : ∀ i : Fin 9, i ≠ 5 → i ≠ 8 → Fp.Disj
        (Store.inBlock st.1 st.2 1 ⊔ Store.inBlock r.1 r.2 2)
        (schurBlock (n + 1) ps.length a t p uo f st wk ub r i) :=
      fun i h5 h8 => Fp.disj_sup_left.mpr
        ⟨(show Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) _ from
            g 5 i (Ne.symm h5) SchurGeometry.side).mono
          (Fp.inBlock_le_inBlock le_rfl (by omega)) le_rfl,
        (show Fp.Disj (Store.inBlock r.1 r.2 5) _ from g 8 i (Ne.symm h8) SchurGeometry.side).mono
          (Fp.inBlock_le_inBlock le_rfl (by omega)) le_rfl⟩
    refine ⟨lo, d, ⟨hG.of_eqOff hfr₁,
      hfr₁.keep (Store.readsOnly_get _ _ _) (hpd 1 (by simp) (by simp)) ht,
      hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hpd 2 (by simp) (by simp)) hp,
      hfr₁.keep (Store.readsOnly_get _ _ _) (hpd 4 (by simp) (by simp)) hf, rs', done, A, U',
      hSt₁, hA.of_eqOff hfr₁ (hpd 0 (by simp) (by simp)),
      hU'.of_eqOff hfr₁ (hpd 3 (by simp) (by simp)), fun h => absurd h (by simp), hsh,
      by omega, htr⟩, ?_, ?_⟩
    · simpa [vec] using Store.get_of_readBlock hRange (j := 0) (by omega) (0 : ℝ)
    · simpa [vec] using Store.get_of_readBlock hRange (j := 1) (by omega) (0 : ℝ)
  refine PWrites.bindIdx hI (B := n + 1) rfl rfl
    (fun μ ⟨lo, d, hP, hLo, hd⟩ => ⟨lo, ?_, hQ.index_eq_of_decode_nat hLo rfl⟩) fun v _ => ?_
  · obtain ⟨-, -, -, -, rs, done, A, -, -, -, -, -, hsh, -⟩ := hP
    have := hsh.1.2.1 (lo, d) (by simp); simp only at this; omega
  refine PWrites.bindIdx hI (B := n + 1) rfl rfl
    (fun μ ⟨⟨lo, d, hP, hLo, hd⟩, _⟩ => ⟨d, ?_, hQ.index_eq_of_decode_nat hd rfl⟩)
    fun v' _ => ?_
  · obtain ⟨-, -, -, -, rs, done, A, -, -, -, -, -, hsh, -⟩ := hP
    have := hsh.1.2.1 (lo, d) (by simp); simp only at this; omega
  have hpre : ∀ μ, ((∃ lo d : ℕ,
      SchurPopped false n H U u εL e m thr ps a t p uo f st wk ub r j lo d μ ∧
        μ.store.get r.1 r.2 = some (lo : ℝ) ∧ μ.store.get r.1 (r.2 + 1) = some (d : ℝ)) ∧
      I.index (Has.inj IdxTst.toNat) [r] μ = some v) ∧
      I.index (Has.inj IdxTst.toNat) [(r.1, r.2 + 1)] μ = some v' →
      v + v' ≤ n + 1 ∧ SchurPopped false n H U u εL e m thr ps a t p uo f st wk ub r j v v' μ := by
    rintro μ ⟨⟨⟨lo, d, hP, hLo, hd⟩, hv⟩, hv'⟩
    obtain rfl : lo = v := Option.some.inj ((hQ.index_eq_of_decode_nat hLo rfl).symm.trans hv)
    obtain rfl : d = v' := Option.some.inj ((hQ.index_eq_of_decode_nat hd rfl).symm.trans hv')
    refine ⟨?_, hP⟩
    obtain ⟨-, -, -, -, rs, done, A, -, -, -, -, -, hsh, -⟩ := hP
    have := hsh.1.2.1 (lo, d) (by simp); simpa using this.2
  by_cases hvv : v + v' ≤ n + 1
  · exact ((roundedRange_pwrites hS hM hu0 hu hL hNat hQ hC hI hloc hm1 hm2 D hD L hLeaf hφD hφL
      hV hHV hκ hg hgap hεL hfind hcut hc heD heL hroomD hroomL he0 hN₀ hsmall hj hvv).in_frame
      rfl rfl fun μ h => h.1.live_of_subset (by simp)).mono (fun μ h => (hpre μ h).2) le_rfl
      (fun _ h => h) le_rfl
  · exact ⟨fun _ => Set.univ, by simp, fun _ _ _ _ => Iff.rfl,
      fun μ h => absurd (hpre μ h).1 hvv⟩

omit [Has ScalarOp O] [Has IdxTst Q] in
/-- The exit of the capped loop on the good tapes: from the state before round $i \le 2(n + 1)$
with the loop test false or the fuel spent, the stack is empty, so the exit skips, and the
stored matrix is upper triangular and tracked with the final errors. -/
theorem roundedWorklistExit_reached {I : Interp O Q ℝ} (hC : IsCmp id I) {n : ℕ} {u εL e : ℝ}
    (hu0 : 0 ≤ u) (hεL : 0 ≤ εL) (he0 : 0 ≤ e) {k F T ns w m i : ℕ} {thr : ℝ} {ps : List ℝ}
    {H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {a t p uo f st wk ub r : ℕ × ℕ} {τ : Tape ℝ}
    {μ : Mem ℝ} (hi : i ≤ 2 * (n + 1))
    (hst : SchurReached n H U u εL e m thr ps a t p uo f st wk ub r i μ)
    (hcase : i = 2 * (n + 1) ∨ I.testAt (Has.inj CmpTst.isPos) [] [{ buf := 4, off := IExp.var 11 }]
      ((Env.frame [n + 1, k, ps.length, F, T, ns, w] [a, t, p, uo, st, wk, ub, r, f]).pushIdx i)
      μ = some false) :
    Writes .total I τ (Stmt.ite (Has.inj CmpTst.isPos) [] [{ buf := 4, off := IExp.var 11 }]
        (Stmt.frame [] [{ buf := 4, off := IExp.var 11 }, { buf := 8, off := IExp.var 15 }]
          (roundedAbort (O := O) (Q := Q))) Stmt.skip)
      ((Env.frame [n + 1, k, ps.length, F, T, ns, w] [a, t, p, uo, st, wk, ub, r, f]).pushIdx i)
      ⊥ (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ U' Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          HoldsMatrix a Tm μ'.store ∧ HoldsMatrix uo U' μ'.store ∧ Tm.IsUpperTriangular ∧
          IsTrackedUnitarySimilar
            ((1 + 24 * u) ^ (2 * (n + 1) * m) * (1 + εL) ^ (n + 1) - 1) (2 * (n + 1) * e)
            U H U' Tm) μ := by
  obtain ⟨hG, -, -, hf, rs, done, A, U', hSt, hA, hU', hsh, hcnt, htr⟩ := hst
  have hlen0 := (hsh.deflationInv (H := A) (V := 1) (ε := 0)
    (by simpa using IsPerturbedUnitarySimilarBy.refl A)).length_le
  simp only [List.length_append] at hlen0
  have hrs : rs = [] := by
    rcases hcase with rfl | htest
    · exfalso; omega
    · rw [Interp.testAt_eq rfl rfl, hC.test_isPos hSt.1] at htest
      by_contra hne
      have hp : (0 : ℝ) < rs.length := by exact_mod_cast List.length_pos_iff.mpr hne
      simp [hp] at htest
  subst hrs
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := st) hSt.1) ?_
  rw [if_neg (by simp)]
  refine Writes.skip ⟨hf, U', A, hA, hU', hsh.isUpperTriangular, htr.mono ?_ ?_⟩
  · have := accumFactor_le_final hu0 hεL m hi (show done.length ≤ n + 1 by simpa using hlen0)
    linarith
  · have : (i : ℝ) ≤ 2 * (n + 1) := by exact_mod_cast hi
    nlinarith

/-- The capped worklist in Schur mode on the good tapes: from the views of the worklist in
Schur mode holding an upper Hessenberg $\mathbf{H}$, diagonalizable with condition at most $B$
and eigenvalues separated by $g > 0$, an accumulator $\mathbf{U}$, the threshold word and the
parameter words, with the decoupler and the Schur leaf as in
`NLAlib.ShiftedQR.roundedRange_pwrites` and the round errors within $e$, the initialization and
the $2(n + 1)$ capped rounds reach, except with probability at most
$2(n + 1)(\varphi_L + \varphi_D)$, the failure word $0$, an upper triangular stored matrix and an
accumulator tracked from $(\mathbf{U}, \mathbf{H})$ with the errors
$((1 + 24\boldsymbol{u})^{2(n+1)m}(1 + \varepsilon_L)^{n+1} - 1, 2(n + 1)e)$.

Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and `NLAlib.SmallEig.smallEigRoutine`,
on their scratch. -/
theorem roundedWorklist_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ}
    {B g φD φL N₀ εL β e ω c thr : ℝ} {k F T ns w m : ℕ} (hm1 : ns * w ≤ m)
    (hm2 : 2 * k * (k + 2) ≤ m) {ps : List ℝ} {ε : ℝ → ℝ} (D : Stmt O Q)
    (hD : RandomDecouplingRoutineContract law (2 * B) (g / 2) φD k F T n N₀ ps ns w ω ε D I)
    (L : Stmt O Q)
    (hLeaf : Schur.RandomSchurLeafContract law εL β φL (min k (n + 1)) N₀ ps T L I)
    (hφD : 0 ≤ φD) (hφL : 0 ≤ φL)
    {H U V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {dd : Fin (n + 1) → ℂ}
    (hHess : IsUpperHessenberg H) (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal dd) (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g)
    (hgap : ∀ i j, i ≠ j → g ≤ ‖dd i - dd j‖) (hεL : 0 ≤ εL)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (heD : ε N₀ + 78 * u * (ns * w : ℕ) * N₀ + c ≤ e)
    (heL : β + (8 * (n + 1) * (k + 2) * u * N₀ + 2 * εL * N₀) ≤ e)
    (hroomD : 2 * (n + 1) * (78 * u * (ns * w : ℕ) * N₀) ≤ N₀)
    (hroomL : 2 * (n + 1) * (8 * (n + 1) * (k + 2) * u * N₀) ≤ N₀) (he0 : 0 ≤ e)
    (hN₀ : specNorm H + 2 * (n + 1) * e ≤ N₀) (hsmall : 2 * (n + 1) * e ≤ g / (16 * (n + 1) * B))
    {a t p uo f st wk ub r : ℕ × ℕ} :
    PWrites law I (roundedWorklistWith D L)
      (Env.frame [n + 1, k, ps.length, F, T, ns, w] [a, t, p, uo, st, wk, ub, r, f])
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (fun μ => SchurGeometry (n + 1) ps.length a t p uo f st wk ub r μ ∧
        HoldsMatrix a H μ.store ∧ HoldsMatrix uo U μ.store ∧ μ.store.get t.1 t.2 = some thr ∧
        μ.store.readBlock p.1 p.2 ps.length = some ps)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ U' Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          HoldsMatrix a Tm μ'.store ∧ HoldsMatrix uo U' μ'.store ∧ Tm.IsUpperTriangular ∧
          IsTrackedUnitarySimilar
            ((1 + 24 * u) ^ (2 * (n + 1) * m) * (1 + εL) ^ (n + 1) - 1) (2 * (n + 1) * e)
            U H U' Tm)
      (2 * (n + 1) * (φL + φD)) := by
  have h0 : Mch.lit ((0 : ℕ) : ℚ) = 0 := by simpa using hNat 0 (Nat.zero_le _)
  unfold roundedWorklistWith
  refine (PWrites.seq hI hloc (by positivity)
    (PWrites.of_writes (F := Store.inBlock f.1 f.2 1) (Post := fun μ₁ => ∃ μ,
      (SchurGeometry (n + 1) ps.length a t p uo f st wk ub r μ ∧ HoldsMatrix a H μ.store ∧
        HoldsMatrix uo U μ.store ∧ μ.store.get t.1 t.2 = some thr ∧
        μ.store.readBlock p.1 p.2 ps.length = some ps) ∧
      μ.store.EqOff (Store.inBlock f.1 f.2 1) μ₁.store ∧ μ₁.store.get f.1 f.2 = some 0) le_rfl
      fun μ τ hpre => ?_)
    (PWrites.seq hI hloc (by positivity)
      (PWrites.of_writes (F := Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
        (Post := SchurReached n H U u εL e m thr ps a t p uo f st wk ub r 0) le_rfl
        fun μ₁ τ ⟨μ, ⟨hG, hA, hU, ht, hp⟩, hfr₁, hF₁⟩ => ?_)
      (PWrites.whileFuel (F := schurRoundFp (n + 1) a uo f st wk ub r) (G := ⊥)
        (N := 2 * (n + 1)) hI hloc rfl
        (SchurReached n H U u εL e m thr ps a t p uo f st wk ub r)
        (fun _ => φL + φD) (fun _ _ => by positivity) le_rfl (fun _ h => h) ?_ ?_ ?_))).mono
    (fun _ h => h) (by fp_sub [schurRoundFp]) (fun _ h => h) (le_of_eq ?_)
  · refine (writes_indexLit hL rfl rfl
      (by have := hpre.1.room.2.2.2.2.1; omega)).mono le_rfl ?_
    rintro μ₁ hfr ⟨-, hF⟩
    exact ⟨μ, hpre, hfr, by simpa only [h0] using hF⟩
  · have hG₁ := hG.of_eqOff hfr₁
    have hlS : μ₁.Live [st] := hG₁.live_of_subset (by simp)
    have g : ∀ i j : Fin 9, i ≠ j → ¬(i = 1 ∧ j = 2) ∧ ¬(i = 2 ∧ j = 1) → _ :=
      fun i j h h' => hG.disj' i j h h'
    have hFA : Fp.Disj (Store.inBlock f.1 f.2 1)
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := by
      simpa [schurBlock] using g 4 0 (by simp) (by decide)
    have hFU : Fp.Disj (Store.inBlock f.1 f.2 1)
        (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) := by
      simpa [schurBlock] using g 4 3 (by simp) (by decide)
    have hFS : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) := by
      simpa using g 4 5 (by simp) (by decide)
    have hSA : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := by
      simpa [schurBlock] using g 5 0 (by simp) (by decide)
    have hSU : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
        (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) := by
      simpa [schurBlock] using g 5 3 (by simp) (by decide)
    refine ((stackInit_writes_of_isExactNatLit (Op := O) (Tst := Q) (τ := τ) hL hQ hNat
      (lo := 0) (size := n + 1) (by omega) le_rfl le_rfl (Nat.succ_pos n)
      (by simpa only [Nat.add_assoc] using hG₁.room.2.2.2.2.2.1)).in_frame rfl rfl hlS).mono
      le_rfl ?_
    rintro μ₂ hfr₂ ⟨-, hSt₂⟩
    have hfr₁₂ := hfr₁.trans' hfr₂
    refine SchurReached.of_core hG ht hp hfr₁₂ (by fp_sub [schurRoundFp])
      ⟨hfr₂.keep (Store.readsOnly_get _ _ _) hFS.symm hF₁, [(0, n + 1)], [], H, U, hSt₂,
        hA.of_eqOff hfr₁₂ (Fp.disj_sup_left.mpr ⟨hFA, hSA⟩),
        hU.of_eqOff hfr₁₂ (Fp.disj_sup_left.mpr ⟨hFU, hSU⟩), SchurShape.init hHess, by simp, ?_⟩
    simpa using IsTrackedUnitarySimilar.refl U H
  · rintro i - μ hst
    obtain ⟨-, -, -, -, rs, -, -, -, hSt, -⟩ := hst
    exact ⟨_, by rw [Interp.testAt_eq rfl rfl, hC.test_isPos hSt.1]⟩
  · intro i hi
    refine ((roundedWorklistRound_pwrites hS hM hu0 hu hL hNat hQ hC hI hloc hm1 hm2 D hD L hLeaf
      hφD hφL hV hHV hκ hg hgap hεL hfind hcut hc heD heL hroomD hroomL he0 hN₀ hsmall
      hi).in_frame rfl rfl fun μ h => h.1.1.live_of_subset (by simp)).mono
      (fun μ ⟨hst, htest⟩ => ?_) le_rfl (fun _ h => h) le_rfl
    obtain ⟨-, -, -, -, rs, -, -, -, hSt, -⟩ := id hst
    rw [Interp.testAt_eq rfl rfl, hC.test_isPos hSt.1] at htest
    have hpos : (0 : ℝ) < id (rs.length : ℝ) := of_decide_eq_true (Option.some.inj htest)
    exact ⟨hst, rs.length, hSt.1, by simpa using hpos⟩
  · exact fun i hi => PWrites.of_writes le_rfl fun μ τ ⟨hst, hcase⟩ =>
      roundedWorklistExit_reached hC hu0 hεL he0 hi hst hcase
  · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_zero, zero_add]
    push_cast
    ring

/-- **The rounded worklist in Schur mode as a probabilistic block**
([BanksGarzaVargasSrivastava2022, Theorem 6.3] with the Schur form): on a scalar machine with the
standard model at $0 \le \boldsymbol{u} \le 1/100$, exact natural literals up to $n + 1$, exact
`toNat` and comparisons, and a measurable tape-local interpretation, let the decoupler meet
`NLAlib.ShiftedQR.RandomDecouplingRoutineContract` on the class $(2B, g/2)$ with error
$\varepsilon(N_0)$, and the leaf meet the Schur leaf contract
(`NLAlib.Schur.RandomSchurLeafContract`) with errors $(\varepsilon_L, \beta)$ on orders at most
$\min(k, n + 1)$. From an upper Hessenberg $\mathbf{H}$, diagonalizable with condition at most $B$
and eigenvalues separated by $g > 0$, and an accumulator $\mathbf{U}$, with the threshold word $t$,
$(1 + \boldsymbol{u})^2\omega^2 \le t \le (1 - \boldsymbol{u})^2c^2$, $c, \beta, \varepsilon(N_0),
\varepsilon_L, N_0 \ge 0$ and the round error $e = c + \varepsilon(N_0) + \beta +
2\varepsilon_L N_0 + \rho + \rho_L$ with the replay and product errors
$\rho = 78\boldsymbol{u}\,n_s w N_0$ and $\rho_L = 8(n + 1)(k + 2)\boldsymbol{u}N_0$,
$\|\mathbf{H}\|_2 + 2(n + 1)e \le N_0$ and $2(n + 1)e \le g/(16(n + 1)B)$, except with
probability at most $2(n + 1)(\varphi_D + \varphi_L)$ the flag is $0$, the stored matrix
$\widehat{\mathbf{T}}$ is upper triangular and $(\widehat{\mathbf{U}}, \widehat{\mathbf{T}})$ is
tracked from $(\mathbf{U}, \mathbf{H})$ (`NLAlib.IsTrackedUnitarySimilar`) with the backward error
$2(n + 1)e$ and the relative accumulator error
$(1 + 24\boldsymbol{u})^{2(n+1)(n_s w + 2k(k+2))}(1 + \varepsilon_L)^{n+1} - 1$.

Shared by the trees of `NLAlib.ShiftedQR.shqrSmallEigRoutine` and `NLAlib.SmallEig.smallEigRoutine`,
on their scratch. -/
theorem solveRoundedWith_pwrites {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) (hI : I.IsMeasurable) {win : O → List ℕ → ℕ}
    (hloc : ∀ o, I.TapeLocal o (win o)) {law : ℕ → Measure ℝ} {B g φD εL β φL : ℝ}
    {k F T ns w : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Stmt O Q) {N₀ : ℝ}
    (hD : RandomDecouplingRoutineContract law (2 * B) (g / 2) φD k F T n N₀ ps ns w ω ε D I)
    (L : Stmt O Q)
    (hLeaf : Schur.RandomSchurLeafContract law εL β φL (min k (n + 1)) N₀ ps T L I)
    (hφD : 0 ≤ φD) (hφL : 0 ≤ φL) (hεL : 0 ≤ εL) {a t p uo f : ℕ × ℕ}
    {H U V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} {thr c : ℝ}
    (hHess : IsUpperHessenberg H) (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d)
    (hκ : pseudoConditionNumber V ≤ B) (hg : 0 < g) (hgap : ∀ i j, i ≠ j → g ≤ ‖d i - d j‖)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀) (hN0 : 0 ≤ N₀)
    (hN₀ : specNorm H + 2 * (n + 1) * (c + ε N₀ + β + 2 * εL * N₀ + 78 * u * (ns * w) * N₀ +
      8 * (n + 1) * (k + 2) * u * N₀) ≤ N₀)
    (hsmall : 2 * (n + 1) * (c + ε N₀ + β + 2 * εL * N₀ + 78 * u * (ns * w) * N₀ +
      8 * (n + 1) * (k + 2) * u * N₀) ≤ g / (16 * (n + 1) * B)) :
    PWrites law I (solveRoundedWith D L)
      (Env.frame [n + 1, k, ps.length, F, T, ns, w] [a, t, p, uo, a, uo, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ => μ.Live [a, t, p, uo, f] ∧
        μ.Room [a, t, p, uo, f]
          [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * ((n + 1) * (n + 1)), 1] ∧
        ShQRViewsApart (n + 1) ps.length a t p uo f ∧
        HoldsMatrix a H μ.store ∧ HoldsMatrix uo U μ.store ∧ μ.store.get t.1 t.2 = some thr ∧
        μ.store.readBlock p.1 p.2 ps.length = some ps)
      (fun μ' => μ'.store.get f.1 f.2 = some 0 ∧
        ∃ U' Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
          HoldsMatrix a Tm μ'.store ∧ HoldsMatrix uo U' μ'.store ∧ Tm.IsUpperTriangular ∧
          IsTrackedUnitarySimilar
            ((1 + 24 * u) ^ (2 * (n + 1) * (ns * w + 2 * k * (k + 2))) * (1 + εL) ^ (n + 1) - 1)
            (2 * (n + 1) * (c + ε N₀ + β + 2 * εL * N₀ + 78 * u * (ns * w) * N₀ +
              8 * (n + 1) * (k + 2) * u * N₀)) U H U' Tm)
      (2 * (n + 1) * (φD + φL)) := by
  set e := c + ε N₀ + β + 2 * εL * N₀ + 78 * u * (ns * w) * N₀ + 8 * (n + 1) * (k + 2) * u * N₀
  have hnw : ((ns * w : ℕ) : ℝ) = ns * w := by push_cast; ring
  have h1 : 0 ≤ 2 * εL * N₀ := by positivity
  have h2 : 0 ≤ 78 * u * (ns * w) * N₀ := by positivity
  have h3 : 0 ≤ 8 * ((n : ℝ) + 1) * (k + 2) * u * N₀ := by positivity
  have he0 : 0 ≤ e := by positivity
  have hHn := specNorm_nonneg H
  have hn1 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hroomD : 2 * (n + 1) * (78 * u * (ns * w : ℕ) * N₀) ≤ N₀ := by
    rw [hnw]; nlinarith
  have hroomL : 2 * (n + 1) * (8 * (n + 1) * (k + 2) * u * N₀) ≤ N₀ := by nlinarith
  unfold solveRoundedWith
  refine PWrites.allocs (lens := [.const 1 + .const 2 * .var 0, .const 2 * (.var 0 * .var 0),
    .const 2 * (.var 0 * .var 0), .const 5])
    (ns := [1 + 2 * (n + 1), 2 * ((n + 1) * (n + 1)), 2 * ((n + 1) * (n + 1)), 5]) rfl
    (Pre₁ := fun b₀ μ => SchurGeometry (n + 1) ps.length a t p uo f (b₀, 0) (b₀ + 1, 0)
      (b₀ + 2, 0) (b₀ + 3, 0) μ ∧ HoldsMatrix a H μ.store ∧ HoldsMatrix uo U μ.store ∧
      μ.store.get t.1 t.2 = some thr ∧ μ.store.readBlock p.1 p.2 ps.length = some ps) ?_ ?_
    fun b₀ => ?_
  · rintro μ s₁ ⟨hl, hr, ha, hA, hU, ht, hp⟩ hs hlens hBelow
    exact ⟨SchurGeometry.allocated hl hr ha hs hlens hBelow, hA.of_below hBelow (hl a (by simp)),
      hU.of_below hBelow (hl uo (by simp)), ((hBelow t.1 (hl t (by simp))).2 _).trans ht,
      (hBelow.readBlock (hl p (by simp)) p.2 ps.length).trans hp⟩
  · rintro μ ⟨hl, -⟩ s s' pos hBelow ⟨hf, U', Tm, hTm, hU', hrest⟩
    exact ⟨((hBelow f.1 (hl f (by simp))).2 _).trans hf, U', Tm,
      hTm.of_below hBelow (hl a (by simp)), hU'.of_below hBelow (hl uo (by simp)), hrest⟩
  refine ((roundedWorklist_pwrites (F := F) (T := T) (st := (b₀, 0)) (wk := (b₀ + 1, 0))
    (ub := (b₀ + 2, 0)) (r := (b₀ + 3, 0)) (e := e) hS hM hu hu1 hL hNat hQ hC hI hloc le_self_add
    le_add_self D hD L hLeaf hφD hφL hHess hV hHV hκ hg hgap hεL hfind hcut hc
    (by rw [hnw]; simp only [e]; linarith) (by simp only [e]; linarith) hroomD hroomL he0 hN₀
    hsmall).in_frame (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    fun μ h => h.1.live_of_subset (by simp)).mono (fun _ h => h) ?_ (fun _ h => h)
    (le_of_eq (by ring))
  intro b i h
  simp only [schurRoundFp, Fp.blocks_cons, Fp.blocks_nil, fpNF] at h ⊢
  omega

end Theorems

end NLAlib.ShiftedQR
