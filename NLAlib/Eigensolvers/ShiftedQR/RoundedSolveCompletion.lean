/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedWorklistTermination

/-!
# The rounded deflation worklist in Schur mode always terminates

The termination-only counterpart of `NLAlib.ShiftedQR.solveRoundedWith_pwrites`: on every tape
and from every stored matrix and accumulator, `NLAlib.ShiftedQR.solveRoundedWith` runs to completion
when its decoupler and its Schur leaf do (`NLAlib.ShiftedQR.TerminatingDecouplerRoutine`,
`NLAlib.ShiftedQR.CompletingLeafRoutine`), with no rounding model; under the standard model and with
a leaf whose accumulator is near a unitary (`NLAlib.ShiftedQR.TerminatingLeafRoutine`), the stored
accumulator stays near the input accumulator times a unitary. The proof follows the rounds with a
value-free state (`NLAlib.Eigensolvers.ShiftedQR.RoundedWorklistTermination`): the views keep
their geometry, every word read is stored, the stack holds nonempty ranges inside the order whose
sizes plus the number of finished leaves sum to at most the order, and the accumulator is within
a factor that grows by $(1 + 24\boldsymbol{u})^{n_s w}$ per decoupled block (the replay of its log,
`NLAlib.specNorm_foldl_replayColumnStep_sub_le`) and by $(1 + 24\boldsymbol{u})^{2k(k+2)}(1 +
\varepsilon_L)$ per leaf (the product with the leaf's accumulator,
`NLAlib.specNorm_setRect_matMulWord_sub_le`). The fuel of the loop makes the run finite.

## Main results

* `NLAlib.ShiftedQR.roundedWorklistRound_terminates`: one round keeps the value-free state.
* `NLAlib.ShiftedQR.solveRoundedWith_completes`: the rounded worklist in Schur mode runs to
  completion on any scalar machine (no rounding model).
* `NLAlib.ShiftedQR.solveRoundedWith_terminates`: the same with the accumulator bound under the
  standard model.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix
variable {O Q : Type}

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- A leaf multiplies the accumulator factor by at most $(1 + 24\boldsymbol{u})^m(1 +
\varepsilon_L)$: with $2d(d + 2) \le m$, round $j$ with $\ell$ leaves times the leaf factor is at
most round $j + 1$ with $\ell + 1$ leaves. -/
theorem accumFactor_leaf_le {u εL : ℝ} (hu0 : 0 ≤ u) (hεL : 0 ≤ εL) {d m j ℓ : ℕ}
    (hdm : 2 * d * (d + 2) ≤ m) :
    (1 + 24 * u) ^ (j * m) * (1 + εL) ^ ℓ * ((1 + 24 * u) ^ (2 * d * (d + 2)) * (1 + εL)) ≤
      (1 + 24 * u) ^ ((j + 1) * m) * (1 + εL) ^ (ℓ + 1) := by
  have hX1 : (1 : ℝ) ≤ 1 + 24 * u := by linarith
  have h1 : (1 + 24 * u) ^ (2 * d * (d + 2)) ≤ (1 + 24 * u) ^ m := pow_le_pow_right₀ hX1 hdm
  rw [add_mul, one_mul, pow_add, pow_succ]
  have h0 : 0 ≤ (1 + 24 * u) ^ (j * m) * (1 + εL) ^ ℓ :=
    mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
  have h2 := mul_le_mul_of_nonneg_left h1 h0
  have h3 : (0 : ℝ) ≤ 1 + εL := by linarith
  nlinarith

omit [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The leaf branch keeps the core: on a scalar machine, with the standard model at
$\boldsymbol{u} \le 1/100$ if `P`, and a Schur leaf on orders at most $\min(k, n + 1)$ whose
accumulator is within $\varepsilon_L \ge 0$ of a unitary if `P`
(`NLAlib.ShiftedQR.TerminatingLeafRoutineIf`), from the
geometry of the worklist in Schur mode with the parameter words stored, any failure word, a
matrix $\mathbf{A}$ whose block on $(lo, d)$, $d \le k$, is in the work matrix, a stack whose
ranges after $(lo, d)$ fit with a leaf count $\ell$, and the accumulator within its factor at
round $j$ ($2k(k + 2) \le m$), the leaf, the copy back and `NLAlib.ShiftedQR.roundedLeafUpdate`
reach the core of round $j + 1$ with $\ell + 1$ leaves. -/
theorem roundedLeafBranch_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) {P : Prop} (hP : P → StdModel u id Mch ∧ u ≤ 1 / 100) {n : ℕ}
    {k F T ns w m : ℕ} (hm : 2 * k * (k + 2) ≤ m) {ps : List ℝ} {εL : ℝ} (hεL : P → 0 ≤ εL)
    (L : Stmt O Q) (hLeaf : TerminatingLeafRoutineIf P εL (min k (n + 1)) ps T L I) {tape : Tape ℝ}
    {μ : Mem ℝ} {lo d j ℓ : ℕ} {a t p uo f st wk ub r : ℕ × ℕ} {rs : List (ℕ × ℕ)}
    {A U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {x : ℝ}
    (hG : SchurGeometry (n + 1) ps.length a t p uo f st wk ub r μ)
    (hp : μ.store.readBlock p.1 p.2 ps.length = some ps) (hf : μ.store.get f.1 f.2 = some x)
    (hA : HoldsMatrix a A μ.store) (hW : HoldsMatrix wk (subBlock A (lo, d)) μ.store)
    (hSt : StackHolds st rs μ.store) (hfit : RangesFit (n + 1) ((lo, d) :: rs))
    (hℓ : ℓ + d + (rs.map Prod.snd).sum ≤ n + 1) (hdk : d ≤ k)
    (hacc : AccumIf P U ((1 + 24 * u) ^ (j * m) * (1 + εL) ^ ℓ) uo μ) :
    Writes .total I tape
      ((Stmt.frame [IExp.var 8, IExp.var 2, IExp.var 4]
          [{ buf := 5, off := IExp.var 14 }, { buf := 2, off := IExp.var 11 },
            { buf := 5, off := IExp.var 14 }, { buf := 6, off := IExp.var 15 }] L).seq
        ((Stmt.frame [IExp.var 0, IExp.var 7, IExp.var 8]
            [{ buf := 5, off := IExp.var 14 }, { buf := 0, off := IExp.var 9 }]
            (copyToGlobal (Op := O) (Tst := Q))).seq
          (Stmt.frame [IExp.var 0, IExp.var 7, IExp.var 8]
            [{ buf := 6, off := IExp.var 15 }, { buf := 0, off := IExp.var 9 },
              { buf := 4, off := IExp.var 13 }] (roundedLeafUpdate (O := O) (Q := Q)))))
      (Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d] [a, t, p, st, uo, wk, ub, r, f])
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (SchurStoredCore n P U u εL m a uo f st (j + 1)) μ := by
  have hu0 : P → 0 ≤ u := fun hp => (abs_nonneg _).trans (by simpa using (hP hp).1.lit 1)
  have hfit0 := hfit.1 _ List.mem_cons_self
  dsimp only at hfit0
  have hd : d ≤ n + 1 := by omega
  have hsq := Nat.mul_le_mul hd hd
  have hWd : Store.inBlock wk.1 wk.2 (2 * (d * d)) ≤
      Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  have hUd : Store.inBlock ub.1 ub.2 (2 * (d * d)) ≤
      Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  have g : ∀ i j : Fin 9, i ≠ j → _ := fun i j h => hG.disj' i j h
  have hWU : Fp.Disj (Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using g 6 7 (by simp)
  have hPW : Fp.Disj (Store.inBlock p.1 p.2 ps.length)
      (Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using g 2 6 (by simp)
  have hPU : Fp.Disj (Store.inBlock p.1 p.2 ps.length)
      (Store.inBlock ub.1 ub.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using g 2 7 (by simp)
  have hlL : μ.Live [wk, p, ub] := hG.live_of_subset (by simp)
  refine ((hLeaf (tape := tape) (subBlock A (lo, d)) (le_min hdk hd) hW hp hlL
    (by have := hG.room.2.2.2.2.2.2.2.1; dsimp only; omega) (hWU.mono hWd hUd)
    (Fp.disj_sup_right.mpr ⟨hPW.mono le_rfl hWd, hPU.mono le_rfl hUd⟩)).in_frame rfl rfl
    (hG.live_of_subset (by simp))).seq_le (by fp_sub [schurRoundFp]) ?_
  rintro μ₁ hfr₁ ⟨Tb, Ub, hTb, hUb, hUbV⟩
  have hWUd : ∀ i : Fin 9, i ≠ 6 → i ≠ 7 → Fp.Disj
      (Store.inBlock wk.1 wk.2 (2 * (d * d)) ⊔ Store.inBlock ub.1 ub.2 (2 * (d * d)))
      (schurBlock (n + 1) ps.length a t p uo f st wk ub r i) :=
    fun i h6 h7 => Fp.disj_sup_left.mpr ⟨(g 6 i (Ne.symm h6)).mono hWd le_rfl,
      (g 7 i (Ne.symm h7)).mono hUd le_rfl⟩
  have hA₁ := hA.of_eqOff hfr₁ (hWUd 0 (by simp) (by simp))
  have hf₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (hWUd 4 (by simp) (by simp)) hf
  have hSt₁ := hSt.of_eqOff hfr₁ ((hWUd 5 (by simp) (by simp)).mono le_rfl
    (Fp.inBlock_le_inBlock le_rfl (by have := hfit.length_add_le; simp; omega)))
  have hacc₁ := hacc.of_eqOff hfr₁ (hWUd 3 (by simp) (by simp))
  have hG₁ := hG.of_eqOff hfr₁
  have hAW : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using g 0 6 (by simp)
  have hlWA : μ₁.Live [wk, a] := hG₁.live_of_subset (by simp)
  refine ((copyToGlobal_writes (τ := tape) hS hlWA hA₁ hTb hfit0.2 hG₁.room.1
    (hAW.symm.mono hWd le_rfl)).in_frame rfl rfl hlWA).seq_le
    ((blockFp_le a hfit0.2).trans (by fp_sub [schurRoundFp])) ?_
  rintro μ₂ hfr₂ ⟨-, hA₂⟩
  have hAX : ∀ i : Fin 9, i ≠ 0 → Fp.Disj ((EntryCodec.pair ℝ).regionFp a.1
      (a.2 + 2 * (lo * (n + 1) + lo)) d (fun i j => j * (n + 1) + i) (fun _ => d))
      (schurBlock (n + 1) ps.length a t p uo f st wk ub r i) :=
    fun i h0 => (g 0 i (Ne.symm h0)).mono (blockFp_le a hfit0.2) le_rfl
  have hUb₂ := hUb.of_eqOff hfr₂ ((hAX 7 (by simp)).mono le_rfl hUd)
  obtain ⟨⟨U₁, hU₁⟩, hacc'⟩ := hacc₁
  have hU₂ := hU₁.of_eqOff hfr₂ (hAX 3 (by simp))
  have hG₂ := hG₁.of_eqOff hfr₂
  have hlU : μ₂.Live [ub, a, uo] := hG₂.live_of_subset (by simp)
  refine ((roundedLeafUpdate_writes (O := O) (Q := Q) (τ := tape) hS hfit0.2 hlU hUb₂ hA₂ hU₂
    hG₂.room.1 hG₂.room.2.2.2.1 ((g 7 0 (by simp)).mono hUd le_rfl)
    (by simpa [schurBlock] using g 0 3 (by simp))).in_frame rfl rfl hlU).mono
    (by fp_sub [schurRoundFp]) ?_
  rintro μ₃ hfr₃ ⟨-, hA₃, hU₃⟩
  have hAU3 : ∀ i : Fin 9, i ≠ 0 → i ≠ 3 → Fp.Disj
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))))
      (schurBlock (n + 1) ps.length a t p uo f st wk ub r i) :=
    fun i h0 h3 => Fp.disj_sup_left.mpr ⟨g 0 i (Ne.symm h0), g 3 i (Ne.symm h3)⟩
  have hst5 : Store.inBlock st.1 st.2 (1 + 2 * rs.length) ≤
      Store.inBlock st.1 st.2 (1 + 2 * (n + 1)) :=
    Fp.inBlock_le_inBlock le_rfl (by have := hfit.length_add_le; omega)
  refine ⟨⟨x, (hfr₂.trans' hfr₃).keep (Store.readsOnly_get _ _ _)
      (Fp.disj_sup_left.mpr ⟨hAX 4 (by simp), hAU3 4 (by simp) (by simp)⟩) hf₁⟩,
    ⟨_, hA₃⟩, rs, ℓ + 1, (hSt₁.of_eqOff hfr₂ ((hAX 5 (by simp)).mono le_rfl hst5)).of_eqOff hfr₃
      ((hAU3 5 (by simp) (by simp)).mono le_rfl hst5), hfit.of_cons, by omega, ⟨_, hU₃⟩,
    fun hp => ?_⟩
  have hX1 : (1 : ℝ) ≤ 1 + 24 * u := by linarith [hu0 hp]
  obtain ⟨V, hV, hUbV⟩ := hUbV hp
  refine AccumNear.step ((hacc' hp).of_eqOff hfr₂ (hAX 3 (by simp))) hU₂ hU₃
    (hasOrthonormalCols_embedBlock hfit0.2 hV)
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hX1) (by linarith [hεL hp]))
    (specNorm_setRect_matMulWord_sub_le (hP hp).1 (hu0 hp) (by linarith [(hP hp).2]) hfit0.2 U₁ hV
      (hεL hp) hUbV) ?_
  exact accumFactor_leaf_le (hu0 hp) (hεL hp) (le_trans (by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hdk) (Nat.add_le_add_right hdk 2); linarith) hm)

/-- Processing a popped range keeps the core: under the conditions of
`NLAlib.ShiftedQR.roundedLarge_terminates` and `NLAlib.ShiftedQR.roundedLeafBranch_terminates`
($n_s w \le m$, $2k(k + 2) \le m$), from the geometry of the worklist in Schur mode with the
threshold and parameter words and the failure word stored, a matrix $\mathbf{A}$, a stack whose
ranges after the popped $(lo, d)$ fit with a leaf count $\ell$, and the accumulator within its
factor at round $j$, `NLAlib.ShiftedQR.roundedProcessRangeWith` reaches the core of round
$j + 1$. -/
theorem roundedRange_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I)
    {P : Prop} (hP : P → StdModel u id Mch ∧ u ≤ 1 / 100) (hL : IsIndexLit Mch I)
    {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    {k F T ns w m : ℕ} (hm1 : ns * w ≤ m) (hm2 : 2 * k * (k + 2) ≤ m) {ps : List ℝ} {εL : ℝ}
    (hεL : P → 0 ≤ εL) (D : Stmt O Q) (hD : TerminatingDecouplerRoutine n k F T ps ns w D I)
    (L : Stmt O Q) (hLeaf : TerminatingLeafRoutineIf P εL (min k (n + 1)) ps T L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {lo d j ℓ : ℕ} {a t p uo f st wk ub r : ℕ × ℕ}
    {rs : List (ℕ × ℕ)} {A U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr x : ℝ}
    (hG : SchurGeometry (n + 1) ps.length a t p uo f st wk ub r μ)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps)
    (hf : μ.store.get f.1 f.2 = some x) (hA : HoldsMatrix a A μ.store)
    (hSt : StackHolds st rs μ.store) (hfit : RangesFit (n + 1) ((lo, d) :: rs))
    (hℓ : ℓ + d + (rs.map Prod.snd).sum ≤ n + 1)
    (hacc : AccumIf P U ((1 + 24 * u) ^ (j * m) * (1 + εL) ^ ℓ) uo μ) :
    Writes .total I tape (roundedProcessRangeWith D L)
      (Env.frame [n + 1, k, ps.length, F, T, ns, w, lo, d] [a, t, p, st, uo, wk, ub, r, f])
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (SchurStoredCore n P U u εL m a uo f st (j + 1)) μ := by
  have hfit0 := hfit.1 _ List.mem_cons_self
  dsimp only at hfit0
  have hd : d ≤ n + 1 := by omega
  have hsq := Nat.mul_le_mul hd hd
  have hWd : Store.inBlock wk.1 wk.2 (2 * (d * d)) ≤
      Store.inBlock wk.1 wk.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  have g : ∀ i : Fin 9, i ≠ 6 → _ := fun i h => (hG.disj' 6 i (Ne.symm h)).mono hWd le_rfl
  have hlAW : μ.Live [a, wk] := hG.live_of_subset (by simp)
  unfold roundedProcessRangeWith
  refine (copyToWork_writes (τ := tape) (lo := lo) (d := d) hS hlAW hA hfit0.2
    (by have := hG.room.2.2.2.2.2.2.1; omega)
    (by simpa [schurBlock] using (g 0 (by simp)).symm)).frame_seq_le rfl rfl
    hlAW (hWd.trans (by fp_sub [schurRoundFp])) ?_
  rintro μ₁ hfr₁ ⟨-, hW₁⟩
  have hG₁ := hG.of_eqOff hfr₁
  have hf₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (by simpa [schurBlock] using g 4 (by simp)) hf
  have hA₁ := hA.of_eqOff hfr₁ (by simpa [schurBlock] using g 0 (by simp))
  have hSt₁ := hSt.of_eqOff hfr₁ ((by simpa [schurBlock] using g 5 (by simp) : Fp.Disj _
    (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))).mono le_rfl
      (Fp.inBlock_le_inBlock le_rfl (by have := hfit.length_add_le; omega)))
  have hp₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ _)
    (by simpa [schurBlock] using g 2 (by simp)) hp
  have ht₁ := hfr₁.keep (Store.readsOnly_get _ _ _) (by simpa [schurBlock] using g 1 (by simp)) ht
  have hacc₁ := hacc.of_eqOff hfr₁ (by simpa [schurBlock] using g 3 (by simp))
  by_cases hs : d ≤ k
  · refine (writes_ifPos (P := SchurStoredCore n P U u εL m a uo f st (j + 1)) (n := k + 1 - d)
      rfl ?_).seq_le le_rfl ?_
    · rw [if_pos (by omega)]
      exact roundedLeafBranch_terminates (F := F) (ns := ns) (w := w) hS hP hm2 hεL L hLeaf hG₁
        hp₁ hf₁ hA₁ hW₁ hSt₁ hfit hℓ hs hacc₁
    · intro μ₂ _ hpost
      refine writes_ifPos (n := d - k) rfl ?_
      rw [if_neg (by omega)]
      exact hpost
  · refine (writes_ifPos (F := ⊥) (P := fun μ₂ => μ₂ = μ₁) (n := k + 1 - d) rfl
      (by rw [if_neg (by omega)])).seq_le bot_le ?_
    rintro μ₂ - rfl
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    refine writes_ifPos (n := d' + 1 - k) rfl ?_
    rw [if_pos (by omega)]
    exact (roundedLarge_terminates hS hP hL hNat hQ hC hm1 D hD hεL hG₁ ht₁ hp₁ hA₁ hW₁ hSt₁
      hfit (by omega) (by omega) hacc₁).in_frame rfl rfl (hG₁.live_of_subset (by simp))

/-- One round keeps the value-free state: under the conditions of
`NLAlib.ShiftedQR.roundedRange_terminates`, from the state `NLAlib.ShiftedQR.SchurStoredState` of
round $j$ with a positive stack count, `NLAlib.ShiftedQR.roundedWorklistRoundWith` reaches the
state of round $j + 1$. -/
theorem roundedWorklistRound_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I)
    {P : Prop} (hP : P → StdModel u id Mch ∧ u ≤ 1 / 100) (hL : IsIndexLit Mch I)
    {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    {k F T ns w m : ℕ} (hm1 : ns * w ≤ m) (hm2 : 2 * k * (k + 2) ≤ m) {ps : List ℝ} {εL : ℝ}
    (hεL : P → 0 ≤ εL) (D : Stmt O Q) (hD : TerminatingDecouplerRoutine n k F T ps ns w D I)
    (L : Stmt O Q) (hLeaf : TerminatingLeafRoutineIf P εL (min k (n + 1)) ps T L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {j cnt : ℕ} {a t p uo f st wk ub r : ℕ × ℕ}
    {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h : SchurStoredState n P U u εL m ps a t p uo f st wk ub r j μ)
    (hcount : μ.store.get st.1 st.2 = some (cnt : ℝ)) (hpos : 0 < cnt) :
    Writes .total I tape (roundedWorklistRoundWith D L)
      (Env.frame [n + 1, k, ps.length, F, T, ns, w] [a, t, p, st, uo, wk, ub, r, f])
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (SchurStoredState n P U u εL m ps a t p uo f st wk ub r (j + 1)) μ := by
  obtain ⟨hG, ⟨thr, ht⟩, hp, ⟨x, hf⟩, ⟨A, hA⟩, rs, ℓ, hSt, hfit, hℓ, hacc⟩ := h
  refine Writes.mono (P := SchurStoredCore n P U u εL m a uo f st (j + 1)) ?_ le_rfl
    (fun μ' hfr hcore => SchurStoredState.of_core hG ⟨thr, ht⟩ hp hfr le_rfl hcore)
  obtain rfl | ⟨rs', ⟨lo, d⟩, rfl⟩ := List.eq_nil_or_concat rs
  · have hc0 : (cnt : ℝ) = 0 := Option.some.inj (hcount.symm.trans (by simpa using hSt.1))
    exact absurd (by exact_mod_cast hc0 : cnt = 0) (by omega)
  rw [List.concat_eq_append] at hfit hSt hℓ
  have hfit' := hfit.cons_of_concat
  have hfit0 := hfit'.1 _ List.mem_cons_self
  have hlen := hfit'.length_add_le
  dsimp only at hfit0
  have hℓ' : ℓ + d + (rs'.map Prod.snd).sum ≤ n + 1 := by
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at hℓ
    omega
  have g : ∀ i j : Fin 9, i ≠ j → _ := fun i j h => hG.disj' i j h
  have hRS : Fp.Disj (Store.inBlock r.1 r.2 2) (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) :=
    (by simpa [schurBlock] using g 8 5 (by simp) : Fp.Disj (Store.inBlock r.1 r.2 5)
      (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))).mono (by fp_sub) le_rfl
  have hlSR : μ.Live [st, r] := hG.live_of_subset (by simp)
  unfold roundedWorklistRoundWith
  refine (rangePop_writes_of_isExactNatLit (τ := tape) hS hL hQ hNat hSt (by omega)
    (by simpa only [Nat.add_assoc] using hG.room.2.2.2.2.2.1)
    (by have := hG.room.2.2.2.2.2.2.2.2.1; omega) hlSR hRS).frame_seq_le rfl rfl hlSR
    (by fp_sub [schurRoundFp]) ?_
  rintro μ₁ hfr₁ ⟨-, hSt₁, hRange⟩
  have hpd : ∀ i : Fin 9, i ≠ 5 → i ≠ 8 → Fp.Disj
      (Store.inBlock st.1 st.2 1 ⊔ Store.inBlock r.1 r.2 2)
      (schurBlock (n + 1) ps.length a t p uo f st wk ub r i) :=
    fun i h5 h8 => Fp.disj_sup_left.mpr
      ⟨(show Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) _ from g 5 i (Ne.symm h5)).mono
        (Fp.inBlock_le_inBlock le_rfl (by omega)) le_rfl,
      (show Fp.Disj (Store.inBlock r.1 r.2 5) _ from g 8 i (Ne.symm h8)).mono
        (Fp.inBlock_le_inBlock le_rfl (by omega)) le_rfl⟩
  have hLo : μ₁.store.get r.1 r.2 = some (lo : ℝ) := by
    simpa [vec] using Store.get_of_readBlock hRange (j := 0) (by omega) (0 : ℝ)
  have hSize : μ₁.store.get r.1 (r.2 + 1) = some (d : ℝ) := by
    simpa [vec] using Store.get_of_readBlock hRange (j := 1) (by omega) (0 : ℝ)
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hLo rfl (by omega) ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hSize rfl (by omega) ?_
  have hG₁ := hG.of_eqOff hfr₁
  exact (roundedRange_terminates hS hP hL hNat hQ hC hm1 hm2 hεL D hD L hLeaf hG₁
    (hfr₁.keep (Store.readsOnly_get _ _ _) (hpd 1 (by simp) (by simp)) ht)
    (hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hpd 2 (by simp) (by simp)) hp)
    (hfr₁.keep (Store.readsOnly_get _ _ _) (hpd 4 (by simp) (by simp)) hf)
    (hA.of_eqOff hfr₁ (hpd 0 (by simp) (by simp))) hSt₁ hfit' hℓ'
    (hacc.of_eqOff hfr₁ (hpd 3 (by simp) (by simp)))).in_frame rfl rfl
    (hG₁.live_of_subset (by simp))

/-- The accumulator factor at round $i \le 2(n + 1)$ with $\ell \le n + 1$ leaves is at most the
final factor. -/
theorem accumFactor_le_final {u εL : ℝ} (hu0 : 0 ≤ u) (hεL : 0 ≤ εL) {n i ℓ : ℕ} (m : ℕ)
    (hi : i ≤ 2 * (n + 1)) (hℓ : ℓ ≤ n + 1) :
    (1 + 24 * u) ^ (i * m) * (1 + εL) ^ ℓ ≤
      (1 + 24 * u) ^ (2 * (n + 1) * m) * (1 + εL) ^ (n + 1) :=
  mul_le_mul (pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right m hi))
    (pow_le_pow_right₀ (by linarith) hℓ) (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)

omit [Has ScalarOp O] [Has IdxTst Q] in
/-- The exit of the capped loop keeps a stored matrix and the accumulator within the final
factor: on a machine whose natural literals up to $n + 1$ are exact, with exact comparisons, from
the state `NLAlib.ShiftedQR.SchurStoredState` of round $i \le 2(n + 1)$, the exit of
`NLAlib.ShiftedQR.roundedWorklistWith` (abort on a positive stack count, else skip) runs to
completion. -/
theorem roundedWorklistExit_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hC : IsCmp id I)
    {k F T ns w m : ℕ} {ps : List ℝ} {tape : Tape ℝ} {μ : Mem ℝ} {u εL : ℝ} {P : Prop}
    (hu0 : P → 0 ≤ u) (hεL : P → 0 ≤ εL) {U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {a t p uo f st wk ub r : ℕ × ℕ} {i : ℕ} (hi : i ≤ 2 * (n + 1))
    (h : SchurStoredState n P U u εL m ps a t p uo f st wk ub r i μ) :
    Writes .total I tape (Stmt.ite (Has.inj CmpTst.isPos) [] [{ buf := 4, off := IExp.var 11 }]
        (Stmt.frame [] [{ buf := 4, off := IExp.var 11 }, { buf := 8, off := IExp.var 15 }]
          (roundedAbort (O := O) (Q := Q))) Stmt.skip)
      ((Env.frame [n + 1, k, ps.length, F, T, ns, w] [a, t, p, uo, st, wk, ub, r, f]).pushIdx i)
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (fun μ' => (∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A μ'.store) ∧
        AccumIf P U ((1 + 24 * u) ^ (2 * (n + 1) * m) * (1 + εL) ^ (n + 1)) uo μ') μ := by
  obtain ⟨hG, -, -, -, hA, rs, ℓ, hSt, -, hℓ, hacc⟩ := h
  have hℓ' : ℓ ≤ n + 1 := by omega
  refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := st) hSt.1) ?_
  by_cases hpos : 0 < rs.length
  · rw [if_pos (by simpa [schurBlock] using hpos)]
    exact ((roundedAbort_writes_schurCore hL hNat hG hA hℓ' hacc).in_frame rfl rfl
      (hG.live_of_subset (by simp))).mono (by fp_sub [schurRoundFp])
      fun _ _ hc => by
        obtain ⟨-, hA', rs', ℓ', -, -, hℓ'', hacc'⟩ := hc
        exact ⟨hA', hacc'.mono (fun hp => accumFactor_le_final (hu0 hp) (hεL hp) m hi (by omega))⟩
  · rw [if_neg (by simpa [schurBlock] using hpos)]
    exact (Writes.skip ⟨hA, hacc.mono (fun hp => accumFactor_le_final (hu0 hp) (hεL hp) m hi
      hℓ')⟩).mono bot_le
      fun _ _ h => h

/-- The capped loop of the worklist in Schur mode terminates: under the conditions of
`NLAlib.ShiftedQR.roundedRange_terminates`, from the geometry of the worklist in Schur mode with
any matrix $\mathbf{H}$, an accumulator $\mathbf{U}$, the threshold word and the parameter words
stored, `NLAlib.ShiftedQR.roundedWorklistWith` runs to completion within the round footprint and
leaves a matrix and an accumulator within
$((1 + 24\boldsymbol{u})^{2(n+1)m}(1 + \varepsilon_L)^{n+1} - 1)\|\mathbf{U}\|_2$ of
$\mathbf{U}$ times a unitary. -/
theorem roundedWorklist_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I)
    {P : Prop} (hP : P → StdModel u id Mch ∧ u ≤ 1 / 100) (hL : IsIndexLit Mch I)
    {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    {k F T ns w m : ℕ} (hm1 : ns * w ≤ m) (hm2 : 2 * k * (k + 2) ≤ m) {ps : List ℝ} {εL : ℝ}
    (hεL : P → 0 ≤ εL) (D : Stmt O Q) (hD : TerminatingDecouplerRoutine n k F T ps ns w D I)
    (L : Stmt O Q) (hLeaf : TerminatingLeafRoutineIf P εL (min k (n + 1)) ps T L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {a t p uo f st wk ub r : ℕ × ℕ}
    {H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr : ℝ}
    (hG : SchurGeometry (n + 1) ps.length a t p uo f st wk ub r μ)
    (hA : HoldsMatrix a H μ.store) (hU : HoldsMatrix uo U μ.store)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps) :
    Writes .total I tape (roundedWorklistWith D L)
      (Env.frame [n + 1, k, ps.length, F, T, ns, w] [a, t, p, uo, st, wk, ub, r, f])
      (schurRoundFp (n + 1) a uo f st wk ub r)
      (fun μ' => (∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a A μ'.store) ∧
        AccumIf P U ((1 + 24 * u) ^ (2 * (n + 1) * m) * (1 + εL) ^ (n + 1)) uo μ') μ := by
  have hu0 : P → 0 ≤ u := fun hp => (abs_nonneg _).trans (by simpa using (hP hp).1.lit 1)
  have g : ∀ i j : Fin 9, i ≠ j → _ := fun i j h => hG.disj' i j h
  have hFA : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) :=
    by simpa [schurBlock] using g 4 0 (by simp)
  have hFU : Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using g 4 3 (by simp)
  have hFS : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) := by
    simpa using g 4 5 (by simp)
  have hSA : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using g 5 0 (by simp)
  have hSU : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
      (Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1)))) :=
        by simpa [schurBlock] using g 5 3 (by simp)
  unfold roundedWorklistWith
  refine (writes_indexLit hL rfl rfl (by have := hG.room.2.2.2.2.1; dsimp only; omega)).seq_le
    (by fp_sub [schurRoundFp]) ?_
  rintro μ₁ hfr₁ ⟨-, hF₁⟩
  have hlS : μ₁.Live [st] := (hG.of_eqOff hfr₁).live_of_subset (by simp)
  have hw := stackInit_writes_of_isExactNatLit (Op := O) (Tst := Q) (τ := tape) hL hQ hNat
    (lo := 0) (size := n + 1) (by omega) le_rfl le_rfl (Nat.succ_pos n)
    (by simpa only [Nat.add_assoc] using (hG.of_eqOff hfr₁).room.2.2.2.2.2.1)
  refine hw.frame_seq_le rfl rfl hlS (by fp_sub [schurRoundFp]) ?_
  rintro μ₂ hfr₂ ⟨-, hSt₂⟩
  have hfr₁₂ := hfr₁.trans' hfr₂
  have hS0 : SchurStoredState n P U u εL m ps a t p uo f st wk ub r 0 μ₂ :=
    SchurStoredState.of_core hG ⟨thr, ht⟩ hp hfr₁₂ (by fp_sub [schurRoundFp])
      ⟨⟨_, hfr₂.keep (Store.readsOnly_get _ _ _) hFS.symm hF₁⟩,
        ⟨H, hA.of_eqOff hfr₁₂ (Fp.disj_sup_left.mpr ⟨hFA, hSA⟩)⟩, [(0, n + 1)], 0, hSt₂,
        by simp [RangesFit], by simp,
        ⟨⟨U, hU.of_eqOff hfr₁₂ (Fp.disj_sup_left.mpr ⟨hFU, hSU⟩)⟩, fun _ =>
          ⟨U, 1, hU.of_eqOff hfr₁₂ (Fp.disj_sup_left.mpr ⟨hFU, hSU⟩), hasOrthonormalCols_one,
            by simp⟩⟩⟩
  refine (writes_whileFuel (N := 2 * (n + 1)) rfl
    (fun _ => schurRoundFp (n + 1) a uo f st wk ub r) (fun _ _ => le_rfl)
    (schurRoundFp (n + 1) a uo f st wk ub r)
    (fun i => SchurStoredState n P U u εL m ps a t p uo f st wk ub r i) _ hS0 ?_
    (fun _ _ hS' => roundedWorklistExit_terminates hL hNat hC hu0 hεL le_rfl hS')).mono
      (by simp) fun _ _ h => h
  intro i hi μ' _ hS'
  obtain ⟨rs, ℓ, hSt, -⟩ := hS'.2.2.2.2.2
  rw [Interp.testAt_eq rfl rfl, hC.test_isPos hSt.1]
  refine Mode.holds_some ?_
  by_cases hpos : 0 < rs.length
  · rw [if_pos (by simpa [schurBlock] using hpos)]
    exact (roundedWorklistRound_terminates hS hP hL hNat hQ hC hm1 hm2 hεL D hD L hLeaf hS'
      hSt.1 hpos).in_frame rfl rfl (hS'.1.live_of_subset (by simp))
  · rw [if_neg (by simpa [schurBlock] using hpos)]
    exact roundedWorklistExit_terminates hL hNat hC hu0 hεL (by omega) hS'

/-- The rounded worklist in Schur mode runs to completion, with the accumulator bound if `P`: the
common form of `NLAlib.ShiftedQR.solveRoundedWith_completes` (no rounding model, `P` false) and
`NLAlib.ShiftedQR.solveRoundedWith_terminates` (`P` the standard model at
$\boldsymbol{u} \le 1/100$ and $\varepsilon_L \ge 0$). -/
theorem solveRoundedWith_terminates_if {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) {P : Prop} (hP : P → StdModel u id Mch ∧ u ≤ 1 / 100)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {k F T ns w : ℕ} {ps : List ℝ} {εL : ℝ} (hεL : P → 0 ≤ εL) (D : Stmt O Q)
    (hD : TerminatingDecouplerRoutine n k F T ps ns w D I) (L : Stmt O Q)
    (hLeaf : TerminatingLeafRoutineIf P εL (min k (n + 1)) ps T L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {a t p uo f : ℕ × ℕ}
    {H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr : ℝ}
    (hl : μ.Live [a, t, p, uo, f])
    (hr : μ.Room [a, t, p, uo, f]
      [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * ((n + 1) * (n + 1)), 1])
    (ha : Fp.Apart [a, t, p, uo, f]
      [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * ((n + 1) * (n + 1)), 1])
    (hA : HoldsMatrix a H μ.store) (hU : HoldsMatrix uo U μ.store)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps) :
    Writes .total I tape (solveRoundedWith D L)
      (Env.frame [n + 1, k, ps.length, F, T, ns, w] [a, t, p, uo, a, uo, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (∃ Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, HoldsMatrix a Tm μ'.store) ∧
        AccumIf P U ((1 + 24 * u) ^ (2 * (n + 1) * (ns * w + 2 * k * (k + 2))) * (1 + εL) ^ (n + 1))
          uo μ') μ := by
  unfold solveRoundedWith
  change Writes .total I tape (Stmt.allocs [IExp.const 1 + IExp.const 2 * IExp.var 0,
    IExp.const 2 * (IExp.var 0 * IExp.var 0), IExp.const 2 * (IExp.var 0 * IExp.var 0),
    IExp.const 5] _) _ _ _ μ
  refine writes_allocs_preserving_post
    (ns := [1 + 2 * (n + 1), 2 * ((n + 1) * (n + 1)), 2 * ((n + 1) * (n + 1)), 5])
    (by simp [IExp.evalList, IExp.eval, Env.frame])
    (fun hBelow ⟨⟨Tm, hTm⟩, hacc⟩ => ⟨⟨Tm, hTm.of_below hBelow (hl a (by simp))⟩,
      hacc.of_below hBelow (hl uo (by simp))⟩) ?_
  intro s hs hlens hBelow
  set Lc := μ.store.length
  have hG := Geometry.allocated ⟨hl, hr, ha⟩ hs hlens hBelow
  have hG' : SchurGeometry (n + 1) ps.length a t p uo f (Lc, 0) (Lc + 1, 0) (Lc + 2, 0)
      (Lc + 3, 0) ⟨s, μ.pos⟩ := by
    simpa [List.range_succ] using hG
  have hw := roundedWorklist_terminates (F := F) (T := T) (tape := tape) hS hP hL hNat hQ hC
    le_self_add le_add_self hεL D hD L hLeaf hG' (hA.of_below hBelow (hl a (by simp)))
    (hU.of_below hBelow (hl uo (by simp))) (((hBelow t.1 (hl t (by simp))).2 _).trans ht)
    ((hBelow.readBlock (hl p (by simp)) p.2 ps.length).trans hp)
  refine (hw.in_frame (by simp [IExp.evalList, IExp.eval, Env.frame])
    (by simp [Operand.evalList, Operand.eval, IExp.eval, Env.frame])
    (hG'.live_of_subset (by simp))).mono ?_ fun _ _ h => h
  intro b i h
  simp only [schurRoundFp, Fp.blocks_cons, Fp.blocks_nil, fpNF] at h ⊢
  omega

/-- **The rounded worklist in Schur mode runs to completion on any machine**: on a scalar machine
with natural literals up to $n + 1$ exact, exact `toNat` and comparisons (no rounding model), let
the decoupling routine terminate with a closed log (`NLAlib.ShiftedQR.TerminatingDecouplerRoutine`)
and the leaf routine complete on orders at most $\min(k, n + 1)$
(`NLAlib.ShiftedQR.CompletingLeafRoutine`, no accumulator bound). Then for any matrix and
accumulator, any threshold word and on every tape, `solveRoundedWith D L` runs to completion, writes
only the matrix, the accumulator and the failure word, and leaves a matrix and an accumulator
stored. The accumulator
bound under the standard model is `NLAlib.ShiftedQR.solveRoundedWith_terminates`. -/
theorem solveRoundedWith_completes {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1))
    (hQ : IsToNat id I) (hC : IsCmp id I) {k F T ns w : ℕ} {ps : List ℝ} (D : Stmt O Q)
    (hD : TerminatingDecouplerRoutine n k F T ps ns w D I) (L : Stmt O Q)
    (hLeaf : CompletingLeafRoutine (min k (n + 1)) ps T L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {a t p uo f : ℕ × ℕ}
    {H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr : ℝ}
    (hl : μ.Live [a, t, p, uo, f])
    (hr : μ.Room [a, t, p, uo, f]
      [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * ((n + 1) * (n + 1)), 1])
    (ha : Fp.Apart [a, t, p, uo, f]
      [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * ((n + 1) * (n + 1)), 1])
    (hA : HoldsMatrix a H μ.store) (hU : HoldsMatrix uo U μ.store)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps) :
    Writes .total I tape (solveRoundedWith D L)
      (Env.frame [n + 1, k, ps.length, F, T, ns, w] [a, t, p, uo, a, uo, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => ∃ Tm U' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsMatrix a Tm μ'.store ∧ HoldsMatrix uo U' μ'.store) μ :=
  (solveRoundedWith_terminates_if (u := 0) hS (P := False) False.elim hL hNat hQ hC
    False.elim D hD L (hLeaf.terminatingLeafRoutineIf 0) hl hr ha hA hU ht hp).mono le_rfl
    fun _ _ h => by
      obtain ⟨⟨Tm, hTm⟩, ⟨U', hU'⟩, -⟩ := h
      exact ⟨Tm, U', hTm, hU'⟩

/-- **The rounded worklist in Schur mode terminates, and its accumulator stays near a unitary on
every tape**: on a scalar machine with the standard model, natural literals up to $n + 1$ exact,
exact `toNat` and comparisons, let the decoupling routine terminate with a closed log
(`NLAlib.ShiftedQR.TerminatingDecouplerRoutine`) and the leaf routine terminate with an
accumulator within $\varepsilon_L$ of a unitary on orders at most $\min(k, n + 1)$
(`NLAlib.ShiftedQR.TerminatingLeafRoutine`). Then for any matrix $\mathbf{H}$ and accumulator
$\mathbf{U}$, any threshold word and on every tape, `solveRoundedWith D L` runs to completion,
writes only the matrix, the accumulator and the failure word, and the stored accumulator is
within $((1 + 24\boldsymbol{u})^{2(n+1)(n_s w + 2k(k+2))}(1 + \varepsilon_L)^{n+1} - 1)
\|\mathbf{U}\|_2$ of $\mathbf{U}\mathbf{V}$ for an exact unitary $\mathbf{V}$, whatever the
shifts (each replayed rotation and each leaf product is a near-unitary update). -/
theorem solveRoundedWith_terminates {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu1 : u ≤ 1 / 100) (hL : IsIndexLit Mch I)
    (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I) (hC : IsCmp id I)
    {k F T ns w : ℕ} {ps : List ℝ} {εL : ℝ} (hεL : 0 ≤ εL) (D : Stmt O Q)
    (hD : TerminatingDecouplerRoutine n k F T ps ns w D I) (L : Stmt O Q)
    (hLeaf : TerminatingLeafRoutine εL (min k (n + 1)) ps T L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {a t p uo f : ℕ × ℕ}
    {H U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr : ℝ}
    (hl : μ.Live [a, t, p, uo, f])
    (hr : μ.Room [a, t, p, uo, f]
      [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * ((n + 1) * (n + 1)), 1])
    (ha : Fp.Apart [a, t, p, uo, f]
      [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * ((n + 1) * (n + 1)), 1])
    (hA : HoldsMatrix a H μ.store) (hU : HoldsMatrix uo U μ.store)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps) :
    Writes .total I tape (solveRoundedWith D L)
      (Env.frame [n + 1, k, ps.length, F, T, ns, w] [a, t, p, uo, a, uo, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock uo.1 uo.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => ∃ U' Tm V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        HoldsMatrix a Tm μ'.store ∧ HoldsMatrix uo U' μ'.store ∧ HasOrthonormalCols V ∧
        specNorm (U' - U * V) ≤
          ((1 + 24 * u) ^ (2 * (n + 1) * (ns * w + 2 * k * (k + 2))) * (1 + εL) ^ (n + 1) - 1) *
            specNorm U) μ :=
  (solveRoundedWith_terminates_if hS (P := True) (fun _ => ⟨hM, hu1⟩) hL hNat hQ hC
    (fun _ => hεL) D hD L (hLeaf.terminatingLeafRoutineIf True) hl hr ha hA hU ht hp).mono le_rfl
    fun _ _ h => by
      obtain ⟨⟨Tm, hTm⟩, -, hacc⟩ := h
      obtain ⟨U', V, hU', hV, hb⟩ := hacc trivial
      exact ⟨U', Tm, V, hTm, hU', hV, hb⟩

end Theorems

end NLAlib.ShiftedQR
