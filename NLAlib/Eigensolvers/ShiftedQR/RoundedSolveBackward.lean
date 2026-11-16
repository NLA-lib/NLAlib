/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.RoundedSolve

/-!
# Backward error of the rounded deflation worklist

The program `NLAlib.ShiftedQR.solveRounded` of `NLAlib.Eigensolvers.ShiftedQR.RoundedSolve`, a
worklist of active ranges with a decoupling implementation for large blocks and a leaf routine for
small ones, is total and capped, and on its success word stores the spectrum of a matrix within
the composed backward error of the input. The rounds are composed by
`NLAlib.Ops.BackwardStep.whileFuel` with the perturbed unitary similarity as backward-error
relation: a round is exact (a failure), a leaf ($\beta$), or a decoupling call and a cut
($\varepsilon(N_0) + c$) [BanksGarzaVargasSrivastava2022, §6].

## Main results

* `NLAlib.ShiftedQR.bottomScan_writes`: the rounded bottom-$k$ scan (the decision of `Deflate`).
* `NLAlib.ShiftedQR.roundedWorklistRound_backwardStep`: one round is a backward step.
* `NLAlib.ShiftedQR.solveRounded_backward`: the backward error of the rounded worklist.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type}

section Theorems

variable [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q]

/-- The registers of `bottomScan` after its first `j` visits: either the flag is $1$ and the
index is a bottom-$k$ position whose entry passed the rounded test, or the flag is $0$, the index
word is stored, and every visited entry failed it. -/
def BottomScanHolds {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (u thr : ℝ) (k j : ℕ)
    (r : ℕ × ℕ) (st : Store ℝ) : Prop :=
  (st.get r.1 (r.2 + 3) = some 1 ∧ ∃ i : Fin n, n ≤ (i : ℕ) + k ∧
      st.get r.1 (r.2 + 4) = some (i : ℝ) ∧ (1 - u) ^ 2 * ‖H i.succ i.castSucc‖ ^ 2 ≤ thr) ∨
    (st.get r.1 (r.2 + 3) = some 0 ∧ (∃ x, st.get r.1 (r.2 + 4) = some x) ∧
      ∀ i : Fin n, n ≤ (i : ℕ) + k → (i : ℕ) < n - k + j →
        thr < (1 + u) ^ 2 * ‖H i.succ i.castSucc‖ ^ 2)

/-- One visit of `bottomScan` advances `NLAlib.ShiftedQR.BottomScanHolds`. -/
private theorem bottomScanHolds_step {M : Machine ℝ} {u : ℝ} (hM : StdModel u id M) (hu : 0 ≤ u)
    (hu1 : u ≤ 1) {n k j : ℕ} (hk : k ≤ n) (hj : j < k)
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr flag index : ℝ} {r : ℕ × ℕ}
    {st st' : Store ℝ} (h : BottomScanHolds H u thr k j r st)
    (hflag : st.get r.1 (r.2 + 3) = some flag) (hindex : st.get r.1 (r.2 + 4) = some index)
    (hF : st'.get r.1 (r.2 + 3) =
      some (if subdiagonalSqWord M H (n - k + j) ≤ thr then 1 else flag))
    (hI : st'.get r.1 (r.2 + 4) =
      some (if subdiagonalSqWord M H (n - k + j) ≤ thr then ((n - k + j : ℕ) : ℝ) else index)) :
    BottomScanHolds H u thr k (j + 1) r st' := by
  let i₀ : Fin n := ⟨n - k + j, by omega⟩
  have hb := subdiagonalSqWord_bounds hM hu hu1 H i₀
  by_cases hs : subdiagonalSqWord M H (n - k + j) ≤ thr
  · rw [if_pos hs] at hF hI
    exact Or.inl ⟨hF, i₀, by simp only [i₀]; omega, hI, hb.1.trans hs⟩
  · rw [if_neg hs] at hF hI
    rcases h with ⟨h1, i, hik, hi, hthr⟩ | ⟨h0, -, hall⟩
    · rw [h1, Option.some.injEq] at hflag
      rw [hi, Option.some.injEq] at hindex
      exact Or.inl ⟨hflag ▸ hF, i, hik, hindex ▸ hI, hthr⟩
    · rw [h0, Option.some.injEq] at hflag
      refine Or.inr ⟨hflag ▸ hF, ⟨_, hI⟩, fun i hik hlt => ?_⟩
      by_cases he : (i : ℕ) = n - k + j
      · have hii : i = i₀ := Fin.ext he
        subst hii
        exact (lt_of_not_ge hs).trans_le hb.2
      · exact hall i hik (by omega)

omit [Has IdxTst Q] in
/-- **The rounded bottom-$k$ scan** (the decision of `Deflate`,
[BanksGarzaVargasSrivastava2022, §6], corrected: it scans the bottom $k$ subdiagonal entries,
where `Deflate` takes the bottom $k - 1$): on a machine with the standard model at
$0 \le \boldsymbol{u} \le 1$ whose natural literals up to $n + 1$ are exact (the flag and the index
are such literals), for an $(n+1) \times (n+1)$ matrix $\mathbf{H}$, $k \le n$ and the threshold
word $t$, `bottomScan` writes only its five registers and either sets the flag to $1$ and the
index to some $i$ among the bottom $k$ subdiagonal positions ($n \le i + k$) with
$(1 - \boldsymbol{u})^2\lvert h_{i+1,i} \rvert^2 \le t$, or sets the flag to $0$, and then every
bottom $k$ subdiagonal entry has $t < (1 + \boldsymbol{u})^2\lvert h_{i+1,i} \rvert^2$. -/
theorem bottomScan_writes {M : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar M I) (hM : StdModel u id M) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hL : IsIndexLit M I) (hNat : IsExactNatLit id M (n + 1)) (hC : IsCmp id I)
    {τ : Tape ℝ} {m : Mem ℝ} {k : ℕ} (hk : k ≤ n)
    {a t r : ℕ × ℕ} {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr : ℝ}
    (hH : HoldsMatrix a H m.store) (ht : m.store.get t.1 t.2 = some thr)
    (hl : m.Live [a, t, r]) (hroom : r.2 + 5 ≤ m.store.len r.1)
    (hA : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hT : Fp.Disj (Store.inBlock r.1 r.2 5) (Store.inBlock t.1 t.2 1)) :
    Writes .total I τ (bottomScan (O := O) (Q := Q)).body (Env.frame [n + 1, k] [a, t, r])
      (Store.inBlock r.1 r.2 5)
      (fun m' => m'.pos = m.pos ∧
        ((m'.store.get r.1 (r.2 + 3) = some 1 ∧ ∃ i : Fin n, n ≤ (i : ℕ) + k ∧
            m'.store.get r.1 (r.2 + 4) = some (i : ℝ) ∧
            (1 - u) ^ 2 * ‖H i.succ i.castSucc‖ ^ 2 ≤ thr) ∨
          (m'.store.get r.1 (r.2 + 3) = some 0 ∧ ∀ i : Fin n, n ≤ (i : ℕ) + k →
            thr < (1 + u) ^ 2 * ‖H i.succ i.castSucc‖ ^ 2))) m := by
  have hzero : M.lit ((0 : ℕ) : ℚ) = (0 : ℝ) := by simpa using hNat 0 (Nat.zero_le _)
  unfold bottomScan
  refine (writes_indexLit hL rfl rfl (by dsimp only; omega)).seq_le (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hFlag⟩
  refine (writes_indexLit hL rfl rfl (by dsimp only; rw [hfr₁.len_eq]; omega)).seq_le
    (by fp_sub) ?_
  intro m₂ hfr₂ ⟨hp₂, hIndex⟩
  have hFlag₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hFlag
  simp only [hzero] at hFlag₂ hIndex
  have hfr := (hfr₁.trans' hfr₂).mono (by fp_sub : _ ≤ Store.inBlock r.1 r.2 5)
  have hH₂ := hH.of_eqOff hfr hA
  have ht₂ := hfr.keep (Store.readsOnly_get _ _ _) hT ht
  have hl₂ := hl.congr hfr.length_eq
  have hroom₂ : r.2 + 5 ≤ m₂.store.len r.1 := by rw [hfr.len_eq]; exact hroom
  refine (writes_loop rfl (fun _ => Store.inBlock r.1 r.2 5) (fun _ _ => le_rfl)
    (fun j m' => m'.pos = m₂.pos ∧ BottomScanHolds H u thr k j r m'.store)
    ⟨rfl, Or.inr ⟨hFlag₂, ⟨0, hIndex⟩, fun i hik hlt => by omega⟩⟩ ?_).mono le_rfl ?_
  · intro j hj m' hfr' ⟨hp', hs⟩
    obtain ⟨flag, hflag⟩ : ∃ x, m'.store.get r.1 (r.2 + 3) = some x := by
      rcases hs with ⟨h1, -⟩ | ⟨h0, -⟩
      exacts [⟨_, h1⟩, ⟨_, h0⟩]
    obtain ⟨index, hindex⟩ : ∃ x, m'.store.get r.1 (r.2 + 4) = some x := by
      rcases hs with ⟨-, i, -, hi, -⟩ | ⟨-, hx, -⟩
      exacts [⟨_, hi⟩, hx]
    have hw := scanRound_writes_word (τ := τ) (k := n + 1 - 1 - k + j) hS hL hC
      (hNat.mono n.le_succ)
      (by omega) (hH₂.of_eqOff hfr' hA) (hfr'.keep (Store.readsOnly_get _ _ _) hT ht₂) hflag
      hindex (hl₂.congr hfr'.length_eq) (by rw [hfr'.len_eq]; exact hroom₂) hA hT
    refine (hw.in_frame rfl rfl (hl₂.congr hfr'.length_eq)).mono le_rfl ?_
    intro m'' _ ⟨hp'', hF, hI⟩
    have he : n + 1 - 1 - k + j = n - k + j := by omega
    rw [he] at hF hI
    exact ⟨hp''.trans hp', bottomScanHolds_step hM hu hu1 hk hj hs hflag hindex hF hI⟩
  · intro m' _ ⟨hp', hs⟩
    refine ⟨hp'.trans (hp₂.trans hp₁), ?_⟩
    rcases hs with h1 | ⟨h0, -, hall⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h0, fun i hik => hall i hik (by omega)⟩

omit [Has ScalarOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The abort writes the failure word $1$ and the stack count $0$, on any machine whose literals
$0$ and $1$ are exact. -/
theorem roundedAbort_writes {M : Machine ℝ} {I : Interp O Q ℝ} (hL : IsIndexLit M I) {B : ℕ}
    (hN : IsExactNatLit id M B) (hB : 1 ≤ B) {τ : Tape ℝ} {m : Mem ℝ} {st f : ℕ × ℕ}
    (hst : st.2 < m.store.len st.1) (hf : f.2 < m.store.len f.1)
    (hd : Fp.Disj (Store.inBlock f.1 f.2 1) (Store.inBlock st.1 st.2 1)) :
    Writes .total I τ (roundedAbort (O := O) (Q := Q)).body (Env.frame [] [st, f])
      (Store.inBlock f.1 f.2 1 ⊔ Store.inBlock st.1 st.2 1)
      (fun m' => m'.store.get f.1 f.2 = some 1 ∧ m'.store.get st.1 st.2 = some 0) m := by
  have h1 : M.lit ((1 : ℕ) : ℚ) = 1 := by simpa using hN 1 hB
  have h0 : M.lit ((0 : ℕ) : ℚ) = 0 := by simpa using hN 0 (Nat.zero_le _)
  unfold roundedAbort
  refine (writes_indexLit hL rfl rfl (by omega)).seq_le le_sup_left ?_
  rintro m₁ hfr₁ ⟨-, hOne⟩
  refine (writes_indexLit hL rfl rfl (by rw [hfr₁.len_eq]; omega)).mono
    le_sup_right ?_
  rintro m₂ hfr₂ ⟨-, hZero⟩
  have hOne₂ := hfr₂.keep (Store.readsOnly_get _ _ _) hd.symm hOne
  exact ⟨by simpa only [h1] using hOne₂, by simpa only [h0] using hZero⟩

omit [Has CmpTst Q] in
/-- Commit and split, memory effect: `writeAndSplit` copies the work block $\mathbf{B}$ into
the diagonal block of the range $(lo, d)$ of the stored matrix and pushes the right child, then
the left child, on any scalar machine whose natural literals up to $n + 1$ are exact. -/
theorem writeAndSplit_writes_mem {M : Machine ℝ} {I : Interp O Q ℝ} (hS : IsScalar M I)
    (hL : IsIndexLit M I) (hQ : IsToNat id I) {n : ℕ} (hN : IsExactNatLit id M (n + 1))
    {τ : Tape ℝ} {m : Mem ℝ} {lo d i : ℕ} {a st w : ℕ × ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {B : Matrix (Fin d) (Fin d) ℂ}
    {rs : List (ℕ × ℕ)} (hl : m.Live [a, st, w]) (hA : HoldsMatrix a A m.store)
    (hW : HoldsMatrix w B m.store) (hSt : StackHolds st rs m.store) (hr : lo + d ≤ n + 1)
    (hi : i < d) (hcap : rs.length + 2 ≤ n + 1)
    (hroomA : a.2 + 2 * ((n + 1) * (n + 1)) ≤ m.store.len a.1)
    (hroomS : st.2 + (1 + 2 * (n + 1)) ≤ m.store.len st.1)
    (hWA : Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))))
    (hAS : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))) :
    Writes .total I τ (writeAndSplit (O := O) (Q := Q)).body
      (Env.frame [n + 1, lo, d, i] [a, st, w])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
      (fun m' => m'.pos = m.pos ∧ HoldsMatrix a (setSubBlock A (lo, d) B) m'.store ∧
        StackHolds st (rs ++ [(lo + i + 1, d - i - 1), (lo, i + 1)]) m'.store) m := by
  have hlWA : m.Live [w, a] := by
    simpa [Mem.Live] using And.intro (hl w (by simp)) (hl a (by simp))
  unfold writeAndSplit
  refine (copyToGlobal_writes (τ := τ) hS hlWA hA hW hr hroomA hWA).frame_seq_le rfl rfl hlWA
    ((blockFp_le a hr).trans le_sup_left) ?_
  intro m₁ hfr₁ ⟨hp₁, hA₁⟩
  have hSt₁ := hSt.of_eqOff hfr₁ (hAS.mono (blockFp_le a hr) (by fp_sub))
  have hlS : m₁.Live [st] := by
    simpa [Mem.Live, ← hfr₁.length_eq] using hl st (by simp)
  have hw := splitPush_writes_of_isExactNatLit (τ := τ) (lo := lo) (d := d) (i := i) hL hQ hN
    (by omega) (by omega) le_rfl hlS hSt₁ hcap
    (by rw [hfr₁.len_eq]; simpa only [Nat.add_assoc] using hroomS)
  refine (hw.in_frame rfl rfl hlS).mono le_sup_right ?_
  intro m₂ hfr₂ ⟨hp₂, hSt₂⟩
  exact ⟨hp₂.trans hp₁, hA₁.of_eqOff hfr₂ hAS.symm, hSt₂⟩

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The leaf of a round, mathematics: from a popped state, a run that writes only the output
words of the popped range $(lo, d)$ and stores there a listing of the eigenvalues of the popped
block plus $\mathbf{F}$, $\|\mathbf{F}\|_2 \le \beta \le e$, ends in the core state of the next
round, reached by a perturbed unitary similarity with error $e$. -/
theorem roundedLeaf_core {fails : Prop} {n j : ℕ} {a t p st out w r f : ℕ × ℕ}
    {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ} {e thr β : ℝ}
    {ps : List ℝ} {lo d : ℕ} {rest done : List (ℕ × ℕ)} {μ μ' : Mem ℝ}
    (hP : RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ)
    (hβe : β ≤ e) (hfr : μ.store.EqOff (Store.inBlock out.1 (out.2 + 2 * lo) (2 * d)) μ'.store)
    (hpost : ∃ (rts : Fin d → ℂ) (F : Matrix (Fin d) (Fin d) ℂ), specNorm F ≤ β ∧
      IsEigenvalueListing (subBlock A (lo, d) + F) rts ∧
      HoldsMatrix (out.1, out.2 + 2 * lo) (Matrix.of fun i (_ : Fin 1) => rts i) μ'.store) :
    ∃ M', IsPerturbedUnitarySimilar M M' e ∧ RoundedCore fails H₀ e a st out f (j + 1) M' μ' := by
  obtain ⟨hG, -, -, hf, hnorm, hInv, hA, hOut, hSt, hj⟩ := hP
  obtain ⟨rts, F, hF, hList, hO⟩ := hpost
  have hr := hInv.active_block (r := (lo, d)) List.mem_cons_self
  have houtFp : Store.inBlock out.1 (out.2 + 2 * lo) (2 * d) ≤
      Store.inBlock out.1 out.2 (2 * (n + 1)) := by have := hr.2.1; fp_sub
  have hOA : Fp.Disj (Store.inBlock out.1 out.2 (2 * (n + 1)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := by simpa using hG.disj 4 0 (by simp)
  have hOS : Fp.Disj (Store.inBlock out.1 out.2 (2 * (n + 1)))
      (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) := by simpa using hG.disj 4 3 (by simp)
  have hOF : Fp.Disj (Store.inBlock out.1 out.2 (2 * (n + 1))) (Store.inBlock f.1 f.2 1) := by
    simpa using hG.disj 4 7 (by simp)
  obtain ⟨M', hMM', hInv'⟩ := hInv.exists_isPerturbedUnitarySimilar_finish hF hList
  have hrest : rest.length ≤ n + 1 := by
    have hb := hInv.length_le
    simp only [List.length_append, List.length_cons] at hb
    omega
  have hNew : HoldsMatrix (out.1, out.2 + 2 * lo)
      (Matrix.of fun i (_ : Fin 1) => subVec (setSubVec roots (lo, d) rts) (lo, d) i)
      μ'.store := by
    simpa only [subVec_setSubVec_self roots (lo, d) rts hr.2.1] using hO
  have hOut' := hOut.cons hfr (fun q hq => (hInv.disjoint_of_mem List.mem_cons_self hq).1)
    (fun q hq => subVec_setSubVec_of_disjoint roots (lo, d) q rts
      (hInv.disjoint_of_mem List.mem_cons_self hq).2
      (hInv.disjoint_of_mem List.mem_cons_self hq).1) hNew
  refine ⟨M', hMM'.mono hβe, Or.inr ⟨hfr.keep (Store.readsOnly_get _ _ _)
    (hOF.mono houtFp le_rfl) hf, ?_, rest, (lo, d) :: done, A, _, hInv',
    hA.of_eqOff hfr (hOA.mono houtFp le_rfl), hOut',
    hSt.of_eqOff hfr (hOS.mono houtFp (by simp only [List.length_reverse]; fp_sub)), ?_⟩⟩
  · have hle := hMM'.specNorm_le
    push_cast
    linarith
  · simp only [List.length_cons]
    omega

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The operands of the leaf call of a round: the work matrix and the output words of the popped
range are live, have room and are apart. -/
theorem RoundedPopped.leaf_operands {n j : ℕ} {a t p st out w r f : ℕ × ℕ}
    {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ} {e thr : ℝ}
    {ps : List ℝ} {lo d : ℕ} {rest done : List (ℕ × ℕ)} {μ : Mem ℝ}
    (hP : RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ) :
    μ.Live [w, (out.1, out.2 + 2 * lo)] ∧
      (out.1, out.2 + 2 * lo).2 + 2 * d ≤ μ.store.len (out.1, out.2 + 2 * lo).1 ∧
      Fp.Disj (Store.inBlock w.1 w.2 (2 * (d * d)))
        (Store.inBlock out.1 (out.2 + 2 * lo) (2 * d)) := by
  have hG := hP.1
  have hr := hP.2.2.2.2.2.1.active_block (r := (lo, d)) List.mem_cons_self
  have hd : d ≤ n + 1 := by have := hr.2.1; omega
  have hsq := Nat.mul_le_mul hd hd
  have hroomO : out.2 + 2 * (n + 1) ≤ μ.store.len out.1 := hG.room.2.2.2.2.1
  have houtFp : Store.inBlock out.1 (out.2 + 2 * lo) (2 * d) ≤
      Store.inBlock out.1 out.2 (2 * (n + 1)) := by have := hr.2.1; fp_sub
  have hfull : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock out.1 out.2 (2 * (n + 1))) := by simpa using hG.disj 5 4 (by simp)
  exact ⟨by simpa [Mem.Live] using And.intro (hG.live w (by simp)) (hG.live out (by simp)),
    by dsimp only; have := hr.2.1; omega, hfull.mono (by fp_sub) houtFp⟩

omit [Has ScalarOp O] [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The leaf branch of a round: the leaf routine on the copied block of the popped range
finishes it, a perturbed unitary similarity with error $\beta \le e$. -/
theorem roundedLeaf_writes {I : Interp O Q ℝ} {β : ℝ} (L : Impl O Q)
    (hLeaf : BackwardLeafContract β L I) {tape : Tape ℝ} {μ : Mem ℝ} {fails : Prop} {n j : ℕ}
    {a t p st out w r f : ℕ × ℕ} {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {roots : Fin (n + 1) → ℂ} {e thr : ℝ} {ps : List ℝ} {lo d : ℕ} {rest done : List (ℕ × ℕ)}
    (hP : RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ)
    (hW : HoldsMatrix w (subBlock A (lo, d)) μ.store) (hβe : β ≤ e) :
    Writes .total I tape L.body (Env.frame [d] [w, (out.1, out.2 + 2 * lo)])
      (Store.inBlock out.1 (out.2 + 2 * lo) (2 * d))
      (fun μ' => ∃ M', IsPerturbedUnitarySimilar M M' e ∧
        RoundedCore fails H₀ e a st out f (j + 1) M' μ') μ := by
  obtain ⟨hlWO, hroom, hWO⟩ := hP.leaf_operands
  have hr := hP.2.2.2.2.2.1.active_block (r := (lo, d)) List.mem_cons_self
  exact (hLeaf (subBlock A (lo, d)) hr.2.2 hW hlWO hroom hWO).mono le_rfl
    fun μ' hfr hpost => roundedLeaf_core hP hβe hfr hpost

/-- The cut of a round, mathematics: after a successful decoupling call with output
$\mathbf{H}'$ (error $\varepsilon(N_0)$) and a scan that passed at $i$ with
$(1-\boldsymbol{u})^2\lvert h'_{i+1,i} \rvert^2 \le t \le (1-\boldsymbol{u})^2c^2$, the stored split
is the core state of the next round, reached with error $e \ge \varepsilon(N_0) + c$. -/
theorem roundedCut_core {fails : Prop} {n j lo d : ℕ} {a st out f : ℕ × ℕ}
    {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ}
    {rest done : List (ℕ × ℕ)} {u thr c e ε : ℝ} {μ' : Mem ℝ}
    {H' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} (hu1 : u < 1) (hc : 0 ≤ c)
    (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (he : c + ε ≤ e)
    (hnorm : specNorm M ≤ specNorm H₀ + j * e)
    (hInv : DeflationInv M 0 ((lo, d + 1) :: rest) done A roots)
    (hH' : IsPerturbedUnitarySimilar (subBlock A (lo, d + 1)) H' ε)
    (hHess : IsUpperHessenberg H') (i : Fin d)
    (hthr : (1 - u) ^ 2 * ‖H' i.succ i.castSucc‖ ^ 2 ≤ thr)
    (hf : μ'.store.get f.1 f.2 = some 0)
    (hA : HoldsMatrix a (setSubBlock A (lo, d + 1) H') μ'.store)
    (hOut : FinishedHolds out done roots μ'.store)
    (hSt : StackHolds st (rest.reverse ++ [(lo + i + 1, d + 1 - i - 1), (lo, i + 1)]) μ'.store)
    (hj : 2 * done.length + rest.length = j) :
    ∃ M', IsPerturbedUnitarySimilar M M' e ∧ RoundedCore fails H₀ e a st out f (j + 1) M' μ' := by
  have hcut' : ‖H' i.succ i.castSucc‖ ≤ c := by
    have hpos : 0 < (1 - u) ^ 2 := by have : 0 < 1 - u := by linarith
                                      positivity
    have hsq : ‖H' i.succ i.castSucc‖ ^ 2 ≤ c ^ 2 := le_of_mul_le_mul_left (hthr.trans hcut) hpos
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc two_ne_zero).mp hsq
  obtain ⟨M', hMM', hInv'⟩ := hInv.exists_isPerturbedUnitarySimilar_split hH' hHess i hcut'
  refine ⟨M', hMM'.mono (by linarith), Or.inr ⟨hf, ?_, _, done, _, roots, hInv', hA, hOut,
    by simpa [List.reverse_cons, List.append_assoc] using hSt, ?_⟩⟩
  · have hle := hMM'.specNorm_le
    push_cast
    linarith
  · simp only [List.length_cons]
    omega

/-- The large branch of a round after the decoupling call: from the memory after a
decoupling call on the copied block of the popped range $(lo, d + 1)$, $d \ge k$, that wrote only
the work matrix and the flag and either failed (flag $1$, allowed when `fails` holds) or returned
an upper Hessenberg perturbed unitary similarity $\mathbf{H}'$ of the block with error
$\varepsilon(N_0)$ and a bottom-$k$ subdiagonal entry of modulus at most $\omega$ (flag $0$), the
rest of the branch aborts, or scans, cuts and pushes both children (the scan always passes); the
core state of the next round is reached with error $e \ge \varepsilon(N_0) + c$, $e \ge 0$. -/
theorem roundedLargeRest_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {fails : Prop} {k F : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    {tape : Tape ℝ} {μ μ₁ : Mem ℝ} {j lo d : ℕ} {a t p st out w r f : ℕ × ℕ}
    {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ}
    {rest done : List (ℕ × ℕ)} {thr c e N₀ : ℝ}
    (hP : RoundedPopped H₀ e thr ps a t p st out w r f j M lo (d + 1) rest done A roots μ)
    (hk : k ≤ d) (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2)
    (hc : 0 ≤ c) (he : c + ε N₀ ≤ e) (he0 : 0 ≤ e)
    (hfr₁ : μ.store.EqOff (Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ⊔
      Store.inBlock f.1 f.2 1) μ₁.store)
    (hD₁ : (fails ∧ μ₁.store.get f.1 f.2 = some 1) ∨
      (μ₁.store.get f.1 f.2 = some 0 ∧
        ∃ H' : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ,
          IsPerturbedUnitarySimilar (subBlock A (lo, d + 1)) H' (ε N₀) ∧
          IsUpperHessenberg H' ∧ (∃ i : Fin d, d ≤ (i : ℕ) + k ∧ ‖H' i.succ i.castSucc‖ ≤ ω) ∧
          HoldsMatrix w H' μ₁.store)) :
    Writes .total I tape (roundedLargeRest D)
      (Env.frame [n + 1, k, ps.length, F, lo, d + 1] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (fun μ' => ∃ M', IsPerturbedUnitarySimilar M M' e ∧
        RoundedCore fails H₀ e a st out f (j + 1) M' μ') μ₁ := by
  obtain ⟨hG, ht, hp, hf, hnorm, hInv, hA, hOut, hSt, hj'⟩ := id hP
  have hr := hInv.active_block (r := (lo, d + 1)) List.mem_cons_self
  have hd : d + 1 ≤ n + 1 := by have := hr.2.1; omega
  have hsq := Nat.mul_le_mul hd hd
  have hrest : rest.length + 1 ≤ n + 1 := by
    have hb := hInv.length_le
    simp only [List.length_append, List.length_cons] at hb
    omega
  have hWw : Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ≤
      Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  have hdone : finishedFp out done ≤ Store.inBlock out.1 out.2 (2 * (n + 1)) :=
    finishedFp_le (fun q hq => (hInv.partition.2.1 q (List.mem_append_right _ hq)).2)
  obtain ⟨hWA, hWT, hWP, hWS, hWO, hWF, hRA, hRT, hRS, hRO,
    hRF, hRW, hFA, hFS, hFO, hFT, hAS, hAO, hSO, hPF⟩ := hG.disj_round
  have hDfp : Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1 ≤
      Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) ⊔ Store.inBlock f.1 f.2 1 :=
    sup_le_sup_right hWw _
  have hG₁ := hG.of_eqOff hfr₁
  have hA₁ := hA.of_eqOff hfr₁ ((Fp.disj_sup_left.mpr ⟨hWA, hFA⟩).mono hDfp le_rfl)
  have hSt₁ := hSt.of_eqOff hfr₁ ((Fp.disj_sup_left.mpr ⟨hWS, hFS⟩).mono hDfp
    (by simp only [List.length_reverse]; fp_sub))
  have hOut₁ := hOut.of_eqOff hfr₁ ((Fp.disj_sup_left.mpr ⟨hWO, hFO⟩).mono hDfp hdone)
  have ht₁ := hfr₁.keep (Store.readsOnly_get _ _ _)
    ((Fp.disj_sup_left.mpr ⟨hWT, hFT⟩).mono hDfp le_rfl) ht
  have hlSF : μ₁.Live [st, f] := hG₁.live_of_subset (by simp)
  have habort := roundedAbort_writes (O := O) (Q := Q) (τ := tape) (m := μ₁) hL hNat
    (by omega) (st := st) (f := f) (by have := hG₁.room.2.2.2.1; omega)
    (by have := hG₁.room.2.2.2.2.2.2.2.1; omega) (hFS.mono le_rfl (by fp_sub))
  rcases hD₁ with ⟨hfails, hF1⟩ | ⟨hF0, H', hH', hHess', ⟨i₀, hi₀k, hi₀⟩, hW₁⟩
  · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := f) hF1) ?_
    have h1 : decide (0 < id (1 : ℝ)) = true := by simp
    rw [h1, if_pos rfl]
    refine (habort.in_frame rfl rfl hlSF).mono (by fp_sub [roundedWorklistFp]) ?_
    rintro μ₂ - ⟨hF, hS0⟩
    exact ⟨M, (IsPerturbedUnitarySimilar.refl M).mono he0, Or.inl ⟨hfails, hF, hS0⟩⟩
  · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := f) hF0) ?_
    have h0 : decide (0 < id (0 : ℝ)) = false := by simp
    rw [h0, if_neg (by simp)]
    have hlS : μ₁.Live [w, t, r] := hG₁.live_of_subset (by simp)
    have hb := bottomScan_writes (τ := tape) (n := d) (k := k) hS hM hu hu1.le hL
      (hNat.mono (by omega)) hC hk hW₁ ht₁ hlS hG₁.room.2.2.2.2.2.2.1 (hRW.mono le_rfl hWw) hRT
    refine (hb.in_frame rfl rfl hlS).seq_le (by fp_sub [roundedWorklistFp]) ?_
    rintro μ₂ hfr₂ ⟨-, hscan⟩
    have hG₂ := hG₁.of_eqOff hfr₂
    rcases hscan with ⟨hR1, i, -, hRi, hthr⟩ | ⟨-, hall⟩
    · refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := (r.1, r.2 + 3)) hR1) ?_
      have h1 : decide (0 < id (1 : ℝ)) = true := by simp
      rw [h1, if_pos rfl]
      refine writes_bindIdx_of_decode_nat hQ rfl rfl hRi rfl (by have := i.isLt; omega) ?_
      obtain ⟨_, -, hInvc⟩ := hInv.exists_isPerturbedUnitarySimilar_split hH' hHess' i le_rfl
      have hcap := hInvc.length_le
      simp only [List.length_append, List.length_cons] at hcap
      have hlASW : μ₂.Live [a, st, w] := hG₂.live_of_subset (by simp)
      have hsplit := writeAndSplit_writes_mem (O := O) (Q := Q) (τ := tape) (i := (i : ℕ)) hS hL
        hQ hNat hlASW (hA₁.of_eqOff hfr₂ hRA) (hW₁.of_eqOff hfr₂ (hRW.mono le_rfl hWw))
        (hSt₁.of_eqOff hfr₂ (hRS.mono le_rfl (by simp only [List.length_reverse]; fp_sub)))
        hr.2.1 (by have := i.isLt; omega) (by simp only [List.length_reverse]; omega)
        hG₂.room.1 hG₂.room.2.2.2.1 (hWA.mono hWw le_rfl) hAS
      refine (hsplit.in_frame rfl rfl hlASW).mono (by fp_sub [roundedWorklistFp]) ?_
      rintro μ₃ hfr₃ ⟨-, hA₃, hSt₃⟩
      have hfr₂₃ := hfr₂.trans' hfr₃
      exact roundedCut_core hu1 hc hcut he hnorm hInv hH' hHess' i hthr
        (hfr₂₃.keep (Store.readsOnly_get _ _ _)
          (Fp.disj_sup_left.mpr ⟨hRF, Fp.disj_sup_left.mpr ⟨hFA.symm, hFS.symm⟩⟩) hF0)
        hA₃ (hOut₁.of_eqOff hfr₂₃
          ((Fp.disj_sup_left.mpr ⟨hRO, Fp.disj_sup_left.mpr ⟨hAO, hSO⟩⟩).mono le_rfl hdone))
        hSt₃ hj'
    · exfalso
      have h1 := hall i₀ hi₀k
      have h2 : ‖H' i₀.succ i₀.castSucc‖ ^ 2 ≤ ω ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hi₀ 2
      nlinarith [sq_nonneg (1 + u)]

/-- The operands of the decoupling call of a round on the popped range $(lo, d + 1)$, and the
popped block's norm bound: the work matrix, the parameter words and the flag are live, have room
and are apart, and the block has norm at most $N_0$ when
$\|\mathbf{H}_0\|_2 + 2(n+1)e \le N_0$, $e \ge 0$ and $j < 2(n+1)$. -/
theorem RoundedPopped.decouple_operands {n j lo d : ℕ} {a t p st out w r f : ℕ × ℕ}
    {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ} {e thr N₀ : ℝ}
    {ps : List ℝ} {rest done : List (ℕ × ℕ)} {μ : Mem ℝ}
    (hP : RoundedPopped H₀ e thr ps a t p st out w r f j M lo (d + 1) rest done A roots μ)
    (he0 : 0 ≤ e) (hN₀ : specNorm H₀ + 2 * (n + 1) * e ≤ N₀) (hj : j < 2 * (n + 1)) :
    IsUpperHessenberg (subBlock A (lo, d + 1)) ∧ specNorm (subBlock A (lo, d + 1)) ≤ N₀ ∧
      μ.store.readBlock p.1 p.2 ps.length = some ps ∧ μ.Live [w, p, w, f] ∧
      w.2 + 2 * ((d + 1) * (d + 1)) ≤ μ.store.len w.1 ∧ f.2 + 1 ≤ μ.store.len f.1 ∧
      Fp.Disj (Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1)))) (Store.inBlock f.1 f.2 1) ∧
      Fp.Disj (Store.inBlock p.1 p.2 ps.length)
        (Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ⊔ Store.inBlock f.1 f.2 1) := by
  have hG := hP.1
  have hr := hP.2.2.2.2.2.1.active_block (r := (lo, d + 1)) List.mem_cons_self
  have hd : d + 1 ≤ n + 1 := by have := hr.2.1; omega
  have hsq := Nat.mul_le_mul hd hd
  have hWw : Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))) ≤
      Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))) := by fp_sub
  obtain ⟨-, -, hWP, -, -, hWF, -, -, -, -, -, -, -, -, -, -, -, -, -, hPF⟩ := hG.disj_round
  exact ⟨hr.2.2, hP.specNorm_subBlock_le he0 hN₀ hj, hP.2.2.1, hG.live_of_subset (by simp),
    by have := hG.room.2.2.2.2.2.1; omega, hG.room.2.2.2.2.2.2.2.1, hWF.mono hWw le_rfl,
    Fp.disj_sup_right.mpr ⟨hWP.symm.mono le_rfl hWw, hPF⟩⟩

/-- The large branch of a round: the decoupler on the copied block of the popped range
$(lo, d + 1)$, $d \ge k$, either fails (failure word $1$, stack count $0$) or is followed by the
bottom scan, which then always passes, and the cut and the push of both children; the core state
of the next round is reached with error $e \ge \varepsilon(N_0) + c$. -/
theorem roundedLarge_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {fails : Prop} {k F : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    (hD : RoundedDecouplingContract fails k F ps ω ε D I)
    {tape : Tape ℝ} {μ : Mem ℝ} {j lo d : ℕ} {a t p st out w r f : ℕ × ℕ}
    {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ}
    {rest done : List (ℕ × ℕ)} {thr c e N₀ : ℝ}
    (hP : RoundedPopped H₀ e thr ps a t p st out w r f j M lo (d + 1) rest done A roots μ)
    (hW : HoldsMatrix w (subBlock A (lo, d + 1)) μ.store) (hk : k ≤ d)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (he : c + ε N₀ ≤ e) (he0 : 0 ≤ e) (hN₀ : specNorm H₀ + 2 * (n + 1) * e ≤ N₀)
    (hj : j < 2 * (n + 1)) :
    Writes .total I tape (roundedProcessLarge D).body
      (Env.frame [n + 1, k, ps.length, F, lo, d + 1] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (fun μ' => ∃ M', IsPerturbedUnitarySimilar M M' e ∧
        RoundedCore fails H₀ e a st out f (j + 1) M' μ') μ := by
  obtain ⟨hHess, hnorm, hp, hlD, hroomW, hroomF, hWF, hPWF⟩ := hP.decouple_operands he0 hN₀ hj
  have hw := hD (tape := tape) (N := N₀) (subBlock A (lo, d + 1)) hk hHess hnorm hW hp hlD
    hroomW hroomF hWF hPWF
  have hr := hP.2.2.2.2.2.1.active_block (r := (lo, d + 1)) List.mem_cons_self
  have hd : d + 1 ≤ n + 1 := by have := hr.2.1; omega
  have hsq := Nat.mul_le_mul hd hd
  unfold roundedProcessLarge
  refine hw.frame_seq_le rfl rfl hlD (by fp_sub [roundedWorklistFp]) ?_
  intro μ₁ hfr₁ hD₁
  exact roundedLargeRest_writes hS hM hu hu1 hL hNat hQ hC D hP hk hfind hcut hc he he0 hfr₁ hD₁

omit [Has IndexOp O] [Has CmpTst Q] [Has IdxTst Q] in
/-- The copy of a round: from a popped state, `copyToWork` copies the popped block into the
work matrix, and the popped state survives. -/
theorem RoundedPopped.writes_copyToWork {Mch : Machine ℝ} {I : Interp O Q ℝ}
    {tape : Tape ℝ} {μ : Mem ℝ} {n j lo d : ℕ} {a t p st out w r f : ℕ × ℕ}
    {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ} {e thr : ℝ}
    {ps : List ℝ} {rest done : List (ℕ × ℕ)}
    (hP : RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ)
    (hS : IsScalar Mch I) :
    Writes .total I tape (copyToWork (Op := O) (Tst := Q)).body (Env.frame [n + 1, lo, d] [a, w])
      (Store.inBlock w.1 w.2 (2 * (d * d)))
      (fun μ₁ => RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ₁ ∧
        HoldsMatrix w (subBlock A (lo, d)) μ₁.store) μ := by
  have hG := hP.1
  have hr := hP.2.2.2.2.2.1.active_block (r := (lo, d)) List.mem_cons_self
  have hd : d ≤ n + 1 := by have := hr.2.1; omega
  have hsq := Nat.mul_le_mul hd hd
  have hAW : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock w.1 w.2 (2 * (d * d))) :=
    (by simpa using hG.disj 0 5 (by simp) : Fp.Disj (Store.inBlock a.1 a.2
      (2 * ((n + 1) * (n + 1)))) (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))).mono
      le_rfl (by fp_sub)
  refine (copyToWork_writes (τ := tape) (lo := lo) (d := d) hS (hG.live_of_subset (by simp))
    hP.2.2.2.2.2.2.1 hr.2.1 (by have := hG.room.2.2.2.2.2.1; omega) hAW).mono le_rfl ?_
  rintro μ₁ hfr₁ ⟨-, hW₁⟩
  exact ⟨hP.of_eqOff_work hfr₁ (by fp_sub), hW₁⟩

/-- Processing a popped range: the copy of its block, then the leaf routine (order at most
$k$) or the large branch; the core state of the next round is reached with error $e$. -/
theorem roundedRange_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) {n : ℕ} (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {fails : Prop} {k F : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    (hD : RoundedDecouplingContract fails k F ps ω ε D I)
    {β : ℝ} (L : Impl O Q) (hLeaf : BackwardLeafContract β L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {j lo d : ℕ} {a t p st out w r f : ℕ × ℕ}
    {H₀ M A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {roots : Fin (n + 1) → ℂ}
    {rest done : List (ℕ × ℕ)} {thr c e N₀ : ℝ}
    (hP : RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀) (he : c + ε N₀ + β ≤ e)
    (hN₀ : specNorm H₀ + 2 * (n + 1) * e ≤ N₀) (hj : j < 2 * (n + 1)) :
    Writes .total I tape (roundedProcessRange D L).body
      (Env.frame [n + 1, k, ps.length, F, lo, d] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (fun μ' => ∃ M', IsPerturbedUnitarySimilar M M' e ∧
        RoundedCore fails H₀ e a st out f (j + 1) M' μ') μ := by
  have hr := hP.2.2.2.2.2.1.active_block (r := (lo, d)) List.mem_cons_self
  have hlAW : μ.Live [a, w] := hP.1.live_of_subset (by simp)
  unfold roundedProcessRange
  have hd : d ≤ n + 1 := by have := hr.2.1; omega
  have hsq := Nat.mul_le_mul hd hd
  refine (hP.writes_copyToWork (tape := tape) hS).frame_seq_le rfl rfl hlAW
    (by fp_sub [roundedWorklistFp]) ?_
  rintro μ₁ - ⟨hP₁, hW₁⟩
  have hG₁ := hP₁.1
  by_cases hs : d ≤ k
  · refine (writes_ifPos (P := fun μ₂ => ∃ M', IsPerturbedUnitarySimilar M M' e ∧
      RoundedCore fails H₀ e a st out f (j + 1) M' μ₂) (n := k + 1 - d) rfl ?_).seq_le le_rfl ?_
    · rw [if_pos (by omega)]
      have hl : μ₁.Live [w, (out.1, out.2 + 2 * lo)] := by
        simpa [Mem.Live] using And.intro (hG₁.live w (by simp)) (hG₁.live out (by simp))
      exact ((roundedLeaf_writes L hLeaf hP₁ hW₁ (by linarith)).in_frame rfl rfl hl).mono
        (by have := hr.2.1; fp_sub [roundedWorklistFp]) (fun _ _ hp => hp)
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
    exact (roundedLarge_writes hS hM hu hu1 hL hNat hQ hC D hD hP₁ hW₁ (by omega) hfind hcut hc
      (by linarith) (by linarith) hN₀ hj).in_frame rfl rfl hG₁.live

omit [Has CmpTst Q] in
/-- The pop of a round: from a state of the worklist with a positive stack count,
`rangePop` pops the top range $(lo, d)$ into the scan registers and reaches a popped state. -/
theorem RoundedWorklistState.writes_rangePop {Mch : Machine ℝ} {I : Interp O Q ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hL : IsIndexLit Mch I) (hQ : IsToNat id I)
    (hNat : IsExactNatLit id Mch (n + 1)) {fails : Prop} {tape : Tape ℝ} {μ : Mem ℝ} {j : ℕ}
    {a t p st out w r f : ℕ × ℕ} {H₀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {e thr : ℝ}
    {ps : List ℝ} {count : ℕ}
    (h : RoundedWorklistState fails H₀ e thr ps a t p st out w r f j M μ)
    (hcount : μ.store.get st.1 st.2 = some (count : ℝ)) (hpos : 0 < count) :
    Writes .total I tape (rangePop (Op := O) (Tst := Q)).body (Env.frame [n + 1] [st, r])
      (Store.inBlock st.1 st.2 1 ⊔ Store.inBlock r.1 r.2 2)
      (fun μ₁ => ∃ (lo d : ℕ) (rest done : List (ℕ × ℕ))
        (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (roots : Fin (n + 1) → ℂ),
        RoundedPopped H₀ e thr ps a t p st out w r f j M lo d rest done A roots μ₁ ∧
          μ₁.store.get r.1 r.2 = some (lo : ℝ) ∧ μ₁.store.get r.1 (r.2 + 1) = some (d : ℝ)) μ := by
  obtain ⟨hG, ht, hp, hcore⟩ := h
  rcases hcore with ⟨-, -, hS0⟩ | ⟨hf, hnorm, active, done, A, roots, hInv, hA, hOut, hSt, hj'⟩
  · have h0 : (count : ℝ) = 0 := Option.some.inj (hcount.symm.trans hS0)
    exact absurd (by exact_mod_cast h0 : count = 0) (by omega)
  cases active with
  | nil =>
    have hc0 : (count : ℝ) = 0 := Option.some.inj (hcount.symm.trans (by simpa using hSt.1))
    exact absurd (by exact_mod_cast hc0 : count = 0) (by omega)
  | cons range rest =>
    rcases range with ⟨lo, d⟩
    have hrest : rest.length + 1 ≤ n + 1 := by
      have hb := hInv.length_le
      simp only [List.length_append, List.length_cons] at hb
      omega
    have htop : StackHolds st (rest.reverse ++ [(lo, d)]) μ.store := by
      simpa only [List.reverse_cons] using hSt
    have hRS : Fp.Disj (Store.inBlock r.1 r.2 2) (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) :=
      (by simpa using hG.disj 6 3 (by simp) : Fp.Disj (Store.inBlock r.1 r.2 5)
        (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))).mono (by fp_sub) le_rfl
    have hlSR : μ.Live [st, r] := hG.live_of_subset (by simp)
    refine (rangePop_writes_of_isExactNatLit (τ := tape) hS hL hQ hNat htop
      (by simpa using hrest) (by simpa only [Nat.add_assoc] using hG.room.2.2.2.1)
      (by have := hG.room.2.2.2.2.2.2.1; omega) hlSR hRS).mono le_rfl ?_
    rintro μ₁ hfr₁ ⟨-, hSt₁, hRange⟩
    have hpop : Store.inBlock st.1 st.2 1 ⊔ Store.inBlock r.1 r.2 2 ≤
        roundedWorklistFp (n + 1) a st out w r f := by fp_sub [roundedWorklistFp]
    have hpar := hG.disj_params.mono hpop le_rfl
    have hfin : finishedFp out done ≤ Store.inBlock out.1 out.2 (2 * (n + 1)) :=
      finishedFp_le (fun q hq => (hInv.partition.2.1 q (List.mem_append_right _ hq)).2)
    have hpd {X : Fp} (h1 : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) X)
        (h2 : Fp.Disj (Store.inBlock r.1 r.2 5) X) :
        Fp.Disj (Store.inBlock st.1 st.2 1 ⊔ Store.inBlock r.1 r.2 2) X :=
      Fp.disj_sup_left.mpr ⟨h1.mono (by fp_sub) le_rfl, h2.mono (by fp_sub) le_rfl⟩
    refine ⟨lo, d, rest, done, A, roots, ⟨hG.of_eqOff hfr₁,
      hfr₁.keep (Store.readsOnly_get _ _ _) (hpar.mono le_rfl le_sup_left) ht,
      hfr₁.keep (Store.readsOnly_readBlock _ _ _ _) (hpar.mono le_rfl le_sup_right) hp,
      hfr₁.keep (Store.readsOnly_get _ _ _) (hpd (by simpa using hG.disj 3 7 (by simp))
        (by simpa using hG.disj 6 7 (by simp))) hf,
      hnorm, hInv, hA.of_eqOff hfr₁ (hpd (by simpa using hG.disj 3 0 (by simp))
        (by simpa using hG.disj 6 0 (by simp))),
      hOut.of_eqOff hfr₁ ((hpd (by simpa using hG.disj 3 4 (by simp))
        (by simpa using hG.disj 6 4 (by simp))).mono le_rfl hfin), hSt₁,
      by simp only [List.length_cons] at hj'; omega⟩, ?_, ?_⟩
    · simpa [vec] using Store.get_of_readBlock hRange (j := 0) (by omega) (0 : ℝ)
    · simpa [vec] using Store.get_of_readBlock hRange (j := 1) (by omega) (0 : ℝ)

/-- **One round of the rounded worklist is a backward step** (the per-round half of
[BanksGarzaVargasSrivastava2022, Theorem 6.3], backward error): on a machine with the standard model
at $0 \le \boldsymbol{u} < 1$ whose natural literals up to $n + 1$ are exact (the stack, the flags
and the indices are such literals), with a decoupler meeting `RoundedDecouplingContract` with the
bottom width $k$, the parameter words `ps`, the threshold $\omega$ and the error $\varepsilon$, and
a leaf routine with backward error $\beta \ge 0$, suppose the threshold word $t$ has $(1 +
\boldsymbol{u})^2\omega^2 \le t \le (1 - \boldsymbol{u})^2 c^2$ with $c \ge 0$, $\varepsilon(N_0)
\ge 0$, $c + \varepsilon(N_0) + \beta \le e$ and $\|\mathbf{H}_0\|_2 + 2(n+1)e \le N_0$. Then for $j
< 2(n+1)$ the round is a backward step, for the perturbed unitary similarity of the current matrix
with error $e$, from the state before round $j$ with a positive stack count to the state before
round $j + 1$. -/
theorem roundedWorklistRound_backwardStep {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {fails : Prop} {k F : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    (hD : RoundedDecouplingContract fails k F ps ω ε D I)
    {β : ℝ} (L : Impl O Q) (hLeaf : BackwardLeafContract β L I)
    {tape : Tape ℝ} {j : ℕ} {a t p st out w r f : ℕ × ℕ}
    {H₀ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr c e N₀ : ℝ}
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀) (he : c + ε N₀ + β ≤ e)
    (hN₀ : specNorm H₀ + 2 * (n + 1) * e ≤ N₀) (hj : j < 2 * (n + 1)) :
    BackwardStep .total I tape (roundedWorklistRound D L).body
      (Env.frame [n + 1, k, ps.length, F] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (fun ε A B => IsPerturbedUnitarySimilar A B ε)
      (fun M μ => RoundedWorklistState fails H₀ e thr ps a t p st out w r f j M μ ∧
        ∃ count : ℕ, μ.store.get st.1 st.2 = some (count : ℝ) ∧ 0 < count)
      (RoundedWorklistState fails H₀ e thr ps a t p st out w r f (j + 1)) e := by
  rintro M μ ⟨hst, count, hcount, hpos⟩
  obtain ⟨hG, ht, hp, -⟩ := id hst
  refine Writes.mono (P := fun μ' => ∃ M', IsPerturbedUnitarySimilar M M' e ∧
    RoundedCore fails H₀ e a st out f (j + 1) M' μ') ?_ le_rfl
    (fun μ' hfr ⟨M', hMM', hcore'⟩ =>
      ⟨M', hMM', RoundedWorklistState.of_core hG ht hp hfr le_rfl hcore'⟩)
  have hlSR : μ.Live [st, r] := hG.live_of_subset (by simp)
  unfold roundedWorklistRound
  refine (hst.writes_rangePop hS hL hQ hNat hcount hpos).frame_seq_le rfl rfl hlSR
    (by fp_sub [roundedWorklistFp]) ?_
  rintro μ₁ - ⟨lo, d, rest, done, A, roots, hP₁, hLo, hSize⟩
  have hbounds := hP₁.2.2.2.2.2.1.active_block (r := (lo, d)) List.mem_cons_self
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hLo rfl (by have := hbounds.2.1; omega) ?_
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hSize rfl (by have := hbounds.2.1; omega) ?_
  exact (roundedRange_writes hS hM hu hu1 hL hNat hQ hC D hD L hLeaf hP₁ hfind hcut hc hβ hε0
    he hN₀ hj).in_frame rfl rfl hP₁.1.live

/-- The capped loop of the rounded worklist, from the initialized state: the rounds compose
by `NLAlib.Ops.BackwardStep.whileFuel` (each by
`NLAlib.ShiftedQR.roundedWorklistRound_backwardStep`), and both exits find an empty stack and skip;
the final state is reached from $\mathbf{H}$ with error $2(n+1)e$. -/
theorem roundedWorklist_writes {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {fails : Prop} {k F : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    (hD : RoundedDecouplingContract fails k F ps ω ε D I)
    {β : ℝ} (L : Impl O Q) (hLeaf : BackwardLeafContract β L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {a t p st out w r f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr c N₀ : ℝ}
    (hG : RoundedGeometry (n + 1) ps.length a t p st out w r f μ)
    (hHess : IsUpperHessenberg H) (hA : HoldsMatrix a H μ.store)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀)
    (hN₀ : specNorm H + 2 * (n + 1) * (c + ε N₀ + β) ≤ N₀) :
    Writes .total I tape (roundedWorklist D L).body
      (Env.frame [n + 1, k, ps.length, F] [a, t, p, st, out, w, r, f])
      (roundedWorklistFp (n + 1) a st out w r f)
      (fun μ' => ∃ M', IsPerturbedUnitarySimilar H M' (2 * (n + 1) * (c + ε N₀ + β)) ∧
        RoundedFinal fails out f M' μ') μ := by
  have he0 : 0 ≤ c + ε N₀ + β := by linarith
  obtain ⟨hFA, hFS⟩ : Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) ∧ Fp.Disj (Store.inBlock f.1 f.2 1)
      (Store.inBlock st.1 st.2 (1 + 2 * (n + 1))) :=
    ⟨by simpa using hG.disj 7 0 (by simp), by simpa using hG.disj 7 3 (by simp)⟩
  have hSA : Fp.Disj (Store.inBlock st.1 st.2 (1 + 2 * (n + 1)))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := by simpa using hG.disj 3 0 (by simp)
  have hpar := hG.disj_params
  unfold roundedWorklist
  refine (writes_indexLit hL rfl rfl (by have := hG.room.2.2.2.2.2.2.2.1; dsimp only; omega)).seq_le
    (by fp_sub [roundedWorklistFp]) ?_
  rintro μ₁ hfr₁ ⟨-, hF₁⟩
  have hlS : μ₁.Live [st] := (hG.of_eqOff hfr₁).live_of_subset (by simp)
  have hw := stackInit_writes_of_isExactNatLit (Op := O) (Tst := Q) (τ := tape) hL hQ hNat
    (lo := 0) (size := n + 1) (by omega) le_rfl le_rfl (Nat.succ_pos n)
    (by simpa only [Nat.add_assoc] using (hG.of_eqOff hfr₁).room.2.2.2.1)
  refine hw.frame_seq_le rfl rfl hlS (by fp_sub [roundedWorklistFp]) ?_
  rintro μ₂ hfr₂ ⟨-, hSt₂⟩
  have hfr₁₂ := hfr₁.trans' hfr₂
  have h01 : Store.inBlock f.1 f.2 1 ⊔ Store.inBlock st.1 st.2 (1 + 2 * (n + 1)) ≤
      roundedWorklistFp (n + 1) a st out w r f := by fp_sub [roundedWorklistFp]
  have hS0 : RoundedWorklistState fails H (c + ε N₀ + β) thr ps a t p st out w r f 0 H μ₂ := by
    refine RoundedWorklistState.of_core hG ht hp hfr₁₂ h01 (Or.inr ⟨?_, by simp, [(0, n + 1)],
      [], H, fun _ => 0, hHess.deflationInv_init _,
      hA.of_eqOff hfr₁₂ (Fp.disj_sup_left.mpr ⟨hFA, hSA⟩),
      fun _ hq => by simp at hq, by simpa using hSt₂, by simp⟩)
    have h0 : Mch.lit ((0 : ℕ) : ℚ) = 0 := by simpa using hNat 0 (Nat.zero_le _)
    have := hfr₂.keep (Store.readsOnly_get _ _ _) hFS.symm hF₁
    simpa only [h0] using this
  have hR := isBackwardErrorRel_isPerturbedUnitarySimilar (𝕜 := ℂ) (n := Fin (n + 1))
  have hexit : ∀ i, ∀ M μ', RoundedWorklistState fails H (c + ε N₀ + β) thr ps a t p st out w r f
      i M μ' → μ'.store.get st.1 st.2 = some 0 →
      Writes .total I tape (Stmt.ite (Has.inj CmpTst.isPos) [] [{ buf := 3, off := IExp.var 7 }]
        (Stmt.frame [] [{ buf := 3, off := IExp.var 7 }, { buf := 7, off := IExp.var 11 }]
          (roundedAbort (O := O) (Q := Q)).body) Stmt.skip)
        ((Env.frame [n + 1, k, ps.length, F] [a, t, p, st, out, w, r, f]).pushIdx i) ⊥
        (fun μ'' => ∃ M', IsPerturbedUnitarySimilar M M' 0 ∧ RoundedFinal fails out f M' μ'')
        μ' := by
    intro i M μ' hS' h0
    obtain ⟨cnt, hcnt, hfin, -⟩ := hS'.count
    have hc0 : cnt = 0 := by exact_mod_cast Option.some.inj (hcnt.symm.trans h0)
    refine writes_ite rfl rfl (hC.test_isPos (d := []) (x := st) h0) ?_
    rw [show decide (0 < id (0 : ℝ)) = false by simp, if_neg (by simp)]
    exact Writes.skip ⟨M, IsPerturbedUnitarySimilar.refl M, hfin hc0⟩
  refine ((BackwardStep.whileFuel (F := roundedWorklistFp (n + 1) a st out w r f) (G := ⊥)
    (S' := fun M μ => RoundedFinal fails out f M μ) (ε' := 0) hR rfl
    (fun i M μ => RoundedWorklistState fails H (c + ε N₀ + β) thr ps a t p st out w r f i M μ)
    (fun _ b _ μ => ∃ cnt : ℕ, μ.store.get st.1 st.2 = some (cnt : ℝ) ∧
      b = decide (0 < (cnt : ℝ)))
    (fun _ => c + ε N₀ + β) (fun _ _ => he0) ?_ ?_ ?_ ?_) H μ₂ hS0).mono
    (by simp) ?_
  · intro i _ M μ' hS'
    obtain ⟨cnt, hcnt, -, -⟩ := hS'.count
    rw [Interp.testAt_eq rfl rfl, hC.test_isPos hcnt]
    exact Mode.holds_some ⟨cnt, hcnt, rfl⟩
  · intro i hi
    refine BackwardStep.in_frame (fun M μ' ⟨hS', cnt, hcnt, hb⟩ =>
      roundedWorklistRound_backwardStep hS hM hu hu1 hL hNat hQ hC D hD L hLeaf hfind hcut hc
        hβ hε0 le_rfl hN₀ hi M μ' ⟨hS', cnt, hcnt, ?_⟩) rfl rfl
      (fun _ _ hx => hx.1.1.live)
    have : (0 : ℝ) < cnt := by simpa using hb.symm
    exact_mod_cast this
  · intro i _ M μ' ⟨hS', cnt, hcnt, hb⟩
    have hc0 : cnt = 0 := by
      by_contra hne
      have : (0 : ℝ) < cnt := by exact_mod_cast Nat.pos_of_ne_zero hne
      simp [this] at hb
    subst hc0
    exact hexit i M μ' hS' (by simpa using hcnt)
  · intro M μ' hS'
    obtain ⟨cnt, hcnt, -, hlt⟩ := hS'.count
    have hc0 : cnt = 0 := by by_contra hne; have := hlt (Nat.pos_of_ne_zero hne); omega
    subst hc0
    exact hexit _ M μ' hS' (by simpa using hcnt)
  · rintro μ' - ⟨M', hHM, hfin⟩
    refine ⟨M', hHM.mono (le_of_eq ?_), hfin⟩
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_zero]
    push_cast
    ring

/-- **Backward error of the rounded deflation worklist** ([BanksGarzaVargasSrivastava2022,
Theorem 6.3], backward half, with `Deflate` scanning the bottom $k$ subdiagonal entries): on a
machine with the standard model
at $0 \le \boldsymbol{u} < 1$ whose natural literals up to $n + 1$ are exact (the stack, the flags
and the indices are such literals), let the decoupler `D` meet `RoundedDecouplingContract` with the
failure alternative `fails`, the bottom width $k$, the parameter words `ps`, the threshold
$\omega$ and the error $\varepsilon$, and let the leaf routine `L` have backward error
$\beta \ge 0$. Let $\mathbf{H}$ be upper Hessenberg of order $n + 1$, stored at `a`, the threshold
word $t$ satisfy $(1 + \boldsymbol{u})^2\omega^2 \le t \le (1 - \boldsymbol{u})^2c^2$ with
$c \ge 0$, and $\varepsilon(N_0) \ge 0$ with
$\|\mathbf{H}\|_2 + 2(n+1)(c + \varepsilon(N_0) + \beta) \le N_0$. Then `solveRounded D L` runs
to completion, writes only the matrix, the output and the failure word, and either fails (word
$1$, only when `fails` holds) or sets the failure word to $0$ and stores all eigenvalues, with
multiplicity, of $\mathbf{H} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le 2(n+1)(c + \varepsilon(N_0) + \beta)$. With `fails` false the run never
fails. The views are live, have room and are pairwise apart. -/
theorem solveRounded_backward {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {fails : Prop} {k F : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ} (D : Impl O Q)
    (hD : RoundedDecouplingContract fails k F ps ω ε D I)
    {β : ℝ} (L : Impl O Q) (hLeaf : BackwardLeafContract β L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {a t p out f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr c N₀ : ℝ}
    (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * (n + 1), 1])
    (ha : Fp.Apart [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * (n + 1), 1])
    (hHess : IsUpperHessenberg H) (hA : HoldsMatrix a H μ.store)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀)
    (hN₀ : specNorm H + 2 * (n + 1) * (c + ε N₀ + β) ≤ N₀) :
    Writes .total I tape (solveRounded D L).body
      (Env.frame [n + 1, k, ps.length, F] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (fails ∧ μ'.store.get f.1 f.2 = some 1) ∨
        (μ'.store.get f.1 f.2 = some 0 ∧
          ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
            HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
            specNorm E ≤ 2 * (n + 1) * (c + ε N₀ + β) ∧
            (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ))) μ := by
  unfold solveRounded
  refine writes_allocs_preserving_post
    (lens := [.const 1 + .const 2 * .var 0, .const 2 * (.var 0 * .var 0), .const 5])
    (ns := [1 + 2 * (n + 1), 2 * ((n + 1) * (n + 1)), 5]) rfl ?_ ?_
  · intro s s' pos hBelow h
    rcases h with ⟨hfa, hf⟩ | ⟨hf, roots, E, hOut, hE, hR⟩
    · exact Or.inl ⟨hfa, hBelow.get_of (hl f (by simp)) hf⟩
    · exact Or.inr ⟨hBelow.get_of (hl f (by simp)) hf, roots, E,
        hOut.of_below hBelow (hl out (by simp)), hE, hR⟩
  · intro s hs hlens hBelow
    have hG := roundedGeometry_allocated (np := ps.length) hl hr ha hs hlens hBelow
    have hA' := hA.of_below hBelow (hl a (by simp))
    have ht' := hBelow.get_of (hl t (by simp)) ht
    have hp' := (hBelow.readBlock (hl p (by simp)) p.2 ps.length).trans hp
    have hw := roundedWorklist_writes hS hM hu hu1 hL hNat hQ hC D hD L hLeaf (tape := tape) hG
      hHess hA' ht' hp' hfind hcut hc hβ hε0 hN₀
    refine (hw.in_frame rfl rfl hG.live).mono (by fp_sub [roundedWorklistFp]) ?_
    rintro μ' - ⟨M', hHM, hfin⟩
    rcases hfin with h1 | ⟨hf, done, A, roots, hInv, hOut⟩
    · exact Or.inl h1
    · obtain ⟨E, hE, hR⟩ := (hInv.of_isPerturbedUnitarySimilar hHM).exists_roots_eq
      exact Or.inr ⟨hf, roots, E, hOut, by simpa using hE, hR⟩

/-- **The rounded worklist with routines, backward error** ([BanksGarzaVargasSrivastava2025,
Theorem 6.1]; [BanksGarzaVargasSrivastava2022, Theorem 6.3], backward half):
`NLAlib.ShiftedQR.solveRounded_backward` for `NLAlib.ShiftedQR.solveRoundedWith`, with a decoupling
routine meeting `NLAlib.ShiftedQR.RoundedDecouplingRoutineContract` and a leaf routine with
backward error $\beta \ge 0$ on the blocks of order at most $\min(k, n + 1)$ and norm at most $N_0$
(`NLAlib.ShiftedQR.BackwardLeafRoutineContract`). On a machine with the standard model at
$0 \le \boldsymbol{u} < 1$ and exact natural literals up to $n + 1$, for $\mathbf{H}$ upper
Hessenberg of order $n + 1$, a threshold $t$ with
$(1 + \boldsymbol{u})^2\omega^2 \le t \le (1 - \boldsymbol{u})^2c^2$, $c \ge 0$,
$\varepsilon(N_0) \ge 0$ and $\|\mathbf{H}\|_2 + 2(n + 1)(c + \varepsilon(N_0) + \beta) \le N_0$,
the run is total, writes only the matrix, the output and the failure word, and either fails
(only when `fails` holds) or stores all eigenvalues of $\mathbf{H} + \mathbf{E}$ for some
$\|\mathbf{E}\|_2 \le 2(n + 1)(c + \varepsilon(N_0) + \beta)$ with the failure word $0$. -/
theorem solveRoundedWith_backward {Mch : Machine ℝ} {I : Interp O Q ℝ} {u : ℝ} {n : ℕ}
    (hS : IsScalar Mch I) (hM : StdModel u id Mch) (hu : 0 ≤ u) (hu1 : u < 1)
    (hL : IsIndexLit Mch I) (hNat : IsExactNatLit id Mch (n + 1)) (hQ : IsToNat id I)
    (hC : IsCmp id I) {fails : Prop} {k F T : ℕ} {ps : List ℝ} {ω : ℝ} {ε : ℝ → ℝ}
    (D : Impl O Q) (hD : RoundedDecouplingRoutineContract fails k F T ps ω ε D I)
    {β N₀ : ℝ} (L : Impl O Q) (hLeaf : BackwardLeafRoutineContract β (min k (n + 1)) N₀ ps T L I)
    {tape : Tape ℝ} {μ : Mem ℝ} {a t p out f : ℕ × ℕ}
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {thr c : ℝ}
    (hl : μ.Live [a, t, p, out, f])
    (hr : μ.Room [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * (n + 1), 1])
    (ha : Fp.Apart [a, t, p, out, f] [2 * ((n + 1) * (n + 1)), 1, ps.length, 2 * (n + 1), 1])
    (hHess : IsUpperHessenberg H) (hA : HoldsMatrix a H μ.store)
    (ht : μ.store.get t.1 t.2 = some thr) (hp : μ.store.readBlock p.1 p.2 ps.length = some ps)
    (hfind : (1 + u) ^ 2 * ω ^ 2 ≤ thr) (hcut : thr ≤ (1 - u) ^ 2 * c ^ 2) (hc : 0 ≤ c)
    (hβ : 0 ≤ β) (hε0 : 0 ≤ ε N₀)
    (hN₀ : specNorm H + 2 * (n + 1) * (c + ε N₀ + β) ≤ N₀) :
    Writes .total I tape (solveRoundedWith D L).body
      (Env.frame [n + 1, k, ps.length, F, T] [a, t, p, out, f])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock out.1 out.2 (2 * (n + 1)) ⊔ Store.inBlock f.1 f.2 1)
      (fun μ' => (fails ∧ μ'.store.get f.1 f.2 = some 1) ∨
        (μ'.store.get f.1 f.2 = some 0 ∧
          ∃ (roots : Fin (n + 1) → ℂ) (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
            HoldsMatrix out (Matrix.of fun i (_ : Fin 1) => roots i) μ'.store ∧
            specNorm E ≤ 2 * (n + 1) * (c + ε N₀ + β) ∧
            (H + E).charpoly.roots = (List.ofFn roots : Multiset ℂ))) μ := by
  sorry

end Theorems

end NLAlib.ShiftedQR
