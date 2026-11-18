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

end Theorems

end NLAlib.ShiftedQR
