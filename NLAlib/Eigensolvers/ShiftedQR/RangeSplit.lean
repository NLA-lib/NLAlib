/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.ShiftedQR.WorklistSolve

/-!
# Committing and splitting a decoupled active range

The actual work matrix is copied back into its global diagonal view. A small subdiagonal
entry determines two nonempty child ranges, which are pushed right then left. The mathematical
perturbation charge and stored range transition refer to the same committed work matrix.

## Main results

* `NLAlib.ShiftedQR.writeAndSplit_writes`: commit and split advance the full invariant.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops
open scoped Matrix

variable {O Q : Type} [Has ScalarOp O] [Has IndexOp O] [Has IdxTst Q]

/-- Copying back the actual unitary-conjugate block and pushing its children advances the
worklist invariant. The partition itself proves capacity for both new stack entries. -/
theorem writeAndSplit_writes {M : Machine ℝ} {I : Interp O Q ℝ}
    (hS : IsScalar M I) (hE : ExactModel id M) (hL : IsIndexLit M I) (hQ : IsToNat id I)
    {tape : Tape ℝ} {μ : Mem ℝ} {n d lo j : ℕ} {i : Fin d}
    {a p stack out w r : ℕ × ℕ} {H A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {U B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} {roots : Fin (n + 1) → ℂ}
    {τ ε : ℝ} {rest done : List (ℕ × ℕ)}
    (hG : WorklistGeometry (n + 1) a p stack out w r μ)
    (hInv : DeflationInv H ε ((lo, d + 1) :: rest) done A roots)
    (hA : HoldsMatrix a A μ.store) (hW : HoldsMatrix w B μ.store)
    (hOut : FinishedHolds out done roots μ.store) (hSt : StackHolds stack rest.reverse μ.store)
    (hU : HasOrthonormalCols U) (hB : B = Uᴴ * subBlock A (lo, d + 1) * U)
    (hHess : IsUpperHessenberg B) (hsmall : ‖B i.succ i.castSucc‖ ≤ τ)
    (hε : ε = (((((lo, d + 1) :: rest) ++ done).length - 1 : ℕ) : ℝ) * τ)
    (hj : 2 * done.length + ((lo, d + 1) :: rest).length = j + 1) :
    Writes .total I tape (writeAndSplit (O := O) (Q := Q)).body
      (Env.frame [n + 1, lo, d + 1, i] [a, stack, w])
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))) ⊔
        Store.inBlock stack.1 stack.2 (1 + 2 * (n + 1)))
      (fun μ' => μ'.pos = μ.pos ∧ WorklistInv H τ a stack out (j + 1) μ') μ := by
  let A' := setSubBlock A (lo, d + 1) B
  let left := (lo, (i : ℕ) + 1)
  let right := (lo + i + 1, d + 1 - i - 1)
  have hr := (hInv.active_block (r := (lo, d + 1)) List.mem_cons_self).2.1
  have hnewInv := hInv.conj_split hU hB hHess hr i.isLt hsmall
  have hcap : rest.reverse.length + 2 ≤ n + 1 := by
    have hb := hnewInv.length_le
    simp only [List.length_append, List.length_cons, List.length_reverse] at hb ⊢
    omega
  have hrest : rest.length ≤ n + 1 := by
    have hb : rest.length + 2 ≤ n + 1 := by simpa using hcap
    omega
  have hAO : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock out.1 out.2 (2 * (n + 1))) := by simpa using hG.disj 0 3 (by omega)
  have hAS : Fp.Disj (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1))))
      (Store.inBlock stack.1 stack.2 (1 + 2 * (n + 1))) := by
    simpa using hG.disj 0 2 (by omega)
  have hWA : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((d + 1) * (d + 1))))
      (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := by
    have hb : d + 1 ≤ n + 1 := by omega
    have hs := Nat.mul_le_mul hb hb
    have hfull : Fp.Disj (Store.inBlock w.1 w.2 (2 * ((n + 1) * (n + 1))))
        (Store.inBlock a.1 a.2 (2 * ((n + 1) * (n + 1)))) := by
      simpa using hG.disj 4 0 (by omega)
    exact hfull.mono (by fp_sub) le_rfl
  have hdone : finishedFp out done ≤ Store.inBlock out.1 out.2 (2 * (n + 1)) :=
    finishedFp_le (fun q hq => (hInv.partition.2.1 q (List.mem_append_right _ hq)).2)
  unfold writeAndSplit
  refine (copyToGlobal_writes (τ := tape) hS
    (by simpa [Mem.Live] using And.intro (hG.live w (by simp)) (hG.live a (by simp)))
    hA hW hr hG.room.1 hWA).frame_seq_le rfl rfl
      (by simpa [Mem.Live] using And.intro (hG.live w (by simp)) (hG.live a (by simp)))
      ((blockFp_le a hr).trans le_sup_left) ?_
  intro μ₁ hfr₁ ⟨hp₁, hA₁⟩
  have hG₁ := hG.of_eqOff hfr₁
  have hSt₁ := hSt.of_eqOff hfr₁
    (hAS.mono (blockFp_le a hr) (by simp only [List.length_reverse]; fp_sub))
  have hOut₁ := hOut.of_eqOff hfr₁ (hAO.mono (blockFp_le a hr) hdone)
  have hw := splitPush_writes (τ := tape) (lo := lo) (d := d + 1) (i := (i : ℕ))
    hL hQ hE
    (by simpa [Mem.Live] using hG₁.live stack (by simp)) hSt₁ hcap
      (by simpa only [Nat.add_assoc] using hG₁.room.2.2.1)
  refine (hw.in_frame rfl rfl (by simpa [Mem.Live] using hG₁.live stack (by simp))).mono
    le_sup_right ?_
  intro μ₂ hfr₂ ⟨hp₂, hSt₂⟩
  have hSO : Fp.Disj (Store.inBlock stack.1 stack.2 (1 + 2 * (n + 1)))
      (Store.inBlock out.1 out.2 (2 * (n + 1))) := by simpa using hG₁.disj 2 3 (by omega)
  refine ⟨hp₂.trans hp₁, left :: right :: rest, done, A', roots, ε + τ, hnewInv,
    hA₁.of_eqOff hfr₂ hAS.symm, hOut₁.of_eqOff hfr₂ (hSO.mono le_rfl hdone), ?_, ?_, ?_⟩
  · simpa [left, right, List.reverse_cons, List.append_assoc] using hSt₂
  · have ho : ((((lo, d + 1) :: rest) ++ done).length - 1) = rest.length + done.length := by
      simp only [List.length_append, List.length_cons]
      omega
    have hn : (((left :: right :: rest) ++ done).length - 1) = rest.length + done.length + 1 := by
      simp only [List.length_append, List.length_cons]
      omega
    rw [hε, ho, hn]
    push_cast
    ring
  · simp only [List.length_cons] at hj ⊢
    omega

end NLAlib.ShiftedQR
