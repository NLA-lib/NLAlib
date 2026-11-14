/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Orthogonalization.CGS2.ExtendColumn

/-!
# The loop of the column-wise two-pass Gram–Schmidt extension

The loop over the columns of `NLAlib.CGS2.cgs2Extend` with its invariant: the new columns, the
reduced columns and the coefficient columns before the current one are each read as one block,
the columns of the block from the current one on hold the words read at entry, and every
column before the current one satisfies `NLAlib.CGS2.ColOut` against the basis followed by the
earlier new columns. The result is the contract of a basis extension for every predicate on the
decoded matrices that follows from the relations of the columns; the exact and the rounded
contract are two instances.

## Main definitions

* `NLAlib.CGS2.ColsDone`: the relations of the columns before the current one.
* `NLAlib.CGS2.ColsStored`: the invariant of the loop on the store.

## Main results

* `NLAlib.CGS2.ColsDone.succ`: one more column.
* `NLAlib.CGS2.writes_round`: a round keeps the invariant.
* `NLAlib.CGS2.cgs2Extend_triple_of`: the program meets the contract of a basis extension for
  every predicate implied by the relations of its columns.
-/

@[expose] public section

namespace NLAlib.CGS2

open Ops Krylov.Lanczos.Reorth

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst]

omit [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst] in
/-- **The relations of the columns before `c`**: for the basis words `qs`, the block words `ws`
read at entry, the new columns `qn`, the reduced columns `wd` and the coefficient columns `cs`
written so far, every column `c' < c` satisfies `NLAlib.CGS2.ColOut` with the stored columns
`(qs ++ qn).take ((k + c') * n)`, the basis followed by the new columns before `c'`. -/
def ColsDone (M : Machine K) (dec : K → ℝ) (ed ea : ℝ) (N : (ℕ → K) → K → Prop)
    (S : K → (ℕ → K) → (ℕ → K) → Prop) (τ : ℚ) (n k b : ℕ) (qs ws : List K) (c : ℕ)
    (qn wd cs : List K) : Prop :=
  ∀ c' < c, ColOut M dec ed ea N S τ n (k + c') (k + b) ((qs ++ qn).take ((k + c') * n))
    ((ws.drop (c' * n)).take n) ((wd.drop (c' * n)).take n)
    ((cs.drop (c' * (k + b))).take (k + b)) ((qn.drop (c' * n)).take n)

omit [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst] in
/-- One more column: appending the three columns written by round `c` keeps the relations of
the earlier columns, whose slices are unchanged, and adds those of column `c`. -/
theorem ColsDone.succ {M : Machine K} {dec : K → ℝ} {ed ea : ℝ} {N : (ℕ → K) → K → Prop}
    {S : K → (ℕ → K) → (ℕ → K) → Prop} {τ : ℚ} {n k b c : ℕ}
    {qs ws qn wd cs w₂ cc qc : List K} (h : ColsDone M dec ed ea N S τ n k b qs ws c qn wd cs)
    (hqs : qs.length = k * n) (hqn : qn.length = c * n) (hwd : wd.length = c * n)
    (hcs : cs.length = c * (k + b)) (hw₂ : w₂.length = n) (hcc : cc.length = k + b)
    (hqc : qc.length = n)
    (hcol : ColOut M dec ed ea N S τ n (k + c) (k + b) (qs ++ qn) ((ws.drop (c * n)).take n)
      w₂ cc qc) :
    ColsDone M dec ed ea N S τ n k b qs ws (c + 1) (qn ++ qc) (wd ++ w₂) (cs ++ cc) := by
  intro c' hc'
  obtain hlt | heq : c' < c ∨ c' = c := by omega
  · have h1 : c' * n + n ≤ c * n := by
      have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hlt)
      rwa [Nat.succ_mul] at h
    have h2 : c' * (k + b) + (k + b) ≤ c * (k + b) := by
      have h := Nat.mul_le_mul_right (k + b) (Nat.succ_le_of_lt hlt)
      rwa [Nat.succ_mul] at h
    have h3 : (k + c') * n ≤ k * n + c * n := by
      rw [Nat.add_mul]
      omega
    have e1 : (qs ++ (qn ++ qc)).take ((k + c') * n) = (qs ++ qn).take ((k + c') * n) := by
      rw [← List.append_assoc,
        List.take_append_of_le_length (by rw [List.length_append]; omega)]
    have e2 : ((wd ++ w₂).drop (c' * n)).take n = (wd.drop (c' * n)).take n := by
      rw [List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by rw [List.length_drop]; omega)]
    have e3 : ((cs ++ cc).drop (c' * (k + b))).take (k + b) =
        (cs.drop (c' * (k + b))).take (k + b) := by
      rw [List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by rw [List.length_drop]; omega)]
    have e4 : ((qn ++ qc).drop (c' * n)).take n = (qn.drop (c' * n)).take n := by
      rw [List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by rw [List.length_drop]; omega)]
    rw [e1, e2, e3, e4]
    exact h c' hlt
  · have e1 : (qs ++ (qn ++ qc)).take ((k + c) * n) = qs ++ qn := by
      rw [← List.append_assoc,
        List.take_left' (by rw [List.length_append, Nat.add_mul]; omega)]
    have e2 : ((wd ++ w₂).drop (c * n)).take n = w₂ := by
      rw [List.drop_left' hwd, List.take_of_length_le (by omega)]
    have e3 : ((cs ++ cc).drop (c * (k + b))).take (k + b) = cc := by
      rw [List.drop_left' hcs, List.take_of_length_le (by omega)]
    have e4 : ((qn ++ qc).drop (c * n)).take n = qc := by
      rw [List.drop_left' hqn, List.take_of_length_le (by omega)]
    rw [heq, e1, e2, e3, e4]
    exact hcol

omit [Has ScalarOp Op] [Has Blas1Op Op] [Has CmpTst Tst] in
/-- **The invariant of the loop on the store** before round `c`: the first `c` columns of the
new block, of the block and of the coefficient block are read as three blocks whose columns
satisfy `NLAlib.CGS2.ColsDone`. -/
def ColsStored (M : Machine K) (dec : K → ℝ) (ed ea : ℝ) (N : (ℕ → K) → K → Prop)
    (S : K → (ℕ → K) → (ℕ → K) → Prop) (τ : ℚ) (n k b : ℕ) (Q W C : ℕ × ℕ) (qs ws : List K)
    (c : ℕ) (s : Store K) : Prop :=
  ∃ qn wd cs, s.readBlock Q.1 (Q.2 + k * n) (c * n) = some qn ∧
    s.readBlock W.1 W.2 (c * n) = some wd ∧ s.readBlock C.1 C.2 (c * (k + b)) = some cs ∧
    ColsDone M dec ed ea N S τ n k b qs ws c qn wd cs

/-- A round keeps the invariant. From a memory with the layout of the rounds, the basis
`qs`, the words read at entry in column `c` of the block and the invariant before round `c`,
the round writes only its three columns and the scratch, keeps the position, and establishes
the invariant before round `c + 1`. -/
theorem writes_round {M : Machine K} {dec : K → ℝ} {ed : ℕ → ℝ} {ea : ℝ}
    {N : ℕ → (ℕ → K) → K → Prop} {S : ℕ → K → (ℕ → K) → (ℕ → K) → Prop} {ok : ℕ → Prop}
    {I : Interp Op Tst K} (ops : ColOps M dec ed ea N S ok I) {τ' : Tape K} {τ : ℚ}
    {n k b c : ℕ} {Q W C : ℕ × ℕ} {hb tb : ℕ} {m : Mem K} {qs ws : List K}
    (L : ColMem n k b Q W C hb tb m) (hc : c < b) (hok : ok n)
    (hqs : m.store.readBlock Q.1 Q.2 (k * n) = some qs)
    (hw : m.store.readBlock W.1 (W.2 + c * n) n = some ((ws.drop (c * n)).take n))
    (hinv : ColsStored M dec (ed n) ea (N n) (S n) τ n k b Q W C qs ws c m.store) :
    Writes .total I τ' (cgs2ExtendColumn τ) (colEnv n k b c Q W C hb tb)
      (colFp n k b c Q W C hb tb)
      (fun m' => m'.pos = m.pos ∧
        ColsStored M dec (ed n) ea (N n) (S n) τ n k b Q W C qs ws (c + 1) m'.store) m := by
  obtain ⟨qn, wd, cs, hqn, hwd, hcs, hdone⟩ := hinv
  have hV : m.store.readBlock Q.1 Q.2 ((k + c) * n) = some (qs ++ qn) := by
    rw [Nat.add_mul]
    exact Store.readBlock_add hqs hqn
  refine (writes_column ops L hc hok hV hw).mono le_rfl ?_
  intro m' hfr ⟨hpos, w₂, cc, qc, hw₂, hcc, hqc, hcol⟩
  obtain ⟨hQW, hQC, hWC, hQh, hWh, hCh, hht, -⟩ := id L
  have hWQ : W.1 ≠ Q.1 := hQW.symm
  have hCQ : C.1 ≠ Q.1 := hQC.symm
  have hCW : C.1 ≠ W.1 := hWC.symm
  refine ⟨hpos, qn ++ qc, wd ++ w₂, cs ++ cc, ?_, ?_, ?_,
    hdone.succ (Store.length_of_readBlock hqs) (Store.length_of_readBlock hqn)
      (Store.length_of_readBlock hwd) (Store.length_of_readBlock hcs)
      (Store.length_of_readBlock hw₂) (Store.length_of_readBlock hcc)
      (Store.length_of_readBlock hqc) hcol⟩
  · rw [Nat.succ_mul]
    exact Store.readBlock_add (hfr.readBlock_of hqn fun j hj => by disjoint) hqc
  · rw [Nat.succ_mul]
    exact Store.readBlock_add (hfr.readBlock_of hwd fun j hj => by disjoint) hw₂
  · rw [Nat.succ_mul]
    exact Store.readBlock_add (hfr.readBlock_of hcs fun j hj => by disjoint) hcc

/-- The column-wise two-pass extension meets the contract of a basis extension for every
predicate implied by the relations of its columns. Under the contracts `NLAlib.CGS2.ColOps`
of the operations, the implementation with the threshold `θ` runs on all admitted operands at
the dimensions `ok`, which the level-1 operations must admit, and its decoded output satisfies
`P` whenever `P` follows from `NLAlib.CGS2.ColsDone` of the `b` columns for blocks of the
declared lengths. -/
theorem cgs2Extend_triple_of {M : Machine K} {dec : K → ℝ} {ed : ℕ → ℝ} {ea : ℝ}
    {N : ℕ → (ℕ → K) → K → Prop} {S : ℕ → K → (ℕ → K) → (ℕ → K) → Prop} {okB : ℕ → Prop}
    {I : Interp Op Tst K} (ops : ColOps M dec ed ea N S okB I) {θ : ℚ}
    {ok : ℕ → ℕ → ℕ → Prop} {P : ExtendPred ℝ} (hok : ∀ n k b, ok n k b → okB n)
    (hP : ∀ n k b (qs ws qn wd cs : List K), ok n k b → qs.length = k * n →
      ws.length = b * n → qn.length = b * n → wd.length = b * n → cs.length = b * (k + b) →
      ColsDone M dec (ed n) ea (N n) (S n) θ n k b qs ws b qn wd cs →
      ExtendOut dec P n k b qs ws qn cs) :
    (cgs2ExtendImpl (Op := Op) (Tst := Tst) θ).Triple I .total
      ((extendRelOf dec ok P).spec ExtendOperands) := by
  cert_intro [n, k, b] (Q, W) → (Qn, W', C) reads (qs, ws)
  obtain ⟨rfl, hW, hQW, hQC, hWC⟩ := hadm
  subst W'
  obtain ⟨hlQ, hlW, -, -, hlC⟩ := hl
  obtain ⟨hzQ, hzW, hzC⟩ := hz
  have hdom' : ok n k b := hdom
  have hokn := hok _ _ _ hdom'
  change Writes _ _ _ (Stmt.alloc (IExp.var 1 + IExp.var 2) (Stmt.alloc (IExp.const 3)
    (Stmt.loop (IExp.var 2) (cgs2ExtendColumn θ)))) _ _ _ _
  refine writes_alloc rfl fun s₁ hs₁ hH hB₁ => writes_alloc rfl fun s₂ hs₂ hT hB₂ => ?_
  simp only [hs₁] at hs₂ hT hB₂ ⊢
  have hlen₂ : ∀ x < μ.store.length, s₂.len x = μ.store.len x := fun x hx =>
    (hB₂ x (by omega)).1.trans (hB₁ x hx).1
  have L₀ : ColMem n k b Q W C μ.store.length (μ.store.length + 1) (⟨s₂, μ.pos⟩ : Mem K) :=
    ⟨hQW, hQC, hWC, hlQ, hlW, hlC, Nat.lt_succ_self _, hs₂ ▸ Nat.lt_succ_self _,
      le_of_le_of_eq hzQ (hlen₂ _ hlQ).symm, le_of_le_of_eq hzW (hlen₂ _ hlW).symm,
      le_of_le_of_eq hzC (hlen₂ _ hlC).symm,
      ((hB₂ _ (Nat.lt_succ_self _)).1.trans hH).ge, hT.ge⟩
  refine Writes.mono (writes_loop (N := b) rfl
    (fun c => Store.inBlock W.1 W.2 (c * n) ⊔ Store.inBlock C.1 C.2 (c * (k + b)) ⊔
      Store.inBlock Q.1 (Q.2 + k * n) (c * n) ⊔ Store.inBuf μ.store.length ⊔
      Store.inBuf (μ.store.length + 1))
    (fun c hc => by fp_sub)
    (fun c m' => m'.pos = μ.pos ∧
      ColsStored M dec (ed n) ea (N n) (S n) θ n k b Q W C qs ws c m'.store)
    ⟨rfl, [], [], [], by simp, by simp, by simp, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    fun c hc m' hfr ⟨hpos, hinv⟩ => ?_)
    (by simp only [Nat.mul_comm b (k + b)]; fp_sub) ?_
  · have hcn : c * n + n ≤ b * n := by
      have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hc)
      rwa [Nat.succ_mul] at h
    have hqs' : m'.store.readBlock Q.1 Q.2 (k * n) = some qs := by kept
    have hwc : μ.store.readBlock W.1 (W.2 + c * n) n = some ((ws.drop (c * n)).take n) :=
      Store.readBlock_sub hws (by omega)
    have hw : m'.store.readBlock W.1 (W.2 + c * n) n = some ((ws.drop (c * n)).take n) := by
      kept
    exact (writes_round ops (L₀.of_eqOff hfr) hc hokn hqs' hw hinv).mono (by fp_sub)
      fun m'' _ h => ⟨h.1.trans hpos, h.2⟩
  · rintro m' - ⟨hpos, qn, wd, cs, hqn, hwd, hcs, hdone⟩ s₃ hs₃ hB₃ s₄ hs₄ hB₄
    have hB := (hB₃.mono (by omega)).trans hB₄
    have hcs' : m'.store.readBlock C.1 C.2 ((k + b) * b) = some cs := by
      rw [Nat.mul_comm]
      exact hcs
    refine ⟨by simp [hpos], [qn, wd, cs], Mem.readBlocks_of_cons (hB.readBlock_of hlQ hqn)
      (Mem.readBlocks_of_cons (hB.readBlock_of hlW hwd)
        (Mem.readBlocks_of_cons (hB.readBlock_of hlC hcs') rfl)), ?_⟩
    exact hP n k b qs ws qn wd cs hdom' (Store.length_of_readBlock hqs)
      (Store.length_of_readBlock hws) (Store.length_of_readBlock hqn)
      (Store.length_of_readBlock hwd) (Store.length_of_readBlock hcs) hdone

end NLAlib.CGS2
