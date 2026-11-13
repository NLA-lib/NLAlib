/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.IndexLiteral
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Blas.MapCorrect
public import NLAlib.Matrix.QRIteration.HessenbergDeflation

/-!
# Stored range stacks for the deflation worklist

The stack occupies one count word followed by pairs of natural words. The last pair is the
top. Counts are read through the actual bounded natural-index query; pushes materialize the
new range and count through counted dimension literals. Persistent capacity is a raw premise.

## Main results

* `NLAlib.ShiftedQR.StackHolds` describes the actual active stack words.
* `NLAlib.ShiftedQR.rangePush`, `NLAlib.ShiftedQR.rangePop` are scalar/index implementations.
* `NLAlib.ShiftedQR.rangePush_writes` proves total range insertion.
-/

@[expose] public section

namespace NLAlib.ShiftedQR

open Ops

/-- One real count followed by pairs `(lo,d)`, with the final pair at the top of the stack. -/
def StackHolds (b : ℕ × ℕ) (rs : List (ℕ × ℕ)) (st : Store ℝ) : Prop :=
  st.get b.1 b.2 = some (rs.length : ℝ) ∧ ∀ t (ht : t < rs.length),
    st.get b.1 (b.2 + 1 + 2 * t) = some (rs[t].1 : ℝ) ∧
    st.get b.1 (b.2 + 2 + 2 * t) = some (rs[t].2 : ℝ)

variable {Op Tst : Type} [Has IndexOp Op] [Has IdxTst Tst]

/-- Read the stored count with bound `capacity`, then write the supplied range and new count.
The stack view reserves `1+2*capacity` words; it is mutated in place. -/
def rangePush : Impl Op Tst := opsImpl% [capacity, lo, size] (St) → () {
  let count ← index (Has.inj IdxTst.toNat) (St) ≤ capacity;
  call (Has.inj IndexOp.lit) [lo] () → (St[1 + 2 * count]);
  call (Has.inj IndexOp.lit) [size] () → (St[2 + 2 * count]);
  call (Has.inj IndexOp.lit) [count + 1] () → (St)
}

/-- Read the actual count, copy the top pair to `R`, and write the decremented count.
Total execution requires a nonempty stack and a disjoint two-word output range. -/
def rangePop [Has ScalarOp Op] : Impl Op Tst := opsImpl% [capacity] (St) → (R) {
  let count ← index (Has.inj IdxTst.toNat) (St) ≤ capacity;
  run (unaryMap (Has.inj ScalarOp.copy)).body [2] (St[1 + 2 * (count - 1)], R);
  call (Has.inj IndexOp.lit) [count - 1] () → (St)
}

/-- The two new range words and the count are the only cells changed by a push. -/
def pushFp (b : ℕ × ℕ) (count : ℕ) : Fp :=
  Store.inBlock b.1 b.2 1 ⊔ Store.inBlock b.1 (b.2 + 1 + 2 * count) 2

/-- Inserting one final pair preserves every earlier range through the ordinary write frame. -/
theorem StackHolds.push {b : ℕ × ℕ} {rs : List (ℕ × ℕ)} {st st' : Store ℝ}
    (h : StackHolds b rs st) (r : ℕ × ℕ) (hfr : st.EqOff (pushFp b rs.length) st')
    (hc : st'.get b.1 b.2 = some ((rs.length + 1 : ℕ) : ℝ))
    (hl : st'.get b.1 (b.2 + 1 + 2 * rs.length) = some (r.1 : ℝ))
    (hd : st'.get b.1 (b.2 + 2 + 2 * rs.length) = some (r.2 : ℝ)) :
    StackHolds b (rs ++ [r]) st' := by
  refine ⟨by simpa using hc, fun t ht => ?_⟩
  by_cases hlt : t < rs.length
  · have hkeep (j : ℕ) (hj : j = b.2 + 1 + 2 * t ∨ j = b.2 + 2 + 2 * t) :
        st'.get b.1 j = st.get b.1 j := by
      apply hfr.get_eq
      rcases hj with rfl | rfl <;>
        simp [pushFp, Store.inBlock] <;> omega
    simpa only [List.getElem_append_left hlt] using
      And.intro ((hkeep _ (Or.inl rfl)).trans (h.2 t hlt).1)
        ((hkeep _ (Or.inr rfl)).trans (h.2 t hlt).2)
  · have ht' : t < rs.length + 1 := by simpa using ht
    have he : t = rs.length := by omega
    subst t
    simpa using And.intro hl hd

/-- Push executes the bounded query and three dimension-literal calls on the actual stack.
The persistent capacity and strict count bound guarantee room before any write. -/
theorem rangePush_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hL : IsIndexLit M I) (hQ : IsToNat id I) (hE : ExactModel id M)
    {τ : Tape ℝ} {m : Mem ℝ} {capacity lo size : ℕ} {b : ℕ × ℕ}
    {rs : List (ℕ × ℕ)} (hSt : StackHolds b rs m.store) (hcap : rs.length < capacity)
    (hroom : b.2 + 1 + 2 * capacity ≤ m.store.len b.1) :
    Writes .total I τ (rangePush (Op := Op) (Tst := Tst)).body
      (Env.frame [capacity, lo, size] [b]) (pushFp b rs.length)
      (fun m' => m'.pos = m.pos ∧ StackHolds b (rs ++ [(lo, size)]) m'.store) m := by
  have hlit (n : ℕ) : M.lit (n : ℚ) = (n : ℝ) := by simpa using hE.lit (n : ℚ)
  suffices hw : Writes .total I τ (rangePush (Op := Op) (Tst := Tst)).body
      (Env.frame [capacity, lo, size] [b]) (pushFp b rs.length)
      (fun m' => m'.pos = m.pos ∧
        m'.store.get b.1 b.2 = some ((rs.length + 1 : ℕ) : ℝ) ∧
        m'.store.get b.1 (b.2 + 1 + 2 * rs.length) = some (lo : ℝ) ∧
        m'.store.get b.1 (b.2 + 2 + 2 * rs.length) = some (size : ℝ)) m by
    exact hw.mono le_rfl fun _ hfr hp =>
      ⟨hp.1, hSt.push (lo, size) hfr hp.2.1 hp.2.2.1 hp.2.2.2⟩
  unfold rangePush
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hSt.1 rfl hcap.le ?_
  refine (writes_indexLit hL rfl rfl (by dsimp only; omega)).seq_le (by fp_sub [pushFp]) ?_
  intro m₁ hfr₁ ⟨hp₁, hLo⟩
  refine (writes_indexLit hL rfl rfl (by dsimp only; rw [hfr₁.len_eq]; omega)).seq_le
    (by fp_sub [pushFp]) ?_
  intro m₂ hfr₂ ⟨hp₂, hSize⟩
  refine (writes_indexLit hL rfl rfl (by dsimp only; rw [hfr₂.len_eq, hfr₁.len_eq]; omega)).mono
    (by fp_sub [pushFp]) ?_
  intro m₃ hfr₃ ⟨hp₃, hCount⟩
  refine ⟨hp₃.trans (hp₂.trans hp₁), by simpa only [hlit] using hCount, ?_, ?_⟩
  · have hLo₂ := hfr₂.keep (Store.readsOnly_get _ _ _) (by disjoint) hLo
    have hLo₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (by disjoint) hLo₂
    simpa only [hlit] using hLo₃
  · have hSize₃ := hfr₃.keep (Store.readsOnly_get _ _ _) (by disjoint) hSize
    simpa only [hlit] using hSize₃

/-- A range stack survives writes to a separate view of the same arena. -/
theorem StackHolds.of_eqOff {b : ℕ × ℕ} {rs : List (ℕ × ℕ)} {st st' : Store ℝ}
    {F : Fp} (h : StackHolds b rs st) (hfr : st.EqOff F st')
    (hd : Fp.Disj F (Store.inBlock b.1 b.2 (1 + 2 * rs.length))) : StackHolds b rs st' := by
  have hget (j : ℕ) (hj : b.2 ≤ j ∧ j < b.2 + (1 + 2 * rs.length)) :
      st'.get b.1 j = st.get b.1 j := hfr.get_eq fun hf => hd _ _ hf ⟨rfl, hj⟩
  exact ⟨(hget _ (by omega)).trans h.1, fun t ht =>
    ⟨(hget _ (by omega)).trans (h.2 t ht).1, (hget _ (by omega)).trans (h.2 t ht).2⟩⟩

/-- The top pair is an actual contiguous two-word block. -/
theorem StackHolds.read_top {b : ℕ × ℕ} {rs : List (ℕ × ℕ)} {r : ℕ × ℕ}
    {st : Store ℝ} (h : StackHolds b (rs ++ [r]) st) :
    st.readBlock b.1 (b.2 + 1 + 2 * rs.length) 2 = some [(r.1 : ℝ), (r.2 : ℝ)] := by
  have ht : st.get b.1 (b.2 + 1 + 2 * rs.length) = some (r.1 : ℝ) ∧
      st.get b.1 (b.2 + 2 + 2 * rs.length) = some (r.2 : ℝ) := by
    simpa using h.2 rs.length (by simp)
  rw [Store.readBlock_eq_some_iff]
  refine ⟨rfl, fun i hi => ?_⟩
  interval_cases i
  · simpa using ht.1
  · change st.get b.1 (b.2 + 1 + 2 * rs.length + 1) = some (r.2 : ℝ)
    convert ht.2 using 1; congr 1; omega

/-- Removing the count's last range leaves the earlier pairs unchanged. -/
private theorem StackHolds.pop_count {b : ℕ × ℕ} {rs : List (ℕ × ℕ)} {r : ℕ × ℕ}
    {st st' : Store ℝ} (h : StackHolds b (rs ++ [r]) st)
    (hfr : st.EqOff (Store.inBlock b.1 b.2 1) st')
    (hc : st'.get b.1 b.2 = some (rs.length : ℝ)) : StackHolds b rs st' := by
  refine ⟨hc, fun t ht => ?_⟩
  have ht' : t < (rs ++ [r]).length := by simp; omega
  have hpair := h.2 t ht'
  simp only [List.getElem_append_left ht] at hpair
  exact ⟨(hfr.get_eq (by simp [Store.inBlock]; omega)).trans hpair.1,
    (hfr.get_eq (by simp [Store.inBlock]; omega)).trans hpair.2⟩

/-- Pop reads the actual bounded count, copies the last pair into a separate output view,
and writes the decremented count. The persistent stack and output capacities are raw premises;
the earlier ranges and tape position are preserved by the same total run. -/
theorem rangePop_writes [Has ScalarOp Op] {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hS : IsScalar M I) (hL : IsIndexLit M I) (hQ : IsToNat id I) (hE : ExactModel id M)
    {τ : Tape ℝ} {m : Mem ℝ} {capacity : ℕ} {b out : ℕ × ℕ}
    {rs : List (ℕ × ℕ)} {r : ℕ × ℕ} (hSt : StackHolds b (rs ++ [r]) m.store)
    (hcap : rs.length + 1 ≤ capacity)
    (hroom : b.2 + 1 + 2 * capacity ≤ m.store.len b.1)
    (hout : out.2 + 2 ≤ m.store.len out.1) (hl : m.Live [b, out])
    (hd : Fp.Disj (Store.inBlock out.1 out.2 2)
      (Store.inBlock b.1 b.2 (1 + 2 * capacity))) :
    Writes .total I τ (rangePop (Op := Op) (Tst := Tst)).body
      (Env.frame [capacity] [b, out])
      (Store.inBlock b.1 b.2 1 ⊔ Store.inBlock out.1 out.2 2)
      (fun m' => m'.pos = m.pos ∧ StackHolds b rs m'.store ∧
        m'.store.readBlock out.1 out.2 2 = some [(r.1 : ℝ), (r.2 : ℝ)]) m := by
  have hcount : m.store.get b.1 b.2 = some ((rs.length + 1 : ℕ) : ℝ) := by
    simpa using hSt.1
  have htop := hSt.read_top
  have hsep : Fp.Disj (Store.inBlock b.1 (b.2 + 1 + 2 * rs.length) 2)
      (Store.inBlock out.1 out.2 2) := by
    intro c j hB hO
    exact hd c j hO ⟨hB.1, by have := hB.2.1; omega, by have := hB.2.2; omega⟩
  unfold rangePop
  refine writes_bindIdx_of_decode_nat hQ rfl rfl hcount rfl hcap ?_
  have hw := writes_unaryMap_of_disj_or_eq (md := .total) (τ := τ) (f := id)
    (x := (b.1, b.2 + 1 + 2 * rs.length)) (y := out) (hS .copy) (Or.inl hsep) htop hout
  simp only [List.map_id] at hw
  refine hw.frame_seq_le rfl rfl (by simpa [Mem.Live] using hl) le_sup_right ?_
  intro m₁ hfr₁ ⟨hp₁, hOut⟩
  have hSt₁ := hSt.of_eqOff hfr₁ (by
    simp only [List.length_append, List.length_singleton]
    exact hd.mono le_rfl (fun c j hj =>
      ⟨hj.1, hj.2.1, by have := hj.2.2; omega⟩))
  refine (writes_indexLit hL rfl rfl
    (by rw [hfr₁.len_eq]; omega)).mono le_sup_left ?_
  intro m₂ hfr₂ ⟨hp₂, hCount⟩
  have hCount' : m₂.store.get b.1 b.2 = some (rs.length : ℝ) := by
    simpa only [Nat.add_sub_cancel, show M.lit (rs.length : ℚ) = (rs.length : ℝ) by
      simpa using hE.lit (rs.length : ℚ)] using hCount
  refine ⟨hp₂.trans hp₁, hSt₁.pop_count hfr₂ hCount', ?_⟩
  exact hfr₂.keep (Store.readsOnly_readBlock _ _ _ _)
    (hd.symm.mono (by fp_sub) le_rfl) hOut

/-- Initialize an empty count and push one initial range into reserved stack storage. -/
def stackInit : Impl Op Tst := opsImpl% [capacity, lo, size] () → (St) {
  call (Has.inj IndexOp.lit) [0] () → (St);
  run (rangePush (Op := Op) (Tst := Tst)).body [capacity, lo, size] (St)
}

/-- The initial stack is built from literal words, with no initialized stack premise. -/
theorem stackInit_writes {M : Machine ℝ} {I : Interp Op Tst ℝ}
    (hL : IsIndexLit M I) (hQ : IsToNat id I) (hE : ExactModel id M)
    {τ : Tape ℝ} {m : Mem ℝ} {capacity lo size : ℕ} {b : ℕ × ℕ}
    (hcap : 0 < capacity) (hroom : b.2 + 1 + 2 * capacity ≤ m.store.len b.1) :
    Writes .total I τ (stackInit (Op := Op) (Tst := Tst)).body
      (Env.frame [capacity, lo, size] [b]) (Store.inBlock b.1 b.2 (1 + 2 * capacity))
      (fun m' => m'.pos = m.pos ∧ StackHolds b [(lo, size)] m'.store) m := by
  have hlit : M.lit (0 : ℚ) = (0 : ℝ) := by simpa using hE.lit 0
  unfold stackInit
  refine (writes_indexLit hL rfl rfl (by dsimp only; omega)).seq_le (by fp_sub) ?_
  intro m₁ hfr₁ ⟨hp₁, hzero⟩
  have hs : StackHolds b [] m₁.store :=
    ⟨by simpa only [List.length_nil, Nat.cast_zero, hlit] using hzero,
      fun _ ht => by simp only [List.length_nil] at ht; omega⟩
  have hw := rangePush_writes (τ := τ) hL hQ hE hs (capacity := capacity)
    (lo := lo) (size := size) hcap (by rw [hfr₁.len_eq]; exact hroom)
  refine (hw.in_frame rfl rfl ?_).mono (by simp only [List.length_nil]; fp_sub [pushFp]) ?_
  · have hb := Store.lt_length_of_lt_len (show b.2 < m.store.len b.1 by omega)
    simpa [Mem.Live, ← hfr₁.length_eq] using hb
  · intro _ _ ⟨hp₂, hstack⟩
    exact ⟨hp₂.trans hp₁, by simpa only [List.nil_append] using hstack⟩

end NLAlib.ShiftedQR
