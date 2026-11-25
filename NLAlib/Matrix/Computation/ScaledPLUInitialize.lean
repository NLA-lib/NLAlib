/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.ScaledPLUIteration

/-!
# Original row scales and initialized LU factors

Row scales are computed once from the input and stored after the residual matrix in a single
scoped buffer. Copying the residual and clearing the factors retains that disjoint suffix.

## Main results

* `NLAlib.Computation.ScaledPLU.exec_body`: initialization and all scaled elimination steps.
-/

@[expose] public section

namespace NLAlib.Computation.ScaledPLU

open scoped Matrix
open Builder

variable {P ι : Type} [DecidableEq P]

private theorem exec_initialize (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A S L U H : ℕ) (ao lo uo ho : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : Holds st.store tag A ao.eval M)
    (hS : Writable st.store tag S 0 (n.eval * n.eval))
    (hsc : Writable st.store tag S (n.eval * n.eval) n.eval)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval))
    (hU : Writable st.store tag U uo.eval (n.eval * n.eval))
    (hAS : A ≠ S) (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) :
    ∃ out, exec I (do
      rowScales tag n n A ao S (n * n)
      copyv tag A ao S 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)).run st = some out ∧
      State st.store tag M S L U H lo.eval uo.eval ho.eval 0 out.store := by
  have hs : IsRelErrSem (fun _ => 0) (fun _ x => x) (fun _ _ => True) I.sem := by
    rw [hI]; exact isRelErrSem_exactSem
  obtain ⟨scaled, W, hr₁, hw₁, hd⟩ := hs.exec_rowScales I tag trivial st n n A ao S (n * n)
    M (fun i j => ⟨M i j, hM i j, rfl⟩) hsc (fun _ => hAS)
  have hM' : Holds scaled.store tag A ao.eval M := fun i j =>
    (Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hAS)).trans (hM i j)
  have hshape₁ := Store.shape_of_writeBlock_eq_some hw₁
  obtain ⟨out, hr₂, hshape₂, hframe, hR, hF, hG⟩ := exec_luInitialize I hI hc tag scaled n
    A S L U ao lo uo M hM' (hS.of_shape_eq hshape₁) (hL.of_shape_eq hshape₁)
    (hU.of_shape_eq hshape₁) hAS hSL hSU hLU
  refine ⟨out, ?_, State.zero ⟨hshape₂.trans hshape₁, ?_⟩ hR hF hG ?_⟩
  · rw [exec_run_bind I (b := rowScales tag n n A ao S (n * n)) (fun _ => rfl),
      hr₁, Option.bind_some]
    exact hr₂
  · intro q b i hbS hbL hbU _
    rw [hframe q b i (Or.inl hbS) hbL hbU,
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hbS)]
  · intro i
    refine ⟨W i, ?_, hd i⟩
    rw [hframe tag S (n.eval * n.eval + i) (by omega) (Or.inl hSL) (Or.inl hSU)]
    simpa only [IExp.eval_mul, Array.getElem?_ofFn, Fin.isLt, ↓reduceDIte, Fin.eta] using
      Store.read_of_writeBlock_eq_some_of_lt (j := i.val) hw₁ (by simp)

private theorem exec_emptyBody {K C : Type} [AddMonoid C] (I : Interp P ι K C) (tag : P)
    (st : St P K C) (n : IExp ℕ) (A S L U H : ℕ) (ao lo uo ho : IExp ℕ)
    (hn : n.eval = 0) : exec I (do
      rowScales tag n n A ao S (n * n)
      copyv tag A ao S 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        scaledPartialPivot tag n (.var k) S 0 S (n * n) ⟨H, ho + IExp.var k⟩
        bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
          swapRows tag n n L lo (.var k) (.var selected)
        luColumnTotal tag n (.var k) S L U 0 lo uo
        schurStepTotal tag n S 0 (.var k)).run st = some st := by
  change exec I (.seq (.loop n _) (.seq (.named "copy" _ (.seq (.loop (n * n) _) .skip))
    (.seq (.loop (n * n) _) (.seq (.loop (n * n) _) (.seq (.loop n _) .skip))))) st = some st
  simp only [exec_seq, exec_named, exec_loop, IExp.eval_mul, hn, zero_mul,
    List.range_zero, List.foldlM_nil, Option.pure_def, Option.bind_some, exec_skip]

/-- Compute original row scales once, initialize the factors, and execute every active scaled
pivot and elimination step. The packed scratch buffer has exactly $N^2+N$ cells. Empty
matrices execute only empty loops and do not require initialized storage or valid handles. -/
theorem exec_body (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n : IExp ℕ)
    (A L U H : ℕ) (ao lo uo ho : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : Holds initial tag A ao.eval M)
    (hL : Writable initial tag L lo.eval (n.eval * n.eval))
    (hU : Writable initial tag U uo.eval (n.eval * n.eval))
    (hH : Writable initial tag H ho.eval n.eval) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (hstore : st.store = initial.push (tag, Array.replicate (n.eval * n.eval + n.eval) none)) :
    ∃ out, exec I (do
      rowScales tag n n A ao initial.size (n * n)
      copyv tag A ao initial.size 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        scaledPartialPivot tag n (.var k) initial.size 0 initial.size (n * n)
          ⟨H, ho + IExp.var k⟩
        bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
          swapRows tag n n L lo (.var k) (.var selected)
        luColumnTotal tag n (.var k) initial.size L U 0 lo uo
        schurStepTotal tag n initial.size 0 (.var k)).run st = some out ∧
      State st.store tag M initial.size L U H lo.eval uo.eval ho.eval n.eval out.store := by
  by_cases hn : n.eval = 0
  · exact ⟨st, exec_emptyBody I tag st n A initial.size L U H ao lo uo ho hn,
      State.empty st.store tag M initial.size L U H lo.eval uo.eval ho.eval hn⟩
  have hN : 0 < n.eval := Nat.pos_of_ne_zero hn
  have hAb : A < initial.size := Store.lt_size_of_read_eq_some (hM ⟨0, hN⟩ ⟨0, hN⟩)
  have hLb := hL.lt_size (Nat.mul_pos hN hN)
  have hUb := hU.lt_size (Nat.mul_pos hN hN)
  have hHb := hH.lt_size hN
  have hMp : Holds st.store tag A ao.eval M := fun i j => by
    rw [hstore, Store.read_push_of_lt hAb]
    exact hM i j
  have hS : Writable st.store tag initial.size 0 (n.eval * n.eval) := by
    rw [hstore]
    exact writable_of_shape_eq rfl (Store.getElem?_shape_push_size initial tag
      (n.eval * n.eval + n.eval)) (by omega)
  have hsc : Writable st.store tag initial.size (n.eval * n.eval) n.eval := by
    rw [hstore]
    exact writable_of_shape_eq rfl (Store.getElem?_shape_push_size initial tag
      (n.eval * n.eval + n.eval)) (by omega)
  have hLp : Writable st.store tag L lo.eval (n.eval * n.eval) := hstore ▸ hL.push _
  have hUp : Writable st.store tag U uo.eval (n.eval * n.eval) := hstore ▸ hU.push _
  have hHp : Writable st.store tag H ho.eval n.eval := hstore ▸ hH.push _
  obtain ⟨ready, hr₁, h0⟩ := exec_initialize I hI hc tag st n A initial.size L U H ao lo uo ho
    M hMp hS hsc hLp hUp (Nat.ne_of_lt hAb) (Nat.ne_of_gt hLb) (Nat.ne_of_gt hUb) hLU
  obtain ⟨out, hr₂, hs⟩ := exists_exec_loop_eq_some_of_forall I
    (n := n) (fun k σ => State st.store tag M initial.size L U H lo.eval uo.eval ho.eval k
      σ.store) h0 (fun k hk σ hσ => exec_iteration I hI hc tag st.store n M
      initial.size L U H lo uo ho hHp (Nat.ne_of_gt hLb) (Nat.ne_of_gt hUb)
      (Nat.ne_of_gt hHb) hLU hLH hUH k hk σ hσ)
  refine ⟨out, ?_, hs⟩
  have hcomp : ExecutionComposable I (do
      rowScales tag n n A ao initial.size (n * n)
      copyv tag A ao initial.size 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)) :=
    (executionComposable_single I (fun _ => rfl)).bind
      ((executionComposable_single I (fun _ => rfl)).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          (executionComposable_single I (fun _ => rfl))))
  change exec I ((do
    rowScales tag n n A ao initial.size (n * n)
    copyv tag A ao initial.size 0 (n * n)
    forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
    forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)) >>= fun _ =>
    forRange n fun k => do
      scaledPartialPivot tag n (.var k) initial.size 0 initial.size (n * n)
        ⟨H, ho + IExp.var k⟩
      bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
        swapRows tag n n L lo (.var k) (.var selected)
      luColumnTotal tag n (.var k) initial.size L U 0 lo uo
      schurStepTotal tag n initial.size 0 (.var k)).run st = some out
  rw [hcomp, hr₁, Option.bind_some]
  change exec I (.seq (.loop n _) .skip) ready = some out
  rw [exec_seq_skip]
  exact hr₂

end NLAlib.Computation.ScaledPLU
