/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.BlockedLUSteps
public import NLAlib.Matrix.Computation.TrailingSchurUpdate
public import Mathlib.Algebra.Order.Floor.Div

/-!
# Full blocked LU body execution

Panels advance the canonical factors while deferring their trailing updates. One actual
GEMM-backed trailing update restores the full Gaussian residual between consecutive panels.
The symbolic block count is constrained by the exact ceiling formula.

## Main results

* `NLAlib.Computation.BlockedLU.exec_body`: successful initialization and every blocked step.
-/

@[expose] public section

namespace NLAlib.Computation.BlockedLU

open Builder

variable {P ι : Type} [DecidableEq P]

private theorem exec_trailing (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P)
    (base : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n start width : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (S L U : ℕ) (lo uo : IExp ℕ)
    (hsw : start.eval + width.eval ≤ n.eval) (hSL : S ≠ L) (hSU : S ≠ U)
    (hs : State base p A S L U lo.eval uo.eval (start.eval + width.eval)
      (luPanelState A start.eval (start.eval + width.eval) (start.eval + width.eval)) st.store) :
    ∃ out, exec I (trailingSchurUpdate p n start width L U S lo uo 0).run st = some out ∧
      State base p A S L U lo.eval uo.eval (start.eval + width.eval)
        (gaussState A (start.eval + width.eval)) out.store := by
  obtain ⟨F, G, hM, hF, hG, hFp, hGp⟩ := hs.values
  obtain ⟨out, W, M', hW, hex, hw, hM', hin, hout⟩ := exec_trailingSchurUpdate I hI hc p
    st n start width L U S lo uo 0 F G _ hsw hF hG hM
  have heq : M' = gaussState A (start.eval + width.eval) :=
    eq_gaussState_of_panel_products A F G M' start.eval width.eval hsw hFp hGp hin hout
  refine ⟨out, hex, hs.frame.write_residual hw hW, F, G, ?_, ?_, ?_, hFp, hGp⟩
  · simpa only [IExp.eval_zero, heq] using hM'
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hSL.symm)]
    exact hF i j
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hSU.symm)]
    exact hG i j

private theorem exec_block (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P)
    (base : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n start width : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (S L U : ℕ) (lo uo : IExp ℕ)
    (hsw : start.eval + width.eval ≤ n.eval)
    (hp : ∀ r : Fin n.eval, gaussState A r.val r r ≠ 0)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U)
    (hs : State base p A S L U lo.eval uo.eval start.eval (gaussState A start.eval) st.store) :
    ∃ out, exec I (do
      luPanel p n start width S L U lo uo
      trailingSchurUpdate p n start width L U S lo uo 0).run st = some out ∧
      State base p A S L U lo.eval uo.eval (start.eval + width.eval)
        (gaussState A (start.eval + width.eval)) out.store := by
  obtain ⟨panel, hex₁, hpanel⟩ := exec_panel I hI hc p base st n start width A S L U lo uo
    hsw hp hSL hSU hLU hs
  obtain ⟨out, hex₂, hout⟩ := exec_trailing I hI hc p base panel n start width A S L U lo uo
    hsw hSL hSU hpanel
  refine ⟨out, ?_, hout⟩
  rw [exec_run_bind I (b := luPanel p n start width S L U lo uo) (fun _ => rfl),
    hex₁, Option.bind_some]
  exact hex₂

private theorem exec_blockLoop (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P)
    (base : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n b q : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (S L U : ℕ) (lo uo : IExp ℕ)
    (hb : 0 < b.eval) (hq : q.eval = (n.eval + b.eval - 1) / b.eval)
    (hp : ∀ r : Fin n.eval, gaussState A r.val r r ≠ 0)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U)
    (hs : State base p A S L U lo.eval uo.eval 0 A st.store) :
    ∃ out, exec I (forRange q fun block => do
      let start := b * IExp.var block
      let width := b - (b - (n - start))
      luPanel p n start width S L U lo uo
      trailingSchurUpdate p n start width L U S lo uo 0).run st = some out ∧
      State base p A S L U lo.eval uo.eval n.eval (gaussState A n.eval) out.store := by
  have hceil : n.eval ⌈/⌉ b.eval = q.eval := by
    rw [Nat.ceilDiv_eq_add_pred_div, hq]
  let Inv := fun t (σ : St P ℝ (OpCount P ι)) =>
    State base p A S L U lo.eval uo.eval (min (b.eval * t) n.eval)
      (gaussState A (min (b.eval * t) n.eval)) σ.store
  have hzero : Inv 0 st := by
    simpa only [Inv, Nat.mul_zero, zero_min, gaussState_zero] using hs
  obtain ⟨out, hex, hout⟩ := exists_exec_loop_eq_some_of_forall I (n := q)
    (body := fun block => (do
      let start := b * IExp.var block
      let width := b - (b - (n - start))
      luPanel p n start width S L U lo uo
      trailingSchurUpdate p n start width L U S lo uo 0).run) Inv hzero (by
      intro t ht σ hσ
      let start := b * IExp.var t
      let width := b - (b - (n - start))
      have hstart : b.eval * t < n.eval := by
        by_contra h
        have hN : n.eval ≤ b.eval * t := Nat.le_of_not_gt h
        have hqt : n.eval ⌈/⌉ b.eval ≤ t := (ceilDiv_le_iff_le_mul hb).mpr hN
        rw [hceil] at hqt
        omega
      have hend : start.eval + width.eval = min (b.eval * (t + 1)) n.eval := by
        simp only [start, width, IExp.eval_mul, IExp.eval_var, IExp.eval_sub, Nat.mul_succ]
        omega
      have hwidth : start.eval + width.eval ≤ n.eval := by rw [hend]; exact min_le_right _ _
      have hσ' : State base p A S L U lo.eval uo.eval start.eval
          (gaussState A start.eval) σ.store := by
        simpa only [Inv, start, IExp.eval_mul, IExp.eval_var, min_eq_left hstart.le] using hσ
      obtain ⟨out, he, ho⟩ := exec_block I hI hc p base σ n start width A S L U lo uo
        hwidth hp hSL hSU hLU hσ'
      exact ⟨out, he, by simpa only [Inv, hend] using ho⟩)
  refine ⟨out, ?_, ?_⟩
  · change exec I (.seq (.loop q _) .skip) st = some out
    rw [exec_seq_skip]
    exact hex
  · have hN : n.eval ≤ b.eval * q.eval := (ceilDiv_le_iff_le_mul hb).mp hceil.le
    simpa only [Inv, min_eq_right hN] using hout

/-- The complete blocked body executes only empty loops when both the matrix dimension
and outer block count are zero, with no valid-handle or scalar-semantics premise. -/
theorem exec_body_of_zero {K C : Type} [AddMonoid C] (I : Interp P ι K C) (p : P)
    (st : St P K C) (n b q : IExp ℕ) (A S L U : ℕ) (ao lo uo : IExp ℕ)
    (hn : n.eval = 0) (hb : 0 < b.eval)
    (hq : q.eval = (n.eval + b.eval - 1) / b.eval) : exec I (do
      copyv p A ao S 0 (n * n)
      forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)
      forRange q fun block => do
        let start := b * IExp.var block
        let width := b - (b - (n - start))
        luPanel p n start width S L U lo uo
        trailingSchurUpdate p n start width L U S lo uo 0).run st = some st := by
  have hq0 : q.eval = 0 := by
    rw [hq, hn, zero_add]
    exact Nat.div_eq_of_lt (Nat.sub_lt hb zero_lt_one)
  change exec I (.seq (.named "copy" _ (.seq (.loop (n * n) _) .skip))
    (.seq (.loop (n * n) _) (.seq (.loop (n * n) _) (.seq (.loop q _) .skip)))) st = some st
  simp only [exec_seq, exec_named, exec_loop, IExp.eval_mul, hn, hq0, zero_mul,
    List.range_zero, List.foldlM_nil, Option.pure_def, Option.bind_some, exec_skip]

/-- Copy the input before clearing either output, then execute every panel and one BLAS3
trailing update per block. Nonzero original canonical pivots suffice for actual success.
The input may overlap either output. Empty dimensions require no valid input/output handles;
the positive block size and exact symbolic ceiling block count determine the loop controls. -/
theorem exec_body (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n b q : IExp ℕ)
    (A L U : ℕ) (ao lo uo : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hb : 0 < b.eval) (hq : q.eval = (n.eval + b.eval - 1) / b.eval)
    (hp : ∀ r : Fin n.eval, gaussState M r.val r r ≠ 0) (hM : Holds initial p A ao.eval M)
    (hL : Writable initial p L lo.eval (n.eval * n.eval))
    (hU : Writable initial p U uo.eval (n.eval * n.eval)) (hLU : L ≠ U)
    (hst : st.store = initial.push (p, Array.replicate (n.eval * n.eval) none)) :
    ∃ out, exec I (do
      copyv p A ao initial.size 0 (n * n)
      forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)
      forRange q fun block => do
        let start := b * IExp.var block
        let width := b - (b - (n - start))
        luPanel p n start width initial.size L U lo uo
        trailingSchurUpdate p n start width L U initial.size lo uo 0).run st = some out ∧
      State st.store p M initial.size L U lo.eval uo.eval n.eval (gaussState M n.eval)
        out.store := by
  by_cases hn : n.eval = 0
  · exact ⟨st, exec_body_of_zero I p st n b q A initial.size L U ao lo uo hn hb hq,
      State.empty st.store p M (gaussState M n.eval) initial.size L U lo.eval uo.eval hn⟩
  have hN : 0 < n.eval := Nat.pos_of_ne_zero hn
  have hAb := Store.lt_size_of_read_eq_some (hM ⟨0, hN⟩ ⟨0, hN⟩)
  have hLb := hL.lt_size (Nat.mul_pos hN hN)
  have hUb := hU.lt_size (Nat.mul_pos hN hN)
  have hMp : Holds st.store p A ao.eval M := fun i j => by
    rw [hst, Store.read_push_of_lt hAb]; exact hM i j
  have hS : Writable st.store p initial.size 0 (n.eval * n.eval) := by
    rw [hst]
    exact writable_of_shape_eq rfl (Store.getElem?_shape_push_size initial p _) (by omega)
  obtain ⟨ready, hex₁, hshape, hframe, hS₁, hL₁, hU₁⟩ := exec_luInitialize I hI hc p st n
    A initial.size L U ao lo uo M hMp hS (hst ▸ hL.push _) (hst ▸ hU.push _)
    (Nat.ne_of_lt hAb) (Nat.ne_of_gt hLb) (Nat.ne_of_gt hUb) hLU
  have hf : PLU.Frame st.store n.eval initial.size L U initial.size lo.eval uo.eval 0
      ready.store := by
    refine ⟨hshape, ?_⟩
    intro tag buf idx hbS hbL hbU _
    exact hframe tag buf idx (by omega) hbL hbU
  have hzero := State.zero hf hS₁ hL₁ hU₁
  obtain ⟨out, hex₂, hout⟩ := exec_blockLoop I hI hc p st.store ready n b q M initial.size L U
    lo uo hb hq hp (Nat.ne_of_gt hLb) (Nat.ne_of_gt hUb) hLU hzero
  refine ⟨out, ?_, hout⟩
  have hcomp : ExecutionComposable I (do
      copyv p A ao initial.size 0 (n * n)
      forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)) :=
    (executionComposable_single I (fun _ => rfl)).bind
      ((executionComposable_single I (fun _ => rfl)).bind
        (executionComposable_single I (fun _ => rfl)))
  change exec I ((do
    copyv p A ao initial.size 0 (n * n)
    forRange (n * n) fun i => ins (.lit p ⟨L, lo + IExp.var i⟩ 0)
    forRange (n * n) fun i => ins (.lit p ⟨U, uo + IExp.var i⟩ 0)) >>= fun _ =>
    forRange q fun block => do
      let start := b * IExp.var block
      let width := b - (b - (n - start))
      luPanel p n start width initial.size L U lo uo
      trailingSchurUpdate p n start width L U initial.size lo uo 0).run st = some out
  rw [hcomp, hex₁, Option.bind_some]
  exact hex₂

end NLAlib.Computation.BlockedLU
