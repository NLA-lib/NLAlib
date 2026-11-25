/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQRoundingSteps
public import NLAlib.Matrix.Computation.PLUQEmpty

/-!
# Full rounded complete-pivoted LU execution

The unchanged full driver initializes its scoped residual and factors, then executes every
actual pivoted iteration. The empty-dimensional path performs no source or output reads.
The final stored prefix carries the actual factors, index log and conditional backward error.

## Main results

* `NLAlib.Computation.PLUQRounding.exec_body`: successful actual full driver body.
-/

@[expose] public section

namespace NLAlib.Computation.PLUQRounding

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The full actual rounded driver body succeeds from decoded input and writable factors/log.
The scalar model has every result in range and exact bounded index controls; no pivot or
roundoff upper-bound premise is required. Zero-dimensional matrices perform no reads.
[Higham2002, §9.3; GolubVanLoan2013, §3.4]. -/
theorem exec_body {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (initial : Store P K) (st : St P K C)
    (A L U Hr Hc : ℕ) (ao lo uo hro hco : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : HoldsDecoded initial dec tag A ao.eval M)
    (hL : Writable initial tag L lo.eval (n.eval * n.eval))
    (hU : Writable initial tag U uo.eval (n.eval * n.eval))
    (hR : Writable initial tag Hr hro.eval n.eval)
    (hC : Writable initial tag Hc hco.eval n.eval)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc)
    (hstore : st.store = initial.push (tag, Array.replicate (n.eval * n.eval) none)) :
    ∃ out, exec I (do
      copyv tag A ao initial.size 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        completePivotChoice tag n (.var k) initial.size 0
          ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
        bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
          swapRows tag n n initial.size 0 (.var k) (.var row)
          swapRows tag n n L lo (.var k) (.var row)
        bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
          swapColumns tag n n initial.size 0 (.var k) (.var col)
          swapColumns tag n n U uo (.var k) (.var col)
        luColumnTotal tag n (.var k) initial.size L U 0 lo uo
        schurStepTotal tag n initial.size 0 (.var k)).run st = some out ∧
      State dec (u tag) st.store tag M initial.size L U Hr Hc
        lo.eval uo.eval hro.eval hco.eval n.eval
        out.store := by
  by_cases hn : n.eval = 0
  · exact ⟨st, PLUQ.exec_emptyBody I tag st n A initial.size L U Hr Hc ao lo uo hro hco hn,
      State.empty dec (u tag) st.store tag M initial.size L U Hr Hc
        lo.eval uo.eval hro.eval hco.eval hn⟩
  have hN : 0 < n.eval := Nat.pos_of_ne_zero hn
  have hAb : A < initial.size := by
    obtain ⟨w, hw, -⟩ := hM ⟨0, hN⟩ ⟨0, hN⟩
    exact Store.lt_size_of_read_eq_some hw
  have hLb := hL.lt_size (Nat.mul_pos hN hN)
  have hUb := hU.lt_size (Nat.mul_pos hN hN)
  have hRb := hR.lt_size hN
  have hCb := hC.lt_size hN
  have hMp : HoldsDecoded st.store dec tag A ao.eval M :=
    hstore ▸ hM.push (tag, Array.replicate (n.eval * n.eval) none)
  have hS : Writable st.store tag initial.size 0 (n.eval * n.eval) := by
    rw [hstore]
    exact writable_of_shape_eq rfl (Store.getElem?_shape_push_size initial tag
      (n.eval * n.eval)) (by omega)
  have hLp : Writable st.store tag L lo.eval (n.eval * n.eval) := hstore ▸ hL.push _
  have hUp : Writable st.store tag U uo.eval (n.eval * n.eval) := hstore ▸ hU.push _
  have hRp : Writable st.store tag Hr hro.eval n.eval := hstore ▸ hR.push _
  have hCp : Writable st.store tag Hc hco.eval n.eval := hstore ▸ hC.push _
  obtain ⟨ready, hr₁, hshape, hframe, hS₁, hF₁, hG₁⟩ := PLURounding.exec_initialize I h tag st n
    A initial.size L U ao lo uo M hMp hS hLp hUp (Nat.ne_of_lt hAb)
    (Nat.ne_of_gt hLb) (Nat.ne_of_gt hUb) hLU
  have hf : PLUQ.Frame st.store n.eval initial.size L U Hr Hc
      lo.eval uo.eval hro.eval hco.eval ready.store := by
    refine ⟨hshape, ?_⟩
    intro q b i hbS hbL hbU _ _
    exact hframe q b i hbS hbL hbU
  have h0 := State.zero (u := u tag) hf hS₁ hF₁ hG₁
  obtain ⟨out, hr₂, hs⟩ := exists_exec_loop_eq_some_of_forall I
    (n := n) (fun k σ => State dec (u tag) st.store tag M initial.size L U Hr Hc lo.eval uo.eval
      hro.eval hco.eval k σ.store) h0 (fun k hk σ hσ => exec_iteration I h n hi tag st.store M
      initial.size L U Hr Hc lo uo hro hco hRp hCp (Nat.ne_of_gt hLb) (Nat.ne_of_gt hUb)
      (Nat.ne_of_gt hRb) (Nat.ne_of_gt hCb) hLU hLR hLC hUR hUC hRC k hk σ hσ)
  refine ⟨out, ?_, hs⟩
  have hcomp : ExecutionComposable I (do
      copyv tag A ao initial.size 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)) :=
    (executionComposable_single I (fun _ => rfl)).bind
      ((executionComposable_single I (fun _ => rfl)).bind
        (executionComposable_single I (fun _ => rfl)))
  change exec I ((do
    copyv tag A ao initial.size 0 (n * n)
    forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
    forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)) >>= fun _ =>
    forRange n fun k => do
      completePivotChoice tag n (.var k) initial.size 0
        ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
      bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
        swapRows tag n n initial.size 0 (.var k) (.var row)
        swapRows tag n n L lo (.var k) (.var row)
      bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
        swapColumns tag n n initial.size 0 (.var k) (.var col)
        swapColumns tag n n U uo (.var k) (.var col)
      luColumnTotal tag n (.var k) initial.size L U 0 lo uo
      schurStepTotal tag n initial.size 0 (.var k)).run st = some out
  rw [hcomp, hr₁, Option.bind_some]
  change exec I (.seq (.loop n _) .skip) ready = some out
  rw [exec_seq_skip]
  exact hr₂

end NLAlib.Computation.PLUQRounding
