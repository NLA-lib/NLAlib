/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLURoundingSteps
public import NLAlib.Matrix.Computation.PLU

/-!
# Full rounded partial-pivoted LU execution

The unchanged full driver initializes its scoped residual and factors, then executes every
actual pivoted iteration. The empty-dimensional path performs no source or output reads.
The final stored prefix carries the actual factors, index log and conditional backward error.

## Main results

* `NLAlib.Computation.PLURounding.exec_body`: successful actual full driver body.
-/

@[expose] public section

namespace NLAlib.Computation.PLURounding

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
    (A L U H : ℕ) (ao lo uo ho : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : HoldsDecoded initial dec tag A ao.eval M)
    (hL : Writable initial tag L lo.eval (n.eval * n.eval))
    (hU : Writable initial tag U uo.eval (n.eval * n.eval))
    (hH : Writable initial tag H ho.eval n.eval) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (hstore : st.store = initial.push (tag, Array.replicate (n.eval * n.eval) none)) :
    ∃ out, exec I (do
      copyv tag A ao initial.size 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        partialPivot tag n (.var k) initial.size 0 ⟨H, ho + IExp.var k⟩
        bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
          swapRows tag n n L lo (.var k) (.var selected)
        luColumnTotal tag n (.var k) initial.size L U 0 lo uo
        schurStepTotal tag n initial.size 0 (.var k)).run st = some out ∧
      State dec (u tag) st.store tag M initial.size L U H lo.eval uo.eval ho.eval n.eval
        out.store := by
  by_cases hn : n.eval = 0
  · exact ⟨st, PLU.exec_emptyBody I tag st n A initial.size L U H ao lo uo ho hn,
      State.empty dec (u tag) st.store tag M initial.size L U H lo.eval uo.eval ho.eval hn⟩
  have hN : 0 < n.eval := Nat.pos_of_ne_zero hn
  have hAb : A < initial.size := by
    obtain ⟨w, hw, -⟩ := hM ⟨0, hN⟩ ⟨0, hN⟩
    exact Store.lt_size_of_read_eq_some hw
  have hLb := hL.lt_size (Nat.mul_pos hN hN)
  have hUb := hU.lt_size (Nat.mul_pos hN hN)
  have hHb := hH.lt_size hN
  have hMp : HoldsDecoded st.store dec tag A ao.eval M :=
    hstore ▸ hM.push (tag, Array.replicate (n.eval * n.eval) none)
  have hS : Writable st.store tag initial.size 0 (n.eval * n.eval) := by
    rw [hstore]
    exact writable_of_shape_eq rfl (Store.getElem?_shape_push_size initial tag
      (n.eval * n.eval)) (by omega)
  have hLp : Writable st.store tag L lo.eval (n.eval * n.eval) := hstore ▸ hL.push _
  have hUp : Writable st.store tag U uo.eval (n.eval * n.eval) := hstore ▸ hU.push _
  have hHp : Writable st.store tag H ho.eval n.eval := hstore ▸ hH.push _
  obtain ⟨ready, hr₁, hshape, hframe, hS₁, hF₁, hG₁⟩ := exec_initialize I h tag st n
    A initial.size L U ao lo uo M hMp hS hLp hUp (Nat.ne_of_lt hAb)
    (Nat.ne_of_gt hLb) (Nat.ne_of_gt hUb) hLU
  have hf : PLU.Frame st.store n.eval initial.size L U H lo.eval uo.eval ho.eval ready.store := by
    refine ⟨hshape, ?_⟩
    intro q b i hbS hbL hbU _
    exact hframe q b i hbS hbL hbU
  have h0 := State.zero (u := u tag) hf hS₁ hF₁ hG₁
  obtain ⟨out, hr₂, hs⟩ := exists_exec_loop_eq_some_of_forall I
    (n := n) (fun k σ => State dec (u tag) st.store tag M initial.size L U H lo.eval uo.eval
      ho.eval k σ.store) h0 (fun k hk σ hσ => exec_iteration I h n hi tag st.store M
      initial.size L U H lo uo ho hHp (Nat.ne_of_gt hLb) (Nat.ne_of_gt hUb)
      (Nat.ne_of_gt hHb) hLU hLH hUH k hk σ hσ)
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
      partialPivot tag n (.var k) initial.size 0 ⟨H, ho + IExp.var k⟩
      bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
        swapRows tag n n L lo (.var k) (.var selected)
      luColumnTotal tag n (.var k) initial.size L U 0 lo uo
      schurStepTotal tag n initial.size 0 (.var k)).run st = some out
  rw [hcomp, hr₁, Option.bind_some]
  change exec I (.seq (.loop n _) .skip) ready = some out
  rw [exec_seq_skip]
  exact hr₂

end NLAlib.Computation.PLURounding
