/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.RowSwap
public import NLAlib.Matrix.Factorizations.LUPivoting
public import NLAlib.Computation.Contract

/-!
# Applying stored pivot logs to vectors

The actual bounded binder consumes each recorded absolute position and exchanges two vector
rows using the rectangular row routine. Forward order applies the current-to-original swap
permutation; reverse order applies its inverse. The vector words have arbitrary carrier.

## Main definitions

* `NLAlib.Computation.applyPivotLog`: forward pivot-log exchanges.
* `NLAlib.Computation.applyPivotLogReverse`: inverse exchanges in reverse execution order.

## Main results

* `NLAlib.Computation.exec_applyPivotLog`: actual forward permutation and one vector write.
* `NLAlib.Computation.exec_applyPivotLogReverse`: actual inverse permutation and one vector write.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Apply stored absolute pivot indices in forward order to a vector, using actual bounded
index conversion and one-row exchanges. The log is retained and row-exchange scratch is scoped. -/
def applyPivotLog {P ι VB VI : Type} (tag : P) (n : IExp VI) (log : VB)
    (lo : IExp VI) (xb : VB) (xo : IExp VI) : Builder P ι VB VI Unit := scope do
  forRange n fun k => bindIdx tag ⟨log, lo + .var k⟩ n fun selected =>
    swapRows tag n 1 xb xo (.var k) (.var selected)

/-- Apply the inverse permutation by consuming the stored swaps in reverse order. For an
empty vector the loop performs no log or vector reads, even for invalid buffer handles. -/
def applyPivotLogReverse {P ι VB VI : Type} (tag : P) (n : IExp VI) (log : VB)
    (lo : IExp VI) (xb : VB) (xo : IExp VI) : Builder P ι VB VI Unit := scope do
  forRange n fun t => bindIdx tag ⟨log, lo + (n - 1 - .var t)⟩ n fun selected =>
    swapRows tag n 1 xb xo (n - 1 - .var t) (.var selected)

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Forward log exchanges compose after releasing each row exchange's scratch. -/
theorem executionComposable_applyPivotLog (I : Interp P ι K C) (tag : P) (n : IExp ℕ)
    (log : ℕ) (lo : IExp ℕ) (xb : ℕ) (xo : IExp ℕ) :
    ExecutionComposable I (applyPivotLog tag n log lo xb xo) :=
  executionComposable_single I (fun _ => rfl)

/-- Reverse log exchanges compose after releasing each row exchange's scratch. -/
theorem executionComposable_applyPivotLogReverse (I : Interp P ι K C) (tag : P) (n : IExp ℕ)
    (log : ℕ) (lo : IExp ℕ) (xb : ℕ) (xo : IExp ℕ) :
    ExecutionComposable I (applyPivotLogReverse tag n log lo xb xo) :=
  executionComposable_single I (fun _ => rfl)

namespace PivotLogPermutation

private theorem read_of_write {N : ℕ} {before after : Store P K} {tag : P}
    {xb off : ℕ} {x : Fin N → K}
    (hw : before.writeBlock tag xb off (Array.ofFn x) = some after) (i : Fin N) :
    after.read tag xb (off + i) = some (x i) := by
  have hr := Store.read_of_writeBlock_eq_some_of_lt hw (j := i.val)
    (by rw [Array.size_ofFn]; exact i.isLt)
  rw [Array.getElem?_eq_getElem (by rw [Array.size_ofFn]; exact i.isLt),
    Array.getElem_ofFn] at hr
  exact hr

private theorem write_self {N : ℕ} (st : Store P K) (tag : P) (xb off : ℕ)
    (x : Fin N → K) (hx : ∀ i : Fin N, st.read tag xb (off + i) = some (x i)) :
    st.writeBlock tag xb off (Array.ofFn x) = some st :=
  Store.writeBlock_eq_some_of_read rfl (fun t ht => by
    simpa only [Array.getElem?_ofFn, show t < N from by simpa using ht, ↓reduceDIte] using
      hx ⟨t, by simpa using ht⟩) (fun _ _ _ _ => rfl)

private theorem exec_swapVector {dec : P → K → ℝ}
    (I : Interp P ι K C) (tag : P) (st : St P K C) (n k : IExp ℕ)
    (hi : IsIndexExactSem dec n.eval I.sem) (index : Cell ℕ ℕ) (w : K)
    (r : Fin n.eval) (hk : k.eval < n.eval)
    (hread : st.store.read tag index.buf index.idx.eval = some w) (hd : dec tag w = r.val)
    (xb : ℕ) (xo : IExp ℕ) (x : Fin n.eval → K)
    (hx : ∀ i : Fin n.eval, st.store.read tag xb (xo.eval + i) = some (x i)) :
    ∃ out, exec I (bindIdx tag index n fun selected =>
      swapRows tag n 1 xb xo k (.var selected)).run st = some out ∧
      st.store.writeBlock tag xb xo.eval
        (Array.ofFn (fun i => x (Equiv.swap ⟨k.eval, hk⟩ r i))) = some out.store := by
  have hto : I.sem.toNat tag w = some r.val := by rw [hi.toNat tag w, hd]; simp
  let ready : St P K C := { st with cnt := st.cnt + I.charge (.toNat tag) }
  obtain ⟨out, W, he, hw, hX⟩ := exec_swapRows I tag ready n 1 xb xo k (.var r.val)
    (fun i _ => x i) hk r.isLt (fun i j => by
      have hj : j.val = 0 := by have := j.isLt; simp only [IExp.eval_one] at this; omega
      simpa only [hj, mul_zero, Nat.add_zero] using hx i)
  refine ⟨out, ?_, ?_⟩
  swap
  · apply Store.writeBlock_eq_some_of_read (Store.shape_of_writeBlock_eq_some hw)
    · intro i hi
      have hin : i < n.eval := by simpa only [Array.size_ofFn] using hi
      have hh := hX ⟨i, hin⟩ ⟨0, by simp [IExp.eval]⟩
      change out.store.read tag xb (xo.eval + i + n.eval * 0) =
        some (x (Equiv.swap ⟨k.eval, hk⟩ r ⟨i, hin⟩)) at hh
      rw [mul_zero, Nat.add_zero] at hh
      rw [Array.getElem?_eq_getElem hi, Array.getElem_ofFn]
      exact hh
    · intro q b i hout
      apply Store.read_of_writeBlock_eq_some_of_ne hw
      have hsize : (Array.ofFn W).size = n.eval := by
        rw [Array.size_ofFn]; simp only [IExp.eval_one, Nat.mul_one]
      rw [hsize]
      simpa only [Array.size_ofFn] using hout
  change exec I (.seq (.bindIdx tag index n _) .skip) st = some out
  rw [exec_seq_skip, exec_bindIdx_of_read I hread hto r.isLt.le]
  exact he

end PivotLogPermutation

/-- A readable stored log and vector suffice for actual forward permutation under exact
bounded index conversion/literals. Vector words are copied exactly for every carrier and
charge monoid. Only one full vector block changes; empty inputs need no valid handles. -/
theorem exec_applyPivotLog {dec : P → K → ℝ} (I : Interp P ι K C)
    (tag : P) (n : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem)
    (st : St P K C) (log : ℕ) (lo : IExp ℕ) (xb : ℕ) (xo : IExp ℕ)
    (p : Fin n.eval → Fin n.eval) (x : Fin n.eval → K)
    (hp : ReadsDecoded st.store dec tag log lo.eval (fun i => (p i).val))
    (hx : ∀ i : Fin n.eval, st.store.read tag xb (xo.eval + i) = some (x i))
    (hLX : 0 < n.eval → log ≠ xb) :
    ∃ out, exec I (applyPivotLog tag n log lo xb xo).run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn (x ∘ luPivotPermutation p n.eval)) =
        some out.store := by
  let R := fun k (s : St P K C) => st.store.writeBlock tag xb xo.eval
    (Array.ofFn (x ∘ luPivotPermutation p k)) = some s.store
  have h0 : R 0 st := by
    simpa only [R, luPivotPermutation_zero, Equiv.refl_apply, Function.comp_def] using
      PivotLogPermutation.write_self st.store tag xb xo.eval x hx
  obtain ⟨out, he, hs⟩ := exists_exec_loop_eq_some_of_forall I (n := n) R h0 (by
    intro k hk s hs
    let r : Fin n.eval := ⟨k, hk⟩
    obtain ⟨w, hw, hd⟩ := hp r
    have hw' : s.store.read tag log (lo + .var k).eval = some w := by
      rw [Store.read_of_writeBlock_eq_some_of_ne hs (Or.inl (hLX (by omega)))]
      simpa only [IExp.eval_add, IExp.eval_var] using hw
    obtain ⟨out, he, hwout⟩ := PivotLogPermutation.exec_swapVector I tag s n (.var k)
      hi ⟨log, lo + .var k⟩ w (p r) hk hw' hd xb xo (x ∘ luPivotPermutation p k)
      (PivotLogPermutation.read_of_write hs)
    refine ⟨out, he, ?_⟩
    have hperm : (fun i => (x ∘ luPivotPermutation p k) (Equiv.swap r (p r) i)) =
        x ∘ luPivotPermutation p (k + 1) := by rw [luPivotPermutation_succ p k hk]; rfl
    have hnet := Store.writeBlock_writeBlock_self hs hwout (by simp)
    change st.store.writeBlock tag xb xo.eval
      (Array.ofFn (fun i => (x ∘ luPivotPermutation p k) (Equiv.swap r (p r) i))) =
        some out.store at hnet
    rw [hperm] at hnet
    exact hnet)
  refine ⟨out, ?_, hs⟩
  change exec I (.seq (.seq (.loop n _) .skip) .skip) st = some out
  rw [exec_seq_skip, exec_seq_skip]
  exact he

/-- Reversing the actual stored exchanges applies the inverse decoded permutation. Success
requires the same initialized data and exact bounded index controls as the forward pass.
No arithmetic model, nonzero data or nonempty-dimension premise is needed. -/
theorem exec_applyPivotLogReverse {dec : P → K → ℝ} (I : Interp P ι K C)
    (tag : P) (n : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem)
    (st : St P K C) (log : ℕ) (lo : IExp ℕ) (xb : ℕ) (xo : IExp ℕ)
    (p : Fin n.eval → Fin n.eval) (x : Fin n.eval → K)
    (hp : ReadsDecoded st.store dec tag log lo.eval (fun i => (p i).val))
    (hx : ∀ i : Fin n.eval, st.store.read tag xb (xo.eval + i) = some (x i))
    (hLX : 0 < n.eval → log ≠ xb) :
    ∃ out, exec I (applyPivotLogReverse tag n log lo xb xo).run st = some out ∧
      st.store.writeBlock tag xb xo.eval
        (Array.ofFn (x ∘ (luPivotPermutation p n.eval).symm)) = some out.store := by
  let τ := luPivotPermutation p n.eval
  let f := fun t i => x (τ.symm (luPivotPermutation p (n.eval - t) i))
  let R := fun t (s : St P K C) =>
    st.store.writeBlock tag xb xo.eval (Array.ofFn (f t)) = some s.store
  have h0 : R 0 st := by
    simpa only [R, f, Nat.sub_zero, τ, Equiv.symm_apply_apply] using
      PivotLogPermutation.write_self st.store tag xb xo.eval x hx
  obtain ⟨out, he, hs⟩ := exists_exec_loop_eq_some_of_forall I (n := n) R h0 (by
    intro t ht s hs
    let k := n.eval - 1 - t
    have hk : k < n.eval := by dsimp only [k]; omega
    let r : Fin n.eval := ⟨k, hk⟩
    obtain ⟨w, hw, hd⟩ := hp r
    have hw' : s.store.read tag log (lo + (n - 1 - .var t)).eval = some w := by
      rw [Store.read_of_writeBlock_eq_some_of_ne hs (Or.inl (hLX (by omega)))]
      simpa only [IExp.eval_add, IExp.eval_sub, IExp.eval_one, IExp.eval_var, k, r] using hw
    obtain ⟨out, he, hwout⟩ := PivotLogPermutation.exec_swapVector I tag s n (n - 1 - .var t)
      hi ⟨log, lo + (n - 1 - .var t)⟩ w (p r) hk hw' hd xb xo (f t)
      (PivotLogPermutation.read_of_write hs)
    have hfunc : (fun i => f t (Equiv.swap r (p r) i)) = f (t + 1) := by
      funext i
      have heq : n.eval - t = k + 1 := by dsimp only [k]; omega
      have heq' : n.eval - (t + 1) = k := by dsimp only [k]; omega
      simp only [f, heq, luPivotPermutation_succ p k hk, Equiv.trans_apply,
        Equiv.swap_apply_self, heq', r]
    refine ⟨out, he, ?_⟩
    have hnet := Store.writeBlock_writeBlock_self hs hwout (by simp)
    change st.store.writeBlock tag xb xo.eval
      (Array.ofFn (fun i => f t (Equiv.swap r (p r) i))) = some out.store at hnet
    rw [hfunc] at hnet
    exact hnet)
  refine ⟨out, ?_, ?_⟩
  · change exec I (.seq (.seq (.loop n _) .skip) .skip) st = some out
    rw [exec_seq_skip, exec_seq_skip]; exact he
  · simpa only [R, f, Nat.sub_self, luPivotPermutation_zero, Equiv.refl_apply,
      Function.comp_def, τ] using hs

end NLAlib.Computation
