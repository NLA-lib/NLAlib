/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.MatrixKernels
public import NLAlib.Computation.MatrixStorage
public import NLAlib.Computation.ScalarFrames

/-!
# Stored block Schur update using GEMM

Packed factors of a completed panel update a packed trailing block by a single actual GEMM,
followed by subtraction. The matrix product is scoped and computed before the destination
changes, so either factor may overlap the destination. A panel of width zero skips the
update. This is the arithmetic core of a blocked factorization.

## Main results

* `NLAlib.Computation.exec_blockSchurUpdate`: exact execution and complete trailing-block frame.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Update a packed trailing block `C ← C - A*B` from packed panel factors of dimensions
`m × r` and `r × n`. The GEMM product is scoped and computed before any destination write.
The expression `r - (r - 1)` executes the body once for positive panel width and skips it at
width zero, without a scalar comparison. [GolubVanLoan2013, §3.6]. -/
def blockSchurUpdate {P ι VB VI : Type} (p : P) (m r n : IExp VI)
    (A B C : VB) (ao bo co : IExp VI) : Builder P ι VB VI Unit :=
  forRange (r - (r - 1)) fun _ => scope do
    let product ← alloc p (m * n)
    gemm p m r n A ao B bo product 0
    forRange (m * n) fun t =>
      ins (.bin p .sub ⟨C, co + IExp.var t⟩ ⟨C, co + IExp.var t⟩ ⟨product, IExp.var t⟩)

variable {𝕜 P ι : Type} [RCLike 𝕜] [DecidableEq P]

namespace BlockSchurUpdate

omit [RCLike 𝕜] in
private theorem exec_loop_one {D : Type} [AddMonoid D] (I : Interp P ι 𝕜 D)
    (st : St P 𝕜 D) (len : IExp ℕ) (body : ℕ → Stmt P ι ℕ ℕ) (hlen : len.eval = 1) :
    exec I (.loop len body) st = exec I (body 0) st := by
  rw [exec_loop, hlen]
  change (exec I (body 0) st).bind (fun s => some s) = exec I (body 0) st
  cases exec I (body 0) st <;> rfl

private theorem exec_subtractPacked {D : Type} [AddMonoid D]
    (I : Interp P ι 𝕜 D) (hI : I.sem = exactSem) (p : P) (st : St P 𝕜 D)
    (m n : IExp ℕ) (product C : ℕ) (co : IExp ℕ)
    (MC MP : Matrix (Fin m.eval) (Fin n.eval) 𝕜)
    (hC : Holds st.store p C co.eval MC) (hP : Holds st.store p product 0 MP)
    (hPC : 0 < m.eval * n.eval → product ≠ C) :
    ∃ out, exec I (forRange (m * n) fun t =>
      ins (.bin p .sub ⟨C, co + IExp.var t⟩ ⟨C, co + IExp.var t⟩ ⟨product, IExp.var t⟩)).run st =
        some out ∧ st.store.writeBlock p C co.eval (flatten (MC - MP)) = some out.store := by
  obtain ⟨out, W, hr, hw, hW⟩ := exists_exec_loop_writeBlock I (n := m * n) p C co.eval
    (fun t w => ∀ ht : t < (flatten (MC - MP)).size, w = (flatten (MC - MP))[t]) (by
      intro t ht ys σ hys _ hs
      have ht' : t < m.eval * n.eval := ht
      have hm : 0 < m.eval := by nlinarith
      let i : Fin m.eval := ⟨t % m.eval, Nat.mod_lt _ hm⟩
      let j : Fin n.eval := ⟨t / m.eval, (Nat.div_lt_iff_lt_mul hm).mpr (by simpa only
          [Nat.mul_comm] using ht')⟩
      have hidx : i.val + m.eval * j.val = t := Nat.mod_add_div t m.eval
      have hCr : σ.store.read p C (co.eval + t) = some (MC i j) := by
        rw [Store.read_of_writeBlock_eq_some_of_ne hs (Or.inr (Or.inr (by omega)))]
        simpa only [Nat.add_assoc, hidx] using hC i j
      have hPr : σ.store.read p product t = some (MP i j) := by
        rw [Store.read_of_writeBlock_eq_some_of_ne hs (Or.inl (hPC (by omega)))]
        simpa only [Nat.zero_add, hidx] using hP i j
      obtain ⟨len, hlen, hlt⟩ := hC.writable t ht'
      obtain ⟨store, hv, hrun, _, _, _⟩ := exec_scalar_bin I p σ .sub
        ⟨C, co + IExp.var t⟩ ⟨C, co + IExp.var t⟩ ⟨product, IExp.var t⟩
        (MC i j) (MP i j) (MC i j - MP i j) hCr hPr
        (by rw [hI]; rfl)
        ⟨len, by rw [Store.shape_of_writeBlock_eq_some hs]; exact hlen, hlt⟩
      refine ⟨_, MC i j - MP i j, hrun, hv, ?_⟩
      intro ht''
      have hval : (flatten (MC - MP))[t]? = some (MC i j - MP i j) := by
        simpa only [hidx, Matrix.sub_apply] using getElem?_flatten (MC - MP) i j
      exact (Array.getElem?_eq_some_iff.mp hval).2.symm)
  have heq : Array.ofFn W = flatten (MC - MP) := by
    have hsizeW : (Array.ofFn W).size = (m * n).eval := Array.size_ofFn
    apply Array.ext (hsizeW.trans (by rw [size_flatten]; rfl))
    intro t ht ht'
    simp only [Array.getElem_ofFn]
    exact hW ⟨t, by simpa only [Array.size_ofFn] using ht⟩ ht'
  refine ⟨out, ?_, heq ▸ hw⟩
  change exec I (.seq (.loop (m * n) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

private theorem exec_body (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (initial : Store P 𝕜) (st : St P 𝕜 (OpCount P ι)) (m r n : IExp ℕ)
    (A B C : ℕ) (ao bo co : IExp ℕ)
    (MA : Matrix (Fin m.eval) (Fin r.eval) 𝕜)
    (MB : Matrix (Fin r.eval) (Fin n.eval) 𝕜)
    (MC : Matrix (Fin m.eval) (Fin n.eval) 𝕜)
    (hr : 0 < r.eval) (hA : Holds initial p A ao.eval MA)
    (hB : Holds initial p B bo.eval MB) (hC : Holds initial p C co.eval MC)
    (hstore : st.store = initial.push (p, Array.replicate (m.eval * n.eval) none)) :
    ∃ out, exec I (do
      gemm p m r n A ao B bo initial.size 0
      forRange (m * n) fun t => ins (.bin p .sub ⟨C, co + IExp.var t⟩
        ⟨C, co + IExp.var t⟩ ⟨initial.size, IExp.var t⟩)).run st = some out ∧
      initial.writeBlock p C co.eval (flatten (MC - MA * MB)) = some out.store.pop := by
  have hAp : Holds st.store p A ao.eval MA := fun i j => by
    rw [hstore, Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hA i j))]
    exact hA i j
  have hBp : Holds st.store p B bo.eval MB := fun i j => by
    rw [hstore, Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hB i j))]
    exact hB i j
  have hCp : Holds st.store p C co.eval MC := fun i j => by
    rw [hstore, Store.read_push_of_lt (Store.lt_size_of_read_eq_some (hC i j))]
    exact hC i j
  have hsepA : initial.size = A → m.eval * n.eval ≤ ao.eval ∨
      ao.eval + m.eval * r.eval ≤ 0 := by
    intro he
    by_cases hm : 0 < m.eval
    · have hb := Store.lt_size_of_read_eq_some (hA ⟨0, hm⟩ ⟨0, hr⟩)
      omega
    · have hm0 : m.eval = 0 := by omega
      exact Or.inl (by simp only [hm0, zero_mul]; exact Nat.zero_le _)
  have hsepB : initial.size = B → m.eval * n.eval ≤ bo.eval ∨
      bo.eval + r.eval * n.eval ≤ 0 := by
    intro he
    by_cases hn : 0 < n.eval
    · have hb := Store.lt_size_of_read_eq_some (hB ⟨0, hr⟩ ⟨0, hn⟩)
      omega
    · have hn0 : n.eval = 0 := by omega
      exact Or.inl (by simp only [hn0, mul_zero]; exact Nat.zero_le _)
  have htmp : Writable st.store p initial.size 0 (flatten (MA * MB)).size := by
    rw [size_flatten, hstore]
    exact writable_of_shape_eq rfl
      (Store.getElem?_shape_push_size initial p (m.eval * n.eval)) (by omega)
  obtain ⟨prodStore, hprod⟩ := htmp.exists_writeBlock
  obtain ⟨computed, hexec, hcomputed, _, _, _, _, _, _⟩ := exec_gemm I hI hc p st m r n A ao B bo
    initial.size 0 MA MB hAp hBp
    (by simpa only [IExp.eval_zero, Nat.zero_add] using hsepA)
    (by simpa only [IExp.eval_zero, Nat.zero_add] using hsepB) prodStore hprod
  have hwrite : st.store.writeBlock p initial.size 0 (flatten (MA * MB)) =
      some computed.store := hcomputed.symm ▸ hprod
  have hCP : Holds computed.store p C co.eval MC := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hwrite
      (Or.inl (Nat.ne_of_lt (Store.lt_size_of_read_eq_some (hC i j))))]
    exact hCp i j
  have hProd : Holds computed.store p initial.size 0 (MA * MB) := fun i j => by
    simpa only [Nat.zero_add, Nat.add_assoc] using
      (Store.read_of_writeBlock_eq_some_of_lt hwrite
        (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)).trans
          (getElem?_flatten (MA * MB) i j)
  obtain ⟨out, hsub, hw⟩ := exec_subtractPacked I hI p computed m n initial.size C co MC (MA * MB)
    hCP hProd (fun hn => Nat.ne_of_gt (hC.writable.lt_size hn))
  have hpop : computed.store.pop = initial := by
    rw [Store.pop_of_writeBlock_top hwrite (by simp only [hstore, Array.size_push]; omega),
      hstore]
    exact Array.pop_push
  have hsize : computed.store.size = initial.size + 1 := by
    rw [Store.size_of_writeBlock_eq_some hwrite, hstore, Array.size_push]
  have hfinal := Store.writeBlock_pop_of_lt hw (fun hn => by
    have := hC.writable.lt_size (by simpa only [size_flatten] using hn)
    omega)
  refine ⟨out, ?_, hpop ▸ hfinal⟩
  rw [exec_run_bind I (b := gemm p m r n A ao B bo initial.size 0)
    (fun _ => rfl), hexec, Option.bind_some]
  exact hsub

end BlockSchurUpdate

/-- Exact GEMM-backed block Schur update succeeds on readable packed panel factors and trailing
block. Either panel factor may overlap the trailing block, because the product is completed
before subtraction begins. A zero-width panel performs no arithmetic; empty dimensions need
no valid handles beyond cells actually read by the factors. The only net write is the full
trailing block. [GolubVanLoan2013, §3.6]. -/
theorem exec_blockSchurUpdate (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (st : St P 𝕜 (OpCount P ι))
    (m r n : IExp ℕ) (A B C : ℕ) (ao bo co : IExp ℕ)
    (MA : Matrix (Fin m.eval) (Fin r.eval) 𝕜)
    (MB : Matrix (Fin r.eval) (Fin n.eval) 𝕜)
    (MC : Matrix (Fin m.eval) (Fin n.eval) 𝕜)
    (hA : Holds st.store p A ao.eval MA) (hB : Holds st.store p B bo.eval MB)
    (hC : Holds st.store p C co.eval MC) :
    ∃ out, exec I (blockSchurUpdate p m r n A B C ao bo co).run st = some out ∧
      st.store.writeBlock p C co.eval (flatten (MC - MA * MB)) = some out.store ∧
      Holds out.store p C co.eval (MC - MA * MB) := by
  have hrun : ∃ out, exec I (blockSchurUpdate p m r n A B C ao bo co).run st = some out ∧
      st.store.writeBlock p C co.eval (flatten (MC - MA * MB)) = some out.store := by
    by_cases hr : r.eval = 0
    · refine ⟨st, ?_, ?_⟩
      · change exec I (.seq (.loop (r - (r - 1)) _) .skip) st = some st
        simp only [exec_seq_skip, exec_loop, IExp.eval_sub, IExp.eval_one, hr,
          Nat.zero_sub, List.range_zero, List.foldlM_nil, Option.pure_def]
      · have hmul : MA * MB = 0 := by
          ext i j
          rw [Matrix.mul_apply]
          apply Finset.sum_eq_zero
          intro k _
          have := k.isLt
          omega
        rw [hmul, sub_zero]
        exact hC.writeBlock_self
    · obtain ⟨out, hexec, hw⟩ := exists_exec_alloc I p (m * n) (fun product => (do
        gemm p m r n A ao B bo product 0
        forRange (m * n) fun t => ins (.bin p .sub ⟨C, co + IExp.var t⟩
          ⟨C, co + IExp.var t⟩ ⟨product, IExp.var t⟩)).run) st
        (fun s => st.store.writeBlock p C co.eval (flatten (MC - MA * MB)) = some s)
        (fun σ hσ => BlockSchurUpdate.exec_body I hI hc p st.store σ m r n A B C ao bo co
          MA MB MC (Nat.pos_of_ne_zero hr) hA hB hC hσ)
      have hlen : (r - (r - 1)).eval = 1 := by
        change r.eval - (r.eval - 1) = 1
        omega
      have hscope : exec I (scope do
          let product ← alloc p (m * n)
          gemm p m r n A ao B bo product 0
          forRange (m * n) fun t => ins (.bin p .sub ⟨C, co + IExp.var t⟩
            ⟨C, co + IExp.var t⟩ ⟨product, IExp.var t⟩)).run st = some out := by
        change exec I (.seq (.alloc p (m * n) _) .skip) st = some out
        rw [exec_seq_skip]
        exact hexec
      refine ⟨out, ?_, hw⟩
      change exec I (.seq (.loop (r - (r - 1)) fun _ => (scope do
        let product ← alloc p (m * n)
        gemm p m r n A ao B bo product 0
        forRange (m * n) fun t => ins (.bin p .sub ⟨C, co + IExp.var t⟩
          ⟨C, co + IExp.var t⟩ ⟨product, IExp.var t⟩)).run) .skip) st = some out
      rw [exec_seq_skip, BlockSchurUpdate.exec_loop_one I st _ _ hlen]
      exact hscope
  obtain ⟨out, hexec, hw⟩ := hrun
  refine ⟨out, hexec, hw, fun i j => ?_⟩
  simpa only [Nat.add_assoc] using
    (Store.read_of_writeBlock_eq_some_of_lt hw
      (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)).trans
        (getElem?_flatten (MC - MA * MB) i j)

end NLAlib.Computation
