/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.LU
public import NLAlib.Computation.CopyStride
public import NLAlib.Matrix.Factorizations.LDL

/-!
# Stored one-by-one-pivot LDL factorization

The routine uses the existing elimination lower factor, retains the upper factor in scoped
workspace, and copies its diagonal to the diagonal-vector output. Hermitian inputs with
nonzero elimination pivots yield an LDL factorization. Both positive and negative pivots are
admitted; selection of two-by-two pivots is a separate algorithm.

## Main results

* `NLAlib.Computation.exec_ldlFactor`: exact success, output frame and LDL identity.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Factor a stored Hermitian matrix into a unit lower triangular matrix and a diagonal
vector. A scoped upper factor shares the actual LU elimination implementation; its diagonal
is copied to the vector output. No square roots are taken. [GolubVanLoan2013, §4.1]. -/
def ldlFactor {P ι VB VI : Type} (tag : P) (n : IExp VI) (A L D : VB)
    (ao lo doff : IExp VI) : Builder P ι VB VI Unit := scope do
  let U ← alloc tag (n * n)
  luFactor tag n A L U ao lo 0
  copyStride tag n U D 0 (n + 1) doff

variable {P ι : Type} [DecidableEq P]

namespace LDL

private theorem exec_empty_lu {K C : Type} [AddMonoid C] (I : Interp P ι K C)
    (tag : P) (st : St P K C) (n : IExp ℕ) (A L U : ℕ) (ao lo uo : IExp ℕ)
    (hn : n.eval = 0) :
    ∃ out, exec I (luFactor tag n A L U ao lo uo).run st = some out ∧
      out.store = st.store := by
  obtain ⟨out, hr, hs⟩ := exists_exec_alloc I tag (n * n) (fun S => (do
    copyv tag A ao S 0 (n * n)
    forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
    forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
    forRange n fun k => do
      luColumn tag n (.var k) S L U 0 lo uo
      schurStep tag n S 0 (.var k)).run) st (fun s => s = st.store) (by
        intro σ hσ
        refine ⟨σ, ?_, ?_⟩
        · change exec I (.seq (.named "copy" _ (.seq (.loop (n * n) _) .skip))
            (.seq (.loop (n * n) _) (.seq (.loop (n * n) _)
              (.seq (.loop n _) .skip)))) σ = some σ
          simp only [exec_seq, exec_named, exec_loop, IExp.eval_mul, hn, zero_mul,
            List.range_zero, List.foldlM_nil, Option.pure_def, Option.bind_some, exec_skip]
        · rw [hσ]
          exact Array.pop_push)
  refine ⟨out, ?_, hs⟩
  change exec I (.seq (.alloc tag (n * n) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

private theorem exec_empty_body (I : Interp P ι ℝ (OpCount P ι)) (tag : P)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n : IExp ℕ)
    (A L D : ℕ) (ao lo doff : IExp ℕ) (hn : n.eval = 0)
    (hstore : st.store = initial.push (tag, Array.replicate (n.eval * n.eval) none)) :
    ∃ out, exec I (do
      luFactor tag n A L initial.size ao lo 0
      copyStride tag n initial.size D 0 (n + 1) doff).run st = some out ∧
      out.store.pop = initial := by
  obtain ⟨out, hr, hs⟩ := exec_empty_lu I tag st n A L initial.size ao lo 0 hn
  refine ⟨out, ?_, ?_⟩
  · rw [exec_run_bind I (b := luFactor tag n A L initial.size ao lo 0)
      (fun _ => rfl), hr, Option.bind_some]
    change exec I (.seq (.loop n _) .skip) out = some out
    simp only [exec_seq, exec_loop, hn, List.range_zero, List.foldlM_nil,
      Option.pure_def, Option.bind_some, exec_skip]
  · rw [hs, hstore]
    exact Array.pop_push

private theorem exec_body (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n : IExp ℕ)
    (A L D : ℕ) (ao lo doff : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : Holds initial tag A ao.eval M)
    (hp : ∀ k : Fin n.eval, gaussState M k k k ≠ 0)
    (hL : Writable initial tag L lo.eval (n.eval * n.eval))
    (hD : Writable initial tag D doff.eval n.eval)
    (hAL : 0 < n.eval → A ≠ L)
    (hstore : st.store = initial.push (tag, Array.replicate (n.eval * n.eval) none)) :
    ∃ out, exec I (do
      luFactor tag n A L initial.size ao lo 0
      copyStride tag n initial.size D 0 (n + 1) doff).run st = some out ∧
      initial.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (D, doff.eval, n.eval)]
        [flatten (luLower M), Array.ofFn fun i : Fin n.eval => gaussState M i i i] =
          some out.store.pop := by
  by_cases hn : n.eval = 0
  · obtain ⟨out, hr, hs⟩ := exec_empty_body I tag initial st n A L D ao lo doff hn hstore
    refine ⟨out, hr, ?_⟩
    rw [hs]
    exact Store.writeBlocks_pair_eq_some_iff.mpr ⟨size_flatten _, Array.size_ofFn, initial,
      Store.writeBlock_eq_some_of_size_eq_zero (by simp only [size_flatten, hn, zero_mul]),
      Store.writeBlock_eq_some_of_size_eq_zero (by simp only [Array.size_ofFn, hn])⟩
  have hN : 0 < n.eval := Nat.pos_of_ne_zero hn
  have hLb := hL.lt_size (Nat.mul_pos hN hN)
  have hDb := hD.lt_size hN
  have hAb := Store.lt_size_of_read_eq_some (hM ⟨0, hN⟩ ⟨0, hN⟩)
  have hM' : Holds st.store tag A ao.eval M := fun i j => by
    rw [hstore, Store.read_push_of_lt hAb]
    exact hM i j
  have hU : Writable st.store tag initial.size 0 (n.eval * n.eval) := by
    rw [hstore]
    exact writable_of_shape_eq rfl
      (Store.getElem?_shape_push_size initial tag (n.eval * n.eval)) (by omega)
  obtain ⟨factored, hr₁, hw, _, hFU, _, _⟩ := exec_luFactor I hI hc tag st n A L
    initial.size ao lo 0 M hM' hp (hstore ▸ hL.push _) hU hAL
    (fun _ => Nat.ne_of_lt hAb) (Nat.ne_of_lt hLb)
  have hD' := (hstore ▸ hD.push (tag, Array.replicate (n.eval * n.eval) none)).of_shape_eq
    (Store.shape_of_writeBlocks_eq_some hw)
  obtain ⟨out, hr₂, hd⟩ := exec_copyStride I tag factored n initial.size D 0 (n + 1) doff
    (fun i => gaussState M i i i) (Nat.ne_of_gt hDb)
    (fun i => by simpa only [IExp.eval_zero, IExp.eval_add, IExp.eval_one, zero_add,
      Nat.add_mul, one_mul, luUpper_apply_self, Nat.add_comm] using hFU i i) hD'
  obtain ⟨_, _, mid, hlow, hupp⟩ := Store.writeBlocks_pair_eq_some_iff.mp hw
  have hsize : st.store.size = initial.size + 1 := by simp only [hstore, Array.size_push]
  have hmid : mid.size = st.store.size := Store.size_of_writeBlock_eq_some hlow
  have hfinal : factored.store.size = mid.size := Store.size_of_writeBlock_eq_some hupp
  have hlowpop := Store.writeBlock_pop_of_lt hlow (fun _ => by omega)
  have hpop : factored.store.pop = mid.pop := Store.pop_of_writeBlock_top hupp (by omega)
  have hdpop := Store.writeBlock_pop_of_lt hd (fun _ => by omega)
  rw [hpop] at hdpop
  have hstart : st.store.pop = initial := by rw [hstore]; exact Array.pop_push
  rw [hstart] at hlowpop
  refine ⟨out, ?_, Store.writeBlocks_pair_eq_some_iff.mpr
    ⟨size_flatten _, Array.size_ofFn, mid.pop, hlowpop, hdpop⟩⟩
  rw [exec_run_bind I (b := luFactor tag n A L initial.size ao lo 0)
    (fun _ => rfl), hr₁, Option.bind_some]
  exact hr₂

end LDL

/-- Exact stored LDL factorization succeeds for Hermitian inputs with nonzero elimination
pivots, including indefinite matrices. The only net writes are the unit lower factor and
pivot diagonal vector. Input may overlap the diagonal output; it is separate from the lower
factor when nonempty, and the two output buffers are distinct. Empty matrices require no
valid handles. [GolubVanLoan2013, §4.1]. -/
theorem exec_ldlFactor (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A L D : ℕ) (ao lo doff : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : Holds st.store tag A ao.eval M)
    (hHerm : M.IsHermitian) (hp : ∀ k : Fin n.eval, gaussState M k k k ≠ 0)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval))
    (hD : Writable st.store tag D doff.eval n.eval) (hLD : L ≠ D)
    (hAL : 0 < n.eval → A ≠ L) :
    ∃ out, exec I (ldlFactor tag n A L D ao lo doff).run st = some out ∧
      st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (D, doff.eval, n.eval)]
        [flatten (luLower M), Array.ofFn fun i : Fin n.eval => gaussState M i i i] =
          some out.store ∧ Holds out.store tag L lo.eval (luLower M) ∧
      (∀ i : Fin n.eval, out.store.read tag D (doff.eval + i) =
        some (gaussState M i i i)) ∧ IsLDL M (luLower M) (fun i => gaussState M i i i) := by
  obtain ⟨out, hr, hw⟩ := exists_exec_alloc I tag (n * n) (fun U => (do
    luFactor tag n A L U ao lo 0
    copyStride tag n U D 0 (n + 1) doff).run) st
    (fun s => st.store.writeBlocks tag
      [(L, lo.eval, n.eval * n.eval), (D, doff.eval, n.eval)]
      [flatten (luLower M), Array.ofFn fun i : Fin n.eval => gaussState M i i i] = some s)
    (fun σ hσ => LDL.exec_body I hI hc tag st.store σ n A L D ao lo doff M hM hp hL hD
      hAL hσ)
  obtain ⟨_, _, mid, hl, hd⟩ := Store.writeBlocks_pair_eq_some_iff.mp hw
  refine ⟨out, ?_, hw, ?_, ?_, hHerm.isLDL_luLower hp⟩
  · change exec I (.seq (.alloc tag (n * n) _) .skip) st = some out
    rw [exec_seq_skip]
    exact hr
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hd (Or.inl hLD)]
    simpa only [Nat.add_assoc] using (Store.read_of_writeBlock_eq_some_of_lt hl
      (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)).trans
        (getElem?_flatten (luLower M) i j)
  · intro i
    simpa only [Array.getElem?_ofFn, dif_pos i.isLt, Fin.eta] using
      Store.read_of_writeBlock_eq_some_of_lt (j := i.val) hd
        (by simpa only [Array.size_ofFn] using i.isLt)

end NLAlib.Computation
