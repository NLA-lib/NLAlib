/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.CholeskyFactorization
public import NLAlib.Matrix.Computation.TriangularSolve
public import NLAlib.Matrix.Computation.LU

/-!
# Solving linear systems through stored factorizations

The routines in this file execute a full factorization and triangular solves, using scoped
factor workspace. Their execution theorems relate the actual final right-hand side block to
the original linear system. The initial matrix is read before that block is overwritten, so
matrix entries inside an overlapping right-hand side block are allowed to change on return.

## Main definitions

* `NLAlib.Computation.choleskySolve`: factor a positive definite matrix and solve one system.
* `NLAlib.Computation.luSolve`: factor without pivoting and solve one system.

## Main results

* `NLAlib.Computation.exec_choleskySolve`: exact success, solution and output block write.
* `NLAlib.Computation.isLinearSolveRoutine_choleskySolve`: a zero-error routine certificate.
* `NLAlib.Computation.exec_luSolve`: exact unpivoted factorization and solution.
* `NLAlib.Computation.isLinearSolveRoutine_luSolve`: the corresponding zero-error certificate.
-/

@[expose] public section

namespace NLAlib.Computation

open scoped Matrix
open Builder

/-- Factor a stored matrix by the full Cholesky routine, solve through its lower factor and
the factor's adjoint, and overwrite the right-hand side with the solution. Factor storage is
scoped. The execution theorem assumes positive definiteness in exact real arithmetic.
[GolubVanLoan2013, §4.2]. -/
def choleskySolve {P ι VB VI : Type} (tag : P) (n : IExp VI) (matrix : VB)
    (off : IExp VI) (xb : VB) (xo : IExp VI) : Builder P ι VB VI Unit := scope do
  let factor ← alloc tag (n * n)
  cholesky tag n matrix off factor 0
  trsvLower tag n factor 0 xb xo
  trsvLowerAdjoint tag n factor 0 xb xo

/-- Factor a stored matrix by the full unpivoted LU routine, solve its lower and upper
triangular systems and overwrite the right-hand side with the solution. Both factor buffers
are scoped. Exact execution assumes every elimination pivot is nonzero.
[GolubVanLoan2013, §3.2]. -/
def luSolve {P ι VB VI : Type} (tag : P) (n : IExp VI) (matrix : VB)
    (off : IExp VI) (xb : VB) (xo : IExp VI) : Builder P ι VB VI Unit := scope do
  let lower ← alloc tag (n * n)
  let upper ← alloc tag (n * n)
  luFactor tag n matrix lower upper off 0 0
  trsvLower tag n lower 0 xb xo
  trsvUpper tag n upper 0 xb xo

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Factor-then-solve through Cholesky releases all factor workspace before its continuation. -/
theorem executionComposable_choleskySolve (I : Interp P ι K C) (tag : P) (n : IExp ℕ)
    (matrix : ℕ) (off : IExp ℕ) (xb : ℕ) (xo : IExp ℕ) :
    ExecutionComposable I (choleskySolve tag n matrix off xb xo) :=
  executionComposable_single I (fun _ => rfl)

/-- Factor-then-solve through unpivoted LU releases both factors before its continuation. -/
theorem executionComposable_luSolve (I : Interp P ι K C) (tag : P) (n : IExp ℕ)
    (matrix : ℕ) (off : IExp ℕ) (xb : ℕ) (xo : IExp ℕ) :
    ExecutionComposable I (luSolve tag n matrix off xb xo) :=
  executionComposable_single I (fun _ => rfl)

namespace FactorizationSolve

private theorem exec_lower (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P)
    (N : ℕ) (L : Matrix (Fin N) (Fin N) ℝ) (hL : L.IsLowerTriangular)
    (hd : ∀ i, L i i ≠ 0) (factor xb : ℕ) (xo : IExp ℕ) (st : St P ℝ C)
    (b : Fin N → ℝ) (hM : Holds st.store tag factor 0 L)
    (hb : ∀ i : Fin N, st.store.read tag xb (xo.eval + i) = some (b i))
    (hsep : 0 < N → factor ≠ xb) :
    ∃ (out : St P ℝ C) (y : Fin N → ℝ),
      exec I (trsvLower tag (.const N) factor 0 xb xo).run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn y) = some out.store ∧ L *ᵥ y = b := by
  have h : IsRelErrSem (fun _ => 0) (fun _ x => x) (fun _ _ => True) I.sem := by
    rw [hI]
    exact isRelErrSem_exactSem
  have hdis : blockDisjoint (factor, 0, N * N) (xb, xo.eval, N) = true := by
    apply blockDisjoint_iff.mpr
    by_cases hN : N = 0
    · exact Or.inr (Or.inr (Or.inl hN))
    · exact Or.inl (hsep (Nat.pos_of_ne_zero hN))
  have hcert := h.isLinearSolveRoutine_trsvLower I tag N L hL hd factor xb 0 xo
    (by norm_num) hdis
  have hw : Writable st.store tag xb xo.eval N := fun i hi =>
    Store.exists_getElem?_shape_of_read_eq_some (hb ⟨i, hi⟩)
  obtain ⟨out, Y, hr, hwrite, he⟩ := hcert.run st b
    (fun i j => ⟨L i j, hM i j, rfl⟩) (fun i => ⟨b i, hb i, rfl⟩) hw
  have he₀ : IsLinearSolveErr 0 L b Y := by
    simpa only [roundingFactor, sub_zero, one_pow, inv_one, sub_self] using he
  exact ⟨out, Y, hr, hwrite, he₀.mulVec_eq⟩

private theorem rhs_read_of_write {N : ℕ} {P : Type} [DecidableEq P]
    {before after : Store P ℝ} {tag : P} {xb off : ℕ} {y : Fin N → ℝ}
    (hw : before.writeBlock tag xb off (Array.ofFn y) = some after) (i : Fin N) :
    after.read tag xb (off + i) = some (y i) := by
  have hr := Store.read_of_writeBlock_eq_some_of_lt hw (j := i.val)
    (by rw [Array.size_ofFn]; exact i.isLt)
  simpa only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte] using hr

private theorem exec_choleskySolveBody {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef) (b : Fin N → ℝ)
    (matrix xb : ℕ) (off xo : IExp ℕ) (hM : Holds initial tag matrix off.eval A)
    (hb : ∀ i : Fin N, initial.read tag xb (xo.eval + i) = some (b i))
    (hw : Writable initial tag xb xo.eval N)
    (hstore : st.store = initial.push (tag, Array.replicate (N * N) none)) :
    ∃ (out : St P ℝ (OpCount P ι)) (x : Fin N → ℝ), exec I (do
      cholesky tag (.const N) matrix off initial.size 0
      trsvLower tag (.const N) initial.size 0 xb xo
      trsvLowerAdjoint tag (.const N) initial.size 0 xb xo).run st = some out ∧
      initial.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store.pop ∧ A *ᵥ x = b := by
  have hxb : 0 < N → xb < initial.size := fun hN => hw.lt_size hN
  have hMp : Holds st.store tag matrix off.eval A := fun i j => by
    have hmb := Store.lt_size_of_read_eq_some (hM i j)
    rw [hstore, Store.read_push_of_lt hmb]
    exact hM i j
  have hfactor : Writable st.store tag initial.size 0 (N * N) := by
    rw [hstore]
    exact writable_of_shape_eq rfl (Store.getElem?_shape_push_size initial tag (N * N))
      (by omega)
  obtain ⟨factored, hr₁, hwrite₁, hL, hchol⟩ := exec_cholesky I hI hc tag st (.const N)
    matrix initial.size off 0 A hA hMp hfactor
  have hshape₁ := Store.shape_of_writeBlock_eq_some hwrite₁
  have hb₁ : ∀ i : Fin N, factored.store.read tag xb (xo.eval + i) = some (b i) := fun i => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hwrite₁
      (Or.inl (Nat.ne_of_lt (hxb (Nat.zero_lt_of_lt i.isLt)))),
      hstore, Store.read_push_of_lt (hxb (Nat.zero_lt_of_lt i.isLt))]
    exact hb i
  obtain ⟨forward, y, hr₂, hwrite₂, hLy⟩ := exec_lower I hI tag N (choleskyLower A)
    hchol.isLowerTriangular (fun i => (hchol.apply_self_pos i).ne') initial.size xb xo
    factored b hL hb₁ (fun hN => Nat.ne_of_gt (hxb hN))
  have hL₂ : Holds forward.store tag initial.size 0 (choleskyLower A) := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hwrite₂
      (Or.inl (Nat.ne_of_gt (hxb (Nat.zero_lt_of_lt i.isLt))))]
    exact hL i j
  obtain ⟨out, x, hr₃, hwrite₃, hLHx⟩ := exec_trsvLowerAdjoint I hI tag N (choleskyLower A)
    hchol.isLowerTriangular (fun i => (hchol.apply_self_pos i).ne') initial.size xb 0 xo
    forward y hL₂ (rhs_read_of_write hwrite₂)
  have hnet := Store.writeBlock_writeBlock_self hwrite₂ hwrite₃ (by simp)
  have hpop : factored.store.pop = initial := by
    rw [Store.pop_of_writeBlock_top hwrite₁ (by simp only [hstore, Array.size_push]; omega),
      hstore]
    exact Array.pop_push
  have hsize : factored.store.size = initial.size + 1 := by
    simpa only [Store.size_shape, hstore, Array.size_push] using congrArg Array.size hshape₁
  have hfinal := Store.writeBlock_pop_of_lt hnet (fun hp => by
    have := hxb (by simpa only [Array.size_ofFn] using hp)
    omega)
  refine ⟨out, x, ?_, hpop ▸ hfinal, ?_⟩
  · rw [exec_run_bind I (b := cholesky tag (.const N) matrix off initial.size 0)
      (fun _ => rfl), hr₁, Option.bind_some,
      exec_run_bind I (b := trsvLower tag (.const N) initial.size 0 xb xo)
      (fun _ => rfl), hr₂, Option.bind_some]
    exact hr₃
  · have hcanonical : IsCholesky A (choleskyLower A) := hA.isCholesky_choleskyLower
    rw [hcanonical.eq_mul_conjTranspose]
    exact (Matrix.mulVec_mulVec _ _ _).symm.trans (by rw [hLHx, hLy])

/-- Execute the lower and upper substitutions of an actual LU factorization. Nonzero factor
diagonals guarantee success; the net effect is one RHS block write and a solution of the
factored system. Factor buffers may be invalid in the empty dimension. -/
theorem exec_luTriangularSolves (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (N : ℕ) (A L U : Matrix (Fin N) (Fin N) ℝ)
    (hf : IsLU A L U) (hdL : ∀ i, L i i ≠ 0) (hdU : ∀ i, U i i ≠ 0)
    (lower upper xb : ℕ) (xo : IExp ℕ) (b : Fin N → ℝ)
    (hL : Holds st.store tag lower 0 L) (hU : Holds st.store tag upper 0 U)
    (hb : ∀ i : Fin N, st.store.read tag xb (xo.eval + i) = some (b i))
    (hLx : 0 < N → lower ≠ xb) (hUx : 0 < N → upper ≠ xb) :
    ∃ (out : St P ℝ C) (x : Fin N → ℝ), exec I (do
      trsvLower tag (.const N) lower 0 xb xo
      trsvUpper tag (.const N) upper 0 xb xo).run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store ∧ A *ᵥ x = b := by
  obtain ⟨forward, y, hr₁, hwrite₁, hLy⟩ := exec_lower I hI tag N L
    hf.isUnitLowerTriangular.isLowerTriangular hdL lower xb xo st b hL hb hLx
  have hU' : Holds forward.store tag upper 0 U := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hwrite₁
      (Or.inl (hUx (Nat.zero_lt_of_lt i.isLt)))]
    exact hU i j
  obtain ⟨out, x, hr₂, hwrite₂, hUxsol⟩ := exec_trsvUpper I hI tag N U hf.isUpperTriangular
    hdU upper xb 0 xo forward y hU' (rhs_read_of_write hwrite₁)
  refine ⟨out, x, ?_, Store.writeBlock_writeBlock_self hwrite₁ hwrite₂ (by simp), ?_⟩
  · rw [exec_run_bind I (b := trsvLower tag (.const N) lower 0 xb xo)
      (fun _ => rfl), hr₁, Option.bind_some]
    exact hr₂
  · rw [hf.eq_mul]
    exact (Matrix.mulVec_mulVec _ _ _).symm.trans (by rw [hUxsol, hLy])

private theorem pop_pop_of_factorWrites (initial start mid final : Store P ℝ) (tag : P)
    (N : ℕ) (hstore : start = (initial.push (tag, Array.replicate (N * N) none)).push
      (tag, Array.replicate (N * N) none)) (L U : Array ℝ)
    (hL : start.writeBlock tag initial.size 0 L = some mid)
    (hU : mid.writeBlock tag (initial.size + 1) 0 U = some final) :
    final.pop.pop = initial := by
  have hmidsize : mid.size = initial.size + 2 := by
    simpa only [Store.size_shape, hstore, Array.size_push, Nat.add_assoc] using
      congrArg Array.size (Store.shape_of_writeBlock_eq_some hL)
  have hpopU := Store.pop_of_writeBlock_top hU (by omega)
  have hLpop := Store.writeBlock_pop_of_lt hL (fun _ => by
    simp only [hstore, Array.size_push]
    omega)
  have hpopL := Store.pop_of_writeBlock_top hLpop (by
    simp only [hstore, Array.size_push, Array.size_pop]
    omega)
  rw [hpopU, hpopL, hstore]
  simp only [Array.pop_push]

private theorem exec_luSolveBody {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hp : ∀ k : Fin N, gaussState A k k k ≠ 0)
    (b : Fin N → ℝ) (matrix xb : ℕ) (off xo : IExp ℕ)
    (hM : Holds initial tag matrix off.eval A)
    (hb : ∀ i : Fin N, initial.read tag xb (xo.eval + i) = some (b i))
    (hw : Writable initial tag xb xo.eval N)
    (hstore : st.store = (initial.push (tag, Array.replicate (N * N) none)).push
      (tag, Array.replicate (N * N) none)) :
    ∃ (out : St P ℝ (OpCount P ι)) (x : Fin N → ℝ), exec I (do
      luFactor tag (.const N) matrix initial.size (initial.size + 1) off 0 0
      trsvLower tag (.const N) initial.size 0 xb xo
      trsvUpper tag (.const N) (initial.size + 1) 0 xb xo).run st = some out ∧
      initial.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store.pop.pop ∧ A *ᵥ x = b := by
  have hxb : 0 < N → xb < initial.size := fun hN => hw.lt_size hN
  have hmb : 0 < N → matrix < initial.size := fun hN =>
    Store.lt_size_of_read_eq_some (hM ⟨0, hN⟩ ⟨0, hN⟩)
  have hMp : Holds st.store tag matrix off.eval A := fun i j => by
    have hm := hmb (Nat.zero_lt_of_lt i.isLt)
    rw [hstore, Store.read_push_of_lt (by simp only [Array.size_push]; omega),
      Store.read_push_of_lt hm]
    exact hM i j
  have hcap := writable_of_shape_eq rfl (Store.getElem?_shape_push_size initial tag (N * N))
    (by omega : 0 + N * N ≤ N * N)
  have hLcap : Writable st.store tag initial.size 0 (N * N) := hstore ▸ hcap.push _
  have hUcap : Writable st.store tag (initial.size + 1) 0 (N * N) := by
    rw [hstore]
    apply writable_of_shape_eq rfl
    · simpa only [Array.size_push] using Store.getElem?_shape_push_size
        (initial.push (tag, Array.replicate (N * N) none)) tag (N * N)
    · omega
  obtain ⟨factored, hr₁, hwrite₁, hL, hU, hf, -⟩ := exec_luFactor I hI hc tag st (.const N)
    matrix initial.size (initial.size + 1) off 0 0 A hMp hp hLcap hUcap
    (fun hN => Nat.ne_of_lt (hmb hN)) (fun hN => by have := hmb hN; omega) (by omega)
  have hb₁ : ∀ i : Fin N, factored.store.read tag xb (xo.eval + i) = some (b i) := fun i => by
    have hx := hxb (Nat.zero_lt_of_lt i.isLt)
    rw [Store.read_of_writeBlocks_eq_some_of_forall hwrite₁ (fun block hblock => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
      rcases hblock with rfl | rfl <;> exact Or.inl (by omega)), hstore,
      Store.read_push_of_lt (by simp only [Array.size_push]; omega), Store.read_push_of_lt hx]
    exact hb i
  have hf' : IsLU A (luLower A) (luUpper A) := isLU_luLower_luUpper
    (fun i _ => by rw [luUpper_apply_self]; exact hp i)
  obtain ⟨out, x, hr₂, hwrite₂, hsol⟩ := exec_luTriangularSolves I hI tag factored N A
    (luLower A) (luUpper A) hf'
    (fun i => by rw [(isUnitLowerTriangular_luLower A).apply_self]; exact one_ne_zero)
    (fun i => by rw [luUpper_apply_self]; exact hp i) initial.size (initial.size + 1) xb xo b
    hL hU hb₁ (fun hN => Nat.ne_of_gt (hxb hN)) (fun hN => by have := hxb hN; omega)
  obtain ⟨-, -, mid, hwL, hwU⟩ := Store.writeBlocks_pair_eq_some_iff.mp hwrite₁
  have hpop := pop_pop_of_factorWrites initial st.store mid factored.store tag N hstore _ _ hwL hwU
  have hsize : factored.store.size = initial.size + 2 := by
    simpa only [Store.size_shape, hstore, Array.size_push, Nat.add_assoc] using
      congrArg Array.size (Store.shape_of_writeBlocks_eq_some hwrite₁)
  have hwritepop := Store.writeBlock_pop_of_lt hwrite₂ (fun hN => by
    have := hxb (by simpa only [Array.size_ofFn] using hN)
    omega)
  have hwritepop₂ := Store.writeBlock_pop_of_lt hwritepop (fun hN => by
    have := hxb (by simpa only [Array.size_ofFn] using hN)
    simp only [Array.size_pop]
    omega)
  refine ⟨out, x, ?_, hpop ▸ hwritepop₂, hsol⟩
  rw [exec_run_bind I
    (b := luFactor tag (.const N) matrix initial.size (initial.size + 1) off 0 0)
    (fun _ => rfl), hr₁, Option.bind_some]
  exact hr₂

end FactorizationSolve

/-- Under exact real arithmetic and standard instruction charges, a stored positive definite
matrix and a stored right-hand side suffice for full factorization followed by two triangular
solves to succeed. The output solves the original system, and the only net store change is
the right-hand side block write. Factor workspace is released; source and output may overlap,
and empty matrices require no valid input handles. [GolubVanLoan2013, §4.2]. -/
theorem exec_choleskySolve {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.PosDef) (b : Fin N → ℝ) (matrix xb : ℕ) (off xo : IExp ℕ)
    (hM : Holds st.store tag matrix off.eval A)
    (hb : ∀ i : Fin N, st.store.read tag xb (xo.eval + i) = some (b i)) :
    ∃ (out : St P ℝ (OpCount P ι)) (x : Fin N → ℝ),
      exec I (choleskySolve tag (.const N) matrix off xb xo).run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store ∧ A *ᵥ x = b := by
  let Q : Store P ℝ → Prop := fun s => ∃ x : Fin N → ℝ,
    st.store.writeBlock tag xb xo.eval (Array.ofFn x) = some s ∧ A *ᵥ x = b
  have hw : Writable st.store tag xb xo.eval N := fun i hi =>
    Store.exists_getElem?_shape_of_read_eq_some (hb ⟨i, hi⟩)
  obtain ⟨out, hr, x, hwrite, hsol⟩ := exists_exec_alloc I tag
    (IExp.const N * IExp.const N) (fun factor => ((do
      cholesky tag (.const N) matrix off factor 0
      trsvLower tag (.const N) factor 0 xb xo
      trsvLowerAdjoint tag (.const N) factor 0 xb xo) : Builder P ι ℕ ℕ Unit).run) st Q
    (fun σ hσ => by
      obtain ⟨out, x, hr, hw, hs⟩ := FactorizationSolve.exec_choleskySolveBody I hI hc tag
        st.store σ N A hA b matrix xb off xo hM hb hw
        (by simpa only [IExp.eval_mul, IExp.eval_const] using hσ)
      exact ⟨out, hr, x, hw, hs⟩)
  refine ⟨out, x, ?_, hwrite, hsol⟩
  change exec I (.seq (.alloc tag (IExp.const N * IExp.const N) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

/-- The full stored Cholesky factor-then-solve program supplies a zero-error linear-solve
certificate under exact real semantics and standard instruction charges, for each positive
definite input. The original matrix precondition and a readable right-hand side are sufficient;
the factorization is executed by the program. [GolubVanLoan2013, §4.2]. -/
theorem isLinearSolveRoutine_choleskySolve {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosDef) (matrix xb : ℕ) (off xo : IExp ℕ) :
    IsLinearSolveRoutine I (fun _ x => x) tag A 0
      (fun s => Holds s tag matrix off.eval A) xb xo
      (choleskySolve tag (.const N) matrix off xb xo) where
  composable := executionComposable_choleskySolve I tag (.const N) matrix off xb xo
  run st b hM hb _ := by
    have hb' : ∀ i : Fin N, st.store.read tag xb (xo.eval + i) = some (b i) := fun i => by
      obtain ⟨w, hw, hd⟩ := hb i
      simpa only [hd] using hw
    obtain ⟨out, x, hr, hwrite, hsol⟩ := exec_choleskySolve I hI hc tag st N A hA b
      matrix xb off xo hM hb'
    exact ⟨out, x, hr, hwrite, IsLinearSolveErr.of_mulVec_eq le_rfl hsol⟩

/-- Under exact real arithmetic and standard instruction charges, readable matrix and
right-hand side blocks and nonzero elimination pivots suffice for full unpivoted LU followed
by triangular solves to succeed. The output solves the original system and is the only net
store write. Both factor buffers are released. Source and output may overlap, and empty
matrices require no valid input handles. [GolubVanLoan2013, §3.2]. -/
theorem exec_luSolve {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (hp : ∀ k : Fin N, gaussState A k k k ≠ 0) (b : Fin N → ℝ)
    (matrix xb : ℕ) (off xo : IExp ℕ) (hM : Holds st.store tag matrix off.eval A)
    (hb : ∀ i : Fin N, st.store.read tag xb (xo.eval + i) = some (b i)) :
    ∃ (out : St P ℝ (OpCount P ι)) (x : Fin N → ℝ),
      exec I (luSolve tag (.const N) matrix off xb xo).run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store ∧ A *ᵥ x = b := by
  let Q : Store P ℝ → Prop := fun s => ∃ x : Fin N → ℝ,
    st.store.writeBlock tag xb xo.eval (Array.ofFn x) = some s ∧ A *ᵥ x = b
  have hw : Writable st.store tag xb xo.eval N := fun i hi =>
    Store.exists_getElem?_shape_of_read_eq_some (hb ⟨i, hi⟩)
  have houter : ∀ σ : St P ℝ (OpCount P ι),
      σ.store = st.store.push (tag, Array.replicate (N * N) none) →
      ∃ out, exec I (.alloc tag (IExp.const N * IExp.const N) fun upper => (do
        luFactor tag (.const N) matrix st.store.size upper off 0 0
        trsvLower tag (.const N) st.store.size 0 xb xo
        trsvUpper tag (.const N) upper 0 xb xo).run) σ = some out ∧ Q out.store.pop := by
    intro σ hσ
    have hsize : σ.store.size = st.store.size + 1 := by simp only [hσ, Array.size_push]
    apply exists_exec_alloc I tag (IExp.const N * IExp.const N) _ σ (fun s => Q s.pop)
    intro τ hτ
    have hstore : τ.store = (st.store.push (tag, Array.replicate (N * N) none)).push
        (tag, Array.replicate (N * N) none) := by
      simpa only [hσ, IExp.eval_mul, IExp.eval_const] using hτ
    obtain ⟨out, x, hr, hwrite, hsol⟩ := FactorizationSolve.exec_luSolveBody I hI hc tag
      st.store τ N A hp b matrix xb off xo hM hb hw hstore
    exact ⟨out, by simpa only [hsize] using hr, x, hwrite, hsol⟩
  obtain ⟨out, hr, x, hwrite, hsol⟩ := exists_exec_alloc I tag
    (IExp.const N * IExp.const N) (fun lower => .alloc tag (IExp.const N * IExp.const N)
      fun upper => ((do
        luFactor tag (.const N) matrix lower upper off 0 0
        trsvLower tag (.const N) lower 0 xb xo
        trsvUpper tag (.const N) upper 0 xb xo) : Builder P ι ℕ ℕ Unit).run) st Q
    (fun σ hσ => houter σ (by simpa only [IExp.eval_mul, IExp.eval_const] using hσ))
  refine ⟨out, x, ?_, hwrite, hsol⟩
  change exec I (.seq (.alloc tag (IExp.const N * IExp.const N) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

/-- The full stored unpivoted LU factor-then-solve program supplies a zero-error linear-solve
certificate under exact real semantics and standard instruction charges whenever every
elimination pivot is nonzero. Its precondition reads the original coefficient matrix; the
program executes the factorization before solving through the factors.
[GolubVanLoan2013, §3.2]. -/
theorem isLinearSolveRoutine_luSolve {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P) (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (hp : ∀ k : Fin N, gaussState A k k k ≠ 0)
    (matrix xb : ℕ) (off xo : IExp ℕ) :
    IsLinearSolveRoutine I (fun _ x => x) tag A 0
      (fun s => Holds s tag matrix off.eval A) xb xo
      (luSolve tag (.const N) matrix off xb xo) where
  composable := executionComposable_luSolve I tag (.const N) matrix off xb xo
  run st b hM hb _ := by
    have hb' : ∀ i : Fin N, st.store.read tag xb (xo.eval + i) = some (b i) := fun i => by
      obtain ⟨w, hw, hd⟩ := hb i
      simpa only [hd] using hw
    obtain ⟨out, x, hr, hwrite, hsol⟩ := exec_luSolve I hI hc tag st N A hp b
      matrix xb off xo hM hb'
    exact ⟨out, x, hr, hwrite, IsLinearSolveErr.of_mulVec_eq le_rfl hsol⟩

end NLAlib.Computation
