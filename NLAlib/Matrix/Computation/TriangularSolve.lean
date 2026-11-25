/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.TriangularSolveFrames
public import NLAlib.Matrix.Computation.LinearSolveRoutine
public import NLAlib.Matrix.Factorizations.Triangular
public import Mathlib.Data.Fin.Rev

/-!
# Stored upper and adjoint triangular solves

Upper and adjoint solves copy transformed operands into packed workspace, call the actual
lower triangular solve and copy the solution back. Matrix and vector workspace is scoped.
They use $N^2+N$ operand workspace cells in addition to the lower solver's one-word scratch.
The rounded certificates use real decoded arithmetic; an adjoint load executes scalar
conjugation and transposed addresses. They do not assert complex floating-point accuracy.

## Main definitions

* `NLAlib.Computation.trsvUpper`: upper triangular solve through index reversal.
* `NLAlib.Computation.trsvLowerAdjoint`: solve the adjoint of a lower triangular matrix.
* `NLAlib.Computation.trsvUpperAdjoint`: solve the adjoint of an upper triangular matrix.

## Main results

* `NLAlib.Computation.executionComposable_trsvUpper`: composition of the upper solve.
* `NLAlib.Computation.IsRelErrSem.isLinearSolveRoutine_trsvUpper`: the rounded upper solve.
* `NLAlib.Computation.IsRelErrSem.isLinearSolveRoutine_trsvLowerAdjoint`,
  `NLAlib.Computation.IsRelErrSem.isLinearSolveRoutine_trsvUpperAdjoint`: rounded adjoint solves.
* `NLAlib.Computation.exec_trsvUpper`, `NLAlib.Computation.exec_trsvLowerAdjoint`,
  `NLAlib.Computation.exec_trsvUpperAdjoint`: exact real success, solution and output frame.
-/

@[expose] public section

namespace NLAlib.Computation

open scoped Matrix
open Builder

namespace TriangularSolve

/-- Pack transformed matrix and vector operands, run the actual lower triangular solver and
gather its output into the original right-hand side block. The matrix workspace has $n^2$
cells and the vector workspace $n$ cells; both are scoped. Address functions are symbolic
index expressions, so every data access is an instruction in the stored computation model. -/
def solvePacked {P ι VB VI : Type} (tag : P) (n : IExp VI) (matrix : VB)
    (matrixAt : IExp VI → IExp VI → IExp VI) (xb : VB) (xo : IExp VI)
    (inputAt outputAt : IExp VI → IExp VI) (conjugate : Bool) : Builder P ι VB VI Unit :=
  scope do
    let packed ← alloc tag (n * n)
    let rhs ← alloc tag n
    copyMatrixMapped tag n matrix matrixAt packed conjugate
    copyMapped tag n xb inputAt rhs 0 false
    trsvLower tag n packed 0 rhs 0
    copyMapped tag n rhs outputAt xb xo false

end TriangularSolve

/-- Solve an upper triangular system in place by reversing the rows and columns of a packed
matrix copy and the entries of a right-hand side copy, using lower triangular substitution,
then reversing the output copy. The extra matrix and vector workspace is scoped.
[GolubVanLoan2013, §3.1]. -/
def trsvUpper {P ι VB VI : Type} (tag : P) (n : IExp VI) (matrix : VB)
    (off : IExp VI) (xb : VB) (xo : IExp VI) : Builder P ι VB VI Unit :=
  TriangularSolve.solvePacked tag n matrix
    (fun i j => off + (n - 1 - i) + n * (n - 1 - j)) xb xo
    (fun i => xo + (n - 1 - i)) (fun i => n - 1 - i) false

/-- Solve the adjoint of a lower triangular system in place. A reversed transposed matrix
copy passes through actual scalar conjugation, and a reversed right-hand side is solved by
the lower triangular kernel. The extra matrix and vector workspace is scoped. Accuracy
certificates use real decoding, where the adjoint equals the transpose. -/
def trsvLowerAdjoint {P ι VB VI : Type} (tag : P) (n : IExp VI) (matrix : VB)
    (off : IExp VI) (xb : VB) (xo : IExp VI) : Builder P ι VB VI Unit :=
  TriangularSolve.solvePacked tag n matrix
    (fun i j => off + (n - 1 - j) + n * (n - 1 - i)) xb xo
    (fun i => xo + (n - 1 - i)) (fun i => n - 1 - i) true

/-- Solve the adjoint of an upper triangular system in place. A transposed matrix copy passes
through actual scalar conjugation before lower triangular substitution. The extra matrix and
vector workspace is scoped. Accuracy certificates use real decoding, where the adjoint equals
the transpose. -/
def trsvUpperAdjoint {P ι VB VI : Type} (tag : P) (n : IExp VI) (matrix : VB)
    (off : IExp VI) (xb : VB) (xo : IExp VI) : Builder P ι VB VI Unit :=
  TriangularSolve.solvePacked tag n matrix (fun i j => off + j + n * i) xb xo
    (fun i => xo + i) id true

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- An upper triangular solve releases its copied operands before executing its continuation. -/
theorem executionComposable_trsvUpper (I : Interp P ι K C) (tag : P) (n : IExp ℕ)
    (matrix : ℕ) (off : IExp ℕ) (xb : ℕ) (xo : IExp ℕ) :
    ExecutionComposable I (trsvUpper tag n matrix off xb xo) :=
  executionComposable_single I (fun _ => rfl)

/-- A solve of a lower triangular matrix's adjoint releases its copied operands before its
continuation executes. -/
theorem executionComposable_trsvLowerAdjoint (I : Interp P ι K C) (tag : P) (n : IExp ℕ)
    (matrix : ℕ) (off : IExp ℕ) (xb : ℕ) (xo : IExp ℕ) :
    ExecutionComposable I (trsvLowerAdjoint tag n matrix off xb xo) :=
  executionComposable_single I (fun _ => rfl)

/-- A solve of an upper triangular matrix's adjoint releases its copied operands before its
continuation executes. -/
theorem executionComposable_trsvUpperAdjoint (I : Interp P ι K C) (tag : P) (n : IExp ℕ)
    (matrix : ℕ) (off : IExp ℕ) (xb : ℕ) (xo : IExp ℕ) :
    ExecutionComposable I (trsvUpperAdjoint tag n matrix off xb xo) :=
  executionComposable_single I (fun _ => rfl)

namespace TriangularSolve

private theorem exec_loadOperands {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (tag : P)
    (st : St P K C) (N : ℕ) (matrix : ℕ) (matrixAt : IExp ℕ → IExp ℕ → IExp ℕ)
    (xb : ℕ) (inputAt : IExp ℕ → IExp ℕ) (packed rhs : ℕ) (conjugate : Bool)
    (B : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (hM : ∀ i j : Fin N, ∃ w,
      st.store.read tag matrix (matrixAt (.var i) (.var j)).eval = some w ∧ dec tag w = B i j)
    (hb : ∀ i : Fin N, ∃ w,
      st.store.read tag xb (inputAt (.var i)).eval = some w ∧ dec tag w = b i)
    (hwM : Writable st.store tag packed 0 (N * N)) (hwr : Writable st.store tag rhs 0 N)
    (hmp : 0 < N → matrix ≠ packed) (hxp : 0 < N → xb ≠ packed)
    (hxr : 0 < N → xb ≠ rhs) (hpr : packed ≠ rhs) :
    ∃ out : St P K C, exec I (do
      copyMatrixMapped tag (.const N) matrix matrixAt packed conjugate
      copyMapped tag (.const N) xb inputAt rhs 0 false).run st = some out ∧
      out.store.shape = st.store.shape ∧ HoldsDecoded out.store dec tag packed 0 B ∧
      ReadsDecoded out.store dec tag rhs 0 b ∧
      ∀ q buf i, buf ≠ packed → buf ≠ rhs → out.store.read q buf i = st.store.read q buf i := by
  obtain ⟨mid, hr₁, hshape, hpacked, hframe⟩ :=
    exec_copyMatrixMapped I h tag st N matrix matrixAt packed conjugate B hM hwM hmp
  have hb' : ∀ i : Fin N, ∃ w,
      mid.store.read tag xb (inputAt (.var i)).eval = some w ∧ dec tag w = b i := fun i => by
    rw [hframe tag xb _ (hxp (by have := i.isLt; omega))]
    exact hb i
  obtain ⟨out, W, hr₂, hw, hdec⟩ := exec_copyMapped_const I h tag mid N xb inputAt rhs
    0 false b hb' (hwr.of_shape_eq hshape) hxr
  refine ⟨out, ?_, (Store.shape_of_writeBlock_eq_some hw).trans hshape, ?_, ?_, ?_⟩
  · rw [exec_run_bind I
      (b := copyMatrixMapped tag (.const N) matrix matrixAt packed conjugate)
      (fun _ => rfl), hr₁, Option.bind_some]
    exact hr₂
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hpr)]
    exact hpacked i j
  · intro i
    refine ⟨W i, ?_, hdec i⟩
    have hr := Store.read_of_writeBlock_eq_some_of_lt hw (j := i.val)
      (by rw [Array.size_ofFn]; exact i.isLt)
    simpa only [IExp.eval_zero, Array.getElem?_ofFn, i.isLt, ↓reduceDIte] using hr
  · intro q buf i hbp hbr
    exact (Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hbr)).trans (hframe q buf i hbp)

private theorem solve_error_reindex {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b y x : Fin N → ℝ} {η : ℝ} (e : Fin N ≃ Fin N)
    (h : IsLinearSolveErr η (A.submatrix e e) (b ∘ e) y)
    (hx : x = y ∘ e.symm) : IsLinearSolveErr η A b x := by
  rw [hx]
  have he := h.reindex e.symm
  convert he using 1
  · ext i j
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
  · ext i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]

private theorem exec_solveCopy {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (tag : P)
    (st : St P K C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (e : Fin N ≃ Fin N) (packed rhs xb : ℕ) (xo : IExp ℕ)
    (outputAt : IExp ℕ → IExp ℕ) (houtput : ∀ i : Fin N, (outputAt (.var i)).eval = e.symm i)
    (hB : (A.submatrix e e).IsLowerTriangular) (hd : ∀ i, A (e i) (e i) ≠ 0)
    (hu : u tag < 1) (hpr : packed ≠ rhs) (hrx : 0 < N → rhs ≠ xb)
    (hM : HoldsDecoded st.store dec tag packed 0 (A.submatrix e e))
    (hb : ReadsDecoded st.store dec tag rhs 0 (b ∘ e))
    (hwr : Writable st.store tag rhs 0 N) (hwx : Writable st.store tag xb xo.eval N) :
    ∃ (out before : St P K C) (W : Fin N → K), exec I (do
      trsvLower tag (.const N) packed 0 rhs 0
      copyMapped tag (.const N) rhs outputAt xb xo false).run st = some out ∧
      before.store.writeBlock tag xb xo.eval (Array.ofFn W) = some out.store ∧
      before.store.shape = st.store.shape ∧
      (∀ q buf i, buf ≠ rhs → before.store.read q buf i = st.store.read q buf i) ∧
      IsLinearSolveErr (roundingFactor N (u tag)) A b (fun i => dec tag (W i)) := by
  have hcert := h.isLinearSolveRoutine_trsvLower I tag N (A.submatrix e e) hB hd
    packed rhs 0 0 hu (by simp [blockDisjoint, hpr])
  obtain ⟨before, Y, hr₁, hwy, herr⟩ := hcert.run st (b ∘ e) hM hb hwr
  have hshape := Store.shape_of_writeBlock_eq_some hwy
  have hread : ∀ i : Fin N, ∃ w,
      before.store.read tag rhs (outputAt (.var i)).eval = some w ∧
        dec tag w = dec tag (Y (e.symm i)) := fun i => by
    refine ⟨Y (e.symm i), ?_, rfl⟩
    have hr := Store.read_of_writeBlock_eq_some_of_lt hwy (j := (e.symm i).val)
      (by rw [Array.size_ofFn]; exact (e.symm i).isLt)
    simpa only [houtput i, IExp.eval_zero, Nat.zero_add, Array.getElem?_ofFn, (e.symm i).isLt,
      ↓reduceDIte] using hr
  obtain ⟨out, W, hr₂, hw, hdec⟩ := exec_copyMapped_const I h tag before N rhs outputAt
    xb xo false (fun i => dec tag (Y (e.symm i))) hread (hwx.of_shape_eq hshape) hrx
  refine ⟨out, before, W, ?_, hw, hshape, ?_, solve_error_reindex e herr (funext hdec)⟩
  · rw [exec_run_bind I (b := trsvLower tag (.const N) packed 0 rhs 0)
      (fun _ => rfl), hr₁, Option.bind_some]
    exact hr₂
  · intro q buf i hbr
    exact Store.read_of_writeBlock_eq_some_of_ne hwy (Or.inl hbr)

private theorem pop_pop_eq_of_frame (initial before : Store P K) (tag : P)
    (matrixWords vectorWords : Array (Option K))
    (hshape : before.shape = Store.shape ((initial.push (tag, matrixWords)).push
      (tag, vectorWords)))
    (hframe : ∀ q buf i, buf ≠ initial.size → buf ≠ initial.size + 1 →
      before.read q buf i = Store.read ((initial.push (tag, matrixWords)).push
        (tag, vectorWords)) q buf i) : before.pop.pop = initial := by
  have hsize : before.size = initial.size + 2 := by
    simpa only [Store.size_shape, Array.size_push, Nat.add_assoc] using
      congrArg Array.size hshape
  refine Store.ext_of_shape_eq ?_ fun q buf i => ?_
  · rw [Store.shape_pop, Store.shape_pop, hshape]
    simp only [Store.shape, Array.map_push, Array.pop_push]
  · by_cases hbuf : buf < initial.size
    · rw [Store.read_pop_of_lt (by simp only [Array.size_pop]; omega),
        Store.read_pop_of_lt (by omega), hframe q buf i (by omega) (by omega),
        Store.read_push_of_lt (by simp only [Array.size_push]; omega),
        Store.read_push_of_lt hbuf]
    · rw [Store.read_eq_none_of_size_le (by simp only [Array.size_pop]; omega),
        Store.read_eq_none_of_size_le (by omega)]

private theorem exec_solvePackedBody {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (tag : P)
    (initial : Store P K) (st : St P K C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (e : Fin N ≃ Fin N) (matrix : ℕ)
    (matrixAt : IExp ℕ → IExp ℕ → IExp ℕ) (xb : ℕ) (xo : IExp ℕ)
    (inputAt outputAt : IExp ℕ → IExp ℕ) (conjugate : Bool)
    (hinput : ∀ i : Fin N, (inputAt (.var i)).eval = xo.eval + e i)
    (houtput : ∀ i : Fin N, (outputAt (.var i)).eval = e.symm i)
    (hB : (A.submatrix e e).IsLowerTriangular) (hd : ∀ i, A (e i) (e i) ≠ 0)
    (hu : u tag < 1)
    (hM : ∀ i j : Fin N, ∃ w,
      initial.read tag matrix (matrixAt (.var i) (.var j)).eval = some w ∧
        dec tag w = A (e i) (e j))
    (hb : ReadsDecoded initial dec tag xb xo.eval b)
    (hwx : Writable initial tag xb xo.eval N)
    (hstore : st.store = (initial.push (tag, Array.replicate (N * N) none)).push
      (tag, Array.replicate N none)) :
    ∃ (out : St P K C) (W : Fin N → K), exec I (do
      copyMatrixMapped tag (.const N) matrix matrixAt initial.size conjugate
      copyMapped tag (.const N) xb inputAt (initial.size + 1) 0 false
      trsvLower tag (.const N) initial.size 0 (initial.size + 1) 0
      copyMapped tag (.const N) (initial.size + 1) outputAt xb xo false).run st = some out ∧
      initial.writeBlock tag xb xo.eval (Array.ofFn W) = some out.store.pop.pop ∧
      IsLinearSolveErr (roundingFactor N (u tag)) A b (fun i => dec tag (W i)) := by
  have hm : 0 < N → matrix < initial.size := fun hN => by
    obtain ⟨w, hw, -⟩ := hM ⟨0, hN⟩ ⟨0, hN⟩
    exact Store.lt_size_of_read_eq_some hw
  have hx : 0 < N → xb < initial.size := fun hN => hwx.lt_size hN
  have hM' : ∀ i j : Fin N, ∃ w,
      st.store.read tag matrix (matrixAt (.var i) (.var j)).eval = some w ∧
        dec tag w = (A.submatrix e e) i j := fun i j => by
    have him := hm (Nat.zero_lt_of_lt i.isLt)
    rw [hstore, Store.read_push_of_lt (by simp only [Array.size_push]; omega),
      Store.read_push_of_lt him]
    exact hM i j
  have hb' : ∀ i : Fin N, ∃ w,
      st.store.read tag xb (inputAt (.var i)).eval = some w ∧ dec tag w = (b ∘ e) i :=
    fun i => by
      have hix := hx (Nat.zero_lt_of_lt i.isLt)
      rw [hinput i, hstore, Store.read_push_of_lt (by simp only [Array.size_push]; omega),
        Store.read_push_of_lt hix]
      exact hb (e i)
  have hwM : Writable st.store tag initial.size 0 (N * N) := by
    rw [hstore]
    exact (writable_of_shape_eq rfl (Store.getElem?_shape_push_size initial tag (N * N))
      (by omega)).push (tag, Array.replicate N none)
  have hwr : Writable st.store tag (initial.size + 1) 0 N := by
    rw [hstore]
    apply writable_of_shape_eq rfl
    · simpa only [Array.size_push] using Store.getElem?_shape_push_size
        (initial.push (tag, Array.replicate (N * N) none)) tag N
    · omega
  obtain ⟨ready, hr₁, hshape₁, hpacked, hrhs, hframe₁⟩ := exec_loadOperands I h tag st N
    matrix matrixAt xb inputAt initial.size (initial.size + 1) conjugate
    (A.submatrix e e) (b ∘ e) hM' hb' hwM hwr
    (fun hN => Nat.ne_of_lt (hm hN)) (fun hN => Nat.ne_of_lt (hx hN))
    (fun hN => by have := hx hN; omega) (by omega)
  obtain ⟨out, before, W, hr₂, hwrite, hshape₂, hframe₂, herr⟩ := exec_solveCopy I h tag
    ready N A b e initial.size (initial.size + 1) xb xo outputAt houtput hB hd hu (by omega)
    (fun hN => by have := hx hN; omega) hpacked hrhs (hwr.of_shape_eq hshape₁)
    ((hwx.push _ |>.push _).of_shape_eq (hshape₁.trans (congrArg Store.shape hstore)))
  have hshape : before.store.shape = Store.shape ((initial.push
      (tag, Array.replicate (N * N) none)).push (tag, Array.replicate N none)) :=
    hshape₂.trans (hshape₁.trans (congrArg Store.shape hstore))
  have hpop := pop_pop_eq_of_frame initial before.store tag
    (Array.replicate (N * N) none) (Array.replicate N none) hshape
    (fun q buf i h₁ h₂ => by rw [hframe₂ q buf i h₂, hframe₁ q buf i h₁ h₂, hstore])
  have hsize : before.store.size = initial.size + 2 := by
    simpa only [Store.size_shape, Array.size_push, Nat.add_assoc] using
      congrArg Array.size hshape
  have hwrite₁ := Store.writeBlock_pop_of_lt hwrite
    (fun hp => by have := hx (by simpa only [Array.size_ofFn] using hp); omega)
  have hwrite₂ := Store.writeBlock_pop_of_lt hwrite₁ (fun hp => by
    have := hx (by simpa only [Array.size_ofFn] using hp)
    simp only [Array.size_pop]
    omega)
  refine ⟨out, W, ?_, hpop ▸ hwrite₂, herr⟩
  have hcomp : ExecutionComposable I (do
      copyMatrixMapped tag (.const N) matrix matrixAt initial.size conjugate
      copyMapped tag (.const N) xb inputAt (initial.size + 1) 0 false) :=
    (executionComposable_single I (fun _ => rfl)).bind
      (executionComposable_single I (fun _ => rfl))
  change exec I ((do
    copyMatrixMapped tag (.const N) matrix matrixAt initial.size conjugate
    copyMapped tag (.const N) xb inputAt (initial.size + 1) 0 false) >>= fun _ => do
    trsvLower tag (.const N) initial.size 0 (initial.size + 1) 0
    copyMapped tag (.const N) (initial.size + 1) outputAt xb xo false).run st = some out
  rw [hcomp, hr₁, Option.bind_some]
  exact hr₂

/-- A packed triangular adapter succeeds and writes only the original right-hand side block.
Its matrix and vector gather addresses must describe one simultaneous finite reindexing of
the desired system. The decoded packed matrix is lower triangular with nonzero diagonal, and
the standard model has all values in range and unit roundoff below one. Both workspace
allocations are released, including for the empty dimension. -/
theorem exec_solvePacked {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (tag : P)
    (st : St P K C) (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (e : Fin N ≃ Fin N) (matrix : ℕ) (matrixAt : IExp ℕ → IExp ℕ → IExp ℕ)
    (xb : ℕ) (xo : IExp ℕ) (inputAt outputAt : IExp ℕ → IExp ℕ) (conjugate : Bool)
    (hinput : ∀ i : Fin N, (inputAt (.var i)).eval = xo.eval + e i)
    (houtput : ∀ i : Fin N, (outputAt (.var i)).eval = e.symm i)
    (hB : (A.submatrix e e).IsLowerTriangular) (hd : ∀ i, A (e i) (e i) ≠ 0)
    (hu : u tag < 1)
    (hM : ∀ i j : Fin N, ∃ w,
      st.store.read tag matrix (matrixAt (.var i) (.var j)).eval = some w ∧
        dec tag w = A (e i) (e j))
    (hb : ReadsDecoded st.store dec tag xb xo.eval b)
    (hwx : Writable st.store tag xb xo.eval N) :
    ∃ (out : St P K C) (W : Fin N → K),
      exec I (solvePacked tag (.const N) matrix matrixAt xb xo inputAt outputAt conjugate).run
        st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn W) = some out.store ∧
      IsLinearSolveErr (roundingFactor N (u tag)) A b (fun i => dec tag (W i)) := by
  let Q : Store P K → Prop := fun s => ∃ W : Fin N → K,
    st.store.writeBlock tag xb xo.eval (Array.ofFn W) = some s ∧
    IsLinearSolveErr (roundingFactor N (u tag)) A b (fun i => dec tag (W i))
  have houter : ∀ σ : St P K C,
      σ.store = st.store.push (tag, Array.replicate (N * N) none) →
      ∃ out, exec I (.alloc tag (.const N) fun rhs => (do
        copyMatrixMapped tag (.const N) matrix matrixAt st.store.size conjugate
        copyMapped tag (.const N) xb inputAt rhs 0 false
        trsvLower tag (.const N) st.store.size 0 rhs 0
        copyMapped tag (.const N) rhs outputAt xb xo false).run) σ = some out ∧
        Q out.store.pop := by
    intro σ hσ
    have hsize : σ.store.size = st.store.size + 1 := by simp only [hσ, Array.size_push]
    apply exists_exec_alloc I tag (.const N) _ σ (fun s => Q s.pop)
    intro τ hτ
    have hstore : τ.store = (st.store.push (tag, Array.replicate (N * N) none)).push
        (tag, Array.replicate N none) := by simpa only [hσ, IExp.eval_const] using hτ
    obtain ⟨out, W, hr, hw, he⟩ := exec_solvePackedBody I h tag st.store τ N A b e matrix
      matrixAt xb xo inputAt outputAt conjugate hinput houtput hB hd hu hM hb hwx hstore
    exact ⟨out, by simpa only [hsize] using hr, W, hw, he⟩
  obtain ⟨out, hr, W, hw, he⟩ := exists_exec_alloc I tag
    (IExp.const N * IExp.const N) (fun packed => .alloc tag (.const N) fun rhs => (do
      copyMatrixMapped tag (.const N) matrix matrixAt packed conjugate
      copyMapped tag (.const N) xb inputAt rhs 0 false
      trsvLower tag (.const N) packed 0 rhs 0
      copyMapped tag (.const N) rhs outputAt xb xo false).run) st Q
    (fun σ hσ => houter σ (by simpa only [IExp.eval_mul, IExp.eval_const] using hσ))
  refine ⟨out, W, ?_, hw, he⟩
  change exec I (.seq (.alloc tag (IExp.const N * IExp.const N) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

end TriangularSolve

variable {dec : P → K → ℝ} {u : P → ℝ}

/-- The actual packed upper triangular solve is a certified linear solve. A real upper
triangular matrix with nonzero diagonal, the standard relative-error model with all values
in range and $u_p<1$ give componentwise backward allowance $(1-u_p)^{-N}-1$. The only net store
effect is the right-hand side output write. All operands are copied before it, so input and
output may overlap; source entries inside that output block are then overwritten.
[Higham2002, Theorem 8.5], applied to the reversed system. -/
theorem IsRelErrSem.isLinearSolveRoutine_trsvUpper
    (I : Interp P ι K C) (tag : P) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (N : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.IsUpperTriangular)
    (hd : ∀ i, T i i ≠ 0) (matrix xb : ℕ) (off xo : IExp ℕ) (hu : u tag < 1) :
    IsLinearSolveRoutine I dec tag T (roundingFactor N (u tag))
      (fun s => HoldsDecoded s dec tag matrix off.eval T) xb xo
      (trsvUpper tag (.const N) matrix off xb xo) where
  composable := executionComposable_trsvUpper I tag (.const N) matrix off xb xo
  run st b hM hb hw := by
    have hB : (T.submatrix Fin.rev Fin.rev).IsLowerTriangular :=
      fun i j hij => hT (i := i.rev) (j := j.rev) (Fin.rev_lt_rev.2 hij)
    exact TriangularSolve.exec_solvePacked I h tag st N T b Fin.revPerm matrix
      (fun i j => off + (IExp.const N - 1 - i) + IExp.const N * (IExp.const N - 1 - j))
      xb xo (fun i => xo + (IExp.const N - 1 - i)) (fun i => IExp.const N - 1 - i) false
      (fun i => by simp only [IExp.eval_add, IExp.eval_sub, IExp.eval_const, IExp.eval_var,
        IExp.eval_one, Fin.revPerm_apply, Fin.val_rev, Nat.sub_sub, Nat.add_comm])
      (fun i => by simp only [IExp.eval_sub, IExp.eval_const, IExp.eval_var, IExp.eval_one,
        Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_rev, Nat.sub_sub, Nat.add_comm])
      hB (fun i => hd i.rev) hu
      (fun i j => by
        simpa only [IExp.eval_add, IExp.eval_sub, IExp.eval_mul, IExp.eval_const,
          IExp.eval_var, IExp.eval_one, Fin.revPerm_apply, Fin.val_rev,
          Nat.sub_sub, Nat.add_comm] using hM i.rev j.rev)
      hb hw

/-- Solving the adjoint of a real lower triangular matrix is a certified linear solve.
Under the standard relative-error model with all values in range, nonzero diagonal and
$u_p<1$, the actual conjugating, transposing and reversing copies followed by lower
substitution have componentwise backward allowance $(1-u_p)^{-N}-1$. Only the right-hand side
block is overwritten; all matrix and vector workspace is scoped. Inputs may overlap the
eventual output block because both operands are packed before that write.
[Higham2002, Theorem 8.5], applied to the reversed adjoint system. -/
theorem IsRelErrSem.isLinearSolveRoutine_trsvLowerAdjoint
    (I : Interp P ι K C) (tag : P) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (N : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.IsLowerTriangular)
    (hd : ∀ i, T i i ≠ 0) (matrix xb : ℕ) (off xo : IExp ℕ) (hu : u tag < 1) :
    IsLinearSolveRoutine I dec tag Tᴴ (roundingFactor N (u tag))
      (fun s => HoldsDecoded s dec tag matrix off.eval T) xb xo
      (trsvLowerAdjoint tag (.const N) matrix off xb xo) where
  composable := executionComposable_trsvLowerAdjoint I tag (.const N) matrix off xb xo
  run st b hM hb hw := by
    have hU : Tᴴ.IsUpperTriangular := hT.conjTranspose
    have hB : (Tᴴ.submatrix Fin.rev Fin.rev).IsLowerTriangular :=
      fun i j hij => hU (i := i.rev) (j := j.rev) (Fin.rev_lt_rev.2 hij)
    exact TriangularSolve.exec_solvePacked I h tag st N Tᴴ b Fin.revPerm matrix
      (fun i j => off + (IExp.const N - 1 - j) + IExp.const N * (IExp.const N - 1 - i))
      xb xo (fun i => xo + (IExp.const N - 1 - i)) (fun i => IExp.const N - 1 - i) true
      (fun i => by simp only [IExp.eval_add, IExp.eval_sub, IExp.eval_const, IExp.eval_var,
        IExp.eval_one, Fin.revPerm_apply, Fin.val_rev, Nat.sub_sub, Nat.add_comm])
      (fun i => by simp only [IExp.eval_sub, IExp.eval_const, IExp.eval_var, IExp.eval_one,
        Fin.revPerm_symm, Fin.revPerm_apply, Fin.val_rev, Nat.sub_sub, Nat.add_comm]) hB
      (fun (i : Fin N) => by
        simpa only [Fin.revPerm_apply, Matrix.conjTranspose_apply, star_trivial]
          using (hd i.rev)) hu
      (fun i j => by
        simpa only [IExp.eval_add, IExp.eval_sub, IExp.eval_mul, IExp.eval_const,
          IExp.eval_var, IExp.eval_one, Fin.revPerm_apply, Fin.val_rev,
          Matrix.conjTranspose_apply, star_trivial, Nat.sub_sub, Nat.add_comm]
          using hM j.rev i.rev) hb hw

/-- Solving the adjoint of a real upper triangular matrix is a certified linear solve.
Under the standard relative-error model with all values in range, nonzero diagonal and
$u_p<1$, actual conjugating and transposing copies followed by lower substitution give
componentwise backward allowance $(1-u_p)^{-N}-1$. Only the right-hand side block is
overwritten, and both workspace blocks are scoped. Inputs may overlap the eventual output.
[Higham2002, Theorem 8.5], applied to the adjoint system. -/
theorem IsRelErrSem.isLinearSolveRoutine_trsvUpperAdjoint
    (I : Interp P ι K C) (tag : P) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (N : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.IsUpperTriangular)
    (hd : ∀ i, T i i ≠ 0) (matrix xb : ℕ) (off xo : IExp ℕ) (hu : u tag < 1) :
    IsLinearSolveRoutine I dec tag Tᴴ (roundingFactor N (u tag))
      (fun s => HoldsDecoded s dec tag matrix off.eval T) xb xo
      (trsvUpperAdjoint tag (.const N) matrix off xb xo) where
  composable := executionComposable_trsvUpperAdjoint I tag (.const N) matrix off xb xo
  run st b hM hb hw := by
    exact TriangularSolve.exec_solvePacked I h tag st N Tᴴ b (Equiv.refl _) matrix
      (fun i j => off + j + IExp.const N * i) xb xo (fun i => xo + i) id true
      (fun i => by simp only [IExp.eval_add, IExp.eval_var, Equiv.refl_apply])
      (fun i => by simp only [id_eq, IExp.eval_var, Equiv.refl_symm, Equiv.refl_apply])
      (by
        intro i j hij
        simpa only [Matrix.submatrix_apply, Equiv.refl_apply, Matrix.conjTranspose_apply,
          star_trivial] using hT (i := j) (j := i) hij)
      (fun (i : Fin N) => by
        simpa only [Equiv.refl_apply, Matrix.conjTranspose_apply, star_trivial] using (hd i)) hu
      (fun i j => by
        simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_var,
          Equiv.refl_apply, Matrix.conjTranspose_apply, star_trivial] using hM j i) hb hw

private theorem exec_exact_of_certificate (I : Interp P ι ℝ C) (tag : P) (N : ℕ)
    (T : Matrix (Fin N) (Fin N) ℝ) (pre : Store P ℝ → Prop) (xb : ℕ) (xo : IExp ℕ)
    (routine : Builder P ι ℕ ℕ Unit)
    (hcert : IsLinearSolveRoutine I (fun _ x => x) tag T 0 pre xb xo routine)
    (st : St P ℝ C) (b : Fin N → ℝ) (hp : pre st.store)
    (hb : ∀ i : Fin N, st.store.read tag xb (xo.eval + i) = some (b i)) :
    ∃ (out : St P ℝ C) (x : Fin N → ℝ), exec I routine.run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store ∧ T *ᵥ x = b := by
  have hw : Writable st.store tag xb xo.eval N := fun i hi =>
    Store.exists_getElem?_shape_of_read_eq_some (hb ⟨i, hi⟩)
  obtain ⟨out, W, hr, hwrite, he⟩ := hcert.run st b hp (fun i => ⟨b i, hb i, rfl⟩) hw
  exact ⟨out, W, hr, hwrite, he.mulVec_eq⟩

/-- Under exact real arithmetic, stored upper triangular coefficients with nonzero diagonal
and a stored right-hand side imply successful execution of the actual packed upper solve.
Its output solves the original system exactly, and the only net store effect is that output
vector block write. Operands may overlap, arbitrary offsets and the empty dimension are
allowed, and charges are arbitrary. [GolubVanLoan2013, §3.1]. -/
theorem exec_trsvUpper (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P)
    (N : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.IsUpperTriangular)
    (hd : ∀ i, T i i ≠ 0) (matrix xb : ℕ) (off xo : IExp ℕ) (st : St P ℝ C)
    (b : Fin N → ℝ) (hM : Holds st.store tag matrix off.eval T)
    (hb : ∀ i : Fin N, st.store.read tag xb (xo.eval + i) = some (b i)) :
    ∃ (out : St P ℝ C) (x : Fin N → ℝ),
      exec I (trsvUpper tag (.const N) matrix off xb xo).run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store ∧ T *ᵥ x = b := by
  have h : IsRelErrSem (fun _ => 0) (fun _ x => x) (fun _ _ => True) I.sem := by
    rw [hI]
    exact isRelErrSem_exactSem
  have hcert := h.isLinearSolveRoutine_trsvUpper I tag N T hT hd matrix xb off xo (by norm_num)
  have hcert₀ : IsLinearSolveRoutine I (fun _ x => x) tag T 0
      (fun s => HoldsDecoded s (fun _ x => x) tag matrix off.eval T) xb xo
      (trsvUpper tag (.const N) matrix off xb xo) := by
    simpa only [roundingFactor, sub_zero, one_pow, inv_one, sub_self] using hcert
  exact exec_exact_of_certificate I tag N T _ xb xo _ hcert₀ st b
    (fun i j => ⟨T i j, hM i j, rfl⟩) hb

/-- Under exact real arithmetic, stored lower triangular coefficients with nonzero diagonal
and a stored right-hand side imply successful execution of the actual adjoint solve. Its
output solves the adjoint system exactly, and only the output vector block is overwritten.
The adapter executes conjugation instructions and transposed copy addresses; operands
may overlap and the dimension may be zero. [GolubVanLoan2013, §3.1]. -/
theorem exec_trsvLowerAdjoint (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P)
    (N : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.IsLowerTriangular)
    (hd : ∀ i, T i i ≠ 0) (matrix xb : ℕ) (off xo : IExp ℕ) (st : St P ℝ C)
    (b : Fin N → ℝ) (hM : Holds st.store tag matrix off.eval T)
    (hb : ∀ i : Fin N, st.store.read tag xb (xo.eval + i) = some (b i)) :
    ∃ (out : St P ℝ C) (x : Fin N → ℝ),
      exec I (trsvLowerAdjoint tag (.const N) matrix off xb xo).run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store ∧ Tᴴ *ᵥ x = b := by
  have h : IsRelErrSem (fun _ => 0) (fun _ x => x) (fun _ _ => True) I.sem := by
    rw [hI]
    exact isRelErrSem_exactSem
  have hcert := h.isLinearSolveRoutine_trsvLowerAdjoint I tag N T hT hd matrix xb off xo
    (by norm_num)
  have hcert₀ : IsLinearSolveRoutine I (fun _ x => x) tag Tᴴ 0
      (fun s => HoldsDecoded s (fun _ x => x) tag matrix off.eval T) xb xo
      (trsvLowerAdjoint tag (.const N) matrix off xb xo) := by
    simpa only [roundingFactor, sub_zero, one_pow, inv_one, sub_self] using hcert
  exact exec_exact_of_certificate I tag N Tᴴ _ xb xo _ hcert₀ st b
    (fun i j => ⟨T i j, hM i j, rfl⟩) hb

/-- Under exact real arithmetic, stored upper triangular coefficients with nonzero diagonal
and a stored right-hand side imply successful execution of the actual adjoint solve. Its
output solves the adjoint system exactly, and only the output vector block is overwritten.
Operands may overlap, the dimension may be zero, and both packing allocations are scoped.
[GolubVanLoan2013, §3.1]. -/
theorem exec_trsvUpperAdjoint (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P)
    (N : ℕ) (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.IsUpperTriangular)
    (hd : ∀ i, T i i ≠ 0) (matrix xb : ℕ) (off xo : IExp ℕ) (st : St P ℝ C)
    (b : Fin N → ℝ) (hM : Holds st.store tag matrix off.eval T)
    (hb : ∀ i : Fin N, st.store.read tag xb (xo.eval + i) = some (b i)) :
    ∃ (out : St P ℝ C) (x : Fin N → ℝ),
      exec I (trsvUpperAdjoint tag (.const N) matrix off xb xo).run st = some out ∧
      st.store.writeBlock tag xb xo.eval (Array.ofFn x) = some out.store ∧ Tᴴ *ᵥ x = b := by
  have h : IsRelErrSem (fun _ => 0) (fun _ x => x) (fun _ _ => True) I.sem := by
    rw [hI]
    exact isRelErrSem_exactSem
  have hcert := h.isLinearSolveRoutine_trsvUpperAdjoint I tag N T hT hd matrix xb off xo
    (by norm_num)
  have hcert₀ : IsLinearSolveRoutine I (fun _ x => x) tag Tᴴ 0
      (fun s => HoldsDecoded s (fun _ x => x) tag matrix off.eval T) xb xo
      (trsvUpperAdjoint tag (.const N) matrix off xb xo) := by
    simpa only [roundingFactor, sub_zero, one_pow, inv_one, sub_self] using hcert
  exact exec_exact_of_certificate I tag N Tᴴ _ xb xo _ hcert₀ st b
    (fun i j => ⟨T i j, hM i j, rfl⟩) hb

end NLAlib.Computation
