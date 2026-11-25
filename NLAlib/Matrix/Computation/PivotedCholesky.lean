/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PivotedCholeskyInitialize

/-!
# Symmetric diagonal-pivoted semidefinite Cholesky

The actual maximal active diagonal selects one symmetric residual exchange and a factor
row exchange per step. Singular positive semidefinite inputs are supported exactly. The
actual absolute pivot log determines the same permutation on both input axes.

## Main results

* `NLAlib.Computation.exec_pivotedCholesky`: exact PSD success and the two complete output writes.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder
open scoped Matrix

/-- Compute a diagonally pivoted Cholesky factor and its absolute current-position swap
log. The input is copied first, all factor words are initialized, and each active diagonal
is scanned with stride one greater than the matrix order. Zero pivots use zero columns
without division. The residual is scoped. No tolerance or floating-point rank is inferred.
[GolubVanLoan2013, §4.2]. -/
def pivotedCholesky {P ι VB VI : Type} (tag : P) (n : IExp VI)
    (A : VB) (ao : IExp VI) (L : VB) (lo : IExp VI) (H : VB) (ho : IExp VI) :
    Builder P ι VB VI Unit := scope do
  let R ← alloc tag (n * n)
  pivotedCholeskyBody tag n A R L H ao lo ho

variable {P ι : Type} [DecidableEq P]

/-- The full diagonal-pivoted Cholesky routine releases its residual before continuing. -/
theorem executionComposable_pivotedCholesky {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (tag : P) (n : IExp ℕ) (A : ℕ) (ao : IExp ℕ)
    (L : ℕ) (lo : IExp ℕ) (H : ℕ) (ho : IExp ℕ) :
    ExecutionComposable I (pivotedCholesky tag n A ao L lo H ho) :=
  executionComposable_single I (fun _ => rfl)

/-- At dimension zero the full routine succeeds for arbitrary word semantics and invalid
handles, including handles equal to the fresh residual index. Its scoped store is restored. -/
theorem exec_pivotedCholesky_of_zero {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (tag : P) (st : St P K C) (n : IExp ℕ)
    (A : ℕ) (ao : IExp ℕ) (L : ℕ) (lo : IExp ℕ) (H : ℕ) (ho : IExp ℕ)
    (hn : n.eval = 0) :
    ∃ out, exec I (pivotedCholesky tag n A ao L lo H ho).run st = some out ∧
      out.store = st.store := by
  obtain ⟨out, hr, hs⟩ := exists_exec_alloc I tag (n * n)
    (fun R => (pivotedCholeskyBody tag n A R L H ao lo ho).run) st
    (fun s => s = st.store) (by
      intro σ hσ
      refine ⟨σ, PivotedCholesky.exec_emptyBody I tag σ n A st.store.size L H ao lo ho hn, ?_⟩
      rw [hσ]
      exact Array.pop_push)
  refine ⟨out, ?_, hs⟩
  change exec I (.seq (.alloc tag (n * n) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

/-- Exact diagonal-pivoted Cholesky succeeds on every stored positive semidefinite real
matrix, including singular and empty inputs. The only net writes are the full factor and
actual absolute pivot log. Their decoded swap permutation simultaneously reindexes both input
axes and gives the exact Gram factorization with a nonnegative factor diagonal. Source may
overlap either output, since it is copied first. Distinct factor and history buffers retain
one another; empty inputs need no valid handle. [GolubVanLoan2013, §4.2]. -/
theorem exec_pivotedCholesky (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A : ℕ) (ao : IExp ℕ)
    (L : ℕ) (lo : IExp ℕ) (H : ℕ) (ho : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : M.PosSemidef)
    (hinput : Holds st.store tag A ao.eval M)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval))
    (hH : Writable st.store tag H ho.eval n.eval) (hLH : L ≠ H) :
    ∃ (out : St P ℝ (OpCount P ι)) (p : Fin n.eval → Fin n.eval),
      exec I (pivotedCholesky tag n A ao L lo H ho).run st = some out ∧
      st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (H, ho.eval, n.eval)]
        [flatten (choleskyLower
          (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation p n.eval))),
          Array.ofFn (fun j => ((p j).val : ℝ))] = some out.store ∧
      (∀ j, j ≤ p j) ∧
      Holds out.store tag L lo.eval (choleskyLower
        (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation p n.eval))) ∧
      (∀ j : Fin n.eval, out.store.read tag H (ho.eval + j) = some ((p j).val : ℝ)) ∧
      (choleskyLower
        (M.submatrix (luPivotPermutation p n.eval)
          (luPivotPermutation p n.eval))).IsLowerTriangular ∧
      (∀ i, 0 ≤ choleskyLower
        (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation p n.eval)) i i) ∧
      M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation p n.eval) =
        choleskyLower (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation p n.eval)) *
          (choleskyLower
            (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation p n.eval)))ᴴ := by
  let Q : Store P ℝ → Prop := fun s => ∃ p : Fin n.eval → Fin n.eval,
    st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (H, ho.eval, n.eval)]
      [flatten (choleskyLower
        (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation p n.eval))),
        Array.ofFn (fun j => ((p j).val : ℝ))] = some s ∧ (∀ j, j ≤ p j) ∧
      Holds s tag L lo.eval (choleskyLower
        (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation p n.eval))) ∧
      (∀ j : Fin n.eval, s.read tag H (ho.eval + j) = some ((p j).val : ℝ))
  obtain ⟨out, hr, p, hw, hp, hLF, hlog⟩ := exists_exec_alloc I tag (n * n)
    (fun R => (pivotedCholeskyBody tag n A R L H ao lo ho).run) st Q (by
      intro σ hσ
      obtain ⟨final, he, hs⟩ := PivotedCholesky.exec_body I hI hc tag st.store σ n A L H
        ao lo ho M hM hinput hL hH hLH (by simpa only [IExp.eval_mul] using hσ)
      obtain ⟨p, hw, hp, hLF, hlog⟩ :=
        PivotedCholesky.State.writeBlocks_pop (hσ ▸ hs) hL hH hLH
      exact ⟨final, he, p, hw, hp, hLF, hlog⟩)
  have hPSD := hM.submatrix (luPivotPermutation p n.eval)
  refine ⟨out, p, ?_, hw, hp, hLF, hlog, isLowerTriangular_choleskyLower _,
    hPSD.isHermitian.choleskyLower_apply_self_nonneg,
    hPSD.eq_choleskyLower_mul_conjTranspose⟩
  change exec I (.seq (.alloc tag (n * n) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

end NLAlib.Computation
