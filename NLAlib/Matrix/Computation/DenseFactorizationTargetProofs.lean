/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.DenseFactorizationTargets
public import NLAlib.Matrix.Computation.DenseFactorizationTargetSupport
public import NLAlib.Matrix.Computation.DenseFactorizationCounts

/-!
# Stored-entry dense factorization guarantees

The seven approved targets use the actual first-order factorization trees under exact real
arithmetic. The proofs establish successful execution, the specified factors and pivot logs,
source and shape preservation, independent closed operation budgets, and peak memory including
caller buffers. Each target includes order zero. Identity inputs establish nonvacuity at every
order, including the unpivoted numerical input domains.

## Main results

* `NLAlib.Computation.storedEntriesDenseLU`: canonical-pivot LU.
* `NLAlib.Computation.storedEntriesDensePLU`: actual partial pivoting.
* `NLAlib.Computation.storedEntriesDensePLUQ`: actual complete pivoting with two logs.
* `NLAlib.Computation.storedEntriesDenseScaledPLU`: original-row-scale partial pivoting.
* `NLAlib.Computation.storedEntriesDenseCholesky`: positive definite Cholesky.
* `NLAlib.Computation.storedEntriesDenseSemidefiniteCholesky`: guarded semidefinite Cholesky.
* `NLAlib.Computation.storedEntriesDenseLDL`: Hermitian scalar LDL.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

open DenseFactorizationTarget

/-- **Stored-entry LU.** On the canonical nonzero-pivot input domain, the actual tree returns
canonical unit lower and upper factors.

The output $\mathsf{luFactor}(\mathbf{A})$ is computed under exact real arithmetic. The target
includes order zero and preserves the declared source and shape. Its independent closed
operation budget is $1024(N+1)^3$ for each operation kind. Peak memory, including caller
buffers and scratch, is at most $4N^2+2N+3$ cells.
No printed source.

Result: dense-lu-stored-program -/
theorem storedEntriesDenseLU : StoredEntriesDenseLU := by
  intro N n hn x vals ξ
  have hn' : n = fun _ => 0 := funext hn
  subst n
  let bufs := luInputs N (fun _ => 0) x
  let st : State := inputState () (List.ofFn bufs)
  let I := storedInterp (ι := Empty) 0 vals ξ ()
  have hA := holds_inputState (C := OpCount Unit Empty) () bufs (0 : Fin 3) x.val rfl
  have hL := writable_inputState (C := OpCount Unit Empty) () bufs (1 : Fin 3)
    (N * N) (by simp [bufs, luInputs])
  have hU := writable_inputState (C := OpCount Unit Empty) () bufs (2 : Fin 3)
    (N * N) (by simp [bufs, luInputs])
  obtain ⟨out, hr, hw, hLf, hUf, hf, hsource⟩ :=
    exec_luFactor I rfl (fun _ => rfl) () st (.const N) 0 1 2 0 0 0
      x.val hA x.property hL hU (fun _ => by omega) (fun _ => by omega) (by omega)
  have htree : Prog.toStmt (luResourceTree (ι := Empty) ()) N (fun _ => 0) =
      (luFactor () (.const N) 0 1 2 0 0 0).run := rfl
  have hrun : Prog.exec I (luResourceTree (ι := Empty) ()) N (fun _ => 0)
      st = some out := by
    rw [Prog.exec_eq_exec_toStmt, htree]
    exact hr
  have hpost : LUPost N (fun _ => 0) x vals ξ out :=
    ⟨hLf, hUf, hf, hsource, Store.shape_of_writeBlocks_eq_some hw⟩
  have hcaller : ((List.ofFn bufs).map Array.size).sum ≤ 3 * N * N := by
    simp [bufs, luInputs, List.ofFn_succ, size_flatten, Nat.mul_assoc]
    omega
  have hspace : (Prog.staticCost (luResourceTree (ι := Empty) ())
      (fun k => Finsupp.single k 1) (fun _ => 0) N (fun _ => 0)).cells () ≤
      N * N + 2 * N + 3 := by
    have henv : Fin.cons N (fun _ : Fin 3 => 0) = ![N, 0, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact luFactorResources_cells_le _ _ () N 0 0 0
  have hcount : (Prog.staticCost (luResourceTree (ι := Empty) ())
      (fun k => Finsupp.single k 1) (fun _ => 0) N (fun _ => 0)).count ≤
      closedCountBudget N := by
    have henv : Fin.cons N (fun _ : Fin 3 => 0) = ![N, 0, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact luFactorResources_count_le N
  exact runsWithin_of_exec (luResourceTree ()) N (fun _ => 0) bufs vals ξ
    (3 * N * N) (N * N + 2 * N + 3) hcaller hspace hcount hrun hpost

/-- Every order admits the identity in the canonical-pivot LU domain. -/
theorem storedEntriesDenseLU_nonVacuous : StoredEntriesDenseLUNonVacuous := by
  intro N₀
  exact ⟨N₀, (fun _ => 0), le_rfl, (fun _ => rfl), ⟨⟨(1 : Mat N₀), (fun k => ne_of_gt
      ((Matrix.PosDef.one : (1 : Mat N₀).PosDef).gaussState_apply_self_pos k))⟩⟩⟩

/-- **Stored-entry PLU.** For every real square input, including singular matrices, the actual
partial-pivot tree returns its pivot log and row-permuted factors.

The output $\mathsf{pluFactor}(\mathbf{A})$ is computed under exact real arithmetic. The target
includes order zero and preserves the declared source and shape. Its independent closed
operation budget is $1024(N+1)^3$ for each operation kind. Peak memory, including caller
buffers and scratch, is at most $4N^2+3N+7$ cells.
No printed source.

Result: partial-pivoted-factorization-budget -/
theorem storedEntriesDensePLU : StoredEntriesDensePLU := by
  intro N n hn A vals ξ
  have hn' : n = fun _ => 0 := funext hn
  subst n
  change Mat N at A
  let bufs := pluInputs N (fun _ => 0) A
  let st : State := inputState () (List.ofFn bufs)
  let I := storedInterp (ι := Empty) 0 vals ξ ()
  have hA := holds_inputState (C := OpCount Unit Empty) () bufs (0 : Fin 4) A rfl
  have hL := writable_inputState (C := OpCount Unit Empty) () bufs (1 : Fin 4)
    (N * N) (by simp [bufs, pluInputs])
  have hU := writable_inputState (C := OpCount Unit Empty) () bufs (2 : Fin 4)
    (N * N) (by simp [bufs, pluInputs])
  have hH := writable_inputState (C := OpCount Unit Empty) () bufs (3 : Fin 4)
    N (by simp [bufs, pluInputs])
  obtain ⟨out, p, hr, hw, hp, hf, -, hLf, hUf, hlog, hsource⟩ :=
    exec_pluFactor I rfl (fun _ => rfl) () st (.const N)
      0 1 2 3 0 0 0 0 A hA hL hU hH (by omega) (by omega) (by omega)
      (fun _ => by omega) (fun _ => by omega) (fun _ => by omega)
  have htree : Prog.toStmt (pluResourceTree (ι := Empty) ()) N (fun _ => 0) =
      (pluFactor () (.const N) 0 1 2 3 0 0 0 0).run := rfl
  have hrun : Prog.exec I (pluResourceTree (ι := Empty) ()) N (fun _ => 0)
      st = some out := by
    rw [Prog.exec_eq_exec_toStmt, htree]
    exact hr
  have hpost : PLUPost N (fun _ => 0) A vals ξ out :=
    ⟨p, hlog, hp, hLf, hUf, hf, hsource, Store.shape_of_writeBlocks_eq_some hw⟩
  have hcaller : ((List.ofFn bufs).map Array.size).sum ≤ 3 * N * N + N := by
    simp [bufs, pluInputs, List.ofFn_succ, size_flatten, Nat.mul_assoc]
    omega
  have hspace : (Prog.staticCost (pluResourceTree (ι := Empty) ())
      (fun k => Finsupp.single k 1) (fun _ => 0) N (fun _ => 0)).cells () ≤
      N * N + 2 * N + 7 := by
    have henv : Fin.cons N (fun _ : Fin 4 => 0) = ![N, 0, 0, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact pluFactorResources_cells_le _ _ () N 0 0 0 0
  have hcount : (Prog.staticCost (pluResourceTree (ι := Empty) ())
      (fun k => Finsupp.single k 1) (fun _ => 0) N (fun _ => 0)).count ≤
      closedCountBudget N := by
    have henv : Fin.cons N (fun _ : Fin 4 => 0) = ![N, 0, 0, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact pluFactorResources_count_le N
  exact runsWithin_of_exec (pluResourceTree ()) N (fun _ => 0) bufs vals ξ
    (3 * N * N + N) (N * N + 2 * N + 7) hcaller hspace hcount hrun hpost

/-- Arbitrarily large identity inputs witness nonvacuity of the partial-pivoted target. -/
theorem storedEntriesDensePLU_nonVacuous : StoredEntriesDensePLUNonVacuous := by
  intro N₀
  exact ⟨N₀, (fun _ => 0), le_rfl, (fun _ => rfl), ⟨(1 : Mat N₀)⟩⟩

/-- **Stored-entry PLUQ.** For every real square input, the actual complete-pivot tree returns
independent row and column logs and corresponding factors.

The output $\mathsf{pluqFactor}(\mathbf{A})$ is computed under exact real arithmetic. The target
includes order zero and preserves the declared source and shape. Its independent closed
operation budget is $1024(N+1)^3$ for each operation kind. Peak memory, including caller
buffers and scratch, is at most $4N^2+4N+7$ cells.
No printed source.

Result: complete-pivoting-stored-entries -/
theorem storedEntriesDensePLUQ : StoredEntriesDensePLUQ := by
  intro N n hn A vals ξ
  have hn' : n = fun _ => 0 := funext hn
  subst n
  change Mat N at A
  let bufs := pluqInputs N (fun _ => 0) A
  let st : State := inputState () (List.ofFn bufs)
  let I := storedInterp (ι := Empty) 0 vals ξ ()
  have hA := holds_inputState (C := OpCount Unit Empty) () bufs (0 : Fin 5) A rfl
  have hL := writable_inputState (C := OpCount Unit Empty) () bufs (1 : Fin 5)
    (N * N) (by simp [bufs, pluqInputs])
  have hU := writable_inputState (C := OpCount Unit Empty) () bufs (2 : Fin 5)
    (N * N) (by simp [bufs, pluqInputs])
  have hR := writable_inputState (C := OpCount Unit Empty) () bufs (3 : Fin 5)
    N (by simp [bufs, pluqInputs])
  have hC := writable_inputState (C := OpCount Unit Empty) () bufs (4 : Fin 5)
    N (by simp [bufs, pluqInputs])
  obtain ⟨out, p, q, hr, hw, hp, hq, hf, -, hLf, hUf, hrow, hcol, hsource⟩ :=
    exec_pluqFactor I rfl (fun _ => rfl) () st (.const N)
      0 1 2 3 4 0 0 0 0 0 A hA hL hU hR hC
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun _ => by omega) (fun _ => by omega) (fun _ => by omega) (fun _ => by omega)
  have htree : Prog.toStmt (pluqResourceTree (ι := Empty) ()) N (fun _ => 0) =
      (pluqFactor () (.const N) 0 1 2 3 4 0 0 0 0 0).run := rfl
  have hrun : Prog.exec I (pluqResourceTree (ι := Empty) ()) N (fun _ => 0)
      st = some out := by
    rw [Prog.exec_eq_exec_toStmt, htree]
    exact hr
  have hpost : PLUQPost N (fun _ => 0) A vals ξ out :=
    ⟨p, q, hrow, hcol, hp, hq, hLf, hUf, hf, hsource,
      Store.shape_of_writeBlocks_eq_some hw⟩
  have hcaller : ((List.ofFn bufs).map Array.size).sum ≤ 3 * N * N + 2 * N := by
    simp [bufs, pluqInputs, List.ofFn_succ, size_flatten, Nat.mul_assoc]
    omega
  have hspace : (Prog.staticCost (pluqResourceTree (ι := Empty) ())
      (fun k => Finsupp.single k 1) (fun _ => 0) N (fun _ => 0)).cells () ≤
      N * N + 2 * N + 7 := by
    have henv : Fin.cons N (fun _ : Fin 5 => 0) = ![N, 0, 0, 0, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact pluqFactorResources_cells_le _ _ () N 0 0 0 0 0
  have hcount : (Prog.staticCost (pluqResourceTree (ι := Empty) ())
      (fun k => Finsupp.single k 1) (fun _ => 0) N (fun _ => 0)).count ≤
      closedCountBudget N := by
    have henv : Fin.cons N (fun _ : Fin 5 => 0) = ![N, 0, 0, 0, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact pluqFactorResources_count_le N
  exact runsWithin_of_exec (pluqResourceTree ()) N (fun _ => 0) bufs vals ξ
    (3 * N * N + 2 * N) (N * N + 2 * N + 7) hcaller hspace hcount hrun hpost

/-- Arbitrarily large identity inputs witness nonvacuity of the complete-pivoted target. -/
theorem storedEntriesDensePLUQ_nonVacuous : StoredEntriesDensePLUQNonVacuous := by
  intro N₀
  exact ⟨N₀, (fun _ => 0), le_rfl, (fun _ => rfl), ⟨(1 : Mat N₀)⟩⟩

/-- **Stored-entry ScaledPLU.** For every real square input, the actual original-row-scale pivot
tree returns its row log and corresponding factors.

The output $\mathsf{scaledPluFactor}(\mathbf{A})$ is computed under exact real arithmetic. The
target
includes order zero and preserves the declared source and shape. Its independent closed
operation budget is $1024(N+1)^3$ for each operation kind. Peak memory, including caller
buffers and scratch, is at most $4N^2+4N+7$ cells.
No printed source.

Result: scaled-row-factorization-program -/
theorem storedEntriesDenseScaledPLU : StoredEntriesDenseScaledPLU := by
  intro N n hn A vals ξ
  have hn' : n = fun _ => 0 := funext hn
  subst n
  change Mat N at A
  let bufs := pluInputs N (fun _ => 0) A
  let st : State := inputState () (List.ofFn bufs)
  let I := storedInterp (ι := Empty) 0 vals ξ ()
  have hA := holds_inputState (C := OpCount Unit Empty) () bufs (0 : Fin 4) A rfl
  have hL := writable_inputState (C := OpCount Unit Empty) () bufs (1 : Fin 4)
    (N * N) (by simp [bufs, pluInputs])
  have hU := writable_inputState (C := OpCount Unit Empty) () bufs (2 : Fin 4)
    (N * N) (by simp [bufs, pluInputs])
  have hH := writable_inputState (C := OpCount Unit Empty) () bufs (3 : Fin 4)
    N (by simp [bufs, pluInputs])
  obtain ⟨out, p, hr, hw, hp, hf, hLf, hUf, hlog, hsource⟩ :=
    exec_scaledPluFactor I rfl (fun _ => rfl) () st (.const N)
      0 1 2 3 0 0 0 0 A hA hL hU hH (by omega) (by omega) (by omega)
      (fun _ => by omega) (fun _ => by omega) (fun _ => by omega)
  have htree : Prog.toStmt (scaledPluResourceTree (ι := Empty) ()) N (fun _ => 0) =
      (scaledPluFactor () (.const N) 0 1 2 3 0 0 0 0).run := rfl
  have hrun : Prog.exec I (scaledPluResourceTree (ι := Empty) ()) N (fun _ => 0)
      st = some out := by
    rw [Prog.exec_eq_exec_toStmt, htree]
    exact hr
  have hpost : PLUPost N (fun _ => 0) A vals ξ out :=
    ⟨p, hlog, hp, hLf, hUf, hf, hsource, Store.shape_of_writeBlocks_eq_some hw⟩
  have hcaller : ((List.ofFn bufs).map Array.size).sum ≤ 3 * N * N + N := by
    simp [bufs, pluInputs, List.ofFn_succ, size_flatten, Nat.mul_assoc]
    omega
  have hspace : (Prog.staticCost (scaledPluResourceTree (ι := Empty) ())
      (fun k => Finsupp.single k 1) (fun _ => 0) N (fun _ => 0)).cells () ≤
      N * N + 3 * N + 7 := by
    have henv : Fin.cons N (fun _ : Fin 4 => 0) = ![N, 0, 0, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact scaledPluFactorResources_cells_le _ _ () N 0 0 0 0
  have hcount : (Prog.staticCost (scaledPluResourceTree (ι := Empty) ())
      (fun k => Finsupp.single k 1) (fun _ => 0) N (fun _ => 0)).count ≤
      closedCountBudget N := by
    have henv : Fin.cons N (fun _ : Fin 4 => 0) = ![N, 0, 0, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact scaledPluFactorResources_count_le N
  exact runsWithin_of_exec (scaledPluResourceTree ()) N (fun _ => 0) bufs vals ξ
    (3 * N * N + N) (N * N + 3 * N + 7) hcaller hspace hcount hrun hpost

/-- Identity inputs also witness nonvacuity of the fixed-scale all-input target. -/
theorem storedEntriesDenseScaledPLU_nonVacuous : StoredEntriesDenseScaledPLUNonVacuous := by
  intro N₀
  exact ⟨N₀, (fun _ => 0), le_rfl, (fun _ => rfl), ⟨(1 : Mat N₀)⟩⟩

/-- Every order admits an SPD identity input at zero offsets. -/
theorem storedEntriesDenseCholesky_nonVacuous : StoredEntriesDenseCholeskyNonVacuous := by
  intro N₀
  exact ⟨N₀, fun _ => 0, le_rfl, fun _ => rfl, ⟨⟨1, Matrix.PosDef.one⟩⟩⟩

/-- Every order admits a PSD identity input at zero offsets. -/
theorem storedEntriesDenseSemidefiniteCholesky_nonVacuous :
    StoredEntriesDenseSemidefiniteCholeskyNonVacuous := by
  intro N₀
  exact ⟨N₀, fun _ => 0, le_rfl, fun _ => rfl, ⟨⟨1, Matrix.PosDef.one.posSemidef⟩⟩⟩

/-- Every order admits a Hermitian identity input with nonzero canonical LDL pivots. -/
theorem storedEntriesDenseLDL_nonVacuous : StoredEntriesDenseLDLNonVacuous := by
  intro N₀
  have hI : (1 : Mat N₀).PosDef := Matrix.PosDef.one
  exact ⟨N₀, fun _ => 0, le_rfl, fun _ => rfl,
    ⟨⟨1, hI.isHermitian, fun k => (hI.gaussState_apply_self_pos k).ne'⟩⟩⟩

/-- **Stored-entry Cholesky.** For every positive definite real square input, the actual tree
returns its canonical positive-diagonal Cholesky factor.

The output $\mathsf{cholesky}(\mathbf{A})$ is computed under exact real arithmetic. The target
includes order zero and preserves the declared source and shape. Its independent closed
operation budget is $1024(N+1)^3$ for each operation kind. Peak memory, including caller
buffers and scratch, is at most $3N^2+2N+3$ cells.
No printed source.

Result: positive-definite-cholesky-program -/
theorem storedEntriesDenseCholesky : StoredEntriesDenseCholesky := by
  intro N n hn x vals ξ
  obtain rfl : n = fun _ => 0 := funext hn
  let bufs := spdInputs N (fun _ => 0) x
  let st : State := inputState () (List.ofFn bufs)
  have hin : Holds st.store () 0 0 x.val :=
    holds_inputState (C := OpCount Unit Empty) () bufs 0 x.val (by simp [bufs, spdInputs])
  have hL : Writable st.store () 1 0 (N * N) :=
    writable_inputState (C := OpCount Unit Empty) () bufs 1 (N * N) (by simp [bufs, spdInputs])
  obtain ⟨out, he, hw, hLF, hchol⟩ := exec_cholesky (storedInterp (ι := Empty) 0 vals ξ ()) rfl
    (fun _ => rfl) () st (.const N) 0 1 0 0 x.val x.prop hin hL
  have htree : Prog.toStmt (choleskyResourceTree (ι := Empty) ()) N (fun _ => 0) =
      (cholesky () (.const N) 0 0 1 0).run := rfl
  have hprog : Prog.exec (storedInterp (ι := Empty) 0 vals ξ ())
      (choleskyResourceTree (ι := Empty) ()) N (fun _ => 0) st = some out := by
    rw [Prog.exec_eq_exec_toStmt, htree]
    exact he
  have hcaller : ((List.ofFn bufs).map Array.size).sum ≤ 2 * N * N := by
    simp [bufs, spdInputs, List.ofFn_succ, size_flatten, Nat.mul_assoc]
    omega
  have hspace : (Prog.staticCost (choleskyResourceTree (ι := Empty) ())
      (fun k => Finsupp.single k 1) (fun _ => 0) N (fun _ => 0)).cells () ≤ N * N + 2 * N + 3 := by
    have henv : Fin.cons N (fun _ : Fin 2 => 0) = ![N, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact choleskyResources_cells_le _ _ () N 0 0
  have hcount : (Prog.staticCost (choleskyResourceTree (ι := Empty) ())
      (fun k => Finsupp.single k 1) (fun _ => 0) N (fun _ => 0)).count ≤
        closedCountBudget N := by
    have henv : Fin.cons N (fun _ : Fin 2 => 0) = ![N, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact choleskyResources_count_le N
  have hp : SPDPost N (fun _ => 0) x vals ξ out := by
    refine ⟨hLF, hchol, ?_, Store.shape_of_writeBlock_eq_some hw⟩
    intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl (by omega : 0 ≠ 1))]
    exact hin i j
  exact runsWithin_of_exec _ N (fun _ => 0) bufs vals ξ (2 * N * N)
    (N * N + 2 * N + 3) hcaller hspace hcount hprog hp

/-- **Stored-entry SemidefiniteCholesky.** For every positive semidefinite real square input,
including singular matrices, the actual guarded tree returns a lower factor with nonnegative
diagonal and the exact Gram identity.

The output $\mathsf{semidefiniteCholesky}(\mathbf{A})$ is computed under exact real arithmetic.
The target
includes order zero and preserves the declared source and shape. Its independent closed
operation budget is $1024(N+1)^3$ for each operation kind. Peak memory, including caller
buffers and scratch, is at most $3N^2+2N+4$ cells.
No printed source.

Result: semidefinite-square-root-program -/
theorem storedEntriesDenseSemidefiniteCholesky : StoredEntriesDenseSemidefiniteCholesky := by
  intro N n hn x vals ξ
  obtain rfl : n = fun _ => 0 := funext hn
  let bufs := psdInputs N (fun _ => 0) x
  let st : State := inputState () (List.ofFn bufs)
  have hin : Holds st.store () 0 0 x.val :=
    holds_inputState (C := OpCount Unit Empty) () bufs 0 x.val (by simp [bufs, psdInputs])
  have hL : Writable st.store () 1 0 (N * N) :=
    writable_inputState (C := OpCount Unit Empty) () bufs 1 (N * N) (by simp [bufs, psdInputs])
  obtain ⟨out, he, hw, hLF, hlow, hdiag, hgram⟩ := exec_semidefiniteCholesky
    (storedInterp (ι := Empty) 0 vals ξ ()) rfl (fun _ => rfl) () st (.const N)
    0 1 0 0 x.val x.prop hin hL
  have htree : Prog.toStmt (semidefiniteCholeskyResourceTree (ι := Empty) ()) N (fun _ => 0) =
      (semidefiniteCholesky () (.const N) 0 0 1 0).run := rfl
  have hprog : Prog.exec (storedInterp (ι := Empty) 0 vals ξ ())
      (semidefiniteCholeskyResourceTree (ι := Empty) ()) N (fun _ => 0)
      st = some out := by
    rw [Prog.exec_eq_exec_toStmt, htree]
    exact he
  have hcaller : ((List.ofFn bufs).map Array.size).sum ≤ 2 * N * N := by
    simp [bufs, psdInputs, List.ofFn_succ, size_flatten, Nat.mul_assoc]
    omega
  have hspace : (Prog.staticCost (semidefiniteCholeskyResourceTree (ι := Empty) ())
      (fun k => Finsupp.single k 1) (fun _ => 0) N (fun _ => 0)).cells () ≤
        N * N + 2 * N + 4 := by
    have henv : Fin.cons N (fun _ : Fin 2 => 0) = ![N, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact semidefiniteCholeskyResources_cells_le _ _ () N 0 0
  have hcount : (Prog.staticCost (semidefiniteCholeskyResourceTree (ι := Empty) ())
      (fun k => Finsupp.single k 1) (fun _ => 0) N (fun _ => 0)).count ≤
        closedCountBudget N := by
    have henv : Fin.cons N (fun _ : Fin 2 => 0) = ![N, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact semidefiniteCholeskyResources_count_le N
  have hp : PSDPost N (fun _ => 0) x vals ξ out := by
    refine ⟨hLF, hlow, hdiag, hgram, ?_, Store.shape_of_writeBlock_eq_some hw⟩
    intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl (by omega : 0 ≠ 1))]
    exact hin i j
  exact runsWithin_of_exec _ N (fun _ => 0) bufs vals ξ (2 * N * N)
    (N * N + 2 * N + 4) hcaller hspace hcount hprog hp

/-- **Stored-entry LDL.** On the Hermitian canonical nonzero-pivot input domain, the actual tree
returns unit lower and diagonal LDL factors.

The output $\mathsf{ldlFactor}(\mathbf{A})$ is computed under exact real arithmetic. The target
includes order zero and preserves the declared source and shape. Its independent closed
operation budget is $1024(N+1)^3$ for each operation kind. Peak memory, including caller
buffers and scratch, is at most $4N^2+3N+3$ cells.
No printed source.

Result: hermitian-diagonal-factorization-program -/
theorem storedEntriesDenseLDL : StoredEntriesDenseLDL := by
  intro N n hn x vals ξ
  obtain rfl : n = fun _ => 0 := funext hn
  let bufs := ldlInputs N (fun _ => 0) x
  let st : State := inputState () (List.ofFn bufs)
  have hin : Holds st.store () 0 0 x.val :=
    holds_inputState (C := OpCount Unit Empty) () bufs 0 x.val (by simp [bufs, ldlInputs])
  have hL : Writable st.store () 1 0 (N * N) :=
    writable_inputState (C := OpCount Unit Empty) () bufs 1 (N * N) (by simp [bufs, ldlInputs])
  have hD : Writable st.store () 2 0 N :=
    writable_inputState (C := OpCount Unit Empty) () bufs 2 N (by simp [bufs, ldlInputs])
  obtain ⟨out, he, hw, hLF, hdiag, hldl⟩ := exec_ldlFactor
    (storedInterp (ι := Empty) 0 vals ξ ()) rfl (fun _ => rfl) () st (.const N)
    0 1 2 0 0 0 x.val hin x.prop.1 x.prop.2
    hL hD (by omega) (fun _ => by omega)
  have htree : Prog.toStmt (ldlResourceTree (ι := Empty) ()) N (fun _ => 0) =
      (ldlFactor () (.const N) 0 1 2 0 0 0).run := rfl
  have hprog : Prog.exec (storedInterp (ι := Empty) 0 vals ξ ())
      (ldlResourceTree (ι := Empty) ()) N (fun _ => 0) st = some out := by
    rw [Prog.exec_eq_exec_toStmt, htree]
    exact he
  have hcaller : ((List.ofFn bufs).map Array.size).sum ≤ 2 * N * N + N := by
    simp [bufs, ldlInputs, List.ofFn_succ, size_flatten, Nat.mul_assoc]
    omega
  have hspace : (Prog.staticCost (ldlResourceTree (ι := Empty) ()) (fun k => Finsupp.single k 1)
      (fun _ => 0) N (fun _ => 0)).cells () ≤ 2 * N * N + 2 * N + 3 := by
    have henv : Fin.cons N (fun _ : Fin 3 => 0) = ![N, 0, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact ldlFactorResources_cells_le _ _ () N 0 0 0
  have hcount : (Prog.staticCost (ldlResourceTree (ι := Empty) ())
      (fun k => Finsupp.single k 1) (fun _ => 0) N (fun _ => 0)).count ≤
        closedCountBudget N := by
    have henv : Fin.cons N (fun _ : Fin 3 => 0) = ![N, 0, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    unfold Prog.staticCost
    rw [henv]
    exact ldlFactorResources_count_le N
  have hp : LDLPost N (fun _ => 0) x vals ξ out := by
    obtain ⟨_, _, mid, hwl, hwd⟩ := Store.writeBlocks_pair_eq_some_iff.mp hw
    refine ⟨hLF, hdiag, hldl, ?_, (Store.shape_of_writeBlock_eq_some hwd).trans
      (Store.shape_of_writeBlock_eq_some hwl)⟩
    intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hwd (Or.inl (by omega : 0 ≠ 2)),
      Store.read_of_writeBlock_eq_some_of_ne hwl (Or.inl (by omega : 0 ≠ 1))]
    exact hin i j
  exact runsWithin_of_exec _ N (fun _ => 0) bufs vals ξ (2 * N * N + N)
    (2 * N * N + 2 * N + 3) hcaller hspace hcount hprog hp

end NLAlib.Computation
