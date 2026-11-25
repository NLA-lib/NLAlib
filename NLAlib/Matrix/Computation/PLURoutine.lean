/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineFrames
public import NLAlib.Matrix.Computation.PLU
public import NLAlib.Matrix.Factorizations.LUPivoting
public import NLAlib.Matrix.Perturbation.LUErr

/-!
# Row-pivoted LU routine certificates

The pivot log records absolute current row positions, before each exchange. Its decoded
values determine the permutation in the factorization guarantee. In particular, a solve
consumer must apply this permutation to the right-hand side before triangular substitution.
The contract separates this storage and error guarantee from a particular pivot policy.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main results

* `NLAlib.Computation.IsPLURoutine.mono`: larger error allowances.
* `NLAlib.Computation.IsPLURoutine.toBlockRoutine`: the three-output footprint.
* `NLAlib.Computation.isPLURoutine_pluFactor`: the actual exact partial-pivoted instance.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- A row-pivoted LU routine succeeds, writes only two factors and a pivot log, and meets
the componentwise error allowance for the input permuted by that actual log. Each logged
row is an absolute current position in the active suffix, not an original input row label.
The three disjoint output blocks preserve one another. Arithmetic assumptions and the
choice of pivot policy belong to implementation instances. -/
structure IsPLURoutine (I : Interp P ι K C) (dec : P → K → ℝ) (tag : P)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (ε : ℝ) (pre : Store P K → Prop)
    (Lb Ub Pb : ℕ) (lo uo po : IExp ℕ) (routine : Builder P ι ℕ ℕ Unit) : Prop where
  /-- Execution composes with the following routine. -/
  composable : ExecutionComposable I routine
  /-- Successful execution, exact output writes and the guarantee tied to the decoded log. -/
  run : ∀ st : St P K C, pre st.store →
    WritableBlocks st.store tag
      [(Lb, lo.eval, N * N), (Ub, uo.eval, N * N), (Pb, po.eval, N)] →
    blockDisjoint (Lb, lo.eval, N * N) (Ub, uo.eval, N * N) = true →
    blockDisjoint (Lb, lo.eval, N * N) (Pb, po.eval, N) = true →
    blockDisjoint (Ub, uo.eval, N * N) (Pb, po.eval, N) = true →
    ∃ (out : St P K C) (Lw Uw Pw : Array K) (p : Fin N → Fin N),
      Lw.size = N * N ∧ Uw.size = N * N ∧ Pw.size = N ∧
      exec I routine.run st = some out ∧
      st.store.writeBlocks tag
        [(Lb, lo.eval, N * N), (Ub, uo.eval, N * N), (Pb, po.eval, N)]
        [Lw, Uw, Pw] = some out.store ∧
      ReadsDecoded out.store dec tag Pb po.eval (fun i => (p i : ℕ)) ∧
      (∀ i, i ≤ p i) ∧
      IsLUErr ε (A.submatrix (luPivotPermutation p N) id)
        (unflatten N N (Lw.map (dec tag))) (unflatten N N (Uw.map (dec tag)))

variable {I : Interp P ι K C} {dec : P → K → ℝ} {tag : P} {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {ε ε' : ℝ} {pre : Store P K → Prop}
    {Lb Ub Pb : ℕ} {lo uo po : IExp ℕ} {routine : Builder P ι ℕ ℕ Unit}

/-- Increasing the componentwise error allowance preserves a pivoted LU certificate. -/
theorem IsPLURoutine.mono
    (h : IsPLURoutine I dec tag A ε pre Lb Ub Pb lo uo po routine) (hε : ε ≤ ε') :
    IsPLURoutine I dec tag A ε' pre Lb Ub Pb lo uo po routine where
  composable := h.composable
  run st hp hw hLU hLP hUP := by
    obtain ⟨out, Lw, Uw, Pw, p, hLs, hUs, hPs, hr, hs, hd, ha, he⟩ :=
      h.run st hp hw hLU hLP hUP
    exact ⟨out, Lw, Uw, Pw, p, hLs, hUs, hPs, hr, hs, hd, ha, he.mono hε⟩

/-- The footprint of a pivoted LU certificate consists of both factors and the pivot log. -/
theorem IsPLURoutine.toBlockRoutine
    (h : IsPLURoutine I dec tag A ε pre Lb Ub Pb lo uo po routine)
    (hLU : blockDisjoint (Lb, lo.eval, N * N) (Ub, uo.eval, N * N) = true)
    (hLP : blockDisjoint (Lb, lo.eval, N * N) (Pb, po.eval, N) = true)
    (hUP : blockDisjoint (Ub, uo.eval, N * N) (Pb, po.eval, N) = true) :
    IsBlockRoutine I tag pre
      [(Lb, lo.eval, N * N), (Ub, uo.eval, N * N), (Pb, po.eval, N)] routine where
  composable := h.composable
  run st hp hw := by
    obtain ⟨out, Lw, Uw, Pw, -, -, -, -, hr, hs, -⟩ := h.run st hp hw hLU hLP hUP
    exact ⟨out, [Lw, Uw, Pw], hr, hs⟩

/-- The actual partial-pivoted driver supplies a zero-error row-pivoted LU certificate for
every real square matrix, including singular inputs. Exact scalar semantics and standard
charges suffice; no nonzero-pivot premise is needed. The source and three output buffers are
separate, and arbitrary offsets are allowed. [GolubVanLoan2013, §3.4]. -/
theorem isPLURoutine_pluFactor {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (Ab Lb Ub Pb : ℕ) (ao lo uo po : IExp ℕ)
    (hAL : Ab ≠ Lb) (hAU : Ab ≠ Ub) (hAP : Ab ≠ Pb)
    (hLU : Lb ≠ Ub) (hLP : Lb ≠ Pb) (hUP : Ub ≠ Pb) :
    IsPLURoutine I (fun _ x => x) tag A 0 (fun s => Holds s tag Ab ao.eval A)
      Lb Ub Pb lo uo po (pluFactor tag (.const N) Ab Lb Ub Pb ao lo uo po) where
  composable := executionComposable_pluFactor I tag (.const N) Ab Lb Ub Pb ao lo uo po
  run st hA hw _ _ _ := by
    obtain ⟨out, p, hr, hs, hp, he, -, -, -, hlog, -⟩ := exec_pluFactor I hI hc tag st
      (.const N) Ab Lb Ub Pb ao lo uo po A hA
      (hw _ List.mem_cons_self) (hw (Ub, uo.eval, N * N) (by simp))
      (hw (Pb, po.eval, N) (by simp)) hLU hLP hUP
      (fun _ => hAL) (fun _ => hAU) (fun _ => hAP)
    change Fin N → Fin N at p
    refine ⟨out, flatten (luLower (A.submatrix (luPivotPermutation p N) id)),
      flatten (luUpper (A.submatrix (luPivotPermutation p N) id)),
      Array.ofFn (fun j => ((p j).val : ℝ)), p, size_flatten _, size_flatten _,
      Array.size_ofFn, hr, hs, ?_, hp, ?_⟩
    · intro i
      exact ⟨((p i).val : ℝ), hlog i, rfl⟩
    · rw [Array.map_id', Array.map_id', unflatten_flatten, unflatten_flatten]
      exact he.isLUErr

end NLAlib.Computation
