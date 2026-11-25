/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineFrames
public import NLAlib.Matrix.Computation.LU
public import NLAlib.Matrix.Perturbation.LUErr

/-!
# LU routines: execution and decoded factorization

An LU routine succeeds and writes exactly its two disjoint factor blocks. Its decoded
factors meet the componentwise backward-error guarantee `NLAlib.IsLUErr`. Input storage and
arithmetic assumptions belong to concrete implementation instances.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main results

* `NLAlib.Computation.IsLURoutine.mono`: larger error allowances.
* `NLAlib.Computation.IsLURoutine.toBlockRoutine`: the two-factor footprint.
* `NLAlib.Computation.isLURoutine_luFactor`: the actual exact stored LU instance.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- A certified LU routine for a fixed decoded real matrix: the backend precondition and
writable disjoint factor blocks imply successful execution, exactly those two block writes
and decoded componentwise backward error at most $\varepsilon$. Disjointness ensures that
the upper-factor write preserves the lower factor. No arithmetic contract is hidden here. -/
structure IsLURoutine (I : Interp P ι K C) (dec : P → K → ℝ) (tag : P)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (ε : ℝ) (pre : Store P K → Prop)
    (Lb Ub : ℕ) (lo uo : IExp ℕ) (routine : Builder P ι ℕ ℕ Unit) : Prop where
  /-- Execution composes with the following routine. -/
  composable : ExecutionComposable I routine
  /-- Successful execution, exact disjoint factor writes and their decoded guarantee. -/
  run : ∀ st : St P K C, pre st.store →
    Writable st.store tag Lb lo.eval (N * N) → Writable st.store tag Ub uo.eval (N * N) →
    blockDisjoint (Lb, lo.eval, N * N) (Ub, uo.eval, N * N) = true →
    ∃ (out : St P K C) (Lw Uw : Array K) (mid : Store P K),
      Lw.size = N * N ∧ Uw.size = N * N ∧ exec I routine.run st = some out ∧
      st.store.writeBlock tag Lb lo.eval Lw = some mid ∧
      mid.writeBlock tag Ub uo.eval Uw = some out.store ∧
      IsLUErr ε A (unflatten N N (Lw.map (dec tag))) (unflatten N N (Uw.map (dec tag)))

variable {I : Interp P ι K C} {dec : P → K → ℝ} {tag : P} {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {ε ε' : ℝ} {pre : Store P K → Prop}
    {Lb Ub : ℕ} {lo uo : IExp ℕ} {routine : Builder P ι ℕ ℕ Unit}

/-- Increasing the componentwise factorization error allowance preserves an LU certificate. -/
theorem IsLURoutine.mono (h : IsLURoutine I dec tag A ε pre Lb Ub lo uo routine)
    (hε : ε ≤ ε') : IsLURoutine I dec tag A ε' pre Lb Ub lo uo routine where
  composable := h.composable
  run st hp hL hU hd := by
    obtain ⟨out, Lw, Uw, mid, hLs, hUs, hr, hLw, hUw, he⟩ := h.run st hp hL hU hd
    exact ⟨out, Lw, Uw, mid, hLs, hUs, hr, hLw, hUw, he.mono hε⟩

/-- The footprint of an LU certificate is its pair of disjoint factor blocks. -/
theorem IsLURoutine.toBlockRoutine (h : IsLURoutine I dec tag A ε pre Lb Ub lo uo routine)
    (hd : blockDisjoint (Lb, lo.eval, N * N) (Ub, uo.eval, N * N) = true) :
    IsBlockRoutine I tag pre [(Lb, lo.eval, N * N), (Ub, uo.eval, N * N)] routine where
  composable := h.composable
  run st hp hw := by
    obtain ⟨out, Lw, Uw, mid, hLs, hUs, hr, hLw, hUw, -⟩ :=
      h.run st hp (hw _ List.mem_cons_self)
        (hw (Ub, uo.eval, N * N) (by simp)) hd
    exact ⟨out, [Lw, Uw], hr,
      Store.writeBlocks_pair_eq_some_iff.mpr ⟨hLs, hUs, mid, hLw, hUw⟩⟩

/-- The actual stored no-pivot LU routine supplies a zero-error certificate under exact
real semantics and standard charges when every elimination pivot is nonzero. Source and
factor buffers are distinct; the input and output windows may have arbitrary offsets.
[GolubVanLoan2013, §3.2]. -/
theorem isLURoutine_luFactor {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hp : ∀ k : Fin N, gaussState A k k k ≠ 0)
    (Ab Lb Ub : ℕ) (ao lo uo : IExp ℕ)
    (hAL : Ab ≠ Lb) (hAU : Ab ≠ Ub) (hLU : Lb ≠ Ub) :
    IsLURoutine I (fun _ x => x) tag A 0 (fun s => Holds s tag Ab ao.eval A) Lb Ub lo uo
      (luFactor tag (.const N) Ab Lb Ub ao lo uo) where
  composable := executionComposable_luFactor I tag (.const N) Ab Lb Ub ao lo uo
  run st hA hL hU _ := by
    obtain ⟨out, hr, hs, -, -, he, -⟩ :=
      exec_luFactor I hI hc tag st (.const N) Ab Lb Ub ao lo uo A hA hp hL hU
        (fun _ => hAL) (fun _ => hAU) hLU
    obtain ⟨hLs, hUs, mid, hLw, hUw⟩ := Store.writeBlocks_pair_eq_some_iff.mp hs
    refine ⟨out, flatten (luLower A), flatten (luUpper A), mid,
      hLs, hUs, hr, hLw, hUw, ?_⟩
    rw [Array.map_id', Array.map_id', unflatten_flatten, unflatten_flatten]
    exact he.isLUErr

end NLAlib.Computation
