/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineFrames
public import NLAlib.Matrix.Computation.PLUQ
public import NLAlib.Matrix.Perturbation.LUErr

/-!
# Complete-pivoted LU routine certificates

The two actual output logs determine independent current-to-original permutations on the row
and column axes. Their reindexed input is the matrix to which the factor error guarantee
applies. The certificate requires four disjoint output blocks, so its factor arrays and both
logs agree with the final store. Arithmetic contracts and pivot policy belong to instances.
Design: `docs/design/Matrix-DenseFactorizationRoutines.md`.

## Main definitions

* `NLAlib.Computation.IsPLUQRoutine`: a four-output certificate tied to both actual logs.

## Main results

* `NLAlib.Computation.IsPLUQRoutine.mono`: larger componentwise error allowances.
* `NLAlib.Computation.IsPLUQRoutine.toBlockRoutine`: the complete four-output footprint.
* `NLAlib.Computation.isPLUQRoutine_pluqFactor`: the actual all-input exact instance.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- A complete-pivoted LU routine succeeds and writes two factors and two absolute pivot logs.
Both actual decoded logs map current positions to original positions by their swap folds;
the factor error guarantee concerns the input reindexed by those two permutations. Each
recorded choice is in its active suffix. Six block-disjointness conditions preserve all four
outputs in the final store, including when output buffers are shared at disjoint offsets. -/
structure IsPLUQRoutine (I : Interp P ι K C) (dec : P → K → ℝ) (tag : P)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (ε : ℝ) (pre : Store P K → Prop)
    (Lb Ub Rb Cb : ℕ) (lo uo ro co : IExp ℕ) (routine : Builder P ι ℕ ℕ Unit) : Prop where
  /-- Execution composes with a following routine. -/
  composable : ExecutionComposable I routine
  /-- Actual success, four original-store writes and error tied to the two final decoded logs. -/
  run : ∀ st : St P K C, pre st.store →
    WritableBlocks st.store tag [(Lb, lo.eval, N * N), (Ub, uo.eval, N * N),
      (Rb, ro.eval, N), (Cb, co.eval, N)] →
    blockDisjoint (Lb, lo.eval, N * N) (Ub, uo.eval, N * N) = true →
    blockDisjoint (Lb, lo.eval, N * N) (Rb, ro.eval, N) = true →
    blockDisjoint (Lb, lo.eval, N * N) (Cb, co.eval, N) = true →
    blockDisjoint (Ub, uo.eval, N * N) (Rb, ro.eval, N) = true →
    blockDisjoint (Ub, uo.eval, N * N) (Cb, co.eval, N) = true →
    blockDisjoint (Rb, ro.eval, N) (Cb, co.eval, N) = true →
    ∃ (out : St P K C) (Lw Uw Rw Cw : Array K) (p q : Fin N → Fin N),
      Lw.size = N * N ∧ Uw.size = N * N ∧ Rw.size = N ∧ Cw.size = N ∧
      exec I routine.run st = some out ∧
      st.store.writeBlocks tag [(Lb, lo.eval, N * N), (Ub, uo.eval, N * N),
        (Rb, ro.eval, N), (Cb, co.eval, N)] [Lw, Uw, Rw, Cw] = some out.store ∧
      ReadsDecoded out.store dec tag Rb ro.eval (fun i => (p i : ℕ)) ∧
      ReadsDecoded out.store dec tag Cb co.eval (fun i => (q i : ℕ)) ∧
      (∀ i, i ≤ p i) ∧ (∀ i, i ≤ q i) ∧
      IsLUErr ε (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))
        (unflatten N N (Lw.map (dec tag))) (unflatten N N (Uw.map (dec tag)))

variable {I : Interp P ι K C} {dec : P → K → ℝ} {tag : P} {N : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {ε ε' : ℝ} {pre : Store P K → Prop}
    {Lb Ub Rb Cb : ℕ} {lo uo ro co : IExp ℕ} {routine : Builder P ι ℕ ℕ Unit}

/-- Increasing the componentwise factor error allowance preserves the complete-pivoted
certificate, with both actual log permutations and its full storage footprint. -/
theorem IsPLUQRoutine.mono
    (h : IsPLUQRoutine I dec tag A ε pre Lb Ub Rb Cb lo uo ro co routine) (hε : ε ≤ ε') :
    IsPLUQRoutine I dec tag A ε' pre Lb Ub Rb Cb lo uo ro co routine where
  composable := h.composable
  run st hp hw hLU hLR hLC hUR hUC hRC := by
    obtain ⟨out, Lw, Uw, Rw, Cw, p, q, hLs, hUs, hRs, hCs, hr, hs, hdR, hdC, ha, hb, he⟩ :=
      h.run st hp hw hLU hLR hLC hUR hUC hRC
    exact ⟨out, Lw, Uw, Rw, Cw, p, q, hLs, hUs, hRs, hCs, hr, hs,
      hdR, hdC, ha, hb, he.mono hε⟩

/-- The footprint consists of both factors and both actual pivot logs. -/
theorem IsPLUQRoutine.toBlockRoutine
    (h : IsPLUQRoutine I dec tag A ε pre Lb Ub Rb Cb lo uo ro co routine)
    (hLU : blockDisjoint (Lb, lo.eval, N * N) (Ub, uo.eval, N * N) = true)
    (hLR : blockDisjoint (Lb, lo.eval, N * N) (Rb, ro.eval, N) = true)
    (hLC : blockDisjoint (Lb, lo.eval, N * N) (Cb, co.eval, N) = true)
    (hUR : blockDisjoint (Ub, uo.eval, N * N) (Rb, ro.eval, N) = true)
    (hUC : blockDisjoint (Ub, uo.eval, N * N) (Cb, co.eval, N) = true)
    (hRC : blockDisjoint (Rb, ro.eval, N) (Cb, co.eval, N) = true) :
    IsBlockRoutine I tag pre [(Lb, lo.eval, N * N), (Ub, uo.eval, N * N),
      (Rb, ro.eval, N), (Cb, co.eval, N)] routine where
  composable := h.composable
  run st hp hw := by
    obtain ⟨out, Lw, Uw, Rw, Cw, -, -, -, -, -, -, hr, hs, -⟩ :=
      h.run st hp hw hLU hLR hLC hUR hUC hRC
    exact ⟨out, [Lw, Uw, Rw, Cw], hr, hs⟩

/-- An actual certified column-quality chooser supplies a zero-error four-output LU
routine certificate. Both final decoded logs and the original factor/log block writes come
from the single shared factorization execution theorem. Singular and empty inputs are admitted. -/
theorem isPLUQRoutine_pivotedLUFactor {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (choose : PivotChoice P ι ℕ ℕ) {α : ℝ} {fixedColumns : Bool}
    (hchoice : IsPivotChoiceRoutine I tag α fixedColumns choose) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (Ab Lb Ub Rb Cb : ℕ) (ao lo uo ro co : IExp ℕ)
    (hAL : Ab ≠ Lb) (hAU : Ab ≠ Ub) (hAR : Ab ≠ Rb) (hAC : Ab ≠ Cb)
    (hLU : Lb ≠ Ub) (hLR : Lb ≠ Rb) (hLC : Lb ≠ Cb)
    (hUR : Ub ≠ Rb) (hUC : Ub ≠ Cb) (hRC : Rb ≠ Cb) :
    IsPLUQRoutine I (fun _ x => x) tag A 0 (fun s => Holds s tag Ab ao.eval A)
      Lb Ub Rb Cb lo uo ro co
      (pivotedLUFactor tag choose (.const N) Ab Lb Ub Rb Cb ao lo uo ro co) where
  composable := executionComposable_pivotedLUFactor I tag choose (.const N)
    Ab Lb Ub Rb Cb ao lo uo ro co
  run st hA hw _ _ _ _ _ _ := by
    obtain ⟨out, p, q, hr, hs, hp, hq, he, -, -, -, hrow, hcol, -, -⟩ :=
      exec_pivotedLUFactor I hI hc tag choose hchoice st (.const N)
        Ab Lb Ub Rb Cb ao lo uo ro co A hA
        (hw _ List.mem_cons_self) (hw (Ub, uo.eval, N * N) (by simp))
        (hw (Rb, ro.eval, N) (by simp)) (hw (Cb, co.eval, N) (by simp))
        hLU hLR hLC hUR hUC hRC (fun _ => hAL) (fun _ => hAU) (fun _ => hAR) (fun _ => hAC)
    change Fin N → Fin N at p q
    refine ⟨out,
      flatten (luLower (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))),
      flatten (luUpper (A.submatrix (luPivotPermutation p N) (luPivotPermutation q N))),
      Array.ofFn (fun j => ((p j).val : ℝ)), Array.ofFn (fun j => ((q j).val : ℝ)), p, q,
      size_flatten _, size_flatten _, Array.size_ofFn, Array.size_ofFn, hr, hs,
      ?_, ?_, hp, hq, ?_⟩
    · intro i; exact ⟨((p i).val : ℝ), hrow i, rfl⟩
    · intro i; exact ⟨((q i).val : ℝ), hcol i, rfl⟩
    · rw [Array.map_id', Array.map_id', unflatten_flatten, unflatten_flatten]
      exact he.isLUErr

/-- The actual complete-pivoted driver supplies a zero-error certificate for every real
square matrix, including singular and empty inputs. Exact scalar semantics and standard
charges suffice. The source and four outputs have distinct buffers, with arbitrary offsets.
Both decoded current-position logs determine the actual row and column permutations.
[GolubVanLoan2013, §3.4]. -/
theorem isPLUQRoutine_pluqFactor {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (Ab Lb Ub Rb Cb : ℕ) (ao lo uo ro co : IExp ℕ)
    (hAL : Ab ≠ Lb) (hAU : Ab ≠ Ub) (hAR : Ab ≠ Rb) (hAC : Ab ≠ Cb)
    (hLU : Lb ≠ Ub) (hLR : Lb ≠ Rb) (hLC : Lb ≠ Cb)
    (hUR : Ub ≠ Rb) (hUC : Ub ≠ Cb) (hRC : Rb ≠ Cb) :
    IsPLUQRoutine I (fun _ x => x) tag A 0 (fun s => Holds s tag Ab ao.eval A)
      Lb Ub Rb Cb lo uo ro co (pluqFactor tag (.const N) Ab Lb Ub Rb Cb ao lo uo ro co) := by
  exact isPLUQRoutine_pivotedLUFactor I hI hc tag (completePivotChoice tag)
    (isPivotChoiceRoutine_completePivotChoice I hI tag) A Ab Lb Ub Rb Cb ao lo uo ro co
    hAL hAU hAR hAC hLU hLR hLC hUR hUC hRC

end NLAlib.Computation
