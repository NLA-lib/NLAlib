/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQRoutine
public import NLAlib.Matrix.Computation.PLURoutine
public import NLAlib.Matrix.Computation.PivotedLUFactors

/-!
# Routine instances for rook and threshold LU

The actual policy-driven factorizations supply ordinary zero-error pivoted LU certificates.
Both recorded permutations are used for rook selection; threshold partial pivoting additionally
scopes its actual identity column log to expose the ordinary three-output row-pivoted contract.
No computed factorization or successful execution is assumed by these instances.

## Main results

* `NLAlib.Computation.isPLUQRoutine_rookPluqFactor`: actual rook four-output certificate.
* `NLAlib.Computation.isPLUQRoutine_thresholdPluqFactor`: actual threshold four-output certificate.
* `NLAlib.Computation.isPLURoutine_thresholdPluFactor`: actual threshold row-only certificate.
-/

@[expose] public section

namespace NLAlib.Computation

/-- Actual rook-pivoted LU supplies the ordinary zero-error certificate on every real square
input, including singular and empty matrices. Both actual logs determine its permutations. -/
theorem isPLUQRoutine_rookPluqFactor {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (Ab Lb Ub Rb Cb : ℕ) (ao lo uo ro co : IExp ℕ)
    (hAL : Ab ≠ Lb) (hAU : Ab ≠ Ub) (hAR : Ab ≠ Rb) (hAC : Ab ≠ Cb)
    (hLU : Lb ≠ Ub) (hLR : Lb ≠ Rb) (hLC : Lb ≠ Cb)
    (hUR : Ub ≠ Rb) (hUC : Ub ≠ Cb) (hRC : Rb ≠ Cb) :
    IsPLUQRoutine I (fun _ x => x) tag A 0 (fun s => Holds s tag Ab ao.eval A)
      Lb Ub Rb Cb lo uo ro co (rookPluqFactor tag (.const N) Ab Lb Ub Rb Cb ao lo uo ro co) := by
  exact isPLUQRoutine_pivotedLUFactor I hI hc tag (rookPivotChoice tag)
    (isPivotChoiceRoutine_rookPivotChoice I hI tag) A Ab Lb Ub Rb Cb ao lo uo ro co
    hAL hAU hAR hAC hLU hLR hLC hUR hUC hRC

/-- Actual threshold LU supplies a zero-error four-output certificate when its rational
threshold is positive and at most one. Its actual column log records identity exchanges. -/
theorem isPLUQRoutine_thresholdPluqFactor {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (τ : ℚ) (hτ₀ : 0 < τ) (hτ₁ : τ ≤ 1) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (Ab Lb Ub Rb Cb : ℕ) (ao lo uo ro co : IExp ℕ)
    (hAL : Ab ≠ Lb) (hAU : Ab ≠ Ub) (hAR : Ab ≠ Rb) (hAC : Ab ≠ Cb)
    (hLU : Lb ≠ Ub) (hLR : Lb ≠ Rb) (hLC : Lb ≠ Cb)
    (hUR : Ub ≠ Rb) (hUC : Ub ≠ Cb) (hRC : Rb ≠ Cb) :
    IsPLUQRoutine I (fun _ x => x) tag A 0 (fun s => Holds s tag Ab ao.eval A)
      Lb Ub Rb Cb lo uo ro co
      (thresholdPluqFactor tag τ (.const N) Ab Lb Ub Rb Cb ao lo uo ro co) := by
  exact isPLUQRoutine_pivotedLUFactor I hI hc tag _
    (isPivotChoiceRoutine_thresholdPivotChoice I hI tag τ hτ₀ hτ₁)
    A Ab Lb Ub Rb Cb ao lo uo ro co hAL hAU hAR hAC hLU hLR hLC hUR hUC hRC

/-- Actual threshold partial pivoting supplies the ordinary three-output zero-error row-pivoted
certificate. Its source and outputs are separate buffers; the identity column log is scoped. -/
theorem isPLURoutine_thresholdPluFactor {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (τ : ℚ) (hτ₀ : 0 < τ) (hτ₁ : τ ≤ 1) {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (Ab Lb Ub Pb : ℕ) (ao lo uo po : IExp ℕ)
    (hAL : Ab ≠ Lb) (hAU : Ab ≠ Ub) (hAP : Ab ≠ Pb)
    (hLU : Lb ≠ Ub) (hLP : Lb ≠ Pb) (hUP : Ub ≠ Pb) :
    IsPLURoutine I (fun _ x => x) tag A 0 (fun s => Holds s tag Ab ao.eval A)
      Lb Ub Pb lo uo po (thresholdPluFactor tag τ (.const N) Ab Lb Ub Pb ao lo uo po) where
  composable := executionComposable_thresholdPluFactor I tag τ (.const N) Ab Lb Ub Pb ao lo uo po
  run st hA hw _ _ _ := by
    obtain ⟨out, p, hr, hs, hp, he, -, -, -, hlog, -⟩ :=
      exec_thresholdPluFactor I hI hc tag τ hτ₀ hτ₁ st
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
