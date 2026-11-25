/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.LURoundingStep

/-!
# Actual rounded partial-pivoted LU iterations

Each iteration consumes the actual pivot choice, rounded factor column and saved-pivot Schur
trace. The stored prefix advances without an execution premise or an exact Gaussian-state
identity. Zero active columns use the actual division-free guarded branches.

## Main results

* `NLAlib.Computation.PLURounding.exec_iteration`: one actual full rounded pivoted iteration.
-/

@[expose] public section

namespace NLAlib.Computation.PLURounding

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- One actual partial-pivoted iteration advances the stored decoded prefix. Comparisons and
index controls are exact, factor divisions and Schur operations use the standard model with
every result in range, and all factor/history buffers are separate. No successful-run or
nonzero-pivot premise is required. [Higham2002, §9.3; GolubVanLoan2013, §3.4]. -/
theorem exec_iteration {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P)
    (base : Store P K) (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (S L U H : ℕ) (lo uo ho : IExp ℕ) (hH : Writable base tag H ho.eval n.eval)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSH : S ≠ H) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (k : ℕ) (hk : k < n.eval) (st : St P K C)
    (hs : State dec (u tag) base tag A S L U H lo.eval uo.eval ho.eval k st.store) :
    ∃ out, exec I (do
      partialPivot tag n (.var k) S 0 ⟨H, ho + IExp.var k⟩
      bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
        swapRows tag n n L lo (.var k) (.var selected)
      luColumnTotal tag n (.var k) S L U 0 lo uo
      schurStepTotal tag n S 0 (.var k)).run st = some out ∧
      State dec (u tag) base tag A S L U H lo.eval uo.eval ho.eval (k + 1) out.store := by
  obtain ⟨history, R, F, G, hS, hF, hG, hlower, hdiag, hupper, hbound, hpref, hlog⟩ := hs.values
  let r : Fin n.eval := ⟨k, hk⟩
  obtain ⟨swapped, chosen, hr₁, hchosen, hf₁, hS₁, hF₁, hG₁, hmax₁, hlog₁⟩ :=
    exec_pivotPhase I h n (.var k) hi tag st S L U H lo uo ho R F G history hk hS hF hG
      (hH.of_shape_eq hs.frame.shape) hlog hSL hSU hSH hLH hUH hLU base hs.frame
  let τ := Equiv.swap r chosen
  let R' := R.submatrix τ id
  let F' := F.submatrix τ id
  let B' := A.submatrix (luPivotPermutation (Function.update history r chosen) (k + 1)) id
  have hchosen' : r ≤ chosen := hchosen
  have hfix : ∀ i : Fin n.eval, i.val < k → τ i = i :=
    Fin.swap_apply_of_lt_of_le r chosen hchosen'
  have hmax : ∀ i, r ≤ i → |R' i r| ≤ |R' r r| := by
    intro i hri
    have hactive := Fin.le_swap_apply_of_le r chosen hchosen' i hri
    simpa only [R', Matrix.submatrix_apply, id_eq, τ, Equiv.swap_apply_left, r, IExp.eval_var] using
      hmax₁ (τ i) hactive
  have hnum : u tag < 1 → IsLURoundingPrefix (u tag) k B' R' F' G := by
    intro hu1
    dsimp only [B']
    rw [PLU.submatrix_luPivotPermutation_update]
    exact (hpref hu1).submatrix_left τ hfix
  obtain ⟨out, R'', v, hr₂, hf₂, hS₂, hF₂, hG₂, hv0, hv1, hvrel, hnum₂, hhist₂⟩ :=
    exec_totalPhase I h n (.var k) hi tag swapped S L U H lo uo ho B' R' F' G hk
      hS₁ hF₁ hG₁ hmax hnum hSL hSU hSH hLU hLH hUH base hf₁
  have hvbound := abs_column_le_one_add (h.nonneg (p := tag) trivial) R' r v hv0 hv1 hvrel hmax
  obtain ⟨hlower₂, hdiag₂, hupper₂, hbound₂⟩ := shape_update F G r chosen rfl hchosen' v
    (fun j => if j < r then 0 else R' r j) hlower hdiag hupper hbound hv0 hv1
    (fun j hj => if_pos hj) hvbound
  refine ⟨out, ?_, hf₂, Function.update history r chosen, R'', _, _, hS₂, hF₂, hG₂,
    hlower₂, hdiag₂, hupper₂, hbound₂, hnum₂, ?_⟩
  · have hcomp : ExecutionComposable I (do
        partialPivot tag n (.var k) S 0 ⟨H, ho + IExp.var k⟩
        bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
          swapRows tag n n L lo (.var k) (.var selected)) :=
      (executionComposable_single I (fun _ => rfl)).bind
        (executionComposable_single I (fun _ => rfl))
    change exec I ((do
      partialPivot tag n (.var k) S 0 ⟨H, ho + IExp.var k⟩
      bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
        swapRows tag n n L lo (.var k) (.var selected)) >>= fun _ => do
      luColumnTotal tag n (.var k) S L U 0 lo uo
      schurStepTotal tag n S 0 (.var k)).run st = some out
    rw [hcomp, hr₁, Option.bind_some]
    exact hr₂
  · intro j hj
    obtain ⟨w, hw, hd, hle⟩ := hlog₁ j hj
    exact ⟨w, (hhist₂ tag (ho.eval + j)).trans hw, hd, hle⟩

end NLAlib.Computation.PLURounding
