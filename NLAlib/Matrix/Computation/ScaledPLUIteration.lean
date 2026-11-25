/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.ScaledPLUPivot
public import NLAlib.Matrix.Computation.GuardedElimination
public import NLAlib.Matrix.Computation.LU

/-!
# Fixed-scale LU iteration

A completed pivot phase feeds the zero-safe factor materialization and full Schur update.
Original row scales remain in the disjoint suffix of the same residual buffer.

## Main results

* `NLAlib.Computation.ScaledPLU.exec_iteration`: the actual loop body advances its stored prefix.
-/

@[expose] public section

namespace NLAlib.Computation.ScaledPLU

open scoped Matrix
open Builder

variable {P ι : Type} [DecidableEq P]

private theorem exec_totalPhase (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n k : IExp ℕ) (S L U H : ℕ) (lo uo ho : IExp ℕ)
    (M F G : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : Holds st.store tag S 0 M) (hF : Holds st.store tag L lo.eval F)
    (hG : Holds st.store tag U uo.eval G)
    (sc : Fin n.eval → ℝ)
    (hsc : ReadsDecoded st.store (fun _ x => x) tag S (n.eval * n.eval) sc)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSH : S ≠ H) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (base : Store P ℝ) (hframe : Frame base n.eval S L U H lo.eval uo.eval ho.eval st.store) :
    let r : Fin n.eval := ⟨k.eval, hk⟩
    let F' := F.updateCol r (fun i => if i < r then 0 else if i = r then 1 else M i r / M r r)
    let G' := G.updateRow r (fun j => if j < r then 0 else M r j)
    ∃ out : St P ℝ (OpCount P ι), exec I (do
      luColumnTotal tag n k S L U 0 lo uo
      schurStepTotal tag n S 0 k).run st = some out ∧
      Frame base n.eval S L U H lo.eval uo.eval ho.eval out.store ∧
      Holds out.store tag S 0 (eliminationStep M r) ∧
      Holds out.store tag L lo.eval F' ∧ Holds out.store tag U uo.eval G' ∧
      (∀ q i, out.store.read q H i = st.store.read q H i) ∧
      ReadsDecoded out.store (fun _ x => x) tag S (n.eval * n.eval) sc := by
  dsimp only
  obtain ⟨materialized, hr₁, hw₁, hF', hG'⟩ := exec_luColumnTotal I hI tag st n k S L U
    0 lo uo M F G hk hM hF hG hSL hSU hLU
  have hM' : Holds materialized.store tag S 0 M := fun i j => by
    rw [Store.read_of_writeBlocks_eq_some_of_forall hw₁ (fun block hblock => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
      rcases hblock with rfl | rfl
      · exact Or.inl hSL
      · exact Or.inl hSU)]
    exact hM i j
  obtain ⟨out, hr₂, hw₂, hM''⟩ := exec_schurStepTotal I hI hc tag materialized n S 0 k M hk hM'
  refine ⟨out, ?_, (hframe.write_factors hw₁).write_workspace hw₂, hM'',
    ?_, ?_, ?_, ?_⟩
  · rw [exec_run_bind I (b := luColumnTotal tag n k S L U 0 lo uo)
      (fun _ => rfl), hr₁, Option.bind_some]
    exact hr₂
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hSL.symm)]
    exact hF' i j
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hSU.symm)]
    exact hG' i j
  · intro q i
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hSH.symm),
      Store.read_of_writeBlocks_eq_some_of_forall hw₁ (fun block hblock => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
        rcases hblock with rfl | rfl
        · exact Or.inl hLH.symm
        · exact Or.inl hUH.symm)]
  · intro i
    obtain ⟨w, hr, hd⟩ := hsc i
    refine ⟨w, ?_, hd⟩
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂
      (Or.inr (Or.inr (by simp only [IExp.eval_zero, size_flatten]; omega))),
      Store.read_of_writeBlocks_eq_some_of_forall hw₁ (fun block hb => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact Or.inl hSL
        · exact Or.inl hSU)]
    exact hr


/-- The actual scaled-pivoted loop body advances the canonical factor prefixes, the recorded
permutation and the fixed-scale maximum property, including zero active columns. -/
theorem exec_iteration (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (base : Store P ℝ) (n : IExp ℕ) (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (S L U H : ℕ) (lo uo ho : IExp ℕ) (hH : Writable base tag H ho.eval n.eval)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSH : S ≠ H) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (k : ℕ) (hk : k < n.eval) (st : St P ℝ (OpCount P ι))
    (hs : State base tag A S L U H lo.eval uo.eval ho.eval k st.store) :
    ∃ out, exec I (do
      scaledPartialPivot tag n (.var k) S 0 S (n * n) ⟨H, ho + IExp.var k⟩
      bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
        swapRows tag n n L lo (.var k) (.var selected)
      luColumnTotal tag n (.var k) S L U 0 lo uo
      schurStepTotal tag n S 0 (.var k)).run st = some out ∧
      State base tag A S L U H lo.eval uo.eval ho.eval (k + 1) out.store := by
  obtain ⟨p, F, G, hS, hF, hG, hFpref, hGpref, hscale, hmax, hlog⟩ := hs.values
  let pivot : Fin n.eval := ⟨k, hk⟩
  let B := A.submatrix (luPivotPermutation p k) id
  obtain ⟨swapped, chosen, hr₁, hchosen, hf₁, hS₁, hF₁, hG₁, hscale₁, hmax₁, hlog₁⟩ :=
    exec_pivotPhase I hI tag st n (.var k) S L U H lo uo ho (gaussState B k) F G
      (fun i => ‖A (luPivotPermutation p k i)‖) p hk hS hF hG hscale (fun i => norm_nonneg _)
      (fun i _ hi => gaussState_apply_eq_zero_of_norm_row_eq_zero B i hi k pivot)
      (hH.of_shape_eq hs.frame.shape) hlog hSL hSU hSH hLH hUH hLU base hs.frame
  let τ := Equiv.swap pivot chosen
  let R := (gaussState B k).submatrix τ id
  obtain ⟨out, hr₂, hf₂, hS₂, hF₂, hG₂, hhist₂, hscale₂⟩ := exec_totalPhase I hI hc tag swapped
    n (.var k) S L U H lo uo ho R (F.submatrix τ id) G hk hS₁ hF₁ hG₁
    _ hscale₁ hSL hSU hSH hLU hLH hUH base hf₁
  obtain ⟨hFnew, hGnew⟩ := factors_update A p pivot chosen hchosen F G hFpref hGpref
  have hmaxnew := hmax.update A p pivot chosen hchosen
    (by simpa only [Real.norm_eq_abs, IExp.eval_var, Fin.le_def, B, pivot] using hmax₁)
  have hfix : ∀ i : Fin n.eval, i.val < k → τ i = i :=
    Fin.swap_apply_of_lt_of_le pivot chosen hchosen
  have hR : gaussState (A.submatrix
      (luPivotPermutation (Function.update p pivot chosen) (k + 1)) id) k = R := by
    rw [PLU.submatrix_luPivotPermutation_update]
    exact gaussState_submatrix_left B τ k hfix
  refine ⟨out, ?_, hf₂, Function.update p pivot chosen, _, _, ?_, hF₂, hG₂,
    hFnew, hGnew, ?_, hmaxnew, ?_⟩
  · have hcomp : ExecutionComposable I (do
        scaledPartialPivot tag n (.var k) S 0 S (n * n) ⟨H, ho + IExp.var k⟩
        bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
          swapRows tag n n L lo (.var k) (.var selected)) :=
      (executionComposable_single I (fun _ => rfl)).bind
        (executionComposable_single I (fun _ => rfl))
    change exec I ((do
      scaledPartialPivot tag n (.var k) S 0 S (n * n) ⟨H, ho + IExp.var k⟩
      bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
        swapRows tag n n L lo (.var k) (.var selected)) >>= fun _ => do
      luColumnTotal tag n (.var k) S L U 0 lo uo
      schurStepTotal tag n S 0 (.var k)).run st = some out
    rw [hcomp, hr₁, Option.bind_some]
    exact hr₂
  · rw [gaussState_succ _ hk, hR]
    exact hS₂
  · intro i
    obtain ⟨w, hr, hd⟩ := hscale₂ i
    refine ⟨w, hr, ?_⟩
    change w = ‖A (luPivotPermutation (Function.update p pivot chosen) (pivot.val + 1) i)‖
    rw [luPivotPermutation_update]
    exact hd
  · intro j hj
    rw [hhist₂ tag (ho.eval + j)]
    exact hlog₁ j hj


end NLAlib.Computation.ScaledPLU
