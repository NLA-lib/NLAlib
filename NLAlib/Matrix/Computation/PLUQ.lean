/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQEmpty
public import NLAlib.Matrix.Computation.PLUQPrefix
public import NLAlib.Matrix.Computation.PLUQPivot
public import NLAlib.Matrix.Computation.GuardedElimination

/-!
# Complete-pivoted stored LU

The actual complete pivot choice writes both absolute pivot indices before bounded binders
exchange residual/lower rows and residual/upper columns. Total elimination admits every real
input, including singular and empty matrices. Both actual logs decode the final factorization.

## Main definitions

* `NLAlib.Computation.pivotedLUFactor`: the shared exact chooser-based factorization driver.
* `NLAlib.Computation.pluqFactor`: the full exact complete-pivoted driver.

## Main results

* `NLAlib.Computation.executionComposable_pluqFactor`: scoped composition.
* `NLAlib.Computation.exec_pluqFactor`: all-input success with both actual logs and four writes.
* `NLAlib.Computation.exec_pivotedLUFactor`: shared success under actual column-quality selection.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Factor a square matrix using an actual two-index chooser at each active pivot. The
residual/lower row exchanges and residual/upper column exchanges precede the shared total
elimination kernels. The residual buffer is scoped. -/
def pivotedLUFactor {P ι VB VI : Type} (tag : P) (choose : PivotChoice P ι VB VI)
    (n : IExp VI) (A L U Hr Hc : VB)
    (ao lo uo hro hco : IExp VI) : Builder P ι VB VI Unit := scope do
  let S ← alloc tag (n * n)
  copyv tag A ao S 0 (n * n)
  forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
  forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
  forRange n fun k => do
    choose n (.var k) S 0 ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
    bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
      swapRows tag n n S 0 (.var k) (.var row)
      swapRows tag n n L lo (.var k) (.var row)
    bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
      swapColumns tag n n S 0 (.var k) (.var col)
      swapColumns tag n n U uo (.var k) (.var col)
    luColumnTotal tag n (.var k) S L U 0 lo uo
    schurStepTotal tag n S 0 (.var k)

/-- Factor a square matrix by complete pivoting with separate lower/upper outputs and two
absolute pivot logs. Row binders exchange residual and lower rows; column binders exchange
residual and upper columns before the zero-safe elimination kernels. The residual is scoped.
The permuted input under both recorded current-position permutations equals the factor product.
[GolubVanLoan2013, §3.4]. -/
def pluqFactor {P ι VB VI : Type} (tag : P) (n : IExp VI) (A L U Hr Hc : VB)
    (ao lo uo hro hco : IExp VI) : Builder P ι VB VI Unit :=
  pivotedLUFactor tag (completePivotChoice tag) n A L U Hr Hc ao lo uo hro hco

variable {P ι : Type} [DecidableEq P]

/-- The chooser-based factorization releases its residual before a following builder. -/
theorem executionComposable_pivotedLUFactor {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (tag : P) (choose : PivotChoice P ι ℕ ℕ)
    (n : IExp ℕ) (A L U Hr Hc : ℕ) (ao lo uo hro hco : IExp ℕ) :
    ExecutionComposable I (pivotedLUFactor tag choose n A L U Hr Hc ao lo uo hro hco) :=
  executionComposable_single I (fun _ => rfl)

/-- Complete-pivoted factorization releases its residual before its continuation. -/
theorem executionComposable_pluqFactor {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (tag : P) (n : IExp ℕ) (A L U Hr Hc : ℕ)
    (ao lo uo hro hco : IExp ℕ) :
    ExecutionComposable I (pluqFactor tag n A L U Hr Hc ao lo uo hro hco) :=
  executionComposable_single I (fun _ => rfl)

/-- At dimension zero the actual chooser-based factorization succeeds and restores the
original store without reading any handle. Allocation metadata may record its scoped buffer. -/
theorem exec_pivotedLUFactor_of_zero {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (tag : P) (choose : PivotChoice P ι ℕ ℕ)
    (st : St P K C) (n : IExp ℕ) (A L U Hr Hc : ℕ) (ao lo uo hro hco : IExp ℕ)
    (hn : n.eval = 0) :
    ∃ out, exec I (pivotedLUFactor tag choose n A L U Hr Hc ao lo uo hro hco).run st = some out ∧
      out.store = st.store := by
  let Q : Store P K → Prop := fun s => s = st.store
  obtain ⟨out, he, hs⟩ := exists_exec_alloc I tag (n * n) (fun S => ((do
    copyv tag A ao S 0 (n * n)
    forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
    forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
    forRange n fun k => do
      choose n (.var k) S 0 ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
      bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
        swapRows tag n n S 0 (.var k) (.var row); swapRows tag n n L lo (.var k) (.var row)
      bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
        swapColumns tag n n S 0 (.var k) (.var col)
        swapColumns tag n n U uo (.var k) (.var col)
      luColumnTotal tag n (.var k) S L U 0 lo uo
      schurStepTotal tag n S 0 (.var k)) : Builder P ι ℕ ℕ Unit).run) st Q (by
        intro σ hσ
        refine ⟨σ, PLUQ.exec_emptyBody_choice I tag σ n A st.store.size L U Hr Hc
          ao lo uo hro hco choose hn, ?_⟩
        dsimp only [Q]
        rw [hσ]
        exact Array.pop_push)
  refine ⟨out, ?_, hs⟩
  change exec I (.seq (.alloc tag (n * n) _) .skip) st = some out
  rw [exec_seq_skip]
  exact he

namespace PLUQ

private theorem exec_totalPhase (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n k : IExp ℕ) (S L U Hr Hc : ℕ)
    (lo uo hro hco : IExp ℕ) (M F G : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hM : Holds st.store tag S 0 M)
    (hF : Holds st.store tag L lo.eval F) (hG : Holds st.store tag U uo.eval G)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U) (base : Store P ℝ)
    (hf : Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval st.store) :
    let r : Fin n.eval := ⟨k.eval, hk⟩
    let F' := F.updateCol r (fun i => if i < r then 0 else if i = r then 1 else M i r / M r r)
    let G' := G.updateRow r (fun j => if j < r then 0 else M r j)
    ∃ out, exec I (do
      luColumnTotal tag n k S L U 0 lo uo
      schurStepTotal tag n S 0 k).run st = some out ∧
      Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval out.store ∧
      Holds out.store tag S 0 (eliminationStep M r) ∧
      Holds out.store tag L lo.eval F' ∧ Holds out.store tag U uo.eval G' ∧
      ∀ q b i, b ≠ S → b ≠ L → b ≠ U → out.store.read q b i = st.store.read q b i := by
  dsimp only
  obtain ⟨materialized, he₁, hw₁, hF', hG'⟩ := exec_luColumnTotal I hI tag st n k S L U
    0 lo uo M F G hk hM hF hG hSL hSU hLU
  have hM' : Holds materialized.store tag S 0 M := fun i j => by
    rw [Store.read_of_writeBlocks_eq_some_of_forall hw₁ (fun block hblock => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
      rcases hblock with rfl | rfl
      · exact Or.inl hSL
      · exact Or.inl hSU)]; exact hM i j
  obtain ⟨out, he₂, hw₂, hM''⟩ := exec_schurStepTotal I hI hc tag materialized n S 0 k M hk hM'
  refine ⟨out, ?_, (hf.write_factors hw₁).write_residual hw₂ (size_flatten _), hM'',
    ?_, ?_, ?_⟩
  · rw [exec_run_bind I (b := luColumnTotal tag n k S L U 0 lo uo)
      (fun _ => rfl), he₁, Option.bind_some]; exact he₂
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hSL.symm)]; exact hF' i j
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hSU.symm)]; exact hG' i j
  · intro q b i hbS hbL hbU
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hbS),
      Store.read_of_writeBlocks_eq_some_of_forall hw₁ (fun block hblock => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
        rcases hblock with rfl | rfl
        · exact Or.inl hbL
        · exact Or.inl hbU)]

private theorem log_update {N : ℕ} (p : Fin N → Fin N) (k r : Fin N) (hkr : k ≤ r)
    (before after : Store P ℝ) (tag : P) (H ho : ℕ)
    (hlog : ∀ j : Fin N, j.val < k.val →
      before.read tag H (ho + j) = some ((p j).val : ℝ) ∧ j ≤ p j)
    (hnew : after.read tag H (ho + k) = some (r.val : ℝ))
    (hpast : ∀ j : Fin N, j.val < k.val →
      after.read tag H (ho + j) = before.read tag H (ho + j)) :
    ∀ j : Fin N, j.val < k.val + 1 →
      after.read tag H (ho + j) = some (((Function.update p k r) j).val : ℝ) ∧
        j ≤ Function.update p k r j := by
  intro j hj
  by_cases hjk : j = k
  · subst j; rw [Function.update_self]; exact ⟨hnew, hkr⟩
  · have hj' : j.val < k.val := by
      have hne : j.val ≠ k.val := fun heq => hjk (Fin.ext heq)
      omega
    rw [Function.update_of_ne hjk, hpast j hj']
    exact hlog j hj'

private theorem log_update_fixed {N : ℕ} (p : Fin N → Fin N) (k r : Fin N) (hkr : k ≤ r)
    (before after : Store P ℝ) (tag : P) (H ho : ℕ) (fixedColumns : Bool)
    (hlog : ∀ j : Fin N, j.val < k.val →
      before.read tag H (ho + j) = some ((p j).val : ℝ) ∧ j ≤ p j ∧
        (fixedColumns = true → p j = j))
    (hfixed : fixedColumns = true → r = k)
    (hnew : after.read tag H (ho + k) = some (r.val : ℝ))
    (hpast : ∀ j : Fin N, j.val < k.val →
      after.read tag H (ho + j) = before.read tag H (ho + j)) :
    ∀ j : Fin N, j.val < k.val + 1 →
      after.read tag H (ho + j) = some (((Function.update p k r) j).val : ℝ) ∧
        j ≤ Function.update p k r j ∧ (fixedColumns = true → Function.update p k r j = j) := by
  have hbase := log_update p k r hkr before after tag H ho
    (fun j hj => ⟨(hlog j hj).1, (hlog j hj).2.1⟩) hnew hpast
  intro j hj
  refine ⟨(hbase j hj).1, (hbase j hj).2, ?_⟩
  intro hflag
  by_cases hjk : j = k
  · subst j; rw [Function.update_self]; exact hfixed hflag
  · rw [Function.update_of_ne hjk]
    exact (hlog j (by have hne := Fin.val_ne_of_ne hjk; omega)).2.2 hflag

private theorem exec_iteration (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (choose : PivotChoice P ι ℕ ℕ) {α : ℝ} {fixedColumns : Bool}
    (hchoice : IsPivotChoiceRoutine I tag α fixedColumns choose)
    (base : Store P ℝ) (n : IExp ℕ) (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (S L U Hr Hc : ℕ) (lo uo hro hco : IExp ℕ)
    (hR : Writable base tag Hr hro.eval n.eval) (hC : Writable base tag Hc hco.eval n.eval)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSR : S ≠ Hr) (hSC : S ≠ Hc)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc)
    (k : ℕ) (hk : k < n.eval) (st : St P ℝ (OpCount P ι))
    (hs : State base tag A S L U Hr Hc lo.eval uo.eval hro.eval hco.eval k st.store
      α fixedColumns) :
    ∃ out, exec I (do
      choose n (.var k) S 0 ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
      bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
        swapRows tag n n S 0 (.var k) (.var row); swapRows tag n n L lo (.var k) (.var row)
      bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
        swapColumns tag n n S 0 (.var k) (.var col)
        swapColumns tag n n U uo (.var k) (.var col)
      luColumnTotal tag n (.var k) S L U 0 lo uo
      schurStepTotal tag n S 0 (.var k)).run st = some out ∧
      State base tag A S L U Hr Hc lo.eval uo.eval hro.eval hco.eval (k + 1) out.store
        α fixedColumns := by
  obtain ⟨p, q, F, G, hS, hF, hG, hFpref, hGpref, hmax, hlogR, hlogC⟩ := hs.values
  let pivot : Fin n.eval := ⟨k, hk⟩
  let B := A.submatrix (luPivotPermutation p k) (luPivotPermutation q k)
  obtain ⟨swapped, row, col, he₁, hrow, hcol, hf₁, hS₁, hF₁, hG₁, hquality₁, hr₁, hc₁, hpast⟩ :=
    exec_pivotPhase_choice I hI tag st n (.var k) S L U Hr Hc lo uo hro hco (gaussState B k) F G hk
      hS hF hG (hR.of_shape_eq hs.frame.shape) (hC.of_shape_eq hs.frame.shape)
      hSL hSU hSR hSC hLU hLR hLC hUR hUC hRC base hs.frame choose hchoice
  simp only [IExp.eval_var] at hpast
  let ρ := Equiv.swap pivot row
  let κ := Equiv.swap pivot col
  let R := (gaussState B k).submatrix ρ κ
  obtain ⟨out, he₂, hf₂, hS₂, hF₂, hG₂, hhist⟩ := exec_totalPhase I hI hc tag swapped
    n (.var k) S L U Hr Hc lo uo hro hco R (F.submatrix ρ id) (G.submatrix id κ)
      hk hS₁ hF₁ hG₁ hSL hSU hLU base hf₁
  obtain ⟨hFnew, hGnew, hmaxnew⟩ :=
    forall_luLower_luUpper_mul_norm_le_of_update A p q pivot row col hrow hcol F G α
    hFpref hGpref (by simpa only [Real.norm_eq_abs] using hmax)
    (by simpa only [Real.norm_eq_abs, IExp.eval_var, Fin.le_def, B, pivot] using hquality₁.1)
  have hρ : ∀ i : Fin n.eval, i.val < k → ρ i = i :=
    Fin.swap_apply_of_lt_of_le pivot row hrow
  have hκ : ∀ j : Fin n.eval, j.val < k → κ j = j :=
    Fin.swap_apply_of_lt_of_le pivot col hcol
  have hR : gaussState (A.submatrix
      (luPivotPermutation (Function.update p pivot row) (k + 1))
      (luPivotPermutation (Function.update q pivot col) (k + 1))) k = R := by
    rw [submatrix_luPivotPermutation_update]
    exact gaussState_submatrix_left_right B ρ κ k hρ hκ
  refine ⟨out, ?_, hf₂, Function.update p pivot row, Function.update q pivot col, _, _,
    ?_, hF₂, hG₂, hFnew, hGnew, (by simpa only [Real.norm_eq_abs] using hmaxnew), ?_, ?_⟩
  · have hcomp : ExecutionComposable I (do
        choose n (.var k) S 0 ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
        bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
          swapRows tag n n S 0 (.var k) (.var row); swapRows tag n n L lo (.var k) (.var row)
        bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
          swapColumns tag n n S 0 (.var k) (.var col)
          swapColumns tag n n U uo (.var k) (.var col)) :=
      (hchoice.composable n (.var k) S 0 ⟨Hr, hro + IExp.var k⟩
        ⟨Hc, hco + IExp.var k⟩).bind
        ((executionComposable_single I (fun _ => rfl)).bind
          (executionComposable_single I (fun _ => rfl)))
    change exec I ((do
      choose n (.var k) S 0 ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
      bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
        swapRows tag n n S 0 (.var k) (.var row); swapRows tag n n L lo (.var k) (.var row)
      bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
        swapColumns tag n n S 0 (.var k) (.var col)
        swapColumns tag n n U uo (.var k) (.var col)) >>= fun _ => do
      luColumnTotal tag n (.var k) S L U 0 lo uo
      schurStepTotal tag n S 0 (.var k)).run st = some out
    rw [hcomp, he₁, Option.bind_some]; exact he₂
  · rw [gaussState_succ _ hk, hR]; exact hS₂
  · apply log_update p pivot row hrow st.store out.store tag Hr hro.eval hlogR
    · exact (hhist tag Hr _ hSR.symm hLR.symm hUR.symm).trans hr₁
    · intro j hj
      change j.val < k at hj
      rw [hhist tag Hr _ hSR.symm hLR.symm hUR.symm]
      apply hpast tag Hr _ hSR.symm hLR.symm hUR.symm
      · exact Or.inr (by omega)
      · exact Or.inl hRC
  · apply log_update_fixed q pivot col hcol st.store out.store tag Hc hco.eval
      fixedColumns hlogC hquality₁.2
    · exact (hhist tag Hc _ hSC.symm hLC.symm hUC.symm).trans hc₁
    · intro j hj
      change j.val < k at hj
      rw [hhist tag Hc _ hSC.symm hLC.symm hUC.symm]
      apply hpast tag Hc _ hSC.symm hLC.symm hUC.symm
      · exact Or.inl hRC.symm
      · exact Or.inr (by omega)

private theorem exec_body (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (choose : PivotChoice P ι ℕ ℕ) {α : ℝ} {fixedColumns : Bool}
    (hchoice : IsPivotChoiceRoutine I tag α fixedColumns choose)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n : IExp ℕ)
    (A L U Hr Hc : ℕ) (ao lo uo hro hco : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : Holds initial tag A ao.eval M)
    (hL : Writable initial tag L lo.eval (n.eval * n.eval))
    (hU : Writable initial tag U uo.eval (n.eval * n.eval))
    (hR : Writable initial tag Hr hro.eval n.eval) (hC : Writable initial tag Hc hco.eval n.eval)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc)
    (hstore : st.store = initial.push (tag, Array.replicate (n.eval * n.eval) none)) :
    ∃ out, exec I (do
      copyv tag A ao initial.size 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        choose n (.var k) initial.size 0
          ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
        bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
          swapRows tag n n initial.size 0 (.var k) (.var row)
          swapRows tag n n L lo (.var k) (.var row)
        bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
          swapColumns tag n n initial.size 0 (.var k) (.var col)
          swapColumns tag n n U uo (.var k) (.var col)
        luColumnTotal tag n (.var k) initial.size L U 0 lo uo
        schurStepTotal tag n initial.size 0 (.var k)).run st = some out ∧
      State st.store tag M initial.size L U Hr Hc lo.eval uo.eval hro.eval hco.eval n.eval
        out.store α fixedColumns := by
  by_cases hn : n.eval = 0
  · exact ⟨st, exec_emptyBody_choice I tag st n A initial.size L U Hr Hc ao lo uo hro hco choose hn,
      State.empty st.store tag M initial.size L U Hr Hc lo.eval uo.eval hro.eval hco.eval
        hn α fixedColumns⟩
  have hN : 0 < n.eval := Nat.pos_of_ne_zero hn
  have hAb : A < initial.size := Store.lt_size_of_read_eq_some (hM ⟨0, hN⟩ ⟨0, hN⟩)
  have hLb := hL.lt_size (Nat.mul_pos hN hN)
  have hUb := hU.lt_size (Nat.mul_pos hN hN)
  have hRb := hR.lt_size hN
  have hCb := hC.lt_size hN
  have hMp : Holds st.store tag A ao.eval M := fun i j => by
    rw [hstore, Store.read_push_of_lt hAb]; exact hM i j
  have hS : Writable st.store tag initial.size 0 (n.eval * n.eval) := by
    rw [hstore]
    exact writable_of_shape_eq rfl (Store.getElem?_shape_push_size initial tag
      (n.eval * n.eval)) (by omega)
  have hLp : Writable st.store tag L lo.eval (n.eval * n.eval) := hstore ▸ hL.push _
  have hUp : Writable st.store tag U uo.eval (n.eval * n.eval) := hstore ▸ hU.push _
  have hRp : Writable st.store tag Hr hro.eval n.eval := hstore ▸ hR.push _
  have hCp : Writable st.store tag Hc hco.eval n.eval := hstore ▸ hC.push _
  obtain ⟨ready, he₁, hshape, hframe, hS₁, hF₁, hG₁⟩ := exec_luInitialize I hI hc tag st n
    A initial.size L U ao lo uo M hMp hS hLp hUp (Nat.ne_of_lt hAb)
    (Nat.ne_of_gt hLb) (Nat.ne_of_gt hUb) hLU
  have hf : Frame st.store n.eval initial.size L U Hr Hc lo.eval uo.eval hro.eval hco.eval
      ready.store := by
    refine ⟨hshape, ?_⟩
    intro q b i hbS hbL hbU _ _
    exact hframe q b i (by omega) hbL hbU
  have h0 := State.zero hf hS₁ hF₁ hG₁ α fixedColumns
  obtain ⟨out, he₂, hs⟩ := exists_exec_loop_eq_some_of_forall I (n := n)
    (fun k σ => State st.store tag M initial.size L U Hr Hc lo.eval uo.eval hro.eval hco.eval
      k σ.store α fixedColumns) h0 (fun k hk σ hσ =>
      exec_iteration I hI hc tag choose hchoice st.store n M
        initial.size L U Hr Hc lo uo hro hco hRp hCp (Nat.ne_of_gt hLb) (Nat.ne_of_gt hUb)
        (Nat.ne_of_gt hRb) (Nat.ne_of_gt hCb) hLU hLR hLC hUR hUC hRC k hk σ hσ)
  refine ⟨out, ?_, hs⟩
  have hcomp : ExecutionComposable I (do
      copyv tag A ao initial.size 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)) :=
    (executionComposable_single I (fun _ => rfl)).bind
      ((executionComposable_single I (fun _ => rfl)).bind
        (executionComposable_single I (fun _ => rfl)))
  change exec I ((do
    copyv tag A ao initial.size 0 (n * n)
    forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
    forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)) >>= fun _ =>
    forRange n fun k => do
      choose n (.var k) initial.size 0
        ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
      bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
        swapRows tag n n initial.size 0 (.var k) (.var row)
        swapRows tag n n L lo (.var k) (.var row)
      bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
        swapColumns tag n n initial.size 0 (.var k) (.var col)
        swapColumns tag n n U uo (.var k) (.var col)
      luColumnTotal tag n (.var k) initial.size L U 0 lo uo
      schurStepTotal tag n initial.size 0 (.var k)).run st = some out
  rw [hcomp, he₁, Option.bind_some]
  change exec I (.seq (.loop n _) .skip) ready = some out
  rw [exec_seq_skip]; exact he₂

end PLUQ
/-- A certified actual chooser supplies a full stored LU factorization on every real square
input, including singular and empty matrices. Both actual logs decode the row and column
permutations whose reindexed input is the factor product. A positive quality fraction `α` at
most one bounds lower multipliers by its reciprocal. The only net writes are the factors and
both logs; source separation is required only for nonempty inputs. A fixed-column policy also
records an identity column log. No nonsingularity or assumed execution premise is imposed. -/
theorem exec_pivotedLUFactor (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (choose : PivotChoice P ι ℕ ℕ) {α : ℝ} {fixedColumns : Bool}
    (hchoice : IsPivotChoiceRoutine I tag α fixedColumns choose)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A L U Hr Hc : ℕ)
    (ao lo uo hro hco : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : Holds st.store tag A ao.eval M)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval))
    (hU : Writable st.store tag U uo.eval (n.eval * n.eval))
    (hR : Writable st.store tag Hr hro.eval n.eval)
    (hC : Writable st.store tag Hc hco.eval n.eval)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc)
    (hAL : 0 < n.eval → A ≠ L) (hAU : 0 < n.eval → A ≠ U)
    (hAR : 0 < n.eval → A ≠ Hr) (hAC : 0 < n.eval → A ≠ Hc) :
    ∃ (out : St P ℝ (OpCount P ι)) (p q : Fin n.eval → Fin n.eval),
      exec I (pivotedLUFactor tag choose n A L U Hr Hc ao lo uo hro hco).run st = some out ∧
      st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
        (Hr, hro.eval, n.eval), (Hc, hco.eval, n.eval)]
        [flatten (luLower (M.submatrix (luPivotPermutation p n.eval)
          (luPivotPermutation q n.eval))),
          flatten (luUpper (M.submatrix (luPivotPermutation p n.eval)
            (luPivotPermutation q n.eval))),
          Array.ofFn (fun j => ((p j).val : ℝ)), Array.ofFn (fun j => ((q j).val : ℝ))] =
            some out.store ∧ (∀ j, j ≤ p j) ∧ (∀ j, j ≤ q j) ∧
      IsLU (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))
        (luLower (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval)))
        (luUpper (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
      (∀ i j, |luLower (M.submatrix (luPivotPermutation p n.eval)
        (luPivotPermutation q n.eval)) i j| ≤ α⁻¹) ∧
      Holds out.store tag L lo.eval
        (luLower (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
      Holds out.store tag U uo.eval
        (luUpper (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
      (∀ j : Fin n.eval, out.store.read tag Hr (hro.eval + j) = some ((p j).val : ℝ)) ∧
      (∀ j : Fin n.eval, out.store.read tag Hc (hco.eval + j) = some ((q j).val : ℝ)) ∧
      (fixedColumns = true → ∀ j, q j = j) ∧ Holds out.store tag A ao.eval M := by
  let Q : Store P ℝ → Prop := fun store => ∃ p q : Fin n.eval → Fin n.eval,
    st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
      (Hr, hro.eval, n.eval), (Hc, hco.eval, n.eval)]
      [flatten (luLower (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))),
        flatten (luUpper (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))),
        Array.ofFn (fun j => ((p j).val : ℝ)), Array.ofFn (fun j => ((q j).val : ℝ))] = some store ∧
    (∀ j, j ≤ p j) ∧ (∀ j, j ≤ q j) ∧
    IsLU (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))
      (luLower (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval)))
      (luUpper (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
    (∀ i j, |luLower (M.submatrix (luPivotPermutation p n.eval)
      (luPivotPermutation q n.eval)) i j| ≤ α⁻¹) ∧
    Holds store tag L lo.eval
      (luLower (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
    Holds store tag U uo.eval
      (luUpper (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
    (∀ j : Fin n.eval, store.read tag Hr (hro.eval + j) = some ((p j).val : ℝ)) ∧
    (∀ j : Fin n.eval, store.read tag Hc (hco.eval + j) = some ((q j).val : ℝ)) ∧
    (fixedColumns = true → ∀ j, q j = j)
  obtain ⟨out, he, p, q, hw, hp, hq, hfact, hmult, hLf, hUf, hrow, hcol, hfixed⟩ :=
    exists_exec_alloc I tag (n * n) (fun S => ((do
      copyv tag A ao S 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        choose n (.var k) S 0 ⟨Hr, hro + IExp.var k⟩ ⟨Hc, hco + IExp.var k⟩
        bindIdx tag ⟨Hr, hro + IExp.var k⟩ n fun row => do
          swapRows tag n n S 0 (.var k) (.var row); swapRows tag n n L lo (.var k) (.var row)
        bindIdx tag ⟨Hc, hco + IExp.var k⟩ n fun col => do
          swapColumns tag n n S 0 (.var k) (.var col)
          swapColumns tag n n U uo (.var k) (.var col)
        luColumnTotal tag n (.var k) S L U 0 lo uo
        schurStepTotal tag n S 0 (.var k)) : Builder P ι ℕ ℕ Unit).run) st Q (by
        intro σ hσ
        obtain ⟨final, hrun, hs⟩ :=
          PLUQ.exec_body I hI hc tag choose hchoice st.store σ n A L U Hr Hc
          ao lo uo hro hco M hM hL hU hR hC hLU hLR hLC hUR hUC hRC
          (by simpa only [IExp.eval_mul] using hσ)
        obtain ⟨p, q, hw, hp, hq, hfact, hmult, hLf, hUf, hrow, hcol, hfixed⟩ :=
          PLUQ.State.writeBlocks_pop hchoice.pos hchoice.le_one (hσ ▸ hs) hL hU hR hC
            hLU hLR hLC hUR hUC hRC
        exact ⟨final, hrun, p, q, hw, hp, hq, hfact, hmult, hLf, hUf, hrow, hcol, hfixed⟩)
  refine ⟨out, p, q, ?_, hw, hp, hq, hfact, hmult, hLf, hUf, hrow, hcol, hfixed, ?_⟩
  · change exec I (.seq (.alloc tag (n * n) _) .skip) st = some out
    rw [exec_seq_skip]; exact he
  · intro i j
    have hN : 0 < n.eval := Nat.zero_lt_of_lt i.isLt
    exact (Store.read_of_writeBlocks_eq_some_of_forall hw (fun block hblock => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
      rcases hblock with rfl | rfl | rfl | rfl
      · exact Or.inl (hAL hN)
      · exact Or.inl (hAU hN)
      · exact Or.inl (hAR hN)
      · exact Or.inl (hAC hN))).trans (hM i j)

/-- Full complete-pivoted LU succeeds on every stored real square matrix under exact semantics
and standard instruction charges. Both actual absolute pivot logs decode the independent row
and column permutations whose reindexed input is the factor product. All lower multipliers
have magnitude at most one. The only net writes are the lower factor, upper factor, row log
and column log, in that order, and the source is retained. The four output buffers are
distinct. Empty inputs require no valid handles; no nonsingularity or nonzero-pivot premise
is required. [GolubVanLoan2013, §3.4]. -/
theorem exec_pluqFactor (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A L U Hr Hc : ℕ)
    (ao lo uo hro hco : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : Holds st.store tag A ao.eval M)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval))
    (hU : Writable st.store tag U uo.eval (n.eval * n.eval))
    (hR : Writable st.store tag Hr hro.eval n.eval)
    (hC : Writable st.store tag Hc hco.eval n.eval)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc)
    (hAL : 0 < n.eval → A ≠ L) (hAU : 0 < n.eval → A ≠ U)
    (hAR : 0 < n.eval → A ≠ Hr) (hAC : 0 < n.eval → A ≠ Hc) :
    ∃ (out : St P ℝ (OpCount P ι)) (p q : Fin n.eval → Fin n.eval),
      exec I (pluqFactor tag n A L U Hr Hc ao lo uo hro hco).run st = some out ∧
      st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
        (Hr, hro.eval, n.eval), (Hc, hco.eval, n.eval)]
        [flatten (luLower (M.submatrix (luPivotPermutation p n.eval)
          (luPivotPermutation q n.eval))),
          flatten (luUpper (M.submatrix (luPivotPermutation p n.eval)
            (luPivotPermutation q n.eval))),
          Array.ofFn (fun j => ((p j).val : ℝ)), Array.ofFn (fun j => ((q j).val : ℝ))] =
            some out.store ∧ (∀ j, j ≤ p j) ∧ (∀ j, j ≤ q j) ∧
      IsLU (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))
        (luLower (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval)))
        (luUpper (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
      (∀ i j, |luLower (M.submatrix (luPivotPermutation p n.eval)
        (luPivotPermutation q n.eval)) i j| ≤ 1) ∧
      Holds out.store tag L lo.eval
        (luLower (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
      Holds out.store tag U uo.eval
        (luUpper (M.submatrix (luPivotPermutation p n.eval) (luPivotPermutation q n.eval))) ∧
      (∀ j : Fin n.eval, out.store.read tag Hr (hro.eval + j) = some ((p j).val : ℝ)) ∧
      (∀ j : Fin n.eval, out.store.read tag Hc (hco.eval + j) = some ((q j).val : ℝ)) ∧
      Holds out.store tag A ao.eval M := by
  obtain ⟨out, p, q, he, hw, hp, hq, hf, hm, hLf, hUf, hr, hc', -, hMS⟩ :=
    exec_pivotedLUFactor I hI hc tag (completePivotChoice tag)
      (isPivotChoiceRoutine_completePivotChoice I hI tag) st n A L U Hr Hc ao lo uo hro hco M
      hM hL hU hR hC hLU hLR hLC hUR hUC hRC hAL hAU hAR hAC
  refine ⟨out, p, q, he, hw, hp, hq, hf, ?_, hLf, hUf, hr, hc', hMS⟩
  simpa only [inv_one] using hm

end NLAlib.Computation
