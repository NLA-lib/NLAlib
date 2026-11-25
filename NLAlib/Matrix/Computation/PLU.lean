/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUPrefix
public import NLAlib.Matrix.Computation.GuardedElimination
public import NLAlib.Matrix.Computation.LU

/-!
# Stored partial-pivoted LU factorization

The driver scans each active column, records its selected absolute row index, exchanges both
residual and earlier multiplier rows, then executes zero-safe factor materialization and
Schur elimination. The recorded swap log determines the row permutation in the factorization.
Singular inputs and zero active columns are admitted in exact arithmetic.

## Main definitions

* `NLAlib.Computation.pluFactor`: the full stored partial-pivoted factorization driver.

## Main results

* `NLAlib.Computation.executionComposable_pluFactor`: composition with a following routine.
* `NLAlib.Computation.exec_pluFactor`: successful exact factorization for every input, with
  the actual recorded permutation, full output frame and multiplier bound.
-/

@[expose] public section

namespace NLAlib.Computation

open scoped Matrix
open Builder

/-- Factor a stored square matrix by partial pivoting, writing separate lower and upper
factors and an absolute pivot-index log. An active-column scan exchanges residual rows; the
recorded index is consumed by a bounded binder to exchange earlier multiplier rows before
zero-safe column materialization and Schur elimination. The residual matrix is scoped.
The permutation convention is that the row-permuted input equals the factor product.
[GolubVanLoan2013, §3.4]. -/
def pluFactor {P ι VB VI : Type} (tag : P) (n : IExp VI) (A L U H : VB)
    (ao lo uo ho : IExp VI) : Builder P ι VB VI Unit := scope do
  let S ← alloc tag (n * n)
  copyv tag A ao S 0 (n * n)
  forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
  forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
  forRange n fun k => do
    partialPivot tag n (.var k) S 0 ⟨H, ho + IExp.var k⟩
    bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
      swapRows tag n n L lo (.var k) (.var selected)
    luColumnTotal tag n (.var k) S L U 0 lo uo
    schurStepTotal tag n S 0 (.var k)

variable {P ι : Type} [DecidableEq P]

/-- The partial-pivoted factorization releases its residual workspace before executing its
continuation, independently of its scalar interpretation. -/
theorem executionComposable_pluFactor {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (tag : P) (n : IExp ℕ) (A L U H : ℕ)
    (ao lo uo ho : IExp ℕ) : ExecutionComposable I (pluFactor tag n A L U H ao lo uo ho) :=
  executionComposable_single I (fun _ => rfl)

namespace PLU

private theorem exec_totalPhase (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n k : IExp ℕ) (S L U H : ℕ) (lo uo ho : IExp ℕ)
    (M F G : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : Holds st.store tag S 0 M) (hF : Holds st.store tag L lo.eval F)
    (hG : Holds st.store tag U uo.eval G)
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
      ∀ q i, out.store.read q H i = st.store.read q H i := by
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
  refine ⟨out, ?_, (hframe.write_factors hw₁).write_residual hw₂ (size_flatten _), hM'',
    ?_, ?_, ?_⟩
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

private theorem exec_iteration (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (base : Store P ℝ) (n : IExp ℕ) (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (S L U H : ℕ) (lo uo ho : IExp ℕ) (hH : Writable base tag H ho.eval n.eval)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSH : S ≠ H) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (k : ℕ) (hk : k < n.eval) (st : St P ℝ (OpCount P ι))
    (hs : State base tag A S L U H lo.eval uo.eval ho.eval k st.store) :
    ∃ out, exec I (do
      partialPivot tag n (.var k) S 0 ⟨H, ho + IExp.var k⟩
      bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
        swapRows tag n n L lo (.var k) (.var selected)
      luColumnTotal tag n (.var k) S L U 0 lo uo
      schurStepTotal tag n S 0 (.var k)).run st = some out ∧
      State base tag A S L U H lo.eval uo.eval ho.eval (k + 1) out.store := by
  obtain ⟨p, F, G, hS, hF, hG, hFpref, hGpref, hmax, hlog⟩ := hs.values
  let pivot : Fin n.eval := ⟨k, hk⟩
  let B := A.submatrix (luPivotPermutation p k) id
  obtain ⟨swapped, chosen, hr₁, hchosen, hf₁, hS₁, hF₁, hG₁, hmax₁, hlog₁⟩ :=
    exec_pivotPhase I hI tag st n (.var k) S L U H lo uo ho (gaussState B k) F G p hk
      hS hF hG (hH.of_shape_eq hs.frame.shape) hlog hSL hSU hSH hLH hUH hLU base hs.frame
  let τ := Equiv.swap pivot chosen
  let R := (gaussState B k).submatrix τ id
  obtain ⟨out, hr₂, hf₂, hS₂, hF₂, hG₂, hhist₂⟩ := exec_totalPhase I hI hc tag swapped
    n (.var k) S L U H lo uo ho R (F.submatrix τ id) G hk hS₁ hF₁ hG₁
    hSL hSU hSH hLU hLH hUH base hf₁
  obtain ⟨hFnew, hGnew, hmaxnew⟩ := prefix_update A p pivot chosen hchosen F G
    hFpref hGpref (by simpa only [Real.norm_eq_abs] using hmax)
    (by simpa only [Real.norm_eq_abs, IExp.eval_var, Fin.le_def, B, pivot] using hmax₁)
  have hfix : ∀ i : Fin n.eval, i.val < k → τ i = i :=
    Fin.swap_apply_of_lt_of_le pivot chosen hchosen
  have hR : gaussState (A.submatrix
      (luPivotPermutation (Function.update p pivot chosen) (k + 1)) id) k = R := by
    rw [submatrix_luPivotPermutation_update]
    exact gaussState_submatrix_left B τ k hfix
  refine ⟨out, ?_, hf₂, Function.update p pivot chosen, _, _, ?_, hF₂, hG₂,
    hFnew, hGnew, (by simpa only [Real.norm_eq_abs] using hmaxnew), ?_⟩
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
  · rw [gaussState_succ _ hk, hR]
    exact hS₂
  · intro j hj
    rw [hhist₂ tag (ho.eval + j)]
    exact hlog₁ j hj

/-- At dimension zero the actual PLU body leaves its entire execution state unchanged, for
arbitrary word semantics and charges. It performs no scalar operations or reads, and requires
no valid or distinct source, factor or history buffer handles. -/
theorem exec_emptyBody {K C : Type} [AddMonoid C] (I : Interp P ι K C) (tag : P)
    (st : St P K C) (n : IExp ℕ) (A S L U H : ℕ) (ao lo uo ho : IExp ℕ)
    (hn : n.eval = 0) : exec I (do
      copyv tag A ao S 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        partialPivot tag n (.var k) S 0 ⟨H, ho + IExp.var k⟩
        bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
          swapRows tag n n L lo (.var k) (.var selected)
        luColumnTotal tag n (.var k) S L U 0 lo uo
        schurStepTotal tag n S 0 (.var k)).run st = some st := by
  change exec I (.seq (.named "copy" _ (.seq (.loop (n * n) _) .skip))
    (.seq (.loop (n * n) _) (.seq (.loop (n * n) _) (.seq (.loop n _) .skip)))) st = some st
  simp only [exec_seq, exec_named, exec_loop, IExp.eval_mul, hn, zero_mul,
    List.range_zero, List.foldlM_nil, Option.pure_def, Option.bind_some, exec_skip]

private theorem exec_body (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n : IExp ℕ)
    (A L U H : ℕ) (ao lo uo ho : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : Holds initial tag A ao.eval M)
    (hL : Writable initial tag L lo.eval (n.eval * n.eval))
    (hU : Writable initial tag U uo.eval (n.eval * n.eval))
    (hH : Writable initial tag H ho.eval n.eval) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (hstore : st.store = initial.push (tag, Array.replicate (n.eval * n.eval) none)) :
    ∃ out, exec I (do
      copyv tag A ao initial.size 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        partialPivot tag n (.var k) initial.size 0 ⟨H, ho + IExp.var k⟩
        bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
          swapRows tag n n L lo (.var k) (.var selected)
        luColumnTotal tag n (.var k) initial.size L U 0 lo uo
        schurStepTotal tag n initial.size 0 (.var k)).run st = some out ∧
      State st.store tag M initial.size L U H lo.eval uo.eval ho.eval n.eval out.store := by
  by_cases hn : n.eval = 0
  · exact ⟨st, exec_emptyBody I tag st n A initial.size L U H ao lo uo ho hn,
      State.empty st.store tag M initial.size L U H lo.eval uo.eval ho.eval hn⟩
  have hN : 0 < n.eval := Nat.pos_of_ne_zero hn
  have hAb : A < initial.size := Store.lt_size_of_read_eq_some (hM ⟨0, hN⟩ ⟨0, hN⟩)
  have hLb := hL.lt_size (Nat.mul_pos hN hN)
  have hUb := hU.lt_size (Nat.mul_pos hN hN)
  have hHb := hH.lt_size hN
  have hMp : Holds st.store tag A ao.eval M := fun i j => by
    rw [hstore, Store.read_push_of_lt hAb]
    exact hM i j
  have hS : Writable st.store tag initial.size 0 (n.eval * n.eval) := by
    rw [hstore]
    exact writable_of_shape_eq rfl (Store.getElem?_shape_push_size initial tag
      (n.eval * n.eval)) (by omega)
  have hLp : Writable st.store tag L lo.eval (n.eval * n.eval) := hstore ▸ hL.push _
  have hUp : Writable st.store tag U uo.eval (n.eval * n.eval) := hstore ▸ hU.push _
  have hHp : Writable st.store tag H ho.eval n.eval := hstore ▸ hH.push _
  obtain ⟨ready, hr₁, hshape, hframe, hS₁, hF₁, hG₁⟩ := exec_luInitialize I hI hc tag st n
    A initial.size L U ao lo uo M hMp hS hLp hUp (Nat.ne_of_lt hAb)
    (Nat.ne_of_gt hLb) (Nat.ne_of_gt hUb) hLU
  have hf : Frame st.store n.eval initial.size L U H lo.eval uo.eval ho.eval ready.store := by
    refine ⟨hshape, ?_⟩
    intro q b i hbS hbL hbU _
    exact hframe q b i (by omega) hbL hbU
  have h0 := State.zero hf hS₁ hF₁ hG₁
  obtain ⟨out, hr₂, hs⟩ := exists_exec_loop_eq_some_of_forall I
    (n := n) (fun k σ => State st.store tag M initial.size L U H lo.eval uo.eval ho.eval k
      σ.store) h0 (fun k hk σ hσ => exec_iteration I hI hc tag st.store n M
      initial.size L U H lo uo ho hHp (Nat.ne_of_gt hLb) (Nat.ne_of_gt hUb)
      (Nat.ne_of_gt hHb) hLU hLH hUH k hk σ hσ)
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
      partialPivot tag n (.var k) initial.size 0 ⟨H, ho + IExp.var k⟩
      bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
        swapRows tag n n L lo (.var k) (.var selected)
      luColumnTotal tag n (.var k) initial.size L U 0 lo uo
      schurStepTotal tag n initial.size 0 (.var k)).run st = some out
  rw [hcomp, hr₁, Option.bind_some]
  change exec I (.seq (.loop n _) .skip) ready = some out
  rw [exec_seq_skip]
  exact hr₂

end PLU

/-- Full partial-pivoted LU succeeds on every stored real square matrix under exact semantics
and standard instruction charges. Its actual absolute pivot-index log decodes the row
permutation for which the canonical factors multiply to the permuted input, and every lower
multiplier has magnitude at most one. The only net writes are the lower factor, upper factor
and pivot log, in that order. The three output buffers are distinct; separation from the
input preserves it. Empty inputs require no valid input or output handles. No nonsingularity
or nonzero-pivot premise is required. [GolubVanLoan2013, §3.4]. -/
theorem exec_pluFactor (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A L U H : ℕ) (ao lo uo ho : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : Holds st.store tag A ao.eval M)
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval))
    (hU : Writable st.store tag U uo.eval (n.eval * n.eval))
    (hH : Writable st.store tag H ho.eval n.eval) (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (hAL : 0 < n.eval → A ≠ L) (hAU : 0 < n.eval → A ≠ U) (hAH : 0 < n.eval → A ≠ H) :
    ∃ (out : St P ℝ (OpCount P ι)) (p : Fin n.eval → Fin n.eval),
      exec I (pluFactor tag n A L U H ao lo uo ho).run st = some out ∧
      st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
        (H, ho.eval, n.eval)]
        [flatten (luLower (M.submatrix (luPivotPermutation p n.eval) id)),
          flatten (luUpper (M.submatrix (luPivotPermutation p n.eval) id)),
          Array.ofFn (fun j => ((p j).val : ℝ))] = some out.store ∧
      (∀ j, j ≤ p j) ∧
      IsLU (M.submatrix (luPivotPermutation p n.eval) id)
        (luLower (M.submatrix (luPivotPermutation p n.eval) id))
        (luUpper (M.submatrix (luPivotPermutation p n.eval) id)) ∧
      (∀ i j, |luLower (M.submatrix (luPivotPermutation p n.eval) id) i j| ≤ 1) ∧
      Holds out.store tag L lo.eval (luLower (M.submatrix (luPivotPermutation p n.eval) id)) ∧
      Holds out.store tag U uo.eval (luUpper (M.submatrix (luPivotPermutation p n.eval) id)) ∧
      (∀ j : Fin n.eval, out.store.read tag H (ho.eval + j) = some ((p j).val : ℝ)) ∧
      Holds out.store tag A ao.eval M := by
  let Q : Store P ℝ → Prop := fun store => ∃ p : Fin n.eval → Fin n.eval,
    st.store.writeBlocks tag [(L, lo.eval, n.eval * n.eval), (U, uo.eval, n.eval * n.eval),
      (H, ho.eval, n.eval)]
      [flatten (luLower (M.submatrix (luPivotPermutation p n.eval) id)),
        flatten (luUpper (M.submatrix (luPivotPermutation p n.eval) id)),
        Array.ofFn (fun j => ((p j).val : ℝ))] = some store ∧
    (∀ j, j ≤ p j) ∧
    IsLU (M.submatrix (luPivotPermutation p n.eval) id)
      (luLower (M.submatrix (luPivotPermutation p n.eval) id))
      (luUpper (M.submatrix (luPivotPermutation p n.eval) id)) ∧
    (∀ i j, |luLower (M.submatrix (luPivotPermutation p n.eval) id) i j| ≤ 1) ∧
    Holds store tag L lo.eval (luLower (M.submatrix (luPivotPermutation p n.eval) id)) ∧
    Holds store tag U uo.eval (luUpper (M.submatrix (luPivotPermutation p n.eval) id)) ∧
    (∀ j : Fin n.eval, store.read tag H (ho.eval + j) = some ((p j).val : ℝ))
  obtain ⟨out, hr, p, hw, hp, hf, hmult, hLf, hUf, hlog⟩ := exists_exec_alloc I tag (n * n)
    (fun S => ((do
      copyv tag A ao S 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
      forRange (n * n) fun i => ins (.lit tag ⟨U, uo + IExp.var i⟩ 0)
      forRange n fun k => do
        partialPivot tag n (.var k) S 0 ⟨H, ho + IExp.var k⟩
        bindIdx tag ⟨H, ho + IExp.var k⟩ n fun selected =>
          swapRows tag n n L lo (.var k) (.var selected)
        luColumnTotal tag n (.var k) S L U 0 lo uo
        schurStepTotal tag n S 0 (.var k)) : Builder P ι ℕ ℕ Unit).run) st Q (by
      intro σ hσ
      obtain ⟨final, hrun, hs⟩ := PLU.exec_body I hI hc tag st.store σ n A L U H ao lo uo ho
        M hM hL hU hH hLU hLH hUH (by simpa only [IExp.eval_mul] using hσ)
      obtain ⟨p, hw, hp, hf, hm, hLf, hUf, hl⟩ := PLU.State.writeBlocks_pop
        (hσ ▸ hs) hL hU hH hLU hLH hUH
      exact ⟨final, hrun, p, hw, hp, hf, hm, hLf, hUf, hl⟩)
  refine ⟨out, p, ?_, hw, hp, hf, hmult, hLf, hUf, hlog, ?_⟩
  · change exec I (.seq (.alloc tag (n * n) _) .skip) st = some out
    rw [exec_seq_skip]
    exact hr
  · intro i j
    have hN : 0 < n.eval := Nat.zero_lt_of_lt i.isLt
    exact (Store.read_of_writeBlocks_eq_some_of_forall hw (fun block hblock => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
      rcases hblock with rfl | rfl | rfl
      · exact Or.inl (hAL hN)
      · exact Or.inl (hAU hN)
      · exact Or.inl (hAH hN))).trans (hM i j)

end NLAlib.Computation
