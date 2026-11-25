/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.BlockedLUPrefix
public import NLAlib.Matrix.Factorizations.LUEntries

/-!
# Actual blocked LU panel execution

Each panel column materializes the canonical factor entries and updates only the two panel
rectangles. The trailing square retains its panel-entry state until the following BLAS3 update.

## Main definitions

* `NLAlib.Computation.luPanel`: the actual panel factorization loop.

## Main results

* `NLAlib.Computation.BlockedLU.exec_panel`: exact execution and completed stored panel prefix.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

open Builder

/-- Materialize each factor column and row of a panel and execute its two rank-one rectangle
updates. The trailing square is left for a subsequent matrix multiplication.
[GolubVanLoan2013, §3.2]. -/
def luPanel {P ι VB VI : Type} (p : P) (n start width : IExp VI) (S L U : VB)
    (lo uo : IExp VI) : Builder P ι VB VI Unit :=
  forRange width fun t => do
    luColumn p n (start + IExp.var t) S L U 0 lo uo
    panelSchurStep p n (start + IExp.var t) (start + width) S 0

namespace BlockedLU

variable {P ι : Type} [DecidableEq P] {N : ℕ}

private theorem commit_prefix (A F G M : Matrix (Fin N) (Fin N) ℝ) (r : Fin N)
    (hcol : ∀ i, M i r = gaussState A r.val i r)
    (hrow : ∀ j, M r j = gaussState A r.val r j)
    (hF : ∀ i j : Fin N, j.val < r.val → F i j = luLower A i j)
    (hG : ∀ i j : Fin N, i.val < r.val → G i j = luUpper A i j) :
    let F' := F.updateCol r (fun i => if i < r then 0 else if i = r then 1 else M i r / M r r)
    let G' := G.updateRow r (fun j => if j < r then 0 else M r j)
    (∀ i j : Fin N, j.val < r.val + 1 → F' i j = luLower A i j) ∧
    (∀ i j : Fin N, i.val < r.val + 1 → G' i j = luUpper A i j) := by
  dsimp only
  constructor
  · intro i j hj
    by_cases he : j = r
    · subst j
      rw [Matrix.updateCol_self, luLower_apply_eq_ite, hcol, hcol]
    · rw [Matrix.updateCol_ne he]
      exact hF i j (by have hne : j.val ≠ r.val := fun e => he (Fin.ext e); omega)
  · intro i j hi
    by_cases he : i = r
    · subst i
      rw [Matrix.updateRow_self, luUpper_apply_eq_ite, hrow]
    · rw [Matrix.updateRow_ne he]
      exact hG i j (by have hne : i.val ≠ r.val := fun e => he (Fin.ext e); omega)

private theorem exec_panelStep (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P)
    (base : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n k stop : IExp ℕ) (start : ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (S L U : ℕ) (lo uo : IExp ℕ)
    (hk : k.eval < n.eval) (hstop : k.eval < stop.eval) (hs : stop.eval ≤ n.eval)
    (hp : ∀ r : Fin n.eval, gaussState A r.val r r ≠ 0)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U)
    (hstate : State base p A S L U lo.eval uo.eval k.eval
      (luPanelState A start stop.eval k.eval) st.store) :
    ∃ out, exec I (do
      luColumn p n k S L U 0 lo uo
      panelSchurStep p n k stop S 0).run st = some out ∧
      State base p A S L U lo.eval uo.eval (k.eval + 1)
        (luPanelState A start stop.eval (k.eval + 1)) out.store := by
  obtain ⟨F, G, hM, hF, hG, hFp, hGp⟩ := hstate.values
  let r : Fin n.eval := ⟨k.eval, hk⟩
  let M := luPanelState A start stop.eval k.eval
  have hcol : ∀ i, M i r = gaussState A k.eval i r :=
    fun i => luPanelState_apply_column A start stop.eval r i hstop
  have hrow : ∀ j, M r j = gaussState A k.eval r j :=
    fun j => luPanelState_apply_row A start stop.eval r j hstop
  have hpM : M r r ≠ 0 := by rw [hcol]; exact hp r
  obtain ⟨mat, hex₁, hw₁, hF₁, hG₁⟩ := exec_luColumn I hI p st n k S L U 0 lo uo
    M F G hk hM hpM hF hG hSL hSU hLU
  have hM₁ : Holds mat.store p S 0 M := fun i j => by
    rw [Store.read_of_writeBlocks_eq_some_of_forall hw₁ (fun block hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact Or.inl hSL
      · exact Or.inl hSU)]
    exact hM i j
  obtain ⟨out, hex₂, hw₂, hM₂⟩ := exec_panelSchurStep I hI hc p mat n k stop S 0 M
    hk hstop.le hs hM₁ hpM
  obtain ⟨hFp', hGp'⟩ := commit_prefix A F G M r hcol hrow hFp hGp
  refine ⟨out, ?_, (hstate.frame.write_factors hw₁).write_residual hw₂ (size_flatten _),
    _, _, ?_, ?_, ?_, hFp', hGp'⟩
  · rw [executionComposable_luColumn I p n k S L U 0 lo uo, hex₁, Option.bind_some]
    exact hex₂
  · simpa only [M, IExp.eval_zero,
      luPanelStep_luPanelState A start stop.eval ⟨k.eval, hk⟩ hstop hp] using hM₂
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hSL.symm)]
    exact hF₁ i j
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hSU.symm)]
    exact hG₁ i j

/-- The actual panel loop advances the canonical factor prefix through every panel pivot,
while retaining the entry-state trailing square. Original nonzero canonical pivots suffice;
there is no assumed successful run. Empty panels execute no column reads. -/
theorem exec_panel (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (p : P)
    (base : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n start width : IExp ℕ)
    (A : Matrix (Fin n.eval) (Fin n.eval) ℝ) (S L U : ℕ) (lo uo : IExp ℕ)
    (hwidth : start.eval + width.eval ≤ n.eval)
    (hp : ∀ r : Fin n.eval, gaussState A r.val r r ≠ 0)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLU : L ≠ U)
    (hstate : State base p A S L U lo.eval uo.eval start.eval
      (gaussState A start.eval) st.store) :
    ∃ out, exec I (luPanel p n start width S L U lo uo).run st = some out ∧
      State base p A S L U lo.eval uo.eval (start.eval + width.eval)
        (luPanelState A start.eval (start.eval + width.eval) (start.eval + width.eval))
        out.store := by
  let Inv := fun t (σ : St P ℝ (OpCount P ι)) =>
    State base p A S L U lo.eval uo.eval (start.eval + t)
      (luPanelState A start.eval (start.eval + width.eval) (start.eval + t)) σ.store
  have hzero : Inv 0 st := by
    simpa only [Inv, Nat.add_zero, luPanelState_start] using hstate
  obtain ⟨out, hex, hout⟩ := exists_exec_loop_eq_some_of_forall I (n := width)
    (body := fun t => (do
      luColumn p n (start + IExp.var t) S L U 0 lo uo
      panelSchurStep p n (start + IExp.var t) (start + width) S 0).run) Inv hzero (by
      intro t ht σ hσ
      obtain ⟨out, he, ho⟩ := exec_panelStep I hI hc p base σ n (start + .var t) (start + width)
        start.eval A S L U lo uo (by simp only [IExp.eval_add, IExp.eval_var]; omega)
        (by simp only [IExp.eval_add, IExp.eval_var]; omega)
        (by simpa only [IExp.eval_add] using hwidth) hp hSL hSU hLU
        (by simpa only [Inv, IExp.eval_add, IExp.eval_var] using hσ)
      exact ⟨out, he, by simpa only [Inv, IExp.eval_add, IExp.eval_var, Nat.add_assoc] using ho⟩)
  refine ⟨out, ?_, hout⟩
  change exec I (.seq (.loop width _) .skip) st = some out
  rw [exec_seq_skip]
  exact hex

end BlockedLU
end NLAlib.Computation
