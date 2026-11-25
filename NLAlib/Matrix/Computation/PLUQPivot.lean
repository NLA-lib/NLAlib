/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQFrames
public import NLAlib.Matrix.Computation.PLUQSwaps
public import NLAlib.Matrix.Computation.PivotChoiceRoutine

/-!
# Recorded complete-pivot exchanges

The actual selected row and column words are consumed by bounded binders. Row exchanges act
on the residual and lower factor; column exchanges act on the residual and upper factor.
Both actual logs and every unrelated cell are retained through these exchanges.

## Main results

* `NLAlib.Computation.PLUQ.exec_swapsPhase`: both recorded exchanges and their full frame.
* `NLAlib.Computation.PLUQ.exec_pivotPhase`: actual complete choice followed by those exchanges.
-/

@[expose] public section

namespace NLAlib.Computation.PLUQ

open Builder

variable {P ι C : Type} [DecidableEq P] [AddMonoid C]

/-- Both actual selected words are bound before the corresponding residual/factor exchange.
Only the three matrix blocks change; the two log words are retained. -/
theorem exec_swapsPhase (I : Interp P ι ℝ C) (tag : P) (st : St P ℝ C)
    (n k : IExp ℕ) (hi : IsIndexExactSem (fun _ x => x) n.eval I.sem)
    (S L U Hr Hc : ℕ) (lo uo hro hco : IExp ℕ)
    (M F G : Matrix (Fin n.eval) (Fin n.eval) ℝ) (r c : Fin n.eval)
    (hk : k.eval < n.eval) (hM : Holds st.store tag S 0 M)
    (hF : Holds st.store tag L lo.eval F) (hG : Holds st.store tag U uo.eval G)
    (hr : st.store.read tag Hr (hro + k).eval = some (r.val : ℝ))
    (hc : st.store.read tag Hc (hco + k).eval = some (c.val : ℝ))
    (hSL : S ≠ L) (hSU : S ≠ U) (hLC : L ≠ Hc) (hSC : S ≠ Hc) (hLU : L ≠ U)
    (base : Store P ℝ)
    (hf : Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval st.store) :
    ∃ out, exec I (do
      bindIdx tag ⟨Hr, hro + k⟩ n fun row => do
        swapRows tag n n S 0 k (.var row)
        swapRows tag n n L lo k (.var row)
      bindIdx tag ⟨Hc, hco + k⟩ n fun col => do
        swapColumns tag n n S 0 k (.var col)
        swapColumns tag n n U uo k (.var col)).run st = some out ∧
      Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval out.store ∧
      Holds out.store tag S 0 (M.submatrix (Equiv.swap ⟨k.eval, hk⟩ r)
        (Equiv.swap ⟨k.eval, hk⟩ c)) ∧
      Holds out.store tag L lo.eval (F.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      Holds out.store tag U uo.eval (G.submatrix id (Equiv.swap ⟨k.eval, hk⟩ c)) ∧
      ∀ q b i, b ≠ S → b ≠ L → b ≠ U → out.store.read q b i = st.store.read q b i := by
  exact exec_swapsPhase_of_index I tag st n k (r.val : ℝ) (c.val : ℝ) hi
    S L U Hr Hc lo uo hro hco M F G r c hk hM hF hG hr hc rfl rfl
    hSL hSU hLC hSC hLU base hf

private theorem exec_pivotPhase_of_choice (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (n k : IExp ℕ) (S L U Hr Hc : ℕ)
    (lo uo hro hco : IExp ℕ) (M F G : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval)
    (hF : Holds st.store tag L lo.eval F) (hG : Holds st.store tag U uo.eval G)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSR : S ≠ Hr) (hSC : S ≠ Hc)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc) (base : Store P ℝ)
    (hf : Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval st.store)
    (choose : PivotChoice P ι ℕ ℕ)
    (hcomp : ExecutionComposable I (choose n k S 0 ⟨Hr, hro + k⟩ ⟨Hc, hco + k⟩))
    (Q : Fin n.eval → Fin n.eval → Prop)
    (hchoose : ∃ (chosen : St P ℝ C) (r c : Fin n.eval) (mid : Store P ℝ),
      exec I (choose n k S 0 ⟨Hr, hro + k⟩ ⟨Hc, hco + k⟩).run st = some chosen ∧
      st.store.writeBlock tag Hr (hro + k).eval #[(r.val : ℝ)] = some mid ∧
      mid.writeBlock tag Hc (hco + k).eval #[(c.val : ℝ)] = some chosen.store ∧
      k.eval ≤ r.val ∧ k.eval ≤ c.val ∧ Holds chosen.store tag S 0 M ∧ Q r c) :
    ∃ (out : St P ℝ C) (r c : Fin n.eval), exec I (do
      choose n k S 0 ⟨Hr, hro + k⟩ ⟨Hc, hco + k⟩
      bindIdx tag ⟨Hr, hro + k⟩ n fun row => do
        swapRows tag n n S 0 k (.var row); swapRows tag n n L lo k (.var row)
      bindIdx tag ⟨Hc, hco + k⟩ n fun col => do
        swapColumns tag n n S 0 k (.var col); swapColumns tag n n U uo k (.var col)).run st =
          some out ∧ k.eval ≤ r.val ∧ k.eval ≤ c.val ∧
      Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval out.store ∧
      Holds out.store tag S 0 (M.submatrix (Equiv.swap ⟨k.eval, hk⟩ r)
        (Equiv.swap ⟨k.eval, hk⟩ c)) ∧
      Holds out.store tag L lo.eval (F.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      Holds out.store tag U uo.eval (G.submatrix id (Equiv.swap ⟨k.eval, hk⟩ c)) ∧
      Q r c ∧
      out.store.read tag Hr (hro.eval + k.eval) = some (r.val : ℝ) ∧
      out.store.read tag Hc (hco.eval + k.eval) = some (c.val : ℝ) ∧
      ∀ q b i, b ≠ S → b ≠ L → b ≠ U →
        (b ≠ Hr ∨ i ≠ hro.eval + k.eval) → (b ≠ Hc ∨ i ≠ hco.eval + k.eval) →
        out.store.read q b i = st.store.read q b i := by
  obtain ⟨chosen, r, c, s₁, he₁, hw₁, hw₂, hkr, hkc, hMS, hQ⟩ := hchoose
  have hi : IsIndexExactSem (fun _ x => x) n.eval I.sem := by
    rw [hI]; exact isIndexExactSem_exactSem _
  change st.store.writeBlock tag Hr (hro.eval + k.eval) #[(r.val : ℝ)] = some s₁ at hw₁
  change s₁.writeBlock tag Hc (hco.eval + k.eval) #[(c.val : ℝ)] = some chosen.store at hw₂
  have hF' : Holds chosen.store tag L lo.eval F := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hLC),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hLR)]; exact hF i j
  have hG' : Holds chosen.store tag U uo.eval G := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hUC),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hUR)]; exact hG i j
  have hr : chosen.store.read tag Hr (hro + k).eval = some (r.val : ℝ) := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hRC)]
    simpa only [IExp.eval_add, Nat.add_zero, Array.getElem?_singleton, ↓reduceIte] using
      Store.read_of_writeBlock_eq_some_of_lt (j := 0) hw₁ (by simp)
  have hc : chosen.store.read tag Hc (hco + k).eval = some (c.val : ℝ) := by
    simpa only [IExp.eval_add, Nat.add_zero, Array.getElem?_singleton, ↓reduceIte] using
      Store.read_of_writeBlock_eq_some_of_lt (j := 0) hw₂ (by simp)
  obtain ⟨out, he₂, hf', hS', hL', hU', hreads⟩ := exec_swapsPhase I tag chosen n k hi
    S L U Hr Hc lo uo hro hco M F G r c hk hMS hF' hG' hr hc
      hSL hSU hLC hSC hLU base ((hf.write_rowHistory hw₁ hk).write_colHistory hw₂ hk)
  refine ⟨out, r, c, ?_, hkr, hkc, hf', hS', hL', hU', hQ, ?_, ?_, ?_⟩
  · rw [hcomp, he₁, Option.bind_some]; exact he₂
  · simpa only [IExp.eval_add] using
      (hreads tag Hr _ hSR.symm hLR.symm hUR.symm).trans hr
  · simpa only [IExp.eval_add] using
      (hreads tag Hc _ hSC.symm hLC.symm hUC.symm).trans hc
  · intro q b i hbS hbL hbU hbR hbC
    rw [hreads q b i hbS hbL hbU,
      Store.read_of_writeBlock_eq_some_of_ne hw₂ (by simp only [Array.size_singleton]; omega),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (by simp only [Array.size_singleton]; omega)]

omit [DecidableEq P] in
private theorem writable_pivotCell {s : Store P ℝ} {tag : P} {H : ℕ}
    {ho n k : IExp ℕ} (hH : Writable s tag H ho.eval n.eval) (hk : k.eval < n.eval) :
    Writable s tag H (ho + k).eval 1 := by
  intro i hi
  obtain ⟨len, hlen, hlt⟩ := hH (k.eval + i) (by omega)
  exact ⟨len, hlen, by simpa only [IExp.eval_add, Nat.add_assoc] using hlt⟩

/-- A certified actual column-quality chooser is followed by the two recorded matrix
exchanges. Its column quality and fixed-column promise concern the original active residual;
actual log words, matrix frame and prior history cells are retained through the swaps. -/
theorem exec_pivotPhase_choice (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (n k : IExp ℕ) (S L U Hr Hc : ℕ)
    (lo uo hro hco : IExp ℕ) (M F G : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hM : Holds st.store tag S 0 M)
    (hF : Holds st.store tag L lo.eval F) (hG : Holds st.store tag U uo.eval G)
    (hR : Writable st.store tag Hr hro.eval n.eval)
    (hC : Writable st.store tag Hc hco.eval n.eval)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSR : S ≠ Hr) (hSC : S ≠ Hc)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc) (base : Store P ℝ)
    (hf : Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval st.store)
    {α : ℝ} {fixedColumns : Bool} (choose : PivotChoice P ι ℕ ℕ)
    (hchoice : IsPivotChoiceRoutine I tag α fixedColumns choose) :
    ∃ (out : St P ℝ C) (r c : Fin n.eval), exec I (do
      choose n k S 0 ⟨Hr, hro + k⟩ ⟨Hc, hco + k⟩
      bindIdx tag ⟨Hr, hro + k⟩ n fun row => do
        swapRows tag n n S 0 k (.var row); swapRows tag n n L lo k (.var row)
      bindIdx tag ⟨Hc, hco + k⟩ n fun col => do
        swapColumns tag n n S 0 k (.var col); swapColumns tag n n U uo k (.var col)).run st =
          some out ∧ k.eval ≤ r.val ∧ k.eval ≤ c.val ∧
      Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval out.store ∧
      Holds out.store tag S 0 (M.submatrix (Equiv.swap ⟨k.eval, hk⟩ r)
        (Equiv.swap ⟨k.eval, hk⟩ c)) ∧
      Holds out.store tag L lo.eval (F.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      Holds out.store tag U uo.eval (G.submatrix id (Equiv.swap ⟨k.eval, hk⟩ c)) ∧
      ((∀ i : Fin n.eval, k.eval ≤ i.val → α * |M i c| ≤ |M r c|) ∧
        (fixedColumns = true → c = ⟨k.eval, hk⟩)) ∧
      out.store.read tag Hr (hro.eval + k.eval) = some (r.val : ℝ) ∧
      out.store.read tag Hc (hco.eval + k.eval) = some (c.val : ℝ) ∧
      ∀ q b i, b ≠ S → b ≠ L → b ≠ U →
        (b ≠ Hr ∨ i ≠ hro.eval + k.eval) → (b ≠ Hc ∨ i ≠ hco.eval + k.eval) →
        out.store.read q b i = st.store.read q b i := by
  apply exec_pivotPhase_of_choice I hI tag st n k S L U Hr Hc lo uo hro hco M F G hk hF hG
    hSL hSU hSR hSC hLU hLR hLC hUR hUC hRC base hf choose
    (hchoice.composable n k S 0 ⟨Hr, hro + k⟩ ⟨Hc, hco + k⟩)
  obtain ⟨chosen, r, c, mid, he, hw₁, hw₂, hkr, hkc, hMS, -, -, hq, hfixed⟩ :=
    hchoice.success st n k S 0 ⟨Hr, hro + k⟩ ⟨Hc, hco + k⟩ M hk hM
      (writable_pivotCell hR hk) (writable_pivotCell hC hk) hSR hSC (Or.inl hRC)
  exact ⟨chosen, r, c, mid, he, hw₁, hw₂, hkr, hkc, hMS, hq, hfixed⟩

/-- The actual complete-pivot choice is followed by the recorded residual/factor exchanges.
Both chosen indices remain stored, active and jointly maximal in the original active square.
The outside frame includes the two singleton log writes and the three matrix blocks. -/
theorem exec_pivotPhase (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (n k : IExp ℕ) (S L U Hr Hc : ℕ)
    (lo uo hro hco : IExp ℕ) (M F G : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hM : Holds st.store tag S 0 M)
    (hF : Holds st.store tag L lo.eval F) (hG : Holds st.store tag U uo.eval G)
    (hR : Writable st.store tag Hr hro.eval n.eval)
    (hC : Writable st.store tag Hc hco.eval n.eval)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSR : S ≠ Hr) (hSC : S ≠ Hc)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc) (base : Store P ℝ)
    (hf : Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval st.store) :
    ∃ (out : St P ℝ C) (r c : Fin n.eval), exec I (do
      completePivotChoice tag n k S 0 ⟨Hr, hro + k⟩ ⟨Hc, hco + k⟩
      bindIdx tag ⟨Hr, hro + k⟩ n fun row => do
        swapRows tag n n S 0 k (.var row); swapRows tag n n L lo k (.var row)
      bindIdx tag ⟨Hc, hco + k⟩ n fun col => do
        swapColumns tag n n S 0 k (.var col); swapColumns tag n n U uo k (.var col)).run st =
          some out ∧ k.eval ≤ r.val ∧ k.eval ≤ c.val ∧
      Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval out.store ∧
      Holds out.store tag S 0 (M.submatrix (Equiv.swap ⟨k.eval, hk⟩ r)
        (Equiv.swap ⟨k.eval, hk⟩ c)) ∧
      Holds out.store tag L lo.eval (F.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      Holds out.store tag U uo.eval (G.submatrix id (Equiv.swap ⟨k.eval, hk⟩ c)) ∧
      (∀ i j : Fin n.eval, k.eval ≤ i.val → k.eval ≤ j.val → |M i j| ≤ |M r c|) ∧
      out.store.read tag Hr (hro.eval + k.eval) = some (r.val : ℝ) ∧
      out.store.read tag Hc (hco.eval + k.eval) = some (c.val : ℝ) ∧
      ∀ q b i, b ≠ S → b ≠ L → b ≠ U →
        (b ≠ Hr ∨ i ≠ hro.eval + k.eval) → (b ≠ Hc ∨ i ≠ hco.eval + k.eval) →
        out.store.read q b i = st.store.read q b i := by
  apply exec_pivotPhase_of_choice I hI tag st n k S L U Hr Hc lo uo hro hco M F G hk hF hG
    hSL hSU hSR hSC hLU hLR hLC hUR hUC hRC base hf (completePivotChoice tag)
    (executionComposable_completePivotChoice I tag n k S 0 ⟨Hr, hro + k⟩ ⟨Hc, hco + k⟩)
  have hs : IsRelErrSem (fun _ => 0) (fun _ x => x) (fun _ _ => True) I.sem := by
    rw [hI]; exact isRelErrSem_exactSem
  obtain ⟨chosen, r, c, rw, cw, mid, he, hw₁, hw₂, hdr, hdc, hkr, hkc, hMS, hm, -⟩ :=
    hs.exec_completePivotChoice I n k (hI ▸ isIndexExactSem_exactSem n.eval) tag st S 0
      ⟨Hr, hro + k⟩ ⟨Hc, hco + k⟩ M hk (fun i j => ⟨M i j, hM i j, rfl⟩)
      (writable_pivotCell hR hk) (writable_pivotCell hC hk) hSR hSC (Or.inl hRC)
  refine ⟨chosen, r, c, mid, he, ?_, ?_, hkr, hkc, ?_, hm⟩
  · simpa only [hdr] using hw₁
  · simpa only [hdc] using hw₂
  · intro i j
    obtain ⟨v, hv, hd⟩ := hMS i j
    simpa only [hd, IExp.eval_zero] using hv

end NLAlib.Computation.PLUQ
