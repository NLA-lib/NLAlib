/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQSwaps

/-!
# Rounded complete-pivot selection and exchanges

Exact decoded comparisons select both active coordinates. Their actual stored index words
control the residual and factor exchanges, without changing matrix words arithmetically.

## Main results

* `NLAlib.Computation.PLUQRounding.exec_pivotPhase`: actual generic complete-pivot phase.
-/

@[expose] public section

namespace NLAlib.Computation.PLUQRounding

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The actual complete-pivot choice is followed by the recorded residual/factor exchanges.
Both chosen indices remain stored, active and jointly maximal in the original active square.
The outside frame includes the two singleton log writes and the three matrix blocks. -/
theorem exec_pivotPhase {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (tag : P) (st : St P K C) (n k : IExp ℕ)
    (hi : IsIndexExactSem dec n.eval I.sem) (S L U Hr Hc : ℕ)
    (lo uo hro hco : IExp ℕ) (M F G : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : k.eval < n.eval) (hM : HoldsDecoded st.store dec tag S 0 M)
    (hF : HoldsDecoded st.store dec tag L lo.eval F)
    (hG : HoldsDecoded st.store dec tag U uo.eval G)
    (hR : Writable st.store tag Hr hro.eval n.eval)
    (hC : Writable st.store tag Hc hco.eval n.eval)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSR : S ≠ Hr) (hSC : S ≠ Hc)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc) (base : Store P K)
    (hf : PLUQ.Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval st.store) :
    ∃ (out : St P K C) (r c : Fin n.eval) (rw cw : K), exec I (do
      completePivotChoice tag n k S 0 ⟨Hr, hro + k⟩ ⟨Hc, hco + k⟩
      bindIdx tag ⟨Hr, hro + k⟩ n fun row => do
        swapRows tag n n S 0 k (.var row); swapRows tag n n L lo k (.var row)
      bindIdx tag ⟨Hc, hco + k⟩ n fun col => do
        swapColumns tag n n S 0 k (.var col); swapColumns tag n n U uo k (.var col)).run st =
          some out ∧ k.eval ≤ r.val ∧ k.eval ≤ c.val ∧
      PLUQ.Frame base n.eval S L U Hr Hc lo.eval uo.eval hro.eval hco.eval out.store ∧
      HoldsDecoded out.store dec tag S 0 (M.submatrix (Equiv.swap ⟨k.eval, hk⟩ r)
        (Equiv.swap ⟨k.eval, hk⟩ c)) ∧
      HoldsDecoded out.store dec tag L lo.eval (F.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      HoldsDecoded out.store dec tag U uo.eval (G.submatrix id (Equiv.swap ⟨k.eval, hk⟩ c)) ∧
      (∀ i j : Fin n.eval, k.eval ≤ i.val → k.eval ≤ j.val → |M i j| ≤ |M r c|) ∧
      out.store.read tag Hr (hro.eval + k.eval) = some rw ∧
      out.store.read tag Hc (hco.eval + k.eval) = some cw ∧
      dec tag rw = r.val ∧ dec tag cw = c.val ∧
      ∀ q b i, b ≠ S → b ≠ L → b ≠ U →
        (b ≠ Hr ∨ i ≠ hro.eval + k.eval) → (b ≠ Hc ∨ i ≠ hco.eval + k.eval) →
        out.store.read q b i = st.store.read q b i := by
  classical
  choose Mw hMw hdMw using hM
  choose Fw hFw hdFw using hF
  choose Gw hGw hdGw using hG
  change Matrix (Fin n.eval) (Fin n.eval) K at Mw Fw Gw
  have cell (H : ℕ) (ho : IExp ℕ) (hH : Writable st.store tag H ho.eval n.eval) :
      Writable st.store tag H (ho + k).eval 1 := fun i hi => by
    obtain ⟨len, hlen, hlt⟩ := hH (k.eval + i) (by omega)
    exact ⟨len, hlen, by simpa only [IExp.eval_add, Nat.add_assoc] using hlt⟩
  obtain ⟨chosen, r, c, rw, cw, s₁, he₁, hw₁, hw₂, hdr, hdc, hkr, hkc, hMS, hmax, -⟩ :=
    h.exec_completePivotChoice I n k hi tag st S 0 ⟨Hr, hro + k⟩ ⟨Hc, hco + k⟩ M hk
      (fun i j => ⟨Mw i j, hMw i j, hdMw i j⟩) (cell Hr hro hR) (cell Hc hco hC)
      hSR hSC (Or.inl hRC)
  change st.store.writeBlock tag Hr (hro.eval + k.eval) #[rw] = some s₁ at hw₁
  change s₁.writeBlock tag Hc (hco.eval + k.eval) #[cw] = some chosen.store at hw₂
  have hF' : Holds chosen.store tag L lo.eval Fw := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hLC),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hLR)]; exact hFw i j
  have hG' : Holds chosen.store tag U uo.eval Gw := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hUC),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hUR)]; exact hGw i j
  have hr : chosen.store.read tag Hr (hro + k).eval = some rw := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hRC)]
    simpa [IExp.eval_add] using
      Store.read_of_writeBlock_eq_some_of_lt (j := 0) hw₁ (by simp)
  have hc : chosen.store.read tag Hc (hco + k).eval = some cw := by
    simpa [IExp.eval_add] using
      Store.read_of_writeBlock_eq_some_of_lt (j := 0) hw₂ (by simp)
  have hMw' : Holds chosen.store tag S 0 Mw := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hSC),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hSR)]
    exact hMw i j
  obtain ⟨out, he₂, hf', hS', hL', hU', hreads⟩ := PLUQ.exec_swapsPhase_of_index I tag
    chosen n k rw cw hi S L U Hr Hc lo uo hro hco Mw Fw Gw r c hk hMw' hF' hG' hr hc
      hdr hdc hSL hSU hLC hSC hLU base ((hf.write_rowHistory hw₁ hk).write_colHistory hw₂ hk)
  refine ⟨out, r, c, rw, cw, ?_, hkr, hkc, hf', ?_, ?_, ?_, hmax, ?_, ?_, hdr, hdc, ?_⟩
  · rw [exec_run_bind I (b := completePivotChoice tag n k S 0
      ⟨Hr, hro + k⟩ ⟨Hc, hco + k⟩) (fun _ => rfl), he₁, Option.bind_some]; exact he₂
  · intro i j
    exact ⟨_, hS' i j, hdMw _ _⟩
  · intro i j
    exact ⟨_, hL' i j, hdFw _ _⟩
  · intro i j
    exact ⟨_, hU' i j, hdGw _ _⟩
  · simpa only [IExp.eval_add] using
      (hreads tag Hr _ hSR.symm hLR.symm hUR.symm).trans hr
  · simpa only [IExp.eval_add] using
      (hreads tag Hc _ hSC.symm hLC.symm hUC.symm).trans hc
  · intro q b i hbS hbL hbU hbR hbC
    rw [hreads q b i hbS hbL hbU,
      Store.read_of_writeBlock_eq_some_of_ne hw₂ (by simp only [Array.size_singleton]; omega),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (by simp only [Array.size_singleton]; omega)]

end NLAlib.Computation.PLUQRounding
