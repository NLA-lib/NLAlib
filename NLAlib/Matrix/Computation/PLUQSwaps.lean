/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQFrames

/-!
# Recorded row and column exchanges for complete LU

Both recorded index words are consumed by exact bounded binders. Residual rows and lower
rows follow the first choice; residual columns and upper columns follow the second choice.
Matrix words need no arithmetic structure.

## Main results

* `NLAlib.Computation.PLUQ.exec_swapsPhase_of_index`: both actual recorded exchanges.
-/

@[expose] public section

namespace NLAlib.Computation.PLUQ

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] {dec : P → K → ℝ}

/-- Both actual selected words are bound before the corresponding residual/factor exchange.
Only the three matrix blocks change; the two log words are retained. -/
theorem exec_swapsPhase_of_index (I : Interp P ι K C) (tag : P) (st : St P K C)
    (n k : IExp ℕ) (rw cw : K) (hi : IsIndexExactSem dec n.eval I.sem)
    (S L U Hr Hc : ℕ) (lo uo hro hco : IExp ℕ)
    (M F G : Matrix (Fin n.eval) (Fin n.eval) K) (r c : Fin n.eval)
    (hk : k.eval < n.eval) (hM : Holds st.store tag S 0 M)
    (hF : Holds st.store tag L lo.eval F) (hG : Holds st.store tag U uo.eval G)
    (hr : st.store.read tag Hr (hro + k).eval = some rw)
    (hc : st.store.read tag Hc (hco + k).eval = some cw)
    (hdr : dec tag rw = r.val) (hdc : dec tag cw = c.val)
    (hSL : S ≠ L) (hSU : S ≠ U) (hLC : L ≠ Hc) (hSC : S ≠ Hc) (hLU : L ≠ U)
    (base : Store P K)
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
  obtain ⟨mid, SW, LW, s₁, he₁, hw₁, hw₂, hMS, hFL⟩ := exec_swapRows_pair_of_index I
    tag st n k hi S L 0 lo ⟨Hr, hro + k⟩ rw r hk hr hdr M F hM hF hSL
  have hG' : Holds mid.store tag U uo.eval G := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hLU.symm),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hSU.symm)]; exact hG i j
  have hc' : mid.store.read tag Hc (hco + k).eval = some cw := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hLC.symm),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hSC.symm)]; exact hc
  obtain ⟨out, SCW, UW, s₂, he₂, hw₃, hw₄, hMSC, hGU⟩ := exec_swapColumns_pair_of_index I
    tag mid n k hi S U 0 uo ⟨Hc, hco + k⟩ cw c hk hc' hdc
      (M.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) G hMS hG' hSU
  refine ⟨out, ?_, (((hf.write_residual hw₁ (by simp)).write_lower hw₂ (by simp)).write_residual
    hw₃ (by simp)).write_upper hw₄ (by simp), ?_, ?_, hGU, ?_⟩
  · rw [exec_run_bind I (b := bindIdx tag ⟨Hr, hro + k⟩ n fun row => do
      swapRows tag n n S 0 k (.var row); swapRows tag n n L lo k (.var row)) (fun _ => rfl),
      he₁, Option.bind_some]
    exact he₂
  · simpa only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp,
      IExp.eval_zero] using hMSC
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₄ (Or.inl hLU),
      Store.read_of_writeBlock_eq_some_of_ne hw₃ (Or.inl hSL.symm)]; exact hFL i j
  · intro q b i hbS hbL hbU
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₄ (Or.inl hbU),
      Store.read_of_writeBlock_eq_some_of_ne hw₃ (Or.inl hbS),
      Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hbL),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hbS)]


end NLAlib.Computation.PLUQ
