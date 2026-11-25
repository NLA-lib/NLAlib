/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLU
public import NLAlib.Matrix.Computation.GuardedEliminationRounding

/-!
# Rounded pivoted elimination phases

The actual partial-pivot search and bounded index binder exchange residual and lower-factor
rows together. Decoded comparisons and bounded index literals determine the recorded absolute
row, independently of arithmetic rounding. Store frames retain every earlier log entry.

## Main results

* `NLAlib.Computation.PLURounding.exec_pivotPhase`: actual pivoting and decoded factor frames.
-/

@[expose] public section

namespace NLAlib.Computation.PLURounding

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- The actual pivot search and recorded lower-row exchange succeed with initialized decoded
matrices, exact bounded index conversion/literals and standard relative-error semantics with
every scalar result in range. The chosen active entry has largest decoded magnitude; both
matrices undergo the same row exchange, the upper factor and earlier log words are retained,
and the full four-block store footprint is preserved. [GolubVanLoan2013, §3.4]. -/
theorem exec_pivotPhase {u : P → ℝ} {dec : P → K → ℝ}
    (I : Interp P ι K C) (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (n k : IExp ℕ) (hi : IsIndexExactSem dec n.eval I.sem) (tag : P) (st : St P K C)
    (S L U H : ℕ) (lo uo ho : IExp ℕ)
    (M F G : Matrix (Fin n.eval) (Fin n.eval) ℝ) (history : Fin n.eval → Fin n.eval)
    (hk : k.eval < n.eval) (hM : HoldsDecoded st.store dec tag S 0 M)
    (hF : HoldsDecoded st.store dec tag L lo.eval F)
    (hG : HoldsDecoded st.store dec tag U uo.eval G)
    (hH : Writable st.store tag H ho.eval n.eval)
    (hlog : ∀ j : Fin n.eval, j.val < k.eval → ∃ w,
      st.store.read tag H (ho.eval + j) = some w ∧ dec tag w = (history j).val ∧ j ≤ history j)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSH : S ≠ H) (hLH : L ≠ H) (hUH : U ≠ H)
    (hLU : L ≠ U) (base : Store P K)
    (hframe : PLU.Frame base n.eval S L U H lo.eval uo.eval ho.eval st.store) :
    ∃ (out : St P K C) (r : Fin n.eval),
      exec I (do
        partialPivot tag n k S 0 ⟨H, ho + k⟩
        Builder.bindIdx tag ⟨H, ho + k⟩ n fun selected =>
          swapRows tag n n L lo k (.var selected)).run st = some out ∧
      k.eval ≤ r.val ∧ PLU.Frame base n.eval S L U H lo.eval uo.eval ho.eval out.store ∧
      HoldsDecoded out.store dec tag S 0 (M.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      HoldsDecoded out.store dec tag L lo.eval (F.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      HoldsDecoded out.store dec tag U uo.eval G ∧
      (∀ i : Fin n.eval, k.eval ≤ i.val → |M i ⟨k.eval, hk⟩| ≤ |M r ⟨k.eval, hk⟩|) ∧
      (∀ j : Fin n.eval, j.val < k.eval + 1 → ∃ w,
        out.store.read tag H (ho.eval + j) = some w ∧
        dec tag w = ((Function.update history ⟨k.eval, hk⟩ r) j).val ∧
        j ≤ Function.update history ⟨k.eval, hk⟩ r j) := by
  classical
  choose Fw hFw hdFw using hF
  change Matrix (Fin n.eval) (Fin n.eval) K at Fw
  have hcell : Writable st.store tag H (ho + k).eval 1 := fun i hi => by
    obtain ⟨len, hlen, hlt⟩ := hH (k.eval + i) (by omega)
    exact ⟨len, hlen, by simpa only [IExp.eval_add, Nat.add_assoc] using hlt⟩
  obtain ⟨pivoted, r, W, iw, mid, hr₁, hwS, hwH, hdi, hkr, hM', hmax, -⟩ :=
    h.exec_partialPivot I tag st n k hi S 0 ⟨H, ho + k⟩ M hk hM hcell hSH
  change st.store.writeBlock tag S 0 (Array.ofFn W) = some mid at hwS
  change mid.writeBlock tag H (ho.eval + k.eval) #[iw] = some pivoted.store at hwH
  have hFp : Holds pivoted.store tag L lo.eval Fw := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hwH (Or.inl hLH),
      Store.read_of_writeBlock_eq_some_of_ne hwS (Or.inl hSL.symm)]
    exact hFw i j
  have hGp : HoldsDecoded pivoted.store dec tag U uo.eval G := by
    intro i j
    obtain ⟨w, hw, hd⟩ := hG i j
    refine ⟨w, ?_, hd⟩
    rw [Store.read_of_writeBlock_eq_some_of_ne hwH (Or.inl hUH),
      Store.read_of_writeBlock_eq_some_of_ne hwS (Or.inl hSU.symm)]
    exact hw
  have hread : pivoted.store.read tag H (ho + k).eval = some iw := by
    simpa [IExp.eval_add] using Store.read_of_writeBlock_eq_some_of_lt (j := 0) hwH (by simp)
  obtain ⟨out, LW, hr₂, hwL, hF'⟩ := PLU.exec_swapRows_of_index I tag pivoted n k hi L lo
    ⟨H, ho + k⟩ iw r hk hread hdi Fw hFp
  refine ⟨out, r, ?_, hkr,
    ((hframe.write_residual hwS (by simp)).write_history hwH hk).write_lower hwL (by simp),
    ?_, ?_, ?_, hmax, ?_⟩
  · rw [exec_run_bind I (b := partialPivot tag n k S 0 ⟨H, ho + k⟩)
      (fun _ => rfl), hr₁, Option.bind_some]
    exact hr₂
  · intro i j
    obtain ⟨w, hw, hd⟩ := hM' i j
    exact ⟨w, (Store.read_of_writeBlock_eq_some_of_ne hwL (Or.inl hSL)).trans hw, hd⟩
  · intro i j
    exact ⟨_, hF' i j, hdFw _ _⟩
  · intro i j
    obtain ⟨w, hw, hd⟩ := hGp i j
    exact ⟨w, (Store.read_of_writeBlock_eq_some_of_ne hwL (Or.inl hLU.symm)).trans hw, hd⟩
  · intro j hj
    by_cases hjk : j = ⟨k.eval, hk⟩
    · subst j
      refine ⟨iw, ?_, ?_, ?_⟩
      · rw [Store.read_of_writeBlock_eq_some_of_ne hwL (Or.inl hLH.symm)]
        exact hread
      · simpa only [Function.update_self] using hdi
      · simpa only [Function.update_self, Fin.le_def] using hkr
    · have hj' : j.val < k.eval := by
        have hne : j.val ≠ k.eval := fun h => hjk (Fin.ext h)
        omega
      obtain ⟨w, hw, hd, hle⟩ := hlog j hj'
      refine ⟨w, ?_, by simpa only [Function.update_of_ne hjk] using hd,
        by simpa only [Function.update_of_ne hjk] using hle⟩
      rw [Store.read_of_writeBlock_eq_some_of_ne hwL (Or.inl hLH.symm),
        Store.read_of_writeBlock_eq_some_of_ne hwH (Or.inr (Or.inl (by omega))),
        Store.read_of_writeBlock_eq_some_of_ne hwS (Or.inl hSH.symm)]
      exact hw

end NLAlib.Computation.PLURounding
