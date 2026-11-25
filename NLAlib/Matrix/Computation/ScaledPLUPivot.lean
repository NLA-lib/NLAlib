/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.ScaledPLUPrefix

/-!
# Stored fixed-scale LU pivot phase

The active column and original row scales are exchanged in the packed workspace. The actual
recorded index then controls the exchange of earlier lower-factor rows.

## Main results

* `NLAlib.Computation.ScaledPLU.exec_pivotPhase`: successful scale-aware pivot and factor swap.
-/

@[expose] public section

namespace NLAlib.Computation.ScaledPLU

variable {P ι C : Type} [DecidableEq P] [AddMonoid C]

private theorem log_update {N : ℕ} {s t : Store P ℝ} {tag : P} {S H ho k : ℕ}
    (p : Fin N → Fin N) (r : Fin N) (hk : k < N) (hkr : k ≤ r.val)
    (M : Matrix (Fin N) (Fin N) ℝ) (sc : Fin N → ℝ)
    (hw : s.writeBlocks tag [(S, 0, N * N), (S, N * N, N), (H, ho + k, 1)]
      [flatten M, Array.ofFn sc, #[(r.val : ℝ)]] = some t)
    (hSH : S ≠ H) (hr : t.read tag H (ho + k) = some (r.val : ℝ))
    (hlog : ∀ j : Fin N, j.val < k →
      s.read tag H (ho + j) = some ((p j).val : ℝ) ∧ j ≤ p j) :
    ∀ j : Fin N, j.val < k + 1 →
      t.read tag H (ho + j) = some (((Function.update p ⟨k, hk⟩ r) j).val : ℝ) ∧
        j ≤ Function.update p ⟨k, hk⟩ r j := by
  intro j hj
  by_cases he : j = ⟨k, hk⟩
  · subst j
    simpa only [Function.update_self, Fin.le_def] using And.intro hr hkr
  · have hj' : j.val < k := by
      have hne : j.val ≠ k := fun e => he (Fin.ext e)
      omega
    rw [Function.update_of_ne he]
    refine ⟨?_, (hlog j hj').2⟩
    rw [Store.read_of_writeBlocks_eq_some_of_forall hw (fun block hb => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact Or.inl hSH.symm
      · exact Or.inl hSH.symm
      · exact Or.inr (Or.inl (by change ho + j.val < ho + k; omega)))]
    exact (hlog j hj').1

/-- One exact scaled pivot swaps both packed residual rows and fixed original scales, then
consumes the actual stored index to exchange lower-factor rows. The upper factor and earlier
log entries are retained. The maximum-ratio statement refers to the pre-swap active column. -/
theorem exec_pivotPhase (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P)
    (st : St P ℝ C) (n k : IExp ℕ) (S L U H : ℕ) (lo uo ho : IExp ℕ)
    (M F G : Matrix (Fin n.eval) (Fin n.eval) ℝ) (sc : Fin n.eval → ℝ)
    (p : Fin n.eval → Fin n.eval) (hk : k.eval < n.eval)
    (hM : Holds st.store tag S 0 M) (hF : Holds st.store tag L lo.eval F)
    (hG : Holds st.store tag U uo.eval G)
    (hsc : ReadsDecoded st.store (fun _ x => x) tag S (n.eval * n.eval) sc)
    (hnonneg : ∀ i, 0 ≤ sc i)
    (hcompat : ∀ i, k.eval ≤ i.val → sc i = 0 → M i ⟨k.eval, hk⟩ = 0)
    (hH : Writable st.store tag H ho.eval n.eval)
    (hlog : ∀ j : Fin n.eval, j.val < k.eval →
      st.store.read tag H (ho.eval + j) = some ((p j).val : ℝ) ∧ j ≤ p j)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSH : S ≠ H) (hLH : L ≠ H) (hUH : U ≠ H)
    (hLU : L ≠ U) (base : Store P ℝ)
    (hframe : Frame base n.eval S L U H lo.eval uo.eval ho.eval st.store) :
    ∃ (out : St P ℝ C) (r : Fin n.eval),
      exec I (do
        scaledPartialPivot tag n k S 0 S (n * n) ⟨H, ho + k⟩
        Builder.bindIdx tag ⟨H, ho + k⟩ n fun selected =>
          swapRows tag n n L lo k (.var selected)).run st = some out ∧
      k.eval ≤ r.val ∧ Frame base n.eval S L U H lo.eval uo.eval ho.eval out.store ∧
      Holds out.store tag S 0 (M.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      Holds out.store tag L lo.eval (F.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      Holds out.store tag U uo.eval G ∧
      ReadsDecoded out.store (fun _ x => x) tag S (n.eval * n.eval)
        (fun i => sc ((Equiv.swap ⟨k.eval, hk⟩ r) i)) ∧
      (∀ i, k.eval ≤ i.val → |M i ⟨k.eval, hk⟩| / sc i ≤ |M r ⟨k.eval, hk⟩| / sc r) ∧
      (∀ j : Fin n.eval, j.val < k.eval + 1 →
        out.store.read tag H (ho.eval + j) =
          some (((Function.update p ⟨k.eval, hk⟩ r) j).val : ℝ) ∧
          j ≤ Function.update p ⟨k.eval, hk⟩ r j) := by
  have hcell : Writable st.store tag H (ho + k).eval 1 := fun i hi => by
    obtain ⟨len, hlen, hlt⟩ := hH (k.eval + i) (by omega)
    exact ⟨len, hlen, by simpa only [IExp.eval_add, Nat.add_assoc] using hlt⟩
  obtain ⟨pivoted, r, hr₁, hkr, hw, hM', hsc', hread, hmax, -, -⟩ :=
    exec_scaledPartialPivot I hI tag st n k S 0 S (n * n) ⟨H, ho + k⟩ M sc hk hM hsc
      hnonneg hcompat hcell (by simp [blockDisjoint, IExp.eval]) hSH hSH
  have hout (q : P) (b i : ℕ) (hbS : b ≠ S) (hbH : b ≠ H) :
      pivoted.store.read q b i = st.store.read q b i := by
    apply Store.read_of_writeBlocks_eq_some_of_forall hw
    intro block hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact Or.inl hbS
    · exact Or.inl hbS
    · exact Or.inl hbH
  have hi : IsIndexExactSem (fun _ x => x) n.eval I.sem := by
    rw [hI]; exact isIndexExactSem_exactSem _
  obtain ⟨out, LW, hr₂, hwL, hF'⟩ := PLU.exec_swapRows_of_index I tag pivoted n k hi L lo
    ⟨H, ho + k⟩ r.val r hk hread rfl F
    (fun i j => (hout tag L _ hSL.symm hLH).trans (hF i j))
  have hf : Frame base n.eval S L U H lo.eval uo.eval ho.eval pivoted.store := by
    apply hframe.writeBlocks hw
    intro block hb b i hbS _ _ hbH
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact Or.inl hbS
    · exact Or.inl hbS
    · simp only [IExp.eval_add]
      omega
  refine ⟨out, r, ?_, hkr, hf.write_lower hwL (by simp), ?_, hF', ?_, ?_, hmax, ?_⟩
  · rw [exec_run_bind I (b := scaledPartialPivot tag n k S 0 S (n * n) ⟨H, ho + k⟩)
      (fun _ => rfl), hr₁, Option.bind_some]
    exact hr₂
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hwL (Or.inl hSL)]
    exact hM' i j
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hwL (Or.inl hLU.symm)]
    exact (hout tag U _ hSU.symm hUH).trans (hG i j)
  · intro i
    obtain ⟨w, hr, hd⟩ := hsc' i
    exact ⟨w, (Store.read_of_writeBlock_eq_some_of_ne hwL (Or.inl hSL)).trans hr, hd⟩
  · intro j hj
    rw [Store.read_of_writeBlock_eq_some_of_ne hwL (Or.inl hLH.symm)]
    exact log_update p r hk hkr _ _ hw hSH hread hlog j hj

end NLAlib.Computation.ScaledPLU
