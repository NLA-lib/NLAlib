/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.MatrixStorage
public import NLAlib.Matrix.Computation.CompletePivot
public import NLAlib.Matrix.Computation.RowSwap
public import NLAlib.Matrix.Computation.ColumnSwap
public import NLAlib.Matrix.Computation.PLUFrames

/-!
# Store frames for complete-pivoted LU

The exact complete-pivoted driver changes its residual, two factors and two recorded pivot
logs. Concrete block-write lemmas retain the complete outside frame.

## Main definitions

* `NLAlib.Computation.PLUQ.Frame`: the five mutable blocks of complete-pivoted elimination.

## Main results

* `NLAlib.Computation.PLUQ.Frame.write_residual`: residual writes preserve the frame.
* `NLAlib.Computation.PLUQ.Frame.write_factors`: factor writes preserve the frame.
-/

@[expose] public section

namespace NLAlib.Computation.PLUQ

variable {P K : Type} [DecidableEq P]

/-- Fixed shape and all-tag reads outside the residual, factors and both pivot logs. -/
structure Frame (base : Store P K) (N S L U Hr Hc lo uo hro hco : ℕ) (s : Store P K) : Prop where
  /-- All buffer capacities and tags remain fixed. -/
  shape : s.shape = base.shape
  /-- Cells outside all five writable blocks are retained. -/
  outside : ∀ q b i, (b ≠ S ∨ N * N ≤ i) →
    (b ≠ L ∨ i < lo ∨ lo + N * N ≤ i) →
    (b ≠ U ∨ i < uo ∨ uo + N * N ≤ i) →
    (b ≠ Hr ∨ i < hro ∨ hro + N ≤ i) →
    (b ≠ Hc ∨ i < hco ∨ hco + N ≤ i) → s.read q b i = base.read q b i

variable {base s s' : Store P K} {N S L U Hr Hc lo uo hro hco : ℕ} {tag : P}

/-- An initial store satisfies its five-block pivoted elimination footprint. -/
theorem Frame.refl (base : Store P K) (N S L U Hr Hc lo uo hro hco : ℕ) :
    Frame base N S L U Hr Hc lo uo hro hco base :=
  ⟨rfl, fun _ _ _ _ _ _ _ _ => rfl⟩

/-- Replacing the complete residual matrix preserves the elimination footprint. -/
theorem Frame.write_residual (h : Frame base N S L U Hr Hc lo uo hro hco s) {W : Array K}
    (hw : s.writeBlock tag S 0 W = some s') (hsize : W.size = N * N) :
    Frame base N S L U Hr Hc lo uo hro hco s' := by
  refine ⟨(Store.shape_of_writeBlock_eq_some hw).trans h.shape, ?_⟩
  intro q b i hbS hbL hbU hbHr hbHc
  rw [Store.read_of_writeBlock_eq_some_of_ne hw (by
    rw [hsize]
    omega)]
  exact h.outside q b i hbS hbL hbU hbHr hbHc

/-- Replacing the complete lower factor preserves the elimination footprint. -/
theorem Frame.write_lower (h : Frame base N S L U Hr Hc lo uo hro hco s) {W : Array K}
    (hw : s.writeBlock tag L lo W = some s') (hsize : W.size = N * N) :
    Frame base N S L U Hr Hc lo uo hro hco s' := by
  refine ⟨(Store.shape_of_writeBlock_eq_some hw).trans h.shape, ?_⟩
  intro q b i hbS hbL hbU hbHr hbHc
  rw [Store.read_of_writeBlock_eq_some_of_ne hw (hsize ▸ hbL)]
  exact h.outside q b i hbS hbL hbU hbHr hbHc

/-- Replacing the complete upper factor preserves the elimination footprint. -/
theorem Frame.write_upper (h : Frame base N S L U Hr Hc lo uo hro hco s) {W : Array K}
    (hw : s.writeBlock tag U uo W = some s') (hsize : W.size = N * N) :
    Frame base N S L U Hr Hc lo uo hro hco s' := by
  refine ⟨(Store.shape_of_writeBlock_eq_some hw).trans h.shape, ?_⟩
  intro q b i hbS hbL hbU hbHr hbHc
  rw [Store.read_of_writeBlock_eq_some_of_ne hw (hsize ▸ hbU)]
  exact h.outside q b i hbS hbL hbU hbHr hbHc

/-- Writing one pivot index inside the declared log preserves the elimination footprint. -/
theorem Frame.write_rowHistory (h : Frame base N S L U Hr Hc lo uo hro hco s) {k : ℕ} {w : K}
    (hw : s.writeBlock tag Hr (hro + k) #[w] = some s') (hk : k < N) :
    Frame base N S L U Hr Hc lo uo hro hco s' := by
  refine ⟨(Store.shape_of_writeBlock_eq_some hw).trans h.shape, ?_⟩
  intro q b i hbS hbL hbU hbHr hbHc
  rw [Store.read_of_writeBlock_eq_some_of_ne hw (by
    simp only [Array.size_singleton]
    omega)]
  exact h.outside q b i hbS hbL hbU hbHr hbHc

/-- Writing one pivot index inside the declared log preserves the elimination footprint. -/
theorem Frame.write_colHistory (h : Frame base N S L U Hr Hc lo uo hro hco s) {k : ℕ} {w : K}
    (hw : s.writeBlock tag Hc (hco + k) #[w] = some s') (hk : k < N) :
    Frame base N S L U Hr Hc lo uo hro hco s' := by
  refine ⟨(Store.shape_of_writeBlock_eq_some hw).trans h.shape, ?_⟩
  intro q b i hbS hbL hbU hbHr hbHc
  rw [Store.read_of_writeBlock_eq_some_of_ne hw (by
    simp only [Array.size_singleton]
    omega)]
  exact h.outside q b i hbS hbL hbU hbHr hbHc

/-- Replacing the two complete factors in lower-then-upper order preserves the elimination
footprint. The two writes need not commute for this frame conclusion. -/
theorem Frame.write_factors (h : Frame base N S L U Hr Hc lo uo hro hco s) {LW UW : Array K}
    (hw : s.writeBlocks tag [(L, lo, N * N), (U, uo, N * N)] [LW, UW] = some s') :
    Frame base N S L U Hr Hc lo uo hro hco s' := by
  obtain ⟨hL, hU, mid, hwL, hwU⟩ := Store.writeBlocks_pair_eq_some_iff.mp hw
  exact (h.write_lower hwL hL).write_upper hwU hU


/-- Full factor matrices, both actual logs and the complete outside frame determine four
ordered net output writes. Empty blocks require no valid output handle. -/
theorem writeBlocks_factors_histories {𝕜 : Type} [RCLike 𝕜] {N : ℕ}
    {initial final : Store P 𝕜} {tag : P} {L U Hr Hc lo uo hro hco : ℕ}
    (F G : Matrix (Fin N) (Fin N) 𝕜) (rows cols : Fin N → 𝕜)
    (hLU : L ≠ U) (hLR : L ≠ Hr) (hLC : L ≠ Hc)
    (hUR : U ≠ Hr) (hUC : U ≠ Hc) (hRC : Hr ≠ Hc)
    (hshape : final.shape = initial.shape)
    (hF : Holds final tag L lo F) (hG : Holds final tag U uo G)
    (hR : ∀ j : Fin N, final.read tag Hr (hro + j) = some (rows j))
    (hC : ∀ j : Fin N, final.read tag Hc (hco + j) = some (cols j))
    (hframe : ∀ q b i, (b ≠ L ∨ i < lo ∨ lo + N * N ≤ i) →
      (b ≠ U ∨ i < uo ∨ uo + N * N ≤ i) →
      (b ≠ Hr ∨ i < hro ∨ hro + N ≤ i) →
      (b ≠ Hc ∨ i < hco ∨ hco + N ≤ i) → final.read q b i = initial.read q b i) :
    initial.writeBlocks tag [(L, lo, N * N), (U, uo, N * N), (Hr, hro, N), (Hc, hco, N)]
      [flatten F, flatten G, Array.ofFn rows, Array.ofFn cols] = some final := by
  refine Store.writeBlocks_eq_some_of_read
    (bs := [(L, lo, N * N), (U, uo, N * N), (Hr, hro, N), (Hc, hco, N)])
    (ys := [flatten F, flatten G, Array.ofFn rows, Array.ofFn cols])
    (.cons (size_flatten F) (.cons (size_flatten G) (.cons (by simp) (.cons (by simp) .nil))))
    ?_ hshape ?_ ?_
  · simp [List.pairwise_cons, blockDisjoint, hLU, hLR, hLC, hUR, hUC, hRC]
  · intro k x y hx hy t ht
    rcases k with _ | k
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      subst x; subst y
      exact hF.read_flatten t ht
    · rcases k with _ | k
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx hy
        subst x; subst y
        exact hG.read_flatten t ht
      · rcases k with _ | k
        · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx hy
          subst x; subst y
          simpa only [Array.getElem?_ofFn, ht, ↓reduceDIte] using hR ⟨t, ht⟩
        · rcases k with _ | k
          · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
              at hx hy
            subst x; subst y
            simpa only [Array.getElem?_ofFn, ht, ↓reduceDIte] using hC ⟨t, ht⟩
          · simp at hx
  · intro q b i hout
    exact hframe q b i (hout _ List.mem_cons_self)
      (hout _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (hout _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      (hout _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))

/-- Consume a recorded index once and exchange two matrices along the rows axis.
The only net writes are the two exchanged matrix blocks, in their execution order. -/
theorem exec_swapRows_pair_of_index {ι C : Type} [AddMonoid C] {dec : P → K → ℝ}
    (I : Interp P ι K C) (tag : P) (st : St P K C) (n k : IExp ℕ)
    (hi : IsIndexExactSem dec n.eval I.sem) (A B : ℕ) (ao bo : IExp ℕ)
    (index : Cell ℕ ℕ) (iw : K) (r : Fin n.eval) (hk : k.eval < n.eval)
    (hread : st.store.read tag index.buf index.idx.eval = some iw)
    (hdec : dec tag iw = (r.val : ℝ)) (F G : Matrix (Fin n.eval) (Fin n.eval) K)
    (hF : Holds st.store tag A ao.eval F) (hG : Holds st.store tag B bo.eval G) (hAB : A ≠ B) :
    ∃ (out : St P K C) (FW GW : Fin (n.eval * n.eval) → K) (mid : Store P K),
      exec I (Builder.bindIdx tag index n fun selected => do
        swapRows tag n n A ao k (.var selected)
        swapRows tag n n B bo k (.var selected)).run st = some out ∧
      st.store.writeBlock tag A ao.eval (Array.ofFn FW) = some mid ∧
      mid.writeBlock tag B bo.eval (Array.ofFn GW) = some out.store ∧
      Holds out.store tag A ao.eval (F.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      Holds out.store tag B bo.eval (G.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) := by
  have hto : I.sem.toNat tag iw = some r.val := by rw [hi.toNat tag iw, hdec]; simp
  let ready : St P K C := { st with cnt := st.cnt + I.charge (.toNat tag) }
  obtain ⟨mid, FW, he₁, hw₁, hF'⟩ := exec_swapRows I tag ready n n A ao k (.var r.val)
    F hk r.isLt hF
  have hG' : Holds mid.store tag B bo.eval G := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hAB.symm)]; exact hG i j
  obtain ⟨out, GW, he₂, hw₂, hG''⟩ := exec_swapRows I tag mid n n B bo k (.var r.val)
    G hk r.isLt hG'
  refine ⟨out, FW, GW, mid.store, ?_, hw₁, hw₂, ?_, ?_⟩
  · change exec I (.seq (.bindIdx tag index n _) .skip) st = some out
    rw [exec_seq_skip, exec_bindIdx_of_read I hread hto r.isLt.le]
    rw [exec_run_bind I (b := swapRows tag n n A ao k (.var r.val)) (fun _ => rfl),
      he₁, Option.bind_some]
    exact he₂
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hAB)]
    simpa only [IExp.eval_var, Fin.eta] using hF' i j
  · simpa only [IExp.eval_var, Fin.eta] using hG''

/-- Consume a recorded index once and exchange two matrices along the columns axis.
The only net writes are the two exchanged matrix blocks, in their execution order. -/
theorem exec_swapColumns_pair_of_index {ι C : Type} [AddMonoid C] {dec : P → K → ℝ}
    (I : Interp P ι K C) (tag : P) (st : St P K C) (n k : IExp ℕ)
    (hi : IsIndexExactSem dec n.eval I.sem) (A B : ℕ) (ao bo : IExp ℕ)
    (index : Cell ℕ ℕ) (iw : K) (r : Fin n.eval) (hk : k.eval < n.eval)
    (hread : st.store.read tag index.buf index.idx.eval = some iw)
    (hdec : dec tag iw = (r.val : ℝ)) (F G : Matrix (Fin n.eval) (Fin n.eval) K)
    (hF : Holds st.store tag A ao.eval F) (hG : Holds st.store tag B bo.eval G) (hAB : A ≠ B) :
    ∃ (out : St P K C) (FW GW : Fin (n.eval * n.eval) → K) (mid : Store P K),
      exec I (Builder.bindIdx tag index n fun selected => do
        swapColumns tag n n A ao k (.var selected)
        swapColumns tag n n B bo k (.var selected)).run st = some out ∧
      st.store.writeBlock tag A ao.eval (Array.ofFn FW) = some mid ∧
      mid.writeBlock tag B bo.eval (Array.ofFn GW) = some out.store ∧
      Holds out.store tag A ao.eval (F.submatrix id (Equiv.swap ⟨k.eval, hk⟩ r)) ∧
      Holds out.store tag B bo.eval (G.submatrix id (Equiv.swap ⟨k.eval, hk⟩ r)) := by
  have hto : I.sem.toNat tag iw = some r.val := by rw [hi.toNat tag iw, hdec]; simp
  let ready : St P K C := { st with cnt := st.cnt + I.charge (.toNat tag) }
  obtain ⟨mid, FW, he₁, hw₁, hF'⟩ := exec_swapColumns I tag ready n n A ao k (.var r.val)
    F hk r.isLt hF
  have hG' : Holds mid.store tag B bo.eval G := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hAB.symm)]; exact hG i j
  obtain ⟨out, GW, he₂, hw₂, hG''⟩ := exec_swapColumns I tag mid n n B bo k (.var r.val)
    G hk r.isLt hG'
  refine ⟨out, FW, GW, mid.store, ?_, hw₁, hw₂, ?_, ?_⟩
  · change exec I (.seq (.bindIdx tag index n _) .skip) st = some out
    rw [exec_seq_skip, exec_bindIdx_of_read I hread hto r.isLt.le]
    rw [exec_run_bind I (b := swapColumns tag n n A ao k (.var r.val)) (fun _ => rfl),
      he₁, Option.bind_some]
    exact he₂
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hAB)]
    simpa only [IExp.eval_var, Fin.eta] using hF' i j
  · simpa only [IExp.eval_var, Fin.eta] using hG''

end NLAlib.Computation.PLUQ
