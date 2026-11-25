/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineFrames
public import NLAlib.Computation.Contract
public import NLAlib.Computation.MatrixStorage
public import NLAlib.Matrix.Computation.RowSwap
public import NLAlib.Matrix.Computation.PartialPivot

/-!
# Store frames for pivoted dense elimination

A pivoted elimination step changes one residual matrix, two factor matrices and a prefix of
the pivot log. The footprint below keeps their complete outside-cell frame across row
exchanges, column materialization and Schur updates.

## Main definitions

* `NLAlib.Computation.PLU.Frame`: the residual, factor and pivot-log footprint.

## Main results

* `NLAlib.Computation.PLU.Frame.write_residual`: a full residual write keeps the frame.
* `NLAlib.Computation.PLU.Frame.write_lower`, `NLAlib.Computation.PLU.Frame.write_upper`:
  full factor writes keep the frame.
* `NLAlib.Computation.PLU.Frame.write_history`: one committed log entry keeps the frame.
* `NLAlib.Computation.PLU.exec_swapRows_of_index`: consume a recorded row through `bindIdx`.
-/

@[expose] public section

namespace NLAlib.Computation.PLU

variable {P K : Type} [DecidableEq P]

/-- A pivoted elimination store has the initial buffer shape, and every cell outside its
square residual matrix, two square factor blocks and length-$N$ pivot log reads as initially,
at every precision tag. This is the net storage footprint, independently of arithmetic or
the values held inside the four blocks. -/
structure Frame (base : Store P K) (N S L U H lo uo ho : ℕ) (s : Store P K) : Prop where
  /-- All buffer capacities and tags remain fixed. -/
  shape : s.shape = base.shape
  /-- Cells outside all four writable blocks are retained. -/
  outside : ∀ q b i, (b ≠ S ∨ N * N ≤ i) →
    (b ≠ L ∨ i < lo ∨ lo + N * N ≤ i) →
    (b ≠ U ∨ i < uo ∨ uo + N * N ≤ i) →
    (b ≠ H ∨ i < ho ∨ ho + N ≤ i) → s.read q b i = base.read q b i

variable {base s s' : Store P K} {N S L U H lo uo ho : ℕ} {tag : P}

/-- An initial store satisfies its four-block pivoted elimination footprint. -/
theorem Frame.refl (base : Store P K) (N S L U H lo uo ho : ℕ) :
    Frame base N S L U H lo uo ho base :=
  ⟨rfl, fun _ _ _ _ _ _ _ => rfl⟩

/-- Replacing the complete residual matrix preserves the elimination footprint. -/
theorem Frame.write_residual (h : Frame base N S L U H lo uo ho s) {W : Array K}
    (hw : s.writeBlock tag S 0 W = some s') (hsize : W.size = N * N) :
    Frame base N S L U H lo uo ho s' := by
  refine ⟨(Store.shape_of_writeBlock_eq_some hw).trans h.shape, ?_⟩
  intro q b i hbS hbL hbU hbH
  rw [Store.read_of_writeBlock_eq_some_of_ne hw (by
    rw [hsize]
    omega)]
  exact h.outside q b i hbS hbL hbU hbH

/-- Replacing the complete lower factor preserves the elimination footprint. -/
theorem Frame.write_lower (h : Frame base N S L U H lo uo ho s) {W : Array K}
    (hw : s.writeBlock tag L lo W = some s') (hsize : W.size = N * N) :
    Frame base N S L U H lo uo ho s' := by
  refine ⟨(Store.shape_of_writeBlock_eq_some hw).trans h.shape, ?_⟩
  intro q b i hbS hbL hbU hbH
  rw [Store.read_of_writeBlock_eq_some_of_ne hw (hsize ▸ hbL)]
  exact h.outside q b i hbS hbL hbU hbH

/-- Replacing the complete upper factor preserves the elimination footprint. -/
theorem Frame.write_upper (h : Frame base N S L U H lo uo ho s) {W : Array K}
    (hw : s.writeBlock tag U uo W = some s') (hsize : W.size = N * N) :
    Frame base N S L U H lo uo ho s' := by
  refine ⟨(Store.shape_of_writeBlock_eq_some hw).trans h.shape, ?_⟩
  intro q b i hbS hbL hbU hbH
  rw [Store.read_of_writeBlock_eq_some_of_ne hw (hsize ▸ hbU)]
  exact h.outside q b i hbS hbL hbU hbH

/-- Writing one pivot index inside the declared log preserves the elimination footprint. -/
theorem Frame.write_history (h : Frame base N S L U H lo uo ho s) {k : ℕ} {w : K}
    (hw : s.writeBlock tag H (ho + k) #[w] = some s') (hk : k < N) :
    Frame base N S L U H lo uo ho s' := by
  refine ⟨(Store.shape_of_writeBlock_eq_some hw).trans h.shape, ?_⟩
  intro q b i hbS hbL hbU hbH
  rw [Store.read_of_writeBlock_eq_some_of_ne hw (by
    simp only [Array.size_singleton]
    omega)]
  exact h.outside q b i hbS hbL hbU hbH

/-- Replacing the two complete factors in lower-then-upper order preserves the elimination
footprint. The two writes need not commute for this frame conclusion. -/
theorem Frame.write_factors (h : Frame base N S L U H lo uo ho s) {LW UW : Array K}
    (hw : s.writeBlocks tag [(L, lo, N * N), (U, uo, N * N)] [LW, UW] = some s') :
    Frame base N S L U H lo uo ho s' := by
  obtain ⟨hL, hU, mid, hwL, hwU⟩ := Store.writeBlocks_pair_eq_some_iff.mp hw
  exact (h.write_lower hwL hL).write_upper hwU hU

/-- A stored row index is consumed by the actual bounded index binder before the row
exchange. The index decoding and conversion are exact; the matrix words themselves may have
any carrier. The only net store write is the full exchanged matrix block. -/
theorem exec_swapRows_of_index {ι C : Type} [AddMonoid C] {dec : P → K → ℝ}
    (I : Interp P ι K C) (tag : P) (st : St P K C) (n k : IExp ℕ)
    (hi : IsIndexExactSem dec n.eval I.sem) (L : ℕ) (lo : IExp ℕ)
    (index : Cell ℕ ℕ) (iw : K) (r : Fin n.eval) (hk : k.eval < n.eval)
    (hread : st.store.read tag index.buf index.idx.eval = some iw)
    (hdec : dec tag iw = (r.val : ℝ)) (F : Matrix (Fin n.eval) (Fin n.eval) K)
    (hF : Holds st.store tag L lo.eval F) :
    ∃ (out : St P K C) (W : Fin (n.eval * n.eval) → K),
      exec I (Builder.bindIdx tag index n fun selected =>
        swapRows tag n n L lo k (.var selected)).run st = some out ∧
      st.store.writeBlock tag L lo.eval (Array.ofFn W) = some out.store ∧
      Holds out.store tag L lo.eval (F.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) := by
  have hto : I.sem.toNat tag iw = some r.val := by
    rw [hi.toNat tag iw, hdec]
    simp
  let ready : St P K C := { st with cnt := st.cnt + I.charge (.toNat tag) }
  obtain ⟨out, W, hr, hw, hF'⟩ := exec_swapRows I tag ready n n L lo k (.var r.val) F hk
    r.isLt hF
  refine ⟨out, W, ?_, hw, ?_⟩
  · change exec I (.seq (.bindIdx tag index n _) .skip) st = some out
    rw [exec_seq_skip, exec_bindIdx_of_read I hread hto r.isLt.le]
    exact hr
  · simpa only [IExp.eval_var, Fin.eta] using hF'

/-- Partial pivoting followed by the recorded exchange of lower-factor rows is an actual
successful program phase. It swaps residual and multiplier rows consistently, preserves the
upper factor, records the absolute selected row and retains every earlier log entry. The
selected entry is maximal in absolute value in the active column, including a zero column. -/
theorem exec_pivotPhase {ι C : Type} [AddMonoid C]
    (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P) (st : St P ℝ C)
    (n k : IExp ℕ) (S L U H : ℕ) (lo uo ho : IExp ℕ)
    (M F G : Matrix (Fin n.eval) (Fin n.eval) ℝ) (p : Fin n.eval → Fin n.eval)
    (hk : k.eval < n.eval) (hM : Holds st.store tag S 0 M)
    (hF : Holds st.store tag L lo.eval F) (hG : Holds st.store tag U uo.eval G)
    (hH : Writable st.store tag H ho.eval n.eval)
    (hlog : ∀ j : Fin n.eval, j.val < k.eval →
      st.store.read tag H (ho.eval + j) = some ((p j).val : ℝ) ∧ j ≤ p j)
    (hSL : S ≠ L) (hSU : S ≠ U) (hSH : S ≠ H) (hLH : L ≠ H) (hUH : U ≠ H)
    (hLU : L ≠ U) (base : Store P ℝ)
    (hframe : Frame base n.eval S L U H lo.eval uo.eval ho.eval st.store) :
    ∃ (out : St P ℝ C) (r : Fin n.eval),
      exec I (do
        partialPivot tag n k S 0 ⟨H, ho + k⟩
        Builder.bindIdx tag ⟨H, ho + k⟩ n fun selected =>
          swapRows tag n n L lo k (.var selected)).run st = some out ∧
      k.eval ≤ r.val ∧
      Frame base n.eval S L U H lo.eval uo.eval ho.eval out.store ∧
      Holds out.store tag S 0 (M.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      Holds out.store tag L lo.eval (F.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      Holds out.store tag U uo.eval G ∧
      (∀ i : Fin n.eval, k.eval ≤ i.val → |M i ⟨k.eval, hk⟩| ≤ |M r ⟨k.eval, hk⟩|) ∧
      (∀ j : Fin n.eval, j.val < k.eval + 1 →
        out.store.read tag H (ho.eval + j) =
            some (((Function.update p ⟨k.eval, hk⟩ r) j).val : ℝ) ∧
          j ≤ Function.update p ⟨k.eval, hk⟩ r j) := by
  have hs : IsRelErrSem (fun _ => 0) (fun _ x => x) (fun _ _ => True) I.sem := by
    rw [hI]
    exact isRelErrSem_exactSem
  have hi : IsIndexExactSem (fun _ x => x) n.eval I.sem := by
    rw [hI]
    exact isIndexExactSem_exactSem _
  have hcell : Writable st.store tag H (ho + k).eval 1 := fun i hi => by
    obtain ⟨len, hlen, hlt⟩ := hH (k.eval + i) (by omega)
    exact ⟨len, hlen, by simpa only [IExp.eval_add, Nat.add_assoc] using hlt⟩
  obtain ⟨pivoted, r, W, iw, mid, hr₁, hwS, hwH, hdi, hkr, hM', hmax, -⟩ :=
    hs.exec_partialPivot I tag st n k hi S 0 ⟨H, ho + k⟩ M hk
      (fun i j => ⟨M i j, hM i j, rfl⟩) hcell hSH
  change st.store.writeBlock tag S 0 (Array.ofFn W) = some mid at hwS
  change mid.writeBlock tag H (ho.eval + k.eval) #[iw] = some pivoted.store at hwH
  have hFp : Holds pivoted.store tag L lo.eval F := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hwH (Or.inl hLH),
      Store.read_of_writeBlock_eq_some_of_ne hwS (Or.inl hSL.symm)]
    exact hF i j
  have hGp : Holds pivoted.store tag U uo.eval G := fun i j => by
    rw [Store.read_of_writeBlock_eq_some_of_ne hwH (Or.inl hUH),
      Store.read_of_writeBlock_eq_some_of_ne hwS (Or.inl hSU.symm)]
    exact hG i j
  have hread : pivoted.store.read tag H (ho + k).eval = some iw := by
    simpa [IExp.eval_add] using
      Store.read_of_writeBlock_eq_some_of_lt (j := 0) hwH (by simp)
  obtain ⟨out, LW, hr₂, hwL, hF'⟩ := exec_swapRows_of_index I tag pivoted n k hi L lo
    ⟨H, ho + k⟩ iw r hk hread hdi F hFp
  have hlog' : ∀ j : Fin n.eval, j.val < k.eval + 1 →
      pivoted.store.read tag H (ho.eval + j) =
          some (((Function.update p ⟨k.eval, hk⟩ r) j).val : ℝ) ∧
        j ≤ Function.update p ⟨k.eval, hk⟩ r j := by
    intro j hj
    by_cases hjk : j = ⟨k.eval, hk⟩
    · subst j
      rw [Function.update_self]
      exact ⟨by simpa only [IExp.eval_add, hdi] using hread, hkr⟩
    · have hj' : j.val < k.eval := by
        have hne : j.val ≠ k.eval := fun h => hjk (Fin.ext h)
        omega
      rw [Function.update_of_ne hjk]
      obtain ⟨hreadj, hjp⟩ := hlog j hj'
      refine ⟨?_, hjp⟩
      rw [Store.read_of_writeBlock_eq_some_of_ne hwH (Or.inr (Or.inl (by omega))),
        Store.read_of_writeBlock_eq_some_of_ne hwS (Or.inl hSH.symm)]
      exact hreadj
  refine ⟨out, r, ?_, hkr,
    ((hframe.write_residual hwS (by simp)).write_history hwH hk).write_lower hwL (by simp),
    ?_, hF', ?_, hmax, ?_⟩
  · rw [exec_run_bind I (b := partialPivot tag n k S 0 ⟨H, ho + k⟩)
      (fun _ => rfl), hr₁, Option.bind_some]
    exact hr₂
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hwL (Or.inl hSL)]
    obtain ⟨w, hw, hd⟩ := hM' i j
    simpa only [hd, IExp.eval_zero] using hw
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hwL (Or.inl hLU.symm)]
    exact hGp i j
  · intro j hj
    rw [Store.read_of_writeBlock_eq_some_of_ne hwL (Or.inl hLH.symm)]
    exact hlog' j hj

/-- Full factor matrices, a complete pivot log, the original shape and the complete outside
frame determine the exact lower-then-upper-then-log block writes. The three output buffers
are distinct; no initialized contents or valid handles are required for empty blocks. -/
theorem writeBlocks_factors_history {𝕜 : Type} [RCLike 𝕜] {N : ℕ}
    {initial final : Store P 𝕜} {tag : P} {L U H lo uo ho : ℕ}
    (F G : Matrix (Fin N) (Fin N) 𝕜) (history : Fin N → 𝕜)
    (hLU : L ≠ U) (hLH : L ≠ H) (hUH : U ≠ H)
    (hshape : final.shape = initial.shape)
    (hF : Holds final tag L lo F) (hG : Holds final tag U uo G)
    (hH : ∀ j : Fin N, final.read tag H (ho + j) = some (history j))
    (hframe : ∀ q b i, (b ≠ L ∨ i < lo ∨ lo + N * N ≤ i) →
      (b ≠ U ∨ i < uo ∨ uo + N * N ≤ i) →
      (b ≠ H ∨ i < ho ∨ ho + N ≤ i) → final.read q b i = initial.read q b i) :
    initial.writeBlocks tag [(L, lo, N * N), (U, uo, N * N), (H, ho, N)]
      [flatten F, flatten G, Array.ofFn history] = some final := by
  refine Store.writeBlocks_eq_some_of_read
    (bs := [(L, lo, N * N), (U, uo, N * N), (H, ho, N)])
    (ys := [flatten F, flatten G, Array.ofFn history])
    (.cons (size_flatten F) (.cons (size_flatten G) (.cons (by simp) .nil))) ?_ hshape ?_ ?_
  · simp [List.pairwise_cons, blockDisjoint, hLU, hLH, hUH]
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
          simpa only [Array.getElem?_ofFn, ht, ↓reduceDIte] using hH ⟨t, ht⟩
        · simp at hx
  · intro q b i hout
    exact hframe q b i (hout _ List.mem_cons_self)
      (hout _ (List.mem_cons_of_mem _ List.mem_cons_self))
      (hout _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

end NLAlib.Computation.PLU
