/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PLUQFrames
public import NLAlib.Matrix.Computation.DiagonalPivot

/-!
# Frames of symmetric Cholesky pivots

The recorded diagonal choice is consumed before exchanging both residual axes and the
factor rows. The existing pivoted-elimination frame is used with coincident factor slots.

## Main results

* `NLAlib.Computation.PivotedCholesky.exec_swaps`: actual symmetric exchange and its frame.
-/

@[expose] public section

namespace NLAlib.Computation.PivotedCholesky

open Builder

/-- Select an active diagonal and exchange both residual axes and full factor rows through
the actual recorded absolute index. The composed pivot phase releases all scratch. -/
def symmetricCholeskyPivot {P ι VB VI : Type} (tag : P) (n k : IExp VI)
    (R L H : VB) (lo ho : IExp VI) : Builder P ι VB VI Unit := scope do
  diagonalPivotChoice tag n k R 0 ⟨H, ho + k⟩
  bindIdx tag ⟨H, ho + k⟩ n fun row => do
    swapRows tag n n R 0 k (.var row)
    swapRows tag n n L lo k (.var row)
  bindIdx tag ⟨H, ho + k⟩ n fun row => swapColumns tag n n R 0 k (.var row)

variable {P ι C : Type} [DecidableEq P] [AddMonoid C]

/-- The composed symmetric pivot releases all internal scratch before continuing. -/
theorem executionComposable_symmetricCholeskyPivot (I : Interp P ι ℝ C) (tag : P)
    (n k : IExp ℕ) (R L H : ℕ) (lo ho : IExp ℕ) :
    ExecutionComposable I (symmetricCholeskyPivot tag n k R L H lo ho) :=
  executionComposable_single I (fun _ => rfl)

/-- Bind the actual logged absolute index, exchange the residual and factor rows, then
bind the retained word to exchange residual columns. All other words are retained. -/
theorem exec_swaps (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (n k : IExp ℕ) (R L H : ℕ) (lo ho : IExp ℕ)
    (M F : Matrix (Fin n.eval) (Fin n.eval) ℝ) (r : Fin n.eval)
    (hk : k.eval < n.eval) (hM : Holds st.store tag R 0 M)
    (hF : Holds st.store tag L lo.eval F)
    (hr : st.store.read tag H (ho + k).eval = some (r.val : ℝ))
    (hRL : R ≠ L) (hRH : R ≠ H) (hLH : L ≠ H) (base : Store P ℝ)
    (hf : PLU.Frame base n.eval R L L H lo.eval lo.eval ho.eval st.store) :
    ∃ out, exec I (do
      bindIdx tag ⟨H, ho + k⟩ n fun row => do
        swapRows tag n n R 0 k (.var row)
        swapRows tag n n L lo k (.var row)
      bindIdx tag ⟨H, ho + k⟩ n fun row =>
        swapColumns tag n n R 0 k (.var row)).run st = some out ∧
      PLU.Frame base n.eval R L L H lo.eval lo.eval ho.eval out.store ∧
      Holds out.store tag R 0
        (M.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) (Equiv.swap ⟨k.eval, hk⟩ r)) ∧
      Holds out.store tag L lo.eval (F.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      ∀ q b i, b ≠ R → b ≠ L → out.store.read q b i = st.store.read q b i := by
  have hi : IsIndexExactSem (fun _ x => x) n.eval I.sem :=
    hI ▸ isIndexExactSem_exactSem _
  obtain ⟨mid, RW, LW, s₁, he₁, hw₁, hw₂, hMR, hFL⟩ :=
    PLUQ.exec_swapRows_pair_of_index I tag st n k hi R L 0 lo ⟨H, ho + k⟩
      (r.val : ℝ) r hk hr rfl M F hM hF hRL
  have hr' : mid.store.read tag H (ho + k).eval = some (r.val : ℝ) := by
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hLH.symm),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hRH.symm)]
    exact hr
  let ready : St P ℝ C := { mid with cnt := mid.cnt + I.charge (.toNat tag) }
  obtain ⟨out, CW, he₂, hw₃, hMC⟩ := exec_swapColumns I tag ready n n R 0 k (.var r.val)
    (M.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) hk r.isLt hMR
  refine ⟨out, ?_, ((hf.write_residual hw₁ (by simp)).write_lower hw₂ (by simp)).write_residual
    hw₃ (by simp), ?_, ?_, ?_⟩
  · rw [exec_run_bind I (b := bindIdx tag ⟨H, ho + k⟩ n fun row => do
        swapRows tag n n R 0 k (.var row); swapRows tag n n L lo k (.var row))
      (fun _ => rfl), he₁, Option.bind_some]
    change exec I (.seq (.bindIdx tag ⟨H, ho + k⟩ n _) .skip) mid = some out
    rw [exec_seq_skip, exec_bindIdx_of_read I hr' (by simp [hI, exactSem]) r.isLt.le]
    exact he₂
  · simpa only [Matrix.submatrix_submatrix, Function.id_comp, Function.comp_id,
      IExp.eval_var, IExp.eval_zero, Fin.eta] using hMC
  · intro i j
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₃ (Or.inl hRL.symm)]
    exact hFL i j
  · intro q b i hbR hbL
    rw [Store.read_of_writeBlock_eq_some_of_ne hw₃ (Or.inl hbR),
      Store.read_of_writeBlock_eq_some_of_ne hw₂ (Or.inl hbL),
      Store.read_of_writeBlock_eq_some_of_ne hw₁ (Or.inl hbR)]

/-- Actual diagonal selection and symmetric exchanges retain all cells outside the
residual, factor, and current history word. The selected diagonal maximizes active magnitude. -/
theorem exec_pivotPhase (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (st : St P ℝ C) (n k : IExp ℕ) (R L H : ℕ) (lo ho : IExp ℕ)
    (M F : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : k.eval < n.eval)
    (hM : Holds st.store tag R 0 M) (hF : Holds st.store tag L lo.eval F)
    (hH : Writable st.store tag H (ho + k).eval 1)
    (hRL : R ≠ L) (hRH : R ≠ H) (hLH : L ≠ H) (base : Store P ℝ)
    (hf : PLU.Frame base n.eval R L L H lo.eval lo.eval ho.eval st.store) :
    ∃ (out : St P ℝ C) (r : Fin n.eval),
      exec I (symmetricCholeskyPivot tag n k R L H lo ho).run st = some out ∧
      k.eval ≤ r.val ∧
      PLU.Frame base n.eval R L L H lo.eval lo.eval ho.eval out.store ∧
      Holds out.store tag R 0
        (M.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) (Equiv.swap ⟨k.eval, hk⟩ r)) ∧
      Holds out.store tag L lo.eval (F.submatrix (Equiv.swap ⟨k.eval, hk⟩ r) id) ∧
      out.store.read tag H (ho.eval + k.eval) = some (r.val : ℝ) ∧
      (∀ i : Fin n.eval, k.eval ≤ i.val → |M i i| ≤ |M r r|) ∧
      ∀ q b i, b ≠ R → b ≠ L → (b ≠ H ∨ i ≠ ho.eval + k.eval) →
        out.store.read q b i = st.store.read q b i := by
  obtain ⟨chosen, r, he₁, hw, hkr, hMC, hmax, -⟩ :=
    exec_diagonalPivotChoice I hI tag st n k R 0 ⟨H, ho + k⟩ M hk hM hH hRH
  change st.store.writeBlock tag H (ho.eval + k.eval) #[(r.val : ℝ)] =
    some chosen.store at hw
  have hFC : Holds chosen.store tag L lo.eval F := fun i j =>
    (Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hLH)).trans (hF i j)
  have hr : chosen.store.read tag H (ho + k).eval = some (r.val : ℝ) := by
    simpa using Store.read_of_writeBlock_eq_some_of_lt hw (j := 0) (by simp)
  obtain ⟨out, he₂, hframe, hMO, hFO, hout⟩ := exec_swaps I hI tag chosen n k
    R L H lo ho M F r hk hMC hFC hr hRL hRH hLH base (hf.write_history hw hk)
  refine ⟨out, r, ?_, hkr, hframe, hMO, hFO, ?_, hmax, ?_⟩
  · change exec I (.seq _ .skip) st = some out
    rw [exec_seq_skip, exec_run_bind I (b := diagonalPivotChoice tag n k R 0 ⟨H, ho + k⟩)
      (fun _ => rfl), he₁, Option.bind_some]
    exact he₂
  · rw [hout tag H _ hRH.symm hLH.symm]
    exact hr
  · intro q b i hbR hbL hbH
    rw [hout q b i hbR hbL, Store.read_of_writeBlock_eq_some_of_ne hw (by
      simp only [Array.size_singleton]
      omega)]

/-- A complete factor, its actual pivot log and the outside frame determine the two net
output writes. Empty matrices require no valid output handles. -/
theorem writeBlocks_factor {N : ℕ} {initial final : Store P ℝ} {tag : P}
    {L H lo ho : ℕ} (F : Matrix (Fin N) (Fin N) ℝ) (p : Fin N → Fin N)
    (hLH : L ≠ H) (hshape : final.shape = initial.shape)
    (hF : Holds final tag L lo F)
    (hH : ∀ j : Fin N, final.read tag H (ho + j) = some ((p j).val : ℝ))
    (hframe : ∀ q b i, (b ≠ L ∨ i < lo ∨ lo + N * N ≤ i) →
      (b ≠ H ∨ i < ho ∨ ho + N ≤ i) → final.read q b i = initial.read q b i) :
    initial.writeBlocks tag [(L, lo, N * N), (H, ho, N)]
      [flatten F, Array.ofFn (fun j => ((p j).val : ℝ))] = some final := by
  apply Store.writeBlocks_eq_some_of_read
    (bs := [(L, lo, N * N), (H, ho, N)])
    (ys := [flatten F, Array.ofFn (fun j => ((p j).val : ℝ))])
    (.cons (size_flatten F) (.cons (by simp) .nil))
  · simp [List.pairwise_cons, blockDisjoint, hLH]
  · exact hshape
  · intro k x y hx hy t ht
    rcases k with _ | k
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      subst x; subst y
      exact hF.read_flatten t ht
    · rcases k with _ | k
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
          at hx hy
        subst x; subst y
        simpa only [Array.getElem?_ofFn, ht, ↓reduceDIte] using hH ⟨t, ht⟩
      · simp at hx
  · intro q b i hout
    exact hframe q b i (hout _ List.mem_cons_self)
      (hout _ (List.mem_cons_of_mem _ List.mem_cons_self))

end NLAlib.Computation.PivotedCholesky
