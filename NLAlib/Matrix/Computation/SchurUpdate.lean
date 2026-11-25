/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.CopyStride
public import NLAlib.Computation.BLAS.MatrixKernels
public import NLAlib.Computation.RoutineFrames
public import NLAlib.Matrix.Factorizations.Elimination

/-!
# Stored Schur complement updates

An elimination step saves its pivot column and row, then applies the existing stored rank-one
update. Saving both operands before the update prevents overwriting a pivot-row entry before
another column consumes it. The exact execution theorem connects the instructions to
`NLAlib.eliminationStep` and retains the complete output block frame.

## Main definitions

* `NLAlib.Computation.prepareSchur`: saved operands and coefficient in caller-owned workspace.

## Main results

* `NLAlib.Computation.SchurPrepared`: the exact saved row, column, coefficient and frame.
* `NLAlib.Computation.exec_prepareSchur`: exact preparation shared by full and panel updates.

* `NLAlib.Computation.executionComposable_schurStep`: composition with a following routine.
* `NLAlib.Computation.exec_schurStep`: successful exact elimination and one net matrix write.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Save the pivot column and row and compute the rank-one coefficient from a minus-one
literal divided by the stored pivot. The caller owns the $2n+1$ workspace words and releases
them after the update. Saving both operands precedes every matrix write. -/
def prepareSchur {P ι VB VI : Type} (p : P) (n : IExp VI) (R work : VB)
    (off pivot : IExp VI) : Builder P ι VB VI Unit := do
  copyStride p n R work (off + n * pivot) 1 0
  copyStride p n R work (off + pivot) n n
  ins (.lit p ⟨work, 2 * n⟩ (-1))
  ins (.bin p .div ⟨work, 2 * n⟩ ⟨work, 2 * n⟩ ⟨R, off + pivot + n * pivot⟩)

/-- Eliminate a nonzero diagonal pivot in a packed square matrix. A scoped workspace saves
the pivot column, pivot row and coefficient before the rank-one update. Its size is
$2n+1$ words in addition to the rank-one kernel's two scratch words.
[GolubVanLoan2013, §3.2]. -/
def schurStep {P ι VB VI : Type} (p : P) (n : IExp VI) (R : VB)
    (off pivot : IExp VI) : Builder P ι VB VI Unit := scope do
  let work ← alloc p (2 * n + 1)
  prepareSchur p n R work off pivot
  ger p n n ⟨work, 2 * n⟩ work 0 work n R off

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- Saving a pivot row, column and coefficient composes with the following routine under
any scalar interpretation. The preparation itself retains its caller-owned workspace. -/
theorem executionComposable_prepareSchur (I : Interp P ι K C) (p : P)
    (n : IExp ℕ) (R work : ℕ) (off pivot : IExp ℕ) :
    ExecutionComposable I (prepareSchur p n R work off pivot) :=
  (executionComposable_single I
    (b := copyStride p n R work (off + n * pivot) 1 0) (fun _ => rfl)).bind
    ((executionComposable_single I
      (b := copyStride p n R work (off + pivot) n n) (fun _ => rfl)).bind
      ((executionComposable_single I
        (b := ins (.lit p ⟨work, 2 * n⟩ (-1))) (fun _ => rfl)).bind
        (executionComposable_single I (fun _ => rfl))))

/-- The scoped elimination step composes with its continuation under any interpretation. -/
theorem executionComposable_schurStep (I : Interp P ι K C) (p : P)
    (n : IExp ℕ) (R : ℕ) (off pivot : IExp ℕ) :
    ExecutionComposable I (schurStep p n R off pivot) :=
  executionComposable_single I (fun _ => rfl)

/-- The actual saved-pivot preparation succeeds from successful literal and quotient scalar
witnesses. It copies the original pivot row and column before materializing the coefficient,
preserves every other buffer and shape, and leaves the scoped-workspace cells initialized.
This execution statement is independent of all numerical error and range models. -/
theorem exec_prepareSchur_of_scalar_results (I : Interp P ι K C)
    (p : P) (st : St P K C) (n : IExp ℕ) (R work : ℕ) (off pivot : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) K) (hk : pivot.eval < n.eval)
    (hM : Holds st.store p R off.eval M) (hne : R ≠ work)
    (hw : st.store.shape[work]? = some (p, 2 * n.eval + 1)) (ell c : K)
    (hell : I.sem.lit p (-1) = some ell)
    (hc : I.sem.bin p .div ell (M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩) = some c) :
    ∃ out, exec I (prepareSchur p n R work off pivot).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ q b i, b ≠ work → out.store.read q b i = st.store.read q b i) ∧
      (∀ i : Fin n.eval, out.store.read p work i = some (M i ⟨pivot.eval, hk⟩)) ∧
      (∀ j : Fin n.eval, out.store.read p work (n.eval + j) = some (M ⟨pivot.eval, hk⟩ j)) ∧
      out.store.read p work (2 * n.eval) = some c := by
  let k : Fin n.eval := ⟨pivot.eval, hk⟩
  obtain ⟨s₁, hr₁, hs₁⟩ := exec_copyStride I p st n R work (off + n * pivot) 1 0
    (fun i => M i k) hne (fun i => by
      simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_one, one_mul,
        Nat.add_right_comm, k] using hM i k)
    (fun i hi => ⟨_, hw, by simp only [IExp.eval_zero]; omega⟩)
  obtain ⟨s₂, hr₂, hs₂⟩ := exec_copyStride I p s₁ n R work (off + pivot) n n
    (M k) hne (fun j => by
      rw [Store.read_of_writeBlock_eq_some_of_ne hs₁ (Or.inl hne)]
      simpa only [IExp.eval_add, k] using hM k j)
    (fun i hi => ⟨_, by rw [Store.shape_of_writeBlock_eq_some hs₁]; exact hw, by omega⟩)
  have hsh₂ : s₂.store.shape = st.store.shape :=
    (Store.shape_of_writeBlock_eq_some hs₂).trans (Store.shape_of_writeBlock_eq_some hs₁)
  obtain ⟨s₃, hs₃, hr₃, -, hv₃, -⟩ := exec_scalar_lit I p s₂ ⟨work, 2 * n⟩ (-1) ell hell
    ⟨_, by rw [hsh₂]; exact hw, by simp only [IExp.eval_mul, IExp.eval_ofNat]; omega⟩
  have hpread : s₃.read p R (off + pivot + n * pivot).eval = some (M k k) := by
    rw [Store.read_of_write_eq_some_of_ne hs₃ (Or.inl hne),
      Store.read_of_writeBlock_eq_some_of_ne hs₂ (Or.inl hne),
      Store.read_of_writeBlock_eq_some_of_ne hs₁ (Or.inl hne)]
    simpa only [IExp.eval_add, IExp.eval_mul, k] using hM k k
  let st₃ : St P K C := { s₂ with store := s₃, cnt := s₂.cnt + I.charge (.lit p) }
  obtain ⟨s₄, hs₄, hr₄, -, hv₄, -⟩ := exec_scalar_bin I p st₃ .div
    ⟨work, 2 * n⟩ ⟨work, 2 * n⟩ ⟨R, off + pivot + n * pivot⟩ ell (M k k)
    c hv₃ hpread hc
    ⟨_, by change s₃.shape[work]? = _
           rw [Store.shape_of_write_eq_some hs₃, hsh₂]; exact hw,
      by simp only [IExp.eval_mul, IExp.eval_ofNat]; omega⟩
  refine ⟨{ st₃ with store := s₄, cnt := st₃.cnt + I.charge (.bin p .div) }, ?_, ?_⟩
  · rw [show (prepareSchur p n R work off pivot) =
        (copyStride p n R work (off + n * pivot) 1 0 >>= fun _ =>
          copyStride p n R work (off + pivot) n n >>= fun _ =>
          ins (.lit p ⟨work, 2 * n⟩ (-1)) >>= fun _ =>
          ins (.bin p .div ⟨work, 2 * n⟩ ⟨work, 2 * n⟩
            ⟨R, off + pivot + n * pivot⟩)) from rfl,
      exec_run_bind I (b := copyStride p n R work (off + n * pivot) 1 0)
        (fun _ => rfl), hr₁, Option.bind_some,
      exec_run_bind I (b := copyStride p n R work (off + pivot) n n)
        (fun _ => rfl), hr₂, Option.bind_some,
      exec_run_bind I (b := ins (.lit p ⟨work, 2 * n⟩ (-1)))
        (fun _ => rfl), hr₃, Option.bind_some]
    exact hr₄
  · refine ⟨(Store.shape_of_write_eq_some hs₄).trans
        ((Store.shape_of_write_eq_some hs₃).trans hsh₂), ?_, ?_, ?_, hv₄⟩
    · intro q b i hb
      rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inl hb),
        Store.read_of_write_eq_some_of_ne hs₃ (Or.inl hb),
        Store.read_of_writeBlock_eq_some_of_ne hs₂ (Or.inl hb),
        Store.read_of_writeBlock_eq_some_of_ne hs₁ (Or.inl hb)]
    · intro i
      rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inr (by simp; omega)),
        Store.read_of_write_eq_some_of_ne hs₃ (Or.inr (by simp; omega)),
        Store.read_of_writeBlock_eq_some_of_ne hs₂ (Or.inr (Or.inl (by omega)))]
      simpa only [IExp.eval_zero, Nat.zero_add, Array.getElem?_ofFn, i.isLt,
        dite_true] using Store.read_of_writeBlock_eq_some_of_lt hs₁
        (show (i : ℕ) < (Array.ofFn (fun i => M i k)).size by simp)
    · intro j
      rw [Store.read_of_write_eq_some_of_ne hs₄ (Or.inr (by simp; omega)),
        Store.read_of_write_eq_some_of_ne hs₃ (Or.inr (by simp; omega))]
      simpa only [Array.getElem?_ofFn, j.isLt, dite_true] using
        Store.read_of_writeBlock_eq_some_of_lt hs₂
          (show (j : ℕ) < (Array.ofFn (M k)).size by simp)

/-- The saved original pivot row and column, exact rank-one coefficient and complete frame
produced by exact Schur preparation. The workspace is separate from the residual matrix. -/
structure SchurPrepared {n : ℕ} (p : P) (initial : Store P ℝ) (work : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (final : Store P ℝ) : Prop where
  /-- Buffer capacities and precision tags are retained. -/
  shape : final.shape = initial.shape
  /-- Every cell outside the workspace retains its value at every precision. -/
  frame : ∀ q b i, b ≠ work → final.read q b i = initial.read q b i
  /-- The saved original pivot column. -/
  col : ∀ i : Fin n, final.read p work i = some (M i k)
  /-- The saved original pivot row. -/
  row : ∀ j : Fin n, final.read p work (n + j) = some (M k j)
  /-- The exact saved rank-one coefficient. -/
  coeff : final.read p work (2 * n) = some ((-1) / M k k)

/-- Exact scalar semantics and a nonzero pivot make the actual saved-pivot preparation
succeed, with its original row/column and coefficient available to subsequent rank-one
updates. Counts may use any additive carrier. -/
theorem exec_prepareSchur (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (p : P) (st : St P ℝ C) (n : IExp ℕ) (R work : ℕ) (off pivot : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : pivot.eval < n.eval)
    (hM : Holds st.store p R off.eval M) (hne : R ≠ work)
    (hw : st.store.shape[work]? = some (p, 2 * n.eval + 1))
    (hp : M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩ ≠ 0) :
    ∃ out, exec I (prepareSchur p n R work off pivot).run st = some out ∧
      SchurPrepared p st.store work M ⟨pivot.eval, hk⟩ out.store := by
  let k : Fin n.eval := ⟨pivot.eval, hk⟩
  obtain ⟨out, hr, hsh, hfr, hcol, hrow, hcoeff⟩ :=
    exec_prepareSchur_of_scalar_results I p st n R work off pivot M hk hM hne hw
      (-1) ((-1) / M k k)
      (by rw [hI]; simp only [exactSem, Rat.cast_neg, Rat.cast_one])
      (by rw [hI]; simp [exactSem, hp, k])
  exact ⟨out, hr, hsh, hfr, hcol, hrow, hcoeff⟩

private theorem schur_matrix_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    M + ((-1) / M k k) • Matrix.vecMulVec (fun i => M i k) (star (M k)) =
      eliminationStep M k := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    star_trivial, eliminationStep_apply, div_eq_mul_inv]
  ring

private theorem holds_of_writeBlock {n : ℕ} {p : P} {R off : ℕ} {s s' : Store P ℝ}
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hw : s.writeBlock p R off (flatten M) = some s') : Holds s' p R off M := by
  intro i j
  have hi : (i : ℕ) + n * j < (flatten M).size := by
    rw [size_flatten]
    exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt
  simpa only [Nat.add_assoc, getElem?_flatten] using
    Store.read_of_writeBlock_eq_some_of_lt hw hi

private theorem exec_schurBody (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n : IExp ℕ)
    (R : ℕ) (off pivot : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hk : pivot.eval < n.eval) (hM : Holds initial p R off.eval M)
    (hp : M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩ ≠ 0)
    (hst : st.store = initial.push (p, Array.replicate (2 * n.eval + 1) none)) :
    ∃ out, exec I (do
        prepareSchur p n R initial.size off pivot
        ger p n n ⟨initial.size, 2 * n⟩ initial.size 0 initial.size n R off).run st = some out ∧
      initial.writeBlock p R off.eval
        (flatten (eliminationStep M ⟨pivot.eval, hk⟩)) = some out.store.pop := by
  let k : Fin n.eval := ⟨pivot.eval, hk⟩
  let E := eliminationStep M k
  have hR : R < initial.size := Store.lt_size_of_read_eq_some (hM k k)
  have hMp : Holds st.store p R off.eval M := fun i j => by
    rw [hst, Store.read_push_of_lt hR]
    exact hM i j
  obtain ⟨mid, hr₁, hprep⟩ := exec_prepareSchur I hI p st n R initial.size off pivot M hk hMp
    (Nat.ne_of_lt hR) (hst ▸ Store.getElem?_shape_push_size initial p (2 * n.eval + 1)) hp
  have hMm : Holds mid.store p R off.eval M := fun i j =>
    (hprep.frame p R _ (Nat.ne_of_lt hR)).trans (hMp i j)
  have hwMm : Writable mid.store p R off.eval (flatten E).size := by
    simpa only [size_flatten] using hMm.writable
  obtain ⟨target, htarget⟩ := hwMm.exists_writeBlock
  obtain ⟨out, hr₂, hout, -⟩ := exec_ger I hI hc p mid n n ⟨initial.size, 2 * n⟩
    initial.size 0 initial.size n R off ((-1) / M k k) (fun i => M i k) (M k) M hMm
    (by simpa only [IExp.eval_mul, IExp.eval_ofNat] using hprep.coeff)
    (by simpa only [IExp.eval_zero, Nat.zero_add] using hprep.col) hprep.row
    (fun h => (Nat.ne_of_gt hR h).elim) (fun h => (Nat.ne_of_gt hR h).elim)
    (fun h => (Nat.ne_of_gt hR h).elim) target (by
      simpa only [schur_matrix_eq, E] using htarget)
  have hF : Store.BlockFrame st.store p initial.size R off.eval (n.eval * n.eval)
      mid.store (fun i => mid.store.read p R (off.eval + i)) :=
    ⟨hprep.shape, fun q b i hb _ => hprep.frame q b i hb, fun _ _ => rfl⟩
  have hF' := hF.writeBlock (off := 0) (by simpa only [Nat.add_zero, hout] using htarget)
    (by simp only [size_flatten, Nat.zero_add]; exact le_refl _)
  have hwM : Writable initial p R off.eval (flatten E).size := by
    simpa only [size_flatten] using hM.writable
  obtain ⟨goal, hgoal⟩ := hwM.exists_writeBlock
  have hFout : Store.BlockFrame
      (initial.push (p, Array.replicate (2 * n.eval + 1) none)) p initial.size R off.eval
      (n.eval * n.eval) out.store (fun i => (flatten E)[i]?) := by
    rw [hout]
    exact (hst ▸ hF').congr (fun i hi => by simp only [size_flatten, Nat.zero_le,
      Nat.zero_add, true_and, if_pos hi, Nat.sub_zero])
  have hpop : out.store.pop = goal :=
    hFout.pop_eq hgoal (by simp only [size_flatten]) (fun _ _ => rfl)
  refine ⟨out, ?_, hpop ▸ hgoal⟩
  have hcomp := executionComposable_prepareSchur I p n R initial.size off pivot
  rw [hcomp, hr₁, Option.bind_some]
  exact hr₂

/-- A nonzero stored pivot suffices for exact elimination to succeed. The only net store
effect is the full packed matrix write of the mathematical elimination step; the saved
column, row, coefficient and kernel scratch are released. The pivot index and matrix offset
are arbitrary index expressions. [GolubVanLoan2013, §3.2]. -/
theorem exec_schurStep (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (R : ℕ) (off pivot : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hk : pivot.eval < n.eval)
    (hM : Holds st.store p R off.eval M) (hp : M ⟨pivot.eval, hk⟩ ⟨pivot.eval, hk⟩ ≠ 0) :
    ∃ out, exec I (schurStep p n R off pivot).run st = some out ∧
      st.store.writeBlock p R off.eval (flatten (eliminationStep M ⟨pivot.eval, hk⟩)) =
        some out.store ∧ Holds out.store p R off.eval (eliminationStep M ⟨pivot.eval, hk⟩) := by
  let E := eliminationStep M ⟨pivot.eval, hk⟩
  obtain ⟨out, hr, hw⟩ := exists_exec_alloc I p (2 * n + 1)
    (fun work => (do
      prepareSchur p n R work off pivot
      ger p n n ⟨work, 2 * n⟩ work 0 work n R off).run) st
    (fun s => st.store.writeBlock p R off.eval (flatten E) = some s)
    (fun σ hσ => exec_schurBody I hI hc p st.store σ n R off pivot M hk hM hp
      (by simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_ofNat] using hσ))
  refine ⟨out, ?_, hw, holds_of_writeBlock E hw⟩
  change exec I (.seq (.alloc p (2 * n + 1) _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

end NLAlib.Computation
