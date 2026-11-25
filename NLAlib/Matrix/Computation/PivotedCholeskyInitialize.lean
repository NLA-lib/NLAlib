/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.PivotedCholeskySteps
public import NLAlib.Matrix.Computation.CholeskyFactorization

/-!
# Initialization of diagonal-pivoted Cholesky

The input is copied before the factor is cleared, so source and output may overlap.
Empty dimensions bypass all matrix, factor and history handle requirements.

## Main results

* `NLAlib.Computation.PivotedCholesky.exec_body`: initialized PSD data yields a full stored prefix.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- The body of diagonal-pivoted Cholesky with a caller-provided residual: save input,
initialize the full factor and execute the symmetric pivot steps. -/
def pivotedCholeskyBody {P ι VB VI : Type} (tag : P) (n : IExp VI)
    (A R L H : VB) (ao lo ho : IExp VI) : Builder P ι VB VI Unit := do
  copyv tag A ao R 0 (n * n)
  forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)
  forRange n fun k => pivotedCholeskyStep tag n (.var k) R L H lo ho

namespace PivotedCholesky

variable {P ι : Type} [DecidableEq P]

/-- At dimension zero the body executes only empty loops, for arbitrary word semantics.
Even handles coinciding with a freshly allocated residual are valid in this case. -/
theorem exec_emptyBody {K C : Type} [AddMonoid C] (I : Interp P ι K C) (tag : P)
    (st : St P K C) (n : IExp ℕ) (A R L H : ℕ) (ao lo ho : IExp ℕ) (hn : n.eval = 0) :
    exec I (pivotedCholeskyBody tag n A R L H ao lo ho).run st = some st := by
  change exec I (.seq (.named "copy" _ (.seq (.loop (n * n) _) .skip))
    (.seq (.loop (n * n) _) (.seq (.loop n _) .skip))) st = some st
  simp only [exec_seq, exec_named, exec_loop, IExp.eval_mul, hn, zero_mul,
    List.range_zero, List.foldlM_nil, Option.pure_def, Option.bind_some, exec_skip]

private theorem exec_initialize (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A R L H : ℕ) (ao lo ho : IExp ℕ)
    (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : Holds st.store tag A ao.eval M)
    (hR : Writable st.store tag R 0 (n.eval * n.eval))
    (hL : Writable st.store tag L lo.eval (n.eval * n.eval))
    (hAR : 0 < n.eval → A ≠ R) (hRL : R ≠ L) :
    ∃ out, exec I (do
      copyv tag A ao R 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)).run st = some out ∧
      State st.store tag M R L H lo.eval ho.eval 0 out.store := by
  obtain ⟨copied, he₁, hw₁, hMR⟩ := CholeskyFactorization.exec_copy_residual I hc tag st n
    A R ao M hM hR hAR
  obtain ⟨sl, he₂, hshape, hread, hframe⟩ := exec_forRange_literal_zero I tag 0
    (by rw [hI]; simp only [exactSem, Rat.cast_zero]) copied (n * n) L lo
    (hL.of_shape_eq (Store.shape_of_writeBlock_eq_some hw₁))
  let out : St P ℝ (OpCount P ι) :=
    { copied with store := sl, cnt := copied.cnt + (n * n).eval • I.charge (.lit tag) }
  have hF : PLU.Frame st.store n.eval R L L H lo.eval lo.eval ho.eval out.store := by
    refine ⟨hshape.trans (Store.shape_of_writeBlock_eq_some hw₁), ?_⟩
    intro q b i hbR hbL _ _
    rw [hframe q b i (Or.inr hbL), Store.read_of_writeBlock_eq_some_of_ne hw₁ (by
      simpa only [size_flatten, Nat.zero_add, Nat.not_lt_zero, false_or] using hbR)]
  have hRout : Holds out.store tag R 0 M := fun i j => by
    rw [hframe tag R _ (Or.inr (Or.inl hRL))]
    exact hMR i j
  have hLout : Holds out.store tag L lo.eval (0 : Matrix (Fin n.eval) (Fin n.eval) ℝ) :=
    fun i j => by
      simpa only [out, Nat.add_assoc, Matrix.zero_apply] using hread (i.val + n.eval * j.val)
        (Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)
  refine ⟨out, ?_, State.zero hF hRout hLout⟩
  rw [exec_run_bind I (b := copyv tag A ao R 0 (n * n)) (fun _ => rfl),
    he₁, Option.bind_some]
  exact he₂

/-- The actual body fills every canonical column and actual pivot-log entry. The residual
is fresh scoped storage; only source readability and output capacities are needed. -/
theorem exec_body (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ kind, I.charge kind = Finsupp.single kind 1) (tag : P)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (A L H : ℕ)
    (ao lo ho : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ) (hM : M.PosSemidef)
    (hinput : Holds initial tag A ao.eval M)
    (hL : Writable initial tag L lo.eval (n.eval * n.eval))
    (hH : Writable initial tag H ho.eval n.eval) (hLH : L ≠ H)
    (hstore : st.store = initial.push (tag, Array.replicate (n.eval * n.eval) none)) :
    ∃ out, exec I (pivotedCholeskyBody tag n A initial.size L H ao lo ho).run st = some out ∧
      State st.store tag M initial.size L H lo.eval ho.eval n.eval out.store := by
  by_cases hn : n.eval = 0
  · exact ⟨st, exec_emptyBody I tag st n A initial.size L H ao lo ho hn,
      State.empty st.store tag M initial.size L H lo.eval ho.eval hn⟩
  have hN : 0 < n.eval := Nat.pos_of_ne_zero hn
  have hAb : A < initial.size := Store.lt_size_of_read_eq_some (hinput ⟨0, hN⟩ ⟨0, hN⟩)
  have hLb := hL.lt_size (Nat.mul_pos hN hN)
  have hHb := hH.lt_size hN
  have hMp : Holds st.store tag A ao.eval M := fun i j => by
    rw [hstore, Store.read_push_of_lt hAb]
    exact hinput i j
  have hR : Writable st.store tag initial.size 0 (n.eval * n.eval) := by
    rw [hstore]
    exact writable_of_shape_eq rfl
      (Store.getElem?_shape_push_size initial tag (n.eval * n.eval)) (by omega)
  have hLp : Writable st.store tag L lo.eval (n.eval * n.eval) := hstore ▸ hL.push _
  have hHp : Writable st.store tag H ho.eval n.eval := hstore ▸ hH.push _
  obtain ⟨ready, he₁, hs⟩ := exec_initialize I hI hc tag st n A initial.size L H ao lo ho M
    hMp hR hLp (fun _ => Nat.ne_of_lt hAb) (Nat.ne_of_gt hLb)
  obtain ⟨out, he₂, hout⟩ := exists_exec_loop_eq_some_of_forall I
    (fun k σ => State st.store tag M initial.size L H lo.eval ho.eval k σ.store) hs
    (fun k hk σ hσ => exec_pivotedCholeskyStep I hI hc tag st.store n M hM
      initial.size L H lo ho hLp hHp (Nat.ne_of_gt hLb) (Nat.ne_of_gt hHb) hLH k hk σ hσ)
  refine ⟨out, ?_, hout⟩
  change exec I ((do
    copyv tag A ao initial.size 0 (n * n)
    forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)) >>= fun _ =>
      forRange n fun k => pivotedCholeskyStep tag n (.var k) initial.size L H lo ho).run st = _
  have hcomp : ExecutionComposable I (do
      copyv tag A ao initial.size 0 (n * n)
      forRange (n * n) fun i => ins (.lit tag ⟨L, lo + IExp.var i⟩ 0)) :=
    (executionComposable_single I (fun _ => rfl)).bind
      (executionComposable_single I (fun _ => rfl))
  rw [hcomp, he₁, Option.bind_some]
  change exec I (.seq (.loop n _) .skip) ready = some out
  rw [exec_seq_skip]
  exact he₂

end PivotedCholesky

end NLAlib.Computation
