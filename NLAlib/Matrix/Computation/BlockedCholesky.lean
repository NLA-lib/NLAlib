/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.BlockedLU
public import NLAlib.Matrix.Computation.CholeskyScaling
public import NLAlib.Matrix.Computation.CholeskyRoutine

/-!
# Blocked Cholesky through LU and column scaling

The actual blocked LU driver supplies the canonical unit lower factor and upper pivots.
Square roots of those pivots scale the lower columns to the canonical Cholesky factor.
Only the factor block remains written after the scoped upper workspace is released.

## Main definitions

* `NLAlib.Computation.blockedCholesky`: the blocked stored Cholesky driver.

## Main results

* `NLAlib.Computation.exec_blockedCholesky`: exact success and the complete output frame.
* `NLAlib.Computation.isCholeskyRoutine_blockedCholesky`: its typed zero-error certificate.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Factor a positive definite square matrix using blocked LU and diagonal-inclusive lower
column scaling. Upper prefixes are explicitly zeroed. Input and output may overlap because
the blocked LU driver copies the original matrix first. [GolubVanLoan2013, §§3.2, 4.2]. -/
def blockedCholesky {P ι VB VI : Type} (p : P) (n b q : IExp VI) (A : VB)
    (ao : IExp VI) (L : VB) (lo : IExp VI) : Builder P ι VB VI Unit := scope do
  let U ← alloc p (n * n)
  blockedLuFactor p n b q A L U ao lo 0
  choleskyScaleColumns p n L U lo 0

variable {P ι : Type} [DecidableEq P]

/-- The complete scoped blocked Cholesky driver composes under arbitrary interpretations. -/
theorem executionComposable_blockedCholesky {K C : Type} [AddMonoid C]
    (I : Interp P ι K C) (p : P) (n b q : IExp ℕ) (A : ℕ) (ao : IExp ℕ)
    (L : ℕ) (lo : IExp ℕ) : ExecutionComposable I (blockedCholesky p n b q A ao L lo) :=
  executionComposable_single I (fun _ => rfl)

namespace BlockedCholesky

/-- The actual body's empty case needs no valid source, output or fresh-workspace handles. -/
theorem exec_body_of_zero {K C : Type} [AddMonoid C] (I : Interp P ι K C)
    (p : P) (st : St P K C) (n b q : IExp ℕ) (A L U : ℕ) (ao lo : IExp ℕ)
    (hn : n.eval = 0) (hb : 0 < b.eval) (hq : q.eval = (n.eval + b.eval - 1) / b.eval) :
    ∃ out, exec I (do
      blockedLuFactor p n b q A L U ao lo 0
      choleskyScaleColumns p n L U lo 0).run st = some out ∧ out.store = st.store := by
  obtain ⟨out, he, hs⟩ := exec_blockedLuFactor_of_zero I p st n b q A L U ao lo 0 hn hb hq
  refine ⟨out, ?_, hs⟩
  rw [executionComposable_blockedLuFactor I p n b q A L U ao lo 0, he, Option.bind_some]
  change exec I (.seq (.loop n _) .skip) out = some out
  simp only [exec_seq_skip, exec_loop, hn, List.range_zero, List.foldlM_nil, Option.pure_def]

private theorem exec_body_of_pos (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (initial : Store P ℝ) (st : St P ℝ (OpCount P ι)) (n b q : IExp ℕ)
    (A L : ℕ) (ao lo : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : M.PosDef) (hn : 0 < n.eval) (hb : 0 < b.eval)
    (hq : q.eval = (n.eval + b.eval - 1) / b.eval)
    (hinput : Holds initial p A ao.eval M)
    (hL : Writable initial p L lo.eval (n.eval * n.eval))
    (hst : st.store = initial.push (p, Array.replicate (n.eval * n.eval) none)) :
    ∃ out, exec I (do
      blockedLuFactor p n b q A L initial.size ao lo 0
      choleskyScaleColumns p n L initial.size lo 0).run st = some out ∧
      initial.writeBlock p L lo.eval (flatten (choleskyLower M)) = some out.store.pop := by
  have hLb : L < initial.size := hL.lt_size (Nat.mul_pos hn hn)
  have hAb : A < initial.size := Store.lt_size_of_read_eq_some (hinput ⟨0, hn⟩ ⟨0, hn⟩)
  have hinput' : Holds st.store p A ao.eval M := fun i j => by
    rw [hst, Store.read_push_of_lt hAb]
    exact hinput i j
  have hL' : Writable st.store p L lo.eval (n.eval * n.eval) := by
    simpa only [hst] using hL.push (p, Array.replicate (n.eval * n.eval) none)
  have hU : Writable st.store p initial.size 0 (n.eval * n.eval) := by
    intro i hi
    exact ⟨n.eval * n.eval, by rw [hst]; exact
      Store.getElem?_shape_push_size initial p (n.eval * n.eval), by omega⟩
  obtain ⟨mid, he, hw, _, hl, hu, _⟩ := exec_blockedLuFactor I hI hc p st n b q A L
    initial.size ao lo 0 M hb hq (fun r => (hM.gaussState_apply_self_pos r).ne')
    hinput' hL' hU (Nat.ne_of_lt hLb)
  obtain ⟨_, _, s, hwl, hwu⟩ := Store.writeBlocks_pair_eq_some_iff.mp hw
  have hf : Store.BlockFrame st.store p initial.size L lo.eval (n.eval * n.eval) st.store
      (fun i => st.store.read p L (lo.eval + i)) :=
    ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  have hf' := (hf.writeBlock (off := 0) (by simpa using hwl)
    (by simp only [size_flatten, zero_add]; exact le_rfl)).writeBlock_scratch
      (fun _ => Nat.ne_of_lt hLb) hwu
  have hs : CholeskyScaling.State st.store p L initial.size lo.eval 0 M 0 mid.store :=
    ⟨⟨_, hf'⟩, fun i j => by simpa only [Nat.not_lt_zero, if_false] using hl i j,
      fun j _ => hu j j⟩
  obtain ⟨out, he', ⟨g, hfout⟩, hout⟩ := CholeskyScaling.exec_columns I hI hc p mid
    st.store n L initial.size lo 0 M hM (Nat.ne_of_lt hLb) hs
  refine ⟨out, ?_, CholeskyFactorization.writeBlock_flatten_of_pop_frame (hst ▸ hfout) hout hL⟩
  rw [executionComposable_blockedLuFactor I p n b q A L initial.size ao lo 0,
    he, Option.bind_some]
  exact he'

end BlockedCholesky

/-- Positive definite input implies successful actual blocked Cholesky execution, the canonical
Cholesky factor and exactly one full output write. Source and output may coincide or overlap.
The supplied positive block width and ceiling count include a final partial panel. At dimension
zero, no valid handles are required, even when the output equals fresh upper scratch.
This theorem uses exact real arithmetic and standard charges. [GolubVanLoan2013, §§3.2, 4.2]. -/
theorem exec_blockedCholesky (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (n b q : IExp ℕ) (A : ℕ) (ao : IExp ℕ)
    (L : ℕ) (lo : IExp ℕ) (M : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hM : M.PosDef) (hb : 0 < b.eval) (hq : q.eval = (n.eval + b.eval - 1) / b.eval)
    (hinput : Holds st.store p A ao.eval M)
    (hL : Writable st.store p L lo.eval (n.eval * n.eval)) :
    ∃ out, exec I (blockedCholesky p n b q A ao L lo).run st = some out ∧
      st.store.writeBlock p L lo.eval (flatten (choleskyLower M)) = some out.store ∧
      Holds out.store p L lo.eval (choleskyLower M) ∧ IsCholesky M (choleskyLower M) := by
  obtain ⟨out, he, hw⟩ := exists_exec_alloc I p (n * n)
    (fun U => ((do
      blockedLuFactor p n b q A L U ao lo 0
      choleskyScaleColumns p n L U lo 0) : Builder P ι ℕ ℕ Unit).run) st
    (fun store => st.store.writeBlock p L lo.eval (flatten (choleskyLower M)) = some store)
    (by
      intro σ hσ
      by_cases hn : n.eval = 0
      · obtain ⟨out, he, hs⟩ := BlockedCholesky.exec_body_of_zero I p σ n b q A L
          st.store.size ao lo hn hb hq
        refine ⟨out, he, ?_⟩
        rw [hs, hσ, Array.pop_push]
        exact Store.writeBlock_eq_some_of_size_eq_zero (by rw [size_flatten, hn])
      · exact BlockedCholesky.exec_body_of_pos I hI hc p st.store σ n b q A L ao lo M
          hM (Nat.pos_of_ne_zero hn) hb hq hinput hL hσ)
  refine ⟨out, ?_, hw, fun i j => ?_, hM.isCholesky_choleskyLower⟩
  · change exec I (.seq (.alloc p (n * n) _) .skip) st = some out
    rw [exec_seq_skip]
    exact he
  · simpa only [Nat.add_assoc] using
      (Store.read_of_writeBlock_eq_some_of_lt hw
        (by rw [size_flatten]; exact Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)).trans
        (getElem?_flatten (choleskyLower M) i j)

/-- Blocked LU followed by actual pivot square roots and lower-column scaling is a certified
zero-error Cholesky routine under exact arithmetic. The source may overlap the factor block. -/
theorem isCholeskyRoutine_blockedCholesky (I : Interp P ι ℝ (OpCount P ι))
    (hI : I.sem = exactSem) (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.PosDef) (b q : IExp ℕ)
    (hb : 0 < b.eval) (hq : q.eval = (N + b.eval - 1) / b.eval)
    (A : ℕ) (ao : IExp ℕ) (L : ℕ) (lo : IExp ℕ) :
    IsCholeskyRoutine I (fun _ x => x) p M 0 (fun s => Holds s p A ao.eval M) L lo
      (blockedCholesky p (.const N) b q A ao L lo) where
  composable := executionComposable_blockedCholesky I p (.const N) b q A ao L lo
  run st hp hw := by
    obtain ⟨out, he, hs, _, herr⟩ := exec_blockedCholesky I hI hc p st (.const N) b q A ao
      L lo M hM hb hq hp hw
    refine ⟨out, flatten (choleskyLower M), size_flatten _, he, hs, ?_⟩
    rw [Array.map_id', unflatten_flatten]
    exact herr.isCholeskyErr

end NLAlib.Computation
