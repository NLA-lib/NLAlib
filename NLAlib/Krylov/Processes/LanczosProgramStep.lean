/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramState
public import NLAlib.Computation.BLAS.GuardedNormalization

/-!
# Exact steps of the concrete stored-matrix Lanczos program

Compositional execution lemmas for the fixed Paige-order candidate. All arithmetic and
storage conclusions are derived from the actual inline kernel sequence. The shared `State`
invariant retains the input, loaded matrix, every completed basis column and coefficient,
input norm, previous vector and persistent zero scalar.

## Main results

* `exec_step` consumes the proved stored-state invariant and an actual step index, and
  returns execution of the approved inline body and the next exact recurrence state.
* `add_eq_stepCount` identifies the phase-wise operation bounds with the approved
  collected step count. Current memory and tape position remain fixed; the peak grows
  by at most one scratch cell.
No symmetry, nonzero-dimension or nonbreakdown premise is required.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.LanczosImplementation

open Computation Computation.Builder

variable {P ι C : Type} [DecidableEq P] [AddMonoid C]

/-- Exact operation increment of the matvec and previous-vector subtraction. -/
noncomputable def mvPrevCount {P ι : Type} (tag : P) (N : ℕ) : OpCount P ι :=
  (N • Finsupp.single (.lit tag) 1 + (N * N) •
    (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1)) +
    (Finsupp.single (.un tag .neg) 1 + N •
      (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1))

/-- Exact operation increment of the diagonal coefficient and current-vector subtraction. -/
noncomputable def dotNegCount {P ι : Type} (tag : P) (N : ℕ) : OpCount P ι :=
  (N • (Finsupp.single (.un tag .conj) 1 + Finsupp.single (.bin tag .mul) 1 +
    Finsupp.single (.bin tag .add) 1) + Finsupp.single (.lit tag) 1) +
    Finsupp.single (.un tag .neg) 1 + N •
      (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1)

private theorem exec_run_bind_two (I : Interp P ι ℝ C)
    (a b f : Builder P ι ℕ ℕ Unit) (X Y : Stmt P ι ℕ ℕ)
    (ha : ∀ k, ContT.run a k = .seq X (k ()))
    (hb : ∀ k, ContT.run b k = .seq Y (k ())) (st : St P ℝ C) :
    exec I (do a; b; f).run st =
      (exec I (do a; b).run st).bind (exec I f.run) := by
  rw [exec_run_bind I ha, exec_run_bind I ha, Option.bind_assoc]
  congr 1
  funext out
  exact exec_run_bind I hb (fun _ => f) out

private theorem exec_run_bind_three (I : Interp P ι ℝ C)
    (a b c f : Builder P ι ℕ ℕ Unit) (X Y Z : Stmt P ι ℕ ℕ)
    (ha : ∀ k, ContT.run a k = .seq X (k ()))
    (hb : ∀ k, ContT.run b k = .seq Y (k ()))
    (hc : ∀ k, ContT.run c k = .seq Z (k ())) (st : St P ℝ C) :
    exec I (do a; b; c; f).run st =
      (exec I (do a; b; c).run st).bind (exec I f.run) := by
  rw [exec_run_bind I ha, exec_run_bind I ha, Option.bind_assoc]
  congr 1
  funext out
  exact exec_run_bind_two I b c f Y Z hb hc out

/-- Writing the work vector, current alpha, next beta and negative scratch leaves the exact
completed-state invariant unchanged. Those are precisely the temporary writes before the
previous and next basis vectors are committed. -/
theorem State.of_frame {storedMatrix : optParam Bool true}
    {tag : P} {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    {b : Fin N → ℝ} {st out : St P ℝ (OpCount P ι)} (h : State tag N q j A b st storedMatrix)
    (hsh : out.store.shape = st.store.shape)
    (hf : ∀ p k i, k ≠ 7 → (k = 2 → i ≠ j) → (k = 3 → i ≠ j + 1) →
      (k = 8 → i ≠ 1) → out.store.read p k i = st.store.read p k i) :
    State tag N q j A b out storedMatrix := by
  refine ⟨hsh.trans h.shape, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hf tag 0 i (by decide) (by omega) (by omega) (by omega)]
    exact h.input i
  · cases storedMatrix with
    | false => trivial
    | true =>
      intro i k
      rw [hf tag 6 _ (by decide) (by omega) (by omega) (by omega)]
      exact h.matrix i k
  · intro c hc i
    rw [hf tag 1 _ (by decide) (by omega) (by omega) (by omega)]
    exact h.basis c hc i
  · intro c hc
    rw [hf tag 2 c (by decide) (by omega) (by omega) (by omega)]
    exact h.alpha c hc
  · intro c hc
    rw [hf tag 3 c (by decide) (by omega) (by omega) (by omega)]
    exact h.beta c hc
  · rw [hf tag 4 0 (by decide) (by omega) (by omega) (by omega)]
    exact h.inputNorm
  · intro i
    rw [hf tag 5 i (by decide) (by omega) (by omega) (by omega)]
    exact h.prev i
  · rw [hf tag 8 0 (by decide) (by omega) (by omega) (by omega)]
    exact h.zero

/-- Exact subtraction of a stored coefficient times a vector, with its full frame,
operation increment and unchanged current memory. The temporary negation is executed. -/
theorem exec_neg_axpy_count
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (buf : Fin 4 → ℕ)
    (hbuf : Function.Injective buf) (xo yo ai ti : IExp ℕ) (av : ℝ)
    (xs ys : Fin N → ℝ) (ha : st.store.read tag (buf 2) ai.eval = some av)
    (hx : ∀ i : Fin N, st.store.read tag (buf 0) (xo.eval + i) = some (xs i))
    (hy : ∀ i : Fin N, st.store.read tag (buf 1) (yo.eval + i) = some (ys i))
    (ht : ∃ w s, st.store.write tag (buf 3) ti.eval w = some s) :
    ∃ out, exec I (do
        ins (.un tag .neg ⟨buf 3, ti⟩ ⟨buf 2, ai⟩)
        axpy tag ⟨buf 3, ti⟩ (buf 0) xo (buf 1) yo (.const N)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, out.store.read tag (buf 1) (yo.eval + i) = some (ys i - av * xs i)) ∧
      (∀ q b i, (b ≠ buf 1 ∨ i < yo.eval ∨ yo.eval + N ≤ i) →
        (b = buf 3 → i ≠ ti.eval) → out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + (Finsupp.single (.un tag .neg) 1 +
        N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1)) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  have hne : ∀ i j : Fin 4, i ≠ j → buf i ≠ buf j := fun _ _ hij he => hij (hbuf he)
  obtain ⟨old, s, hs⟩ := ht
  obtain ⟨s₁, hs₁⟩ := Store.exists_write_eq_some_of_write_eq_some hs (-av)
  let st₁ := { st with store := s₁, cnt := st.cnt + I.charge (.un tag .neg) }
  have hneg : exec I (ins (.un tag .neg ⟨buf 3, ti⟩ ⟨buf 2, ai⟩)).run st = some st₁ :=
    (exec_seq_instr_un I ha (by rw [hI]; rfl) hs₁).trans (exec_skip I _)
  have hx₁ : ∀ i : Fin N, st₁.store.read tag (buf 0) (xo.eval + i) = some (xs i) := by
    intro i
    rw [Store.read_of_write_eq_some_of_ne hs₁ (Or.inl (hne 0 3 (by decide))), hx i]
  have hy₁ : ∀ i : Fin N, st₁.store.read tag (buf 1) (yo.eval + i) = some (ys i) := by
    intro i
    rw [Store.read_of_write_eq_some_of_ne hs₁ (Or.inl (hne 1 3 (by decide))), hy i]
  obtain ⟨out, hax, hsh, hread, hframe, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    Computation.exec_axpy_frame I hI hc tag st₁ N ⟨buf 3, ti⟩
      (buf 0) (buf 1) xo yo (-av) xs ys (Store.read_of_write_eq_some hs₁) hx₁ hy₁
      (hne 0 1 (by decide)) (hne 3 1 (by decide))
  refine ⟨out, ?_, hsh.trans (Store.shape_of_write_eq_some hs₁), ?_, ?_, hpos, hcur, hcurW,
    ?_, hpeak, hpeakW⟩
  · rw [exec_run_bind I (b := ins (.un tag .neg ⟨buf 3, ti⟩ ⟨buf 2, ai⟩)) (fun _ => rfl),
      hneg, Option.bind_some]
    exact hax
  · intro i
    simpa only [neg_mul, sub_eq_add_neg] using hread i
  · intro q b i hi hti
    rw [hframe q b i hi]
    apply Store.read_of_write_eq_some_of_ne hs₁
    by_cases hb : b = buf 3
    · exact Or.inr (hti hb)
    · exact Or.inl hb
  · simpa only [st₁, hc.charge_eq, add_assoc] using hcnt

/-- Exact executed projection of the work vector against the current Lanczos column,
including the dot product, stored coefficient, negation, vector update, frame and usage. -/
theorem exec_dot_neg_axpy_count
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (buf : Fin 4 → ℕ)
    (hbuf : Function.Injective buf) (xo yo ai ti : IExp ℕ) (xs ys : Fin N → ℝ)
    (hx : ∀ i : Fin N, st.store.read tag (buf 0) (xo.eval + i) = some (xs i))
    (hy : ∀ i : Fin N, st.store.read tag (buf 1) (yo.eval + i) = some (ys i))
    (ha : ∃ w s, st.store.write tag (buf 2) ai.eval w = some s)
    (ht : ∃ w s, st.store.write tag (buf 3) ti.eval w = some s) :
    ∃ out, exec I (do
        dot tag ⟨buf 2, ai⟩ (buf 0) xo (buf 1) yo (.const N)
        ins (.un tag .neg ⟨buf 3, ti⟩ ⟨buf 2, ai⟩)
        axpy tag ⟨buf 3, ti⟩ (buf 0) xo (buf 1) yo (.const N)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag (buf 2) ai.eval = some (xs ⬝ᵥ ys) ∧
      (∀ i : Fin N, out.store.read tag (buf 1) (yo.eval + i) =
        some (ys i - (xs ⬝ᵥ ys) * xs i)) ∧
      (∀ q b i, (b ≠ buf 1 ∨ i < yo.eval ∨ yo.eval + N ≤ i) →
        (b = buf 2 → i ≠ ai.eval) → (b = buf 3 → i ≠ ti.eval) →
        out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + ((N • (Finsupp.single (.un tag .conj) 1 +
        Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        Finsupp.single (.lit tag) 1) + Finsupp.single (.un tag .neg) 1 +
        N • (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1)) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  have hne : ∀ i j : Fin 4, i ≠ j → buf i ≠ buf j := fun _ _ hij he => hij (hbuf he)
  obtain ⟨mid, hd, hsd, hval, hfd, hpd, hcd, hcwd, hcntd, hmd, hmwd⟩ :=
    Computation.exec_dot_frame I hI hc tag st N ⟨buf 2, ai⟩
      (buf 0) (buf 1) xo yo xs ys hx hy (hne 2 0 (by decide)) (hne 2 1 (by decide)) ha
  have hxm : ∀ i : Fin N, mid.store.read tag (buf 0) (xo.eval + i) = some (xs i) := by
    intro i
    rw [hfd tag (buf 0) _ (Or.inl (hne 0 2 (by decide))), hx i]
  have hym : ∀ i : Fin N, mid.store.read tag (buf 1) (yo.eval + i) = some (ys i) := by
    intro i
    rw [hfd tag (buf 1) _ (Or.inl (hne 1 2 (by decide))), hy i]
  have htm : ∃ w s, mid.store.write tag (buf 3) ti.eval w = some s := by
    obtain ⟨old, s, hs⟩ := ht
    obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_shape_eq hsd hs old
    exact ⟨old, s', hs'⟩
  obtain ⟨out, hna, hsna, hrna, hfna, hpna, hcna, hcwna, hcntna, hmna, hmwna⟩ :=
    exec_neg_axpy_count I hI hc tag mid N buf hbuf xo yo ai ti (xs ⬝ᵥ ys) xs ys
      hval hxm hym htm
  refine ⟨out, ?_, hsna.trans hsd, ?_, hrna, ?_, hpna.trans hpd, hcna.trans hcd,
    hcwna.trans hcwd, ?_, ?_, ?_⟩
  · rw [exec_run_bind I (b := dot tag ⟨buf 2, ai⟩ (buf 0) xo (buf 1) yo (.const N))
      (fun _ => rfl), hd, Option.bind_some]
    exact hna
  · rw [hfna tag (buf 2) ai.eval (Or.inl (hne 2 1 (by decide)))
      (fun h => (hne 2 3 (by decide) h).elim), hval]
  · intro q b i hi hai hti
    rw [hfna q b i hi hti]
    apply hfd
    by_cases hb : b = buf 2
    · exact Or.inr (hai hb)
    · exact Or.inl hb
  · rw [hcntna, hcntd]
    simp only [add_assoc]
  · funext p
    by_cases hp : p = tag
    · subst p
      simp only [hmna, hmd, hcd, Function.update_self, max_assoc, max_self]
    · simp only [hmna, hmd, Function.update_of_ne hp]
  · rw [hmwna, hmwd, hcwd]
    simp only [max_assoc, max_self]

/-- The actual dense matvec, negation and first update in a Paige step compute
$\mathbf{A}\mathbf{v}_j-\beta_j\mathbf{v}_{j-1}$. The completed-state invariant is retained,
and the exact operation increment and one-cell scratch peak are exposed for loop accounting. -/
theorem exec_mv_prev
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    (st : St P ℝ (OpCount P ι)) (h : State tag N q j A b st) :
    ∃ out, exec I (do
        gemv tag (IExp.const N) (IExp.const N) 6 0 1 (IExp.const N * IExp.var j) 7 0
        ins (.un tag .neg ⟨8, 1⟩ ⟨3, .var j⟩)
        axpy tag ⟨8, 1⟩ 5 0 7 0 (.const N)).run st = some out ∧
      State tag N q j A b out ∧
      (∀ i : Fin N, out.store.read tag 7 i =
        some ((A *ᵥ (lanczosState A b j).cur -
          (lanczosState A b j).beta • (lanczosState A b j).prev) i)) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + mvPrevCount tag N ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  let s := lanczosState A b j
  have hx : ∀ i : Fin N,
      st.store.read tag 1 ((IExp.const N * .var j).eval + i) = some (s.cur i) := by
    intro i
    simpa only [IExp.eval_mul, IExp.eval_const, IExp.eval_var] using h.basis j le_rfl i
  have hcap : ∀ i < N, ∃ len, st.store.shape[7]? = some (tag, len) ∧ i < len := by
    intro i hi
    exact ⟨N, by rw [h.shape]; rfl, hi⟩
  obtain ⟨mid, hg, hsg, hrg, hfg, hpg, hcg, hcwg, hcntg, hmg, hmwg⟩ :=
    exec_gemv_frame I hI hc tag st N 6 1 7 (.const N * .var j) A s.cur h.matrix hx
      (by decide) (by decide) hcap
  have hb : mid.store.read tag 3 j = some s.beta := by
    rw [hfg tag 3 j (Or.inl (by decide))]
    exact h.beta j le_rfl
  have hp : ∀ i : Fin N, mid.store.read tag 5 (0 + i) = some (s.prev i) := by
    intro i
    rw [hfg tag 5 _ (Or.inl (by decide))]
    simpa only [zero_add] using h.prev i
  have hw : ∀ i : Fin N, mid.store.read tag 7 (0 + i) = some ((A *ᵥ s.cur) i) := by
    intro i
    simpa only [zero_add] using hrg i
  have hs8 : mid.store.shape[8]? = some (tag, 2) := by rw [hsg, h.shape]; rfl
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 1) (0 : ℝ)
    hs8 (by decide)
  obtain ⟨out, hn, hsn, hrn, hfn, hpn, hcn, hcwn, hcntn, hmn, hmwn⟩ :=
    exec_neg_axpy_count I hI hc tag mid N ![5, 7, 3, 8] (by decide)
      0 0 (.var j) 1 s.beta s.prev (A *ᵥ s.cur) hb hp hw ⟨0, s', hs'⟩
  have hstate : State tag N q j A b out := h.of_frame (hsn.trans hsg) (by
    intro p k i hk _ _ ht
    exact (hfn p k i (Or.inl hk) ht).trans (hfg p k i (Or.inl hk)))
  refine ⟨out, ?_, hstate, ?_, hpn.trans hpg, hcn.trans hcg, hcwn.trans hcwg, ?_, ?_, ?_⟩
  · rw [exec_run_bind I (b := gemv tag (.const N) (.const N) 6 0 1
      (.const N * .var j) 7 0) (fun _ => rfl), hg, Option.bind_some]
    exact hn
  · intro i
    simpa only [s, Matrix.cons_val_zero, Matrix.cons_val_one, IExp.eval_zero, zero_add,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hrn i
  · rw [hcntn, hcntg]
    simp only [mvPrevCount, add_assoc]
  · rw [hmn, hmg, hcg]
    simp only [Function.update_self, max_assoc, max_self, Function.update_idem]
  · rw [hmwn, hmwg, hcwg]
    simp only [max_assoc, max_self]

/-- The actual diagonal-coefficient and second update in a Paige step produce its exact
unnormalized next vector. The completed prefix, counts, frame and scratch peak are retained. -/
theorem exec_project {storedMatrix : optParam Bool true}
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    (st : St P ℝ (OpCount P ι)) (h : State tag N q j A b st storedMatrix) (hj : j < q)
    (hw : ∀ i : Fin N, st.store.read tag 7 i =
      some ((A *ᵥ (lanczosState A b j).cur -
        (lanczosState A b j).beta • (lanczosState A b j).prev) i)) :
    ∃ out, exec I (do
        dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N)
        ins (.un tag .neg ⟨8, 1⟩ ⟨2, .var j⟩)
        axpy tag ⟨8, 1⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N)).run st = some out ∧
      State tag N q j A b out storedMatrix ∧
      out.store.read tag 2 j = some (lanczosAlpha A (lanczosState A b j)) ∧
      (∀ i : Fin N, out.store.read tag 7 i = some
        ((A *ᵥ (lanczosState A b j).cur - (lanczosState A b j).beta •
          (lanczosState A b j).prev - lanczosAlpha A (lanczosState A b j) •
            (lanczosState A b j).cur) i)) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + dotNegCount tag N ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  let s := lanczosState A b j
  let w := A *ᵥ s.cur - s.beta • s.prev
  have hx : ∀ i : Fin N,
      st.store.read tag 1 ((IExp.const N * .var j).eval + i) = some (s.cur i) := by
    intro i
    simpa only [IExp.eval_mul, IExp.eval_const, IExp.eval_var] using h.basis j le_rfl i
  have hy : ∀ i : Fin N, st.store.read tag 7 (0 + i) = some (w i) := by
    intro i
    simpa only [zero_add] using hw i
  have hs2 : st.store.shape[2]? = some (tag, q) := by rw [h.shape]; rfl
  have hs8 : st.store.shape[8]? = some (tag, 2) := by rw [h.shape]; rfl
  obtain ⟨sa, hsa⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := j) (0 : ℝ) hs2 hj
  obtain ⟨sn, hsn⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := 1) (0 : ℝ)
    hs8 (by decide)
  obtain ⟨out, hr, hsh, ha, hz, hf, hp, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_dot_neg_axpy_count I hI hc tag st N ![1, 7, 2, 8] (by decide)
      (IExp.const N * IExp.var j) 0 (IExp.var j) 1 s.cur w hx hy ⟨0, sa, hsa⟩ ⟨0, sn, hsn⟩
  have hα : s.cur ⬝ᵥ w = lanczosAlpha A s := by
    simp only [lanczosAlpha, star_trivial, RCLike.re_to_real, w, RCLike.ofReal_real_eq_id, id_eq]
  have hstate : State tag N q j A b out storedMatrix := h.of_frame hsh (by
    intro p k i hk hai _ hti
    exact hf p k i (Or.inl hk) hai hti)
  refine ⟨out, hr, hstate, ?_, ?_, hp, hcur, hcurW, ?_, hpeak, hpeakW⟩
  · change out.store.read tag 2 j = some (s.cur ⬝ᵥ w) at ha
    simpa only [hα, s] using ha
  · intro i
    simpa only [s, w, Matrix.cons_val_zero, Matrix.cons_val_one, IExp.eval_zero, zero_add,
      hα, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hz i
  · simpa only [dotNegCount] using hcnt

/-- Committing the new column and previous vector extends the completed recurrence prefix.
All other cells are transported by the concrete copy/normalization frame. -/
theorem State.succ_of_commit {storedMatrix : optParam Bool true}
    {tag : P} {N q j : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {st out : St P ℝ (OpCount P ι)} (h : State tag N q j A b st storedMatrix)
    (ha : st.store.read tag 2 j = some (lanczosAlpha A (lanczosState A b j)))
    (hb : st.store.read tag 3 (j + 1) = some ((lanczosState A b (j + 1)).beta))
    (hsh : out.store.shape = st.store.shape)
    (hv : ∀ i : Fin N, out.store.read tag 1 (N * (j + 1) + i) =
      some ((lanczosState A b (j + 1)).cur i))
    (hp : ∀ i : Fin N, out.store.read tag 5 i =
      some ((lanczosState A b (j + 1)).prev i))
    (hf : ∀ p k i, k ≠ 5 → (k ≠ 1 ∨ i < N * (j + 1) ∨ N * (j + 1) + N ≤ i) →
      out.store.read p k i = st.store.read p k i) : State tag N q (j + 1) A b out storedMatrix := by
  refine ⟨hsh.trans h.shape, ?_, ?_, ?_, ?_, ?_, ?_, hp, ?_⟩
  · intro i
    exact (hf tag 0 i (by decide) (Or.inl (by decide))).trans (h.input i)
  · cases storedMatrix with
    | false => trivial
    | true =>
      intro i k
      exact (hf tag 6 _ (by decide) (Or.inl (by decide))).trans (h.matrix i k)
  · intro c hc i
    by_cases he : c = j + 1
    · subst c; exact hv i
    · have hcj : c ≤ j := by omega
      have hi : N * c + i < N * (j + 1) := by
        have := Nat.add_mul_lt_mul_of_lt_of_lt i.isLt (Nat.lt_succ_of_le hcj)
        simpa only [Nat.add_comm] using this
      exact (hf tag 1 _ (by decide) (Or.inr (Or.inl hi))).trans (h.basis c hcj i)
  · intro c hc
    rw [hf tag 2 c (by decide) (Or.inl (by decide))]
    by_cases he : c = j
    · subst c; exact ha
    · exact h.alpha c (by omega)
  · intro c hc
    rw [hf tag 3 c (by decide) (Or.inl (by decide))]
    by_cases he : c = j + 1
    · subst c; exact hb
    · exact h.beta c (by omega)
  · exact (hf tag 4 0 (by decide) (Or.inl (by decide))).trans h.inputNorm
  · exact (hf tag 8 0 (by decide) (Or.inl (by decide))).trans h.zero

/-- Upper operation count of committing a step: copy the previous vector, compare the norm,
then fill or copy and divide the new column. -/
noncomputable def commitCount {P ι : Type} (tag : P) (N : ℕ) : OpCount P ι :=
  N • Finsupp.single (.copy tag) 1 + Finsupp.single (.cmp tag) 1 + N •
    (Finsupp.single (.lit tag) 1 + Finsupp.single (.copy tag) 1 +
      Finsupp.single (.bin tag .div) 1)

/-- The next basis column is writable at every actual step, including zero dimension. -/
theorem State.next_capacity {storedMatrix : optParam Bool true}
    {tag : P} {N q j : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {st : St P ℝ (OpCount P ι)} (h : State tag N q j A b st storedMatrix) (hj : j < q) :
    ∀ i < N, ∃ len, st.store.shape[1]? = some (tag, len) ∧
      N * (j + 1) + i < len := by
  intro i hi
  refine ⟨N * (q + 1), by rw [h.shape]; rfl, ?_⟩
  have := Nat.add_mul_lt_mul_of_lt_of_lt hi (Nat.succ_lt_succ hj)
  simpa only [Nat.add_comm] using this

/-- The actual copy-previous then guarded-normalization tail commits the exact next state.
It preserves the candidate's operation order, including the total zero continuation. -/
theorem exec_commit {storedMatrix : optParam Bool true}
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    (st : St P ℝ (OpCount P ι)) (h : State tag N q j A b st storedMatrix) (hj : j < q)
    (ha : st.store.read tag 2 j = some (lanczosAlpha A (lanczosState A b j)))
    (hb : st.store.read tag 3 (j + 1) = some ((lanczosState A b (j + 1)).beta))
    (hw : ∀ i : Fin N, st.store.read tag 7 i = some
      ((A *ᵥ (lanczosState A b j).cur - (lanczosState A b j).beta •
        (lanczosState A b j).prev - lanczosAlpha A (lanczosState A b j) •
          (lanczosState A b j).cur) i)) :
    ∃ out, exec I (do
        copyv tag 1 (IExp.const N * IExp.var j) 5 0 (IExp.const N)
        ifThenElse tag .eq ⟨3, IExp.var j + 1⟩ ⟨8, 0⟩
          (forRange (IExp.const N) fun i =>
            ins (.lit tag ⟨1, IExp.const N * (IExp.var j + 1) + IExp.var i⟩ 0))
          (do copyv tag 7 0 1 (IExp.const N * (IExp.var j + 1)) (IExp.const N)
              rscl tag ⟨3, IExp.var j + 1⟩ 1
                (IExp.const N * (IExp.var j + 1)) (IExp.const N))).run st = some out ∧
      State tag N q (j + 1) A b out storedMatrix ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt ≤ st.cnt + commitCount tag N ∧ out.peak = st.peak ∧
      out.peakW = st.peakW := by
  let s := lanczosState A b j
  let z := A *ᵥ s.cur - s.beta • s.prev - lanczosAlpha A s • s.cur
  let xs : ℕ → ℝ := fun i => if hi : i < N then s.cur ⟨i, hi⟩ else 0
  let zs : ℕ → ℝ := fun i => if hi : i < N then z ⟨i, hi⟩ else 0
  have hx : ∀ i < N, st.store.read tag 1 (N * j + i) = some (xs i) := by
    intro i hi; simpa only [xs, dif_pos hi] using h.basis j le_rfl ⟨i, hi⟩
  have hcap : ∀ i < N, ∃ len, st.store.shape[5]? = some (tag, len) ∧ 0 + i < len := by
    intro i hi; exact ⟨N, by rw [h.shape]; rfl, by simpa only [zero_add] using hi⟩
  obtain ⟨mid, hr, hsh, hv, hf, hp, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_copyv_frame I hc tag st (.const N) 1 5 (IExp.const N * IExp.var j) 0 xs
      (by simpa only [IExp.eval_mul, IExp.eval_const, IExp.eval_var] using hx)
      (by decide) hcap
  have hz : ∀ i < N, mid.store.read tag 7 (0 + i) = some (zs i) := by
    intro i hi; rw [hf tag 7 _ (Or.inl (by decide))]
    simpa only [zs, dif_pos hi, zero_add] using hw ⟨i, hi⟩
  have hzs : (fun i : Fin N => zs i) = z := by
    funext i; simp only [zs, dif_pos i.isLt]
  have hn : mid.store.read tag 3 ((IExp.var j + 1).eval) =
      some ‖WithLp.toLp 2 (fun i : Fin N => zs i)‖ := by
    rw [hf tag 3 _ (Or.inl (by decide))]
    rw [hzs]
    simpa only [IExp.eval_add, IExp.eval_var, IExp.eval_one, lanczosState, lanczosStep,
      RCLike.ofReal_real_eq_id, id_eq, z, s] using hb
  have hzero : mid.store.read tag 8 (0 : IExp ℕ).eval = some 0 :=
    (hf tag 8 _ (Or.inl (by decide))).trans h.zero
  obtain ⟨out, hr', hsh', hv', hf', hp', hcur', hcurW', hcnt', hpeak', hpeakW'⟩ :=
    exec_normalize_branch I hI hc tag mid ![7, 1, 3, 8] (by decide)
      (.const N) 0 (IExp.const N * (IExp.var j + 1)) (IExp.var j + 1) 0 zs hz hn hzero
      (by change ∀ i < N, ∃ len, mid.store.shape[1]? = some (tag, len) ∧
          N * (j + 1) + i < len
          simpa only [hsh] using h.next_capacity hj)
  have hstate : State tag N q (j + 1) A b out storedMatrix := h.succ_of_commit ha hb
    (hsh'.trans hsh) (by
      intro i
      have hvv := hv' i i.isLt
      change out.store.read tag 1 (N * (j + 1) + i) =
        some (zs i / ‖WithLp.toLp 2 (fun k : Fin N => zs k)‖) at hvv
      rw [hzs] at hvv
      simpa only [zs, dif_pos i.isLt, lanczosState, lanczosStep,
        RCLike.ofReal_real_eq_id, id_eq, s, z, Pi.smul_apply, smul_eq_mul,
        div_eq_mul_inv, mul_comm] using hvv) (by
      intro i
      rw [hf' tag 5 i (Or.inl (by decide))]
      simpa [xs, lanczosState, lanczosStep, s] using hv i i.isLt) (by
      intro p k i hk hi
      exact (hf' p k i (by simpa using hi)).trans (hf p k i (Or.inl hk)))
  refine ⟨out, ?_, hstate, hp'.trans hp, hcur'.trans hcur, hcurW'.trans hcurW,
    ?_, hpeak'.trans hpeak, hpeakW'.trans hpeakW⟩
  · rw [exec_run_bind I (b := copyv tag 1 (IExp.const N * IExp.var j) 5 0 (.const N))
      (fun _ => rfl), hr, Option.bind_some]
    exact hr'
  · simpa only [hcnt, commitCount, IExp.eval_const, add_assoc] using hcnt'

/-- Exact operation increment of the actual dot-then-square-root norm kernel. -/
noncomputable def normCount {P ι : Type} (tag : P) (N : ℕ) : OpCount P ι :=
  N • (Finsupp.single (.un tag .conj) 1 + Finsupp.single (.bin tag .mul) 1 +
    Finsupp.single (.bin tag .add) 1) + Finsupp.single (.lit tag) 1 +
      Finsupp.single (.un tag .sqrt) 1

/-- Executing the actual norm on the projected work vector writes the next recurrence beta,
retaining its input work vector and the newly computed alpha. -/
theorem exec_next_norm {storedMatrix : optParam Bool true}
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    (st : St P ℝ (OpCount P ι)) (h : State tag N q j A b st storedMatrix) (hj : j < q)
    (ha : st.store.read tag 2 j = some (lanczosAlpha A (lanczosState A b j)))
    (hw : ∀ i : Fin N, st.store.read tag 7 i = some
      ((A *ᵥ (lanczosState A b j).cur - (lanczosState A b j).beta •
        (lanczosState A b j).prev - lanczosAlpha A (lanczosState A b j) •
          (lanczosState A b j).cur) i)) :
    ∃ out, exec I (nrm2 tag ⟨3, IExp.var j + 1⟩ 7 0 (IExp.const N)).run st = some out ∧
      State tag N q j A b out storedMatrix ∧
      out.store.read tag 2 j = some (lanczosAlpha A (lanczosState A b j)) ∧
      out.store.read tag 3 (j + 1) = some ((lanczosState A b (j + 1)).beta) ∧
      (∀ i : Fin N, out.store.read tag 7 i = some
        ((A *ᵥ (lanczosState A b j).cur - (lanczosState A b j).beta •
          (lanczosState A b j).prev - lanczosAlpha A (lanczosState A b j) •
            (lanczosState A b j).cur) i)) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + normCount tag N ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  let z := A *ᵥ (lanczosState A b j).cur - (lanczosState A b j).beta •
    (lanczosState A b j).prev - lanczosAlpha A (lanczosState A b j) •
      (lanczosState A b j).cur
  let xs : ℕ → ℝ := fun i => if hi : i < N then z ⟨i, hi⟩ else 0
  have hx : ∀ i < N, st.store.read tag 7 (0 + i) = some (xs i) := by
    intro i hi; simpa only [xs, dif_pos hi, zero_add] using hw ⟨i, hi⟩
  have hs : st.store.shape[3]? = some (tag, q + 1) := by rw [h.shape]; rfl
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape (i := j + 1)
    (0 : ℝ) hs (Nat.succ_lt_succ hj)
  obtain ⟨out, hr, hsh, hb, hf, hp, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_nrm2_frame I hI hc tag st ⟨3, IExp.var j + 1⟩ 7 0 (.const N) xs hx
      (by change (3 : ℕ) ≠ 7; decide) ⟨0, s', hs'⟩
  have hstate : State tag N q j A b out storedMatrix := h.of_frame hsh (by
    intro p k i _ _ hbi _
    apply hf p k i
    by_cases hk : k = 3
    · subst k; exact Or.inr (by simpa using hbi rfl)
    · exact Or.inl hk)
  refine ⟨out, hr, hstate, (hf tag 2 j (Or.inl (by change (2 : ℕ) ≠ 3; decide))).trans ha, ?_, ?_,
    hp, hcur, hcurW, ?_, hpeak, hpeakW⟩
  · have hxs : (fun i : Fin N => xs i) = z := by
      funext i; simp only [xs, dif_pos i.isLt]
    change out.store.read tag 3 (j + 1) = some ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at hb
    rw [hxs] at hb
    simpa only [lanczosState, lanczosStep, RCLike.ofReal_real_eq_id, id_eq, z] using hb
  · intro i
    exact (hf tag 7 i (Or.inl (by change (7 : ℕ) ≠ 3; decide))).trans (hw i)
  · simpa only [IExp.eval_const, normCount] using hcnt

omit [DecidableEq P] in
/-- The phase-wise operation budgets sum to the approved collected step budget. -/
theorem add_eq_stepCount (tag : P) (N : ℕ) :
    mvPrevCount (ι := ι) tag N + dotNegCount tag N + normCount tag N +
      commitCount tag N = stepCount tag N := by
  classical
  simp only [mvPrevCount, dotNegCount, normCount, commitCount, stepCount,
    nsmul_add, Finsupp.smul_single, smul_eq_mul, mul_one,
    show N ^ 2 + 4 * N = N * N + N + N + N + N by ring,
    show 2 * N = N + N by omega,
    Finsupp.single_add]
  abel_nf
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  abel

/-- One actual inline Paige step executes the exact Lanczos recurrence, including breakdown
and zero dimension, and satisfies the approved componentwise count and footprint budgets. -/
theorem exec_step (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    (st : St P ℝ (OpCount P ι)) (h : State tag N q j A b st) (hj : j < q) :
    ∃ out, exec I (do
        gemv tag (IExp.const N) (IExp.const N) 6 0 1 (IExp.const N * IExp.var j) 7 0
        ins (.un tag .neg ⟨8, 1⟩ ⟨3, IExp.var j⟩)
        axpy tag ⟨8, 1⟩ 5 0 7 0 (IExp.const N)
        dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N)
        ins (.un tag .neg ⟨8, 1⟩ ⟨2, IExp.var j⟩)
        axpy tag ⟨8, 1⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N)
        nrm2 tag ⟨3, IExp.var j + 1⟩ 7 0 (IExp.const N)
        copyv tag 1 (IExp.const N * IExp.var j) 5 0 (IExp.const N)
        ifThenElse tag .eq ⟨3, IExp.var j + 1⟩ ⟨8, 0⟩
          (forRange (IExp.const N) fun i =>
            ins (.lit tag ⟨1, IExp.const N * (IExp.var j + 1) + IExp.var i⟩ 0))
          (do copyv tag 7 0 1 (IExp.const N * (IExp.var j + 1)) (IExp.const N)
              rscl tag ⟨3, IExp.var j + 1⟩ 1
                (IExp.const N * (IExp.var j + 1)) (IExp.const N))).run st = some out ∧
      State tag N q (j + 1) A b out ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt ≤ st.cnt + stepCount tag N ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  obtain ⟨s₁, hr₁, hs₁, hw₁, hp₁, hc₁, hcw₁, hcnt₁, hm₁, hmw₁⟩ :=
    exec_mv_prev I hI hc tag st h
  obtain ⟨s₂, hr₂, hs₂, ha₂, hw₂, hp₂, hc₂, hcw₂, hcnt₂, hm₂, hmw₂⟩ :=
    exec_project I hI hc tag s₁ hs₁ hj hw₁
  obtain ⟨s₃, hr₃, hs₃, ha₃, hb₃, hw₃, hp₃, hc₃, hcw₃, hcnt₃, hm₃, hmw₃⟩ :=
    exec_next_norm I hI hc tag s₂ hs₂ hj ha₂ hw₂
  obtain ⟨out, hr₄, hs₄, hp₄, hc₄, hcw₄, hcnt₄, hm₄, hmw₄⟩ :=
    exec_commit I hI hc tag s₃ hs₃ hj ha₃ hb₃ hw₃
  refine ⟨out, ?_, hs₄, hp₄.trans (hp₃.trans (hp₂.trans hp₁)),
    hc₄.trans (hc₃.trans (hc₂.trans hc₁)), hcw₄.trans (hcw₃.trans (hcw₂.trans hcw₁)),
    ?_, ?_, ?_⟩
  · rw [exec_run_bind_three I
      (gemv tag (.const N) (.const N) 6 0 1 (IExp.const N * IExp.var j) 7 0)
      (ins (.un tag .neg ⟨8, 1⟩ ⟨3, IExp.var j⟩))
      (axpy tag ⟨8, 1⟩ 5 0 7 0 (.const N)) _ _ _ _
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl), hr₁, Option.bind_some]
    rw [exec_run_bind_three I
      (dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j) 7 0 (.const N))
      (ins (.un tag .neg ⟨8, 1⟩ ⟨2, IExp.var j⟩))
      (axpy tag ⟨8, 1⟩ 1 (IExp.const N * IExp.var j) 7 0 (.const N)) _ _ _ _
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl), hr₂, Option.bind_some]
    rw [exec_run_bind I (b := nrm2 tag ⟨3, IExp.var j + 1⟩ 7 0 (.const N))
      (fun _ => rfl), hr₃, Option.bind_some]
    exact hr₄
  · calc
      out.cnt ≤ s₃.cnt + commitCount tag N := hcnt₄
      _ = st.cnt + stepCount tag N := by
        rw [hcnt₃, hcnt₂, hcnt₁]
        simpa only [add_assoc] using congrArg (st.cnt + ·) (add_eq_stepCount tag N)
  · rw [hm₄, hm₃, hm₂, hm₁, hc₂, hc₁]
    simp only [Function.update_self, max_assoc, max_self, Function.update_idem]
  · rw [hmw₄, hmw₃, hmw₂, hmw₁, hcw₂, hcw₁]
    simp only [max_assoc, max_self]

/-- All actual inline iterations preserve the stored input and compute the full recurrence
prefix, with the approved summed operation budget and one-cell scratch peak bound. -/
theorem exec_steps (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    {N q : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    (st : St P ℝ (OpCount P ι)) (h : State tag N q 0 A b st) :
    ∃ out, exec I (forRange (IExp.const q) fun j => do
        gemv tag (IExp.const N) (IExp.const N) 6 0 1 (IExp.const N * IExp.var j) 7 0
        ins (.un tag .neg ⟨8, 1⟩ ⟨3, IExp.var j⟩)
        axpy tag ⟨8, 1⟩ 5 0 7 0 (IExp.const N)
        dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N)
        ins (.un tag .neg ⟨8, 1⟩ ⟨2, IExp.var j⟩)
        axpy tag ⟨8, 1⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N)
        nrm2 tag ⟨3, IExp.var j + 1⟩ 7 0 (IExp.const N)
        copyv tag 1 (IExp.const N * IExp.var j) 5 0 (IExp.const N)
        ifThenElse tag .eq ⟨3, IExp.var j + 1⟩ ⟨8, 0⟩
          (forRange (IExp.const N) fun i =>
            ins (.lit tag ⟨1, IExp.const N * (IExp.var j + 1) + IExp.var i⟩ 0))
          (do copyv tag 7 0 1 (IExp.const N * (IExp.var j + 1)) (IExp.const N)
              rscl tag ⟨3, IExp.var j + 1⟩ 1
                (IExp.const N * (IExp.var j + 1)) (IExp.const N))).run st = some out ∧
      State tag N q q A b out ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt ≤ st.cnt + q • stepCount tag N ∧
      out.peak ≤ Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW ≤ max st.peakW (st.curW + I.width tag) := by
  let body : ℕ → Builder P ι ℕ ℕ Unit := fun j => do
        gemv tag (IExp.const N) (IExp.const N) 6 0 1 (IExp.const N * IExp.var j) 7 0
        ins (.un tag .neg ⟨8, 1⟩ ⟨3, IExp.var j⟩)
        axpy tag ⟨8, 1⟩ 5 0 7 0 (IExp.const N)
        dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N)
        ins (.un tag .neg ⟨8, 1⟩ ⟨2, IExp.var j⟩)
        axpy tag ⟨8, 1⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N)
        nrm2 tag ⟨3, IExp.var j + 1⟩ 7 0 (IExp.const N)
        copyv tag 1 (IExp.const N * IExp.var j) 5 0 (IExp.const N)
        ifThenElse tag .eq ⟨3, IExp.var j + 1⟩ ⟨8, 0⟩
          (forRange (IExp.const N) fun i =>
            ins (.lit tag ⟨1, IExp.const N * (IExp.var j + 1) + IExp.var i⟩ 0))
          (do copyv tag 7 0 1 (IExp.const N * (IExp.var j + 1)) (IExp.const N)
              rscl tag ⟨3, IExp.var j + 1⟩ 1
                (IExp.const N * (IExp.var j + 1)) (IExp.const N))
  let peak := Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1))
  let R (j : ℕ) (out : St P ℝ (OpCount P ι)) : Prop :=
    State tag N q j A b out ∧ out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt ≤ st.cnt + j • stepCount tag N ∧ out.peak ≤ peak ∧
      out.peakW ≤ max st.peakW (st.curW + I.width tag)
  have h0 : R 0 st := by
    refine ⟨h, rfl, rfl, rfl, by simp only [zero_nsmul, add_zero, le_refl], ?_, le_max_left _ _⟩
    intro p
    by_cases hp : p = tag
    · subst p
      simpa only [peak, Function.update_self] using
        le_max_left (st.peak tag) (st.cur tag + 1)
    · simp only [peak, Function.update_of_ne hp, le_refl]
  have hstep : ∀ j < q, ∀ mid, R j mid → ∃ out,
      exec I (body j).run mid = some out ∧ R (j + 1) out := by
    rintro j hj mid ⟨hs, hp, hcur, hcurW, hcnt, hpeak, hpeakW⟩
    obtain ⟨out, hr, hs', hp', hcur', hcurW', hcnt', hpeak', hpeakW'⟩ :=
      exec_step I hI hc tag mid hs hj
    refine ⟨out, hr, hs', hp'.trans hp, hcur'.trans hcur, hcurW'.trans hcurW, ?_, ?_, ?_⟩
    · calc
        out.cnt ≤ mid.cnt + stepCount tag N := hcnt'
        _ ≤ (st.cnt + j • stepCount tag N) + stepCount tag N := add_le_add hcnt le_rfl
        _ = st.cnt + (j + 1) • stepCount tag N := by rw [succ_nsmul, add_assoc]
    · intro p
      by_cases he : p = tag
      · subst p
        rw [hpeak', Function.update_self, hcur]
        have hpt : mid.peak tag ≤ max (st.peak tag) (st.cur tag + 1) := by
          simpa only [peak, Function.update_self] using hpeak tag
        simpa only [peak, Function.update_self] using
          max_le hpt (le_max_right (st.peak tag) (st.cur tag + 1))
      · simpa only [hpeak', Function.update_of_ne he] using hpeak p
    · rw [hpeakW', hcurW]
      exact max_le hpeakW (le_max_right _ _)
  obtain ⟨out, hr, hs, hp, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exists_exec_loop_eq_some_of_forall I (n := IExp.const q) (body := fun j => (body j).run)
      R h0 hstep
  refine ⟨out, ?_, hs, hp, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  change exec I (.seq (.loop (.const q) (fun j => (body j).run)) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

end NLAlib.LanczosImplementation
