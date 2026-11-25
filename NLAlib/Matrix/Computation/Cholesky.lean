/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Computation.RoutineFrames

/-!
# Stored Cholesky column normalization

One column of Cholesky factorization takes a positive Schur pivot, computes its square root
as the factor's diagonal, and divides the residual column below it by that diagonal. The
routine uses scalar instructions and the existing reciprocal scaling kernel, with no
allocation or oracle call. The Schur update and the full factorization loop are separate.

## Main results

* `NLAlib.Computation.executionComposable_choleskyColumn`: the column routine composes.
* `NLAlib.Computation.exec_choleskyColumn`: exact success, two output blocks and operation
  counts from stored inputs and a positive pivot.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Compute one Cholesky column from a Schur pivot and the residual entries below it:
write the square root of `pivot` into `diag`, then divide the `n` entries of `x` from `xo`
by that diagonal. The diagonal cell must lie outside the vector block. The pivot cell may
coincide with the diagonal or with a vector entry: it is read before either is overwritten.
No scratch storage. [GolubVanLoan2013, §4.2]. -/
def choleskyColumn {P ι VB VI : Type} (p : P) (pivot diag : Cell VB VI)
    (x : VB) (xo n : IExp VI) : Builder P ι VB VI Unit :=
  scope do
    ins (.un p .sqrt diag pivot)
    rscl p diag x xo n

/-- The scoped Cholesky column routine composes with subsequent execution under any
interpretation, independently of arithmetic success. -/
theorem executionComposable_choleskyColumn {P ι K C : Type} [DecidableEq P] [AddMonoid C]
    (I : Interp P ι K C) (p : P) (pivot diag : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) :
    ExecutionComposable I (choleskyColumn p pivot diag x xo n) :=
  executionComposable_single I (fun _ => rfl)

/-- Under exact real arithmetic, a positive stored Schur pivot $a$ and a stored vector
$x_i$ suffice for the Cholesky column routine to succeed. It writes $\sqrt a$ into the diagonal
cell and $x_i/\sqrt a$ into the vector block, with no other store changes. The offsets are
arbitrary, the two output blocks must be disjoint, and the vector may be empty. The routine
keeps the tape and all memory counters and charges one square root and $n$ divisions.
[GolubVanLoan2013, §4.2]. -/
theorem exec_choleskyColumn {P ι : Type} [DecidableEq P]
    (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P)
    (st : St P ℝ (OpCount P ι)) (pivot diag : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ)
    (a : ℝ) (xs : ℕ → ℝ) (ha : 0 < a)
    (hp : st.store.read p pivot.buf pivot.idx.eval = some a)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hd : Writable st.store p diag.buf diag.idx.eval 1)
    (hdis : blockDisjoint (diag.buf, diag.idx.eval, 1) (x, xo.eval, n.eval) = true) :
    ∃ out : St P ℝ (OpCount P ι),
      exec I (choleskyColumn p pivot diag x xo n).run st = some out ∧
      st.store.writeBlocks p [(diag.buf, diag.idx.eval, 1), (x, xo.eval, n.eval)]
        [#[Real.sqrt a], (List.range n.eval).toArray.map fun i => xs i / Real.sqrt a] =
          some out.store ∧
      out.cnt = st.cnt + (Finsupp.single (.un p .sqrt) 1 +
        n.eval • Finsupp.single (.bin p .div) 1) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.peak = st.peak ∧ out.peakW = st.peakW := by
  obtain ⟨len, hlen, hlt⟩ := hd 0 (by omega)
  obtain ⟨mid, hm⟩ := Store.exists_write_eq_some_of_getElem?_shape (Real.sqrt a)
    hlen (by simpa using hlt)
  have hne : ∀ i < n.eval, x ≠ diag.buf ∨ xo.eval + i ≠ diag.idx.eval := by
    intro i hi
    have h := blockDisjoint_iff.mp hdis
    dsimp only at h
    omega
  have hx' : ∀ i < n.eval, mid.read p x (xo.eval + i) = some (xs i) := fun i hi =>
    (Store.read_of_write_eq_some_of_ne hm (hne i hi)).trans (hx i hi)
  obtain ⟨final, hf⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape
    (s := mid) (p := p) (b := x) (off := xo.eval)
    (xs := (List.range n.eval).toArray.map fun i => xs i / Real.sqrt a) (by
      intro i hi
      have hi' : i < n.eval := by simpa using hi
      exact Store.exists_getElem?_shape_of_read_eq_some (hx' i hi'))
  let st₁ : St P ℝ (OpCount P ι) :=
    { st with store := mid, cnt := st.cnt + I.charge (.un p .sqrt) }
  obtain ⟨out, hr, hout, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_rscl I hI hc p st₁ diag x xo n (Real.sqrt a) xs (Real.sqrt_pos.mpr ha).ne'
      (Store.read_of_write_eq_some hm) hx'
      (fun h i hi => ((hne i hi).resolve_left (fun hx => hx h.symm)).symm) final hf
  have hm' : st.store.writeBlock p diag.buf diag.idx.eval #[Real.sqrt a] = some mid := by
    simpa [Store.writeBlock] using hm
  refine ⟨out, ?_, ?_, ?_, hpos, hcur, hcurW, hpeak, hpeakW⟩
  · change exec I (.seq (.seq (.instr (.un p .sqrt diag pivot))
      (rscl p diag x xo n).run) .skip) st = some out
    rw [exec_seq_skip]
    exact (exec_seq_instr_un I hp (by rw [hI]; simp [exactSem, ha.le]) hm).trans hr
  · exact Store.writeBlocks_pair_eq_some_iff.mpr
      ⟨by simp, by simp, mid, hm', by rw [hout]; exact hf⟩
  · simpa [st₁, hc, add_assoc] using hcnt

end NLAlib.Computation
