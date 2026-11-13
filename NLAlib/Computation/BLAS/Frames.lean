/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.Normalization
public import NLAlib.Computation.BLAS.MatrixKernels

/-!
# Storage frames for exact BLAS execution

The existing kernels execute with writable output capacity and initialized input windows.
Their frames retain every other cell, the shape, tape positions, current memory, exact
standard operation counts and scratch peaks. Finite-vector wrappers allow arbitrary offsets.
Zero initialization includes both offset and direct-index syntax and zero-length windows.

## Main results

* `exec_copyv_frame`, `exec_gemv_frame`, `exec_rscl_frame`, `exec_nrm2_frame`: kernel frames.
* `exec_dot_frame`, `exec_axpy_frame`: finite-vector pairing and update frames.
* `exec_forRange_zero`, `exec_forRange_zero_var`: exact literal-zero loops and frames.
* `exec_forRange_literal_zero`, `exec_forRange_literal_zero_var`: arbitrary-word zero fills.
* `exec_forRange_zero_var_eq`: semantic equality of direct-index and zero-offset loops.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

open Builder

variable {P ι C : Type} [DecidableEq P] [AddMonoid C]

/-- The actual literal-zero loop succeeds where its output window is writable. It writes
zero to that window, preserves all other cells and every usage field except the literal
count, and keeps the shape. The window may be uninitialized or have length zero. -/
theorem exec_forRange_literal_zero {K : Type} (I : Interp P ι K C) (tag : P)
    (zero : K) (hzero : I.sem.lit tag 0 = some zero)
    (st : St P K C) (n : IExp ℕ) (buf : ℕ) (off : IExp ℕ)
    (hshape : ∀ i < n.eval, ∃ len,
      st.store.shape[buf]? = some (tag, len) ∧ off.eval + i < len) :
    ∃ s', exec I (forRange n fun i => ins (.lit tag ⟨buf, off + .var i⟩ 0)).run st =
      some { st with store := s', cnt := st.cnt + n.eval • I.charge (.lit tag) } ∧
      s'.shape = st.store.shape ∧
      (∀ i < n.eval, s'.read tag buf (off.eval + i) = some zero) ∧
      ∀ q b j, (q ≠ tag ∨ b ≠ buf ∨ j < off.eval ∨ off.eval + n.eval ≤ j) →
        s'.read q b j = st.store.read q b j := by
  let R (k : ℕ) (out : St P K C) : Prop :=
    ∃ s', out = { st with store := s', cnt := st.cnt + k • I.charge (.lit tag) } ∧
      s'.shape = st.store.shape ∧
      (∀ i < k, s'.read tag buf (off.eval + i) = some zero) ∧
      ∀ q b j, (q ≠ tag ∨ b ≠ buf ∨ j < off.eval ∨ off.eval + n.eval ≤ j) →
        s'.read q b j = st.store.read q b j
  have h0 : R 0 st := ⟨st.store, by simp only [zero_nsmul, add_zero], rfl,
    fun i hi => by omega, fun _ _ _ _ => rfl⟩
  have hstep : ∀ i < n.eval, ∀ out, R i out → ∃ out',
      exec I (.seq (.instr (.lit tag ⟨buf, off + .var i⟩ 0)) .skip) out = some out' ∧
        R (i + 1) out' := by
    rintro i hi out ⟨s, rfl, hsh, hread, hframe⟩
    obtain ⟨len, hlen, hlt⟩ := hshape i hi
    have hlen' : s.shape[buf]? = some (tag, len) := by rw [hsh]; exact hlen
    obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape zero hlen' hlt
    refine ⟨{ st with store := s', cnt := st.cnt + (i + 1) • I.charge (.lit tag) },
      ?_, s', rfl, (Store.shape_of_write_eq_some hs').trans hsh, ?_, ?_⟩
    · have hwrite : s.write tag buf (off + IExp.var i).eval zero = some s' := by
        simpa only [IExp.eval_add, IExp.eval_var] using hs'
      have hrun := (exec_seq_instr_lit I (p := tag) (q := 0) (t := .skip)
        (dst := ⟨buf, off + IExp.var i⟩)
        (st := { st with store := s, cnt := st.cnt + i • I.charge (.lit tag) })
        hzero hwrite).trans (exec_skip I _)
      simpa only [succ_nsmul, add_assoc] using hrun
    · intro j hj
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hji
      · exact Store.read_of_write_eq_some hs'
      · rw [Store.read_of_write_eq_some_of_ne hs' (Or.inr (by omega))]
        exact hread j hji
    · intro q b j hout
      have hne : q ≠ tag ∨ b ≠ buf ∨ j ≠ off.eval + i := by
        rcases hout with hq | hb | hj | hj
        · exact Or.inl hq
        · exact Or.inr (Or.inl hb)
        · exact Or.inr (Or.inr (by omega))
        · exact Or.inr (Or.inr (by omega))
      rcases hne with hq | hcell
      · rw [Store.read_of_write_eq_some_of_ne_tag hs' hq]
        exact hframe q b j hout
      · rw [Store.read_of_write_eq_some_of_ne hs' hcell]
        exact hframe q b j hout
  obtain ⟨out, hrun, s', hout, hsh, hread, hframe⟩ :=
    exists_exec_loop_eq_some_of_forall I (n := n) R h0 hstep
  refine ⟨s', ?_, hsh, hread, hframe⟩
  change exec I (.seq (.loop n _) .skip) st = _
  rw [exec_seq_skip]
  exact hout ▸ hrun

/-- The actual literal-zero loop succeeds where its output window is writable. It writes
zero to that window, preserves all other cells and every usage field except the literal
count, and keeps the shape. The window may be uninitialized or have length zero. -/
theorem exec_forRange_zero (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P)
    (st : St P ℝ C) (n : IExp ℕ) (buf : ℕ) (off : IExp ℕ)
    (hshape : ∀ i < n.eval, ∃ len,
      st.store.shape[buf]? = some (tag, len) ∧ off.eval + i < len) :
    ∃ s', exec I (forRange n fun i => ins (.lit tag ⟨buf, off + .var i⟩ 0)).run st =
      some { st with store := s', cnt := st.cnt + n.eval • I.charge (.lit tag) } ∧
      s'.shape = st.store.shape ∧
      (∀ i < n.eval, s'.read tag buf (off.eval + i) = some 0) ∧
      ∀ q b j, (q ≠ tag ∨ b ≠ buf ∨ j < off.eval ∨ off.eval + n.eval ≤ j) →
        s'.read q b j = st.store.read q b j := by
  exact exec_forRange_literal_zero I tag 0 (by rw [hI]; simp only [exactSem, Rat.cast_zero])
    st n buf off hshape

/-- The existing copy kernel preserves the entire store outside its destination window,
including earlier columns of the same basis buffer. Writable capacity suffices; destination
entries need not have been initialized. Its operation count and memory footprint are exact. -/
theorem exec_copyv_frame {K : Type} (I : Interp P ι K (OpCount P ι))
    (hc : IsUnitCharge I) (tag : P)
    (st : St P K (OpCount P ι)) (n : IExp ℕ) (src dst : ℕ) (soff doff : IExp ℕ)
    (xs : ℕ → K) (hx : ∀ i < n.eval, st.store.read tag src (soff.eval + i) = some (xs i))
    (hdisjoint : src ≠ dst)
    (hshape : ∀ i < n.eval, ∃ len,
      st.store.shape[dst]? = some (tag, len) ∧ doff.eval + i < len) :
    ∃ out, exec I (copyv tag src soff dst doff n).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i < n.eval, out.store.read tag dst (doff.eval + i) = some (xs i)) ∧
      (∀ q b i, (b ≠ dst ∨ i < doff.eval ∨ doff.eval + n.eval ≤ i) →
        out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + n.eval • Finsupp.single (.copy tag) 1 ∧
      out.peak = st.peak ∧ out.peakW = st.peakW := by
  obtain ⟨s', hs'⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape
    (xs := (List.range n.eval).toArray.map xs) (fun i hi => hshape i (by simpa using hi))
  obtain ⟨out, hrun, hout, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_copyv I hc tag st src soff dst doff n xs hx (fun h => (hdisjoint h).elim) s' hs'
  refine ⟨out, hrun, ?_, ?_, ?_,
    hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  · rw [hout]
    exact Store.shape_of_writeBlock_eq_some hs'
  · intro i hi
    rw [hout]
    simpa only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hi,
      Option.map_some] using Store.read_of_writeBlock_eq_some_of_lt (j := i) hs'
        (by simpa only [Array.size_map, List.size_toArray, List.length_range] using hi)
  · intro q b i hi
    rw [hout]
    apply Store.read_of_writeBlock_eq_some_of_ne hs'
    simpa only [Array.size_map, List.size_toArray, List.length_range] using hi

/-- The actual stored dense matrix kernel has an exact vector output, a full destination
frame, and its published operation and peak-memory bounds. This uses no oracle accuracy
assumption and permits an uninitialized destination. -/
theorem exec_gemv_frame (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A x y : ℕ) (xo : IExp ℕ)
    (M : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ)
    (hA : Holds st.store tag A 0 M)
    (hx : ∀ i : Fin N, st.store.read tag x (xo.eval + i) = some (v i))
    (hyA : y ≠ A) (hyx : y ≠ x)
    (hshape : ∀ i < N, ∃ len, st.store.shape[y]? = some (tag, len) ∧ i < len) :
    ∃ out, exec I (gemv tag (.const N) (.const N) A 0 x xo y 0).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, out.store.read tag y i = some ((M *ᵥ v) i)) ∧
      (∀ q b i, (b ≠ y ∨ N ≤ i) → out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + (N • Finsupp.single (.lit tag) 1 + (N * N) •
        (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1)) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  obtain ⟨s', hs'⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape
    (b := y) (off := 0) (xs := Array.ofFn (M *ᵥ v)) (fun i hi => by
      obtain ⟨len, hl, hi⟩ := hshape i (by simpa using hi)
      exact ⟨len, hl, by simpa only [zero_add] using hi⟩)
  obtain ⟨out, hrun, hout, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_gemv I hI hc tag st (.const N) (.const N) A 0 x xo y 0 M v hA hx
      (fun h => (hyA h).elim) (fun h => (hyx h).elim) s' hs'
  refine ⟨out, hrun, ?_, ?_, ?_, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  · rw [hout]
    exact Store.shape_of_writeBlock_eq_some hs'
  · intro i
    rw [hout]
    simpa only [IExp.eval_zero, zero_add, Array.getElem?_ofFn, dif_pos i.2] using
      Store.read_of_writeBlock_eq_some_of_lt (j := (i : ℕ)) hs' (by simp)
  · intro q b i hi
    rw [hout]
    apply Store.read_of_writeBlock_eq_some_of_ne hs'
    rcases hi with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (by simpa only [Array.size_ofFn, IExp.eval_zero, zero_add] using h))

/-- Exact componentwise division by a nonzero stored scalar, retaining the entire store
outside the divided window and the exact operation count and memory footprint. -/
theorem exec_rscl_frame (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (a : Cell ℕ ℕ) (x : ℕ) (off : IExp ℕ)
    (av : ℝ) (xs : ℕ → ℝ) (hav : av ≠ 0)
    (ha : st.store.read tag a.buf a.idx.eval = some av)
    (hx : ∀ i < n.eval, st.store.read tag x (off.eval + i) = some (xs i))
    (hax : a.buf ≠ x) :
    ∃ out, exec I (rscl tag a x off n).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i < n.eval, out.store.read tag x (off.eval + i) = some (xs i / av)) ∧
      (∀ q b i, (b ≠ x ∨ i < off.eval ∨ off.eval + n.eval ≤ i) →
        out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + n.eval • Finsupp.single (.bin tag .div) 1 ∧
      out.peak = st.peak ∧ out.peakW = st.peakW := by
  obtain ⟨s', hs'⟩ := Store.exists_writeBlock_eq_some
    (xs := (List.range n.eval).toArray.map fun i => xs i / av)
    (fun i hi => ⟨xs i, hx i (by simpa using hi)⟩)
  obtain ⟨out, hrun, hout, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_rscl I hI hc tag st a x off n av xs hav ha hx (fun h => (hax h).elim) s' hs'
  refine ⟨out, hrun, ?_, ?_, ?_, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  · rw [hout]; exact Store.shape_of_writeBlock_eq_some hs'
  · intro i hi
    rw [hout]
    simpa only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hi,
      Option.map_some] using Store.read_of_writeBlock_eq_some_of_lt (j := i) hs'
        (by simpa only [Array.size_map, List.size_toArray, List.length_range] using hi)
  · intro q b i hi
    rw [hout]
    apply Store.read_of_writeBlock_eq_some_of_ne hs'
    simpa only [Array.size_map, List.size_toArray, List.length_range] using hi

/-- The actual exact norm kernel overwrites its scalar destination with the Euclidean norm,
preserves every other cell, and has the existing dot-then-square-root count and scratch peak. -/
theorem exec_nrm2_frame (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (dst : Cell ℕ ℕ) (src : ℕ) (off n : IExp ℕ)
    (xs : ℕ → ℝ) (hx : ∀ i < n.eval, st.store.read tag src (off.eval + i) = some (xs i))
    (hds : dst.buf ≠ src)
    (hd : ∃ w s, st.store.write tag dst.buf dst.idx.eval w = some s) :
    ∃ out, exec I (nrm2 tag dst src off n).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag dst.buf dst.idx.eval =
        some ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ ∧
      (∀ q b i, (b ≠ dst.buf ∨ i ≠ dst.idx.eval) →
        out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + (n.eval • (Finsupp.single (.un tag .conj) 1 +
        Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        Finsupp.single (.lit tag) 1 + Finsupp.single (.un tag .sqrt) 1) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  let r := ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖
  have hsq : r ^ 2 = ∑ i ∈ Finset.range n.eval, xs i * xs i := by
    rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, dotProduct]
    exact Fin.sum_univ_eq_sum_range (fun i => xs i * xs i) n.eval
  have hval : ((√(RCLike.re (∑ i ∈ Finset.range n.eval, star (xs i) * xs i)) : ℝ) : ℝ) =
      r := by
    simp only [star_trivial, RCLike.re_to_real]
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  obtain ⟨old, s, hs⟩ := hd
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_write_eq_some hs r
  obtain ⟨out, hrun, hout, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_nrm2 I hI hc tag st dst src off n xs hx (fun h => (hds h).elim) s'
      (by rw [hval]; exact hs')
  refine ⟨out, hrun, ?_, ?_, ?_, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  · rw [hout]; exact Store.shape_of_write_eq_some hs'
  · rw [hout]; exact Store.read_of_write_eq_some hs'
  · intro q b i hi
    rw [hout]
    exact Store.read_of_write_eq_some_of_ne hs' hi

/-- The actual exact dot kernel returns the finite-vector dot product, with one scalar-cell
write, exact standard operation counts, unchanged tape and current memory, and its one-cell
scratch peak. The destination is writable and lies outside both input buffers. -/
theorem exec_dot_frame (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (dst : Cell ℕ ℕ) (x y : ℕ)
    (xo yo : IExp ℕ) (xs ys : Fin N → ℝ)
    (hx : ∀ i : Fin N, st.store.read tag x (xo.eval + i) = some (xs i))
    (hy : ∀ i : Fin N, st.store.read tag y (yo.eval + i) = some (ys i))
    (hdx : dst.buf ≠ x) (hdy : dst.buf ≠ y)
    (hd : ∃ w s, st.store.write tag dst.buf dst.idx.eval w = some s) :
    ∃ out, exec I (dot tag dst x xo y yo (.const N)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag dst.buf dst.idx.eval = some (xs ⬝ᵥ ys) ∧
      (∀ q b i, (b ≠ dst.buf ∨ i ≠ dst.idx.eval) →
        out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + (N • (Finsupp.single (.un tag .conj) 1 +
        Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        Finsupp.single (.lit tag) 1) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  let xs' : ℕ → ℝ := fun i => if hi : i < N then xs ⟨i, hi⟩ else 0
  let ys' : ℕ → ℝ := fun i => if hi : i < N then ys ⟨i, hi⟩ else 0
  have hval : (∑ i ∈ Finset.range N, star (xs' i) * ys' i) = xs ⬝ᵥ ys := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by simp [xs', ys', i.isLt]
  obtain ⟨old, s, hs⟩ := hd
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_write_eq_some hs (xs ⬝ᵥ ys)
  obtain ⟨out, hrun, hout, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_dot I hI hc tag st dst x xo y yo (.const N) xs' ys'
      (fun i hi => by
        change i < N at hi
        simpa only [xs', dif_pos hi] using hx ⟨i, hi⟩)
      (fun i hi => by
        change i < N at hi
        simpa only [ys', dif_pos hi] using hy ⟨i, hi⟩)
      (fun h => (hdx h).elim) (fun h => (hdy h).elim) s'
      (by simpa only [IExp.eval_const, hval] using hs')
  refine ⟨out, hrun, ?_, ?_, ?_, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  · rw [hout]
    exact Store.shape_of_write_eq_some hs'
  · rw [hout]
    exact Store.read_of_write_eq_some hs'
  · intro q b i hi
    rw [hout]
    exact Store.read_of_write_eq_some_of_ne hs' hi

/-- The actual exact axpy kernel updates a finite output vector, retains every cell outside
its output window, and has exact standard counts and one-cell scratch peak. The source and
output buffers are disjoint, and the coefficient lies outside the output buffer. -/
theorem exec_axpy_frame (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : IsUnitCharge I) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (a : Cell ℕ ℕ) (x y : ℕ)
    (xo yo : IExp ℕ) (av : ℝ) (xs ys : Fin N → ℝ)
    (ha : st.store.read tag a.buf a.idx.eval = some av)
    (hx : ∀ i : Fin N, st.store.read tag x (xo.eval + i) = some (xs i))
    (hy : ∀ i : Fin N, st.store.read tag y (yo.eval + i) = some (ys i))
    (hxy : x ≠ y) (hay : a.buf ≠ y) :
    ∃ out, exec I (axpy tag a x xo y yo (.const N)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, out.store.read tag y (yo.eval + i) = some (ys i + av * xs i)) ∧
      (∀ q b i, (b ≠ y ∨ i < yo.eval ∨ yo.eval + N ≤ i) →
        out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + N • (Finsupp.single (.bin tag .mul) 1 +
        Finsupp.single (.bin tag .add) 1) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  let xs' : ℕ → ℝ := fun i => if hi : i < N then xs ⟨i, hi⟩ else 0
  let ys' : ℕ → ℝ := fun i => if hi : i < N then ys ⟨i, hi⟩ else 0
  obtain ⟨s', hs'⟩ := Store.exists_writeBlock_eq_some (p := tag) (b := y) (off := yo.eval)
    (xs := (List.range N).toArray.map fun i => av * xs' i + ys' i) (fun i hi => by
      have hi' : i < N := by simpa only [Array.size_map, List.size_toArray,
        List.length_range] using hi
      exact ⟨ys ⟨i, hi'⟩, hy ⟨i, hi'⟩⟩)
  obtain ⟨out, hrun, hout, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_axpy I hI hc tag st a x xo y yo (.const N) av xs' ys' ha
      (fun i hi => by
        change i < N at hi
        simpa only [xs', dif_pos hi] using hx ⟨i, hi⟩)
      (fun i hi => by
        change i < N at hi
        simpa only [ys', dif_pos hi] using hy ⟨i, hi⟩)
      (fun h => (hay h).elim) (fun h => (hxy h).elim) s' hs'
  refine ⟨out, hrun, ?_, ?_, ?_, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  · rw [hout]
    exact Store.shape_of_writeBlock_eq_some hs'
  · intro i
    rw [hout]
    simpa [xs', ys', i.isLt, add_comm] using Store.read_of_writeBlock_eq_some_of_lt
      (j := (i : ℕ)) hs' (by simpa only [Array.size_map, List.size_toArray,
        List.length_range] using i.isLt)
  · intro q b i hi
    rw [hout]
    apply Store.read_of_writeBlock_eq_some_of_ne hs'
    simpa only [Array.size_map, List.size_toArray, List.length_range] using hi

/-- The two index-expression representations execute identically, with every scalar
semantics and carrier. This is semantic equality of the actual loops, including failures. -/
theorem exec_forRange_zero_var_eq {K : Type} (I : Interp P ι K C) (tag : P)
    (st : St P K C) (n : IExp ℕ) (buf : ℕ) :
    exec I (forRange n fun i => ins (.lit tag ⟨buf, .var i⟩ 0)).run st =
      exec I (forRange n fun i => ins (.lit tag ⟨buf, 0 + .var i⟩ 0)).run st := by
  change exec I (.seq (.loop n _) .skip) st = exec I (.seq (.loop n _) .skip) st
  rw [exec_seq_skip, exec_seq_skip, exec_loop, exec_loop]
  congr 1
  funext σ i
  change exec I (.seq (.instr (.lit tag ⟨buf, .var i⟩ 0)) .skip) σ =
    exec I (.seq (.instr (.lit tag ⟨buf, 0 + .var i⟩ 0)) .skip) σ
  simp [exec, Instr.run, Instr.kind, IExp.eval]

/-- Direct-index syntax has the same actual zero-word execution and complete frame. -/
theorem exec_forRange_literal_zero_var {K : Type} (I : Interp P ι K C) (tag : P)
    (zero : K) (hzero : I.sem.lit tag 0 = some zero)
    (st : St P K C) (n : IExp ℕ) (buf : ℕ)
    (hshape : ∀ i < n.eval, ∃ len,
      st.store.shape[buf]? = some (tag, len) ∧ i < len) :
    ∃ s', exec I (forRange n fun i => ins (.lit tag ⟨buf, .var i⟩ 0)).run st =
      some { st with store := s', cnt := st.cnt + n.eval • I.charge (.lit tag) } ∧
      s'.shape = st.store.shape ∧
      (∀ i < n.eval, s'.read tag buf i = some zero) ∧
      ∀ q b j, (q ≠ tag ∨ b ≠ buf ∨ n.eval ≤ j) →
        s'.read q b j = st.store.read q b j := by
  obtain ⟨s', hrun, hsh, hread, hframe⟩ := exec_forRange_literal_zero I tag zero hzero
    st n buf 0 (fun i hi => by simpa only [IExp.eval, zero_add] using hshape i hi)
  refine ⟨s', (exec_forRange_zero_var_eq I tag st n buf).trans hrun,
    hsh, ?_, ?_⟩
  · intro i hi
    simpa only [IExp.eval, zero_add] using hread i hi
  · intro q b j hj
    apply hframe q b j
    rcases hj with hq | hb | hj
    · exact Or.inl hq
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inr (by simpa only [IExp.eval, zero_add] using hj)))

/-- Direct-index literal initialization retains the existing offset-kernel guarantees,
including zero-length windows, store frames and exact charges. -/
theorem exec_forRange_zero_var (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P)
    (st : St P ℝ C) (n : IExp ℕ) (buf : ℕ)
    (hshape : ∀ i < n.eval, ∃ len,
      st.store.shape[buf]? = some (tag, len) ∧ i < len) :
    ∃ s', exec I (forRange n fun i => ins (.lit tag ⟨buf, .var i⟩ 0)).run st =
      some { st with store := s', cnt := st.cnt + n.eval • I.charge (.lit tag) } ∧
      s'.shape = st.store.shape ∧
      (∀ i < n.eval, s'.read tag buf i = some 0) ∧
      ∀ q b j, (q ≠ tag ∨ b ≠ buf ∨ n.eval ≤ j) →
        s'.read q b j = st.store.read q b j := by
  exact exec_forRange_literal_zero_var I tag 0
    (by rw [hI]; simp only [exactSem, Rat.cast_zero]) st n buf hshape

end NLAlib.Computation
