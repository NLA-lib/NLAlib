/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Contract
public import NLAlib.Computation.RoutineFrames

/-!
# Copying and reindexing operands of triangular solves

Upper and adjoint triangular solves pack a transformed coefficient matrix and right-hand side
before using the stored lower solve. These are actual scalar copy and conjugation loops, with
successful execution and exact decoded outputs under the standard real scalar model.

## Main definitions

* `NLAlib.Computation.TriangularSolve.copyMapped`: gather a vector through symbolic addresses.
* `NLAlib.Computation.TriangularSolve.copyMatrixMapped`: gather a packed square matrix.

## Main results

* `NLAlib.Computation.TriangularSolve.exec_copyMapped`: success and one output block write.
* `NLAlib.Computation.TriangularSolve.exec_copyMatrixMapped`: successful matrix packing and frame.
-/

@[expose] public section

namespace NLAlib.Computation.TriangularSolve

open Builder

/-- Gather `n` words from symbolic source addresses into a packed destination vector. When
`conjugate` is true, each word passes through the scalar conjugation instruction; otherwise
it is copied. The source and destination buffers are separate in the execution theorem. -/
def copyMapped {P ι VB VI : Type} (tag : P) (n : IExp VI) (src : VB)
    (srcAt : IExp VI → IExp VI) (dst : VB) (off : IExp VI) (conjugate : Bool) :
    Builder P ι VB VI Unit :=
  forRange n fun k =>
    if conjugate then ins (.un tag .conj ⟨dst, off + IExp.var k⟩ ⟨src, srcAt (.var k)⟩)
    else ins (.copy tag ⟨dst, off + IExp.var k⟩ ⟨src, srcAt (.var k)⟩)

/-- Gather a square matrix column by column into a packed destination buffer. Source addresses
may transpose or reverse the two symbolic indices. Conjugation is an actual scalar instruction
when requested. -/
def copyMatrixMapped {P ι VB VI : Type} (tag : P) (n : IExp VI) (src : VB)
    (srcAt : IExp VI → IExp VI → IExp VI) (dst : VB) (conjugate : Bool) :
    Builder P ι VB VI Unit :=
  forRange n fun j => copyMapped tag n src (fun i => srcAt i (.var j)) dst
    (n * IExp.var j) conjugate

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

private theorem exec_copyWord {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (I : Interp P ι K C) (h : IsRelErrSem u dec safe I.sem) (tag : P)
    (st : St P K C) (src dst : Cell ℕ ℕ) (conjugate : Bool) (v : K)
    (hv : st.store.read tag src.buf src.idx.eval = some v)
    (hw : ∃ len, st.store.shape[dst.buf]? = some (tag, len) ∧ dst.idx.eval < len) :
    ∃ (out : St P K C) (w : K),
      exec I (if conjugate then ins (.un tag .conj dst src)
        else ins (.copy tag dst src)).run st = some out ∧
      st.store.write tag dst.buf dst.idx.eval w = some out.store ∧
      dec tag w = dec tag v := by
  cases conjugate with
  | false =>
    obtain ⟨s, hs, hr, -, -, -⟩ := exec_scalar_copy I tag st dst src v hv hw
    exact ⟨_, v, hr, hs, rfl⟩
  | true =>
    obtain ⟨w, hword, hdw⟩ := h.conj tag v
    obtain ⟨s, hs, hr, -, -, -⟩ := exec_scalar_un I tag st .conj dst src v w hv hword hw
    exact ⟨_, w, hr, hs, hdw⟩

/-- A mapped gather with distinct source and destination buffers succeeds when every source
address is initialized and the output block is writable. Its only net store effect is the
packed output write, whose decodings equal the supplied vector, including for conjugation
under the real decoding contract. Empty vectors require no buffer capacity. -/
theorem exec_copyMapped {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (I : Interp P ι K C) (h : IsRelErrSem u dec safe I.sem) (tag : P)
    (st : St P K C) (n : IExp ℕ) (src : ℕ) (srcAt : IExp ℕ → IExp ℕ)
    (dst : ℕ) (off : IExp ℕ) (conjugate : Bool) (v : Fin n.eval → ℝ)
    (hin : ∀ i : Fin n.eval, ∃ w,
      st.store.read tag src (srcAt (.var i)).eval = some w ∧ dec tag w = v i)
    (hw : Writable st.store tag dst off.eval n.eval) (hsd : 0 < n.eval → src ≠ dst) :
    ∃ (out : St P K C) (W : Fin n.eval → K),
      exec I (copyMapped tag n src srcAt dst off conjugate).run st = some out ∧
      st.store.writeBlock tag dst off.eval (Array.ofFn W) = some out.store ∧
      (∀ i, dec tag (W i) = v i) := by
  let Q : ℕ → K → Prop := fun k w => ∀ hk : k < n.eval, dec tag w = v ⟨k, hk⟩
  obtain ⟨out, W, hr, hwrite, hdec⟩ := exists_exec_loop_writeBlock I tag dst off.eval Q
    (n := n) (body := fun k => (if conjugate then
      ins (.un tag .conj ⟨dst, off + IExp.var k⟩ ⟨src, srcAt (.var k)⟩)
      else ins (.copy tag ⟨dst, off + IExp.var k⟩ ⟨src, srcAt (.var k)⟩)).run)
    (st := st) (fun k hk ys σ hsize hQ hprefix => by
      obtain ⟨vword, hv, hdv⟩ := hin ⟨k, hk⟩
      have hvσ : σ.store.read tag src (srcAt (.var k)).eval = some vword := by
        rw [Store.read_of_writeBlock_eq_some_of_ne hprefix (Or.inl (hsd (by omega)))]
        exact hv
      obtain ⟨len, hlen, hlt⟩ := hw k hk
      obtain ⟨next, w, hr, hs, hd⟩ := exec_copyWord I h tag σ
        ⟨src, srcAt (.var k)⟩ ⟨dst, off + IExp.var k⟩ conjugate vword hvσ
        ⟨len, (Store.shape_of_writeBlock_eq_some hprefix) ▸ hlen, hlt⟩
      exact ⟨next, w, hr, hs, fun _ => hd.trans hdv⟩)
  refine ⟨out, W, ?_, hwrite, fun i => hdec i i.isLt⟩
  change exec I (.seq (.loop n _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

/-- A mapped gather at a natural dimension, exposing its output word family on `Fin N` for
consumers that compose symbolic packed-copy builders. -/
theorem exec_copyMapped_const {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (I : Interp P ι K C) (h : IsRelErrSem u dec safe I.sem) (tag : P)
    (st : St P K C) (N : ℕ) (src : ℕ) (srcAt : IExp ℕ → IExp ℕ)
    (dst : ℕ) (off : IExp ℕ) (conjugate : Bool) (v : Fin N → ℝ)
    (hin : ∀ i : Fin N, ∃ w,
      st.store.read tag src (srcAt (.var i)).eval = some w ∧ dec tag w = v i)
    (hw : Writable st.store tag dst off.eval N) (hsd : 0 < N → src ≠ dst) :
    ∃ (out : St P K C) (W : Fin N → K),
      exec I (copyMapped tag (.const N) src srcAt dst off conjugate).run st = some out ∧
      st.store.writeBlock tag dst off.eval (Array.ofFn W) = some out.store ∧
      (∀ i, dec tag (W i) = v i) := by
  obtain ⟨out, W, hr, hwrite, hdec⟩ := exec_copyMapped I h tag st (.const N) src srcAt
    dst off conjugate v hin hw hsd
  refine ⟨out, fun i => W i, hr, ?_, fun i => hdec i⟩
  convert hwrite using 1
  congr 1

/-- A matrix gather into a separate writable buffer succeeds. Its packed decoded result is
the matrix read at the supplied source addresses, and it preserves all buffer shapes and
every cell in every other buffer, independently of offsets and the matrix dimension. -/
theorem exec_copyMatrixMapped {u : P → ℝ} {dec : P → K → ℝ} {safe : P → ℝ → Prop}
    (I : Interp P ι K C) (h : IsRelErrSem u dec safe I.sem) (tag : P)
    (st : St P K C) (N : ℕ) (src : ℕ) (srcAt : IExp ℕ → IExp ℕ → IExp ℕ)
    (dst : ℕ) (conjugate : Bool) (M : Matrix (Fin N) (Fin N) ℝ)
    (hin : ∀ i j : Fin N, ∃ w,
      st.store.read tag src (srcAt (.var i) (.var j)).eval = some w ∧ dec tag w = M i j)
    (hw : Writable st.store tag dst 0 (N * N)) (hsd : 0 < N → src ≠ dst) :
    ∃ out : St P K C,
      exec I (copyMatrixMapped tag (.const N) src srcAt dst conjugate).run st = some out ∧
      out.store.shape = st.store.shape ∧ HoldsDecoded out.store dec tag dst 0 M ∧
      ∀ q b i, b ≠ dst → out.store.read q b i = st.store.read q b i := by
  let R := fun k (σ : St P K C) => σ.store.shape = st.store.shape ∧
    (∀ q b i, b ≠ dst → σ.store.read q b i = st.store.read q b i) ∧
    ∀ i j : Fin N, j.val < k → ∃ w,
      σ.store.read tag dst (i.val + N * j.val) = some w ∧ dec tag w = M i j
  have h0 : R 0 st := ⟨rfl, fun _ _ _ _ => rfl, fun _ _ hj => (Nat.not_lt_zero _ hj).elim⟩
  obtain ⟨out, hr, hshape, hframe, hpref⟩ := exists_exec_loop_eq_some_of_forall I
    (n := .const N) R h0 (fun k hk σ hs => by
      simp only [IExp.eval_const] at hk
      obtain ⟨hshape, hframe, hpref⟩ := hs
      have hcol : ∀ i : Fin N, ∃ w,
          σ.store.read tag src (srcAt (.var i) (.var k)).eval = some w ∧
            dec tag w = M i ⟨k, hk⟩ := fun i => by
        rw [hframe tag src _ (hsd (by omega))]
        exact hin i ⟨k, hk⟩
      have hwcol : Writable σ.store tag dst (N * k) N := fun i hi => by
        obtain ⟨len, hlen, hlt⟩ := hw (i + N * k)
          (Nat.add_mul_lt_mul_of_lt_of_lt hi hk)
        exact ⟨len, hshape ▸ hlen, by
          simpa only [Nat.zero_add, Nat.add_zero, Nat.add_comm] using hlt⟩
      obtain ⟨next, W, hr, hwrite, hdec⟩ := exec_copyMapped_const I h tag σ N src
        (fun i => srcAt i (.var k)) dst (IExp.const N * IExp.var k) conjugate
        (fun i => M i ⟨k, hk⟩) hcol (by
          simpa only [IExp.eval_mul, IExp.eval_const, IExp.eval_var] using hwcol) hsd
      change σ.store.writeBlock tag dst (N * k) (Array.ofFn W) = some next.store at hwrite
      refine ⟨next, hr, (Store.shape_of_writeBlock_eq_some hwrite).trans hshape,
        (fun q b i hb => (Store.read_of_writeBlock_eq_some_of_ne hwrite (Or.inl hb)).trans
          (hframe q b i hb)), ?_⟩
      intro i j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · obtain ⟨w, hw, hdw⟩ := hpref i j hj
        refine ⟨w, ?_, hdw⟩
        rw [Store.read_of_writeBlock_eq_some_of_ne hwrite (Or.inr (Or.inl
          (Nat.add_mul_lt_mul_of_lt_of_lt i.isLt hj)))]
        exact hw
      · have hj' : j = ⟨k, hk⟩ := Fin.ext hj
        subst j
        refine ⟨W i, ?_, hdec i⟩
        have hread := Store.read_of_writeBlock_eq_some_of_lt hwrite
          (j := i.val) (by rw [Array.size_ofFn]; exact i.isLt)
        rw [Array.getElem?_ofFn, dif_pos i.isLt] at hread
        simpa only [Nat.add_comm] using hread)
  refine ⟨out, ?_, hshape, fun i j => ?_, hframe⟩
  · change exec I (.seq (.loop (.const N) _) .skip) st = some out
    rw [exec_seq_skip]
    exact hr
  · simpa only [Nat.zero_add, Nat.add_assoc] using hpref i j j.isLt

end NLAlib.Computation.TriangularSolve
