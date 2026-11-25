/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.RoutineFrames
public import NLAlib.Computation.BLAS

/-!
# Stored strided copies

A strided source window is copied to a contiguous output block using only word-copy
instructions. The same actual operation prepares saved pivot rows and columns in both exact
and rounded Schur updates; no arithmetic or decoding contract is required.

## Main definitions

* `NLAlib.Computation.copyStride`: strided-source to contiguous-target copy.

## Main results

* `NLAlib.Computation.exec_copyStride`: successful copying and the complete target block write.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

/-- Copy a strided source vector into consecutive destination cells. Source and destination
index expressions and the length remain symbolic; the emitted instructions only copy words. -/
def copyStride {P ι VB VI : Type} (p : P) (n : IExp VI) (src dst : VB)
    (so stride dest : IExp VI) : Builder P ι VB VI Unit :=
  forRange n fun i =>
    ins (.copy p ⟨dst, dest + .var i⟩ ⟨src, so + stride * .var i⟩)

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- A strided-to-contiguous copy succeeds from initialized source words and writable target
capacity in a distinct buffer. Its only net store effect is one packed target write, with
exactly the supplied source words. The carrier, arithmetic interpretation and charge monoid
are arbitrary; zero-length blocks require no valid handles. -/
theorem exec_copyStride (I : Interp P ι K C) (p : P) (st : St P K C)
    (n : IExp ℕ) (src dst : ℕ) (so stride dest : IExp ℕ) (x : Fin n.eval → K)
    (hne : src ≠ dst)
    (hx : ∀ i : Fin n.eval, st.store.read p src (so.eval + stride.eval * i) = some (x i))
    (hw : Writable st.store p dst dest.eval n.eval) :
    ∃ out, exec I (copyStride p n src dst so stride dest).run st = some out ∧
      st.store.writeBlock p dst dest.eval (Array.ofFn x) = some out.store := by
  obtain ⟨out, W, hr, hs, hW⟩ := exists_exec_loop_writeBlock I (n := n) p dst dest.eval
    (fun k w => ∀ hk : k < n.eval, w = x ⟨k, hk⟩) (fun k hk ys s _ _ hs => by
      have hrd : s.store.read p src (so.eval + stride.eval * k) = some (x ⟨k, hk⟩) :=
        (Store.read_of_writeBlock_eq_some_of_ne hs (Or.inl hne)).trans (hx ⟨k, hk⟩)
      obtain ⟨len, hlen, hlt⟩ := hw k hk
      obtain ⟨store, hwrite, hrun, -⟩ := exec_scalar_copy I p s
        ⟨dst, dest + .var k⟩ ⟨src, so + stride * .var k⟩ (x ⟨k, hk⟩)
        (by simpa only [IExp.eval_add, IExp.eval_mul, IExp.eval_var] using hrd)
        ⟨len, by rw [Store.shape_of_writeBlock_eq_some hs]; exact hlen,
          by simpa only [IExp.eval_add, IExp.eval_var] using hlt⟩
      refine ⟨_, x ⟨k, hk⟩, hrun, ?_, fun _ => rfl⟩
      simpa only [IExp.eval_add, IExp.eval_var] using hwrite)
  have hWx : W = x := funext fun i => hW i i.isLt
  refine ⟨out, ?_, hWx ▸ hs⟩
  change exec I (.seq (.loop n _) .skip) st = some out
  rw [exec_seq_skip]
  exact hr

/-- The actual contiguous vector-copy builder succeeds from readable source words and
writable output capacity in a distinct buffer. The output window contains precisely the
original source words; its shape and all other cells are preserved. Arbitrary word carriers
and charge monoids are supported, including an empty copy requiring no readable cells. -/
theorem exec_copyv_block (I : Interp P ι K C) (p : P) (st : St P K C)
    (n : IExp ℕ) (src dst : ℕ) (soff doff : IExp ℕ)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p src (soff.eval + i) = some w)
    (hne : src ≠ dst) (hw : Writable st.store p dst doff.eval n.eval) :
    ∃ out, exec I (copyv p src soff dst doff n).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i < n.eval, out.store.read p dst (doff.eval + i) =
        st.store.read p src (soff.eval + i)) ∧
      ∀ q b i, (b ≠ dst ∨ i < doff.eval ∨ doff.eval + n.eval ≤ i) →
        out.store.read q b i = st.store.read q b i := by
  classical
  choose xs hxs using fun i : Fin n.eval => hx i i.isLt
  obtain ⟨out, W, hr, hs, hW⟩ := exists_exec_loop_writeBlock I (n := n) p dst doff.eval
    (fun k w => ∀ hk : k < n.eval, w = xs ⟨k, hk⟩) (fun k hk ys σ _ _ hs => by
      have hrd : σ.store.read p src (soff.eval + k) = some (xs ⟨k, hk⟩) :=
        (Store.read_of_writeBlock_eq_some_of_ne hs (Or.inl hne)).trans (hxs ⟨k, hk⟩)
      obtain ⟨len, hlen, hlt⟩ := hw k hk
      obtain ⟨store, hwrite, hrun, -⟩ := exec_scalar_copy I p σ
        ⟨dst, doff + .var k⟩ ⟨src, soff + .var k⟩ (xs ⟨k, hk⟩)
        (by simpa only [IExp.eval_add, IExp.eval_var] using hrd)
        ⟨len, by rw [Store.shape_of_writeBlock_eq_some hs]; exact hlen,
          by simpa only [IExp.eval_add, IExp.eval_var] using hlt⟩
      refine ⟨_, xs ⟨k, hk⟩, hrun, ?_, fun _ => rfl⟩
      simpa only [IExp.eval_add, IExp.eval_var] using hwrite)
  have hWx : W = xs := funext fun i => hW i i.isLt
  subst W
  refine ⟨out, ?_, Store.shape_of_writeBlock_eq_some hs, ?_, ?_⟩
  · change exec I (.seq (.named "copy" _ (.seq (.loop n _) .skip)) .skip) st = some out
    rw [exec_seq_skip, exec_named, exec_seq_skip]
    exact hr
  · intro i hi
    rw [Store.read_of_writeBlock_eq_some_of_lt hs (by simp only [Array.size_ofFn]; exact hi),
      hxs ⟨i, hi⟩]
    simp only [Array.getElem?_ofFn, hi, dif_pos]
  · intro q b i hout
    exact Store.read_of_writeBlock_eq_some_of_ne hs (by simpa only [Array.size_ofFn] using hout)

/-- A decoded square matrix is copied by the actual contiguous-copy builder to a separate
residual buffer. The exact shape, decoded matrix and all other buffers are preserved. The
carrier and charges are arbitrary, including empty matrices requiring no source reads. -/
theorem exec_copyv_matrix (I : Interp P ι K C) (p : P) (st : St P K C)
    (n : IExp ℕ) (Ab R : ℕ) (ao : IExp ℕ)
    {dec : P → K → ℝ} (A : Matrix (Fin n.eval) (Fin n.eval) ℝ)
    (hA : HoldsDecoded st.store dec p Ab ao.eval A) (hne : Ab ≠ R)
    (hR : Writable st.store p R 0 (n.eval * n.eval)) :
    ∃ out, exec I (copyv p Ab ao R 0 (n * n)).run st = some out ∧
      out.store.shape = st.store.shape ∧ HoldsDecoded out.store dec p R 0 A ∧
      ∀ q b i, b ≠ R → out.store.read q b i = st.store.read q b i := by
  obtain ⟨out, hr, hsh, hread, hframe⟩ := exec_copyv_block I p st (n * n) Ab R ao 0
    (fun t ht => by
      have hN : 0 < n.eval := by change t < n.eval * n.eval at ht; nlinarith
      have hi := Nat.mod_lt t hN
      have hj := (Nat.div_lt_iff_lt_mul hN).mpr (show t < n.eval * n.eval from ht)
      obtain ⟨w, hw, _⟩ := hA ⟨t % n.eval, hi⟩ ⟨t / n.eval, hj⟩
      exact ⟨w, by simpa only [Nat.add_assoc, Nat.mod_add_div] using hw⟩) hne
    (by simpa only [IExp.eval_zero, IExp.eval_mul] using hR)
  refine ⟨out, hr, hsh, ?_, fun q b i hb => hframe q b i (Or.inl hb)⟩
  intro i j
  obtain ⟨w, hw, hd⟩ := hA i j
  refine ⟨w, ?_, hd⟩
  simpa only [IExp.eval_zero, Nat.zero_add, Nat.add_assoc] using
    (hread (i.val + n.eval * j.val) (by
      simpa only [IExp.eval_mul] using Nat.add_mul_lt_mul_of_lt_of_lt i.isLt j.isLt)).trans
      (by simpa only [Nat.add_assoc] using hw)

end NLAlib.Computation
