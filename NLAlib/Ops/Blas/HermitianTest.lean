/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.Hermitian

/-!
# The Hermitian matrix box test

The matrix test is an instance of the scalar word interval scan. It checks all real and
imaginary words of the actual stored matrix, including an empty matrix, and writes only its
flag cell. Input/output spatial disjointness permits shared buffers at different offsets.

## Main results

* `NLAlib.Ops.Hermitian.writes_boxTest`: the actual machine-literal flag, frame and tape position.
* `NLAlib.Ops.Hermitian.wp_boxTest`: the exact one-cell memory update.
-/

@[expose] public section

namespace NLAlib.Ops.Hermitian

variable {K Op Tst : Type} [Inhabited K] [Has ScalarOp Op] [Has CmpTst Tst]

open Classical in
/-- The box test writes the selected machine zero/one literal for whether all actual component
words decode between the stored bounds. Literal exactness is not assumed. Inputs and
flag occupy disjoint word spans; they may use the same buffer at different offsets. -/
theorem writes_boxTest {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hC : IsCmp dec I) {md : Mode} {τ : Tape K} {m : Mem K}
    {rows cols : ℕ} {x lo hi z : ℕ × ℕ} {a b : K} {xs : List K}
    (hl : m.Live [x, lo, hi, z])
    (hx : m.store.readBlock x.1 x.2 (2 * (rows * cols)) = some xs)
    (hlo : m.store.get lo.1 lo.2 = some a) (hhi : m.store.get hi.1 hi.2 = some b)
    (hz : z.2 < m.store.len z.1)
    (hXz : Fp.Disj (Store.inBlock x.1 x.2 (2 * (rows * cols))) (Store.inBlock z.1 z.2 1))
    (hloz : Fp.Disj (Store.inBlock lo.1 lo.2 1) (Store.inBlock z.1 z.2 1))
    (hhiz : Fp.Disj (Store.inBlock hi.1 hi.2 1) (Store.inBlock z.1 z.2 1)) :
    Writes md I τ (boxTest (Op := Op) (Tst := Tst)).body
      (Env.frame [rows, cols] [x, lo, hi, z]) (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.get z.1 z.2 =
        some (M.lit (if InInterval dec a b (vec xs) (2 * (rows * cols)) then 0 else 1))) m :=
  writes_frame rfl rfl hl
    (writes_intervalScan hS hC (vec xs) (Store.holdsVec_of_readBlock hx) hlo hhi hz hXz hloz hhiz)

open Classical in
/-- The complete box test changes exactly its output flag to the actual machine literal of
its interval predicate. No extra matrix-specific execution or cell-update proof is needed. -/
theorem wp_boxTest {M : Machine K} {dec : K → ℝ} {I : Interp Op Tst K}
    (hS : IsScalar M I) (hC : IsCmp dec I) {md : Mode} {τ : Tape K} {m : Mem K}
    {rows cols : ℕ} {x lo hi z : ℕ × ℕ} {a b : K} {xs : List K}
    (hl : m.Live [x, lo, hi, z])
    (hx : m.store.readBlock x.1 x.2 (2 * (rows * cols)) = some xs)
    (hlo : m.store.get lo.1 lo.2 = some a) (hhi : m.store.get hi.1 hi.2 = some b)
    (hz : z.2 < m.store.len z.1)
    (hXz : Fp.Disj (Store.inBlock x.1 x.2 (2 * (rows * cols))) (Store.inBlock z.1 z.2 1))
    (hloz : Fp.Disj (Store.inBlock lo.1 lo.2 1) (Store.inBlock z.1 z.2 1))
    (hhiz : Fp.Disj (Store.inBlock hi.1 hi.2 1) (Store.inBlock z.1 z.2 1))
    {Q : Mem K → Prop}
    (hQ : Q (m.upd z (M.lit
      (if InInterval dec a b (vec xs) (2 * (rows * cols)) then 0 else 1)))) :
    Wp md I τ (boxTest (Op := Op) (Tst := Tst)).body
      (Env.frame [rows, cols] [x, lo, hi, z]) Q m :=
  ((writes_boxTest hS hC hl hx hlo hhi hz hXz hloz hhiz).wp_eq_upd).mono
    (fun _ he => he.symm ▸ hQ)

end NLAlib.Ops.Hermitian
