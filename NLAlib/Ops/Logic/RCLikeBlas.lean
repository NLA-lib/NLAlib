/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.RCLikeBlas
public import NLAlib.Ops.Logic.Functional

/-!
# Stored-output rules for exact real or complex vector primitives

Each rule applies the common functional-call theorem to readable raw blocks.
Vector maps admit exact alias or disjoint input/output views. Reduction outputs stay
disjoint from their input spans, as declared by the exact operation model.
The same rules apply to real and complex factorization programs.

## Main results

* `NLAlib.Ops.RCLikeBlas.writes_dot` writes the exact Hermitian product.
* `NLAlib.Ops.RCLikeBlas.writes_axpy` writes a vector update.
* `NLAlib.Ops.RCLikeBlas.writes_scal` writes division by the supplied scalar.
* `NLAlib.Ops.RCLikeBlas.writes_copy` copies an actual raw block.
* `NLAlib.Ops.RCLikeBlas.writes_nrm2` writes the nonnegative real norm.
-/

@[expose] public section

namespace NLAlib.Ops.RCLikeBlas

variable {𝕜 Op Tst : Type} [RCLike 𝕜] [Has Blas1Op Op]
  {I : Interp Op Tst 𝕜} {τ : Tape 𝕜} {ρ : Env} {m : Mem 𝕜}

/-- A Hermitian dot call reads both blocks and writes their exact scalar product. -/
theorem writes_dot (hI : IsExact I) {ds : List IExp} {ins outs : List Operand}
    {n : ℕ} {a b z : ℕ × ℕ} {xs ys : List 𝕜}
    (hd : IExp.evalList ρ.idx ds = some [n])
    (ha : Operand.evalList ρ ins = some [a, b])
    (hz : Operand.evalList ρ outs = some [z]) (hl : m.Live [a, b, z])
    (hA : m.store.readBlock a.1 a.2 n = some xs)
    (hB : m.store.readBlock b.1 b.2 n = some ys)
    (hZA : Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock a.1 a.2 n))
    (hZB : Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock b.1 b.2 n))
    (hZ : z.2 + 1 ≤ m.store.len z.1) :
    Writes .total I τ (.call (Has.inj Blas1Op.dot) ds ins outs) ρ
      (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 1 = some [dot n xs ys]) m := by
  exact writes_call_fn1 (hI .dot) (xs := [xs, ys]) hd ha hz rfl rfl
    (by simpa [admissible] using And.intro hZA hZB) hl
    (by simp [Mem.readBlocks, functions, hA, hB]) rfl rfl hZ

/-- An axpy call writes the exact vector update after reading all three input blocks. -/
theorem writes_axpy (hI : IsExact I) {ds : List IExp} {ins outs : List Operand}
    {n : ℕ} {a x y z : ℕ × ℕ} {alpha : 𝕜} {xs ys : List 𝕜}
    (hd : IExp.evalList ρ.idx ds = some [n])
    (ha : Operand.evalList ρ ins = some [a, x, y])
    (hz : Operand.evalList ρ outs = some [z]) (hl : m.Live [a, x, y, z])
    (hA : m.store.readBlock a.1 a.2 1 = some [alpha])
    (hX : m.store.readBlock x.1 x.2 n = some xs)
    (hY : m.store.readBlock y.1 y.2 n = some ys)
    (hAZ : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock z.1 z.2 n))
    (hXZ : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z)
    (hYZ : Fp.Disj (Store.inBlock y.1 y.2 n) (Store.inBlock z.1 z.2 n) ∨ y = z)
    (hZ : z.2 + n ≤ m.store.len z.1) :
    Writes .total I τ (.call (Has.inj Blas1Op.axpy) ds ins outs) ρ
      (Store.inBlock z.1 z.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 n =
        some (List.ofFn fun i : Fin n => ys.getD i 0 + alpha * xs.getD i 0)) m := by
  exact writes_call_fn1 (hI .axpy) (xs := [[alpha], xs, ys]) hd ha hz rfl rfl
    (by simpa [admissible] using And.intro hAZ (And.intro hXZ hYZ)) hl
    (by simp [Mem.readBlocks, functions, hA, hX, hY]) rfl (List.length_ofFn ..) hZ

/-- Scaling divides the input block by the actual supplied scalar. The field operation is
total; an algorithm needing normalization proves its own nonzero norm premise. -/
theorem writes_scal (hI : IsExact I) {ds : List IExp} {ins outs : List Operand}
    {n : ℕ} {a x z : ℕ × ℕ} {alpha : 𝕜} {xs : List 𝕜}
    (hd : IExp.evalList ρ.idx ds = some [n])
    (ha : Operand.evalList ρ ins = some [a, x])
    (hz : Operand.evalList ρ outs = some [z]) (hl : m.Live [a, x, z])
    (hA : m.store.readBlock a.1 a.2 1 = some [alpha])
    (hX : m.store.readBlock x.1 x.2 n = some xs)
    (hAZ : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock z.1 z.2 n))
    (hXZ : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z)
    (hZ : z.2 + n ≤ m.store.len z.1) :
    Writes .total I τ (.call (Has.inj Blas1Op.scal) ds ins outs) ρ
      (Store.inBlock z.1 z.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 n =
        some (List.ofFn fun i : Fin n => xs.getD i 0 / alpha)) m := by
  exact writes_call_fn1 (hI .scal) (xs := [[alpha], xs]) hd ha hz rfl rfl
    (by simpa [admissible] using And.intro hAZ hXZ) hl
    (by simp [Mem.readBlocks, functions, hA, hX]) rfl (List.length_ofFn ..) hZ

/-- A copy writes the input words exactly, including the empty-vector case. -/
theorem writes_copy (hI : IsExact I) {ds : List IExp} {ins outs : List Operand}
    {n : ℕ} {a z : ℕ × ℕ} {xs : List 𝕜}
    (hd : IExp.evalList ρ.idx ds = some [n])
    (ha : Operand.evalList ρ ins = some [a])
    (hz : Operand.evalList ρ outs = some [z]) (hl : m.Live [a, z])
    (hA : m.store.readBlock a.1 a.2 n = some xs)
    (hAZ : Fp.Disj (Store.inBlock a.1 a.2 n) (Store.inBlock z.1 z.2 n) ∨ a = z)
    (hZ : z.2 + n ≤ m.store.len z.1) :
    Writes .total I τ (.call (Has.inj Blas1Op.copy) ds ins outs) ρ
      (Store.inBlock z.1 z.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 n = some xs) m := by
  exact writes_call_fn1 (hI .copy) (xs := [xs]) hd ha hz rfl rfl
    (by simpa [admissible] using hAZ) hl
    (by simp [Mem.readBlocks, functions, hA]) rfl (Store.length_of_readBlock hA) hZ

/-- The norm primitive writes the embedded nonnegative square root of the real norm square. -/
theorem writes_nrm2 (hI : IsExact I) {ds : List IExp} {ins outs : List Operand}
    {n : ℕ} {a z : ℕ × ℕ} {xs : List 𝕜}
    (hd : IExp.evalList ρ.idx ds = some [n])
    (ha : Operand.evalList ρ ins = some [a])
    (hz : Operand.evalList ρ outs = some [z]) (hl : m.Live [a, z])
    (hA : m.store.readBlock a.1 a.2 n = some xs)
    (hZA : Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock a.1 a.2 n))
    (hZ : z.2 + 1 ≤ m.store.len z.1) :
    Writes .total I τ (.call (Has.inj Blas1Op.nrm2) ds ins outs) ρ
      (Store.inBlock z.1 z.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock z.1 z.2 1 =
        some [RCLike.ofReal (Real.sqrt (RCLike.re (dot n xs xs)))]) m := by
  exact writes_call_fn1 (hI .nrm2) (xs := [xs]) hd ha hz rfl rfl
    (by simpa [admissible] using hZA) hl
    (by simp [Mem.readBlocks, functions, hA]) rfl rfl hZ

end NLAlib.Ops.RCLikeBlas
