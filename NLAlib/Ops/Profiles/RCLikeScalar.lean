/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Catalog.RCLikeStar
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Functional
public import NLAlib.Ops.Logic.Scalar
public import NLAlib.Ops.AllocationFree
public import NLAlib.Ops.Workspace
public import NLAlib.Ops.Blas.Broadcast
public import NLAlib.Ops.Blas.MapCorrect
public import NLAlib.Ops.Logic.Allocation
public import NLAlib.Ops.Logic.PrefixRead
public import NLAlib.Ops.Logic.Tactic

/-!
# Exact scalar implementations of the real or complex BLAS collection

Every vector operation is a fixed loop of declared scalar field operations and scalar
conjugation. Dot products stream through one temporary cell. Maps admit disjoint views
or exact alias; reduction outputs stay separate from their inputs. These operation-model
admissions justify constant workspace without assumptions about successful execution.

## Main definitions

* `NLAlib.Ops.RCLikeScalar.table` lowers the entire exact level-one collection.
* `NLAlib.Ops.RCLikeScalar.dot` is an explicit Hermitian scalar dot product.
-/

@[expose] public section

namespace NLAlib.Ops.RCLikeScalar

variable {Op Tst : Type} [Has ScalarOp Op] [Has StarOp Op]

/-- One conjugate, multiplication and accumulation, using caller-owned scalar cells. -/
def starProductStep : Impl Op Tst := opsImpl% [] (X, Y, t, out) → () {
  call (Has.inj StarOp.conj) [] (X) → (t);
  call (Has.inj ScalarOp.mul) [] (t, Y) → (t);
  call (Has.inj ScalarOp.add) [] (out, t) → (out)
}

/-- A Hermitian dot-product loop on caller-owned scalar workspace. -/
def dotWithScratch : Impl Op Tst := opsImpl% [n] (X, Y, t) → (out) {
  call (Has.inj (ScalarOp.lit 0)) [] () → (out);
  for i < n { run starProductStep.body [] (X[i], Y[i], t, out) }
}

/-- A Hermitian dot product with one scoped temporary, including the empty product. -/
def dot : Impl Op Tst := opsImpl% [n] (X, Y) → (out) {
  let t ← alloc 1;
  run dotWithScratch.body [n] (X, Y, t, out)
}

/-- Sequential scalar summation with a caller-supplied output accumulator. -/
def sum : Impl Op Tst := opsImpl% [n] (X) → (out) {
  call (Has.inj (ScalarOp.lit 0)) [] () → (out);
  for i < n { call (Has.inj ScalarOp.add) [] (out, X[i]) → (out) }
}

/-- A pointwise axpy on caller-owned product workspace. -/
def axpyWithScratch : Impl Op Tst := opsImpl% [n] (a, X, Y, t) → (out) {
  for i < n {
    call (Has.inj ScalarOp.mul) [] (a, X[i]) → (t);
    call (Has.inj ScalarOp.add) [] (Y[i], t) → (out[i])
  }
}

/-- A pointwise axpy using one scoped product temporary. -/
def axpy : Impl Op Tst := opsImpl% [n] (a, X, Y) → (out) {
  let t ← alloc 1;
  run axpyWithScratch.body [n] (a, X, Y, t, out)
}

/-- Vector division is the shared scalar broadcast loop, with declared operand order. -/
def scal : Impl Op Tst := opsImpl% [n] (a, X) → (out) {
  run (scalarBroadcast (Has.inj ScalarOp.div)).body [n] (X, a, out)
}

/-- Copying is the shared unary scalar map, allowing exact alias or disjoint views. -/
def copy : Impl Op Tst := unaryMap (Has.inj ScalarOp.copy)

/-- The Euclidean norm is a Hermitian dot product followed by the scalar square root. -/
def nrm2 : Impl Op Tst := opsImpl% [n] (X) → (out) {
  run dot.body [n] (X, X, out);
  call (Has.inj ScalarOp.sqrt) [] (out) → (out)
}

/-- Every level-one operation lowers to scalar arithmetic and explicit scalar conjugation. -/
def table : Table Blas1Op Op Tst
  | .sum => .inl sum
  | .dot => .inl dot
  | .axpy => .inl axpy
  | .nrm2 => .inl nrm2
  | .scal => .inl scal
  | .copy => .inl copy

variable {𝕜 : Type} [RCLike 𝕜] {I : Interp Op Tst 𝕜} {tape : Tape 𝕜} {m : Mem 𝕜}

/-- Zero supplies list padding; valid input lengths make the padding unobservable. -/
local instance instInhabitedRCLikeScalar : Inhabited 𝕜 := ⟨0⟩

private theorem map_eq_ofFn {n : ℕ} (xs : List 𝕜) (f : 𝕜 → 𝕜) (hlen : xs.length = n) :
    xs.map f = List.ofFn (fun i : Fin n => f (xs.getD i 0)) := by
  apply List.ext_getElem (by simp [hlen])
  intro i hi hi'
  have hx : i < xs.length := by simpa using hi
  simp [List.getD_eq_getElem?_getD, hx]

omit [Has StarOp Op] in
/-- The scalar copy loop returns the original block under its admitted alias policy. -/
theorem writes_copy (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {n : ℕ} {x y : ℕ × ℕ} (xs : List 𝕜)
    (hX : m.store.readBlock x.1 x.2 n = some xs)
    (hXY : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) ∨ x = y)
    (hy : y.2 + n ≤ m.store.len y.1) :
    Writes .total I tape copy.body (Env.frame [n] [x, y]) (Store.inBlock y.1 y.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock y.1 y.2 n = some xs) m := by
  simpa [copy, Machine.fn] using
    writes_unaryMap_of_disj_or_eq (hS .copy) hXY hX hy

omit [Has StarOp Op] in
/-- The shared broadcast lowering computes vector division with the exact scalar machine. -/
theorem writes_scal (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {n : ℕ} {a x y : ℕ × ℕ} (xs : List 𝕜) (alpha : 𝕜) (hl : m.Live [a, x, y])
    (hX : m.store.readBlock x.1 x.2 n = some xs) (hA : m.store.get a.1 a.2 = some alpha)
    (hXY : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) ∨ x = y)
    (hAY : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock y.1 y.2 n))
    (hy : y.2 + n ≤ m.store.len y.1) :
    Writes .total I tape scal.body (Env.frame [n] [a, x, y]) (Store.inBlock y.1 y.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock y.1 y.2 n =
        some (List.ofFn fun i : Fin n => xs.getD i 0 / alpha)) m := by
  have hl' : m.Live [x, a, y] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl x (by simp), hl a (by simp), hl y (by simp), trivial⟩
  refine ((writes_scalarBroadcast_readBlock (hS .div) hX hA hy hXY hAY).in_frame
    rfl rfl hl').mono le_rfl ?_
  intro m' _ ⟨hp, hv⟩
  exact ⟨hp, hv.trans (congrArg some (map_eq_ofFn xs (fun v => v / alpha)
    (Store.length_of_readBlock hX)))⟩

/-- One explicit conjugate product step preserves its accumulator through temporary writes. -/
theorem writes_starProductStep (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) {x y t out : ℕ × ℕ} (a b acc : 𝕜)
    (hl : m.Live [x, y, t, out])
    (hX : m.store.readBlock x.1 x.2 1 = some [a])
    (hY : m.store.readBlock y.1 y.2 1 = some [b])
    (hA : m.store.readBlock out.1 out.2 1 = some [acc])
    (hTY : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock y.1 y.2 1))
    (hTO : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock out.1 out.2 1))
    (ht : t.2 + 1 ≤ m.store.len t.1) (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I tape starProductStep.body (Env.frame [] [x, y, t, out])
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [acc + star a * b]) m := by
  unfold starProductStep
  dsimp only
  refine Writes.seq_le (writes_call_fn1 hStar (xs := [[a]])
    rfl rfl rfl rfl rfl trivial (by
      simp only [Mem.live_append, Mem.live_cons, Mem.live_nil]
      exact ⟨⟨hl x (by simp), trivial⟩, hl t (by simp), trivial⟩)
    (by simp [RCLikeStar.functions, Mem.readBlocks, hX]) rfl rfl ht) le_sup_left ?_
  intro m₁ hfr₁ ⟨hp₁, hStarValue⟩
  have hY₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ [b]) hTY hY
  have hA₁ := hfr₁.keep (Store.readsOnly_readBlock _ _ _ [acc]) hTO hA
  have hl₁ := hl.congr hfr₁.length_eq
  refine Writes.seq_le (writes_call_fn1 (hS .mul) (xs := [[star a], [b]])
    rfl rfl rfl rfl rfl trivial (by
      simp only [Mem.live_append, Mem.live_cons, Mem.live_nil]
      exact ⟨⟨hl₁ t (by simp), hl₁ y (by simp), trivial⟩, hl₁ t (by simp), trivial⟩)
    (by simp [Machine.fn, Mem.readBlocks, hStarValue, hY₁]) rfl rfl
    (by simpa only [hfr₁.len_eq] using ht)) le_sup_left ?_
  intro m₂ hfr₂ ⟨hp₂, hProduct⟩
  have hA₂ := hfr₂.keep (Store.readsOnly_readBlock _ _ _ [acc]) hTO hA₁
  have hl₂ := hl₁.congr hfr₂.length_eq
  refine (writes_call_fn1 (hS .add) (xs := [[acc], [star a * b]])
    rfl rfl rfl rfl rfl trivial (by
      simp only [Mem.live_append, Mem.live_cons, Mem.live_nil]
      exact ⟨⟨hl₂ out (by simp), hl₂ t (by simp), trivial⟩, hl₂ out (by simp), trivial⟩)
    (by simp [Machine.fn, RCLikeBlas.machine, Mem.readBlocks, hA₂, hProduct]) rfl rfl
    (by simpa only [hfr₂.len_eq, hfr₁.len_eq] using ho)).mono le_sup_right ?_
  intro m₃ _ ⟨hp₃, hv⟩
  exact ⟨hp₃.trans (hp₂.trans hp₁), hv⟩

omit [Has StarOp Op] in
/-- Sequential scalar summation realizes the exact reduction on disjoint input/output spans. -/
theorem writes_sum (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {n : ℕ} {x out : ℕ × ℕ} (xs : List 𝕜) (hl : m.Live [x, out])
    (hX : m.store.readBlock x.1 x.2 n = some xs)
    (hOX : Fp.Disj (Store.inBlock out.1 out.2 1) (Store.inBlock x.1 x.2 n))
    (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I tape sum.body (Env.frame [n] [x, out])
      (Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [∑ i : Fin n, xs.getD i 0]) m := by
  unfold sum
  dsimp only
  refine Writes.seq_le (writes_call_fn1 (hS (.lit 0)) (xs := [])
    rfl rfl rfl rfl rfl trivial (by simpa [Mem.Live] using hl out (by simp))
    rfl rfl rfl ho) le_rfl ?_
  intro m₁ hfr₁ ⟨hp₁, hzero⟩
  have hzero' : m₁.store.readBlock out.1 out.2 1 = some [0] := by
    simpa [RCLikeBlas.machine] using hzero
  refine (writes_loop rfl (fun _ => Store.inBlock out.1 out.2 1) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
      some [∑ j ∈ Finset.range i, xs.getD j 0]) ⟨hp₁, by simpa using hzero'⟩ ?_).mono
    le_rfl ?_
  · intro i hi m' hfr ⟨hp, hacc⟩
    have hWhole := hfr₁.trans hfr
    have hX' := hWhole.keep (Store.readsOnly_readBlock _ _ _ xs) hOX hX
    have hx : m'.store.readBlock x.1 (x.2 + i) 1 = some [xs.getD i 0] := by
      simp [Store.readBlock, Store.get_of_readBlock hX' hi (0 : 𝕜)]
    have hl' := hl.congr hWhole.length_eq
    refine (writes_call_fn1 (hS .add)
      (xs := [[∑ j ∈ Finset.range i, xs.getD j 0], [xs.getD i 0]])
      rfl rfl rfl rfl rfl trivial (by
        simp only [Mem.live_append, Mem.live_cons, Mem.live_nil]
        exact ⟨⟨hl' out (by simp), hl' x (by simp), trivial⟩, hl' out (by simp), trivial⟩)
      (by simp [Machine.fn, Mem.readBlocks, hacc, hx]) rfl rfl
      (by simpa only [hWhole.len_eq] using ho)).mono le_rfl ?_
    intro m'' _ ⟨hp', hv⟩
    exact ⟨hp'.trans hp, by simpa only [RCLikeBlas.machine, Finset.sum_range_succ] using hv⟩
  · intro m' _ ⟨hp, hv⟩
    exact ⟨hp, by simpa only [← Fin.sum_univ_eq_sum_range (fun i => xs.getD i 0) n] using hv⟩

/-- The explicit conjugate-product loop computes the Hermitian dot product with one
caller-owned temporary. Both input blocks remain outside its two written scalar cells. -/
theorem writes_dotWithScratch (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) {n : ℕ} {x y t out : ℕ × ℕ} (xs ys : List 𝕜)
    (hl : m.Live [x, y, t, out])
    (hX : m.store.readBlock x.1 x.2 n = some xs)
    (hY : m.store.readBlock y.1 y.2 n = some ys)
    (hDX : Fp.Disj (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (Store.inBlock x.1 x.2 n))
    (hDY : Fp.Disj (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (Store.inBlock y.1 y.2 n))
    (hTO : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock out.1 out.2 1))
    (ht : t.2 + 1 ≤ m.store.len t.1) (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I tape dotWithScratch.body (Env.frame [n] [x, y, t, out])
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [RCLikeBlas.dot n xs ys]) m := by
  unfold dotWithScratch
  dsimp only
  refine Writes.seq_le (writes_call_fn1 (hS (.lit 0)) (xs := [])
    rfl rfl rfl rfl rfl trivial (by simpa [Mem.Live] using hl out (by simp))
    rfl rfl rfl ho) le_sup_right ?_
  intro m₁ hfr₁ ⟨hp₁, hzero⟩
  have hzero' : m₁.store.readBlock out.1 out.2 1 = some [0] := by
    simpa [RCLikeBlas.machine] using hzero
  refine (writes_loop rfl (fun _ => Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
    (fun _ _ => le_rfl) (fun i m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
      some [∑ j ∈ Finset.range i, star (xs.getD j 0) * ys.getD j 0])
    ⟨hp₁, by simpa using hzero'⟩ ?_).mono le_rfl ?_
  · intro i hi m' hfr ⟨hp, hacc⟩
    have houtSub : Store.inBlock out.1 out.2 1 ≤
        Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1 := le_sup_right
    have hWhole := (hfr₁.mono houtSub).trans hfr
    have hX' := hWhole.keep (Store.readsOnly_readBlock _ _ _ xs) hDX hX
    have hY' := hWhole.keep (Store.readsOnly_readBlock _ _ _ ys) hDY hY
    have hx : m'.store.readBlock x.1 (x.2 + i) 1 = some [xs.getD i 0] := by
      simp [Store.readBlock, Store.get_of_readBlock hX' hi (0 : 𝕜)]
    have hy : m'.store.readBlock y.1 (y.2 + i) 1 = some [ys.getD i 0] := by
      simp [Store.readBlock, Store.get_of_readBlock hY' hi (0 : 𝕜)]
    have hl' : m'.Live [(x.1, x.2 + i), (y.1, y.2 + i), t, out] := by
      simpa only [Mem.live_cons, Mem.live_nil] using hl.congr hWhole.length_eq
    refine ((writes_starProductStep hS hStar _ _ _ hl' hx hy hacc
      ((hDY.mono le_sup_left le_rfl).mono le_rfl
        (Fp.inBlock_le_inBlock (by omega) (by omega))) hTO
      (by simpa only [hWhole.len_eq] using ht)
      (by simpa only [hWhole.len_eq] using ho)).in_frame rfl rfl hl').mono le_rfl ?_
    intro m'' _ ⟨hp', hv⟩
    exact ⟨hp'.trans hp, by simpa only [Finset.sum_range_succ] using hv⟩
  · intro m' _ ⟨hp, hv⟩
    exact ⟨hp, by simpa only [RCLikeBlas.dot,
      ← Fin.sum_univ_eq_sum_range (fun j => star (xs.getD j 0) * ys.getD j 0) n] using hv⟩

/-- A scoped one-cell scalar dot product realizes the admitted Hermitian reduction,
including zero-length vectors. All scratch is removed before returning. -/
theorem writes_dot (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) {n : ℕ} {x y out : ℕ × ℕ} (xs ys : List 𝕜)
    (hl : m.Live [x, y, out])
    (hX : m.store.readBlock x.1 x.2 n = some xs)
    (hY : m.store.readBlock y.1 y.2 n = some ys)
    (hOX : Fp.Disj (Store.inBlock out.1 out.2 1) (Store.inBlock x.1 x.2 n))
    (hOY : Fp.Disj (Store.inBlock out.1 out.2 1) (Store.inBlock y.1 y.2 n))
    (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I tape dot.body (Env.frame [n] [x, y, out])
      (Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [RCLikeBlas.dot n xs ys]) m := by
  have hxL := hl x (by simp)
  have hyL := hl y (by simp)
  have hoL := hl out (by simp)
  apply writes_allocs_readBlock (lens := [.const 1]) (ns := [1]) rfl hoL
  intro store hlength hlens hBelow
  have ht : store.len m.store.length = 1 := by simpa using hlens 0 (by simp)
  have hlen : store.length = m.store.length + 1 := by simpa using hlength
  have hl' : (Mem.mk store m.pos).Live [x, y, (m.store.length, 0), out] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨by omega, by omega, by omega, by omega, trivial⟩
  refine ((writes_dotWithScratch hS hStar xs ys hl' (by kept) (by kept)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hxL)), hOX⟩)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hyL)), hOY⟩)
    (Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hoL)))
    (by simpa using ht.ge) (by simpa only [(hBelow out.1 hoL).1] using ho)).in_frame
      rfl rfl hl').mono (by fp_sub) (fun _ _ h => h)

/-- The scalar dot product followed by scalar square root computes the exact norm. -/
theorem writes_nrm2 (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) {n : ℕ} {x out : ℕ × ℕ} (xs : List 𝕜)
    (hl : m.Live [x, out]) (hX : m.store.readBlock x.1 x.2 n = some xs)
    (hOX : Fp.Disj (Store.inBlock out.1 out.2 1) (Store.inBlock x.1 x.2 n))
    (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I tape nrm2.body (Env.frame [n] [x, out])
      (Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [RCLike.ofReal (Real.sqrt (RCLike.re (RCLikeBlas.dot n xs xs)))]) m := by
  have hl' : m.Live [x, x, out] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl x (by simp), hl x (by simp), hl out (by simp), trivial⟩
  unfold nrm2
  dsimp only
  refine Writes.seq_le ((writes_dot hS hStar xs xs hl' hX hX hOX hOX ho).in_frame
    rfl rfl hl') le_rfl ?_
  intro m₁ hfr ⟨hp, hDot⟩
  have hl₁ := hl.congr hfr.length_eq
  refine (writes_call_fn1 (hS .sqrt) (xs := [[RCLikeBlas.dot n xs xs]])
    rfl rfl rfl rfl rfl trivial (by
      simp only [Mem.live_append, Mem.live_cons, Mem.live_nil]
      exact ⟨⟨hl₁ out (by simp), trivial⟩, hl₁ out (by simp), trivial⟩)
    (by simp [Machine.fn, Mem.readBlocks, hDot]) rfl rfl
    (by simpa only [hfr.len_eq] using ho)).mono le_rfl ?_
  intro m₂ _ ⟨hp₂, hv⟩
  exact ⟨hp₂.trans hp, hv⟩

omit [Has StarOp Op] in
/-- The pointwise scalar axpy follows the original input words through the output prefix.
Each vector may alias the output exactly; the broadcast scalar remains separate. -/
theorem writes_axpyWithScratch (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {n : ℕ} {a x y t out : ℕ × ℕ} (xs ys : List 𝕜) (alpha : 𝕜)
    (hA : m.store.get a.1 a.2 = some alpha)
    (hX : m.store.readBlock x.1 x.2 n = some xs)
    (hY : m.store.readBlock y.1 y.2 n = some ys)
    (hXO : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock out.1 out.2 n) ∨ x = out)
    (hYO : Fp.Disj (Store.inBlock y.1 y.2 n) (Store.inBlock out.1 out.2 n) ∨ y = out)
    (hAO : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock out.1 out.2 n))
    (hTX : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock x.1 x.2 n))
    (hTY : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock y.1 y.2 n))
    (hTA : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock a.1 a.2 1))
    (hTO : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock out.1 out.2 n))
    (ht : t.2 + 1 ≤ m.store.len t.1) (ho : out.2 + n ≤ m.store.len out.1) :
    Writes .total I tape axpyWithScratch.body (Env.frame [n] [a, x, y, t, out])
      (Store.inBlock out.1 out.2 n ⊔ Store.inBlock t.1 t.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 n =
        some (List.ofFn fun i : Fin n => ys.getD i 0 + alpha * xs.getD i 0)) m := by
  unfold axpyWithScratch
  dsimp only
  refine (writes_fill_scratch rfl (Store.inBlock t.1 t.2 1) hTO
    (fun i => ys.getD i 0 + alpha * xs.getD i 0) (fun _ => m.pos) rfl ?_).mono le_rfl ?_
  · intro i hi m' hfr _ hp
    have hx : m'.store.get x.1 (x.2 + i) = some (xs.getD i 0) :=
      (hfr.get_prefix hXO hTX hi).trans (Store.get_of_readBlock hX hi 0)
    have hy : m'.store.get y.1 (y.2 + i) = some (ys.getD i 0) :=
      (hfr.get_prefix hYO hTY hi).trans (Store.get_of_readBlock hY hi 0)
    have ha : m'.store.get a.1 a.2 = some alpha := by
      rw [hfr.get_eq ?_]
      · exact hA
      · rintro (hw | hw)
        · exact hAO _ _ ⟨rfl, le_rfl, by omega⟩
            ⟨hw.1, hw.2.1, by have := hw.2.2; omega⟩
        · exact hTA _ _ hw ⟨rfl, le_rfl, by omega⟩
    have hne : (y.1, y.2 + i) ≠ t := by
      intro he
      have hb := congrArg Prod.fst he
      have ho := congrArg Prod.snd he
      exact hTY y.1 (y.2 + i) ⟨hb, by omega, by omega⟩ ⟨rfl, by omega, by omega⟩
    let code : List (ScalarIns ScalarOp) :=
      [⟨.mul, [⟨0, .var 1⟩, ⟨1, .var 2 + .var 6⟩], ⟨3, .var 4⟩⟩,
        ⟨.add, [⟨2, .var 3 + .var 6⟩, ⟨3, .var 4⟩], ⟨4, .var 5 + .var 6⟩⟩]
    have hev : ScalarIns.evalBlock RCLikeBlas.machine.eval
        ((Env.frame [n] [a, x, y, t, out]).pushIdx i) code m'.store.cellFn =
      some [(t, alpha * xs.getD i 0), ((out.1, out.2 + i), ys.getD i 0 + alpha * xs.getD i 0)] := by
      simp [code, ScalarIns.evalBlock, Operand.evalList, Operand.eval, IExp.eval,
        Env.frame, Env.pushIdx, Store.cellFn, Machine.eval, RCLikeBlas.machine, ha, hx, hy, hne]
    refine (writes_machineScalarBlock hS hev ?_).mono (by fp_sub) ?_
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · change t.2 < m'.store.len t.1
        rw [hfr.len_eq]
        omega
      · change out.2 + i < m'.store.len out.1
        rw [hfr.len_eq]
        omega
    · intro m'' _ he
      subst m''
      refine ⟨get_updCells (ws₁ := [(t, alpha * xs.getD i 0)]) (ws₂ := []) ?_
        (by simp), hp⟩
      change out.2 + i < m'.store.len out.1
      rw [hfr.len_eq]
      omega
  · intro m' _ ⟨hv, hp⟩
    refine ⟨hp, Store.readBlock_eq_some_iff.mpr ⟨by simp, fun i hi => ?_⟩⟩
    simpa [List.getD_eq_getElem?_getD, hi] using hv i hi

omit [Has StarOp Op] in
/-- One scoped product cell implements axpy for disjoint or exactly aliased vector views.
The broadcast scalar remains outside the output; scratch is removed before returning. -/
theorem writes_axpy (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {n : ℕ} {a x y out : ℕ × ℕ} (xs ys : List 𝕜) (alpha : 𝕜)
    (hl : m.Live [a, x, y, out]) (hA : m.store.get a.1 a.2 = some alpha)
    (hX : m.store.readBlock x.1 x.2 n = some xs)
    (hY : m.store.readBlock y.1 y.2 n = some ys)
    (hXO : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock out.1 out.2 n) ∨ x = out)
    (hYO : Fp.Disj (Store.inBlock y.1 y.2 n) (Store.inBlock out.1 out.2 n) ∨ y = out)
    (hAO : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock out.1 out.2 n))
    (ho : out.2 + n ≤ m.store.len out.1) :
    Writes .total I tape axpy.body (Env.frame [n] [a, x, y, out])
      (Store.inBlock out.1 out.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 n =
        some (List.ofFn fun i : Fin n => ys.getD i 0 + alpha * xs.getD i 0)) m := by
  have haL := hl a (by simp)
  have hxL := hl x (by simp)
  have hyL := hl y (by simp)
  have hoL := hl out (by simp)
  apply writes_allocs_readBlock (lens := [.const 1]) (ns := [1]) rfl hoL
  intro store hlength hlens hBelow
  have hlen : store.length = m.store.length + 1 := by simpa using hlength
  have ht : store.len m.store.length = 1 := by simpa using hlens 0 (by simp)
  have hl' : (Mem.mk store m.pos).Live [a, x, y, (m.store.length, 0), out] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨by omega, by omega, by omega, by omega, by omega, trivial⟩
  refine ((writes_axpyWithScratch hS xs ys alpha (by kept) (by kept) (by kept)
    hXO hYO hAO
    (Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hxL)))
    (Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hyL)))
    (Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt haL)))
    (Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hoL)))
    (by simpa using ht.ge) (by simpa only [(hBelow out.1 hoL).1] using ho)).in_frame
      rfl rfl hl').mono (by fp_sub) (fun _ _ h => h)

omit [Has StarOp Op] in
/-- Scalar summation realizes the exact level-one reduction contract. -/
theorem meets_sum (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (sum (Op := Op) (Tst := Tst)).Triple I .total
      ((RCLikeBlas.functions .sum).rel.spec (RCLikeBlas.admissible .sum)) := by
  refine Impl.meets_of_writes fun d ins outs tape mem vals hnd hadm hl hread _ hroom => ?_
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hread
  obtain ⟨z, rfl, hz⟩ := Mem.room_one hroom
  have hsep : Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock x.1 x.2 n) := by
    simpa [RCLikeBlas.admissible] using hadm
  refine ⟨⟨rfl, rfl, rfl⟩, (writes_sum hS xs hl hx hsep hz).mono ?_ ?_⟩
  · exact le_sup_left
  intro mem' _ h
  refine ⟨h.1, [[∑ i : Fin n, xs.getD i 0]], ?_, rfl⟩
  exact Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩

/-- The streamed conjugate-product implementation realizes the exact Hermitian dot contract. -/
theorem meets_dot (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) :
    (dot (Op := Op) (Tst := Tst)).Triple I .total
      ((RCLikeBlas.functions .dot).rel.spec (RCLikeBlas.admissible .dot)) := by
  refine Impl.meets_of_writes fun d ins outs tape mem vals hnd hadm hl hread _ hroom => ?_
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨x, y, xs, ys, rfl, hx, hy, rfl⟩ := Mem.readBlocks_two hread
  obtain ⟨z, rfl, hz⟩ := Mem.room_one hroom
  have hsep : Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock x.1 x.2 n) ∧
      Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock y.1 y.2 n) := by
    simpa [RCLikeBlas.admissible] using hadm
  refine ⟨⟨rfl, rfl, rfl⟩, (writes_dot hS hStar xs ys hl hx hy hsep.1 hsep.2 hz).mono ?_ ?_⟩
  · exact le_sup_left
  intro mem' _ h
  refine ⟨h.1, [[RCLikeBlas.dot n xs ys]], ?_, rfl⟩
  exact Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩

/-- Scalar Hermitian dot followed by square root realizes the exact norm contract. -/
theorem meets_nrm2 (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) :
    (nrm2 (Op := Op) (Tst := Tst)).Triple I .total
      ((RCLikeBlas.functions .nrm2).rel.spec (RCLikeBlas.admissible .nrm2)) := by
  refine Impl.meets_of_writes fun d ins outs tape mem vals hnd hadm hl hread _ hroom => ?_
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hread
  obtain ⟨z, rfl, hz⟩ := Mem.room_one hroom
  have hsep : Fp.Disj (Store.inBlock z.1 z.2 1) (Store.inBlock x.1 x.2 n) := by
    simpa [RCLikeBlas.admissible] using hadm
  refine ⟨⟨rfl, rfl, rfl⟩, (writes_nrm2 hS hStar xs hl hx hsep hz).mono ?_ ?_⟩
  · exact le_sup_left
  intro mem' _ h
  refine ⟨h.1, [[RCLike.ofReal (Real.sqrt (RCLike.re (RCLikeBlas.dot n xs xs)))]], ?_, rfl⟩
  exact Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩

omit [Has StarOp Op] in
/-- The scalar copy realizes exact copying under disjoint-or-equal vector admission. -/
theorem meets_copy (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (copy (Op := Op) (Tst := Tst)).Triple I .total
      ((RCLikeBlas.functions .copy).rel.spec (RCLikeBlas.admissible .copy)) := by
  refine Impl.meets_of_writes fun d ins outs tape mem vals hnd hadm _ hread _ hroom => ?_
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hread
  obtain ⟨z, rfl, hz⟩ := Mem.room_one hroom
  have hsep : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z := by
    simpa [RCLikeBlas.admissible] using hadm
  refine ⟨⟨rfl, rfl, rfl⟩, (writes_copy hS xs hx hsep hz).mono ?_ ?_⟩
  · exact le_sup_left
  intro mem' _ h
  refine ⟨h.1, [xs], ?_, rfl⟩
  exact Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩

omit [Has StarOp Op] in
/-- Broadcast scalar division realizes the exact scaling contract, with allowed vector alias. -/
theorem meets_scal (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (scal (Op := Op) (Tst := Tst)).Triple I .total
      ((RCLikeBlas.functions .scal).rel.spec (RCLikeBlas.admissible .scal)) := by
  refine Impl.meets_of_writes fun d ins outs tape mem vals hnd hadm hl hread _ hroom => ?_
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨a, x, as, xs, rfl, ha, hx, rfl⟩ := Mem.readBlocks_two hread
  obtain ⟨z, rfl, hz⟩ := Mem.room_one hroom
  obtain ⟨alpha, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock ha)
  have ha' : mem.store.get a.1 a.2 = some alpha := by
    simpa using Store.get_of_readBlock ha Nat.zero_lt_one alpha
  have hsep : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock z.1 z.2 n) ∧
      (Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z) := by
    simpa [RCLikeBlas.admissible] using hadm
  refine ⟨⟨rfl, rfl, rfl⟩, (writes_scal hS xs alpha hl hx ha' hsep.2 hsep.1 hz).mono ?_ ?_⟩
  · exact le_sup_left
  intro mem' _ h
  refine ⟨h.1, [List.ofFn fun i : Fin n => xs.getD i 0 / alpha], ?_, rfl⟩
  exact Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩

omit [Has StarOp Op] in
/-- The one-temporary scalar axpy realizes its exact admitted BLAS function. -/
theorem meets_axpy (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (axpy (Op := Op) (Tst := Tst)).Triple I .total
      ((RCLikeBlas.functions .axpy).rel.spec (RCLikeBlas.admissible .axpy)) := by
  refine Impl.meets_of_writes fun d ins outs tape mem vals hnd hadm hl hread _ hroom => ?_
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨a, x, y, as, xs, ys, rfl, ha, hx, hy, rfl⟩ := Mem.readBlocks_three hread
  obtain ⟨z, rfl, hz⟩ := Mem.room_one hroom
  obtain ⟨alpha, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock ha)
  have ha' : mem.store.get a.1 a.2 = some alpha := by
    simpa using Store.get_of_readBlock ha Nat.zero_lt_one alpha
  have hsep : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock z.1 z.2 n) ∧
      (Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z) ∧
      (Fp.Disj (Store.inBlock y.1 y.2 n) (Store.inBlock z.1 z.2 n) ∨ y = z) := by
    simpa [RCLikeBlas.admissible] using hadm
  refine ⟨⟨rfl, rfl, rfl⟩, (writes_axpy hS xs ys alpha hl ha' hx hy
    hsep.2.1 hsep.2.2 hsep.1 hz).mono ?_ ?_⟩
  · exact le_sup_left
  intro mem' _ h
  refine ⟨h.1, [List.ofFn fun i : Fin n => ys.getD i 0 + alpha * xs.getD i 0], ?_, rfl⟩
  exact Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩

/-- The complete exact BLAS table is realized by scalar arithmetic and conjugation alone. -/
theorem meets_table (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) (o : Blas1Op) :
    match table (Op := Op) (Tst := Tst) o with
    | .inl r => r.Triple I .total ((RCLikeBlas.functions o).rel.spec (RCLikeBlas.admissible o))
    | .inr _ => False := by
  cases o
  · exact meets_sum hS
  · exact meets_dot hS hStar
  · exact meets_axpy hS
  · exact meets_nrm2 hS hStar
  · exact meets_scal hS
  · exact meets_copy hS

/-- The streamed Hermitian dot product reserves exactly one temporary at zero primitive
workspace, for every index environment. Its payload is independent of vector length. -/
theorem dot_peak_zero (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (dot (Tst := Tst)).body idx = 1 := by
  unfold dot
  rw [stmtPeak_alloc]
  change 1 + stmtPeak (fun (_ : Op) _ => 0) _ idx = 1
  rw [stmtPeak_zero_of_allocationFree (by rfl)]

omit [Has StarOp Op] in
/-- The scalar axpy implementation also reserves exactly one temporary cell. -/
theorem axpy_peak_zero (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (axpy (Tst := Tst)).body idx = 1 := by
  unfold axpy
  rw [stmtPeak_alloc]
  change 1 + stmtPeak (fun (_ : Op) _ => 0) _ idx = 1
  rw [stmtPeak_zero_of_allocationFree (by rfl)]

/-- Every operation in the scalar BLAS table needs at most one stored temporary,
independently of its runtime dimensions, aliases and data. -/
theorem table_peak_zero (o : Blas1Op) (idx : List ℕ) :
    match table (Op := Op) (Tst := Tst) o with
    | .inl r => stmtPeak (fun (_ : Op) _ => 0) r.body idx ≤ 1
    | .inr _ => False := by
  cases o
  · exact le_of_eq_of_le (stmtPeak_zero_of_allocationFree (by rfl) idx) (by omega)
  · exact le_of_eq (dot_peak_zero idx)
  · exact le_of_eq (axpy_peak_zero idx)
  · unfold table nrm2
    change max (stmtPeak (fun (_ : Op) _ => 0) (.frame _ _ dot.body) idx) _ ≤ 1
    refine max_le (stmtPeak_frame_le_uniform (fun idx => le_of_eq (dot_peak_zero idx)) _ _ _) ?_
    simp [stmtPeak]
  · exact le_of_eq_of_le (stmtPeak_zero_of_allocationFree (by rfl) idx) (by omega)
  · exact le_of_eq_of_le (stmtPeak_zero_of_allocationFree (by rfl) idx) (by omega)

/-- A Hermitian dot emits one zero literal and one conjugation, multiplication and addition
per entry. Structural instructions are counted separately by canonical instrumentation. -/
theorem stmtCost_dot (n x y out : ℕ) :
    stmtCost (dot (Op := Op) (Tst := Tst)).body [n, x, y, out] =
      Count.one (Has.inj (ScalarOp.lit 0)) [] +
        n • (Count.one (Has.inj StarOp.conj) [] + Count.one (Has.inj ScalarOp.mul) [] +
          Count.one (Has.inj ScalarOp.add) []) := by
  simp [dot, dotWithScratch, starProductStep, stmtCost, useCost, add_assoc]

omit [Has StarOp Op] in
/-- Each pointwise axpy entry emits one multiplication and one addition. -/
theorem stmtCost_axpy (n a x y out : ℕ) :
    stmtCost (axpy (Op := Op) (Tst := Tst)).body [n, a, x, y, out] =
      n • (Count.one (Has.inj ScalarOp.mul) [] + Count.one (Has.inj ScalarOp.add) []) := by
  simp [axpy, axpyWithScratch, stmtCost, useCost]

omit [Has StarOp Op] in
/-- Sequential summation emits one zero literal and one addition per entry. -/
theorem stmtCost_sum (n x out : ℕ) :
    stmtCost (sum (Op := Op) (Tst := Tst)).body [n, x, out] =
      Count.one (Has.inj (ScalarOp.lit 0)) [] + n • Count.one (Has.inj ScalarOp.add) [] := by
  simp [sum, stmtCost, useCost]

omit [Has StarOp Op] in
/-- Scalar division is emitted once per stored vector entry. -/
theorem stmtCost_scal (n a x out : ℕ) :
    stmtCost (scal (Op := Op) (Tst := Tst)).body [n, a, x, out] =
      n • Count.one (Has.inj ScalarOp.div) [] := by
  simp [scal, scalarBroadcast, stmtCost, useCost]

omit [Has StarOp Op] in
/-- The scalar copy loop emits one copy per entry, including exact alias. -/
theorem stmtCost_copy (n x out : ℕ) :
    stmtCost (copy (Op := Op) (Tst := Tst)).body [n, x, out] =
      n • Count.one (Has.inj ScalarOp.copy) [] := by
  simp [copy, unaryMap, stmtCost, useCost]

/-- The Euclidean norm uses the streamed Hermitian dot and one scalar square root. -/
theorem stmtCost_nrm2 (n x out : ℕ) :
    stmtCost (nrm2 (Op := Op) (Tst := Tst)).body [n, x, out] =
      Count.one (Has.inj (ScalarOp.lit 0)) [] +
        n • (Count.one (Has.inj StarOp.conj) [] + Count.one (Has.inj ScalarOp.mul) [] +
          Count.one (Has.inj ScalarOp.add) []) + Count.one (Has.inj ScalarOp.sqrt) [] := by
  simp [nrm2, stmtCost, stmtCost_dot, useCost]

end NLAlib.Ops.RCLikeScalar
