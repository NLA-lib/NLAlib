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
public import NLAlib.Ops.RoutineLink
public import NLAlib.Ops.Logic.RoutineIntro
public import NLAlib.Ops.RoutineSyntax

/-!
# Exact scalar implementations of the real or complex BLAS collection: the trees

Every vector operation is a fixed loop of declared scalar field operations and scalar
conjugation. Dot products stream through one temporary cell. This file defines the trees, their
routines and the table, and states each run in operand form; the judgments of the routines and
the contracts they satisfy are in `NLAlib/Ops/Profiles/RCLikeScalar.lean`.

## Main definitions

* `NLAlib.Ops.RCLikeScalar.table` lowers the entire exact level-one collection.
* `NLAlib.Ops.RCLikeScalar.dot` is an explicit Hermitian scalar dot product.
-/

@[expose] public section

namespace NLAlib.Ops.RCLikeScalar

variable {Op Tst : Type} [Has ScalarOp Op] [Has StarOp Op]

/-- One conjugate, multiplication and accumulation, using caller-owned scalar cells. A fragment of
`NLAlib.Ops.RCLikeScalar.dotRoutine`: one round of its loop. -/
def starProductStep : Stmt Op Tst := ops% [] (X, Y, t, out) → () {
  call (Has.inj StarOp.conj) [] (X) → (t);
  call (Has.inj ScalarOp.mul) [] (t, Y) → (t);
  call (Has.inj ScalarOp.add) [] (out, t) → (out)
}

/-- A Hermitian dot-product loop on caller-owned scalar workspace. A fragment of
`NLAlib.Ops.RCLikeScalar.dotRoutine`: its loop, on the scratch cell the routine allocates. -/
def dotWithScratch : Stmt Op Tst := ops% [n] (X, Y, t) → (out) {
  call (Has.inj (ScalarOp.lit 0)) [] () → (out);
  for i < n { run starProductStep [] (X[i], Y[i], t, out) }
}

/-- A Hermitian dot product with one scoped temporary, including the empty product. -/
def dot : Stmt Op Tst := ops% [n] (X, Y) → (out) {
  let t ← alloc 1;
  run dotWithScratch [n] (X, Y, t, out)
}

/-- Sequential scalar summation with a caller-supplied output accumulator. -/
def sum : Stmt Op Tst := ops% [n] (X) → (out) {
  call (Has.inj (ScalarOp.lit 0)) [] () → (out);
  for i < n { call (Has.inj ScalarOp.add) [] (out, X[i]) → (out) }
}

/-- A pointwise axpy on caller-owned product workspace. A fragment of
`NLAlib.Ops.RCLikeScalar.axpy`: its loop, on the scratch cell the tree allocates. -/
def axpyWithScratch : Stmt Op Tst := ops% [n] (a, X, Y, t) → (out) {
  for i < n {
    call (Has.inj ScalarOp.mul) [] (a, X[i]) → (t);
    call (Has.inj ScalarOp.add) [] (Y[i], t) → (out[i])
  }
}

/-- A pointwise axpy using one scoped product temporary. -/
def axpy : Stmt Op Tst := ops% [n] (a, X, Y) → (out) {
  let t ← alloc 1;
  run axpyWithScratch [n] (a, X, Y, t, out)
}

/-- Vector division is the shared scalar broadcast loop, with declared operand order. -/
def scal : Stmt Op Tst := ops% [n] (a, X) → (out) {
  run (scalarBroadcast (Has.inj ScalarOp.div)) [n] (X, a, out)
}

/-- Copying is the shared unary scalar map, allowing exact alias or disjoint views. -/
def copy : Stmt Op Tst := unaryMap (Has.inj ScalarOp.copy)

omit [Has StarOp Op] in
/-- `sum` as a routine: `[n] (x : read n) → (z : write 1)`, separated by block. -/
def sumRoutine : Routine Op Tst :=
  routine% [n] (x : n) → (z : 1) by blocks := sum

/-- `dot` as a routine: `[n] (x : read n, y : read n) → (z : write 1)`, separated by block. -/
def dotRoutine : Routine Op Tst :=
  routine% [n] (x : n, y : n) → (z : 1) by blocks := dot

/-- The Euclidean norm runs the routine `dotRoutine` on the vector twice over, then takes the
scalar square root. -/
def nrm2 : Stmt Op Tst := ops% [n] (X) → (out) {
  run dotRoutine [n] (X, X, out);
  call (Has.inj ScalarOp.sqrt) [] (out) → (out)
}

omit [Has StarOp Op] in
/-- `axpy` out of place: `[n] (a : read 1, x : read n, y : read n) → (z : write n)`, separated
by block. -/
def axpyRoutine : Routine Op Tst :=
  routine% [n] (a : 1, x : n, y : n) → (z : n) by blocks := axpy

omit [Has StarOp Op] in
/-- `scal` out of place: `[n] (a : read 1, x : read n) → (z : write n)`, separated by block. -/
def scalRoutine : Routine Op Tst :=
  routine% [n] (a : 1, x : n) → (z : n) by blocks := scal

omit [Has StarOp Op] in
/-- `copy` out of place: `[n] (x : read n) → (z : write n)`, separated by block. -/
def copyRoutine : Routine Op Tst :=
  routine% [n] (x : n) → (z : n) by blocks := copy

/-- `nrm2` as a routine: `[n] (x : read n) → (z : write 1)`, separated by block. -/
def nrm2Routine : Routine Op Tst :=
  routine% [n] (x : n) → (z : 1) by blocks := nrm2

/-- Every level-one operation lowers to scalar arithmetic and explicit scalar conjugation. -/
def table : Table Blas1Op Op Tst
  | .sum => .inl sumRoutine.impl
  | .dot => .inl dotRoutine.impl
  | .axpy => .inl axpyRoutine.impl
  | .nrm2 => .inl nrm2Routine.impl
  | .scal => .inl scalRoutine.impl
  | .copy => .inl copyRoutine.impl

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
/-- The scalar copy loop returns the original block under its admitted alias policy. The tree
implements `copy` for two operand layouts, out of place and in place, which are two routines
(`copyRoutine`, `copyInPlaceRoutine`); this lemma, stated for both layouts, is their common
proof.
Shared by the trees of `NLAlib.Deflation.apply`, `NLAlib.reduceLastStep`,
`NLAlib.ShiftedQR.acceptTrialWithScratch` and 83 more. -/
theorem copy_writes (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {n : ℕ} {x y : ℕ × ℕ} (xs : List 𝕜)
    (hX : m.store.readBlock x.1 x.2 n = some xs)
    (hXY : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) ∨ x = y)
    (hy : y.2 + n ≤ m.store.len y.1) :
    Writes .total I tape copy (Env.frame [n] [x, y]) (Store.inBlock y.1 y.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock y.1 y.2 n = some xs) m := by
  simpa [copy, Machine.fn] using
    unaryMap_writes_of_disj_or_eq (hS .copy) hXY hX hy

omit [Has StarOp Op] in
/-- The shared broadcast lowering computes vector division with the exact scalar machine. The
tree implements `scal` out of place and in place, two routines (`scalRoutine`,
`scalInPlaceRoutine`); this lemma, stated for both layouts, is their common proof.
Shared by the trees of `NLAlib.Krylov.Lanczos.normalize`, `NLAlib.CGS2.cgs2Extend`,
`NLAlib.CGS2.cgs2ExtendFinish` and 10 more. -/
theorem scal_writes (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {n : ℕ} {a x y : ℕ × ℕ} (xs : List 𝕜) (alpha : 𝕜) (hl : m.Live [a, x, y])
    (hX : m.store.readBlock x.1 x.2 n = some xs) (hA : m.store.get a.1 a.2 = some alpha)
    (hXY : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock y.1 y.2 n) ∨ x = y)
    (hAY : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock y.1 y.2 n))
    (hy : y.2 + n ≤ m.store.len y.1) :
    Writes .total I tape scal (Env.frame [n] [a, x, y]) (Store.inBlock y.1 y.2 n)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock y.1 y.2 n =
        some (List.ofFn fun i : Fin n => xs.getD i 0 / alpha)) m := by
  have hl' : m.Live [x, a, y] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨hl x (by simp), hl a (by simp), hl y (by simp), trivial⟩
  refine ((scalarBroadcast_writes_readBlock (hS .div) hX hA hy hXY hAY).in_frame
    rfl rfl hl').mono le_rfl ?_
  intro m' _ ⟨hp, hv⟩
  exact ⟨hp, hv.trans (congrArg some (map_eq_ofFn xs (fun v => v / alpha)
    (Store.length_of_readBlock hX)))⟩

/-- One explicit conjugate product step preserves its accumulator through temporary writes.
A fragment of the tree `NLAlib.Ops.RCLikeScalar.dotWithScratch`. -/
theorem starProductStep_writes (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) {x y t out : ℕ × ℕ} (a b acc : 𝕜)
    (hl : m.Live [x, y, t, out])
    (hX : m.store.readBlock x.1 x.2 1 = some [a])
    (hY : m.store.readBlock y.1 y.2 1 = some [b])
    (hA : m.store.readBlock out.1 out.2 1 = some [acc])
    (hTY : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock y.1 y.2 1))
    (hTO : Fp.Disj (Store.inBlock t.1 t.2 1) (Store.inBlock out.1 out.2 1))
    (ht : t.2 + 1 ≤ m.store.len t.1) (ho : out.2 + 1 ≤ m.store.len out.1) :
    Writes .total I tape starProductStep (Env.frame [] [x, y, t, out])
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [acc + star a * b]) m := by
  unfold starProductStep
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

/-- The explicit conjugate-product loop computes the Hermitian dot product with one
caller-owned temporary. Both input blocks remain outside its two written scalar cells.
A fragment of the tree `NLAlib.Ops.RCLikeScalar.dot`. -/
theorem dotWithScratch_writes (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
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
    Writes .total I tape dotWithScratch (Env.frame [n] [x, y, t, out])
      (Store.inBlock t.1 t.2 1 ⊔ Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [RCLikeBlas.dot n xs ys]) m := by
  unfold dotWithScratch
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
    refine ((starProductStep_writes hS hStar _ _ _ hl' hx hy hacc
      ((hDY.mono le_sup_left le_rfl).mono le_rfl
        (Fp.inBlock_le_inBlock (by omega) (by omega))) hTO
      (by simpa only [hWhole.len_eq] using ht)
      (by simpa only [hWhole.len_eq] using ho)).in_frame rfl rfl hl').mono le_rfl ?_
    intro m'' _ ⟨hp', hv⟩
    exact ⟨hp'.trans hp, by simpa only [Finset.sum_range_succ] using hv⟩
  · intro m' _ ⟨hp, hv⟩
    exact ⟨hp, by simpa only [RCLikeBlas.dot,
      ← Fin.sum_univ_eq_sum_range (fun j => star (xs.getD j 0) * ys.getD j 0) n] using hv⟩

omit [Has StarOp Op] in
/-- The pointwise scalar axpy follows the original input words through the output prefix.
Each vector may alias the output exactly; the broadcast scalar remains separate.
A fragment of the tree `NLAlib.Ops.RCLikeScalar.axpy`. -/
theorem axpyWithScratch_writes (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
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
    Writes .total I tape axpyWithScratch (Env.frame [n] [a, x, y, t, out])
      (Store.inBlock out.1 out.2 n ⊔ Store.inBlock t.1 t.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 n =
        some (List.ofFn fun i : Fin n => ys.getD i 0 + alpha * xs.getD i 0)) m := by
  unfold axpyWithScratch
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
The broadcast scalar remains outside the output; scratch is removed before returning. The tree
implements `axpy` for four operand layouts, four routines (`axpyRoutine`, `axpyInPlaceRoutine`,
`axpyOnXRoutine`, `axpySelfRoutine`); this lemma, stated for every layout, is their common
proof.
Shared by the trees of `NLAlib.Krylov.CG.HSCG.step`, `NLAlib.Krylov.CG.HSCG.initializeState`,
`NLAlib.Krylov.CG.HSCG.initializeRoutine` and 26 more. -/
theorem axpy_writes (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    {n : ℕ} {a x y out : ℕ × ℕ} (xs ys : List 𝕜) (alpha : 𝕜)
    (hl : m.Live [a, x, y, out]) (hA : m.store.get a.1 a.2 = some alpha)
    (hX : m.store.readBlock x.1 x.2 n = some xs)
    (hY : m.store.readBlock y.1 y.2 n = some ys)
    (hXO : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock out.1 out.2 n) ∨ x = out)
    (hYO : Fp.Disj (Store.inBlock y.1 y.2 n) (Store.inBlock out.1 out.2 n) ∨ y = out)
    (hAO : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock out.1 out.2 n))
    (ho : out.2 + n ≤ m.store.len out.1) :
    Writes .total I tape axpy (Env.frame [n] [a, x, y, out])
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
  refine ((axpyWithScratch_writes hS xs ys alpha (by kept) (by kept) (by kept)
    hXO hYO hAO
    (Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hxL)))
    (Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hyL)))
    (Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt haL)))
    (Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hoL)))
    (by simpa using ht.ge) (by simpa only [(hBelow out.1 hoL).1] using ho)).in_frame
      rfl rfl hl').mono (by fp_sub) (fun _ _ h => h)

end NLAlib.Ops.RCLikeScalar
