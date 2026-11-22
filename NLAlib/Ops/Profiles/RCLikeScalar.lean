/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Profiles.RCLikeScalarTrees

/-!
# Exact scalar implementations of the real or complex BLAS collection

Every vector operation of the exact level-one collection is implemented by a routine over
declared scalar field operations and scalar conjugation
(`NLAlib/Ops/Profiles/RCLikeScalarTrees.lean`). Maps admit disjoint views or exact alias, each
admitted layout being its own routine; reduction outputs stay separate from their inputs. These
operation-model admissions justify constant workspace without assumptions about successful
execution.

## Main results

* `NLAlib.Ops.RCLikeScalar.satisfies_table`: every entry of the table satisfies the exact contract
  of its operation.
-/

@[expose] public section

namespace NLAlib.Ops.RCLikeScalar

variable {Op Tst : Type} [Has ScalarOp Op] [Has StarOp Op]

variable {𝕜 : Type} [RCLike 𝕜] {I : Interp Op Tst 𝕜} {tape : Tape 𝕜} {m : Mem 𝕜}

omit [Has StarOp Op] in
/-- Scalar summation meets the specification read off the exact level-one reduction: the
cell is set to zero and the entries are added to it in order. -/
theorem sumRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (sumRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (RCLikeBlas.functions (𝕜 := 𝕜) .sum).rel fun _ => True) := by
  routine_intro [n] (x, out) reads (xs)
  have hOX : Fp.Disj (Store.inBlock out.1 out.2 1) (Store.inBlock x.1 x.2 n) := by
    have h : Fp.Disj (Fp.blocks [out] [1]) (Fp.blocks [x] [n]) := hsep.2.1
    simpa using h
  refine (show Writes .total I τ sum (Env.frame [n] [x, out]) (Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [∑ i : Fin n, xs.getD i 0]) m from ?_).mono le_sup_left fun μ' _ h =>
    ⟨h.1, [[∑ i : Fin n, xs.getD i 0]], Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩,
      rfl⟩
  unfold sum
  refine Writes.seq_le (writes_call_fn1 (hS (.lit 0)) (xs := [])
    rfl rfl rfl rfl rfl trivial (by simpa [Mem.Live] using hlive out (by simp))
    rfl rfl rfl hroom) le_rfl ?_
  intro m₁ hfr₁ ⟨hp₁, hzero⟩
  have hzero' : m₁.store.readBlock out.1 out.2 1 = some [0] := by
    simpa [RCLikeBlas.machine] using hzero
  refine (writes_loop rfl (fun _ => Store.inBlock out.1 out.2 1) (fun _ _ => le_rfl)
    (fun i m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
      some [∑ j ∈ Finset.range i, xs.getD j 0]) ⟨hp₁, by simpa using hzero'⟩ ?_).mono
    le_rfl ?_
  · intro i hi m' hfr ⟨hp, hacc⟩
    have hWhole := hfr₁.trans hfr
    have hxs' := hWhole.keep (Store.readsOnly_readBlock _ _ _ xs) hOX hxs
    have hx : m'.store.readBlock x.1 (x.2 + i) 1 = some [xs.getD i 0] := by
      simp [Store.readBlock, Store.get_of_readBlock hxs' hi (0 : 𝕜)]
    have hl' := hlive.congr hWhole.length_eq
    refine (writes_call_fn1 (hS .add)
      (xs := [[∑ j ∈ Finset.range i, xs.getD j 0], [xs.getD i 0]])
      rfl rfl rfl rfl rfl trivial (by
        simp only [Mem.live_append, Mem.live_cons, Mem.live_nil]
        exact ⟨⟨hl' out (by simp), hl' x (by simp), trivial⟩, hl' out (by simp), trivial⟩)
      (by simp [Machine.fn, Mem.readBlocks, hacc, hx]) rfl rfl
      (by simpa only [hWhole.len_eq] using hroom)).mono le_rfl ?_
    intro m'' _ ⟨hp', hv⟩
    exact ⟨hp'.trans hp, by simpa only [RCLikeBlas.machine, Finset.sum_range_succ] using hv⟩
  · intro m' _ ⟨hp, hv⟩
    exact ⟨hp, by simpa only [← Fin.sum_univ_eq_sum_range (fun i => xs.getD i 0) n] using hv⟩

omit [Has StarOp Op] in
/-- The routine of `sum` implements the exact contract of the operation `sum`. -/
theorem sumRoutine_implements :
    (sumRoutine (Op := Op) (Tst := Tst)).Implements (RCLikeBlas.functions (𝕜 := 𝕜) .sum).rel
      (RCLikeBlas.admissible .sum) (fun ins outs => ins ++ outs) := by
  implements [n] (x) → (z) with hadm

omit [Has StarOp Op] in
/-- Scalar summation realizes the exact level-one reduction contract: a consequence of the
judgment of its routine. -/
theorem satisfies_sum (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (sumRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total
      ((RCLikeBlas.functions .sum).rel.spec (RCLikeBlas.admissible .sum)) :=
  (sumRoutine_meets hS).satisfies_ofRel sumRoutine_implements
    fun _ _ _ _ => trivial

/-- The Hermitian dot product meets the specification read off the exact level-one
reduction: one scratch cell holds each conjugate product, which is added to the output cell; the
scratch cell is released at the end. The two inputs may overlap. -/
theorem dotRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) :
    (dotRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (RCLikeBlas.functions (𝕜 := 𝕜) .dot).rel fun _ => True) := by
  routine_intro [n] (x, y, out) reads (xs, ys)
  have hd : Fp.Disj (Store.inBlock out.1 out.2 1)
      (Store.inBlock x.1 x.2 n ⊔ Store.inBlock y.1 y.2 n) := by
    have h : Fp.Disj (Fp.blocks [out] [1]) (Fp.blocks [x, y] [n, n]) := hsep.2.1
    simpa [Fp.blocks] using h
  obtain ⟨hOX, hOY⟩ := Fp.disj_sup_right.mp hd
  refine (show Writes .total I τ dot (Env.frame [n] [x, y, out]) (Store.inBlock out.1 out.2 1)
      (fun m' => m'.pos = m.pos ∧ m'.store.readBlock out.1 out.2 1 =
        some [RCLikeBlas.dot n xs ys]) m from ?_).mono le_sup_left fun μ' _ h =>
    ⟨h.1, [[RCLikeBlas.dot n xs ys]], Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩,
      rfl⟩
  have hxL := hlive x (by simp)
  have hyL := hlive y (by simp)
  have hoL := hlive out (by simp)
  apply writes_allocs_readBlock (lens := [.const 1]) (ns := [1]) rfl hoL
  intro store hlength hlens hBelow
  have ht : store.len m.store.length = 1 := by simpa using hlens 0 (by simp)
  have hlen : store.length = m.store.length + 1 := by simpa using hlength
  have hl' : (Mem.mk store m.pos).Live [x, y, (m.store.length, 0), out] := by
    simp only [Mem.live_cons, Mem.live_nil]
    exact ⟨by omega, by omega, by omega, by omega, trivial⟩
  refine ((dotWithScratch_writes hS hStar xs ys hl' (by kept) (by kept)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hxL)), hOX⟩)
    (Fp.disj_sup_left.mpr ⟨Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hyL)), hOY⟩)
    (Fp.disj_inBlock_of_ne (Ne.symm (Nat.ne_of_lt hoL)))
    (by simpa using ht.ge) (by simpa only [(hBelow out.1 hoL).1] using hroom)).in_frame
      rfl rfl hl').mono (by fp_sub) (fun _ _ h => h)

/-- The routine of `dot` implements the exact contract of the operation `dot`. -/
theorem dotRoutine_implements :
    (dotRoutine (Op := Op) (Tst := Tst)).Implements (RCLikeBlas.functions (𝕜 := 𝕜) .dot).rel
      (RCLikeBlas.admissible .dot) (fun ins outs => ins ++ outs) := by
  implements [n] (x, y) → (z) with hadm

/-- The streamed conjugate-product implementation realizes the exact Hermitian dot contract: a
consequence of the judgment of its routine. -/
theorem satisfies_dot (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) :
    (dotRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total
      ((RCLikeBlas.functions .dot).rel.spec (RCLikeBlas.admissible .dot)) :=
  (dotRoutine_meets hS hStar).satisfies_ofRel dotRoutine_implements fun _ _ _ _ => trivial

/-- The Euclidean norm meets the specification read off the exact level-one norm: the
judgment of `dotRoutine`, called on the vector twice over, then the scalar square root. -/
theorem nrm2Routine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) :
    (nrm2Routine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (RCLikeBlas.functions (𝕜 := 𝕜) .nrm2).rel fun _ => True) := by
  routine_intro [n] (x, out) reads (xs)
  have hdot := dotRoutine_meets (Op := Op) (Tst := Tst) hS hStar
  unfold nrm2
  have hOX : Fp.Disj (Store.inBlock out.1 out.2 1) (Store.inBlock x.1 x.2 n) := by
    simpa [Fp.blocks] using hblocks.2.1
  call hdot [n] (x, x, out) (pre := ⟨trivial, _, rfl, rfl⟩) as μ₁ hfr hp (ds) hpost
  have hfn : some [[RCLikeBlas.dot n xs xs]] = some [ds] := hpost
  obtain rfl : ds = [RCLikeBlas.dot n xs xs] := by simpa using hfn.symm
  have hl₁ := hlive.congr hfr.length_eq
  refine (writes_call_fn1 (hS .sqrt) (xs := [[RCLikeBlas.dot n xs xs]])
    rfl rfl rfl rfl rfl trivial (by
      simp only [Mem.live_append, Mem.live_cons, Mem.live_nil]
      exact ⟨⟨hl₁ out (by simp), trivial⟩, hl₁ out (by simp), trivial⟩)
    (by simp [Machine.fn, Mem.readBlocks, hds]) rfl rfl
    (by simpa only [hfr.len_eq] using hroom)).mono (by fp_sub) ?_
  intro μ₂ _ ⟨hp₂, hv⟩
  exact ⟨hp₂.trans hp, [[RCLike.ofReal (Real.sqrt (RCLike.re (RCLikeBlas.dot n xs xs)))]],
    Mem.readBlocks_cons_eq_some.mpr ⟨_, [], hv, rfl, rfl⟩, rfl⟩

/-- The routine of `nrm2` implements the exact contract of the operation `nrm2`. -/
theorem nrm2Routine_implements :
    (nrm2Routine (Op := Op) (Tst := Tst)).Implements (RCLikeBlas.functions (𝕜 := 𝕜) .nrm2).rel
      (RCLikeBlas.admissible .nrm2) (fun ins outs => ins ++ outs) := by
  implements [n] (x) → (z) with hadm

/-- Scalar Hermitian dot followed by square root realizes the exact norm contract: a
consequence of the judgment of its routine. -/
theorem satisfies_nrm2 (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) :
    (nrm2Routine (Op := Op) (Tst := Tst)).impl.Satisfies I .total
      ((RCLikeBlas.functions .nrm2).rel.spec (RCLikeBlas.admissible .nrm2)) :=
  (nrm2Routine_meets hS hStar).satisfies_ofRel nrm2Routine_implements
    fun _ _ _ _ => trivial

/-! ### Operations that may run in place

The contracts of `copy`, `scal` and `axpy` admit an output that is apart from a vector input or
exactly that input. Each admitted layout is a routine with the same tree: separate operands, or
the vector updated in place with its buffer variables bound to one operand. The contract of the
operation follows by cases on the admission. -/

omit [Has StarOp Op] in
/-- `copy` in place: `[n] (x : update n)`, the same tree with both buffer variables on `x`. -/
def copyInPlaceRoutine : Routine Op Tst :=
  routine% [n] (x : n) → (x) by blocks := copy

omit [Has StarOp Op] in
/-- The scalar copy out of place meets the specification read off the exact copy. -/
theorem copyRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (copyRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (RCLikeBlas.functions (𝕜 := 𝕜) .copy).rel fun _ => True) := by
  routine_intro [n] (x, z) reads (xs)
  have hd : Fp.Disj (Store.inBlock z.1 z.2 n) (Store.inBlock x.1 x.2 n) := by
    have h : Fp.Disj (Fp.blocks [z] [n]) (Fp.blocks [x] [n]) := hsep.2.1
    simpa using h
  refine (copy_writes hS xs hxs (.inl hd.symm) hroom).mono le_sup_left fun μ' _ h => ?_
  exact ⟨h.1, [xs], Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩, rfl⟩

omit [Has StarOp Op] in
/-- The scalar copy in place meets the specification read off the exact copy. -/
theorem copyInPlaceRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (copyInPlaceRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (RCLikeBlas.functions (𝕜 := 𝕜) .copy).rel fun _ => True) := by
  routine_intro [n] (x) reads (xs)
  refine (copy_writes hS xs hxs (.inr rfl) hroom).mono le_sup_left fun μ' _ h => ?_
  exact ⟨h.1, [xs], Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩, rfl⟩

omit [Has StarOp Op] in
/-- The scalar copy realizes exact copying under disjoint-or-equal vector admission: by cases
on the admission, from the routine out of place and the routine in place. -/
theorem satisfies_copy (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (copyRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total
      ((RCLikeBlas.functions .copy).rel.spec (RCLikeBlas.admissible .copy)) := by
  refine Impl.satisfies_of_writes fun d ins outs tape mem vals hnd hadm hl hread hdom hroom => ?_
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨x, xs, rfl, hx, rfl⟩ := Mem.readBlocks_one hread
  obtain ⟨z, rfl, hz⟩ := Mem.room_one hroom
  have hsep : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z := by
    simpa [RCLikeBlas.admissible] using hadm
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  rcases hsep with hd | rfl
  · exact (copyRoutine_meets hS).writes_ofRel (args := [x, z]) rfl rfl hl
      (Routine.separatedAt_of_blocks rfl (Routine.separatedBlocks_of_noIsolated
        (by simp [copyRoutine, Access.isIsolated]) (Fp.apart_singleton z n)
        (by
          change Fp.Disj (Fp.blocks [z] [n]) (Fp.blocks [x] [n])
          simpa using hd.symm)))
      hread trivial hdom hroom rfl
  · exact (copyInPlaceRoutine_meets hS).writes_ofRel (args := [x]) rfl rfl
      (fun w hw => hl w (List.mem_cons_of_mem _ hw))
      (Routine.separatedAt_of_blocks rfl (Routine.separatedBlocks_of_noIsolated
        (by simp [copyInPlaceRoutine, Access.isIsolated]) (Fp.apart_singleton x n)
        (fun _ _ _ h => False.elim h)))
      hread trivial hdom hroom rfl

omit [Has StarOp Op] in
/-- `scal` in place: `[n] (a : read 1, x : update n)`, the same tree with the vector and the
output on `x`. -/
def scalInPlaceRoutine : Routine Op Tst :=
  routine% [n] (a : 1, x : n) → (x) by blocks := scal

omit [Has StarOp Op] in
/-- The run of the scaling tree on a scalar `a`, a vector `x` and an output `z` that is apart
from `x` or is `x`, as the blocks of the exact scaling. -/
theorem scal_blocks (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) {n : ℕ}
    {a x z : ℕ × ℕ} {τ : Tape 𝕜} {μ : Mem 𝕜} {vals : List (List 𝕜)} (hl : μ.Live [a, x, z])
    (hread : μ.readBlocks [a, x] [1, n] = some vals)
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z)
    (haz : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock z.1 z.2 n))
    (hz : z.2 + n ≤ μ.store.len z.1) :
    Writes .total I τ scal (Env.frame [n] [a, x, z]) (Fp.blocks [z] [n])
      (fun μ' => μ'.pos = μ.pos + 0 ∧ ∃ ys, μ'.readBlocks [z] [n] = some ys ∧
        (RCLikeBlas.functions (𝕜 := 𝕜) .scal).rel.rel [n] vals [] ys) μ := by
  obtain ⟨a', x', as, xs, he, ha, hx, rfl⟩ := Mem.readBlocks_two hread
  obtain ⟨rfl, rfl⟩ : a = a' ∧ x = x' := by simpa using he
  obtain ⟨alpha, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock ha)
  have ha' : μ.store.get a.1 a.2 = some alpha := by
    simpa using Store.get_of_readBlock ha Nat.zero_lt_one alpha
  refine (scal_writes hS xs alpha hl hx ha' hxz haz hz).mono le_sup_left fun μ' _ h => ?_
  exact ⟨h.1, [List.ofFn fun i : Fin n => xs.getD i 0 / alpha],
    Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩, rfl⟩

omit [Has StarOp Op] in
/-- Broadcast scalar division out of place meets the specification read off the exact
scaling. -/
theorem scalRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (scalRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (RCLikeBlas.functions (𝕜 := 𝕜) .scal).rel fun _ => True) := by
  routine_intro [n] (a, x, z)
  have hd : Fp.Disj (Store.inBlock z.1 z.2 n) (Store.inBlock a.1 a.2 1) ∧
      Fp.Disj (Store.inBlock z.1 z.2 n) (Store.inBlock x.1 x.2 n) := by
    have h : Fp.Disj (Fp.blocks [z] [n]) (Fp.blocks [a, x] [1, n]) := hsep.2.1
    exact Fp.disj_sup_right.mp (by simpa [Fp.blocks] using h)
  exact scal_blocks hS hlive hr (.inl hd.2.symm) hd.1.symm hroom

omit [Has StarOp Op] in
/-- Broadcast scalar division in place meets the specification read off the exact scaling. -/
theorem scalInPlaceRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (scalInPlaceRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (RCLikeBlas.functions (𝕜 := 𝕜) .scal).rel fun _ => True) := by
  routine_intro [n] (a, x)
  have hd : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock a.1 a.2 1) := by
    have h : Fp.Disj (Fp.blocks [x] [n]) (Fp.blocks [a] [1]) := hsep.2.1
    simpa using h
  exact scal_blocks hS (by simpa only [Mem.live_cons, Mem.live_nil] using
    ⟨hl.1, hl.2, hl.2, trivial⟩) hr (.inr rfl) hd.symm hroom

omit [Has StarOp Op] in
/-- Broadcast scalar division realizes the exact scaling contract, with allowed vector alias:
by cases on the admission, from the routine out of place and the routine in place. -/
theorem satisfies_scal (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (scalRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total
      ((RCLikeBlas.functions .scal).rel.spec (RCLikeBlas.admissible .scal)) := by
  refine Impl.satisfies_of_writes fun d ins outs tape mem vals hnd hadm hl hread hdom hroom => ?_
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨a, x, as, xs, rfl, ha, hx, rfl⟩ := Mem.readBlocks_two hread
  obtain ⟨z, rfl, hz⟩ := Mem.room_one hroom
  have hsep : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock z.1 z.2 n) ∧
      (Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z) := by
    simpa [RCLikeBlas.admissible] using hadm
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  rcases hsep.2 with hd | rfl
  · exact (scalRoutine_meets hS).writes_ofRel (args := [a, x, z]) rfl rfl hl
      (Routine.separatedAt_of_blocks rfl (Routine.separatedBlocks_of_noIsolated
        (by simp [scalRoutine, Access.isIsolated]) (Fp.apart_singleton z n)
        (by
          change Fp.Disj (Fp.blocks [z] [n]) (Fp.blocks [a, x] [1, n])
          simpa [Fp.blocks] using Fp.disj_sup_right.mpr ⟨hsep.1.symm, hd.symm⟩)))
      hread trivial hdom hroom rfl
  · exact (scalInPlaceRoutine_meets hS).writes_ofRel (args := [a, x]) rfl rfl
      (by
        simp only [List.cons_append, List.nil_append, Mem.live_cons, Mem.live_nil,
          and_true] at hl ⊢
        exact ⟨hl.1, hl.2.1⟩)
      (Routine.separatedAt_of_blocks rfl (Routine.separatedBlocks_of_noIsolated
        (by simp [scalInPlaceRoutine, Access.isIsolated]) (Fp.apart_singleton x n)
        (by
          change Fp.Disj (Fp.blocks [x] [n]) (Fp.blocks [a] [1])
          simpa using hsep.1.symm)))
      hread trivial hdom hroom rfl

omit [Has StarOp Op] in
/-- `axpy` in place on `y`: `[n] (a : read 1, x : read n, y : update n)`, the same tree with
the second vector and the output on `y`. -/
def axpyInPlaceRoutine : Routine Op Tst :=
  routine% [n] (a : 1, x : n, y : n) → (y) by blocks := axpy

omit [Has StarOp Op] in
/-- `axpy` in place on `x`: `[n] (a : read 1, x : update n, y : read n)`, the same tree with
the first vector and the output on `x`. -/
def axpyOnXRoutine : Routine Op Tst :=
  routine% [n] (a : 1, x : n, y : n) → (x) by blocks := axpy

omit [Has StarOp Op] in
/-- `axpy` with both vectors and the output one block: `[n] (a : read 1, x : update n)`. -/
def axpySelfRoutine : Routine Op Tst :=
  routine% [n] (a : 1, x : n, x) → (x) by blocks := axpy

/-- The specification of `axpy` with both vectors one block: the relation of the exact `axpy`
with that block as both vectors. -/
def axpySelfSpec : Routine.Spec 𝕜 where
  pre _ _ _ := True
  post d _ X Y := match X with
    | [as, xs] => (RCLikeBlas.functions (𝕜 := 𝕜) .axpy).rel.rel d [as, xs, xs] [] Y
    | _ => False

omit [Has StarOp Op] in
/-- The run of the `axpy` tree on a scalar `a`, vectors `x`, `y` and an output `z` that is
apart from each vector or is that vector, as the blocks of the exact `axpy`. -/
theorem axpy_blocks (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) {n : ℕ}
    {a x y z : ℕ × ℕ} {τ : Tape 𝕜} {μ : Mem 𝕜} {vals : List (List 𝕜)}
    (hl : μ.Live [a, x, y, z]) (hread : μ.readBlocks [a, x, y] [1, n, n] = some vals)
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z)
    (hyz : Fp.Disj (Store.inBlock y.1 y.2 n) (Store.inBlock z.1 z.2 n) ∨ y = z)
    (haz : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock z.1 z.2 n))
    (hz : z.2 + n ≤ μ.store.len z.1) :
    Writes .total I τ axpy (Env.frame [n] [a, x, y, z]) (Fp.blocks [z] [n])
      (fun μ' => μ'.pos = μ.pos + 0 ∧ ∃ ys, μ'.readBlocks [z] [n] = some ys ∧
        (RCLikeBlas.functions (𝕜 := 𝕜) .axpy).rel.rel [n] vals [] ys) μ := by
  obtain ⟨a', x', y', as, xs, ys, he, ha, hx, hy, rfl⟩ := Mem.readBlocks_three hread
  obtain ⟨rfl, rfl, rfl⟩ : a = a' ∧ x = x' ∧ y = y' := by simpa using he
  obtain ⟨alpha, rfl⟩ := List.length_eq_one_iff.mp (Store.length_of_readBlock ha)
  have ha' : μ.store.get a.1 a.2 = some alpha := by
    simpa using Store.get_of_readBlock ha Nat.zero_lt_one alpha
  refine (axpy_writes hS xs ys alpha hl ha' hx hy hxz hyz haz hz).mono le_sup_left
    fun μ' _ h => ?_
  exact ⟨h.1, [List.ofFn fun i : Fin n => ys.getD i 0 + alpha * xs.getD i 0],
    Mem.readBlocks_cons_eq_some.mpr ⟨_, [], h.2, rfl, rfl⟩, rfl⟩

omit [Has StarOp Op] in
/-- The scalar `axpy` out of place meets the specification read off the exact `axpy`. -/
theorem axpyRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (axpyRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (RCLikeBlas.functions (𝕜 := 𝕜) .axpy).rel fun _ => True) := by
  routine_intro [n] (a, x, y, z)
  have h : Fp.Disj (Fp.blocks [z] [n]) (Fp.blocks [a, x, y] [1, n, n]) := hsep.2.1
  obtain ⟨hza, hzx, hzy⟩ : Fp.Disj (Store.inBlock z.1 z.2 n) (Store.inBlock a.1 a.2 1) ∧
      Fp.Disj (Store.inBlock z.1 z.2 n) (Store.inBlock x.1 x.2 n) ∧
      Fp.Disj (Store.inBlock z.1 z.2 n) (Store.inBlock y.1 y.2 n) := by
    simpa [Fp.blocks] using h
  exact axpy_blocks hS hlive hr (.inl hzx.symm) (.inl hzy.symm) hza.symm hroom

omit [Has StarOp Op] in
/-- The scalar `axpy` in place on `y` meets the specification read off the exact `axpy`. -/
theorem axpyInPlaceRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (axpyInPlaceRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (RCLikeBlas.functions (𝕜 := 𝕜) .axpy).rel fun _ => True) := by
  routine_intro [n] (a, x, y)
  have h : Fp.Disj (Fp.blocks [y] [n]) (Fp.blocks [a, x] [1, n]) := hsep.2.1
  obtain ⟨hya, hyx⟩ := Fp.disj_sup_right.mp (by simpa [Fp.blocks] using h)
  exact axpy_blocks hS (by simpa only [Mem.live_cons, Mem.live_nil] using
    ⟨hl.1, hl.2.1, hl.2.2, hl.2.2, trivial⟩) hr (.inl hyx.symm) (.inr rfl) hya.symm hroom

omit [Has StarOp Op] in
/-- The scalar `axpy` in place on `x` meets the specification read off the exact `axpy`. -/
theorem axpyOnXRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (axpyOnXRoutine (Op := Op) (Tst := Tst)).Meets I
      (Routine.Spec.ofRel (RCLikeBlas.functions (𝕜 := 𝕜) .axpy).rel fun _ => True) := by
  routine_intro [n] (a, x, y)
  have h : Fp.Disj (Fp.blocks [x] [n]) (Fp.blocks [a, y] [1, n]) := hsep.2.1
  obtain ⟨hxa, hxy⟩ := Fp.disj_sup_right.mp (by simpa [Fp.blocks] using h)
  exact axpy_blocks hS (by simpa only [Mem.live_cons, Mem.live_nil] using
    ⟨hl.1, hl.2.1, hl.2.2, hl.2.1, trivial⟩) hr (.inr rfl) (.inl hxy.symm) hxa.symm hroom

omit [Has StarOp Op] in
/-- The scalar `axpy` with both vectors and the output one block meets its specification. -/
theorem axpySelfRoutine_meets (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (axpySelfRoutine (Op := Op) (Tst := Tst)).Meets I (axpySelfSpec (𝕜 := 𝕜)) := by
  routine_intro [n] (a, x) reads (as, xs)
  have hd : Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock a.1 a.2 1) := by
    have h : Fp.Disj (Fp.blocks [x] [n]) (Fp.blocks [a] [1]) := hsep.2.1
    simpa using h
  exact axpy_blocks hS (by simpa only [Mem.live_cons, Mem.live_nil] using
    ⟨hl.1, hl.2, hl.2, hl.2, trivial⟩) (Mem.readBlocks_of_cons has (Mem.readBlocks_of_cons hxs
    (Mem.readBlocks_of_cons hxs rfl))) (.inr rfl) (.inr rfl) hd.symm hroom

omit [Has StarOp Op] in
/-- The one-temporary scalar `axpy` realizes its exact admitted BLAS function: by cases on the
admission, from the routine of each layout of the two vectors and the output. -/
theorem satisfies_axpy (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I) :
    (axpyRoutine (Op := Op) (Tst := Tst)).impl.Satisfies I .total
      ((RCLikeBlas.functions .axpy).rel.spec (RCLikeBlas.admissible .axpy)) := by
  refine Impl.satisfies_of_writes fun d ins outs tape mem vals hnd hadm hl hread hdom hroom => ?_
  obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
  obtain ⟨a, x, y, as, xs, ys, rfl, ha, hx, hy, rfl⟩ := Mem.readBlocks_three hread
  obtain ⟨z, rfl, hz⟩ := Mem.room_one hroom
  have hsep : Fp.Disj (Store.inBlock a.1 a.2 1) (Store.inBlock z.1 z.2 n) ∧
      (Fp.Disj (Store.inBlock x.1 x.2 n) (Store.inBlock z.1 z.2 n) ∨ x = z) ∧
      (Fp.Disj (Store.inBlock y.1 y.2 n) (Store.inBlock z.1 z.2 n) ∨ y = z) := by
    simpa [RCLikeBlas.admissible] using hadm
  have hl4 : mem.Live [a, x, y, z] := hl
  simp only [Mem.live_cons, Mem.live_nil, and_true] at hl4
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  rcases hsep.2.1 with hdx | hxz <;> rcases hsep.2.2 with hdy | hyz
  · exact (axpyRoutine_meets hS).writes_ofRel (args := [a, x, y, z]) rfl rfl hl
      (Routine.separatedAt_of_blocks rfl (Routine.separatedBlocks_of_noIsolated
        (by simp [axpyRoutine, Access.isIsolated]) (Fp.apart_singleton z n)
        (by
          change Fp.Disj (Fp.blocks [z] [n]) (Fp.blocks [a, x, y] [1, n, n])
          simpa [Fp.blocks] using Fp.disj_sup_right.mpr
            ⟨hsep.1.symm, Fp.disj_sup_right.mpr ⟨hdx.symm, hdy.symm⟩⟩)))
      hread trivial hdom hroom rfl
  · subst hyz
    exact (axpyInPlaceRoutine_meets hS).writes_ofRel (args := [a, x, y]) rfl rfl
      (by
        simp only [Mem.live_cons, Mem.live_nil, and_true]
        exact ⟨hl4.1, hl4.2.1, hl4.2.2.1⟩)
      (Routine.separatedAt_of_blocks rfl (Routine.separatedBlocks_of_noIsolated
        (by simp [axpyInPlaceRoutine, Access.isIsolated]) (Fp.apart_singleton y n)
        (by
          change Fp.Disj (Fp.blocks [y] [n]) (Fp.blocks [a, x] [1, n])
          simpa [Fp.blocks] using Fp.disj_sup_right.mpr ⟨hsep.1.symm, hdx.symm⟩)))
      hread trivial hdom hroom rfl
  · subst hxz
    exact (axpyOnXRoutine_meets hS).writes_ofRel (args := [a, x, y]) rfl rfl
      (by
        simp only [Mem.live_cons, Mem.live_nil, and_true]
        exact ⟨hl4.1, hl4.2.1, hl4.2.2.1⟩)
      (Routine.separatedAt_of_blocks rfl (Routine.separatedBlocks_of_noIsolated
        (by simp [axpyOnXRoutine, Access.isIsolated]) (Fp.apart_singleton x n)
        (by
          change Fp.Disj (Fp.blocks [x] [n]) (Fp.blocks [a, y] [1, n])
          simpa [Fp.blocks] using Fp.disj_sup_right.mpr ⟨hsep.1.symm, hdy.symm⟩)))
      hread trivial hdom hroom rfl
  · subst hxz
    subst hyz
    obtain rfl : xs = ys := Option.some.inj (hx.symm.trans hy)
    refine ((axpySelfRoutine_meets hS) [n] [a, y] tape mem [as, xs] rfl rfl
      (by
        simp only [Mem.live_cons, Mem.live_nil, and_true]
        exact ⟨hl4.1, hl4.2.1⟩)
      (Routine.separatedAt_of_blocks rfl (Routine.separatedBlocks_of_noIsolated
        (by simp [axpySelfRoutine, Access.isIsolated]) (Fp.apart_singleton y n)
        (by
          change Fp.Disj (Fp.blocks [y] [n]) (Fp.blocks [a] [1])
          simpa using hsep.1.symm)))
      (Mem.readBlocks_of_cons ha (Mem.readBlocks_of_cons hx rfl)) trivial hroom).mono le_rfl
      fun m' _ ⟨hpos, ys', hys, hp⟩ => ⟨hpos, ys', hys, hp⟩

/-- The complete exact BLAS table is realized by scalar arithmetic and conjugation alone. -/
theorem satisfies_table (hS : IsScalar (RCLikeBlas.machine : Machine 𝕜) I)
    (hStar : RCLikeStar.IsExact I) (o : Blas1Op) :
    match table (Op := Op) (Tst := Tst) o with
    | .inl r => r.Satisfies I .total ((RCLikeBlas.functions o).rel.spec (RCLikeBlas.admissible o))
    | .inr _ => False := by
  cases o
  · exact satisfies_sum hS
  · exact satisfies_dot hS hStar
  · exact satisfies_axpy hS
  · exact satisfies_nrm2 hS hStar
  · exact satisfies_scal hS
  · exact satisfies_copy hS

/-- The streamed Hermitian dot product reserves exactly one temporary at zero primitive
workspace, for every index environment. Its payload is independent of vector length. -/
theorem dot_peak_zero (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (dot (Tst := Tst)) idx = 1 := by
  unfold dot
  rw [stmtPeak_alloc]
  change 1 + stmtPeak (fun (_ : Op) _ => 0) _ idx = 1
  rw [stmtPeak_zero_of_allocationFree (by rfl)]

omit [Has StarOp Op] in
/-- The scalar axpy implementation also reserves exactly one temporary cell. -/
theorem axpy_peak_zero (idx : List ℕ) :
    stmtPeak (fun (_ : Op) _ => 0) (axpy (Tst := Tst)) idx = 1 := by
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
  · change stmtPeak (fun (_ : Op) _ => 0) nrm2 idx ≤ 1
    unfold nrm2
    change max (stmtPeak (fun (_ : Op) _ => 0) (.frame _ _ dot) idx) _ ≤ 1
    refine max_le (stmtPeak_frame_le_uniform (fun idx => le_of_eq (dot_peak_zero idx)) _ _ _) ?_
    simp [stmtPeak]
  · exact le_of_eq_of_le (stmtPeak_zero_of_allocationFree (by rfl) idx) (by omega)
  · exact le_of_eq_of_le (stmtPeak_zero_of_allocationFree (by rfl) idx) (by omega)

/-- A Hermitian dot emits one zero literal and one conjugation, multiplication and addition
per entry. Structural instructions are counted separately by canonical instrumentation. -/
theorem stmtCost_dot (n x y out : ℕ) :
    stmtCost (dot (Op := Op) (Tst := Tst)) [n, x, y, out] =
      Count.one (Has.inj (ScalarOp.lit 0)) [] +
        n • (Count.one (Has.inj StarOp.conj) [] + Count.one (Has.inj ScalarOp.mul) [] +
          Count.one (Has.inj ScalarOp.add) []) := by
  simp [dot, dotWithScratch, starProductStep, stmtCost, useCost, add_assoc]

omit [Has StarOp Op] in
/-- Each pointwise axpy entry emits one multiplication and one addition. -/
theorem stmtCost_axpy (n a x y out : ℕ) :
    stmtCost (axpy (Op := Op) (Tst := Tst)) [n, a, x, y, out] =
      n • (Count.one (Has.inj ScalarOp.mul) [] + Count.one (Has.inj ScalarOp.add) []) := by
  simp [axpy, axpyWithScratch, stmtCost, useCost]

omit [Has StarOp Op] in
/-- Sequential summation emits one zero literal and one addition per entry. -/
theorem stmtCost_sum (n x out : ℕ) :
    stmtCost (sum (Op := Op) (Tst := Tst)) [n, x, out] =
      Count.one (Has.inj (ScalarOp.lit 0)) [] + n • Count.one (Has.inj ScalarOp.add) [] := by
  simp [sum, stmtCost, useCost]

omit [Has StarOp Op] in
/-- Scalar division is emitted once per stored vector entry. -/
theorem stmtCost_scal (n a x out : ℕ) :
    stmtCost (scal (Op := Op) (Tst := Tst)) [n, a, x, out] =
      n • Count.one (Has.inj ScalarOp.div) [] := by
  simp [scal, scalarBroadcast, stmtCost, useCost]

omit [Has StarOp Op] in
/-- The scalar copy loop emits one copy per entry, including exact alias. -/
theorem stmtCost_copy (n x out : ℕ) :
    stmtCost (copy (Op := Op) (Tst := Tst)) [n, x, out] =
      n • Count.one (Has.inj ScalarOp.copy) [] := by
  simp [copy, unaryMap, stmtCost, useCost]

/-- The Euclidean norm uses the streamed Hermitian dot and one scalar square root. -/
theorem stmtCost_nrm2 (n x out : ℕ) :
    stmtCost (nrm2 (Op := Op) (Tst := Tst)) [n, x, out] =
      Count.one (Has.inj (ScalarOp.lit 0)) [] +
        n • (Count.one (Has.inj StarOp.conj) [] + Count.one (Has.inj ScalarOp.mul) [] +
          Count.one (Has.inj ScalarOp.add) []) + Count.one (Has.inj ScalarOp.sqrt) [] := by
  simp [nrm2, dotRoutine, stmtCost, stmtCost_dot, useCost]

end NLAlib.Ops.RCLikeScalar
