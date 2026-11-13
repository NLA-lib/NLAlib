/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Blas.DotExecution

/-!
# Functional contract of the sequential scalar dot implementation

The actual sequential implementation returns one specified word from its input blocks,
independently of the surrounding memory and tape. This strengthens its numerical error
contract without changing the computation. Repeated dot calls on identical words therefore
have identical output, including when other memory or accumulator state has changed.

## Main results

* `NLAlib.Ops.dotSeqFn`: the actual machine's product-and-sequential-sum function.
* `NLAlib.Ops.isFn_dot_seq`: the existing scalar implementation meets that functional contract.
-/

@[expose] public section

namespace NLAlib.Ops

variable {K Op Tst : Type} [Inhabited K]

/-- The word returned by sequentially summing actual machine products. The empty vector returns
literal zero; a nonempty sum copies its first product and adds each remaining product. -/
def dotSeqFn (M : Machine K) : BlockFn K :=
  .of2 1 (·.headD 0) (·.headD 0) (fun _ => 1) fun d xs ys =>
    some [sumSeqF M (fun k => M.mul (vec xs k) (vec ys k)) (d.headD 0)]

variable [Has ScalarOp Op] [Has Blas1Op Op] [Apart Blas1Op ScalarOp Op]

/-- Sequential scalar BLAS supplies a functional dot contract, not merely an allowed error
interval. The output depends only on the input words and the same fixed scalar machine. -/
theorem isFn_dot_seq {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I) :
    (I.link (Blas.seq (Op := Op) (Tst := Tst)).table).IsFn .total
      (Has.inj Blas1Op.dot) (dotSeqFn M) (OutApart (fun _ => True)) := by
  refine Interp.link_meets
    (R := ⟨1, 2, 1, dotSum.body.link Blas.sumSeqTable⟩) ?_ ?_
  · simp [Blas.seq, Profile.over, Blas.level1, Blas.level1Table, Blas.sumSeq,
      Table.comp, dotSum]
  · refine Impl.meets_rel fun d ins outs tape mem vals hnd hadm hl hr _ hz => ?_
    obtain ⟨n, rfl⟩ := List.length_eq_one_iff.mp hnd
    obtain ⟨x, y, xs, ys, rfl, hx, hy, rfl⟩ := Mem.readBlocks_two hr
    obtain ⟨z, rfl, hz'⟩ := Mem.room_one hz
    change z.2 + 1 ≤ mem.store.len z.1 at hz'
    refine ⟨⟨rfl, rfl, rfl⟩, (wp_dotSum_seq hI hl hx hy (by omega)).mono ?_⟩
    intro mem' rfl
    exact ⟨[[_]], rfl, rfl, rfl⟩

end NLAlib.Ops
