/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Tactic
public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Examples.CgsQR

/-!
# Test case: the statements of classical Gram–Schmidt in the logic layer (phase A)

The statements that the proof of `cgs` in the new style is made of, checked to elaborate against
the definitions of the logic layer; the proofs are phase B. The proof sketch is in
`docs/design/Ops-ProgramLogic.md`, §14.

## Main results

* `NLAlib.Ops.Examples.cgsCol_writes`: column `j` as one block specification: footprint
  `cgsColFp`, a fresh final memory, the entries of the column of `R` and of `Q` read back and
  related by `CgsCol`. It replaces `wp_cgsDots`, `wp_cgsProj` and `wp_cgsCol`.
* `NLAlib.Ops.Examples.cgs_spec_writes`: the certificate, by `Impl.meets_of_writes`.
* `NLAlib.Ops.Examples.splitB`: an S2-flavoured block in the builder (an index read from the
  store, two scratch buffers, a 2-D fill from the tape, a kernel call, a loop over a
  data-dependent number of columns), elaborated to a plain tree.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {K Op Tst : Type} [Has ScalarOp Op] [Has Blas1Op Op] [Inhabited K] {M : Machine K}
  {dec : K → ℝ} {ε : Blas1Err} {ok : ℕ → Prop} {J : Interp Op Tst K} {τ : Tape K}
  {H : CgsBuf → ℕ} {n p oA oQ oR j : ℕ} {s : Store K} {pos : ℕ} {qs a : List K}

/-- **Column `j` of classical Gram–Schmidt as one block specification.** -/
theorem cgsCol_writes (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ x, dec (M.neg x) = -dec x) (hok : ok n) (hH : Function.Injective H)
    (hl : ∀ b, H b < s.length) (hq : s.readBlock (H .Q) oQ (j * n) = some qs)
    (ha : s.readBlock (H .A) (oA + j * n) n = some a)
    (hR : oR + j * p + j < s.len (H .R)) (hQ : oQ + j * n + n ≤ s.len (H .Q))
    (ht : 0 < s.len (H .t)) (hvl : n ≤ s.len (H .v)) :
    Writes .total J τ cgsCol (cgsEnv H n p oA oQ oR j) (cgsColFp H n p oQ oR j)
      (fun m' => m'.pos = pos ∧ ∃ rp ρ qj,
        m'.store.readBlock (H .R) (oR + j * p) (j + 1) = some (rp ++ [ρ]) ∧
        m'.store.readBlock (H .Q) (oQ + j * n) n = some qj ∧ CgsCol dec ε n j qs a rp ρ qj)
      ⟨s, pos⟩ := by
  sorry

/-- **The certificate of `cgs`, by a block specification.** Same statement as `cgs_spec`. -/
theorem cgs_spec_writes (hS : IsScalar M J) (hJ : IsBlas1 dec ε ok J)
    (hneg : ∀ x, dec (M.neg x) = -dec x) :
    (cgsImpl (Op := Op) (Tst := Tst)).Meets J .total ((cgsRel dec ε).spec (CgsOperands ok)) := by
  refine Impl.meets_of_writes fun d ins outs τ m xs hnd hadm hl hr hdom hz => ?_
  sorry

omit [Has ScalarOp Op] [Has Blas1Op Op] in
/-- **An S2-flavoured block in the builder**: read $k_+ \le k$ from the cell `c`, allocate a `k × k`
test matrix `G` and fill it from the tape, multiply `Y := M G` by a kernel, and copy the first
`k₊` columns of `Y` out. -/
def splitB (toNat : Tst) (draw mm copy : Op) : Stmt Op Tst :=
  ops% [k] (Mat, c) → (Out) {
    let kp ← index toNat (c) ≤ k;
    let G ← alloc k * k;
    for j < k {
      for i < k { call draw [] () → (G[j * k + i]) }
    };
    let Y ← alloc k * k;
    call mm [k, k, k] (Mat, G) → (Y);
    for j < kp {
      call copy [k] (Y[j * k]) → (Out[j * k])
    }
  }

omit [Has ScalarOp Op] [Has Blas1Op Op] in
/-- The block is the positional tree: index variables `k`, the offsets of `Mat`, `c`, `Out`,
then `kp`, `j`, `i`; buffer variables `Mat`, `c`, `Out`, `G`, `Y`. -/
example (toNat : Tst) (draw mm copy : Op) : splitB toNat draw mm copy =
    .bindIdx toNat [⟨1, .var 2⟩] (.var 0)
      (.alloc (.var 0 * .var 0)
        (.seq (.loop (.var 0) (.loop (.var 0) (.call draw [] [] [⟨3, .var 5 * .var 0 + .var 6⟩])))
          (.alloc (.var 0 * .var 0)
            (.seq (.call mm [.var 0, .var 0, .var 0] [⟨0, .var 1⟩, ⟨3, .const 0⟩]
                [⟨4, .const 0⟩])
              (.loop (.var 4) (.call copy [.var 0] [⟨4, .var 5 * .var 0⟩]
                [⟨2, .var 3 + .var 5 * .var 0⟩])))))) := rfl

end NLAlib.Ops.Examples
