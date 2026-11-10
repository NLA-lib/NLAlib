/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Builder

/-!
# Test case: an S2-flavoured block in the builder

The proof of `cgs` in the new style is `NLAlib.Ops.Examples.cgs_spec_w` (`Examples/CgsW.lean`).

## Main results

* `NLAlib.Ops.Examples.splitB`: an S2-flavoured block in the builder (an index read from the
  store, two scratch buffers, a 2-D fill from the tape, a kernel call, a loop over a
  data-dependent number of columns), elaborated to a plain tree.
-/

@[expose] public section

namespace NLAlib.Ops.Examples

open NLAlib.Ops

variable {Op Tst : Type}

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
