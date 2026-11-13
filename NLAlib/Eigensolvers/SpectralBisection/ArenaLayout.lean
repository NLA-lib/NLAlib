/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.SpectralBisection.Arena

/-!
# Complete arena layout for spectral bisection

The solver allocates eleven regions. The operand and capacity lists below describe their
physical layout in allocation order; ordinary `Mem.Room` and `Fp.Apart` apply directly.
Downward and upward proofs share these lists rather than repeating allocation formulas.

## Main results

* `NLAlib.SpectralBisection.arenaOperands`: the eleven solver regions.
* `NLAlib.SpectralBisection.arenaLengths`: their exact capacities in scalar words.
-/

@[expose] public section

namespace NLAlib.SpectralBisection

/-- The shared constants, matrices, results, metadata, level parameters and sample buffers,
in the order in which the solver allocates them. -/
def arenaOperands (c ma ua qa ea sz kd kp lv su sg : ℕ × ℕ) : List (ℕ × ℕ) :=
  [c, ma, ua, qa, ea, sz, kd, kp, lv, su, sg]

/-- Exact capacities of the eleven arenas for root dimension `n` and depth parameter `L`.
Capacities include all reserved words, including uninitialized output slots. -/
def arenaLengths (n L : ℕ) : List ℕ :=
  [5, 2 * (n * n) * (L + 2), 2 * (n * n) * (L + 2),
    2 * (n * n) * (L + 1), n * (L + 2), n * (L + 2) + 1,
    n * (L + 1), n * (L + 1), 2 * (L + 2), n, 4 * (n * n)]

end NLAlib.SpectralBisection
