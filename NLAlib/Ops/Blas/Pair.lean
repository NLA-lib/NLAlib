/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Scalar
public import NLAlib.Ops.Logic.Writes

/-!
# Scalar operations on stored word pairs

Each component is computed by an ordinary scalar operation. The functional proof identifies
the actual updated memory and supports disjoint source and destination regions of one buffer.

## Main results

* `NLAlib.Ops.Pair.multiply`: multiply both component words by one stored scalar.
* `NLAlib.Ops.Pair.wp_multiply`: exact functional execution under scalar multiplication contracts.
-/

@[expose] public section

namespace NLAlib.Ops.Pair

variable {K Op Tst : Type} [Has ScalarOp Op]

/-- Multiply the real and imaginary component words by a stored scalar, one rounding per
component. All effects remain explicit scalar multiplication calls. -/
def multiply : Impl Op Tst := opsImpl% [] (x, c) → (z) {
  call (Has.inj ScalarOp.mul) [] (x, c) → (z);
  call (Has.inj ScalarOp.mul) [] (x[1], c) → (z[1])
}

/-- Component multiplication writes the actual two machine products. The input pair and
scalar cell are disjoint from the output pair, including spatially within one buffer. -/
theorem wp_multiply {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {x c z : ℕ × ℕ} {ar ai a : K}
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock z.1 z.2 2))
    (hcz : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock z.1 z.2 2))
    (hxr : m.store.get x.1 x.2 = some ar)
    (hxi : m.store.get x.1 (x.2 + 1) = some ai)
    (hc : m.store.get c.1 c.2 = some a) (hz : z.2 + 2 ≤ m.store.len z.1)
    {Q : Mem K → Prop} (hQ : Q (m.updBlock z [M.mul ar a, M.mul ai a])) :
    Wp md I τ (multiply (Op := Op) (Tst := Tst)).body (Env.frame [] [x, c, z]) Q m := by
  have hxne := hxz.ne_cells
    (show Store.inBlock x.1 x.2 2 x.1 (x.2 + 1) from ⟨rfl, by omega, by omega⟩)
    (show Store.inBlock z.1 z.2 2 z.1 z.2 from ⟨rfl, le_rfl, by omega⟩)
  have hcne := hcz.ne_cells
    (show Store.inBlock c.1 c.2 1 c.1 c.2 from ⟨rfl, le_rfl, by omega⟩)
    (show Store.inBlock z.1 z.2 2 z.1 z.2 from ⟨rfl, le_rfl, by omega⟩)
  refine wp_seq (wp_call_bin (hI .mul) rfl rfl rfl trivial hxr hc rfl
    (by simpa using (show z.2 < m.store.len z.1 from by omega)) ?_)
  refine wp_call_bin (hI .mul) rfl rfl rfl trivial (a := ai) (b := a) ?_ ?_ rfl ?_ ?_
  · simpa only [Mem.store_upd, Store.get_upd_of_ne hxne] using hxi
  · simpa only [Mem.store_upd, Store.get_upd_of_ne hcne] using hc
  · simpa using (show z.2 + 1 < m.store.len z.1 from by omega)
  · simpa [Mem.updBlock, Store.updBlock, Mem.upd] using hQ

/-- The same pair multiplication WP supplies its output frame through the generic exact-update
rule; no separate scalar-call or component-preservation argument is needed. -/
theorem writes_multiply {M : Machine K} {I : Interp Op Tst K} (hI : IsScalar M I)
    {md : Mode} {τ : Tape K} {m : Mem K} {x c z : ℕ × ℕ} {ar ai a : K}
    (hxz : Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock z.1 z.2 2))
    (hcz : Fp.Disj (Store.inBlock c.1 c.2 1) (Store.inBlock z.1 z.2 2))
    (hxr : m.store.get x.1 x.2 = some ar)
    (hxi : m.store.get x.1 (x.2 + 1) = some ai)
    (hc : m.store.get c.1 c.2 = some a) (hz : z.2 + 2 ≤ m.store.len z.1) :
    Writes md I τ (multiply (Op := Op) (Tst := Tst)).body (Env.frame [] [x, c, z])
      (Store.inBlock z.1 z.2 2)
      (fun m' => m' = m.updBlock z [M.mul ar a, M.mul ai a]) m :=
  Writes.of_wp_eq_updBlock (wp_multiply hI hxz hcz hxr hxi hc hz rfl)

end NLAlib.Ops.Pair
