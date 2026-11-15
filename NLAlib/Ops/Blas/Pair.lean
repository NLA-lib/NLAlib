/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Ops.Logic.Builder
public import NLAlib.Ops.Logic.Scalar
public import NLAlib.Ops.Logic.Writes
public import NLAlib.Ops.Logic.SpatialScalar

/-!
# Scalar operations on stored word pairs

Each component is computed by an ordinary scalar operation. The functional proof identifies
the actual updated memory and supports disjoint source and destination regions of one buffer.

## Main results

* `NLAlib.Ops.Pair.multiply`: multiply both component words by one stored scalar.
* `NLAlib.Ops.Pair.wp_multiply`: exact functional execution under scalar multiplication contracts.
* `NLAlib.Ops.Pair.linearCombination`: actual scalar computation of two complex products and a sum.
* `NLAlib.Ops.Pair.writes_linearCombination`: the rounded word pair and its spatial write frame.
* `NLAlib.Ops.Pair.readBlocks_updCells_pairs`: recovery of two in-place output pairs after scratch.
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


/-- The actual machine products and sums for a complex linear combination of word pairs.
The first component is the real part and the second is the imaginary part. -/
def linearWords (M : Machine K) (a b x y : K × K) : K × K :=
  (M.add (M.sub (M.mul a.1 x.1) (M.mul a.2 x.2))
      (M.sub (M.mul b.1 y.1) (M.mul b.2 y.2)),
    M.add (M.add (M.mul a.1 x.2) (M.mul a.2 x.1))
      (M.add (M.mul b.1 y.2) (M.mul b.2 y.1)))

/-- Fourteen scalar operations for a complex linear combination. The scratch pair is
caller-owned and the output is separate from the input pairs. -/
def linearCombination : Impl Op Tst := opsImpl% [] (a, b, x, y, t) → (z) {
  call (Has.inj ScalarOp.mul) [] (a, x) → (t);
  call (Has.inj ScalarOp.mul) [] (a[1], x[1]) → (t[1]);
  call (Has.inj ScalarOp.sub) [] (t, t[1]) → (z);
  call (Has.inj ScalarOp.mul) [] (a, x[1]) → (t);
  call (Has.inj ScalarOp.mul) [] (a[1], x) → (t[1]);
  call (Has.inj ScalarOp.add) [] (t, t[1]) → (z[1]);
  call (Has.inj ScalarOp.mul) [] (b, y) → (t);
  call (Has.inj ScalarOp.mul) [] (b[1], y[1]) → (t[1]);
  call (Has.inj ScalarOp.sub) [] (t, t[1]) → (t);
  call (Has.inj ScalarOp.add) [] (z, t) → (z);
  call (Has.inj ScalarOp.mul) [] (b, y[1]) → (t);
  call (Has.inj ScalarOp.mul) [] (b[1], y) → (t[1]);
  call (Has.inj ScalarOp.add) [] (t, t[1]) → (t);
  call (Has.inj ScalarOp.add) [] (z[1], t) → (z[1])
}

/-- Shared explicit scalar instruction list, parameterized by its physical operands. -/
def linearInstructions (a b x y t z : Operand) : List (ScalarIns ScalarOp) :=
  [⟨.mul, [a, x], t⟩,
   ⟨.mul, [⟨a.buf, a.off + .const 1⟩, ⟨x.buf, x.off + .const 1⟩],
     ⟨t.buf, t.off + .const 1⟩⟩,
   ⟨.sub, [t, ⟨t.buf, t.off + .const 1⟩], z⟩,
   ⟨.mul, [a, ⟨x.buf, x.off + .const 1⟩], t⟩,
   ⟨.mul, [⟨a.buf, a.off + .const 1⟩, x], ⟨t.buf, t.off + .const 1⟩⟩,
   ⟨.add, [t, ⟨t.buf, t.off + .const 1⟩], ⟨z.buf, z.off + .const 1⟩⟩,
   ⟨.mul, [b, y], t⟩,
   ⟨.mul, [⟨b.buf, b.off + .const 1⟩, ⟨y.buf, y.off + .const 1⟩],
     ⟨t.buf, t.off + .const 1⟩⟩,
   ⟨.sub, [t, ⟨t.buf, t.off + .const 1⟩], t⟩,
   ⟨.add, [z, t], z⟩,
   ⟨.mul, [b, ⟨y.buf, y.off + .const 1⟩], t⟩,
   ⟨.mul, [⟨b.buf, b.off + .const 1⟩, y], ⟨t.buf, t.off + .const 1⟩⟩,
   ⟨.add, [t, ⟨t.buf, t.off + .const 1⟩], t⟩,
   ⟨.add, [⟨z.buf, z.off + .const 1⟩, t], ⟨z.buf, z.off + .const 1⟩⟩]

/-- Chronological word writes of the linear combination. -/
def linearTrace (M : Machine K) (t z : ℕ × ℕ)
  (av bv xv yv : K × K) := [(t, M.mul av.1 xv.1), ((t.1, t.2 + 1), M.mul av.2 xv.2),
  (z, M.sub (M.mul av.1 xv.1) (M.mul av.2 xv.2)),
  (t, M.mul av.1 xv.2), ((t.1, t.2 + 1), M.mul av.2 xv.1),
  ((z.1, z.2 + 1), M.add (M.mul av.1 xv.2) (M.mul av.2 xv.1)),
  (t, M.mul bv.1 yv.1), ((t.1, t.2 + 1), M.mul bv.2 yv.2),
  (t, M.sub (M.mul bv.1 yv.1) (M.mul bv.2 yv.2)),
  (z, (linearWords M av bv xv yv).1),
  (t, M.mul bv.1 yv.2), ((t.1, t.2 + 1), M.mul bv.2 yv.1),
  (t, M.add (M.mul bv.1 yv.2) (M.mul bv.2 yv.1)),
  ((z.1, z.2 + 1), (linearWords M av bv xv yv).2)]

private theorem eval_linearCombination {M : Machine K} {m : Mem K} {a b x y t z : ℕ × ℕ}
    {av bv xv yv : K × K}
    (ht : Fp.Disj (Store.inBlock t.1 t.2 2) (Fp.blocks [a, b, x, y] [2, 2, 2, 2]))
    (hz : Fp.Disj (Store.inBlock z.1 z.2 2) (Fp.blocks [a, b, x, y] [2, 2, 2, 2]))
    (htz : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock z.1 z.2 2))
    (ha₀ : m.store.get a.1 a.2 = some av.1)
    (ha₁ : m.store.get a.1 (a.2 + 1) = some av.2)
    (hb₀ : m.store.get b.1 b.2 = some bv.1)
    (hb₁ : m.store.get b.1 (b.2 + 1) = some bv.2)
    (hx₀ : m.store.get x.1 x.2 = some xv.1)
    (hx₁ : m.store.get x.1 (x.2 + 1) = some xv.2)
    (hy₀ : m.store.get y.1 y.2 = some yv.1)
    (hy₁ : m.store.get y.1 (y.2 + 1) = some yv.2)
 :
    ScalarIns.evalBlock M.eval (Env.frame [] [a, b, x, y, t, z])
      (linearInstructions ⟨0, .var 0⟩ ⟨1, .var 1⟩ ⟨2, .var 2⟩
      ⟨3, .var 3⟩ ⟨4, .var 4⟩ ⟨5, .var 5⟩)
      m.store.cellFn = some (linearTrace M t z av bv xv yv) := by
  have hne (w : ℕ × ℕ) (hw : w ∈ [a, b, x, y]) (i j : ℕ) (hi : i < 2) (hj : j < 2) :
      (w.1, w.2 + i) ≠ (t.1, t.2 + j) ∧ (w.1, w.2 + i) ≠ (z.1, z.2 + j) := by
    have hin : Store.inBlock w.1 w.2 2 ≤ Fp.blocks [a, b, x, y] [2, 2, 2, 2] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> fp_sub
    exact ⟨(ht.symm.mono hin le_rfl).ne_offsets hi hj,
      (hz.symm.mono hin le_rfl).ne_offsets hi hj⟩
  have hna00 := hne a (by simp) 0 0 (by omega) (by omega)
  have hna01 := hne a (by simp) 0 1 (by omega) (by omega)
  have hna10 := hne a (by simp) 1 0 (by omega) (by omega)
  have hna11 := hne a (by simp) 1 1 (by omega) (by omega)
  have hnb00 := hne b (by simp) 0 0 (by omega) (by omega)
  have hnb01 := hne b (by simp) 0 1 (by omega) (by omega)
  have hnb10 := hne b (by simp) 1 0 (by omega) (by omega)
  have hnb11 := hne b (by simp) 1 1 (by omega) (by omega)
  have hnx00 := hne x (by simp) 0 0 (by omega) (by omega)
  have hnx01 := hne x (by simp) 0 1 (by omega) (by omega)
  have hnx10 := hne x (by simp) 1 0 (by omega) (by omega)
  have hnx11 := hne x (by simp) 1 1 (by omega) (by omega)
  have hny00 := hne y (by simp) 0 0 (by omega) (by omega)
  have hny01 := hne y (by simp) 0 1 (by omega) (by omega)
  have hny10 := hne y (by simp) 1 0 (by omega) (by omega)
  have hny11 := hne y (by simp) 1 1 (by omega) (by omega)
  have hnT00 := htz.ne_offsets (i := 0) (j := 0) (by omega) (by omega)
  have hnT01 := htz.ne_offsets (i := 0) (j := 1) (by omega) (by omega)
  have hnT10 := htz.ne_offsets (i := 1) (j := 0) (by omega) (by omega)
  have hnT11 := htz.ne_offsets (i := 1) (j := 1) (by omega) (by omega)
  simp only [Nat.add_zero] at hna00 hna01 hna10 hna11 hnb00 hnb01 hnb10 hnb11
  simp only [Nat.add_zero] at hnx00 hnx01 hnx10 hnx11 hny00 hny01 hny10 hny11
  simp only [Nat.add_zero] at hnT00 hnT01 hnT10 hnT11
  rcases a with ⟨ab, ao⟩
  rcases b with ⟨bb, bo⟩
  rcases x with ⟨xb, xo⟩
  rcases y with ⟨yb, yo⟩
  rcases t with ⟨tb, toff⟩
  rcases z with ⟨zb, zo⟩
  have hnR00 := Ne.symm hnT00
  have hnR01 := Ne.symm hnT01
  have hnR10 := Ne.symm hnT10
  have hnR11 := Ne.symm hnT11
  have hupd (g : ℕ × ℕ → Option K) (u w : ℕ × ℕ) (v : Option K) :
      Function.update g u v w = if w = u then v else g w := Function.update_apply ..
  have hpair := @Prod.mk.injEq ℕ ℕ
  dsimp only [linearInstructions, linearTrace, linearWords, Env.frame, Store.cellFn]
  repeat' first
  | rw [ScalarIns.evalBlock.eq_def]
    simp only [Store.cellFn, Machine.eval, Operand.evalList, Operand.eval, IExp.eval,
      List.map_cons, List.map_nil, List.nil_append,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, Option.map_some,
      and_false, if_true, if_false, Nat.add_eq_left, Nat.left_eq_add, Nat.reduceEqDiff, *]

/-- The linear combination stores its actual rounded word pair and preserves all cells
outside the output and two scratch cells. Source pairs may share buffers or coincide. -/
theorem writes_linearCombination {M : Machine K} {I : Interp Op Tst K}
    (hI : IsScalar M I) {τ : Tape K} {m : Mem K} {a b x y t z : ℕ × ℕ}
    {av bv xv yv : K × K}
    (ht : Fp.Disj (Store.inBlock t.1 t.2 2) (Fp.blocks [a, b, x, y] [2, 2, 2, 2]))
    (hz : Fp.Disj (Store.inBlock z.1 z.2 2) (Fp.blocks [a, b, x, y] [2, 2, 2, 2]))
    (htz : Fp.Disj (Store.inBlock t.1 t.2 2) (Store.inBlock z.1 z.2 2))
    (ha₀ : m.store.get a.1 a.2 = some av.1)
    (ha₁ : m.store.get a.1 (a.2 + 1) = some av.2)
    (hb₀ : m.store.get b.1 b.2 = some bv.1)
    (hb₁ : m.store.get b.1 (b.2 + 1) = some bv.2)
    (hx₀ : m.store.get x.1 x.2 = some xv.1)
    (hx₁ : m.store.get x.1 (x.2 + 1) = some xv.2)
    (hy₀ : m.store.get y.1 y.2 = some yv.1)
    (hy₁ : m.store.get y.1 (y.2 + 1) = some yv.2)
    (htroom : t.2 + 2 ≤ m.store.len t.1) (hzroom : z.2 + 2 ≤ m.store.len z.1) :
    Writes .total I τ linearCombination.body (Env.frame [] [a, b, x, y, t, z])
      (Store.inBlock t.1 t.2 2 ⊔ Store.inBlock z.1 z.2 2)
      (fun μ => μ.pos = m.pos ∧ μ.store.readBlock z.1 z.2 2 =
        some [(linearWords M av bv xv yv).1, (linearWords M av bv xv yv).2]) m := by
  let xs := linearInstructions ⟨0, .var 0⟩ ⟨1, .var 1⟩ ⟨2, .var 2⟩
      ⟨3, .var 3⟩ ⟨4, .var 4⟩ ⟨5, .var 5⟩
  let ws := linearTrace M t z av bv xv yv
  have hev := eval_linearCombination (M := M) ht hz htz ha₀ ha₁ hb₀ hb₁ hx₀ hx₁ hy₀ hy₁
  have hroom : ∀ w ∈ ws, w.1.2 < m.store.len w.1.1 := by
    intro w hw
    simp only [ws, linearTrace, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> dsimp <;> omega
  have h := writes_machineScalarBlock (τ := τ) hI hev hroom
  change Writes .total I τ linearCombination.body _ _ _ m at h
  refine h.mono ?_ ?_
  · intro b i hi
    simp only [linearTrace, List.map_cons, List.map_nil, Fp.cells, List.mem_cons,
      List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      obtain ⟨rfl, rfl⟩ := h <;> first | exact Or.inl ⟨rfl, by omega, by omega⟩ |
        exact Or.inr ⟨rfl, by omega, by omega⟩
  · rintro μ _ rfl
    have hz₀ : z.2 < m.store.len z.1 := by omega
    have hz₁ : z.2 + 1 < m.store.len z.1 := by omega
    have hzt0 : z ≠ t := by
      simpa only [Nat.add_zero, Prod.eta] using
        htz.symm.ne_offsets (i := 0) (j := 0) (by omega) (by omega)
    have hzt1 : z ≠ (t.1, t.2 + 1) := by
      simpa only [Nat.add_zero, Prod.eta] using
        htz.symm.ne_offsets (i := 0) (j := 1) (by omega) (by omega)
    have hzz : z ≠ (z.1, z.2 + 1) := by
      intro h
      have he := congrArg Prod.snd h
      omega
    have h0 : (m.updCells ws).store.get z.1 z.2 =
        some (linearWords M av bv xv yv).1 :=
      get_updCells (ws₁ := ws.take 9) (ws₂ := ws.drop 10) hz₀
        (by simp [ws, linearTrace, hzt0, hzt1, hzz])
    have h1 : (m.updCells ws).store.get z.1 (z.2 + 1) =
        some (linearWords M av bv xv yv).2 :=
      get_updCells (ws₁ := ws.take 13) (ws₂ := []) hz₁ (by simp)
    refine ⟨rfl, Store.readBlock_eq_some_iff.mpr ⟨rfl, ?_⟩⟩
    intro i hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · simpa using h0
    · simpa using h1

/-- The last two component writes recover a packed pair independently of prior scratch writes. -/
theorem readBlock_updCells_pair {m : Mem K} {prior : List ((ℕ × ℕ) × K)}
    {z : ℕ × ℕ} {v : K × K} (hz : z.2 + 2 ≤ m.store.len z.1) :
    (m.updCells (prior ++ [(z, v.1), ((z.1, z.2 + 1), v.2)])).store.readBlock z.1 z.2 2 =
      some [v.1, v.2] := by
  have hzz : z ≠ (z.1, z.2 + 1) := by intro he; have := congrArg Prod.snd he; omega
  have hr := get_updCells (m := m) (ws₁ := prior)
    (ws₂ := [((z.1, z.2 + 1), v.2)]) (z := z) (v := v.1)
    (by omega) (by simp [hzz])
  have hi := get_updCells (m := m) (ws₁ := prior ++ [(z, v.1)])
    (ws₂ := []) (z := (z.1, z.2 + 1)) (v := v.2) (by dsimp; omega) (by simp)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hi
  simp [Store.readBlock_succ, Store.readBlock_zero, hr, hi]

/-- Copying two previously computed pairs back into spatially disjoint output views gives
both packed outputs, independently of the earlier scratch-write trace. -/
theorem readBlocks_updCells_pairs {m : Mem K} {prior : List ((ℕ × ℕ) × K)}
    {x y : ℕ × ℕ} {u v : K × K}
    (hxy : Fp.Disj (Store.inBlock x.1 x.2 2) (Store.inBlock y.1 y.2 2))
    (hx : x.2 + 2 ≤ m.store.len x.1) (hy : y.2 + 2 ≤ m.store.len y.1) :
    (m.updCells (prior ++ [(x, u.1), ((x.1, x.2 + 1), u.2),
      (y, v.1), ((y.1, y.2 + 1), v.2)])).readBlocks [x, y] [2, 2] =
      some [[u.1, u.2], [v.1, v.2]] := by
  have hxy00 := hxy.ne_offsets (i := 0) (j := 0) (by omega) (by omega)
  have hxy01 := hxy.ne_offsets (i := 0) (j := 1) (by omega) (by omega)
  have hxy10 := hxy.ne_offsets (i := 1) (j := 0) (by omega) (by omega)
  have hxy11 := hxy.ne_offsets (i := 1) (j := 1) (by omega) (by omega)
  simp only [Nat.add_zero, Prod.eta] at hxy00 hxy01 hxy10 hxy11
  have hxx : x ≠ (x.1, x.2 + 1) := by intro he; have := congrArg Prod.snd he; omega
  have hyy : y ≠ (y.1, y.2 + 1) := by intro he; have := congrArg Prod.snd he; omega
  have hrx := get_updCells (m := m) (z := x) (ws₁ := prior)
    (ws₂ := [((x.1, x.2 + 1), u.2), (y, v.1), ((y.1, y.2 + 1), v.2)])
    (v := u.1) (show x.2 < m.store.len x.1 by omega) (by simp [hxx, hxy00, hxy01])
  have hix := get_updCells (m := m) (z := (x.1, x.2 + 1)) (ws₁ := prior ++ [(x, u.1)])
    (ws₂ := [(y, v.1), ((y.1, y.2 + 1), v.2)])
    (v := u.2) (show x.2 + 1 < m.store.len x.1 by omega) (by simp [hxy10, hxy11])
  have hry := get_updCells (m := m) (z := y)
    (ws₁ := prior ++ [(x, u.1), ((x.1, x.2 + 1), u.2)])
    (ws₂ := [((y.1, y.2 + 1), v.2)])
    (v := v.1) (show y.2 < m.store.len y.1 by omega) (by simp [hyy])
  have hiy := get_updCells (m := m) (z := (y.1, y.2 + 1))
    (ws₁ := prior ++ [(x, u.1), ((x.1, x.2 + 1), u.2), (y, v.1)]) (ws₂ := [])
    (v := v.2) (show y.2 + 1 < m.store.len y.1 by omega) (by simp)
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hix hry hiy
  simp only [Mem.readBlocks_cons, Mem.readBlocks_nil]
  simp [Store.readBlock_succ, Store.readBlock_zero, hrx, hix, hry, hiy]


end NLAlib.Ops.Pair
