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
* `NLAlib.Ops.Pair.complexDivideWithScratch`: complex division by eleven scalar instructions.
* `NLAlib.Ops.StdModel.norm_complexDivide_sub_le`: the rounded quotient is relatively accurate.
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

/-- The actual eleven scalar instructions for complex division. -/
def divisionInstructions : List (ScalarIns ScalarOp) :=
  [⟨.mul, [⟨1, .var 1⟩, ⟨1, .var 1⟩], ⟨2, .var 2⟩⟩,
   ⟨.mul, [⟨1, .var 1 + .const 1⟩, ⟨1, .var 1 + .const 1⟩],
     ⟨2, .var 2 + .const 3⟩⟩,
   ⟨.add, [⟨2, .var 2⟩, ⟨2, .var 2 + .const 3⟩], ⟨2, .var 2⟩⟩,
   ⟨.mul, [⟨0, .var 0⟩, ⟨1, .var 1⟩], ⟨2, .var 2 + .const 1⟩⟩,
   ⟨.mul, [⟨0, .var 0 + .const 1⟩, ⟨1, .var 1 + .const 1⟩],
     ⟨2, .var 2 + .const 3⟩⟩,
   ⟨.add, [⟨2, .var 2 + .const 1⟩, ⟨2, .var 2 + .const 3⟩],
     ⟨2, .var 2 + .const 1⟩⟩,
   ⟨.mul, [⟨0, .var 0 + .const 1⟩, ⟨1, .var 1⟩], ⟨2, .var 2 + .const 2⟩⟩,
   ⟨.mul, [⟨0, .var 0⟩, ⟨1, .var 1 + .const 1⟩], ⟨2, .var 2 + .const 3⟩⟩,
   ⟨.sub, [⟨2, .var 2 + .const 2⟩, ⟨2, .var 2 + .const 3⟩],
     ⟨2, .var 2 + .const 2⟩⟩,
   ⟨.div, [⟨2, .var 2 + .const 1⟩, ⟨2, .var 2⟩], ⟨3, .var 3⟩⟩,
   ⟨.div, [⟨2, .var 2 + .const 2⟩, ⟨2, .var 2⟩], ⟨3, .var 3 + .const 1⟩⟩]

/-- **Complex division with four caller-owned scratch words**: `[] (x, y, t) → (z)` stores in `z`
the pair of $(x\bar y)/\lvert y\rvert^2$, the denominator the sum of two real squares; both
numerators are computed before either output word is written, so `z` may alias an input pair. -/
def complexDivideWithScratch : Impl Op Tst :=
  ⟨0, 3, 1, .scalarBlock (divisionInstructions.map ScalarIns.lift)⟩

/-- The two words stored by `NLAlib.Ops.Pair.complexDivideWithScratch` on the machine `M` from the
pairs `x` and `y`: $\mathrm{fl}(\mathrm{fl}(x_0y_0 + x_1y_1)/d)$ and
$\mathrm{fl}(\mathrm{fl}(x_1y_0 - x_0y_1)/d)$, $d = \mathrm{fl}(y_0^2 + y_1^2)$. -/
def divideWords (M : Machine K) (x y : K × K) : K × K :=
  let d := M.add (M.mul y.1 y.1) (M.mul y.2 y.2)
  (M.div (M.add (M.mul x.1 y.1) (M.mul x.2 y.2)) d,
    M.div (M.sub (M.mul x.2 y.1) (M.mul x.1 y.2)) d)

end NLAlib.Ops.Pair

/-- A rounded sum of two rounded products: from relative errors $\boldsymbol{u}$ in $p$, $q$
and their rounded sum $r$, $r$ is within
$(2\boldsymbol{u} + \boldsymbol{u}^2)(\lvert P\rvert + \lvert Q\rvert)$ of $P + Q$. -/
private theorem NLAlib.Ops.abs_roundSum_sub_le {u p q r P Q : ℝ} (hu : 0 ≤ u)
    (hp : |p - P| ≤ u * |P|) (hq : |q - Q| ≤ u * |Q|) (hr : |r - (p + q)| ≤ u * |p + q|) :
    |r - (P + Q)| ≤ (2 * u + u ^ 2) * (|P| + |Q|) := by
  have hp' := abs_le_of_abs_sub_le hp
  have hq' := abs_le_of_abs_sub_le hq
  have hpq : |p + q| ≤ (1 + u) * (|P| + |Q|) := by
    have := abs_add_le p q
    linarith
  have h1 : u * |p + q| ≤ u * ((1 + u) * (|P| + |Q|)) := mul_le_mul_of_nonneg_left hpq hu
  have htri : |r - (P + Q)| ≤ |r - (p + q)| + |p - P| + |q - Q| := by
    have e : r - (P + Q) = (r - (p + q)) + (p - P) + (q - Q) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
  nlinarith [abs_nonneg P, abs_nonneg Q]

/-- A rounded quotient of perturbed numbers: with $\lvert d - D\rvert \le eD$,
$\lvert n - N\rvert \le eP$, $\lvert N\rvert \le P$, $e \le \tfrac{65}{32}\boldsymbol{u}$ and
$\boldsymbol{u} \le 1/32$, the rounded quotient $q$ of $n/d$ is within $5.6\boldsymbol{u}P/D$ of
$N/D$. -/
private theorem NLAlib.Ops.abs_roundQuot_sub_le {u e n d N D P q : ℝ} (hu : 0 ≤ u)
    (hu32 : u ≤ 1 / 32) (he : e ≤ 65 / 32 * u) (hD : 0 < D) (hd : |d - D| ≤ e * D)
    (hn : |n - N| ≤ e * P) (hN : |N| ≤ P) (hq : |q - n / d| ≤ u * |n / d|) :
    |q - N / D| ≤ 28 / 5 * u * (P / D) := by
  have he0 : 0 ≤ e := by
    have := abs_nonneg (d - D)
    by_contra h
    push_neg at h
    nlinarith
  have hP : 0 ≤ P := (abs_nonneg N).trans hN
  have hdlo : 959 / 1024 * D ≤ d := by
    have := (abs_le.mp hd).1
    nlinarith
  have hdpos : 0 < d := by linarith
  -- the unrounded quotient
  have hq1 : |n / d - N / D| ≤ 22 / 5 * u * (P / D) := by
    rw [div_sub_div _ _ hdpos.ne' hD.ne', abs_div, abs_mul, abs_of_pos hdpos, abs_of_pos hD]
    have hnum : |n * D - d * N| ≤ 2 * e * P * D := by
      have e1 : n * D - d * N = (n - N) * D - (d - D) * N := by ring
      rw [e1]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hD]
      have := mul_le_mul_of_nonneg_right hn hD.le
      have := mul_le_mul hd hN (abs_nonneg _) (by positivity)
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    have : 2 * e * P * D ≤ 22 / 5 * u * (P / D) * (d * D) := by
      rw [show 22 / 5 * u * (P / D) * (d * D) = 22 / 5 * u * P * d by field_simp]
      have h2 : 2 * e ≤ 22 / 5 * u * (959 / 1024) := by nlinarith
      have := mul_le_mul_of_nonneg_left hdlo (show 0 ≤ 22 / 5 * u * P by positivity)
      nlinarith [mul_nonneg hP hD.le]
    linarith
  have hnd : |n / d| ≤ |N / D| + 22 / 5 * u * (P / D) := by
    have := abs_sub_abs_le_abs_sub (n / d) (N / D)
    linarith
  have hND : |N / D| ≤ P / D := by
    rw [abs_div, abs_of_pos hD]; exact div_le_div_of_nonneg_right hN hD.le
  have hr : 0 ≤ P / D := by positivity
  have htri : |q - N / D| ≤ |q - n / d| + |n / d - N / D| := abs_sub_le _ _ _
  have : u * |n / d| ≤ u * ((1 + 22 / 5 * u) * (P / D)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hu
  nlinarith [mul_le_mul_of_nonneg_right hu32 (mul_nonneg hu hr)]

/-- Cauchy–Schwarz for two pairs: $\lvert pr\rvert + \lvert qs\rvert \le
\sqrt{p^2 + q^2}\sqrt{r^2 + s^2}$. -/
private theorem NLAlib.Ops.abs_mul_add_abs_mul_le (p q r s : ℝ) :
    |p * r| + |q * s| ≤ √(p * p + q * q) * √(r * r + s * s) := by
  rw [← Real.sqrt_mul (by nlinarith [mul_self_nonneg p, mul_self_nonneg q])]
  apply Real.le_sqrt_of_sq_le
  rw [abs_mul, abs_mul]
  have h1 := abs_mul_abs_self p
  have h2 := abs_mul_abs_self q
  have h3 := abs_mul_abs_self r
  have h4 := abs_mul_abs_self s
  nlinarith [sq_nonneg (|p| * |s| - |q| * |r|), abs_nonneg p, abs_nonneg q, abs_nonneg r,
    abs_nonneg s]

/-- **The rounded complex quotient is relatively accurate**: under the standard model at
$\boldsymbol{u} \le 1/32$, for $y \ne 0$ the words of `NLAlib.Ops.Pair.divideWords` are within
$8\boldsymbol{u}\lvert x\rvert/\lvert y\rvert$ of $x/y$ (cancellation in the numerators is allowed:
their
errors are relative to $\lvert x\rvert\lvert y\rvert$). [Higham2002, §3.6] -/
theorem NLAlib.Ops.StdModel.norm_complexDivide_sub_le {M : NLAlib.Ops.Machine ℝ} {u : ℝ}
    (hM : NLAlib.Ops.StdModel u id M) (hu : u ≤ 1 / 32) {x y : ℂ} (hy : y ≠ 0) :
    ‖(⟨(NLAlib.Ops.Pair.divideWords M (x.re, x.im) (y.re, y.im)).1,
        (NLAlib.Ops.Pair.divideWords M (x.re, x.im) (y.re, y.im)).2⟩ : ℂ) - x / y‖ ≤
      8 * u * (‖x‖ / ‖y‖) := by
  have hu0 : 0 ≤ u := by
    have := hM.lit 1
    simp only [Rat.cast_one, abs_one, mul_one, id] at this
    exact (abs_nonneg _).trans this
  set a := x.re
  set b := x.im
  set c := y.re
  set d := y.im
  have hD : 0 < c * c + d * d := by
    have := Complex.normSq_pos.mpr hy
    rwa [Complex.normSq_apply] at this
  have hny : ‖y‖ = √(c * c + d * d) := by rw [Complex.norm_def, Complex.normSq_apply]
  have hnx : ‖x‖ = √(a * a + b * b) := by rw [Complex.norm_def, Complex.normSq_apply]
  set P := ‖x‖ * ‖y‖ with hPdef
  have hPD : P / (c * c + d * d) = ‖x‖ / ‖y‖ := by
    have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have : c * c + d * d = ‖y‖ ^ 2 := by
      rw [hny, Real.sq_sqrt hD.le]
    rw [this, hPdef]; field_simp
  have hCS := abs_mul_add_abs_mul_le
  have he : 2 * u + u ^ 2 ≤ 65 / 32 * u := by nlinarith
  -- the denominator
  have hden := abs_roundSum_sub_le (r := M.add (M.mul c c) (M.mul d d)) hu0 (hM.mul c c)
    (hM.mul d d) (hM.add (M.mul c c) (M.mul d d))
  simp only [id, abs_mul_self] at hden
  -- the numerators
  have hn1 := abs_roundSum_sub_le (r := M.add (M.mul a c) (M.mul b d)) hu0 (hM.mul a c)
    (hM.mul b d) (hM.add (M.mul a c) (M.mul b d))
  simp only [id] at hn1
  have hn2 := abs_roundSum_sub_le (P := b * c) (Q := -(a * d)) hu0 (hM.mul b c)
    (p := M.mul b c) (q := -M.mul a d) (by
      have := hM.mul a d
      simp only [id] at this ⊢
      rw [show -M.mul a d - -(a * d) = -(M.mul a d - a * d) by ring, abs_neg, abs_neg]
      exact this)
    (by simpa [sub_eq_add_neg] using hM.sub (M.mul b c) (M.mul a d))
  rw [abs_neg] at hn2
  have hP1 : |a * c| + |b * d| ≤ P := by rw [hPdef, hnx, hny]; exact hCS a b c d
  have hP2 : |b * c| + |a * d| ≤ P := by
    rw [hPdef, hnx, hny, show a * a + b * b = b * b + a * a by ring]
    have := hCS b a c d
    rwa [add_comm (|b * c|)] at this ⊢
  have hP0 : 0 ≤ 2 * u + u ^ 2 := by positivity
  have hdenD : (c * c + d * d) ≠ 0 := hD.ne'
  set den := M.add (M.mul c c) (M.mul d d)
  have hden' : |den - (c * c + d * d)| ≤ (2 * u + u ^ 2) * (c * c + d * d) := by
    simpa using hden
  have hdenne : den ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg, abs_of_pos hD] at hden'
    nlinarith
  have hq1 := abs_roundQuot_sub_le (P := P) hu0 hu he hD hden'
    (hn1.trans (mul_le_mul_of_nonneg_left hP1 hP0)) ((abs_add_le _ _).trans hP1)
    (by simpa using hM.div (M.add (M.mul a c) (M.mul b d)) den hdenne)
  have hq2 := abs_roundQuot_sub_le (P := P) hu0 hu he hD hden'
    (hn2.trans (mul_le_mul_of_nonneg_left hP2 hP0))
    ((abs_add_le _ _).trans (by rw [abs_neg]; exact hP2))
    (by simpa [sub_eq_add_neg] using hM.div (M.sub (M.mul b c) (M.mul a d)) den hdenne)
  rw [hPD] at hq1 hq2
  have hre : (x / y).re = (a * c + b * d) / (c * c + d * d) := by
    rw [Complex.div_re, Complex.normSq_apply]; ring
  have him : (x / y).im = (b * c + -(a * d)) / (c * c + d * d) := by
    rw [Complex.div_im, Complex.normSq_apply]; ring
  refine (Complex.norm_le_sqrt_two_mul_max _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im, hre, him]
  have hm : max |(Pair.divideWords M (a, b) (c, d)).1 - (a * c + b * d) / (c * c + d * d)|
      |(Pair.divideWords M (a, b) (c, d)).2 - (b * c + -(a * d)) / (c * c + d * d)| ≤
      28 / 5 * u * (‖x‖ / ‖y‖) := max_le (by simpa [Pair.divideWords] using hq1)
        (by simpa [Pair.divideWords, sub_eq_add_neg] using hq2)
  have hs : √2 ≤ 99 / 70 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hr : 0 ≤ 28 / 5 * u * (‖x‖ / ‖y‖) := by positivity
  calc √2 * _ ≤ 99 / 70 * (28 / 5 * u * (‖x‖ / ‖y‖)) :=
        mul_le_mul hs hm (le_max_of_le_left (abs_nonneg _)) (by norm_num)
    _ ≤ 8 * u * (‖x‖ / ‖y‖) := by nlinarith [div_nonneg (norm_nonneg x) (norm_nonneg y)]
